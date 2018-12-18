module Main

import data.Vect

%default total

export
data VectUnknown : Type -> Type where
  MkVect : (len: Nat) -> Vect len a -> VectUnknown a

anyVect : (n ** Vect n String)
anyVect = (_ ** ["a", "b", "c"])

Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0,0,0], [0, 0,0]]

data Format = Number Format
            | Str Format
            | Ch Format
            | Dbl Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt) = (i: Int) -> PrintfType fmt
PrintfType (Str fmt) = (s: String) -> PrintfType fmt
PrintfType (Ch fmt) = (c: Char) -> PrintfType fmt
PrintfType (Dbl fmt) = (d: Double) -> PrintfType fmt
PrintfType (Lit s fmt) = PrintfType fmt
PrintfType End = String

printfFmt : (fmt:Format) -> String -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Ch fmt) acc = \c => printfFmt fmt (acc ++ (strCons c ""))
printfFmt (Dbl fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Lit s fmt) acc = printfFmt fmt (acc ++ s)
printfFmt End acc = acc

toFormat : List Char -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat ('%' :: 'c' :: xs) = Ch (toFormat xs)
toFormat ('%' :: 'd' :: 'l' :: xs) = Dbl (toFormat xs)
toFormat ('%' :: xs) = Lit "%" (toFormat xs)
toFormat (c :: xs) = case toFormat xs of
                        Lit lit xs' => Lit (strCons c lit) xs'
                        fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

TupleVect : (l: Nat) -> (el: Type) -> Type
TupleVect Z el = ()
TupleVect (S k) el = (el, TupleVect k el)

test : TupleVect 4 Nat
test = (1,2,3,4,())

-- data Tree elem = Empty
--                | Node (Tree elem) elem (Tree elem)
--
-- %name Tree tree, tree1

data BSTree : Type -> Type where
     Empty : Ord elem => BSTree elem
     Node : Ord elem => (left : BSTree elem) -> (val : elem) ->
                        (right : BSTree elem) -> BSTree elem

insert : elem -> BSTree elem -> BSTree elem
insert x Empty = Node Empty x Empty
insert x orig @ (Node left val right) = case compare x val of
                                      LT => Node (insert x left) val right
                                      EQ => orig
                                      GT => Node left val (insert x right)

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
     constructor MkData
     schema: Schema
     size : Nat
     items : Vect size (SchemaType schema)

addToStore : (store: DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) rec = MkData schema _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [rec]
    addToData (x :: xs) = x :: addToData xs

displaySchema : SchemaType schema -> String
displaySchema {schema = SString} x = show x
displaySchema {schema = SInt} x = show x
displaySchema {schema = (y .+. z)} (item1, item2) =
  displaySchema item1 ++ ", " ++ displaySchema item2

getRecord : (x : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getRecord x store = let storeItems = items store
  in (case integerToFin x (size store) of
           Nothing => Just ("Out of range\n", store)
           Just id => Just (displaySchema (index id storeItems) ++ "\n", store))

data Command : Schema -> Type where
      Add : SchemaType schema -> Command schema
      Get : Integer -> Command schema
      Quit : Command schema

parse_rhs : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parse_rhs schema "add" args = Just (Add (?parseSchema args))
parse_rhs schema "get" args = case all isDigit (unpack args) of
  False => Nothing
  True => Just (Get (cast args))
parse_rhs _ "quit" "" = Just Quit
parse_rhs _ _ _ = Nothing

parse : (schema: Schema) -> String -> Maybe (Command schema)
parse schema x = case span (/= ' ') x of
                   (cmd, args) => parse_rhs schema cmd (ltrim args)

prInp : DataStore -> String -> Maybe (String, DataStore)
prInp store str = case parse (schema store) str of
                       Nothing => Just ("invalid command\n", store)
                       (Just (Add x)) => Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
                       (Just (Get x)) =>  getRecord x store
                       (Just Quit) => Nothing

partial
main : IO ()
main = replWith (MkData SString _ []) "Command: " prInp
