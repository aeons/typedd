module Chapter6

import Data.Vect

-- 1
Matrix : Nat -> Nat -> Type
Matrix rows cols = Vect rows (Vect cols Double)

-- 2
data Format = Number Format
            | Decimal Format
            | Character Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number fmt)    = (i   : Int) -> PrintfType fmt
PrintfType (Decimal fmt)   = (d   : Double) -> PrintfType fmt
PrintfType (Character fmt) = (c   : Char) -> PrintfType fmt
PrintfType (Str fmt)       = (str : String) -> PrintfType fmt
PrintfType (Lit str fmt)   = PrintfType fmt
PrintfType End             = String

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc    = \i   => printfFmt fmt (acc ++ show i)
printfFmt (Decimal fmt) acc   = \d   => printfFmt fmt (acc ++ show d)
printfFmt (Character fmt) acc = \c   => printfFmt fmt (acc ++ show c)
printfFmt (Str fmt) acc       = \str => printfFmt fmt (acc ++ str)
printfFmt (Lit lit fmt) acc   = printfFmt fmt (acc ++ lit)
printfFmt End acc             = acc

toFormat : (xs : List Char) -> Format
toFormat []                    = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Decimal (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Character (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: chars)        = Lit "%" (toFormat chars)
toFormat (c :: chars)          = case toFormat chars of
                                  Lit lit chars' => Lit (strCons c lit) chars'
                                  fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""

-- 3
TupleVect : Nat -> Type -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

test : TupleVect 4 Nat
test = (1, 2, 3, 4, ())
