
------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


------------------------- Assignment 1: Simple types

data Type =
     Base
     | Type:-> Type
     deriving Eq


nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice (   a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type where
  show = nice

type1 :: Type
type1 =  Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)



-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Type Term
  | Apply    Term Term

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable   x) = x
      f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m 
      f i (Apply    n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty


-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term
numeral i = Lambda "f" type1 (Lambda "x" Base (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))



sucterm :: Term
sucterm =
    Lambda "m" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Variable "f") (Variable "x"))
    )))

addterm :: Term
addterm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
    ))))

multerm :: Term
multerm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Apply (Variable "m") (Apply (Variable "n") (Variable "f")) 
    )))

suc :: Term -> Term
suc m = Apply sucterm m

add :: Term -> Term -> Term
add m n = Apply (Apply addterm m) n

mul :: Term -> Term -> Term
mul m n = Apply (Apply multerm m) n

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` (suc (numeral 2))

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction


used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x type1 n) = [x] `merge` used n
used (Apply  n m) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z type1 n)
    | z == x    = Lambda z type1 n
    | otherwise = Lambda z type1 (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y type1 m)
    | x == y    = Lambda y type1 m
    | otherwise = Lambda z type1 (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)


beta :: Term -> [Term]
beta (Apply (Lambda x type1 n) m) =
  [substitute x m n] ++
  [Apply (Lambda x type1 n') m  | n' <- beta n] ++
  [Apply (Lambda x type1 n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x type1 n) = [Lambda x type1 n' | n' <- beta n]
beta (Variable _) = []


-- - - - - - - - - - - -- Normalize


normalize :: Term -> IO ()
normalize m = do
--putStr("0--")
  putStr(show (bound m) ++ "--")
  print m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)



------------------------- Assignment 2: Type checking


type Context = [(Var, Type)]

extend :: (Var, Type) -> Context -> Context
extend ex context = ex : context

 
typeCheck :: Context -> Term -> Type
typeCheck context term = case term of
  Variable var_  -> do
    case lookup var_ context of
      Just t  -> t
      Nothing -> error $ "Variable " ++ (var_) ++ " not found"
  Lambda var_ type_ term  -> do
    let rightSide  = (typeCheck (extend (var_,type_) context) term)
    (type_ :-> rightSide)
  Apply term_1 term_2 -> do
    let a1 = typeCheck context term_1
    let a2 = typeCheck context term_2
    case a1 of
      (a:-> b)
        | a == a2 -> b
        | otherwise -> error $ "Expecting type " ++ (nice a) ++ ", but given type " ++ (nice a2)
      base -> error "Expecting ARROW type, but given BASE type"

    
typeof :: Context -> Term -> Type
typeof context x = (typeCheck context x) 


example8 = Lambda "x" Base ((Apply (Apply (Variable "f") (Variable "x")) (Variable "x")))



------------------------- Assignment 3: Functionals

data Functional =
    Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f


-- - - - - - - - - - - -- Examples

-- plussix : N -> N
plussix :: Functional
plussix  = Fun p where
          p (Num j) = Num (j+6)
          p (Fun f) = error "Num only"


-- plus : N -> (N -> N)
plus :: Functional
plus = Fun p where
       p (Num i) = Fun q where
                   q (Num j) = Num(i + j)
       p (Fun f) = error " POOP! Try again"

-- twice : (N -> N) -> N -> N
twice :: Functional
twice = Fun p where
        p (Num i) = error "POOP! Try again"
        p (Fun f) = Fun g where
                    g (Num i) = f(f(Num i))

-- - - - - - - - - - - -- Constructing functionals

dummy :: Type -> Functional
dummy Base       = (Num 0)
dummy (a:-> b)   = Fun (\ _ -> (dummy b))

count :: Type -> Functional -> Int
count _ (Num i)        = i
count (a:-> b) (Fun f) = count b (f(dummy b))
count Base _           = 0

increment :: Functional -> Int -> Functional
increment (Num i) j = Num (i + j)
increment (Fun f) j = Fun (g_func (Fun f)j)
    where
    g_func (Fun f) l (Num k)  = fun (fun plus(fun (Fun f) (Num k))) (Num l)
    g_func (Fun f) l (Fun f2) = Fun (g_func (fun (Fun f) (Fun f2)) l)





------------------------- Assignment 4 : Counting reduction steps

type Valuation = [(Var,Functional)]

interpret :: Context -> Valuation -> Term -> Functional
interpret context ((value, func_):values) (Variable y) 
   | value == y = func_
   | otherwise = interpret context values  (Variable y)

interpret context valuation (Lambda a term_a m) = Fun function
  where
    function :: Functional -> Functional
    function f = interpret (context++[(a,term_a)]) ((a,f):(filter (\(value, _) -> (value /= a)) valuation)) m

interpret context valuation (Apply m n) = increment (fun f g) (1 + count (typeof context n) g)
  where
    f = interpret context valuation m
    g = interpret context valuation n
interpret _ _ _ = Num 0

bound :: Term -> Int
bound v = count (typeof [] v) (interpret [] [] v)
