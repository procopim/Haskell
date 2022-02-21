import Data.List
import Debug.Trace

data T = App T T
       | If T T T 
       | Succ T
       | Pred T
       | IsZero T
       | Val V
       | Let Label T T
       | Seq T T
       | Alloc T
       | DeRef T
       | Assign T T
  deriving (Show, Eq)
  
data V = ERROR | Tru | Fls | Z | SuccNV V | UnitV | Location Loc | Var Label | L Label Type T deriving(Show, Eq)
  
data Label = A | C | D | E | F | G | H | I | J | K 
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type deriving (Show, Eq)

type Gamma = [(Label, Type)] 

type Mu = [(Loc, V)]

freeVars :: T -> [Label]
freeVars (Val (Var a)) = [a]
freeVars (Val (L a b (c))) = freeVars (c) \\ freeVars (Val (Var a))
freeVars (App a b) = freeVars a `union` freeVars b

relabel :: T -> Label -> Label -> T 

relabel (Val(Var b)) outlabel inlabel
 | (b == outlabel) && not (b == inlabel) = Val(Var inlabel)
 | not(b == outlabel) = Val(Var b)


sub :: T -> Label -> T -> T  

rlhelper :: Label -> [Label] -> Label
rlhelper x list = case x == head list of
    True -> rlhelper x (tail list)
    False -> head list 

sub (Val (Var subout)) (subfor) (Val(Var subover)) -- [x -> s]x
 | ((Val (Var subout)) == Val((Var subover))) = Val(Var subfor)
 | not ((Val (Var subout)) == (Val (Var subover))) = Val(Var subover)

sub (Val(Var subout)) (subfor) (Val (L va tp target)) -- Lx:T1.[x -> s]t2
 | not(va `elem` freeVars(Val (Var subfor))) && not((Var subout) == (Var va)) =  (Val (L va tp (sub (Val(Var subout)) (subfor) target)))  
 | ((Var subout) == (Var va)) = sub (Val(Var subout)) (subfor) (Val (L (rlhelper va [P,Q,R,S,U,W,X,Y]) tp target))
 | (va `elem` freeVars(Val (Var subfor))) = sub (Val(Var subout)) (subfor) (Val (L (rlhelper va [P,Q,R,S,U,W,X,Y]) tp target))

sub (Val(Var subout)) (subfor) (App t1 t2) = (App (sub (Val(Var subout)) (subfor) t1) (sub (Val(Var subout)) (subfor) t2))  --[x->s](t1 t2)

isNF :: T -> Bool
isNF (Val _) = True
isNF _ = False

ssos :: (T, Mu) -> (T, Mu)

typeCheck :: Gamma -> T -> Maybe Type

eval :: T -> T
eval t = if not(t == fst(ssos(t,[]))) then eval (fst(ssos(t,[]))) else t


run :: T -> T
run x = case typeCheck [] x of
    Just y -> eval x
    otherwise -> Val ERROR



------------Helper funcs----------------------------------------------------
maybehelper :: Maybe Type -> Type
maybehelper (Just t) = t

------freeVars helper for Let-------
freeUpVars :: T -> [Label]
freeUpVars (Val (Var a)) = [a]
freeUpVars (Val (L a b (c))) = a:freeUpVars(c)
--------------------------------------------------------------------------



-----------------------SEMANTICS---------------------------

-------------REFLEXIVE---------------
ssos (Val Tru, m) = (Val Tru, m)                      --reflexive Tru
ssos (Val Fls, m) = (Val Fls, m)                      --reflexive Fls
ssos (Val Z , m) = (Val Z, m)                         --reflexive 0
ssos (Val (SuccNV Z), m) = (Val (SuccNV Z), m)        --reflexive SuccNV Z
ssos (Val Z, m) = (Val Z, m)                          --reflexive Z
-------------BOOLEANS----------------
ssos (If (Val Tru) a _, m) = (a, m)                   --E-IfTrue 
ssos (If (Val Fls) _ b, m) = (b, m)                   --E-IfFalse
ssos (If a b c, m) = (If x b c, m2) where             --E-If v2
    x = fst(ssos(a, m))
    m2 = snd(ssos(a, m))
---------------NATURALS---------------
ssos (Succ (Val x), m) = (Val (SuccNV x), m)          --E-SuccNV
ssos (Succ x, m) = (Succ a, m2) where                 --E-Succ
    a = fst(ssos(x, m))
    m2 = snd(ssos(x, m))
ssos (Pred (Val Z),m) = (Val Z, m)                    --E-PredZero
ssos (Pred (Val (SuccNV x)),m) = (Val (SuccNV x),m)   --E-PredSucc
ssos (Pred x, m) = (Pred a, m2) where                 --E-Pred 
    a = fst(ssos(x, m))
    m2 = snd(ssos(x, m))
ssos (IsZero (Val Z),m) = (Val Tru, m)                --E-IsZeroZero
ssos (IsZero (Succ x), m) = (Val Fls, m)              --E-IsZeroSucc
ssos (IsZero x, m) = (IsZero a, m2) where             --E-IsZero
    a = fst(ssos(x, m))
    m2 = snd(ssos(x, m))
---------------LAMBDA CALC---------------
ssos (App a b, mu) = (App x b, mu2) where                --E-App1 
    x = fst(ssos(a, mu))
    mu2 = snd(ssos(a, mu))
ssos (App (Val a) b, mu) = (App (Val a) x, mu2) where    --E-App2
    x = fst(ssos(b, mu))
    mu2 = snd(ssos(b, mu))
ssos (App(Val (L va tp target))(Val (Var x)),mu) = ((sub (Val(Var va)) x target),mu) --E-AppAbs

---------------LET BINDINGS---------------
ssos (Let lb (Val(Var x)) t2, mu) = ((sub (Val(Var lb)) x t2),mu) --E-LetV

ssos (Let lb t1 t2, mu) = (Let lb x t2, mu2) where                --E-Let
    x = fst(ssos(t1, mu))
    mu2 = snd(ssos(t1, mu))

---------SEQUENCING------------
ssos (Seq (Val UnitV) t2, m) = (t2, m)                    --E-SeqNext
ssos (Seq t1 t2, m) = (Seq (fst(ssos(t1,m))) t2,m)        --E-Seq 






-------------------------TYPE CHECKING----------------------------

---------------BOOLS----------------
typeCheck _ (Val Tru) = Just BOOL                 --T-True
typeCheck _ (Val Fls) = Just BOOL                 --T-False
typeCheck g (If a b c) = case typeCheck g a of    --T-If
    Just BOOL -> case typeCheck g b of
        Just x -> case typeCheck g c of
            Just y -> case x == y of
                True -> Just BOOL
                False -> Nothing

--------------NATURALS----------------
typeCheck _ (Val Z) = Just NAT                    --T-Zero
typeCheck g (Succ t) = case typeCheck g t of      --T-Succ 
    Just NAT -> Just NAT
    otherwise -> Nothing
typeCheck g (Pred t) = case typeCheck g t of      --T-Pred 
    Just NAT -> Just NAT
    otherwise -> Nothing
typeCheck g (IsZero t) = case typeCheck g t of     --T-IsZero
    Just NAT -> Just BOOL
    otherwise -> Nothing

--------------LAMBDA CALCULUS----------------
typeCheck g (Val(Var x)) = case length g > 0 of    --T-Var
    False -> Nothing
    True -> case (x == fst(head g)) of
        True -> Just (snd(head g))
        False -> typeCheck (tail g) (Val(Var x))

typeCheck g (Val(L lb tp term)) = case typeCheck g (Val(Var lb)) of      --T-Abs
    Just someTerm -> Just (Arrow tp (maybehelper((typeCheck ((lb,tp):g) term)))) -- term in gamma, so we typecheck the rest
    Nothing -> case (typeCheck ((lb,tp):g) term) of --add lb:tp to gamma, and typeCheck term
        Just termType -> Just (Arrow tp termType)
        Nothing -> Nothing  --i.e. term is invalid type 

typeCheck g (App t1 t2) = case typeCheck g t1 of     --T-App
    Just (Arrow x y) -> case (typeCheck ((head (freeUpVars(t1)),x):g) t2) of
        Just x -> Just y
        otherwise -> Nothing


----------------------UNIT----------------------
typeCheck g (Val(UnitV)) = Just Unit                 --T-Var

----------------------LET----------------------

typeCheck g (Let lb t1 t2) = case typeCheck g t1 of     --T-Let
    Just someTerm -> case (typeCheck ((lb,someTerm):g) t2) of --we intuitively know x and t1 types agree
        Just nextTerm -> Just nextTerm
        otherwise -> Nothing  --i.e. term is invalid type 
