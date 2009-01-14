module Main where

import Char
import List
import Maybe
import Mpi
import Language.Haskell.Parser
import Language.Haskell.Syntax
import Language.Haskell.Pretty
import IO

infixr 6 >>>

type Regra = Def -> Maybe (String,Def)
type Catamorfismo b a defOrExp =
       (b, b -> b -> b, b, b -> b,
        b, b, b -> b -> b, b -> b -> b, b, b,
        b -> b -> b, b -> b -> b, b -> b -> b -> b,
        String -> b, Int -> b, String -> b, b -> b -> b,
        b -> b -> b, Float -> b, Integer -> b,
        b -> b -> b, b, b, b, b, b -> b, b -> b, b, Ops -> [b] -> b)
    -> defOrExp
    -> a

data Def = Exp :=: Exp | Def :^: Def
    deriving (Eq)

instance Show Def where
    show (exp1 :=: exp2) = show exp1 ++ " = " ++ show exp2
    show (def1 :^: def2) = show def1 ++ "\n" ++ show def2

data Exp = Id | Exp :.: Exp
         | Bang | Const Exp
         | Fst | Snd | Exp :/\: Exp | Exp :*: Exp
         | Inl | Inr | Exp :\/: Exp | Exp :+: Exp
         | Cond Exp Exp Exp
         | Fun String | NumInt Int | NumFloat Float | NumInteger Integer
         | Var String | Pair Exp Exp | Exp :@: Exp --point-wize
         | Lambda Exp Exp
         -- catamorfismos sobre listas...
         | In | Out | Nil | Cons | Cata Exp | Rec Exp
         | Nada
         | Op Ops [Exp]
    deriving (Eq)

data Ops = (:::) | (::++::)
         -- operacoes sobre numerarios...
         | (::+::) | (::-::)
         | (::*::) | (::/::)
         | (::>::)
    deriving (Eq)

instance Show Ops where
    show (:::) = ":"
    show (::++::) = "++"
    show (::+::) = "+"
    show (::-::) = "-"
    show (::*::) = "*"
    show (::/::) = "/"

instance Show Exp where
    show Id = "id"
    show Bang = "bang"
    show (Const exp1) = show exp1
    show (exp1 :.: exp2) = (show exp1) ++ " . " ++ (show exp2)
    show Fst = "p1"
    show Snd = "p2"
    show (exp1 :/\: exp2) = "<" ++ (show exp1) ++ "," ++ (show exp2) ++ ">"
    show (exp1 :*: exp2) = (show exp1) ++ " >< " ++ (show exp2)
    show Inl = "i1"
    show Inr = "i2"
    show (exp1 :\/: exp2) = "[" ++ (show exp1) ++ "," ++ (show exp2) ++ "]"
    show (exp1 :+: exp2) = (show exp1) ++ " -|- " ++ (show exp2)
    show (Cond exp1 exp2 exp3) = show exp1 ++ " -> " ++ show exp2 ++ "," ++ show exp3
    show (Fun s) = s
    show (NumInt i) = show i
    show (Var s) = s
    show (Pair exp1 exp2) = "(" ++ show exp1 ++ "," ++ show exp2 ++ ")"
    show (exp1 :@: exp2) = show exp1 ++ " " ++ show exp2
    show (Lambda exp1 exp2) = "(\\" ++ show exp1 ++ "->" ++ show exp2 ++ ")"
    show In = "in "
    show Out = "out "
    show Nil = "[] "
    show (Cons) = "Cons "
    show (Cata exp1) = "cata " ++ show exp1
    show (Rec exp1)  = "rec " ++ show exp1
    show Nada        = "()"
    show (Op op expl) | length expl == 0 = "(" ++ show op ++ ")"
                     | length expl == 1 = "(" ++ show op ++ show (expl !! 0) ++ ")"
                     | length expl == 2 = "(" ++ show (expl !! 0) ++ show op ++ show (expl !! 1) ++")"

-- combinador de regras
(>>>) :: Regra -> Regra -> Regra
(f >>> g) e = let m = f e
              in case m of
                  (Just (r,x)) -> Just (r,x)
                  Nothing -> g e

pfpw :: Def -> IO Def
pfpw e = do
    putStrLn $ show e
    pfpw' e
    where
    pfpw' :: Def -> IO Def
    pfpw' e = let m = (univcata' >>> retin' >>> absorcm' >>>
                       fusaom' >>> igualddm' >>> retconst' >>>
                       retx' >>> univm' >>> defext' >>>
                       defsplit' >>> defapos' >>> elimx' >>>
                       defsnd' >>> defid') e
              in case m of
                  (Just (s,def)) -> do
                      putStrLn s
                      putStrLn $ show def
                      pfpw' def
                  Nothing -> return e

pwpf :: Def -> IO Def
pwpf e = do
    putStrLn $ show e
    pwpf' e
    where
    pwpf' :: Def -> IO Def
    pwpf' e = let m = (defsnd >>> defapos >>> defsplit >>>
                       retx >>> retconst >>> elimx >>>
                       defext >>> defid >>>
                       univm >>> igualddm >>>
                       fusaom >>> absorcm >>> retin >>> univcata) e
              in case m of
                     (Just (s,def)) -> do
                         putStrLn s
                         putStrLn $ show def
                         pwpf' def
                     Nothing -> return e

-- ******************************************************************************************************** --
-- catamorfismos...
-- ******************************************************************************************************** --
-- in das listas...
inList = In :=: ((Const Nil) :\/: Cons)
-- out das listas...
outList :: Def
outList = ( (Out :@: ( Const Nil )) :=: ( Inl :@: Nada ) )
           :^:
           ( (Out :@: ( Op (:::) [(Var "h"),(Var "t")] )) :=: ( Inr :@: (Pair (Var "h") (Var "t")) ) )

-- passo recursivo sobre listas...
recList :: String -> Def
recList f = (Rec (Fun f)) :=: (Id :+: (Id :*: (Fun f)))

-- cata das listas...
cataList :: Def
cataList = (Cata (Fun "g")) :=: ((Fun "g") :.: ((Rec (Cata (Fun "g"))) :.: Out))

--exemplo::

lenCata1 = (Fun "length") :=: (Cata ((Const (NumInt 0)) :\/: (Fun "succ" :.: Snd)))

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- catamorfismo sobre definicoes (devolve Maybe)
cataDef :: (Show a, Show b) => (b -> b -> a, a -> a -> a) -> Catamorfismo b (Maybe a) Def
cataDef (eq,e) t exp'
    = (\c -> if ((show c) == (show exp')) then Nothing else Just c) (cata exp')
    where cata (e1 :=: e2) = eq (cataExp t e1) (cataExp t e2)
          cata (d1 :^: d2) = e (cata d1) (cata d2)

--catamorfismo sobre expressoes (devolve Maybe)
cataExp' :: (Show e) => Catamorfismo e (Maybe e) Exp
cataExp' (id',punct,bang,const',fst',snd',split,mul,inl,inr,either',plus,cond',fun,numint,var,pair,at,
          numfloat,numinteger,lambda,in',out,nil,cons,cata',rec,nada,op) e
    = (\c -> if ((show c) == (show e)) then Nothing else Just c) (cata e)
    where cata Id             = id'
          cata (l :.: r)      = punct (cata l) (cata r)
          cata Bang           = bang
          cata (Const exp')   = const' $ cata exp'
          cata Fst            = fst'
          cata Snd            = snd'
          cata (l :/\: r)     = split (cata l) (cata r)
          cata (l :*: r)      = mul (cata l) (cata r)
          cata Inl            = inl
          cata Inr            = inr
          cata (l :\/: r)     = either' (cata l) (cata r)
          cata (l :+: r)      = plus (cata l) (cata r)
          cata (Cond l c r)   = cond' (cata l) (cata c) (cata r)
          cata (Fun s)        = fun s
          cata (NumInt i)     = numint i
          cata (Var s)        = var s
          cata (Pair l r)     = pair (cata l) (cata r)
          cata (l :@: r)      = at (cata l) (cata r)
          cata (NumFloat i)   = numfloat i
          cata (NumInteger i) = numinteger i
          cata (Lambda e1 e2) = lambda (cata e1) (cata e2)
          cata In             = in'
          cata Out            = out
          cata Nil            = nil
          cata Cons           = cons
          cata (Cata exp')    = cata' $ cata exp'
          cata (Rec exp')     = rec $ cata exp'
          cata Nada           = nada
          cata (Op o l)       = op o $ map cata l

--catamorfismo sobre expressoes
cataExp :: (Show e) => Catamorfismo e e Exp
cataExp (id',punct,bang,const',fst',snd',split,mul,inl,inr,either',plus,cond',fun,num,var,pair,at,
          numfloat,numinteger,lambda,in',out,nil,cons,cata',rec,nada,op)
    = cata
    where cata Id           = id'
          cata (l :.: r)    = punct (cata l) (cata r)
          cata Bang         = bang
          cata (Const exp') = const' (cata exp')
          cata Fst          = fst'
          cata Snd          = snd'
          cata (l :/\: r)   = split (cata l) (cata r)
          cata (l :*: r)    = mul (cata l) (cata r)
          cata Inl          = inl
          cata Inr          = inr
          cata (l :\/: r)   = either' (cata l) (cata r)
          cata (l :+: r)    = plus (cata l) (cata r)
          cata (Cond l c r) = cond' (cata l) (cata c) (cata r)
          cata (Fun s)      = fun s
          cata (NumInt i)      = num i
          cata (Var s)      = var s
          cata (Pair l r)   = pair (cata l) (cata r)
          cata (l :@: r)    = at (cata l) (cata r)
          cata (NumFloat i)   = numfloat i
          cata (NumInteger i) = numinteger i
          cata (Lambda e1 e2) = lambda (cata e1) (cata e2)
          cata In             = in'
          cata Out            = out
          cata Nil            = nil
          cata Cons           = cons
          cata (Cata exp')    = cata' $ cata exp'
          cata (Rec exp')     = rec $ cata exp'
          cata Nada           = nada
          cata (Op o l)       = op o $ map cata l
-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- catamorfismos... leis... para listas...

-- ******************************************************************************************************** --
univcata' :: Regra
univcata' (f :^: g) = univcata' f >>= \x -> univcata' g >>= \y -> return ("{ univ cata }",((snd $ x) :^:(snd $ y)))
univcata' (f :=: (Cata g)) = let def = ((f :.: In) :=: (g :.: (recL $ saca f)))
                             in Just ("{ univ cata }",def)
univcata' _ = Nothing

univcata :: Regra
univcata (f :^: g) = univcata f >>= \x -> univcata g >>= \y -> return ("{ univ cata }",((snd $ x) :^:(snd $ y)))
univcata ((f :.: In) :=: (g :.: h)) = let def = (f :=: (Cata g))
                                              in Just ("{ univ cata }",def)
univcata _ = Nothing

-- ******************************************************************************************************** --
-- remocao do in
retin' :: Regra
retin' ((f :.: In):=: g) = let def = ((f :.: inL) :=: g)
                                   in Just ("{ ret in }",def)
retin' _ = Nothing

retin :: Regra
retin ((f :.: In) :=: h) = Nothing
retin ((f :.: (Const (Nil) :\/: Cons)) :=: h) = let def = ((f :.: In) :=: h)
                                        in Just ("{ ret in }",def)
retin _ = Nothing

-- ******************************************************************************************************** --
-- absorcao +
absorcm' :: Regra
absorcm' (f :=: ((g :\/: h) :.: (i :+: j))) = let def = (f :=: ((g :.: i) :\/: (h :.: j)))
                                              in Just ("{ absorc+ }",def)
absorcm' _ = Nothing

absorcm :: Regra
absorcm (f :=: ((g :.: i) :\/: (h :.: (j :.: l)))) = let def = (f :=: ((g :\/: (h :.: j)) :.: (i :+: l)))
                                                     in Just ("{ absorc+ }",def)
absorcm (f :=: ((g :.: i) :\/: (h :.: j))) = let def = f :=: ((g :\/: h) :.: (i :+: j))
                                             in Just ("{ absorc+ }",def)
absorcm _ = Nothing

-- ******************************************************************************************************** --
-- fusao +
fusaom' :: Regra
fusaom' ((f :.: (g :\/: h)) :=: i) = let def = (((f :.: g) :\/: (f :.: h)) :=: i)
                                     in Just ("{ fusao+ }",def)
fusaom' _ = Nothing

fusaom :: Regra
fusaom (((f :.: g) :\/: (r :.: h)) :=: i) | f == r = let def = ((f :.: (g :\/: h)) :=: i)
                                                     in Just ("{ fusao+ }",def)
fusaom _ = Nothing

-- ******************************************************************************************************** --
--igualdade +
igualddm' :: Regra
igualddm' ((g :\/: i) :=: (h :\/: j)) = let def = ((g :=: h) :^: (i :=: j))
                                        in Just ("{ igualdade+ }",def)
igualddm' _ = Nothing

igualddm :: Regra
igualddm ((g :=: h) :^: (i :=: j)) = let def = ((g :\/: i) :=: (h :\/: j))
                                     in Just ("{ igualdade+ }",def)
igualddm _ = Nothing

-- ******************************************************************************************************** --
-- pfpw
retconst' :: Regra
retconst' d = cataDef ((:=:),(:^:))
            (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
             NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ ret const }",x)
    where
    at f (Const g) = f :@: g
    at (Const f) g = f :@: g
    at f g = f :@: g

-- pwpf
retconst :: Regra
retconst e = cataDef ((:=:),(:^:))
             (Id,punct,Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) e >>= \x -> Just ("{ ret const }",x)
    where
        at f g@(NumInt _) = f :@: (Const g)
        at f@(NumInt _) g = (Const f) :@: g
        at f g@(NumFloat _) = f :@: (Const g)
        at f@(NumFloat _) g = (Const f) :@: g
        at f g@(NumInteger _) = f :@: (Const g)
        at  f@(NumInteger _) g = (Const f) :@: g
        at f g@(Nil) = f :@: (Const g)
        at f@(Nil) g = (Const f) :@: g
        at f g = f :@: g

        punct f g@(NumInt _) = f :.:(Const g)
        punct f@(NumInt _) g = (Const f) :.: g
        punct f g@(NumFloat _) = f :.: (Const g)
        punct f@(NumFloat _) g = (Const f) :.: g
        punct f g@(NumInteger _) = f :.: (Const g)
        punct  f@(NumInteger _) g = (Const f) :.: g
        punct f g@(Nil) = f :.: (Const g)
        punct f@(Nil) g = (Const f) :.: g
        punct f g = f :.: g

-- ******************************************************************************************************** --
retx' :: Regra
retx' d = cataDef (eq,(:^:))
           (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
            NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ ret * }",x)
    where
    eq i ((f :@: (g :*: h)) :@: (Pair (Var a) (Var b))) = i :=: (f :@: (Pair (g :@: (Var a)) (h :@: (Var b))))
    eq f g = f :=: g


retx :: Regra
retx d = cataDef ((:=:),(:^:))
           (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
            NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ ret * }",x)
    where
         at f (Pair c@(Var _) (a :@: b)) = f :.: ((Id :*: a) :@: (Pair c b))
         at f (Pair (a :@: b) (c :@: d)) = f :.: ((a :*: c) :@: (Pair b d))
         at f g = f :@: g

saca (Fun s) = s
inL = right inList
recL g = right $ recList g

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
defsnd' :: Regra
defsnd' d = cataDef ((:=:),(:^:))
             (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def snd }",x)
    where
    at (f :@: Snd) (Pair a b) = f :@: b
    at f g = f :@: g

defsnd :: Regra
defsnd d = cataDef (eq,(:^:))
              (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
               NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def snd }",x)
    where
       eq n@(f :@: (Pair (Var a) (Var b)))  (i :@: (g :@: (Var c))) | c == b = n :=: (i :@: (Snd :@: (Pair (Id :@: (Var a)) (g :@: (Var b)))))
       eq a b = a :=: b

-- ******************************************************************************************************** --
-- pwpf - definicao de identidade
defid :: Regra
defid d = cataDef (eq,(:^:))
              (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,pair,(:@:),
               NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def id }",x)
    where
        pair f b@(Var a) = Pair f Id
        pair b@(Var a) f = Pair Id f
        pair f g = Pair f g
        eq f a@(NumInt _) = f :=: (a :.: Id)
        eq f a@(NumFloat _) = f :=: (a :.: Id)
        eq f a@(NumInteger _) = f :=: (a :.: Id)
        eq f a@(Const _) = f :=: (a :.: Id)
        eq a b = a :=: b

-- pfpw - definicao de identidade
defid' :: Regra
defid' d = cataDef ((:=:),(:^:))
             (Id,punct,Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def id }",x)
    where
    punct f@(Const _) Id = f
    punct Id f@(Const _) = f
    punct f Id           = f
    punct Id f           = f
    punct f g            = f :.: g
    at f Id           = f
    at Id f           = f
    at f g            = f :@: g

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- pwpf - definicao de extensionalidade
defext :: Regra
defext d = cataDef ((:=:),(:^:))
             (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def ext }",x)
    where
    --pair f (Var _) = Pair f Id
    --pair (Var _) f = Pair Id f
    --pair f g = Pair f g
    at :: Exp -> Exp -> Exp
    at f (Var _) = f
    at (Var _) g = g
    at f (Pair (Var a) (Var b)) = f
    at f g = f :@: g

-- pfpw - definicao de extensionalidade
defext' :: Regra
defext' d = cataDef (eq,(:^:))
              (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
               NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def ext }",x)
    where
    eq l@(f :.: v@(Const _)) r = (l :@: Var "a") :=: (r :@: Var "a")
    eq f@((Fun _) :.: Cons) g = ((f :@: (Pair (Var "a") (Var "b"))) :=: (g :@: (Pair (Var "a") (Var "b"))))
    eq f g = let find = findVar f
             in if find == Nothing
                then (f :@: (Var "a")) :=: (g :@: (Var "a"))
                else f :=: g

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- pwpf -- definicao de eliminacao
elimx :: Regra
elimx e = let l = aux e
          in if l == e then Nothing else Just ("{ elim x }",l)
    where
    aux :: Def -> Def
    aux (l :^: r) = (aux l) :^: (aux r)
    aux a@(((fun :.: Cons) :@: pair@(Pair _ _)) :=: r) = a
    aux ((fun :@: pair@(Pair _ _)) :=: f) = (fun :@: (findl pair $ head $ findvars pair)) :=: (findr f $ head $ findvars pair)
    aux ((fun :.: f) :=: g) = let x = aux (f :=: g)
                              in (fun :.: (left x)) :=: (right x)
    aux a = a

    findl :: Exp -> (String,String,String) -> Exp
    findl (Pair (Var x) (Var y)) (s1,s2,s3) | x == s1 && y == s2 = Var s3
    findl (Pair l r) t = Pair (findl l t) (findl r t)
    findl a _ = a

    findvars :: Exp -> [(String,String,String)]
    findvars (Pair (Var x) (Var y)) = [(x,y,(x++"'"))]
    findvars (Pair f g) = (findvars f) ++ (findvars g)
    findvars (Var _) = []

    findr :: Exp -> (String,String,String) -> Exp
    findr (Var x) (s1,s2,s3) | x == s1 = Fst :@: (Var s3)
    findr (Var x) (s1,s2,s3) | x == s2 = Snd :@: (Var s3)
    findr (f :@: r) s = (f :@: (findr r s))
    findr (Pair l r) t = Pair (findr l t) (findr r t)
    findr a _ = a

-- pfpw - definicao de eliminacao
elimx' :: Regra
elimx' (l :^: r) = (elimx' l) >>= \(_,x) -> (elimx' r) >>= \(_,y) -> return ("{ elim x }",(x :^: y))
elimx' def@((f :@: v):=: r) = let vars  = head $ nub $ geraVars r
                                  evalr = avaliar r vars
                              in  if r == evalr
                                  then Nothing
                                  else Just ("{ elim x }",((f :@: (avalial v vars)) :=: evalr))
    where
    avaliar :: Exp -> (String,String,String) -> Exp
    avaliar v@(Var _) _ = v
    avaliar (Pair l r) t   = Pair (avaliar l t) (avaliar r t )
    avaliar (l :@: (Var x)) (a,b,c) | x == c = remlast l (a,b,c)
    avaliar a _ = a

    remlast :: Exp -> (String,String,String) -> Exp
    remlast Bang (_,_,c) = Bang :@: Var c
    remlast Id (_,_,c) = Id :@: Var c
    remlast Fst (a,b,c) = Var a
    remlast Snd (a,b,c) = Var b
    remlast Inl (a,b,c) = Inl :@: (Var c)
    remlast Inr (a,b,c) = Inr :@: (Var c)
    remlast (f :@: Inr) (_,_,c) = (f :@: Inr) :@: (Var c)
    remlast (f :@: Inl) (_,_,c) = (f :@: Inl) :@: (Var c)
    remlast (f :@: Snd) (_,b,c) = f :@: (Var b)
    remlast (f :@: Fst) (a,_,c) = f :@:(Var a)
    remlast (f :@: Id) (_,_,c) = (f :@: Id) :@: (Var c)
    remlast (f :@: Bang) (_,_,c) = (f :@: Bang) :@: (Var c)
    remlast (f :@: g) t = (remlast f t) :@: (remlast g t)
    remlast a _ = a

    geraVars :: Exp -> [(String,String,String)]
    geraVars (Var x) = []
    geraVars (f :@: (Var x)) = let op = (+) . ord . (\[s] -> s)
                                   a  = [chr (op x 2)]
                                   b  = [chr (op x 3)]
                               in  [(a,b,x)]
    geraVars (f :@: g)  = geraVars g
    geraVars (Pair l r) = geraVars l ++ geraVars r

    varOcupada :: Exp -> (String, String, String) -> Bool
    varOcupada e (_,_,s) = s `elem` (listaVars e)

    listaVars :: Exp -> [String]
    listaVars (Var x)    = [x]
    listaVars (f :@: g)  = listaVars g
    listaVars (Pair l r) = listaVars l ++ listaVars r

    avalial :: Exp -> (String,String,String) -> Exp
    avalial var@(Var v) (a,b,c) | v == c    = Pair (Var a) (Var b)
                                | otherwise = var
    avalial (Pair l r) t = Pair (avalial l t) (avalial r t)

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- pwpf - definicao de split
defsplit :: Regra
defsplit d = cataDef ((:=:),(:^:))
               (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,pair,(:@:),
                NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def split }",x)
    where pair (f :@: (Var x)) (g :@: (Var y)) | x == y = (f :/\: g) :@: (Var x)
          pair (Var x) (g :@: (Var y)) | x == y = (Id :/\: g) :@: (Var x)
          pair (f :@: (Var x)) (Var y) | x == y = (f :/\: Id) :@: (Var x)
          pair (f :@: (Var x)) (g :.: (h :@: (Var y))) | x == y = (f :/\: (g :.: h)) :@: (Var x)
          pair (f :.: (g :@: (Var y))) (h :@: (Var x)) | x == y = ((f :.: g) :/\: h) :@: (Var x)
          pair (f :.: (g :@: (Var y))) (Var x) = ((f :.: g) :/\: Id) :@: (Var x)
          pair f g = Pair f g

findVar :: Exp -> Maybe Exp
findVar = cataExp' (Id,punct,Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,pair,at',
                    NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op)
    where pair _ v@(Var x) = v
          pair v@(Var x) _ = v
          at' _ v@(Var x)  = v
          at' v@(Var x) _  = v
          at' f g = f :@: g
          punct _ v@(Var x)  = v
          punct v@(Var x) _  = v
          punct f g = f :.: g

-- pfpw - definicao de split
defsplit' :: Regra
defsplit' (f :^: g) = defsplit' f >>= \(_,x) -> defsplit' g >>= \(_,y) -> return ("{ def split }",(x :^: y))
defsplit' (f :=: e) = (cataExp' (Id,(:.:),Bang,Const,Fst,Snd,
                        split_ enc,(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
                        NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) e) >>= \x -> return ("{ def split }",(f :=: x))
    where
    enc = fromJust $ findVar e
    at p@(Pair _ _) v@(Var x) = p
    at v@(Var x) p@(Pair _ _) = p
    at l v@(Var x) = (l :@: v)
    at f g = f :@: g
    split_ s l r | temVar l         && temVar r         = Pair l r
                 | temVar l         && (not $ temVar r) = Pair l (r :@: s)
                 | (not $ temVar l) && temVar r         = Pair (l :@: s) r
                 | (not $ temVar l) && (not $ temVar r) = Pair (l :@: s) (r :@: s)
        where temVar e = findVar e /= Nothing

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- pwpf - definicao de apos
defapos :: Regra
defapos d = cataDef ((:=:),(:^:))
               (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
                NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def apos }",x)
    where at f v@(Var _) = f :@: v
          at f pair@(Pair _ _) = f :@: pair
          at f g         = f :.: g

-- pfpw - definicao de apos
defapos' :: Regra
defapos' d = cataDef ((:=:),(:^:))
               (Id,punct,Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
                NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def apos }",x)
    where punct f s@(Var x) = f :@: s
          punct f g         = f :@: g
-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- pwpf - universal+
univm :: Regra
univm d = cataDef ((:=:),e)
            (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
             NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ univ + }",x)
    where
    e :: Def -> Def -> Def
    e ((k :.: Inl) :=: f) ((k2 :.: Inr) :=: g) | k == k2 = k :=: (f :\/: g)
    e ((k :.: (i :.: Inl)) :=: f) ((k2 :.: (h :.: Inr)) :=: g) | (k == k2 && i == h) = (k :.: i) :=: (f :\/: g)
    e f g = f :^: g

-- pfpw - universal+
univm' :: Regra
univm' d = cataDef (eq,(:^:))
             (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ univ + }",x)
    where
    eq k (f :\/: g) = ((k :.: Inl) :=: f) :^: ((k :.: Inr) :=: g)
    eq a      b            = a :=: b

-- ******************************************************************************************************** --
-- funcoes auxiliares
right (_ :=: b) = b
left (a :=: _) = a

-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
-- testes
revCata1 = Fun "rev" :=: Cata ((Const Nil) :\/: (Lambda (Pair (Var "n") (Var "l")) (Op (::++::) [(Var "l"), Cons :@: (Var "n")])))
revCata2 = Fun "rev" :=: Cata ((Const Nil) :\/: (Fun "snoc"))

-- ******************************************************************************************************** --
assocr'' :: Def
assocr'' = ((Fun "assocr") :@: (Pair (Pair (Var "a") (Var "b")) (Pair (Var "c") (Var "d"))))
       :=:
       (Pair ((Snd :.: Snd) :@: (Var "a''"))
              (Pair ((Snd :.: Snd) :@: (Var "a''")) (Pair ((Snd :.: Snd) :@: (Var "a''")) ((Snd :.: Snd) :@: (Var "a''")))))
-- ******************************************************************************************************** --
swap' :: Def
swap' = ((Fun "swap") :@: (Pair (Var "a") (Var "b")))
       :=:
       (Pair (Var "b") (Var "a"))
-- ******************************************************************************************************** --
coswap' =
          (((Fun "coswap") :@: (Inl :@: (Var "x"))) :=: (Inr :@: (Var "x")))
          :^:
          (((Fun "coswap") :@: (Inr :@: (Var "x"))) :=: (Inl :@: (Var "x")))
-- ******************************************************************************************************** --
assocr' :: Def
assocr' = ((Fun "assocr") :@: (Pair (Pair (Var "a") (Var "b")) (Var "c")))
         :=:
         (Pair (Var "a") (Pair(Var "b") (Var "c")))
-- ******************************************************************************************************** --
assocl' = ((Fun "assocl") :@: (Pair (Var "a") (Pair (Var "b") (Var "c"))))
          :=:
          (Pair (Pair (Var "a") (Var "b")) (Var "c"))
-- ******************************************************************************************************** --
undistr' =
          (((Fun "undistr") :@: (Inl :@: (Pair (Var "x") (Var "y")))) :=: (Pair (Var "x") (Inl :@: (Var "y"))))
          :^:
          (((Fun "undistr") :@: (Inr :@: (Pair (Var "x") (Var "y")))) :=: (Pair (Var "x") (Inr :@: (Var "y"))))
-- ******************************************************************************************************** --
coassocl' =
    (((((Fun "coassocl") :@: (Inl :@: (Var "x"))) :=: (Inl :@: (Inl :@: (Var "x")))))
    :^:
    (((Fun "coassocl") :@: (Inr :@: (Inl :@: (Var "x")))) :=: (Inl :@: (Inr :@: (Var "x")))
    :^:
    (((Fun "coassocl") :@: (Inr :@: (Inr :@: (Var "x")))) :=: (Inr :@: (Var "x")))))
-- ******************************************************************************************************** --
coassocr' =
    (((((Fun "coassocr") :@: (Inl :@: ( Inl :@: (Var "x")))) :=: (Inl :@: (Var "x")))
    :^:
    ((((Fun "coassocr") :@: (Inl :@: ( Inr :@: (Var "x")))) :=: (Inr :@: (Inl :@: (Var "x"))))))
    :^:
    (((Fun "coassocr") :@: ( Inr :@: (Var "x"))) :=: (Inr :@: (Inr :@: (Var "x")))))
-- ******************************************************************************************************** --
distwo =
    ((Fun "distwo" :@: (Inl :@: (Var "x"))) :=: (Pair (Inl :@: (Bang :@: (Var "x"))) (Var "x")))
    :^:
    ((Fun "distwo" :@: (Inr :@: (Var "x"))) :=: (Pair (Inr :@: (Bang :@: (Var "x"))) (Var "x")))
-- ******************************************************************************************************** --
-- ******************************************************************************************************** --
--parser...
bla = ParseOk (HsModule (SrcLoc {srcFilename = "<unknown>", srcLine = 1, srcColumn = 1}) (Module "Main") (Just [HsEVar (UnQual (HsIdent "main"))]) [] [HsFunBind [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 1, srcColumn = 1}) (HsIdent "swap") [HsPTuple [HsPVar (HsIdent "a"),HsPVar (HsIdent "b")]] (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent "b")),HsVar (UnQual (HsIdent "a"))])) []],HsFunBind [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 3, srcColumn = 1}) (HsIdent "coswap") [HsPParen (HsPApp (UnQual (HsIdent "Left")) [HsPVar (HsIdent "x")])] (HsUnGuardedRhs (HsApp (HsCon (UnQual (HsIdent "Right"))) (HsVar (UnQual (HsIdent "x"))))) [],HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 4, srcColumn = 1}) (HsIdent "coswap") [HsPParen (HsPApp (UnQual (HsIdent "Right")) [HsPVar (HsIdent "x")])] (HsUnGuardedRhs (HsApp (HsCon (UnQual (HsIdent "Left"))) (HsVar (UnQual (HsIdent "x"))))) []],HsFunBind [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 6, srcColumn = 1}) (HsIdent "assocr") [HsPTuple [HsPTuple [HsPVar (HsIdent "a"),HsPVar (HsIdent "b")],HsPVar (HsIdent "c")]] (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent "a")),HsTuple [HsVar (UnQual (HsIdent "b")),HsVar (UnQual (HsIdent "c"))]])) []],HsFunBind [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 8, srcColumn = 1}) (HsIdent "assocl") [HsPTuple [HsPVar (HsIdent "a"),HsPTuple [HsPVar (HsIdent "b"),HsPVar (HsIdent "c")]]] (HsUnGuardedRhs (HsTuple [HsTuple [HsVar (UnQual (HsIdent "a")),HsVar (UnQual (HsIdent "b"))],HsVar (UnQual (HsIdent "c"))])) []],HsFunBind [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 10, srcColumn = 1}) (HsIdent "undistr") [HsPParen (HsPApp (UnQual (HsIdent "Left")) [HsPTuple [HsPVar (HsIdent "x"),HsPVar (HsIdent "y")]])] (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent "x")),HsApp (HsCon (UnQual (HsIdent "Left"))) (HsVar (UnQual (HsIdent "y")))])) [],HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 11, srcColumn = 1}) (HsIdent "undistr") [HsPParen (HsPApp (UnQual (HsIdent "Right")) [HsPTuple [HsPVar (HsIdent "x"),HsPVar (HsIdent "y")]])] (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent "x")),HsApp (HsCon (UnQual (HsIdent "Right"))) (HsVar (UnQual (HsIdent "y")))])) []]])

imprime :: ParseResult HsModule -> String
imprime (ParseOk a)       = prettyPrint a
imprime (ParseFailed _ s) = s

ff = [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 1, srcColumn = 1}) (HsIdent "swap") [HsPTuple [HsPVar (HsIdent "a"),HsPVar (HsIdent "b")]] (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent "b")),HsVar (UnQual (HsIdent "a"))])) []]

fff = [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 3, srcColumn = 1}) (HsIdent "coswap") [HsPParen (HsPApp (UnQual (HsIdent "Left")) [HsPVar (HsIdent "x")])] (HsUnGuardedRhs (HsApp (HsCon (UnQual (HsIdent "Right"))) (HsVar (UnQual (HsIdent "x"))))) [],HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 4, srcColumn = 1}) (HsIdent "coswap") [HsPParen (HsPApp (UnQual (HsIdent "Right")) [HsPVar (HsIdent "x")])] (HsUnGuardedRhs (HsApp (HsCon (UnQual (HsIdent "Left"))) (HsVar (UnQual (HsIdent "x"))))) []]

ffff = [HsMatch (SrcLoc {srcFilename = "<unknown>", srcLine = 6, srcColumn = 1}) (HsIdent "assocr") [HsPTuple [HsPTuple [HsPVar (HsIdent "a"),HsPVar (HsIdent "b")],HsPVar (HsIdent "c")]] (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent "a")),HsTuple [HsVar (UnQual (HsIdent "b")),HsVar (UnQual (HsIdent "c"))]])) []]

parse :: ParseResult HsModule -> [Def]
parse (ParseOk m) = f m
  where
  f :: HsModule -> [Def]
  f (HsModule _ _ _ [] hsDecl) =
      let m :: [HsMatch] -> Def
          m [a]   = h a
          m [a,b] = (h a) :^: (h b)
      in  map (\(HsFunBind fun) -> m fun) hsDecl
    where
    h :: HsMatch -> Def
    h (HsMatch _ (HsIdent nomeFun) hsPat hsRhs []) =
        ((Fun nomeFun) :@: (avaliaP hsPat)) :=: (avaliaD hsRhs)

avaliaP :: [HsPat] -> Exp
avaliaP [HsPParen (HsPApp (UnQual (HsIdent f)) [HsPTuple [HsPVar (HsIdent v1),HsPVar (HsIdent v2)]])]
    | f == "Left" = Inl :@: (Pair (Var v1) (Var v2))
    | f == "Right" = Inr :@: (Pair (Var v1) (Var v2))
avaliaP [HsPTuple [HsPVar (HsIdent v1), HsPVar (HsIdent v2)]] = Pair (Var v1) (Var v2)
avaliaP [HsPTuple [HsPVar (HsIdent v1),HsPTuple [HsPVar (HsIdent v2),HsPVar (HsIdent v3)]]] = Pair (Var v1) (Pair (Var v2) (Var v3))
avaliaP [HsPTuple [HsPTuple [HsPVar (HsIdent v1),HsPVar (HsIdent v2)],HsPVar (HsIdent v3)]] = Pair (Pair (Var v1) (Var v2)) (Var v3)
avaliaP [HsPParen (HsPApp (UnQual (HsIdent f)) [HsPVar (HsIdent v1)])]
    | f == "Left" = Inl :@: (Var v1)
    | f == "Right" = Inr :@: (Var v1)

avaliaD :: HsRhs -> Exp
avaliaD (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent v1)),HsApp (HsCon (UnQual (HsIdent f))) (HsVar (UnQual (HsIdent v2)))]))
    | f == "Left" = Pair (Var v1) (Inl :@: (Var v2))
    | f == "Right" = Pair (Var v1) (Inr :@: (Var v2))
avaliaD (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent v1)),HsTuple [HsVar (UnQual (HsIdent v2)),HsVar (UnQual (HsIdent v3))]]))
    = Pair (Var v1) (Pair (Var v2) (Var v3))
avaliaD (HsUnGuardedRhs (HsTuple [HsTuple [HsVar (UnQual (HsIdent v1)),HsVar (UnQual (HsIdent v2))],HsVar (UnQual (HsIdent v3))]))
    = Pair (Pair (Var v1) (Var v2)) (Var v3)
avaliaD (HsUnGuardedRhs (HsTuple [HsVar (UnQual (HsIdent v1)),HsVar (UnQual (HsIdent v2))])) = Pair (Var v1) (Var v2)
avaliaD (HsUnGuardedRhs (HsApp (HsCon (UnQual (HsIdent f))) (HsVar (UnQual (HsIdent v1)))))
    | f == "Left" = Inl :@: (Var v1)
    | f == "Right" = Inr :@: (Var v1)
