\documentclass[11pt,a4paper]{article}
\usepackage{graphicx}
\usepackage{alltt}
\usepackage[portuges]{babel}
\usepackage[latin1]{inputenc}
\usepackage{color}
\usepackage[portuges]{minitoc}
\usepackage{fancyhdr}
\usepackage{listings}
\usepackage{multicol}

\setlength{\textwidth}{16.5cm}
\setlength{\textheight}{24cm}
\setlength{\parindent}{1em}
\setlength{\parskip}{0pt plus 1pt}
\setlength{\oddsidemargin}{0cm}
\setlength{\evensidemargin}{0cm}
\setlength{\topmargin}{-1.1cm}
\setlength{\headsep}{20pt}
\setlength{\columnsep}{1.5pc}
\setlength\columnseprule{.4pt}
\setlength\premulticols{6\baselineskip}
\pagestyle{fancy}

\definecolor{gray_ulisses}{gray}{0.55}
\definecolor{castanho_ulisses}{rgb}{0.71,0.33,0.14}
\definecolor{preto_ulisses}{rgb}{0.41,0.20,0.04}
\definecolor{green_ulises}{rgb}{0.2,0.75,0}

\lstdefinelanguage{txt}
{
       basicstyle=\ttfamily\scriptsize,
       showstringspaces=false,
       numbers=left,
       numberstyle=\tiny,
       numberblanklines=true,
       showspaces=false,
       showtabs=false
}

\lstdefinelanguage{HaskellUlisses}
{
	basicstyle=\ttfamily\scriptsize,
	%backgroundcolor=\color{yellow},
	%frameshape={RYRYNYYYY}{yny}{yny}{RYRYNYYYY}, %contornos... muito nice...
	sensitive=true,
	morecomment=[l][\color{gray_ulisses}\scriptsize]{--},
	morecomment=[s][\color{gray_ulisses}\scriptsize]{\{-}{-\}},
	morestring=[b]",
	stringstyle=\color{red},
	showstringspaces=false,
	numbers=left,
	firstnumber=\thelstnumber,
	numberstyle=\tiny,
	numberblanklines=true,
	showspaces=false,
	showtabs=false,
	xleftmargin=15pt,
	xrightmargin=-20pt,
	emph=
	{[1]
		FilePath,IOError,abs,acos,acosh,all,and,any,appendFile,approxRational,asTypeOf,asin,
		asinh,atan,atan2,atanh,basicIORun,break,catch,ceiling,chr,compare,concat,concatMap,
		const,cos,cosh,curry,cycle,decodeFloat,denominator,digitToInt,div,divMod,drop,
		dropWhile,either,elem,encodeFloat,enumFrom,enumFromThen,enumFromThenTo,enumFromTo,
		error,even,exp,exponent,fail,filter,flip,floatDigits,floatRadix,floatRange,floor,
		fmap,foldl,foldl1,foldr,foldr1,fromDouble,fromEnum,fromInt,fromInteger,fromIntegral,
		fromRational,fst,gcd,getChar,getContents,getLine,head,id,inRange,index,init,intToDigit,
		interact,ioError,isAlpha,isAlphaNum,isAscii,isControl,isDenormalized,isDigit,isHexDigit,
		isIEEE,isInfinite,isLower,isNaN,isNegativeZero,isOctDigit,isPrint,isSpace,isUpper,iterate,
		last,lcm,length,lex,lexDigits,lexLitChar,lines,log,logBase,lookup,map,mapM,mapM_,max,
		maxBound,maximum,maybe,min,minBound,minimum,mod,negate,not,notElem,null,numerator,odd,
		or,ord,otherwise,pi,pred,primExitWith,print,product,properFraction,putChar,putStr,putStrLn,quot,
		quotRem,range,rangeSize,read,readDec,readFile,readFloat,readHex,readIO,readInt,readList,readLitChar,
		readLn,readOct,readParen,readSigned,reads,readsPrec,realToFrac,recip,rem,repeat,replicate,return,
		reverse,round,scaleFloat,scanl,scanl1,scanr,scanr1,seq,sequence,sequence_,show,showChar,showInt,
		showList,showLitChar,showParen,showSigned,showString,shows,showsPrec,significand,signum,sin,
		sinh,snd,span,splitAt,sqrt,subtract,succ,sum,tail,take,takeWhile,tan,tanh,threadToIOResult,toEnum,
		toInt,toInteger,toLower,toRational,toUpper,truncate,uncurry,undefined,unlines,until,unwords,unzip,
		unzip3,userError,words,writeFile,zip,zip3,zipWith,zipWith3
	},
	emphstyle={[1]\color{blue}},
	emph=
	{[2]
		Bool,Char,Double,Either,Float,IO,Integer,Int,Maybe,Ordering,Rational,Ratio,ReadS,ShowS,String
	},
	emphstyle={[2]\color{castanho_ulisses}},
	emph=
	{[3]
		case,class,data,deriving,do,else,if,import,in,infixl,infixr,instance,let,
		module,of,primitive,then,type,where
	},
	emphstyle={[3]\color{preto_ulisses}\textbf},
	emph=
	{[4]
		quot,rem,div,mod,elem,notElem,seq
	},
	emphstyle={[4]\color{castanho_ulisses}\textbf},
	emph=
	{[5]
		EQ,False,GT,Just,LT,Left,Nothing,Right,True,Show,Eq,Ord,Num
	},
	emphstyle={[5]\color{preto_ulisses}\textbf}
}

\lstnewenvironment{code}
{\textbf{Código Haskell} \hspace{1cm} \hrulefill \lstset{language=HaskellUlisses}}
{\hrule\smallskip}

%% stuff do minitoc %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\setcounter{secttocdepth}{10}
\setlength{\stcindent}{24pt}
\renewcommand{\stcfont}{\small\rm}
\renewcommand{\stcSSfont}{\small\bf}
%\newenvironment{mtc}{\secttoc\sectlof\sectlot}{\pagebreak}
%                        ^       ^        ^
%                    conteudos  figuras  tabelas
\newenvironment{mtc}{\secttoc\sectlof}{\pagebreak}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\title{\sf  Métodos de Programação I \\
\begin{tabular}{c}
	\includegraphics[width=.1\textwidth]{stuff/uminho.jpg}
	\includegraphics[width=.07\textwidth]{stuff/informatica.jpg}\\
	{\small Universidade do Minho}, {\small LESI}\\
	{\small Ano lectivo 2006/2007}\\
	{\small Trabalho Prático N$º$1}\\
\end{tabular}
}
\author{
	{\small Mário Ulisses Pires Araujo Costa - 43175} \and
	{\small Rami Galil Shashati - 43166} \and
	{\small Vasco Almeida Ferreira - 43207}}
\date{{\small \today}}

\begin{document}

\maketitle

\begin{abstract}
Este trabalho foi implementado no paradigma funcional, em linguagem \textbf{Haskell}.\\
O objectivo é desenvolver um conversor entre \textit{poinwise} e \textit{point-free}.
\end{abstract}

\dosecttoc
%\dosectlof
\doparttoc
%\dopartlof
\tableofcontents
%\listoffigures
\pagebreak

\section{Introdu\c c\~ao}
\begin{code}
--
--  Métodos de Programação I
--  LESI, Universidade do Minho
--
--  conversor pwpf e pfpw
--
--  2006/2007
--
--  autores:
--    Mário Ulisses Pires Araujo Costa - 43185
--    Rami Galil Shashati              - 43166
--    Vasco Almeida Ferreira           - 43207
--

module Trab2 where

import Char
import List
import Maybe
--import Mpi
import Language.Haskell.Parser
import Language.Haskell.Syntax
import Language.Haskell.Pretty
import IO

infixr 6 >>>
\end{code}

Este Trabalho foi realizado no âmbito da disciplina de Métodos de Programação I, da Licenciatura em Engenharia de Sistemas e
Informática da Universidade do Minho.\\
O Objectivo deste trabalho é desenvolver um conversor entre \textit{poinwise} e \textit{point-free}, para todas as funções dadas nas aulas práticas.\\
Este relatório contem as diferentes fases de desenvolvimento do aplicação, a saber: análise do problema, escolha/descoberta
de algoritmos, implementação, testes e documentação.

\section{An\'alise e Especifica\c c\~ao}
\begin{mtc}
\subsection{Descri\c c\~ao informal do problema}
Como já vimos nas aulas práticas, e possível converter programas do estilo pointwise para o estilo point-free usando calculo algebrico.
Por exemplo, a funcao assocr.\\

\lstset{language=txt}
assocr :: ((a, b), c) -> (a, (b, c))\\
assocr ((x, y),z) = (x, (y, z))\\

que convertida ficaria desta forma:\\

\begin{math}
assocr ((x, y), z) = (x, (y, z))\\
\Leftrightarrow \{ ELIM-x \}\\
assocr (w, z) = (fst w, (snd w, z))\\
\Leftrightarrow \{ ELIM-\times \}\\
assocr x = (fst (fst x), (snd (fst x), snd x))\\
\Leftrightarrow \{ DEF-\circ\}\\
assocr x = ((fst \circ fst) x, ((snd \circ fst) x, snd x))\\
\Leftrightarrow \{ DEF-\bigtriangleup\}\\
assocr x = ((fst \circ fst) x, (snd \circ fst \bigtriangleup snd) x)\\
\Leftrightarrow \{ DEF-\bigtriangleup\}\\
assocr x = (fst \circ fst \bigtriangleup (snd \circ fst \bigtriangleup snd)) x\\
\Leftrightarrow \{ EXT-=\}\\
assocr = fst \circ fst \bigtriangleup (snd \circ fst \bigtriangleup snd)\\
\Leftrightarrow \{ NAT-id\}\\
assocr = fst \circ fst \bigtriangleup (snd \circ fst \bigtriangleup id \circ snd)\\
\Leftrightarrow \{ DEF-\times \}\\
assocr = fst \circ fst \bigtriangleup (snd \times id)\\
\end{math}

\subsection{Especifica\c c\~ao dos Requisitos}
Para levar a cabo este trabalho, foram necessários conhecimentos da linguagem \textbf{Haskell}, do acompanhamento
das aulas teórico-práticas afim de saber em detalhe como se converte de pwpf e virse versa,
assim como o domínio de \LaTeXe{} e alguns dos seus pacotes para a elaboração deste relatório.

\subsubsection{Requisitos fundamentais}
Na base de desenvolvimento deste trabalho estão presentes duas ideias fundamentais. A primeira delas, consiste no Parsing da linguagem 
Haskell um outro tipo de dados  chamamos \textbf{Def}. Posteriormente será feita uma conversao de X para Y sendo estas variaveis
ora poinwise ora point-free\ldots
\end{mtc}

\section{Concep\c c\~ao/Desenho da Resolu\c c\~ao}
\begin{mtc}
\subsection{pwpf \& pfpw}

Todo o código listado abaixo irá ser necessário para que consigamos usar a função $(>>>)$, que é a base para a resolução do nosso 
problema. Com esta função conseguimos compôr regras\ldots

\begin{code}
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
    pfpw' e = let m = (univcata' >>> retin'    >>> absorcm'  >>>
                       fusaom'   >>> igualddm' >>> retconst' >>>
                       retx'     >>> univm'    >>> defext'   >>>
                       defsplit' >>> defapos'  >>> elimx'    >>>
                       defsnd'   >>> defid') e
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
    pwpf' e = let m = (defsnd >>> defapos  >>> defsplit >>>
                       retx   >>> retconst >>> elimx    >>>
                       defext >>> defid    >>> igualddm >>>
                       fusaom >>> absorcm  >>> retin    >>>
                       univm  >>> univcata) e
              in case m of
                     (Just (s,def)) -> do
                         putStrLn s
                         putStrLn $ show def
                         pwpf' def
                     Nothing -> return e

-- in das listas...
inList = In :=: ((Const Nil) :\/: Cons)
-- passo recursivo sobre listas...
recList :: String -> Def
recList f = (Rec (Fun f)) :=: (Id :+: (Id :*: (Fun f)))
\end{code}

\subsection{Estruturas de Dados e respectivas instâncias}
De seguida, vamos mostrar as estruturas de dados base deste trabalho e suas instâncias, nomeadamente;

\subsubsection{Def}
\begin{code}
data Def = Exp :=: Exp | Def :^: Def
    deriving Eq

instance Show Def where
    show (exp1 :=: exp2) = show exp1 ++ " = " ++ show exp2
    show (def1 :^: def2) = show def1 ++ "\n" ++ show def2
\end{code}

\subsubsection{Exp}
\begin{code}
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
    deriving Eq
\end{code}

Instância de Show para o tipo de dados Exp.\\

\begin{code}
instance Show Exp where
    show Id = "id"
    show Bang = "()"
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
    show (NumFloat n) = show n
    show (NumInteger n) = show n
    show (NumInt i) = show i
    show (Var s) = s
    show (Pair exp1 exp2) = "(" ++ show exp1 ++ "," ++ show exp2 ++ ")"
    show (exp1 :@: exp2) = show exp1 ++ " " ++ show exp2
    show (Lambda exp1 exp2) = "(\\" ++ show exp1 ++ "->" ++ show exp2 ++ ")"
    show In = "in "
    show Out = "out "
    show Nil = "[] "
    show Cons = []
    show (Cata exp1) = "cata " ++ show exp1
    show (Rec exp1)  = "rec " ++ show exp1
    show Nada        = "()"
    show (Op op expl) | length expl == 0 = "(" ++ show op ++ ")"
                      | length expl == 1 = "(" ++ show op ++ show (expl !! 0) ++ ")"
                      | length expl == 2 = "(" ++ show (expl !! 0) ++ show op ++ show (expl !! 1) ++")"
\end{code}

\subsubsection{Ops}
\begin{code}
data Ops = (:::) | (::++::)
         -- operacoes sobre numerarios...
         | (::+::) | (::-::)
         | (::*::) | (::/::)
         | (::>::)
    deriving Eq

instance Show Ops where
    show (:::) = ":"
    show (::++::) = "++"
    show (::+::) = "+"
    show (::-::) = "-"
    show (::*::) = "*"
    show (::/::) = "/"
\end{code}

\subsubsection{Tipos de dados auxiliares}
\begin{code}
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
\end{code}

\end{mtc}
\section{Estrutura da Aplica\c c\~ao}
\begin{mtc}
\subsection{Catamorfismos}
Para nos facilitar a implementação das regras decidimos implementar um catamorfismo sobre os nossos
tipos de dados (\textbf{Def} e \textbf{Exp}).

\begin{code}
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
\end{code}

\subsection{Regras pwpf}
O comversor pwpf tem como base regras, regras essas que trabalham sobre o nosso tipo \textbf{Regras}:\\

\subsubsection{Universal Cata}
\begin{code}
univcata :: Regra
univcata (f :^: g) = univcata f >>= \x -> univcata g >>= \y -> return ("{ univ cata }",((snd $ x) :^:(snd $ y)))
univcata ((f :.: (Fun "in")) :=: (g :.: h)) = let def = (f :=: (Cata g))
                                              in Just ("{ univ cata }",def)
univcata _ = Nothing
\end{code}

\subsubsection{Ret in}
\begin{code}
retin :: Regra
retin (f :.: (Fun "in") :=: h) = Nothing
retin ((f :.: (Const (Nil) :\/: Cons)) :=: h) = let def = (f :.: (Fun "in") :=: h)
                                        in Just ("{ ret in }",def)
retin _ = Nothing
\end{code}

\subsubsection{Absorção +}
\begin{code}
absorcm :: Regra
absorcm (f :=: ((g :.: i) :\/: (h :.: (j :.: l)))) = let def = (f :=: ((g :\/: (h :.: j)) :.: (i :+: l)))
                                                     in Just ("{ absorc+ }",def)
absorcm (f :=: ((g :.: i) :\/: (h :.: j))) = let def = f :=: ((g :\/: h) :.: (i :+: j))
                                             in Just ("{ absorc+ }",def)
absorcm _ = Nothing
\end{code}

\subsubsection{Fusão +}
\begin{code}
fusaom :: Regra
fusaom (((f :.: g) :\/: (r :.: h)) :=: i) | f == r = let def = ((f :.: (g :\/: h)) :=: i)
                                                     in Just ("{ fusao+ }",def)
fusaom _ = Nothing
\end{code}

\subsubsection{Igualdade +}
\begin{code}
igualddm :: Regra
igualddm ((g :=: h) :^: (i :=: j)) = let def = ((g :\/: i) :=: (h :\/: j))
                                     in Just ("{ igualdade+ }",def)
igualddm _ = Nothing
\end{code}

\subsubsection{Ret Const}
\begin{code}
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
\end{code}

\subsubsection{Ret x}
\begin{code}
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
\end{code}

\subsubsection{Definiçaõ de Snd}
\begin{code}
defsnd :: Regra
defsnd d = cataDef (eq,(:^:))
              (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
               NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def snd }",x)
    where
       eq n@(f :@: (Pair (Var a) (Var b)))  (i :@: (g :@: (Var c)))
           | c == b = n :=: (i :@: (Snd :@: (Pair (Id :@: (Var a)) (g :@: (Var b)))))
       eq a b = a :=: b
\end{code}

\subsubsection{Definiçaõ de Id}
\begin{code}
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
\end{code}

\subsubsection{Definiçaõ de extensionalidade}
\begin{code}
defext :: Regra
defext d = cataDef ((:=:),(:^:))
             (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def ext }",x)
    where
    at :: Exp -> Exp -> Exp
    at f (Var _)                = f
    at (Var _) g                = g
    at f (Pair (Var a) (Var b)) = f
    at f g                      = f :@: g
\end{code}

\subsubsection{Eliminação x}
\begin{code}
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
\end{code}

\subsubsection{Definição de Split}
\begin{code}
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
\end{code}

\subsubsection{Definição de apos}
\begin{code}
defapos :: Regra
defapos d = cataDef ((:=:),(:^:))
               (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
                NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def apos }",x)
    where at f v@(Var _) = f :@: v
          at f pair@(Pair _ _) = f :@: pair
          at f g         = f :.: g
\end{code}

\subsubsection{Universal +}
\begin{code}
univm :: Regra
univm d = cataDef ((:=:),e)
            (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
             NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ univ + }",x)
    where
    e :: Def -> Def -> Def
    e ((k :.: Inl) :=: f) ((k2 :.: Inr) :=: g) | k == k2 = k :=: (f :\/: g)
    e ((k :.: (i :.: Inl)) :=: f) ((k2 :.: (h :.: Inr)) :=: g) | (k == k2 && i == h) = (k :.: i) :=: (f :\/: g)
    e f g = f :^: g

right (_ :=: b) = b
left (a :=: _) = a
\end{code}

\subsection{Regras pfpw}
O comversor pfpw tem como base regras, regras essas que trabalham sobre o nosso tipo \textbf{Regras}:\\

\subsubsection{Universal Cata}
\begin{code}
univcata' :: Regra
univcata' (f :^: g) = univcata' f >>= \x -> univcata' g >>= \y -> return ("{ univ cata }",((snd $ x) :^:(snd $ y)))
univcata' (f :=: (Cata g)) = let def = ((f :.: (Fun "in")) :=: (g :.: (recL $ saca f)))
                             in Just ("{ univ cata }",def)
univcata' _ = Nothing
\end{code}

\subsubsection{Ret in}
\begin{code}
retin' :: Regra
retin' ((f :.: (Fun "in")):=: g) = let def = ((f :.: inL) :=: g)
                                   in Just ("{ ret in }",def)
retin' _ = Nothing
\end{code}

\subsubsection{Absorção +}
\begin{code}
absorcm' :: Regra
absorcm' (f :=: ((g :\/: h) :.: (i :+: j))) = let def = (f :=: ((g :.: i) :\/: (h :.: j)))
                                              in Just ("{ absorc+ }",def)
absorcm' _ = Nothing
\end{code}

\subsubsection{Fusão +}
\begin{code}
fusaom' :: Regra
fusaom' ((f :.: (g :\/: h)) :=: i) = let def = (((f :.: g) :\/: (f :.: h)) :=: i)
                                     in Just ("{ fusao+ }",def)
fusaom' _ = Nothing
\end{code}

\subsubsection{Igualdade +}
\begin{code}
igualddm' :: Regra
igualddm' ((g :\/: i) :=: (h :\/: j)) = let def = ((g :=: h) :^: (i :=: j))
                                        in Just ("{ igualdade+ }",def)
igualddm' _ = Nothing
\end{code}

\subsubsection{Ret Const}
\begin{code}
retconst' :: Regra
retconst' d = cataDef ((:=:),(:^:))
            (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
             NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ ret const }",x)
    where
    at f (Const g) = f :@: g
    at (Const f) g = f :@: g
    at f g = f :@: g
\end{code}

\subsubsection{Ret x}
\begin{code}
retx' :: Regra
retx' d = cataDef (eq,(:^:))
           (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
            NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ ret * }",x)
    where
    eq i ((f :@: (g :*: h)) :@: (Pair (Var a) (Var b))) = i :=: (f :@: (Pair (g :@: (Var a)) (h :@: (Var b))))
    eq f g = f :=: g
\end{code}

\subsubsection{Definiçaõ de Snd}
\begin{code}
defsnd' :: Regra
defsnd' d = cataDef ((:=:),(:^:))
             (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,at,
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def snd }",x)
    where
    at (f :@: Snd) (Pair a b) = f :@: b
    at f g = f :@: g
\end{code}

\subsubsection{Definiçaõ de Id}
\begin{code}
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
    at f Id              = f
    at Id f              = f
    at f g               = f :@: g
\end{code}

\subsubsection{Definiçaõ de extensionalidade}
\begin{code}
defext' :: Regra
defext' d = cataDef (eq,(:^:))
              (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
               NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def ext }",x)
    where
    eq l@(f :.: v@(Const _)) r = (l :@: Var "a") :=: (r :@: Var "a")
    eq f@((Fun _) :.: Cons) g  = ((f :@: (Pair (Var "a") (Var "b"))) :=: (g :@: (Pair (Var "a") (Var "b"))))
    eq f g = let find = findVar f
             in if find == Nothing
                then (f :@: (Var "a")) :=: (g :@: (Var "a"))
                else f :=: g
\end{code}

\subsubsection{Eliminação x}
\begin{code}
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
\end{code}

\subsubsection{Definição de Split}
\begin{code}
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
\end{code}

\subsubsection{Definição de apos}
\begin{code}
defapos' :: Regra
defapos' d = cataDef ((:=:),(:^:))
               (Id,punct,Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
                NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ def apos }",x)
    where punct f s@(Var x) = f :@: s
          punct f g         = f :@: g
\end{code}

\subsubsection{Universal +}
\begin{code}
univm' :: Regra
univm' d = cataDef (eq,(:^:))
             (Id,(:.:),Bang,Const,Fst,Snd,(:/\:),(:*:),Inl,Inr,(:\/:),(:+:),Cond,Fun,NumInt,Var,Pair,(:@:),
              NumFloat,NumInteger,Lambda,In,Out,Nil,Cons,Cata,Rec,Nada,Op) d >>= \x -> Just ("{ univ + }",x)
    where
    eq k (f :\/: g) = ((k :.: Inl) :=: f) :^: ((k :.: Inr) :=: g)
    eq a      b            = a :=: b
\end{code}
\subsection{Parser}
\begin{code}
--parser...
main :: IO()
main = do
    f <- readFile "f"
    putStrLn $ imprime $ parseModule f
    putStrLn "pretende 1 - pwpf, 2 - pfpw ?"
    x <- getLine
    case x of
        '1':_ -> do
            l <- (sequence . map pwpf . parser__) f
            putStrLn $ unwords $ map show l
        '2':_ -> do
            l <- (sequence . map pfpw . parser__) f
            putStrLn $ unwords $ map show l
    return()

parser :: FilePath -> IO()
parser f = do s <- readFile f
              putStrLn $ show $ parser__ s

parser__ :: String -> [Def]
parser__ = parser_ . parseModule

parser_ :: ParseResult HsModule -> [Def]
parser_ (ParseOk l) = [foldr1 (:^:) h | h <- ( hsModule2Def l)]
parser_ _ = []

hsModule2Def :: HsModule -> [[Def]]
hsModule2Def (HsModule srcLoc module_ _ _ l_HsDecl) = map hsDecl2Def l_HsDecl

hsDecl2Def :: HsDecl -> [Def]
hsDecl2Def (HsFunBind l_HsMatch) = map hsMatch2Def l_HsMatch

hsMatch2Def :: HsMatch -> Def
hsMatch2Def (HsMatch srcLoc (HsIdent fun) l_HsPat hsRhs l_HsDecl)
    = (Fun fun :@: (foldr1 (:@:) $ map hsPat2Exp l_HsPat)) :=: (hsRhs2Exp hsRhs)

hsPat2Exp :: HsPat -> Exp
hsPat2Exp (HsPVar hsName) = hsName2Exp hsName
hsPat2Exp (HsPLit hsLiteral) = hsLiteral2Exp hsLiteral
--hsPat2Exp (HsPNeg hsPat) = 
hsPat2Exp (HsPInfixApp hsPat1 hsQName hsPat2) = (hsQName2Exp hsQName ) :@: Pair (hsPat2Exp hsPat1) (hsPat2Exp hsPat2)
hsPat2Exp (HsPApp hsQName l_HsPat)
    | length l_HsPat == 1 = (hsQName2Exp hsQName) :@: (foldr1 (:@:) $ map hsPat2Exp l_HsPat)
hsPat2Exp (HsPTuple l_HsPat)
    | length l_HsPat == 2 = Pair (hsPat2Exp ( l_HsPat !! 0 )) (hsPat2Exp ( l_HsPat !! 1 ))
hsPat2Exp (HsPList l_HsPat) = Nil
hsPat2Exp (HsPParen hsPat) = hsPat2Exp hsPat
--hsPat2Exp (HsPRec HsQName l_HsPatField) = 
--hsPat2Exp (HsPAsPat HsName HsPat) = 
--hsPat2Exp (HsPWildCard) = 
--hsPat2Exp (HsPIrrPat hsPat) = 

hsName2Exp :: HsName -> Exp
hsName2Exp (HsIdent "Right") = Inr
hsName2Exp (HsIdent "Left") = Inl
hsName2Exp (HsIdent var) = Var var

hsQName2Exp :: HsQName -> Exp
--hsQName2Exp (Qual module_ hsName) = 
hsQName2Exp (UnQual hsName) = hsName2Exp hsName
hsQName2Exp (Special hsSpecialCon) = hsSpecialCon2Exp hsSpecialCon

hsSpecialCon2Exp :: HsSpecialCon -> Exp
hsSpecialCon2Exp (HsUnitCon) = Bang
--hsSpecialCon2Exp (HsListCon) =
--hsSpecialCon2Exp (HsFunCon) =
--hsSpecialCon2Exp (HsTupleCon Int) =
hsSpecialCon2Exp (HsCons) = Cons


hsLiteral2Exp :: HsLiteral -> Exp
hsLiteral2Exp (HsInt int) = NumInteger int
--hsLiteral2Exp (HsChar c) =
--hsLiteral2Exp (HsString s) =
--hsLiteral2Exp (HsFrac f) = NumFloat f
--hsLiteral2Exp (HsCharPrim c) =
--hsLiteral2Exp (HsStringPrim s) =
hsLiteral2Exp (HsIntPrim integer) = NumInteger integer
--hsLiteral2Exp (HsFloatPrim f) = 
--hsLiteral2Exp (HsDoublePrim d) =

hsRhs2Exp :: HsRhs -> Exp
hsRhs2Exp (HsUnGuardedRhs hsExp) = hsExp2Exp hsExp
--hsRhs2Exp (HsGuardedRhss  l_HsGuardedRhs) = 

hsExp2Exp :: HsExp -> Exp
hsExp2Exp (HsVar hsQName) = hsQName2Exp hsQName
hsExp2Exp (HsCon hsQName) = hsQName2Exp hsQName
hsExp2Exp (HsLit hsLiteral) = hsLiteral2Exp hsLiteral
--hsExp2Exp (HsInfixApp HsExp HsQOp HsExp) = 
hsExp2Exp (HsApp hsExp1 hsExp2) = (hsExp2Exp hsExp1) :@: (hsExp2Exp hsExp2)
--hsExp2Exp (HsNegApp HsExp) = 
--hsExp2Exp (HsLambda SrcLoc [HsPat] HsExp) = 
--hsExp2Exp (HsLet [HsDecl] HsExp) = 
--hsExp2Exp (HsIf HsExp HsExp HsExp) = 
--hsExp2Exp (HsCase HsExp [HsAlt]) = 
--hsExp2Exp (HsDo [HsStmt]) = 
hsExp2Exp (HsTuple l_HsExp)
    | length l_HsExp == 2 = Pair (hsExp2Exp (l_HsExp !! 0)) ( hsExp2Exp(l_HsExp !! 1))
--hsExp2Exp (HsList [HsExp]) = 
hsExp2Exp (HsParen hsExp) = hsExp2Exp hsExp
--hsExp2Exp (HsLeftSection HsExp HsQOp) = 
--hsExp2Exp (HsRightSection HsQOp HsExp) = 
--hsExp2Exp (HsRecConstr HsQName [HsFieldUpdate]) = 
--hsExp2Exp (HsRecUpdate HsExp [HsFieldUpdate]) = 
--hsExp2Exp (HsEnumFrom HsExp) = 
--hsExp2Exp (HsEnumFromTo HsExp HsExp) = 
--hsExp2Exp (HsEnumFromThen HsExp HsExp) = 
--hsExp2Exp (HsEnumFromThenTo HsExp HsExp HsExp) = 
--hsExp2Exp (HsListComp HsExp [HsStmt]) = 
--hsExp2Exp (HsExpTypeSig SrcLoc HsExp HsQualType) = 
--hsExp2Exp (HsAsPat HsName HsExp) = 
--hsExp2Exp (HsWildCard) = 
--hsExp2Exp (HsIrrPat HsExp) = 

imprime :: ParseResult HsModule -> String
imprime (ParseOk a)       = prettyPrint a
imprime (ParseFailed _ s) = s
\end{code}

\end{mtc}

\section{Testes}
\begin{mtc}
De seguida lista-se algumas funções de teste...\\
\begin{code}
-- testes
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
    ((Fun "distwo" :@: (Inl :@: (Var "x"))) :=: (Pair (Inl :@: Bang) (Var "x")))
    :^:
    ((Fun "distwo" :@: (Inr :@: (Var "x"))) :=: (Pair (Inr :@: Bang) (Var "x")))
\end{code}
\end{mtc}

\end{document}
