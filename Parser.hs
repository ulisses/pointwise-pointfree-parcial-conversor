module Parser where

-- master
data HsDecl = HsFunBind [HsMatch]
    deriving (Eq,Show)
data HsMatch = HsMatch SrcLoc HsName [HsPat] HsRhs {-where-} [HsDecl]
  deriving (Eq,Show)

data SrcLoc = SrcLoc {
		srcFilename :: String,
		srcLine :: Int,
		srcColumn :: Int
		}
  deriving (Eq,Ord,Show)

data HsName
	= HsIdent String	-- ^ /varid/ or /conid/.
	| HsSymbol String	-- ^ /varsym/ or /consym/
  deriving (Eq,Ord,Show)

data HsPat
	= HsPVar HsName    -- variavel no parametro
	| HsPLit HsLiteral -- literal no parametro
	| HsPNeg HsPat
	| HsPInfixApp HsPat HsQName HsPat
	| HsPApp HsQName [HsPat]
	| HsPTuple [HsPat]  -- tuplo
	| HsPList [HsPat]   -- lista
	| HsPParen HsPat
	| HsPRec HsQName [HsPatField]
	| HsPAsPat HsName HsPat
	| HsPWildCard
	| HsPIrrPat HsPat
 deriving (Eq,Show)

data HsRhs
	 = HsUnGuardedRhs HsExp
	 | HsGuardedRhss  [HsGuardedRhs]
  deriving (Eq,Show)

-- | /literal/
data HsLiteral
	= HsInt		Integer
	| HsChar	Char
	| HsString	String
	| HsFrac	Rational
	| HsCharPrim	Char		-- ^ GHC unboxed character literal
	| HsStringPrim	String		-- ^ GHC unboxed string literal
	| HsIntPrim	Integer		-- ^ GHC unboxed integer literal
	| HsFloatPrim	Rational	-- ^ GHC unboxed float literal
	| HsDoublePrim	Rational	-- ^ GHC unboxed double literal
  deriving (Eq, Show)

-- |This type is used to represent qualified variables, and also
-- qualified constructors.
data HsQName
	= Qual Module HsName
	| UnQual HsName
	| Special HsSpecialCon
  deriving (Eq,Ord)

instance Show HsQName where
   showsPrec _ (Qual (Module m) s) =
	showString m . showString "." . shows s
   showsPrec _ (UnQual s) = shows s
   showsPrec _ (Special s) = shows s


data HsPatField
	= HsPFieldPat HsQName HsPat
 deriving (Eq,Show)

data HsExp
	= HsVar HsQName
	| HsCon HsQName
	| HsLit HsLiteral
	| HsInfixApp HsExp HsQOp HsExp
	| HsApp HsExp HsExp
	| HsNegApp HsExp
	| HsLambda SrcLoc [HsPat] HsExp
	| HsLet [HsDecl] HsExp
	| HsIf HsExp HsExp HsExp
	| HsCase HsExp [HsAlt]
	| HsDo [HsStmt]			-- ^ Do expression:
					-- The last statement in the list
					-- should be an expression.
	| HsTuple [HsExp]
	| HsList [HsExp]
	| HsParen HsExp
	| HsLeftSection HsExp HsQOp
	| HsRightSection HsQOp HsExp
	| HsRecConstr HsQName [HsFieldUpdate]
	| HsRecUpdate HsExp [HsFieldUpdate]
	| HsEnumFrom HsExp
	| HsEnumFromTo HsExp HsExp
	| HsEnumFromThen HsExp HsExp
	| HsEnumFromThenTo HsExp HsExp HsExp
	| HsListComp HsExp [HsStmt]
	| HsExpTypeSig SrcLoc HsExp HsQualType
	| HsAsPat HsName HsExp		-- ^ patterns only
	| HsWildCard			-- ^ patterns only
	| HsIrrPat HsExp		-- ^ patterns only
 deriving (Eq,Show)

data HsGuardedRhs
	 = HsGuardedRhs SrcLoc HsExp HsExp
  deriving (Eq,Show)

newtype Module = Module String
  deriving (Eq,Ord,Show)

data HsSpecialCon
	= HsUnitCon		-- ^ Unit type and data constructor @()@
	| HsListCon		-- ^ List type constructor @[]@
	| HsFunCon		-- ^ Function type constructor @->@
	| HsTupleCon Int	-- ^ /n/-ary tuple type and data
				--   constructors @(,)@ etc
	| HsCons		-- ^ list data constructor @(:)@
  deriving (Eq,Ord)

instance Show HsSpecialCon where
	show HsUnitCon = "()"
	show HsListCon = "[]"
	show HsFunCon = "->"
	show (HsTupleCon n) = "(" ++ replicate (n-1) ',' ++ ")"
	show HsCons = ":"

-- | Possibly qualified infix operators (/qop/), appearing in expressions.
data HsQOp
	= HsQVarOp HsQName
	| HsQConOp HsQName
  deriving (Eq,Ord)

instance Show HsQOp where
   showsPrec p (HsQVarOp n) = showsPrec p n
   showsPrec p (HsQConOp n) = showsPrec p n

data HsAlt
	= HsAlt SrcLoc HsPat HsGuardedAlts [HsDecl]
  deriving (Eq,Show)

-- | This type represents both /stmt/ in a @do@-expression,
--   and /qual/ in a list comprehension.
data HsStmt
	= HsGenerator SrcLoc HsPat HsExp
	| HsQualifier HsExp
	| HsLetStmt [HsDecl]
 deriving (Eq,Show)

-- | An /fbind/ in a labeled construction or update.
data HsFieldUpdate
	= HsFieldUpdate HsQName HsExp
  deriving (Eq,Show)

-- | A type qualified with a context.
--   An unqualified type has an empty context.
data HsQualType
	 = HsQualType HsContext HsType
  deriving (Eq,Show)

data HsGuardedAlts
	= HsUnGuardedAlt HsExp
	| HsGuardedAlts  [HsGuardedAlt]
  deriving (Eq,Show)

type HsContext = [HsAsst]

data HsType
	 = HsTyFun   HsType HsType
	 | HsTyTuple [HsType]
	 | HsTyApp   HsType HsType
	 | HsTyVar   HsName
	 | HsTyCon   HsQName
  deriving (Eq,Show)

data HsGuardedAlt
	= HsGuardedAlt SrcLoc HsExp HsExp
  deriving (Eq,Show)

-- | Class assertions.
--   In Haskell 98, the argument would be a /tyvar/, but this definition
--   allows multiple parameters, and allows them to be /type/s.
type HsAsst    = (HsQName,[HsType])
