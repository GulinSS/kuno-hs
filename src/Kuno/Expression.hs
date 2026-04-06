module Kuno.Expression
  ( Term(..)
  , Formula(..)
  , SymbolicAttack(..)
  , Statement(..)
  , isAtomic
  , isNegation
  , isImplication
  , isDisjunction
  , isConjunction
  , isGeneralization
  , isUniversal
  , isExistential
  , isComposite
  , formulaAny
  , containsContradiction
  , containsVerum
  , containsQuantifier
  , containsEquation
  , unnegate
  , antecedent
  , consequent
  , equivalenceToConjunction
  , instantiate
  , substTermForVar
  , isVariableTerm
  , termsIn
  , freeVariables
  , freshVariable
  , termDepth
  , nonVariableTerms
  , variablesIn
  , occursFreelyIn
  , properSubformulas
  , showFormula
  , showTerm
  , nubOrd
  ) where

import Data.List (find, intercalate)
import qualified Data.Set as Set

-- | Terms in first-order logic
data Term
  = Variable String
  | FunTerm String [Term]
  deriving (Show, Eq, Ord)

-- | Formulas
data Formula
  = Atomic String [Term]
  | Equation Term Term
  | Disequation Term Term
  | Verum
  | Falsum
  | Negation Formula
  | Conjunction Formula Formula
  | Disjunction Formula Formula
  | Implication Formula Formula
  | ReverseImplication Formula Formula
  | Equivalence Formula Formula
  | Nonequivalence Formula Formula
  | UniversalQ [Term] Formula
  | ExistentialQ [Term] Formula
  deriving (Show, Eq, Ord)

-- | Symbolic attacks used in dialogue games
data SymbolicAttack
  = AttackLeftConjunct
  | AttackRightConjunct
  | WhichDisjunct
  | WhichInstance (Maybe Term)
  deriving (Show, Eq, Ord)

-- | A statement is either a formula, a symbolic attack, or a term
data Statement
  = FormulaS Formula
  | AttackS SymbolicAttack
  | TermS Term
  deriving (Show, Eq, Ord)

-- Predicates
isAtomic :: Formula -> Bool
isAtomic (Atomic _ _) = True
isAtomic (Equation _ _) = True
isAtomic (Disequation _ _) = True
isAtomic Verum = True
isAtomic Falsum = True
isAtomic _ = False

isNegation :: Formula -> Bool
isNegation (Negation _) = True
isNegation _ = False

isImplication :: Formula -> Bool
isImplication (Implication _ _) = True
isImplication _ = False

isDisjunction :: Formula -> Bool
isDisjunction (Disjunction _ _) = True
isDisjunction _ = False

isConjunction :: Formula -> Bool
isConjunction (Conjunction _ _) = True
isConjunction _ = False

isGeneralization :: Formula -> Bool
isGeneralization (UniversalQ _ _) = True
isGeneralization (ExistentialQ _ _) = True
isGeneralization _ = False

isUniversal :: Formula -> Bool
isUniversal (UniversalQ _ _) = True
isUniversal _ = False

isExistential :: Formula -> Bool
isExistential (ExistentialQ _ _) = True
isExistential _ = False

isComposite :: Formula -> Bool
isComposite = not . isAtomic

unnegate :: Formula -> Formula
unnegate (Negation f) = f
unnegate f = f

-- negate_ :: Formula -> Formula
-- negate_ = Negation

antecedent :: Formula -> Formula
antecedent (Implication a _) = a
antecedent f = f

consequent :: Formula -> Formula
consequent (Implication _ c) = c
consequent f = f

-- makeBinaryConjunction :: Formula -> Formula -> Formula
-- makeBinaryConjunction = Conjunction
--
-- makeBinaryDisjunction :: Formula -> Formula -> Formula
-- makeBinaryDisjunction = Disjunction
--
-- makeImplication :: Formula -> Formula -> Formula
-- makeImplication = Implication
--
-- makeEquivalence :: Formula -> Formula -> Formula
-- makeEquivalence = Equivalence

-- | Check whether any subformula satisfies a predicate
formulaAny :: (Formula -> Bool) -> Formula -> Bool
formulaAny p f
  | p f = True
formulaAny p (Negation f) = formulaAny p f
formulaAny p (Conjunction l r) = formulaAny p l || formulaAny p r
formulaAny p (Disjunction l r) = formulaAny p l || formulaAny p r
formulaAny p (Implication l r) = formulaAny p l || formulaAny p r
formulaAny p (Equivalence l r) = formulaAny p l || formulaAny p r
formulaAny p (UniversalQ _ m) = formulaAny p m
formulaAny p (ExistentialQ _ m) = formulaAny p m
formulaAny _ _ = False

containsContradiction :: Formula -> Bool
containsContradiction = formulaAny (== Falsum)

containsVerum :: Formula -> Bool
containsVerum = formulaAny (== Verum)

containsQuantifier :: Formula -> Bool
containsQuantifier = formulaAny isGeneralization

containsEquation :: Formula -> Bool
containsEquation = formulaAny isEq
  where isEq (Equation _ _) = True
        isEq (Disequation _ _) = True
        isEq _ = False

-- Substitution
substTermForVar :: Term -> Term -> Term -> Term
substTermForVar new var target@(Variable _)
  | var == target = new
  | otherwise = target
substTermForVar new var (FunTerm f args) =
  FunTerm f (map (substTermForVar new var) args)

instantiate :: Formula -> Term -> Term -> Formula
instantiate (Atomic p args) term var =
  Atomic p (map (substTermForVar term var) args)
instantiate (Negation f) term var =
  Negation (instantiate f term var)
instantiate (Conjunction l r) term var =
  Conjunction (instantiate l term var) (instantiate r term var)
instantiate (Disjunction l r) term var =
  Disjunction (instantiate l term var) (instantiate r term var)
instantiate (Implication l r) term var =
  Implication (instantiate l term var) (instantiate r term var)
instantiate (ReverseImplication l r) term var =
  ReverseImplication (instantiate l term var) (instantiate r term var)
instantiate (Equivalence l r) term var =
  Equivalence (instantiate l term var) (instantiate r term var)
instantiate (Nonequivalence l r) term var =
  Nonequivalence (instantiate l term var) (instantiate r term var)
instantiate (Equation l r) term var =
  Equation (substTermForVar term var l) (substTermForVar term var r)
instantiate (Disequation l r) term var =
  Disequation (substTermForVar term var l) (substTermForVar term var r)
instantiate (UniversalQ bindings matrix) term var
  | var `notElem` bindings = UniversalQ bindings (instantiate matrix term var)
  | otherwise =
      let remaining = filter (/= var) bindings
      in if null remaining
         then instantiate matrix term var
         else UniversalQ remaining (instantiate matrix term var)
instantiate (ExistentialQ bindings matrix) term var
  | var `notElem` bindings = ExistentialQ bindings (instantiate matrix term var)
  | otherwise =
      let remaining = filter (/= var) bindings
      in if null remaining
         then instantiate matrix term var
         else ExistentialQ remaining (instantiate matrix term var)
instantiate f _ _ = f

-- Term operations
isVariableTerm :: Term -> Bool
isVariableTerm (Variable _) = True
isVariableTerm _ = False

termsIn :: Formula -> [Term]
termsIn (Atomic _ args) = termsInTerms args
termsIn (Equation l r) = nubOrd (termsInTerm l ++ termsInTerm r)
termsIn (Disequation l r) = nubOrd (termsInTerm l ++ termsInTerm r)
termsIn (Negation f) = termsIn f
termsIn (Conjunction l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (Disjunction l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (Implication l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (ReverseImplication l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (Equivalence l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (Nonequivalence l r) = nubOrd (termsIn l ++ termsIn r)
termsIn (UniversalQ bs m) = nubOrd (bs ++ termsIn m)
termsIn (ExistentialQ bs m) = nubOrd (bs ++ termsIn m)
termsIn _ = []

termsInTerm :: Term -> [Term]
termsInTerm v@(Variable _) = [v]
termsInTerm (FunTerm _ args) = termsInTerms args

termsInTerms :: [Term] -> [Term]
termsInTerms = nubOrd . concatMap termsInTerm

variablesIn :: Formula -> [Term]
variablesIn = filter isVariableTerm . termsIn

nonVariableTerms :: Formula -> [Term]
nonVariableTerms = filter (not . isVariableTerm) . termsIn

freshVariable :: [Term] -> [Formula] -> Term
freshVariable existingTerms formulas =
  let vars = filter isVariableTerm existingTerms
           ++ concatMap (filter isVariableTerm . termsIn) formulas
      numVars = length vars
      candidates = [Variable ("X" ++ show i) | i <- [1 .. numVars + 1]]
  in case find (\c -> c `notElem` vars) candidates of
       Just v  -> v
       Nothing -> Variable ("X" ++ show (numVars + 1))

termDepth :: Term -> Int
termDepth (Variable _) = 0
termDepth (FunTerm _ []) = 0
termDepth (FunTerm _ args) = 1 + maximum (map termDepth args)

occursFreelyIn :: Term -> Formula -> Bool
occursFreelyIn term (Atomic _ args) = any (== term) args
occursFreelyIn term (Equation l r) = term == l || term == r
occursFreelyIn term (Disequation l r) = term == l || term == r
occursFreelyIn term (Negation f) = occursFreelyIn term f
occursFreelyIn term (Conjunction l r) = occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term (Disjunction l r) = occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term (Implication l r) = occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term (ReverseImplication l r) = occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term (Equivalence l r) = occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term (Nonequivalence l r) = occursFreelyIn term l || occursFreelyIn term r
occursFreelyIn term@(Variable _) (UniversalQ bs m) =
  term `notElem` bs && occursFreelyIn term m
occursFreelyIn term@(Variable _) (ExistentialQ bs m) =
  term `notElem` bs && occursFreelyIn term m
occursFreelyIn _ _ = False

freeVariables :: Formula -> [Term]
freeVariables (Atomic _ args) = nubOrd $ concatMap freeVarsInTerm args
freeVariables (Equation l r) = nubOrd (freeVarsInTerm l ++ freeVarsInTerm r)
freeVariables (Disequation l r) = nubOrd (freeVarsInTerm l ++ freeVarsInTerm r)
freeVariables (Negation f) = freeVariables f
freeVariables (Conjunction l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (Disjunction l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (Implication l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (ReverseImplication l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (Equivalence l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (Nonequivalence l r) = nubOrd (freeVariables l ++ freeVariables r)
freeVariables (UniversalQ bs m) =
  filter (\v -> v `notElem` bs) (freeVariables m)
freeVariables (ExistentialQ bs m) =
  filter (\v -> v `notElem` bs) (freeVariables m)
freeVariables _ = []

freeVarsInTerm :: Term -> [Term]
freeVarsInTerm v@(Variable _) = [v]
freeVarsInTerm (FunTerm _ args) = concatMap freeVarsInTerm args

-- Proper subformulas
properSubformulas :: Formula -> [Formula]
properSubformulas = nubOrd . properSubs
  where
    properSubs (Negation f) = f : properSubs f
    properSubs (Conjunction l r) = [l, r] ++ properSubs l ++ properSubs r
    properSubs (Disjunction l r) = [l, r] ++ properSubs l ++ properSubs r
    properSubs (Implication l r) = [l, r] ++ properSubs l ++ properSubs r
    properSubs (ReverseImplication l r) = [l, r] ++ properSubs l ++ properSubs r
    properSubs (Equivalence l r) = [l, r] ++ properSubs l ++ properSubs r
    properSubs (Nonequivalence l r) = [l, r] ++ properSubs l ++ properSubs r
    properSubs (UniversalQ _ m) = m : properSubs m
    properSubs (ExistentialQ _ m) = m : properSubs m
    properSubs _ = []

-- binarize is identity for this ADT (all connectives are already binary)
-- binarize :: Formula -> Formula
-- binarize (Negation f) = Negation (binarize f)
-- binarize (Conjunction l r) = Conjunction (binarize l) (binarize r)
-- binarize (Disjunction l r) = Disjunction (binarize l) (binarize r)
-- binarize (Implication l r) = Implication (binarize l) (binarize r)
-- binarize (ReverseImplication l r) = ReverseImplication (binarize l) (binarize r)
-- binarize (Equivalence l r) = Equivalence (binarize l) (binarize r)
-- binarize (Nonequivalence l r) = Nonequivalence (binarize l) (binarize r)
-- binarize (UniversalQ bs m) = UniversalQ bs (binarize m)
-- binarize (ExistentialQ bs m) = ExistentialQ bs (binarize m)
-- binarize f = f

equivalenceToConjunction :: Formula -> Formula
equivalenceToConjunction (Equivalence l r) =
  let l' = equivalenceToConjunction l
      r' = equivalenceToConjunction r
  in Conjunction (Implication l' r') (Implication r' l')
equivalenceToConjunction (Negation f) = Negation (equivalenceToConjunction f)
equivalenceToConjunction (Conjunction l r) =
  Conjunction (equivalenceToConjunction l) (equivalenceToConjunction r)
equivalenceToConjunction (Disjunction l r) =
  Disjunction (equivalenceToConjunction l) (equivalenceToConjunction r)
equivalenceToConjunction (Implication l r) =
  Implication (equivalenceToConjunction l) (equivalenceToConjunction r)
equivalenceToConjunction (ReverseImplication l r) =
  ReverseImplication (equivalenceToConjunction l) (equivalenceToConjunction r)
equivalenceToConjunction (UniversalQ bs m) =
  UniversalQ bs (equivalenceToConjunction m)
equivalenceToConjunction (ExistentialQ bs m) =
  ExistentialQ bs (equivalenceToConjunction m)
equivalenceToConjunction f = f

-- Ordering: superseded by derived Ord instances
-- formulaLt :: Formula -> Formula -> Bool
-- formulaLt (Atomic p1 _) (Atomic p2 _) = p1 < p2
-- formulaLt (Atomic _ _) _ = True
-- formulaLt (Negation _) (Atomic _ _) = False
-- formulaLt (Negation f1) (Negation f2) = formulaLt f1 f2
-- formulaLt (Negation _) _ = True
-- formulaLt _ (Atomic _ _) = False
-- formulaLt _ (Negation _) = False
-- formulaLt (Conjunction l1 r1) (Conjunction l2 r2) =
--   formulaLt l1 l2 || formulaLt r1 r2
-- formulaLt _ _ = False
--
-- statementLt :: Statement -> Statement -> Bool
-- statementLt (FormulaS f1) (FormulaS f2) = formulaLt f1 f2
-- statementLt (AttackS _) (FormulaS _) = False
-- statementLt (FormulaS _) (AttackS _) = False
-- statementLt (AttackS AttackLeftConjunct) _ = True
-- statementLt (AttackS AttackRightConjunct) (AttackS AttackLeftConjunct) = False
-- statementLt (AttackS AttackRightConjunct) _ = True
-- statementLt _ _ = False

-- Pretty printing
showTerm :: Term -> String
showTerm (Variable x) = x
showTerm (FunTerm f []) = f
showTerm (FunTerm f args) = f ++ "(" ++ commaSep (map showTerm args) ++ ")"

showFormula :: Formula -> String
showFormula (Atomic p []) = p
showFormula (Atomic p args) = p ++ "(" ++ commaSep (map showTerm args) ++ ")"
showFormula (Equation l r) = showTerm l ++ " = " ++ showTerm r
showFormula (Disequation l r) = showTerm l ++ " != " ++ showTerm r
showFormula Verum = "$true"
showFormula Falsum = "$false"
showFormula (Negation f) = "~" ++ showFormula f
showFormula (Conjunction l r) = "(" ++ showFormula l ++ " & " ++ showFormula r ++ ")"
showFormula (Disjunction l r) = "(" ++ showFormula l ++ " | " ++ showFormula r ++ ")"
showFormula (Implication l r) = "(" ++ showFormula l ++ " => " ++ showFormula r ++ ")"
showFormula (ReverseImplication l r) = "(" ++ showFormula l ++ " <= " ++ showFormula r ++ ")"
showFormula (Equivalence l r) = "(" ++ showFormula l ++ " <=> " ++ showFormula r ++ ")"
showFormula (Nonequivalence l r) = "(" ++ showFormula l ++ " <~> " ++ showFormula r ++ ")"
showFormula (UniversalQ bs m) =
  "(! [" ++ commaSep (map showTerm bs) ++ "] : " ++ showFormula m ++ ")"
showFormula (ExistentialQ bs m) =
  "(? [" ++ commaSep (map showTerm bs) ++ "] : " ++ showFormula m ++ ")"

commaSep :: [String] -> String
commaSep = intercalate ","

-- | O(n log n) deduplication preserving first-occurrence order
nubOrd :: Ord a => [a] -> [a]
nubOrd = go Set.empty
  where
    go _ [] = []
    go seen (x:xs)
      | x `Set.member` seen = go seen xs
      | otherwise = x : go (Set.insert x seen) xs
