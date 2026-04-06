module Kuno.Translation
  ( goedelGentzen
  , doubleNegate
  , dnAllSubformulas
  , kuroda
  , negateAtomicSubformulas
  , doubleNegateAtomicSubformulas
  , contrapositivify
  , contrapositive
  , atomicToExcludedMiddle
  , converse
  ) where

import Kuno.Expression

-- | Goedel-Gentzen negative translation
goedelGentzen :: Formula -> Formula
goedelGentzen f@(Atomic _ _) = Negation (Negation (goedelGentzen' f))
  where goedelGentzen' a@(Atomic _ _) = a
        goedelGentzen' _ = f
goedelGentzen (Negation inner) = Negation (goedelGentzen inner)
goedelGentzen (Conjunction l r) =
  Conjunction (goedelGentzen l) (goedelGentzen r)
goedelGentzen (Disjunction l r) =
  Negation (Conjunction (Negation (goedelGentzen l))
                                  (Negation (goedelGentzen r)))
goedelGentzen (Implication l r) =
  Implication (goedelGentzen l) (goedelGentzen r)
goedelGentzen (UniversalQ bs m) =
  UniversalQ bs (goedelGentzen m)
goedelGentzen (ExistentialQ bs m) =
  Negation (UniversalQ bs (Negation (goedelGentzen m)))
goedelGentzen f = Negation (Negation f)

-- | Double negate the whole formula
doubleNegate :: Formula -> Formula
doubleNegate f = Negation (Negation f)

-- | Double negate all subformulas
dnAllSubformulas :: Formula -> Formula
dnAllSubformulas f@(Atomic _ _) = Negation (Negation f)
dnAllSubformulas (Negation inner) =
  Negation (Negation (Negation (dnAllSubformulas inner)))
dnAllSubformulas (Conjunction l r) =
  Negation (Negation (Conjunction (dnAllSubformulas l) (dnAllSubformulas r)))
dnAllSubformulas (Disjunction l r) =
  Negation (Negation (Disjunction (dnAllSubformulas l) (dnAllSubformulas r)))
dnAllSubformulas (Implication l r) =
  Negation (Negation (Implication (dnAllSubformulas l) (dnAllSubformulas r)))
dnAllSubformulas (ReverseImplication l r) =
  Negation (Negation (ReverseImplication (dnAllSubformulas l) (dnAllSubformulas r)))
dnAllSubformulas (Equivalence l r) =
  Negation (Negation (Equivalence (dnAllSubformulas l) (dnAllSubformulas r)))
dnAllSubformulas (UniversalQ bs m) =
  UniversalQ bs (Negation (Negation (dnAllSubformulas m)))
dnAllSubformulas (ExistentialQ bs m) =
  ExistentialQ bs (Negation (Negation (dnAllSubformulas m)))
dnAllSubformulas f = Negation (Negation f)

-- | Kuroda translation
kuroda :: Formula -> Formula
kuroda formula = Negation (Negation (kuroda' formula))
  where
    kuroda' f@(Atomic _ _) = f
    kuroda' (Negation inner) = Negation (kuroda' inner)
    kuroda' (Conjunction l r) = Conjunction (kuroda' l) (kuroda' r)
    kuroda' (Disjunction l r) = Disjunction (kuroda' l) (kuroda' r)
    kuroda' (Implication l r) = Implication (kuroda' l) (kuroda' r)
    kuroda' (ExistentialQ bs m) = ExistentialQ bs (kuroda' m)
    kuroda' (UniversalQ bs m) =
      UniversalQ bs (Negation (Negation (kuroda' m)))
    kuroda' f = f

-- | Apply a transformation to all atomic subformulas, recursing into composites
mapAtomicFormulas :: (Formula -> Formula) -> Formula -> Formula
mapAtomicFormulas f a@(Atomic _ _) = f a
mapAtomicFormulas f (Negation inner) = Negation (mapAtomicFormulas f inner)
mapAtomicFormulas f (Conjunction l r) =
  Conjunction (mapAtomicFormulas f l) (mapAtomicFormulas f r)
mapAtomicFormulas f (Disjunction l r) =
  Disjunction (mapAtomicFormulas f l) (mapAtomicFormulas f r)
mapAtomicFormulas f (Implication l r) =
  Implication (mapAtomicFormulas f l) (mapAtomicFormulas f r)
mapAtomicFormulas f (Equivalence l r) =
  Equivalence (mapAtomicFormulas f l) (mapAtomicFormulas f r)
mapAtomicFormulas f (UniversalQ bs m) = UniversalQ bs (mapAtomicFormulas f m)
mapAtomicFormulas f (ExistentialQ bs m) = ExistentialQ bs (mapAtomicFormulas f m)
mapAtomicFormulas _ f = f

-- | Negate atomic subformulas
negateAtomicSubformulas :: Formula -> Formula
negateAtomicSubformulas = mapAtomicFormulas Negation

-- | Double negate atomic subformulas
doubleNegateAtomicSubformulas :: Formula -> Formula
doubleNegateAtomicSubformulas = mapAtomicFormulas (Negation . Negation)

-- | Take the contrapositive of all implications (recursively)
contrapositivify :: Formula -> Formula
contrapositivify f@(Atomic _ _) = f
contrapositivify (Negation inner) = Negation (contrapositivify inner)
contrapositivify (Conjunction l r) =
  Conjunction (contrapositivify l) (contrapositivify r)
contrapositivify (Disjunction l r) =
  Disjunction (contrapositivify l) (contrapositivify r)
contrapositivify (Implication l r) =
  Implication (Negation (contrapositivify r)) (Negation (contrapositivify l))
contrapositivify (Equivalence l r) =
  Equivalence (contrapositivify l) (contrapositivify r)
contrapositivify (UniversalQ bs m) = UniversalQ bs (contrapositivify m)
contrapositivify (ExistentialQ bs m) = ExistentialQ bs (contrapositivify m)
contrapositivify f = f

-- | Contrapositive of the outermost implication only
contrapositive :: Formula -> Formula
contrapositive (Implication l r) = Implication (Negation r) (Negation l)
contrapositive f = f

-- | Replace atomic subformulas p by (p | ~p)
atomicToExcludedMiddle :: Formula -> Formula
atomicToExcludedMiddle = mapAtomicFormulas (\f -> Disjunction f (Negation f))

-- | Converse of an implication
converse :: Formula -> Formula
converse (Implication l r) = Implication r l
converse f = f
