-- Deriving decidable equality. This works in several cases that use
-- mutual recursion, examples are at the bottom.
--
-- TODO: This breaks with:
-- - dependent records, e.g. Product
-- - anything listed in Tactic.Derive
-- - maybe more

{-# OPTIONS -v allTactics:100 #-}
{-# OPTIONS --safe #-}
open import Meta

module Tactic.Derive.DecEq where

open import MetaPrelude

open import Reflection.AST.Term using (_≟-Pattern_)

open import Generics

import Data.List as L
import Data.List.NonEmpty as NE

open import Relation.Nullary
open import Relation.Nullary.Decidable

module _ where
  open import Interface.DecEq hiding (DecEq-List; DecEq-ℕ; DecEq-ℤ; DecEq-⊤; DecEq-Maybe) public

open import Tactic.ClauseBuilder
open import Tactic.Derive (quote DecEq) (quote _≟_)

open import Interface.Monad.Instance
open import Interface.MonadTC.Instance

instance
  _ = ContextMonad-MonadTC

open ClauseExprM

`yes `no : Term → Term
`yes x = quote _because_ ◆⟦ quote true  ◆ ∣ quote ofʸ ◆⟦ x ⟧ ⟧
`no  x = quote _because_ ◆⟦ quote false ◆ ∣ quote ofⁿ ◆⟦ x ⟧ ⟧

map' : ∀ {p q} {P : Set p} {Q : Set q} → P ⇔ Q → Dec P → Dec Q
map' record { to = to ; from = from } = map′ to from

module _ (transName : Name → Maybe Name) where

  eqFromTerm : Term → Term → Term → Term
  eqFromTerm (def n _) t t' with transName n
  ... | just n'     = def (quote _≟_) (iArg (n' ∙) ∷ vArg t ∷ vArg t' ∷ [])
  ... | nothing     = quote _≟_ ∙⟦ t ∣ t' ⟧
  eqFromTerm _ t t' = quote _≟_ ∙⟦ t ∣ t' ⟧

  toDecEqName : SinglePattern → List (Term → Term → Term)
  toDecEqName (l , _) = L.map (λ where (_ , arg _ t) → eqFromTerm t) l

  -- on the diagonal we have one pattern, outside we don't care
  -- assume that the types in the pattern are properly normalized
  mapDiag : Maybe SinglePattern → TC Term
  mapDiag nothing          = return $ `no `λ⦅ [ ("" , vArg?) ] ⦆∅
  mapDiag (just p@(l , _)) = let k = length l in do
    typeList ← traverseList inferType (applyDownFrom ♯ (length l))
    return $ quote map' ∙⟦ genEquiv k ∣ genPf k (L.map eqFromTerm typeList) ⟧
    where
      genPf : ℕ → List (Term → Term → Term) → Term
      genPf k []      = `yes (quote tt ◆)
      genPf k (n ∷ l) = quote _×-dec_ ∙⟦ genPf k l ∣ n (♯ (length l)) (♯ (length l + k)) ⟧

      -- c x1 .. xn ≡ c y1 .. yn ⇔ x1 ≡ y1 .. xn ≡ yn
      genEquiv : ℕ → Term
      genEquiv n = quote mk⇔ ∙⟦ `λ⟦ reflPattern n ⇒ quote refl ◆ ⟧ ∣ `λ⟦ quote refl ◇ ⇒ reflTerm n ⟧ ⟧
        where
          reflPattern : ℕ → Pattern
          reflPattern 0       = quote tt ◇
          reflPattern (suc n) = quote _,_ ◇⟦ reflPattern n ∣ quote refl ◇ ⟧

          reflTerm : ℕ → Term
          reflTerm 0       = quote tt ◆
          reflTerm (suc n) = quote _,_ ◆⟦ reflTerm n ∣ quote refl ◆ ⟧

  toMapDiag : SinglePattern → SinglePattern → NE.List⁺ SinglePattern × TC (ClauseExpr ⊎ Maybe Term)
  toMapDiag p@(_ , arg _ p₁) p'@(_ , arg _ p₂) =
    (p NE.∷ [ p' ] , finishMatch (if ⌊ p₁ ≟-Pattern p₂ ⌋ then mapDiag (just p) else mapDiag nothing))

module _ ⦃ _ : DebugOptions ⦄ where
  derive-DecEq : List (Name × Name) → UnquoteDecl
  derive-DecEq = derive-Class 0 (λ transName ps → cartesianProductWith (toMapDiag transName) ps ps)

private
  open import Tactic.Derive.TestTypes
  open import Tactic.Defaults

  unquoteDecl DecEq-These = derive-DecEq [ (quote These , DecEq-These) ]

  unquoteDecl DecEq-⊎ = derive-DecEq [ (quote _⊎_ , DecEq-⊎) ]

  unquoteDecl DecEq-Bool DecEq-ℤ DecEq-List DecEq-Maybe DecEq-ℕ DecEq-Sign DecEq-⊤ = derive-DecEq ((quote Bool , DecEq-Bool) ∷ (quote ℤ , DecEq-ℤ) ∷ (quote List , DecEq-List) ∷ (quote Maybe , DecEq-Maybe) ∷ (quote ℕ , DecEq-ℕ) ∷ (quote Sign , DecEq-Sign) ∷ (quote ⊤ , DecEq-⊤) ∷ [])

  unquoteDecl DecEq-Fin = derive-DecEq [ (quote Fin , DecEq-Fin) ]

  -- this doesn't work since the clause builder machinery doesn't deal
  -- with absurd patterns yet

  --unquoteDecl DecEq-Vec = derive-DecEq [ (quote Vec , DecEq-Vec) ]

  unquoteDecl DecEq-E1 = derive-DecEq [ (quote E1 , DecEq-E1) ]
  unquoteDecl DecEq-E2 = derive-DecEq [ (quote E2 , DecEq-E2) ]

  -- this uses mutual recursion with List E3
  unquoteDecl DecEq-E3 = derive-DecEq [ (quote E3 , DecEq-E3) ]
  -- unquoteDecl DecEq-E4 = derive-DecEq [ (quote E4 , DecEq-E4) ]

  unquoteDecl DecEq-R1 = derive-DecEq [ (quote R1 , DecEq-R1) ]
  unquoteDecl DecEq-R2 = derive-DecEq [ (quote R2 , DecEq-R2) ]

  unquoteDecl DecEq-M₁ DecEq-M₂ = derive-DecEq $ (quote M₁ , DecEq-M₁) ∷ (quote M₂ , DecEq-M₂) ∷ []

  -- Expected: DecEq-Term DecEq-Product
