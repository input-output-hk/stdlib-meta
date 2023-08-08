{-# OPTIONS -v Generics:100 #-}
module Tactics.Intro where

open import Function using (case_of_; _$_)
open import Data.Unit using (⊤)
open import Data.Product using (_,_)
open import Data.List using (_∷_; length; applyUpTo)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)

open import Class.Functor
open import Class.Semigroup
open import Class.Monad
open import Class.Show

open import Generics
open import Reflection hiding (_>>=_; _>>_; return)
open import Reflection.AST.Meta
open Debug ("Generics.Intros" , 100)

intro : Hole → Tactic → TC ⊤
intro hole k = do
  ty ← inferType hole
  case ty of λ where
    (pi argTy@(arg (arg-info v _) _) (abs x ty′)) → do
      ctx ← getContext
      hole′ ← inContext (argTy ∷ ctx) $ do
        hole′ ← newMeta ty′
        return hole′
      unifyStrict (hole , ty) (lam v (abs "_" hole′))
      extendContext argTy $ do
        k hole′
    _ → k hole

{-# TERMINATING #-}
intros : Hole → Tactic → TC ⊤
intros hole k = do
  ty ← inferType hole
  case ty of λ where
    (pi argTy@(arg (arg-info v _) _) (abs _ ty′)) → do
      ctx ← getContext
      print $ "\t* " ◇ show argTy
      printContext ctx
      hole′ ← inContext (argTy ∷ ctx) $ do
        hole′ ← newMeta ty′
        return hole′
      unifyStrict (hole , ty) (lam v (abs "_" hole′))
      extendContext argTy $ do
        intros hole′ k
    _ → k hole

private
  fillFromContext : Tactic
  fillFromContext hole = do
    ty ← inferType hole
    ctx ← getContext
    printContext ctx
    let n = length ctx
    let vs = applyUpTo ♯ n
    unifyStricts (hole , ty) vs

  macro
    intro→fill : Tactic
    intro→fill hole = do
      print "***********************"
      inferType hole >>= printS
      print "***********************"
      intro hole fillFromContext

    intros→fill : Tactic
    intros→fill hole = do
      print "***********************"
      inferType hole >>= printS
      print "***********************"
      intros hole fillFromContext

  _ : ℕ → ℕ
  _ = intro→fill

  _ : ∀ (n : ℕ) → ℕ
  _ = intro→fill

  _ : ∀ {n : ℕ} → ℕ
  _ = intro→fill

  _ : ∀ ⦃ n : ℕ ⦄ → ℕ
  _ = intro→fill

  _ : Bool → Bool
  _ = intro→fill

  _ : ∀ (n : Bool) → Bool
  _ = intro→fill

  _ : ∀ {n : Bool} → Bool
  _ = intro→fill

  _ : ℕ → Bool → ℕ
  _ = intros→fill

  _ : Bool → ℕ → ℕ
  _ = intros→fill

  _ : (n : ℕ) → Bool → ℕ
  _ = intros→fill

  _ : ℕ → (b : Bool) → ℕ
  _ = intros→fill

  _ : (n : ℕ) (b : Bool) → ℕ
  _ = intros→fill

  _ : (n : ℕ) {b : Bool} → ℕ
  _ = intros→fill

  _ : {n : ℕ} {b : Bool} → ℕ
  _ = intros→fill

  _ : ∀ {n : Bool} → Bool
  _ = intros→fill

  _ : {n : ℕ} (b : Bool) → Bool
  _ = intros→fill

  _ : (n : ℕ) → Bool → Bool
  _ = intros→fill

  _ : {b : Bool} {n : ℕ} → ℕ
  _ = intros→fill

  _ : (b : Bool) {n : ℕ} → ℕ
  _ = intros→fill

  _ : ∀ {b : Bool} (n : ℕ) → ℕ
  _ = intros→fill

  _ : ∀ (b : Bool) (n : ℕ) → Bool
  _ = intros→fill

  open import Data.List.Membership.Propositional

  _ : ∀ {x : ℕ} {xs} → x ∈ xs → x ∈ xs
  _ = intro→fill

  _ : ∀ {x y : ℕ} {xs ys} → x ∈ xs → y ∈ ys → x ∈ xs
  _ = intros→fill

  _ : ∀ {x y : ℕ} {xs} → x ∈ xs → y ∈ xs → y ∈ xs
  _ = intros→fill
