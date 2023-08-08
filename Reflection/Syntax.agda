{-# OPTIONS --safe --without-K #-}

module Reflection.Syntax where

open import MetaPrelude

open import Reflection.AST.Argument hiding (map) public
open import Reflection.AST.Term hiding (_≟_; getName) public
open import Reflection.AST.Name hiding (_≟_; _≈_; _≈?_) public
open import Reflection.AST.Definition hiding (_≟_) public
open import Reflection.AST.Meta hiding (_≟_; _≡ᵇ_; _≈_; _≈?_) public
open import Reflection.AST.Abstraction using (unAbs) public

open import Reflection.AST.Argument.Visibility using (Visibility) public
open import Reflection.AST.Abstraction using (unAbs) public
open import Reflection.AST.Argument using (vArg; hArg; iArg; unArg; _⟨∷⟩_; map-Args) public
open import Reflection using (Term; Type; Name; data-cons; pi; abs; Abs; Arg; Clause; data-type; record-type; var; con; def; lam; pat-lam; arg; agda-sort; lit; meta; unknown; Pattern; strErr; ErrorPart; arg-info; visible; Definition) public

open import Generics using (absName; getVisibility; findMetas; isMeta; UnquoteDecl; Tactic) public
