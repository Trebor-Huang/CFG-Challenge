open import Data.Nat.Base
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
open import Data.Nat.Induction
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Binary.Equality.Propositional
open import Data.Bool using (_≟_) renaming (Bool to Symbol; true to 𝕀; false to 𝕆)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open        Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function.Base
open import Tactic.Cong
open import Tactic.MonoidSolver

module Proof where
open import Lang
open import ListLemma hiding (count)

insert : Lang (α ++ β) → Lang (α ++ 𝕀 ∷ 𝕆 ∷ 𝕆 ∷ β)
insert = helper refl
  where
    helper : γ ≡ α ++ β → Lang γ → Lang (α ++ 𝕀 ∷ 𝕆 ∷ 𝕆 ∷ β)
    helper {α = α} p (L I L₁ O L₂ O L₃) with ++-view {τ = α} p
    ... | view0 α β γ δ rewrite sym p = (∅ I ∅ O ∅ O L) I L₁ O L₂ O L₃
    ... | view1 α β γ δ τ = subst Lang (++-assoc α _ _) (insert L I L₁ O L₂ O L₃)
    ... | view2 α β γ δ τ = subst Lang (eq α _ _ δ _) (L I insert L₁ O L₂ O L₃)
      where
        eq : ∀ α β γ δ σ → α ++ (β ++ γ) ++ δ ++ σ ≡ (α ++ β) ++ γ ++ δ ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    ... | view3 α β γ δ τ = subst Lang (eq _ β _ _ _) (L I L₁ O insert L₂ O L₃)
      where
        eq : ∀ α β γ δ σ → α ++ β ++ (γ ++ δ) ++ σ ≡ (α ++ β ++ γ) ++ δ ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    ... | view4 α β γ δ τ = subst Lang (eq _ β γ _ _) (L I L₁ O L₂ O insert L₃)
      where
        eq : ∀ α β γ δ σ → α ++ β ++ γ ++ (δ ++ σ) ≡ (α ++ β ++ γ ++ δ) ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    helper {α = α} p (L O L₁ I L₂ O L₃) with ++-view {τ = α} p
    ... | view0 α β γ δ rewrite sym p = (∅ I ∅ O ∅ O L) O L₁ I L₂ O L₃
    ... | view1 α β γ δ τ = subst Lang (++-assoc α _ _) (insert L O L₁ I L₂ O L₃)
    ... | view2 α β γ δ τ = subst Lang (eq α _ _ δ _) (L O insert L₁ I L₂ O L₃)
      where
        eq : ∀ α β γ δ σ → α ++ (β ++ γ) ++ δ ++ σ ≡ (α ++ β) ++ γ ++ δ ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    ... | view3 α β γ δ τ = subst Lang (eq _ β _ _ _) (L O L₁ I insert L₂ O L₃)
      where
        eq : ∀ α β γ δ σ → α ++ β ++ (γ ++ δ) ++ σ ≡ (α ++ β ++ γ) ++ δ ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    ... | view4 α β γ δ τ = subst Lang (eq _ β γ _ _) (L O L₁ I L₂ O insert L₃)
      where
        eq : ∀ α β γ δ σ → α ++ β ++ γ ++ (δ ++ σ) ≡ (α ++ β ++ γ ++ δ) ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    helper {α = α} p (L O L₁ O L₂ I L₃) with ++-view {τ = α} p
    ... | view0 α β γ δ rewrite sym p = (∅ I ∅ O ∅ O L) O L₁ O L₂ I L₃
    ... | view1 α β γ δ τ = subst Lang (++-assoc α _ _) (insert L O L₁ O L₂ I L₃)
    ... | view2 α β γ δ τ = subst Lang (eq α _ _ δ _) (L O insert L₁ O L₂ I L₃)
      where
        eq : ∀ α β γ δ σ → α ++ (β ++ γ) ++ δ ++ σ ≡ (α ++ β) ++ γ ++ δ ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    ... | view3 α β γ δ τ = subst Lang (eq _ β _ _ _) (L O L₁ O insert L₂ I L₃)
      where
        eq : ∀ α β γ δ σ → α ++ β ++ (γ ++ δ) ++ σ ≡ (α ++ β ++ γ) ++ δ ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    ... | view4 α β γ δ τ = subst Lang (eq _ β γ _ _) (L O L₁ O L₂ I insert L₃)
      where
        eq : ∀ α β γ δ σ → α ++ β ++ γ ++ (δ ++ σ) ≡ (α ++ β ++ γ ++ δ) ++ σ
        eq α β γ δ σ = solve (++-monoid Symbol)
    helper {.[]} {[]} {[]} p ∅ = ∅ I ∅ O ∅ O ∅

-- We need to prove that Scan preserves goodness

module _ (α : List Symbol) where
  ScIOO-Good : Good (α ++ 𝕀 ∷ 𝕆 ∷ 𝕆 ∷ β) → Good (α ++ β)
  ScIOO-Good {β} G
    = ++-Good-comm β
    $ cong (_∸ 2)
      -- This removes the 𝕀 ∷ 𝕆 ∷ 𝕆 ∷ part, the same below
    $ ++-Good-comm α G

  ScIO-Good : Good (𝕆 ∷ α ++ 𝕀 ∷ 𝕆 ∷ []) → Good α
  ScIO-Good G
    = cong (_∸ 2) $ ++-Good-comm (𝕆 ∷ α) G

  ScI-Good : Good (𝕆 ∷ 𝕆 ∷ α ++ 𝕀 ∷ []) → Good α
  ScI-Good G
    = cong (_∸ 2) $ ++-Good-comm (𝕆 ∷ 𝕆 ∷ α) G

scan : Good α → Scan α
scan {α} Gα with infix? (𝕀 ∷ 𝕆 ∷ 𝕆 ∷ []) α
... | no ¬p = lumped-Scan (lumped _ ¬p) Gα
... | yes p with infixView p
... | MkView pref eq suff with ≋⇒≡ eq
... | refl = ScIOO pref

descent : Good α → Scan α
  → (∀ {β} → length β < length α → Good β → Lang β)
  → Lang α
descent Gα (ScIOO α) dc =
  insert $ dc (length-++-< α (m≤n+m _ 2)) (ScIOO-Good α Gα)
descent Gα (ScIO  α) dc =
  ∅ O dc (s≤s (length-++-≤ α)) (ScIO-Good α Gα) I ∅ O ∅
descent Gα (ScI   α) dc =
  ∅ O ∅ O dc (≤-step (s≤s (length-++-≤ α))) (ScI-Good α Gα) I ∅
descent Gα  Sc[]     dc = ∅

parse : Good α → Lang α  -- We perform a well-founded recursion
parse = <-rec (λ n → ∀ α → length α ≡ n → Good α → Lang α)
  (λ { _ dc α refl Gα → descent Gα (scan Gα) λ p → dc _ p _ refl })
  _ _ refl

-- A little utility
Good? : Decidable Good
Good? _ = _ ≟ₙ _
