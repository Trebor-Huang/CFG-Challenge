open import Data.Nat.Base
open import Data.Nat.Properties hiding (_≟_)
open import Data.List hiding (align)
open import Data.List.Properties
open import Data.Sum.Base
open import Data.Product
open import Data.Empty
open import Function.Base
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary using (REL; Trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open        Relation.Binary.PropositionalEquality.≡-Reasoning
open import Data.List.Relation.Binary.Equality.Propositional using (≋⇒≡)
import Data.List.Relation.Binary.Prefix.Heterogeneous as Prefix
import Data.List.Relation.Binary.Infix.Heterogeneous as Infix
import Data.List.Relation.Binary.Infix.Heterogeneous.Properties as InfixProp
import Data.List.Relation.Binary.Suffix.Heterogeneous as Suffix
import Data.List.Relation.Binary.Pointwise as Pointwise

-- To be PR'd

module ListLemma where
open Infix using (MkView) renaming (toView to infixView) public
open Prefix using () renaming (_++_ to MkView; toView to prefixView) public
open Prefix using (Prefix; _++ᵖ_)
open Infix using (Infix)
open Suffix using (Suffix)

≥*2 : ∀ m → m ≥ m * 2 → m ≡ 0
≥*2 zero p = refl
≥*2 (suc m) p with ≥*2 m (≤-pred (≤-pred (≤-step p))) | p
... | refl | s≤s ()
module _ {a} {A : Set a} where
  -- TODO better names for these
  length-[] : {α : List A} → length α ≡ 0 → α ≡ []
  length-[] {[]} p = refl

  length-++-< : ∀ (α : List A) {β γ}
    → length β < length γ
    → length (α ++ β) < length (α ++ γ)
  length-++-< α {β} {γ} p
    rewrite length-++ α {β}
    rewrite length-++ α {γ}
    = +-monoʳ-< (length α) p

  length-++-≤ : ∀ (α : List A) {β}
    → length α ≤ length (α ++ β)
  length-++-≤ α {β}
    rewrite length-++ α {β} = m≤m+n _ _

  module _ {p} {P : Pred A p} (P? : Decidable P) where
    count : List A → ℕ
    count α = length (filter P? α)

    count-++ : ∀ α β
      → count (α ++ β) ≡ count α + count β
    count-++ α β
      rewrite filter-++ P? α β
      rewrite length-++ (filter P? α) {filter P? β} = refl

    count-++-comm : ∀ α β
      → count (α ++ β) ≡ count (β ++ α)
    count-++-comm α β rewrite count-++ α β | count-++ β α
      = +-comm (count α) _

  -- Prefix-Prefix -> Another prefix
  -- These are actually not used, but good PR
  module _ {b c d} {B : Set b}
    (R : REL A B c) (S : REL A A d)
    (trans : Trans R (flip R) S) where
    align : ∀ {α β γ}
      → Prefix R α γ
      → Prefix R β γ
      → Prefix S α β ⊎ Prefix S β α
    align Prefix.[] Prefix.[] = inj₁ Prefix.[]
    align Prefix.[] (x Prefix.∷ q) = inj₁ Prefix.[]
    align (x Prefix.∷ p) Prefix.[] = inj₂ Prefix.[]
    align (u Prefix.∷ p) (v Prefix.∷ q) with align p q
    ... | inj₁ x = inj₁ (trans u v Prefix.∷ x)
    ... | inj₂ y = inj₂ (trans v u Prefix.∷ y)

  reflᵖ : {α : List A} → Prefix _≡_ α α
  reflᵖ {[]} = Prefix.[]
  reflᵖ {x ∷ α} = refl Prefix.∷ reflᵖ

  ++-align : ∀ α β {γ δ : List A}
    → α ++ γ ≡ β ++ δ
    → Prefix _≡_ α β ⊎ Prefix _≡_ β α
  ++-align α β {γ} {δ} p = align _≡_ _≡_
    (λ { refl refl → refl })
    (reflᵖ ++ᵖ γ)
    (subst (λ υ → Prefix _≡_ β υ) (sym p) (reflᵖ ++ᵖ δ))

  ++-∷-align : ∀ α β {b} {γ δ : List A}
    → b ∷ α ++ γ ≡ β ++ δ
    → β ≡ []
    ⊎ Prefix _≡_ (b ∷ α) β
    ⊎ Σ (List A) λ β'
    → β ≡ b ∷ β'
    × Prefix _≡_ β' α
  ++-∷-align α β {b} {γ} {δ} p with b ∷ α in q
  ... | α' with ++-align α' β $ subst (λ α' → α' ++ γ ≡ β ++ δ) q p
  ... | inj₁ x = inj₂ (inj₁ x)
  ... | inj₂ y with prefixView y
  ... | MkView r σ with ≋⇒≡ r
  ++-∷-align α [] {b} {γ} {δ} p | .(_ ++ σ) | inj₂ _ | MkView r σ | refl = inj₁ refl
  ++-∷-align α (x ∷ β) {b} {γ} {δ} p | .(_ ++ σ) | inj₂ _ | MkView r σ | refl
    rewrite ∷-injectiveˡ q | ∷-injectiveʳ q = inj₂ (inj₂ (β , refl ,
      Prefix.fromView (MkView (Pointwise.refl refl) σ)))

open import Lang
open import Data.Bool as Bool using (_≟_) renaming (Bool to Symbol; true to 𝕀; false to 𝕆)

count-01 : Lang.count 𝕆 α ≡ 0 → Lang.count 𝕀 α ≡ 0 → length α ≡ 0
count-01 {[]} p q = refl
count-01 {𝕆 ∷ α} () q
count-01 {𝕀 ∷ α} p ()

count-replicate : ∀ {n} → Lang.count 𝕀 (replicate n 𝕆) ≡ 0
count-replicate {zero} = refl
count-replicate {suc n} = count-replicate {n}

++-Good-comm : ∀ α {β} → Good (α ++ β) → Good (β ++ α)
++-Good-comm α {β} G = begin
    Lang.count 𝕆 (β ++ α)
  ≡⟨ count-++-comm (_≟ 𝕆) β α ⟩
    Lang.count 𝕆 (α ++ β)
  ≡⟨ G ⟩
    Lang.count 𝕀 (α ++ β) * 2
  ≡˘⟨ cong (_* 2) $ count-++-comm (_≟ 𝕀) β α ⟩
    Lang.count 𝕀 (β ++ α) * 2
  ∎

-- A staged view
data Sublumped : List Symbol → Set where
  [] : Sublumped []
  𝕀∷_ : Sublumped α → Sublumped (𝕀 ∷ α)
  𝕀∷𝕆∷_ : Sublumped α → Sublumped (𝕀 ∷ 𝕆 ∷ α)

data Lumped : List Symbol → Set where
  ↑_ : Sublumped α → Lumped α
  𝕆∷_ : Lumped α → Lumped (𝕆 ∷ α)

data SublumpedView : List Symbol → Set where
  view[] : SublumpedView []
  view𝕀 : Sublumped α → SublumpedView (α ++ 𝕀 ∷ [])
  view𝕀𝕆 : Sublumped α → SublumpedView (α ++ 𝕀 ∷ 𝕆 ∷ [])

sublumpedView : Sublumped α → SublumpedView α
sublumpedView [] = view[]
sublumpedView (𝕀∷ ς) with sublumpedView ς
... | view[] = view𝕀 ς
... | view𝕀 ς = view𝕀 (𝕀∷ ς)
... | view𝕀𝕆 ς = view𝕀𝕆 (𝕀∷ ς)
sublumpedView (𝕀∷𝕆∷ ς) with sublumpedView ς
... | view[] = view𝕀𝕆 ς
... | view𝕀 ς = view𝕀 (𝕀∷𝕆∷ ς)
... | view𝕀𝕆 ς = view𝕀𝕆 (𝕀∷𝕆∷ ς)

data LumpedView : List Symbol → Set where
  view : ∀ n → Sublumped α → LumpedView (replicate n 𝕆 ++ α)

lumpedView : Lumped α → LumpedView α
lumpedView (↑ ς) = view zero ς
lumpedView (𝕆∷ ℓ) with lumpedView ℓ
... | view n ς = view (1 + n) ς

lumped : ∀ α
  → ¬ Infix _≡_ (𝕀 ∷ 𝕆 ∷ 𝕆 ∷ []) α
  → Lumped α
lumped [] ¬H = ↑ []
lumped (𝕆 ∷ α) ¬H with lumped α (λ H → ¬H $ Infix.there H)
... | ↑ ς = 𝕆∷ ↑ ς
... | 𝕆∷ ℓ = 𝕆∷ 𝕆∷ ℓ
lumped (𝕀 ∷ []) ¬H = ↑ 𝕀∷ []
lumped (𝕀 ∷ 𝕀 ∷ α) ¬H with lumped (𝕀 ∷ α) (λ H → ¬H $ Infix.there H)
... | ↑ ς = ↑ 𝕀∷ ς
lumped (𝕀 ∷ 𝕆 ∷ []) ¬H = ↑ 𝕀∷𝕆∷ []
lumped (𝕀 ∷ 𝕆 ∷ 𝕀 ∷ α) ¬H with lumped (𝕆 ∷ 𝕀 ∷ α) (λ H → ¬H $ Infix.there H)
... | 𝕆∷ (↑ ς) = ↑ 𝕀∷𝕆∷ ς
lumped (𝕀 ∷ 𝕆 ∷ 𝕆 ∷ α) ¬H = ⊥-elim $ ¬H
  $ Infix.here $ refl Prefix.∷ refl Prefix.∷ refl Prefix.∷ Prefix.[]

sublumped-count : Sublumped α
  → Lang.count 𝕀 α ≥ Lang.count 𝕆 α
sublumped-count [] = z≤n
sublumped-count (𝕀∷ ς) = ≤-step (sublumped-count ς)
sublumped-count (𝕀∷𝕆∷ ς) = s≤s (sublumped-count ς)

lumped-Scan : Lumped α → Good α → Scan α
lumped-Scan {α} (↑ ς) p
  = subst Scan (sym $ length-[] $ count-01 {α} eq₀ eq₁) Sc[]
  where
    q = sublumped-count ς
    eq₁ : Lang.count 𝕀 α ≡ 0
    eq₁ = ≥*2 _ $ ≤-trans (≤-reflexive $ sym p) q
    eq₀ : Lang.count 𝕆 α ≡ 0
    eq₀ = n≤0⇒n≡0 $ ≤-trans q $ ≤-reflexive eq₁

lumped-Scan (𝕆∷ ↑ ς) p with sublumpedView ς
lumped-Scan (𝕆∷ (↑ ς)) () | view[]
... | view𝕀𝕆 _ = ScIO _
... | view𝕀 {α} ς
  = case absurd of λ ()
  where
    eq₁ : Lang.count 𝕀 α ≡ 0
    eq₁ = ≥*2 _ $ ≤-trans (≤-pred
      $ ≤-step
      $ ≤-reflexive
      $ sym
      $ suc-injective
      $ ++-Good-comm (𝕆 ∷ α) p) -- count 𝕆 α ≥ count 𝕀 α * 2
      $ sublumped-count ς       -- count 𝕆 α ≤ count 𝕀 α
    eq₀ : Lang.count 𝕆 α ≡ 0
    eq₀ = n≤0⇒n≡0 $ ≤-trans (sublumped-count ς) $ ≤-reflexive eq₁
    eq : α ≡ []
    eq = length-[] $ count-01 {α} eq₀ eq₁
    absurd : 1 ≡ 2
    absurd = subst (λ α → Lang.count 𝕆 (𝕆 ∷ α ++ [ 𝕀 ])
                        ≡ Lang.count 𝕀 (𝕆 ∷ α ++ [ 𝕀 ]) * 2)
      eq p
lumped-Scan (𝕆∷ 𝕆∷ ℓ) p with lumpedView ℓ
... | view n ς with sublumpedView ς
... | view[] rewrite ++-identityʳ (replicate n 𝕆)
      | count-replicate {n} = case p of λ ()
... | view𝕀 {α} _ rewrite sym $ ++-assoc (replicate n 𝕆) α [ 𝕀 ]
  = ScI (replicate n 𝕆 ++ α)
... | view𝕀𝕆 {α} _ rewrite sym $ ++-assoc (replicate n 𝕆) α (𝕀 ∷ 𝕆 ∷ [])
  = ScIO (replicate (1 + n) 𝕆 ++ α)

-- Reexport some stuff
infix? : Relation.Binary.Decidable (Infix {A = Symbol} _≡_)
infix? = InfixProp.infix? _≟_

-- Lastly we specialize the aligning to 4 consecutive matches
variable
  b b' b'' : Symbol
data [_++_++_++_≡_++_]View : (α β γ δ τ σ : List Symbol) → Set where
  view0 : ∀ α β γ δ → [ α ++ β ++ γ ++ δ ≡ [] ++ (α ++ β ++ γ ++ δ) ]View
  view1 : ∀ α β γ δ τ → [ (α ++ β) ++ γ ++ δ ++ τ ≡ α ++ (β ++ γ ++ δ ++ τ) ]View
  view2 : ∀ α β γ δ τ → [ α ++ (b ∷ β ++ γ) ++ δ ++ τ ≡ (α ++ b ∷ β) ++ (γ ++ δ ++ τ) ]View
  view3 : ∀ α β γ δ τ → [ α ++ β ++ (b ∷ γ ++ δ) ++ τ ≡ (α ++ β ++ b ∷ γ) ++ (δ ++ τ) ]View
  view4 : ∀ α β γ δ τ → [ α ++ β ++ γ ++ (b ∷ δ ++ τ) ≡ (α ++ β ++ γ ++ b ∷ δ) ++ (τ) ]View

++-view3
  :                           b'' ∷ δ ≡                          τ  ++ σ
  → [ α ++ b ∷ β ++ b' ∷ γ ++ b'' ∷ δ ≡ (α ++ b ∷ β ++ b' ∷ γ ++ τ) ++ σ ]View
++-view3 {b''} {δ} {[]} {σ} {α} {b} {β} {b'} {γ} refl rewrite ++-identityʳ γ
  = subst [ α ++ b ∷ β ++_++ b'' ∷ δ ≡ (α ++ b ∷ β ++ b' ∷ γ) ++ b'' ∷ δ ]View (++-identityʳ (_ ∷ γ)) $
  view3 _ _ γ [] _
++-view3 {.b''} {.(τ ++ σ)} {b'' ∷ τ} {σ} refl = view4 _ _ _ _ _


++-view2
  :                 b' ∷ γ ++ b'' ∷ δ ≡                τ  ++ σ
  → [ α ++ b ∷ β ++ b' ∷ γ ++ b'' ∷ δ ≡ (α ++ b ∷ β ++ τ) ++ σ ]View
++-view2 {b'} {γ} {b''} {δ} {τ} {σ} {α} {b} {β} p with ++-∷-align γ τ p
... | inj₁ refl rewrite ++-identityʳ β | sym p
   = subst [ α ++_++ b' ∷ γ ++ b'' ∷ δ ≡ (α ++ b ∷ β) ++ (b' ∷ γ ++ b'' ∷ δ) ]View (++-identityʳ (b ∷ β)) $
    view2 α β [] (b' ∷ γ) (b'' ∷ δ)
... | inj₂ (inj₁ x) with prefixView x
... | MkView q τ with ≋⇒≡ q
... | refl =  ++-view3 $ ++-cancelˡ γ $ trans (∷-injectiveʳ p) (++-assoc γ _ _)
++-view2 {b'} {_} {b''} {δ} {τ} {σ} {α} {b} {β} p | inj₂ (inj₂ (γ , refl , x)) with prefixView x
... | MkView q τ with ≋⇒≡ q
... | refl rewrite sym
    $ ++-cancelˡ γ
    $ trans (sym $ ++-assoc γ _ _)
    $ ∷-injectiveʳ p = view3 α (b ∷ β) γ τ (b'' ∷ δ)

++-view1
  :        b ∷ β ++ b' ∷ γ ++ b'' ∷ δ ≡       τ  ++ σ
  → [ α ++ b ∷ β ++ b' ∷ γ ++ b'' ∷ δ ≡ (α ++ τ) ++ σ ]View
++-view1 {b} {β} {b'} {γ} {b''} {δ} {τ} {σ} {α} p with ++-∷-align β τ p
... | inj₁ refl rewrite ++-identityʳ α | sym p
  = subst [_++ _ ++ _ ++ _ ≡ α ++ _ ]View (++-identityʳ α) $
  view1 α [] (b ∷ β) (b' ∷ γ) (b'' ∷ δ)
... | inj₂ (inj₁ x) with prefixView x
... | MkView q τ with ≋⇒≡ q
... | refl = ++-view2 $ ++-cancelˡ β $ trans (∷-injectiveʳ p) (++-assoc β _ _)
++-view1 {b} {β} {b'} {γ} {b''} {δ} {_} {σ} {α} p | inj₂ (inj₂ (τ , refl , x)) with prefixView x
... | MkView q β with ≋⇒≡ q
... | refl rewrite sym
    $ ++-cancelˡ τ
    $ trans (sym $ ++-assoc τ _ _)
    $ ∷-injectiveʳ p = view2 α τ β (b' ∷ γ) (b'' ∷ δ)

++-view
  :   α ++ b ∷ β ++ b' ∷ γ ++ b'' ∷ δ ≡ τ ++ σ
  → [ α ++ b ∷ β ++ b' ∷ γ ++ b'' ∷ δ ≡ τ ++ σ ]View
++-view {τ = []} refl = view0 _ _ _ _
++-view {α} {b} {β} {b'} {γ} {b''} {δ} {b₀ ∷ τ} {σ} p with ++-∷-align τ α (sym p)
... | inj₁ refl = ++-view1 p
... | inj₂ (inj₁ x) with prefixView x
... | MkView q α with ≋⇒≡ q
... | refl rewrite sym
    $ ++-cancelˡ τ
    $ trans (sym $ ++-assoc τ _ _)
    $ ∷-injectiveʳ p = view1 (b₀ ∷ τ) α (b ∷ β) (b' ∷ γ) (b'' ∷ δ)
++-view {_} {b} {β} {b'} {γ} {b''} {δ} {b₀ ∷ τ} {σ} p | inj₂ (inj₂ (α , refl , x)) with prefixView x
... | MkView q τ with ≋⇒≡ q
... | refl = ++-view1 $ ++-cancelˡ _ $ trans (∷-injectiveʳ p) $ ++-assoc α _ _


 