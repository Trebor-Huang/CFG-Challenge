open import Data.Nat using (ℕ; _+_; _*_)
open import Data.List
open import Data.Bool as Bool renaming (Bool to Symbol; true to 𝕀; false to 𝕆)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Lang where
variable
  α β γ δ τ σ : List Symbol

data Lang : List Symbol → Set where
  ∅ : Lang []
  _I_O_O_ : Lang α → Lang β → Lang γ → Lang δ
    → Lang (α ++ 𝕀 ∷ β ++ 𝕆 ∷ γ ++ 𝕆 ∷ δ)
  _O_I_O_ : Lang α → Lang β → Lang γ → Lang δ
    → Lang (α ++ 𝕆 ∷ β ++ 𝕀 ∷ γ ++ 𝕆 ∷ δ)
  _O_O_I_ : Lang α → Lang β → Lang γ → Lang δ
    → Lang (α ++ 𝕆 ∷ β ++ 𝕆 ∷ γ ++ 𝕀 ∷ δ)
infix 10 _I_O_O_ _O_I_O_ _O_O_I_

count : Symbol → List Symbol → ℕ
count b bs = length (filter (_≟ b) bs)

Good : List Symbol → Set
Good bs = count 𝕆 bs ≡ count 𝕀 bs * 2

-- A view of the lists
data Scan : List Symbol → Set where
  ScIOO : ∀ α → Scan (α ++ 𝕀 ∷ 𝕆 ∷ 𝕆 ∷ β)
  ScIO  : ∀ α → Scan (𝕆 ∷ α ++ 𝕀 ∷ 𝕆 ∷ [])
  ScI   : ∀ α → Scan (𝕆 ∷ 𝕆 ∷ α ++ 𝕀 ∷ [])
  Sc[]  : Scan []
