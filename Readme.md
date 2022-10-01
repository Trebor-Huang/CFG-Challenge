# A Context Free Language

Define a context free language with the rules:
```
S -> empty
S -> S 1 S 0 S 0 S
S -> S 0 S 1 S 0 S
S -> S 0 S 0 S 1 S
```
This generates some 01-strings with twice as many 0's as 1's. **Theorem**. `S` contains *every* string of this form. This repository contains an Agda formalization. Formalizations with other proof assistants are more than welcome!

The statement of the theorem is in `Lang.agda`, where the language is defined:

```agda
data Lang : List Symbol → Set where
  ∅ : Lang []
  _I_O_O_ : Lang α → Lang β → Lang γ → Lang δ
    → Lang (α ++ 𝕀 ∷ β ++ 𝕆 ∷ γ ++ 𝕆 ∷ δ)
  _O_I_O_ : Lang α → Lang β → Lang γ → Lang δ
    → Lang (α ++ 𝕆 ∷ β ++ 𝕀 ∷ γ ++ 𝕆 ∷ δ)
  _O_O_I_ : Lang α → Lang β → Lang γ → Lang δ
    → Lang (α ++ 𝕆 ∷ β ++ 𝕆 ∷ γ ++ 𝕀 ∷ δ)

count : Symbol → List Symbol → ℕ
count b bs = length (filter (_≟ b) bs)

Good : List Symbol → Set
Good bs = count 𝕆 bs ≡ count 𝕀 bs * 2
```

The main result is in `Proof.agda`:
```
parse : Good α → Lang α
```

We have `Decidable Good`, so gluing some stuff together and forgetting the proofs, we can produce a parsing function `[Bool] -> Maybe ParseTree`, where `ParseTree` is the non-dependent version of `Lang`. (Can I just mark `@0` on everything to make it work?)

You can use `agda -c Eval.agda` to compile everything. I wrote an additional `Main.hs` to do some testing. `ghc Main.hs -o Main` to compile. It will ask for a string (use I and O instead of 1 and 0), and will produce a representation of the parse tree.
