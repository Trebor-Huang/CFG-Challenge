module Eval where
open import Data.List
open import Data.Maybe
open import Data.Bool as Bool renaming (Bool to Symbol; true to 𝕀; false to 𝕆)
open import Relation.Nullary using (yes; no)
open import Agda.Builtin.Equality
open import Lang
open import Proof
{-# FOREIGN GHC
  data ParseTree = Empty
    | IOO ParseTree ParseTree ParseTree ParseTree
    | OIO ParseTree ParseTree ParseTree ParseTree
    | OOI ParseTree ParseTree ParseTree ParseTree
    deriving Show
#-}
data ParseTree : Set where
  Empty : ParseTree
  IOO OIO OOI : (_ _ _ _ : ParseTree) → ParseTree
{-# COMPILE GHC ParseTree = data ParseTree (Empty | IOO | OIO | OOI) #-}

forget : Lang α → ParseTree
forget ∅ = Empty
forget (L I L₁ O L₂ O L₃) = IOO (forget L) (forget L₁) (forget L₂) (forget L₃)
forget (L O L₁ I L₂ O L₃) = OIO (forget L) (forget L₁) (forget L₂) (forget L₃)
forget (L O L₁ O L₂ I L₃) = OOI (forget L) (forget L₁) (forget L₂) (forget L₃)

reify : List Symbol → Maybe ParseTree
reify α with Good? α
... | yes Gα = just (forget (parse {α} Gα))
... | no _ = nothing
{-# COMPILE GHC reify as reify #-}
