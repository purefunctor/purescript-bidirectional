module Bidirectional.Leibniz where

import Data.Eq (class Eq)
import Data.Show (class Show)

newtype Leibniz ∷ ∀ k. k → k → Type
newtype Leibniz a b = Leibniz (∀ f. f a → f b)

instance Eq (Leibniz a b) where
  eq _ _ = true

instance Show (Leibniz a b) where
  show _ = "~"

infix 4 type Leibniz as ~

coe ∷ ∀ f a b. (a ~ b) → f a → f b
coe (Leibniz f) = f

refl ∷ ∀ a. (a ~ a)
refl = Leibniz (\x → x)

newtype Identity a = Identity a

unIdentity ∷ ∀ a. Identity a → a
unIdentity (Identity a) = a

coerce ∷ ∀ a b. (a ~ b) → a → b
coerce p a = unIdentity (coe p (Identity a))

newtype Flip ∷ ∀ x y. (y → x → Type) → x → y → Type
newtype Flip f a b = Flip (f b a)

unFlip ∷ ∀ f a b. Flip f a b → f b a
unFlip (Flip fba) = fba

symm ∷ ∀ a b. (a ~ b) → (b ~ a)
symm p = unFlip (coe p (Flip refl))
