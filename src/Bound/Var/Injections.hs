{-# LANGUAGE UnicodeSyntax, RankNTypes, TypeOperators, GADTs,
             MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
             IncoherentInstances, OverlappingInstances, ExplicitForAll,
             ConstraintKinds #-}
module Bound.Var.Injections where

import Data.Void
import Bound.Var

{-
class v ∈ a where
  inj :: v → a

instance x ∈ (Var x γ) where
  inj = B

instance (x ∈ γ) ⇒ x ∈ (Var y γ) where
  inj = F . inj
-}

class a ⊆ b where
  injMany :: a → b

instance a ⊆ a where injMany = id

instance Void ⊆ a where injMany = absurd

instance (a ⊆ b) ⇒ a ⊆ Var v b where
  injMany = F . injMany

instance (a ⊆ b) ⇒ Var v a ⊆ Var v b where
  injMany = fmap injMany

type v ∈ a = Var v Void ⊆ a

inj :: ∀ v a. (v ∈ a) ⇒ v → a
inj = injMany . justB
  where
    justB :: a -> Var a Void
    justB = B

var :: ∀ f v a. (v ∈ a, Monad f) ⇒ v → f a
var = return . inj

wk :: (Functor f, a ⊆ b) ⇒ f a → f b
wk = fmap injMany

-- not sure of the name, the uses... but it came in handy several times
wk' :: (Functor f, v ∈ a) ⇒ f v → f a
wk' = fmap inj
