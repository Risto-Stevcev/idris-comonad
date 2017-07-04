module Control.Comonad

import Control.Monad.Identity

--------------------------------------------------------------------------------
-- | Interfaces
--------------------------------------------------------------------------------

-- | `Comonad` extends the `Extend` class with the `extract` function
-- | which extracts a value, discarding the comonadic context.
-- |
-- | dual of |
-- | --------+----------
-- | Monad   | Comonad
-- | bind    | extend
-- | pure    | extract
-- | join    | duplicate

interface Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a

  extend : (w a -> b) -> w a -> w b
  extend f = map f . duplicate

  duplicate : w a -> w (w a)
  duplicate = extend id

interface Comonad w => VerifiedComonad (w : Type -> Type) where
  comonadLeftIdentity : (wx : w a) -> Control.Comonad.extract `extend` wx = wx
  comonadRightIdentity : (wx : w a) -> (f : w a -> b) -> extract (f `extend` wx) = f wx
  comonadAssociative : (wx : w a) -> (f : w b -> c) -> (g : w a -> b) ->
                       (extend f . extend g) wx = extend (f . extend g) wx

infixl 1 <<=
(<<=) : Comonad w => (w a -> b) -> w a -> w b
(<<=) = extend

-- | Forwards co-Kleisli composition
composeCoKleisli : Comonad w => (w a -> b) -> (w b -> c) -> w a -> c
composeCoKleisli f g w = g (f <<= w)

infixl 1 =>=
(=>=) : Comonad w => (w a -> b) -> (w b -> c) -> w a -> c
(=>=) = composeCoKleisli


--------------------------------------------------------------------------------
-- | Functions
--------------------------------------------------------------------------------

liftW : Comonad w => (a -> b) -> w a -> w b
liftW f = extend (f . extract)


--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------

Comonad Identity where
  duplicate = Id
  extract = runIdentity

VerifiedComonad Identity where
  comonadLeftIdentity (Id runIdentity) = Refl
  comonadRightIdentity (Id runIdentity) f = Refl
  comonadAssociative (Id runIdentity) f g = Refl
