{-# LANGUAGE RankNTypes, TypeOperators #-}
import Control.Monad
import Data.Void
import Bound.Var
import Bound.Var.Injections

------------------------------------------------------------------------------
{-
   Based on “Syntax for free: Representing Syntax with
   Binding using Parametricity” by Robert Atkey
-}

-- Open ST
type OST b t r a = (a -> b)             -> -- return
                   (t -> (r -> b) -> b) -> -- new
                   (r -> t -> b -> b)   -> -- upd
                   (r -> (t -> b) -> b) -> -- lkp
                   b

-- Higher-Order ST monad
type HOST t r a = forall b. OST b t r a

retH :: a -> HOST t r a
retH a rt _nw _up _lk = rt a

bindH :: HOST t r a -> (a -> HOST t r b) -> HOST t r b
bindH c f rt nw up lk = c (\a -> f a rt nw up lk) nw up lk

newH :: t -> HOST t r r
newH t rt nw _up _lk = nw t rt

updH :: r -> t -> HOST t r ()
updH r t rt _nw up _lk = up r t (rt ())

lkpH :: r -> HOST t r t
lkpH r rt _nw _up lk = lk r rt

------------------------------------------------------------------------------

type Succ = Var ()

data ST t r a
  = Ret a
  | New t (ST t (Succ r) a)
  | Upd r t (ST t r a)
  | Lkp r (t -> ST t r a)

mapR :: (r -> r') -> ST t r a -> ST t r' a
mapR f (Ret a)     = Ret a
mapR f (New t k)   = New t (mapR (fmap f) k)
mapR f (Upd r t k) = Upd (f r) t (mapR f k)
mapR f (Lkp r k)   = Lkp (f r) (mapR f . k)

instance Monad (ST t r) where
  return = Ret
  Ret a     >>= f = f a
  New t k   >>= f = New t (k >>= mapR return . f)
  Upd r t k >>= f = Upd r t (k >>= f)
  Lkp r k   >>= f = Lkp r (\t -> k t >>= f)

class MonadST st where

new :: t -> (forall r0. r0 -> ST t (Var r0 r) a) -> ST t r a
new t k = New t (k ())

upd :: (r0 ∈ r) => r0 -> t -> ST t r ()
upd r t = Upd (inj r) t (Ret ())

lkp :: (r0 ∈ r) => r0 -> ST t r t
lkp r = Lkp (inj r) Ret

run :: Eq r => (r -> t) -> ST t r a -> a
run f (Ret x)     = x
run f (New t k)   = run (unvar (const t) f) k
run f (Upd r t k) = run (\x -> if x == r then t else f x) k
run f (Lkp r k)   = run f (k $ f r)

runST :: (forall r. ST t r a) -> a
runST c = run absurd c

-- mov r0 r1
--   is
-- r0 := !r1
mov :: (r0 ∈ r, r1 ∈ r) => r0 -> r1 -> ST t r ()
mov r0 r1 = upd r0 =<< lkp r1

-- swp' r0 r1 rtmp
--  swaps contents of r0 and r1 writing rtmp as a temporary location
swp' :: (r0 ∈ r, r1 ∈ r, rtmp ∈ r) => r0 -> r1 -> rtmp -> ST t r ()
swp' r0 r1 rtmp =
  do mov rtmp r0
     mov r0   r1
     mov r1   rtmp

-- swp r0 r1
--  swaps contents of r0 and r1 allocating a temporary
--  reference to store the intermediate value
swp :: (r0 ∈ r, r1 ∈ r) => r0 -> r1 -> ST t r ()
swp r0 r1 =
  new undefined $ \rtmp ->
  swp' r0 r1 rtmp

easySwp :: (r0 ∈ r, r1 ∈ r) => r0 -> r1 -> ST t r ()
easySwp r0 r1 = do v0 <- lkp r0
                   mov r0 r1
                   upd r1 v0

exSwap :: t -> t -> ST t r (t, t)
exSwap x y =
  new x $ \r0 ->
  new y $ \r1 ->
  do swp r0 r1
     v1 <- lkp r1
     v0 <- lkp r0
     return (v0,v1)

exSum :: (Num a, r0 ∈ r, r1 ∈ r) => r0 -> r1 -> ST a r a
exSum r0 r1 = liftM2 (+) (lkp r0) (lkp r1)

facST :: (Enum a, Num a) => a -> ST a r a
facST a =
  new 1 $ \r -> do
    forM_ [1..a] $ \i -> do
      v <- lkp r
      upd r (i * v)
    v <- lkp r
    return v

whileM :: Monad m => m Bool -> m () -> m ()
whileM cond body = go
  where go = do b <- cond
                when b $ body >> go

facST' :: (Enum a, Num a, Ord a) => a -> ST a r a
facST' a =
  new 1 $ \r ->
  new a $ \ri -> do
    whileM (liftM (>=1) $ lkp ri) $ do
      v <- lkp r
      i <- lkp ri
      upd r  (i * v)
      upd ri (i - 1)
    v <- lkp r
    return v

host :: (r -> r') -> ST t r a -> HOST t r' a
host f (Ret x)     rt nw up lk = rt x
host f (New t k)   rt nw up lk = nw t $ \r -> host (unvar (const r) f) k rt nw up lk
host f (Upd r t k) rt nw up lk = up (f r) t (host f k rt nw up lk)
host f (Lkp r k)   rt nw up lk = lk (f r) $ \t -> host f (k t) rt nw up lk

-- -}
-- -}
-- -}
-- -}
-- -}
-- cheap holes
h = h
data H = H
