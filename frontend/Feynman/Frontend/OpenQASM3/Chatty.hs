module Feynman.Frontend.OpenQASM3.Chatty
  ( Chatty (..),
    fromEither,
    fromFailure,
    fromValue,
    Feynman.Frontend.OpenQASM3.Chatty.fail,
    prepend,
    append,
    succeeded,
    failed,
    -- messages,
  )
where

import Data.Traversable

-- Chatty is essentially an Either that also carries a list of messages, for
-- processes like compilation that produce a success or failure result but
-- also want to emit related informational messages along the way

data Chatty w e v
  = Failure {messages :: [w], error :: e}
  | Value {messages :: [w], value :: v}
  deriving (Eq, Read, Show)

instance (Semigroup v) => Semigroup (Chatty w e v) where
  -- (<>) :: (Semigroup v) => Chatty w e v -> Chatty w e v -> Chatty w e v
  (<>) (Failure msgs err) _ = Failure msgs err
  (<>) (Value msgsA valA) (Failure msgsB err) = Failure (msgsA ++ msgsB) err
  (<>) (Value msgsA valA) (Value msgsB valB) = Value (msgsA ++ msgsB) (valA <> valB)

instance (Monoid v) => Monoid (Chatty w e v) where
  -- mempty :: (Monoid v) => Chatty w e v
  mempty = Value [] mempty

instance Functor (Chatty w e) where
  -- fmap :: (a -> b) -> Chatty w e a -> Chatty w e b
  fmap f (Failure msgs err) = Failure msgs err
  fmap f (Value msgs val) = Value msgs (f val)

instance Applicative (Chatty w e) where
  -- pure :: a -> Chatty w e a
  pure = Value []

  -- (<*>) :: Chatty w e (a -> b) -> Chatty w e a -> Chatty w e b
  (<*>) (Failure msgs err) _ = Failure msgs err
  (<*>) (Value msgsA cont) (Failure msgsB err) = Failure (msgsA ++ msgsB) err
  (<*>) (Value msgsA cont) (Value msgsB val) = Value (msgsA ++ msgsB) (cont val)

instance Monad (Chatty w e) where
  -- return :: a -> Chatty w e a
  return = pure

  -- (>>=) :: Chatty w e a -> (a -> Chatty w e b) -> Chatty w e b
  (>>=) (Failure msgs err) f = Failure msgs err
  (>>=) (Value msgsA valA) f =
    case f valA of
      Failure msgsB err -> Failure (msgsA ++ msgsB) err
      Value msgsB valB -> Value (msgsA ++ msgsB) valB

instance Foldable (Chatty w e) where
  -- foldMap :: (Monoid m2) => (a -> m2) -> Chatty m1 f a -> m2
  foldMap f (Failure msgs err) = mempty

instance Traversable (Chatty w e) where
  -- traverse :: (Applicative f) => (a -> f b) -> Chatty w e a -> f (Chatty w e b)
  traverse _ (Failure msgs err) = pure (Failure msgs err)
  traverse f (Value msgs val) = Value msgs <$> f val

fromEither :: Either e v -> Chatty w e v
fromEither (Left x) = Failure [] x
fromEither (Right y) = Value [] y

fromFailure :: e -> Chatty w e v -> e
fromFailure _ (Failure _ err) = err
fromFailure err _ = err

fromValue :: v -> Chatty w e v -> v
fromValue _ (Value _ val) = val
fromValue val _ = val

fail :: e -> Chatty w e v
fail = Failure []

-- Just a little bit yucky
prepend :: w -> Chatty w e v -> Chatty w e v
prepend msg chatty = chatty {messages = msg : messages chatty}

append :: Chatty w e v -> w -> Chatty w e v
append chatty msg = chatty {messages = msg : messages chatty}

succeeded :: Chatty w e v -> Bool
succeeded (Value _ _) = True
succeeded _ = False

failed :: Chatty w e v -> Bool
failed (Failure _ _) = True
failed _ = False

-- messages :: Chatty w e v -> [w]
-- messages (Failure msgs _) = msgs
-- messages (Value msgs _) = msgs
