module Feynman.Frontend.OpenQASM3.Chatty
  ( Chatty (..),
    fromEither,
    fromChattyFailure,
    fromChattyValue,
    hasChattyValue,
  )
where

import Data.Traversable

data Chatty w e v
  = ChattyFailure {chattyMessages :: [w], chattyFailure :: e}
  | ChattyValue {chattyMessages :: [w], chattyValue :: v}
  deriving (Eq, Read, Show)

instance (Semigroup v) => Semigroup (Chatty w e v) where
  -- (<>) :: (Semigroup v) => Chatty w e v -> Chatty w e v -> Chatty w e v
  (<>) (ChattyFailure msgs failure) _ = ChattyFailure msgs failure
  (<>) (ChattyValue msgsA valA) (ChattyFailure msgsB failure) = ChattyFailure (msgsA ++ msgsB) failure
  (<>) (ChattyValue msgsA valA) (ChattyValue msgsB valB) = ChattyValue (msgsA ++ msgsB) (valA <> valB)

instance (Monoid v) => Monoid (Chatty w e v) where
  -- mempty :: (Monoid v) => Chatty w e v
  mempty = ChattyValue [] mempty

instance Functor (Chatty w e) where
  -- fmap :: (a -> b) -> Chatty w e a -> Chatty w e b
  fmap f (ChattyFailure msgs failure) = ChattyFailure msgs failure
  fmap f (ChattyValue msgs val) = ChattyValue msgs (f val)

instance Applicative (Chatty w e) where
  -- pure :: a -> Chatty w e a
  pure = ChattyValue []

  -- (<*>) :: Chatty w e (a -> b) -> Chatty w e a -> Chatty w e b
  (<*>) (ChattyFailure msgs failure) _ = ChattyFailure msgs failure
  (<*>) (ChattyValue msgsA cont) (ChattyFailure msgsB failure) = ChattyFailure (msgsA ++ msgsB) failure
  (<*>) (ChattyValue msgsA cont) (ChattyValue msgsB val) = ChattyValue (msgsA ++ msgsB) (cont val)

instance Monad (Chatty w e) where
  -- return :: a -> Chatty w e a
  return = pure

  -- (>>=) :: Chatty w e a -> (a -> Chatty w e b) -> Chatty w e b
  (>>=) (ChattyFailure msgs failure) f = ChattyFailure msgs failure
  (>>=) (ChattyValue msgsA valA) f =
    case f valA of
      ChattyFailure msgsB failure -> ChattyFailure (msgsA ++ msgsB) failure
      ChattyValue msgsB valB -> ChattyValue (msgsA ++ msgsB) valB

instance Foldable (Chatty w e) where
  -- foldMap :: (Monoid m2) => (a -> m2) -> Chatty m1 f a -> m2
  foldMap f (ChattyFailure msgs failure) = mempty

instance Traversable (Chatty w e) where
  -- traverse :: (Applicative f) => (a -> f b) -> Chatty w e a -> f (Chatty w e b)
  traverse _ (ChattyFailure msgs failure) = pure (ChattyFailure msgs failure)
  traverse f (ChattyValue msgs val) = ChattyValue msgs <$> f val

fromEither :: Either e v -> Chatty w e v
fromEither (Left x) = ChattyFailure [] x
fromEither (Right y) = ChattyValue [] y

fromChattyFailure :: e -> Chatty w e v -> e
fromChattyFailure _ (ChattyFailure _ fail) = fail
fromChattyFailure fail _ = fail

fromChattyValue :: v -> Chatty w e v -> v
fromChattyValue _ (ChattyValue _ val) = val
fromChattyValue val _ = val

hasChattyValue :: Chatty w e v -> Bool
hasChattyValue (ChattyValue _ _) = True
hasChattyValue _ = False
