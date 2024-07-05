module Feynman.Frontend.OpenQASM3.Ast (Node (..), SourceRef (..), isNilNode) where

data SourceRef where
  NilRef :: SourceRef
  TextRef :: {sourceModule :: String, sourceLine :: Int, sourceColumn :: Maybe Int} -> SourceRef
  deriving (Eq, Read, Show)

data Node t c where
  NilNode :: Node t c
  Node :: {tag :: t, children :: [Node t c], context :: c} -> Node t c
  deriving (Eq, Read, Show)

isNilNode :: Node t c -> Bool
isNilNode NilNode = True
isNilNode _ = False

{--

-- I'm not sure these are good for anything

instance Functor (Node t) where
  fmap :: (a -> b) -> Node t a -> Node t b
  fmap f NilNode = NilNode
  fmap f (Node tag children ctx) = Node tag (map (fmap f) children) (f ctx)

instance Foldable (Node t) where
  foldMap :: (Monoid m) => (a -> m) -> Node t a -> m
  foldMap f NilNode = mempty
  foldMap f (Node tag children ctx) = f ctx <> foldMap (foldMap f) children

instance Traversable (Node t) where
  sequenceA :: (Applicative f) => Node t (f a) -> f (Node t a)
  sequenceA NilNode = pure NilNode
  sequenceA (Node tag children ctxA) =
    let mappedChildren = traverse sequenceA children
     in (Node tag <$> mappedChildren) <*> ctxA

--}
