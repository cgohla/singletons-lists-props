{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuasiQuotes              #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
module Data.Singletons.Prelude.List.Props where

import           Data.Singletons
-- import           Data.Singletons.Prelude.Bool
import           Data.Singletons.Prelude.Eq
import           Data.Singletons.Prelude.List

-- import           Data.Singletons.TH

-- import           GHC.TypeLits

-- | The proposition that a value appears in a list
data IsElem (x :: a) (xs :: [a]) where
  First :: Sing x -> IsElem x (x ': xs)
  Any :: IsElem y xs -> IsElem y (x ': xs)

-- | The proposition that all values in the first list are contained
-- in the second list
data IsSubList (xs :: [a]) (ys :: [a]) where
  Empty :: IsSubList '[] ys
  Insert :: IsElem x ys -> IsSubList xs ys -> IsSubList (x ': xs) ys

consWithProof :: Sing (x :: a)
              -> Sing (xs :: [a])
              -> (IsElem x (x ': xs), Sing (x ': xs :: [a]))
consWithProof x xs = (First x, SCons x xs)

-- | A singleton list in fact contains its element
singleElemLem :: Sing (x :: a) -> x `IsElem` '[x]
singleElemLem x = First x

-- | If on list is contained in another, it is also contained in the
-- list with an extra element
subListExtLem :: xs `IsSubList` ys -> xs `IsSubList` (y ': ys)
subListExtLem Empty        = Empty
subListExtLem (Insert e s) = Insert (Any e) $ subListExtLem s

-- | A list with one element dropped is contained in another, if the
-- original one was
subListRedLem :: (x ': xs) `IsSubList` ys -> xs `IsSubList` ys
subListRedLem (Insert _ s) = s

-- | Every list is contained in itself
subListReflLem :: Sing (xs :: [a]) ->  xs `IsSubList` xs
subListReflLem SNil = Empty
subListReflLem (SCons x xs) = Insert (First x) $ subListExtLem $ subListReflLem xs

-- | If an element is in a list, which is contained in a larger list,
-- then it is an element in the larger list
isElemTransLem :: x `IsElem` xs -> xs `IsSubList` zs -> x `IsElem` zs
isElemTransLem = undefined

-- | List containment is transitive
subListTransLem :: IsSubList xs ys -> IsSubList ys zs -> IsSubList xs ys
subListTransLem Empty _        = Empty
subListTransLem (Insert _ _) _ = undefined

-- $(singletons [d|
--                removeOne :: Eq a => a -> [a] -> [a]
--                removeOne y = filter (\x -> not ((==) y x))
--                remove :: Eq a => [a] -> [a] -> [a]
--                remove xs []       = xs
--                remove xs (y : ys) = removeOne y (remove xs ys)
--                |])

-- foo :: SEq a => Sing (x :: a) -> Sing (y :: a) -> Sing (If (x == y) "hello" "there")
-- foo x y = sIf (x %== y) (sing @"hello") (sing @"there")

-- -- | A list with an element removed anywhere is contained in a larger
-- -- list, if the original one was
-- subListRedGenLem :: SEq a => Sing (x :: a) -> xs `IsSubList` yx -> (RemoveOne x xs) `IsSubList` ys
-- subListRedGenLem x Empty          = Empty
-- subListRedGenLem x p@(Insert e s) = _

isElemElim :: forall a b (x :: a) (xs :: [a]).
              (forall (x' :: a) (xs' :: [a]) . Sing x' -> b x' xs')
           -> (forall (x' :: a) (xs' :: [a]) (y :: a) . b y xs' -> b y (x' ': xs'))
           -> IsElem x xs
           -> b x xs
isElemElim f _ (First s) = f s
isElemElim f g (Any e)   = g $ isElemElim f g e

isSubListElim :: (forall (x :: a) (xs' :: [a]). IsElem x ys -> b xs' -> b (x ': xs'))
            -> b '[]
            -> IsSubList xs ys
            -> b xs
isSubListElim _ b Empty        = b
isSubListElim f b (Insert e s) = f e $ isSubListElim f b s

type F x xs = Sing x
getElem :: IsElem x xs -> F x xs
getElem = isElemElim _ _

getSubList :: IsSubList xs ys -> SList xs
getSubList = isSubListElim _ SNil

-- -- | A list with an element removed anywhere is contained in a larger
-- -- list, if the original one was
-- subListRedGenLem :: SEq a => Sing (x :: a) -> xs `IsSubList` yx -> (Delete x xs) `IsSubList` ys
-- subListRedGenLem _ Empty                 = Empty
-- subListRedGenLem x (Insert a@(Any _) s)  = Insert _ _
-- subListRedGenLem x (Insert (First x') s) = _
-- -- we only need to remove the first occurrence

-- -- case e of
-- -- --                                       First x' -> sIf (x %== x') (subListRedLem s) _ -- sIf can't be used here, because that requires returning a singleton, which we don't want to do here.
-- --                                       Any e' -> _

-- -- -- subListRedGenLem :: SEq a => Sing (x :: a) -> Sing xs -> (RemoveOne x xs) `IsSubList` xs
-- -- -- subListRedGenLem _ SNil = Empty
-- -- -- subListRedGenLem x (SCons x' xs) = sIf (x %== x') _ _

-- -- -- In the end we want a proof that (xs `sRemove` ys) IsSubList xs

-- -- removeWithProof :: SEq a
-- --                 => Sing (xs :: [a])
-- --                 -> Sing (ys :: [a])
-- --                 -> ((Remove xs ys) `IsSubList` xs, Sing (Remove xs ys))
-- -- removeWithProof xs SNil = (_, xs)
-- -- removeWithProof xs ys   = (_, sRemove xs ys)

