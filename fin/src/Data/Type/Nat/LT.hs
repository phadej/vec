{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
module Data.Type.Nat.LT (
    LT (..),
    LTProof,
    withLTProof,
    -- * Lemmas
    ltReflAbsurd,
    ltSymAbsurd,
    ltTrans,
    ) where

import Data.Type.Nat
import Data.Type.Nat.LE

-- | An evidence \(n < m\) which is the same as (\1 + n \le m\).
type LTProof n m = LEProof ('S n) m

-------------------------------------------------------------------------------
-- Class
-------------------------------------------------------------------------------

-- | Less-Than-or. \(<\). Well-founded relation on 'Nat'.
--
-- GHC can solve this for us!
--
-- >>> ltProof :: LTProof Nat0 Nat4
-- LESucc LEZero
--
-- >>> ltProof :: LTProof Nat2 Nat4
-- LESucc (LESucc (LESucc LEZero))
--
-- >>> ltProof :: LTProof Nat3 Nat3
-- ...
-- ...error...
-- ...
--
class LT (n :: Nat) (m :: Nat) where
    ltProof :: LTProof n m

instance LE ('S n) m => LT n m where
    ltProof = leProof

withLTProof :: LTProof n m -> (LT n m => r) -> r
withLTProof p f = withLEProof p f -- eta expansion needed for old GHC

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

-- | \(\forall n : \mathbb{N}, n < n \to \bot \)
ltReflAbsurd :: LTProof n n -> a
ltReflAbsurd (LESucc p) = ltReflAbsurd p

-- | \(\forall n\, m : \mathbb{N}, n < m \to m < n \to \bot \)
ltSymAbsurd :: LTProof n m -> LTProof m n -> a
ltSymAbsurd (LESucc p) (LESucc q) = ltSymAbsurd p q

-- | \(\forall n\, m\, p : \mathbb{N}, n < m \to m < p \to n < p \)
ltTrans :: LTProof n m -> LTProof m p -> LTProof n p
ltTrans p (LESucc q) = leStep $ leTrans p q
