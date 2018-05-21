{-# OPTIONS_GHC -fplugin=Plugin #-}

{-# LANGUAGE GADTs, DataKinds, TypeOperators, TypeFamilies,
  MultiParamTypeClasses, FlexibleInstances, PolyKinds,
  FlexibleContexts, UndecidableInstances, ConstraintKinds,
  ScopedTypeVariables, AllowAmbiguousTypes #-}

import Plugin (CmpType)
import Data.Kind (Type)
import Data.Type.Bool
import Data.Type.Equality
import Data.Typeable (Proxy(..))
import GHC.Types (RuntimeRep(..), TYPE)

data Dict c where
  Dict :: c => Dict c

test1 :: forall a . Dict (CmpType (TYPE 'LiftedRep) (TYPE 'LiftedRep) ~ GT); test1 = Dict


main :: IO ()
main = putStrLn "Test suite not yet implemented"
