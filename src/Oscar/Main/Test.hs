{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE IncoherentInstances #-}

module Oscar.Main.Test where

import Oscar.Main.Prelude

data A = A Int
data B = B Int
data C = C Int

class Transmuter from to where
    transmute :: from -> to

instance (Transmuter from middle, Transmuter middle to) => Transmuter from to where
    transmute = (transmute :: middle -> to) . (transmute :: from -> middle)

instance Transmuter A B where
    transmute (A a) = B (a * 10 + 1)

instance Transmuter B C where
    transmute (B b) = C (b * 10 + 2)

foo :: Int -> C
foo = transmute . A
