{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

{-|  Nothing to see here. Currently, this is simply a scratch area for testing 
     ideas or aiding debugging.
-}

module Oscar.Main.Test where

--import Oscar.Main.Prelude

--data A = A Int
--data B = B Int
--data C = C Int

--class Transmuter from to where
--    transmute :: from -> to

--instance (Transmuter from middle, Transmuter middle to) => Transmuter from to where
--    transmute = (transmute :: middle -> to) . (transmute :: from -> middle)

--instance Transmuter A B where
--    transmute (A a) = B (a * 10 + 1)

--instance Transmuter B C where
--    transmute (B b) = C (b * 10 + 2)

--foo :: Int -> C
--foo = transmute . A
