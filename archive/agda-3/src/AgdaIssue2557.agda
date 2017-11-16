{-# OPTIONS --allow-unsolved-metas #-}

module AgdaIssue2557 where

record Superclass : Set₁ where field super : Set

open Superclass ⦃ … ⦄ public

record Subclass : Set₁ where
  field
    ⦃ iSuperclass ⦄ : Superclass
    sub : super

open Subclass

postulate A : Set

instance

  SuperclassA : Superclass
  Superclass.super SuperclassA = A → A

postulate function-A : A → A

test-1 : Subclass
Subclass.sub test-1 = {!!} -- Goal: A → A

test-2 : Subclass
test-2 = record { sub = function-A } -- works

test-3 : Subclass
Subclass.iSuperclass test-3 = SuperclassA -- (could also put "it" here)
Subclass.sub test-3 = function-A -- works

test-4 : Subclass
Subclass.sub test-4 = {!function-A!} -- fails

-- test-5 : Subclass
-- Subclass.sub test-5 x = {!!} -- fails

test-6 : Subclass
Subclass.sub test-6 = {!λ x → {!!}!} -- fails
