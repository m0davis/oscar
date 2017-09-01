
open import Oscar.Prelude

module Test.ṖropertyFactsSubstitunction.imports where

open import Oscar.Prelude public
open import Oscar.Class.Factsurj3 public
open import Oscar.Class.Factsurj4 public
open import Oscar.Class.HasEquivalence public
open import Oscar.Class.Leftstar public
open import Oscar.Class.Leftunit public
open import Oscar.Class.Properthing public
open import Oscar.Class.Quadricity public
open import Oscar.Class.Similarity public
open import Oscar.Class.Smap                  public
open import Oscar.Class.Symmetrical                         public
open import Oscar.Class.Unit                                public
open import Oscar.Data.Proposequality                       public
open import Oscar.Data.Substitunction                       public
open import Oscar.Data.Surjcollation                        public
open import Oscar.Data.Surjextenscollation                  public
open import Oscar.Data.Term                                 public

open import Oscar.Class.HasEquivalence.ExtensionṖroperty public
open import Oscar.Class.HasEquivalence.Ṗroperty                  public
open import Oscar.Class.HasEquivalence.Substitunction            public
open import Oscar.Class.Properthing.ExtensionṖroperty            public
open import Oscar.Class.Properthing.Ṗroperty                     public
open import Oscar.Class.Smap.ExtensionṖroperty                   public
open import Oscar.Class.Smap.TransitiveExtensionLeftṖroperty     public
open import Oscar.Class.Symmetrical.ExtensionalUnifies           public
open import Oscar.Class.Symmetrical.Unifies                      public
open import Oscar.Class.[ExtensibleType].Proposequality          public
open import Oscar.Property.Functor.SubstitunctionExtensionTerm   public
open import Oscar.Property.Propergroup.Substitunction            public
open import Oscar.Property.Setoid.Proposequality                 public
open import Oscar.Class.Surjection.⋆                             public

module Data {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Term 𝔓 public using () renaming (
    Term to 𝑩;
    Terms to 𝑩';
    i to 𝒖;
    _fork_ to _⊛_)
  open Substitunction 𝔓 public using () renaming (
    Substitunction to 𝑪)

  𝑷⁰ = LeftṖroperty ℓ 𝑪
  𝑷¹ = LeftExtensionṖroperty ℓ 𝑪 _≈_
  infix 18 _∼⁰_
  _∼⁰_ = ≡-surjcollation⟦ 𝑪 ⟧
  open Surjextenscollation 𝑪 _≡̇_ public renaming (_⟹_ to _∼¹_)
