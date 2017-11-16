
module Everything where

open import Oscar.Prelude public

-- meta-class
open import Oscar.Class public

-- classes
open import Oscar.Class.Amgu                                        public
open import Oscar.Class.Apply                                       public
open import Oscar.Class.Bind                                        public
open import Oscar.Class.Category                                    public
open import Oscar.Class.Congruity                                   public
open import Oscar.Class.Fmap                                        public
open import Oscar.Class.Functor                                     public
open import Oscar.Class.HasEquivalence                              public
open import Oscar.Class.Hmap                                        public
open import Oscar.Class.Injectivity                                 public
open import Oscar.Class.IsCategory                                  public
open import Oscar.Class.IsDecidable                                 public
open import Oscar.Class.IsEquivalence                               public
open import Oscar.Class.IsFunctor                                   public
open import Oscar.Class.IsPrecategory                               public
open import Oscar.Class.IsPrefunctor                                public
open import Oscar.Class.Leftstar                                    public
open import Oscar.Class.Leftunit                                    public
open import Oscar.Class.Map                                         public
open import Oscar.Class.Precategory                                 public
open import Oscar.Class.Prefunctor                                  public
open import Oscar.Class.Properthing                                 public
open import Oscar.Class.Pure                                        public
open import Oscar.Class.Quadricity                                  public
open import Oscar.Class.Reflexivity                                 public
open import Oscar.Class.Setoid                                      public
open import Oscar.Class.Similarity                                  public
open import Oscar.Class.SimilarityM                                 public
open import Oscar.Class.SimilaritySingleton                         public
open import Oscar.Class.Smap                                        public
open import Oscar.Class.Smapoid                                     public
open import Oscar.Class.Successor₀                                  public
open import Oscar.Class.Successor₁                                  public
open import Oscar.Class.Surjection                                  public
open import Oscar.Class.Surjextensionality                          public
open import Oscar.Class.Surjidentity                                public
open import Oscar.Class.Surjtranscommutativity                      public
open import Oscar.Class.Symmetrical                                 public
open import Oscar.Class.Symmetry                                    public
open import Oscar.Class.Thickandthin                                public
open import Oscar.Class.Transassociativity                          public
open import Oscar.Class.Transextensionality                         public
open import Oscar.Class.Transitivity                                public
open import Oscar.Class.Transleftidentity                           public
open import Oscar.Class.Transrightidentity                          public
open import Oscar.Class.Unit                                        public
open import Oscar.Class.[ExtensibleType]                            public
open import Oscar.Class.[IsExtensionB]                              public

-- individual instances
open import Oscar.Class.Amgu.Term∃SubstitistMaybe                   public
open import Oscar.Class.Congruity.Proposequality                    public
open import Oscar.Class.Congruity.Proposextensequality              public
open import Oscar.Class.HasEquivalence.ExtensionṖroperty            public
open import Oscar.Class.HasEquivalence.Ṗroperty                     public
open import Oscar.Class.HasEquivalence.Substitunction               public
open import Oscar.Class.Hmap.Transleftidentity                      public
open import Oscar.Class.Injectivity.Vec                             public
open import Oscar.Class.IsDecidable.Fin                             public
open import Oscar.Class.IsDecidable.¶                               public
open import Oscar.Class.Properthing.ExtensionṖroperty               public
open import Oscar.Class.Properthing.Ṗroperty                        public
open import Oscar.Class.Reflexivity.Function                        public
open import Oscar.Class.Smap.ExtensionFinExtensionTerm              public
open import Oscar.Class.Smap.ExtensionṖroperty                      public
open import Oscar.Class.Smap.TransitiveExtensionLeftṖroperty        public
open import Oscar.Class.Surjection.⋆                                public
open import Oscar.Class.Symmetrical.ExtensionalUnifies              public
open import Oscar.Class.Symmetrical.Symmetry                        public
open import Oscar.Class.Symmetrical.Unifies                         public
open import Oscar.Class.Transextensionality.Proposequality          public
open import Oscar.Class.Transitivity.Function                       public
open import Oscar.Class.[ExtensibleType].Proposequality             public

-- instance bundles
open import Oscar.Property.Category.AListProposequality                                         public
open import Oscar.Property.Category.ExtensionProposextensequality                               public
open import Oscar.Property.Category.Function                                                    public
open import Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality   public
open import Oscar.Property.Functor.SubstitunctionExtensionTerm                                  public
open import Oscar.Property.Monad.Maybe                                                          public
open import Oscar.Property.Propergroup.Substitunction                                           public
open import Oscar.Property.Setoid.ProductIndexEquivalence                                       public
open import Oscar.Property.Setoid.Proposequality                                                public
open import Oscar.Property.Setoid.Proposextensequality                                          public
open import Oscar.Property.Setoid.ṖropertyEquivalence                                           public
open import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality                 public
open import Oscar.Property.Thickandthin.FinTermProposequalityMaybeProposequality                public

-- data
open import Oscar.Data.Constraint                        public
open import Oscar.Data.Decidable                         public
open import Oscar.Data.Descender                         public
open import Oscar.Data.ExtensionṖroperty                 public
open import Oscar.Data.Fin                               public
open import Oscar.Data.List                              public
open import Oscar.Data.Maybe                             public
open import Oscar.Data.ProductIndexEquivalence           public
open import Oscar.Data.ProperlyExtensionNothing          public
open import Oscar.Data.Proposequality                    public
open import Oscar.Data.ṖropertyEquivalence               public
open import Oscar.Data.Substitist                        public
open import Oscar.Data.Substitunction                    public
open import Oscar.Data.Surjcollation                     public
open import Oscar.Data.Surjextenscollation               public
open import Oscar.Data.Term                              public
open import Oscar.Data.Vec                               public
open import Oscar.Data.¶                                 public
open import Oscar.Data.𝟘                                 public
open import Oscar.Data.𝟙                                 public
open import Oscar.Data.𝟚                                 public

-- class derivations
open import Oscar.Class.Leftunit.ToUnit                  public
open import Oscar.Class.Symmetry.ToSym                   public
open import Oscar.Class.Transleftidentity.ToLeftunit     public
