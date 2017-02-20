private
  record Dummy : Set₁ where
    constructor ⟨_⟩
    field
      {h} : Set
      nh : Set

pattern ⟪_,_⟫ h s = ⟨_⟩ {h} s
pattern ⟪_⟫ h = (⟨_⟩ {h} _)
