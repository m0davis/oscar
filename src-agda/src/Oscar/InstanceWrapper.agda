
module Oscar.InstanceWrapper where

-- given some record named "Class", shouldn't the following two

record InstanceWrapper : Set where
  no-eta-equality
  instance
    postulate Instance : Class

open InstanceWrapper record {} public

-- the above should be equivalent to:

instance
  postulate Instance : Class
