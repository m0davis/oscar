module CSV where

-- | Using LiquidHaskell for CSV lists
-- c.f. http://www.reddit.com/r/scala/comments/1nhzi2/using_shapelesss_sized_type_to_eliminate_real/



-- | Example

--     Item        Price
--     ----        -----
--     Espresso    2.25
--     Macchiato   2.75
--     Cappucino   3.35
--     Americano   2.25

-- | Type

data CSV = Csv { headers :: [String]
               , rows    :: [[String]]
               }

-- | Table

zumbarMenu = Csv [  "Item"     , "Price"]
                 [ ["Espresso" , "2.25" ]
                 , ["Macchiato", "2.75" ]
                 , ["Cappucino", "3.35" ]
                 -- , ["Americano", "2.25" ]
                 ]

{-
 TestLiquidCSV.hs:(26,18)-(30,18): Error: Liquid Type Mismatch
   Inferred type
     VV : {VV : [Char] | len VV >= 0 && len VV >= len ?b && len VV >= len ?c && len VV >= len ?a && len VV >= len ?f && len VV >= len ?d && len VV >= len ?e && len VV >= 0}

   not a subtype of Required type
     VV : {VV : [Char] | len VV > 0}

   In Context
     VV : {VV : [Char] | len VV >= 0 && len VV >= len ?b && len VV >= len ?c && len VV >= len ?a && len VV >= len ?f && len VV >= len ?d && len VV >= len ?e && len VV >= 0}
     ?e : {?e : [[Char]] | len ?e == 0 && (null ?e <=> true) && len ?e >= 0}
     ?a : {?a : [[[Char]]] | len ?a == 0 && (null ?a <=> true) && len ?a >= 0}
     ?c : {?c : [[Char]] | len ?c == 0 && (null ?c <=> true) && len ?c >= 0}
     ?d : {?d : [[Char]] | len ?d == 0 && (null ?d <=> true) && len ?d >= 0}
     ?b : {?b : [[Char]] | len ?b == 0 && (null ?b <=> true) && len ?b >= 0}
     ?f : {?f : [[Char]] | len ?f == 0 && (null ?f <=> true) && len ?f >= 0}

 TestLiquidCSV.hs:(26,18)-(30,18): Error: Liquid Type Mismatch
   Inferred type
     VV : {VV : [Char] | len VV >= 0 && len VV >= len ?b && len VV >= len ?c && len VV >= len ?d && len VV >= len ?e && len VV >= len ?a && len VV >= 0}

   not a subtype of Required type
     VV : {VV : [Char] | len VV > 0}

   In Context
     VV : {VV : [Char] | len VV >= 0 && len VV >= len ?b && len VV >= len ?c && len VV >= len ?d && len VV >= len ?e && len VV >= len ?a && len VV >= 0}
     ?d : {?d : [[[Char]]] | len ?d == 0 && (null ?d <=> true) && len ?d >= 0}
     ?c : {?c : [[Char]] | len ?c == 0 && (null ?c <=> true) && len ?c >= 0}
     ?e : {?e : [[Char]] | len ?e == 0 && (null ?e <=> true) && len ?e >= 0}
     ?a : {?a : [[Char]] | len ?a == 0 && (null ?a <=> true) && len ?a >= 0}
     ?b : {?b : [[Char]] | len ?b == 0 && (null ?b <=> true) && len ?b >= 0}

-}


-- | Off By One Errors

-- Eeks, we missed the header name!
{-
csvBad1 = Csv [  "Date" {- ??? -} ]
              [ ["Mon", "1"]
              , ["Tue", "2"]
              , ["Wed", "3"]
              ]
-}
-- Blergh! we missed a column.
{-
csvBad2 = Csv [  "Name" , "Age"  ]
              [ ["Alice", "32"   ]
              , ["Bob"  {- ??? -}]
              , ["Cris" , "29"   ]
              ]
-}
-- | Invariant

-- Want to *refine* the `CSV` type to specify that the *number* of
-- elements in each row is *exactly* the same as the   *number* of headers.

{- data CSV = Csv { headers :: [String]
                   , rows    :: [{v:[String] | (len v) = (len headers)}]
                   }
  @-}

{-@ data CSV = Csv { headers :: [String]
                   , rows    :: [{v:[{w:String | (length w) > 0}] | (len v) = (len headers)}]
                   }
  @-}


-- All is well!

csvGood = Csv ["Id", "Name", "Days"]
              [ ["1", "Jan", "31"]
              , ["2", "Feb", "28"]
              , ["3", "Mar", "31"]
              , ["4", "Apr", "30"]
              ]


-- | Bonus Points

-- How would you modify the specification to prevent table with
-- degenerate entries like this one?

deg = Csv [  "Id", "Name", "Days"]
          [ ["1" , "Jan" , "31"]
          , ["2" , "Feb" , ""]
          ]
