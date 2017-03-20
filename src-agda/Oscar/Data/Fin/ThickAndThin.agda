
module Oscar.Data.Fin.ThickAndThin where

open import Oscar.Data.Fin
open import Oscar.Class.ThickAndThin

import Data.Fin as F
import Data.Fin.Properties as F

instance ThickAndThinFin : ThickAndThin Fin
ThickAndThin.thin ThickAndThinFin = F.thin
ThickAndThin.thick ThickAndThinFin = F.thick
ThickAndThin.thin-injective ThickAndThinFin z = F.thin-injective {z = z}
ThickAndThin.thick∘thin=id ThickAndThinFin = F.thick-thin
ThickAndThin.check ThickAndThinFin = F.check
ThickAndThin.thin-check-id ThickAndThinFin = F.thin-check-id
