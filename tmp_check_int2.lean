
import Mathlib
open Real

#check (Real.continuousAt_log (x := 2) (by norm_num)).intervalIntegrable
#check intervalIntegrable_of_continuousOn
#check (Real.continuousAt_log (x := 2) (by norm_num))
