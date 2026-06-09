
import Mathlib
open Real

#check ContinuousOn.intervalIntegrable
#check Continuous.intervalIntegrable
#check continuousAt_log
#check (continuousAt_log (x := 1) (by norm_num : 1 ≠ 0))
