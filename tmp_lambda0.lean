import Mathlib
open ArithmeticFunction
#check vonMangoldt 0
#check (vonMangoldt 0 : ℝ) = 0
#check (Subtype.map (λ x => x) (λ x => trivial) : ArithmeticFunction ℝ → (ℕ → ℝ))
