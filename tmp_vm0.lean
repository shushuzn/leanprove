
import Mathlib
open ArithmeticFunction

example : vonMangoldt 0 = 0 := by
  -- ArithmeticFunction 的默认值是 0
  have : vonMangoldt 0 = 0 := rfl
  exact this
