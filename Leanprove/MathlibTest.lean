-- MathlibTest: verify Nat.Prime from Mathlib works
import Leanprove.Basic

-- Test a Mathlib theorem using the same import as Basic.lean
theorem mathlib_test : Nat.Prime 5 := by decide
