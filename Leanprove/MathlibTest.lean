/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (project contributors)
-/

-- MathlibTest: verify Nat.Prime from Mathlib works
import Leanprove.Basic

-- Test a Mathlib theorem using the same import as Basic.lean
theorem mathlib_test : Nat.Prime 5 := by decide
