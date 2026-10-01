import Mathlib

variable (x y z : Int)

example (h₁ : x < y) (h₂ : y + 3 < z + 10) : x + 37 < z + 44 := by
  linarith

example : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example :
    27 ≤ 11*x + 13*y → 11*x + 13*y ≤ 45
    → -10 ≤ 7*x - 9*y → 7*x - 9*y > 4 := by
  grind
