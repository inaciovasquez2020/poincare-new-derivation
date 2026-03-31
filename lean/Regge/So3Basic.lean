import Mathlib.Data.Real.Basic
import Regge.Core

namespace Regge

abbrev so3 := ℝ × ℝ × ℝ

def zero_so3 : so3 := (0, 0, 0)

def so3_add (x y : so3) : so3 :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)

def exp_so3 (x : so3) : so3 := x

end Regge
