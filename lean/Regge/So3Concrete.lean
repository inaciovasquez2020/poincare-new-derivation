namespace Regge

structure so3 where
  data : Unit

def zero_so3 : so3 := ⟨()⟩
def exp_so3 (_ : so3) : so3 := zero_so3
def norm_so3 (_ : so3) : Nat := 0

end Regge
