namespace Regge

structure so3 where
  data : Unit

def zero_so3 : so3 := ⟨()⟩

def so3_add (_ _ : so3) : so3 := zero_so3
def so3_neg (_ : so3) : so3 := zero_so3
def so3_sub (_ _ : so3) : so3 := zero_so3
def so3_bracket (_ _ : so3) : so3 := zero_so3

end Regge
