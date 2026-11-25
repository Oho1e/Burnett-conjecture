import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows

set_option autoImplicit false

namespace Burnett.A06

open Burnett.A02.FrequencySplit
open scoped ENNReal

/-- The two manuscript estimates differ only in which high test has
exponent two. The low input has exponent four in both. -/
def highSlotInputExponent (inputL2 : Bool) : ℝ := if inputL2 then 2 else 4

def highSlotTestExponent (inputL2 : Bool) : ℝ := if inputL2 then 4 else 2

theorem one_lt_highSlotInputExponent (inputL2 : Bool) : 1 < highSlotInputExponent inputL2 := by
  cases inputL2 <;> norm_num [highSlotInputExponent]

theorem one_lt_highSlotTestExponent (inputL2 : Bool) : 1 < highSlotTestExponent inputL2 := by
  cases inputL2 <;> norm_num [highSlotTestExponent]

private theorem triBalance_424 : triBalance 4 2 4 := by
  unfold triBalance
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  norm_num

private theorem triBalance_244 : triBalance 2 4 4 := by
  have h := triBalance_424
  unfold triBalance at h ⊢
  rw [add_comm (ENNReal.ofReal 2)⁻¹ (ENNReal.ofReal 4)⁻¹]
  exact h

theorem highSlotInputTestBalance (inputL2 : Bool) :
    triBalance (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) 4 := by
  cases inputL2
  · exact triBalance_424
  · exact triBalance_244

theorem highSlotTestInputBalance (inputL2 : Bool) :
    triBalance (highSlotTestExponent inputL2) (highSlotInputExponent inputL2) 4 := by
  cases inputL2
  · exact triBalance_244
  · exact triBalance_424

end Burnett.A06
