import Burnett.Analysis.PrincipalEnergy.Quantization.FullActionProperties
import Burnett.Analysis.PrincipalEnergy.Commutator.RenormalizedKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Microlocal.AngularDyadicKernel
open scoped ComplexConjugate

/-- Formal symmetry of the actual first-order action on the original
scalar Schwartz tests, using Lean's second-slot linear convention. -/
def FirstOrderFormalSymmetry (a : E → E → ℂ) : Prop :=
  ∀ u v : SchwartzMap E ℂ,
    (∫ x, conj (u x)*firstOrderAction a v x) =
      ∫ x, conj (firstOrderAction a u x)*v x

def actualCoefficientCommutator (a : E → E → ℂ) (r v : SchwartzMap E ℂ) (x : E) : ℂ :=
  r x*firstOrderAction a v x - firstOrderAction a (scalarSchwartzProduct r v) x

theorem actualCoefficientCommutator_integrable {a : E → E → ℂ} (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (r v : SchwartzMap E ℂ) :
    Integrable (actualCoefficientCommutator a r v) := by
  have hF := firstOrderAction_integrable_of_compactBase hBase hCont v
  have hG := firstOrderAction_integrable_of_compactBase hBase hCont (scalarSchwartzProduct r v)
  exact (hF.bdd_mul r.continuous.aestronglyMeasurable
    ⟨SchwartzMap.seminorm ℝ 0 0 r,fun x => SchwartzMap.norm_le_seminorm ℝ r x⟩).sub hG

/-- The commutator on the actual common test pairings is formally
skew-adjoint for a real coefficient and a formally symmetric full symbol. -/
theorem actualCoefficientCommutator_formal_skew {a : E → E → ℂ}
    (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (hSym : FirstOrderFormalSymmetry a) (r : SchwartzMap E ℂ) (hr : ∀ x, conj (r x) = r x)
    (u v : SchwartzMap E ℂ) :
    (∫ x, conj (u x)*actualCoefficientCommutator a r v x) =
      -(∫ x, conj (actualCoefficientCommutator a r u x)*v x) := by
  let B (s : SchwartzMap E ℂ) (x : E) := firstOrderAction a s x
  let ru := scalarSchwartzProduct r u
  let rv := scalarSchwartzProduct r v
  have hBI (s : SchwartzMap E ℂ) : Integrable (B s) :=
    firstOrderAction_integrable_of_compactBase hBase hCont s
  have hLeft (u' v' : SchwartzMap E ℂ) : Integrable (fun x => conj (u' x)*B v' x) := by
    exact (hBI v').bdd_mul u'.continuous.aestronglyMeasurable.star
      ⟨SchwartzMap.seminorm ℝ 0 0 u',fun x => by rw [Complex.norm_conj]; exact SchwartzMap.norm_le_seminorm ℝ u' x⟩
  have hRight (u' v' : SchwartzMap E ℂ) : Integrable (fun x => conj (B u' x)*v' x) := by
    have hC : Integrable (fun x => conj (B u' x)) := (hBI u').norm.mono'
      (hBI u').aestronglyMeasurable.star (Eventually.of_forall fun x => (Complex.norm_conj (B u' x)).le)
    have h := hC.bdd_mul v'.continuous.aestronglyMeasurable
      ⟨SchwartzMap.seminorm ℝ 0 0 v',fun x => SchwartzMap.norm_le_seminorm ℝ v' x⟩
    simpa only [mul_comm (v' _)] using h
  have hL (x : E) : conj (u x)*actualCoefficientCommutator a r v x =
      conj (ru x)*B v x-conj (u x)*B rv x := by
    dsimp [actualCoefficientCommutator,ru,rv,B]
    rw [map_mul,hr x]
    ring
  have hR (x : E) : conj (actualCoefficientCommutator a r u x)*v x =
      conj (B u x)*rv x-conj (B ru x)*v x := by
    dsimp [actualCoefficientCommutator,ru,rv,B]
    rw [map_sub,map_mul,hr x]
    ring
  simp_rw [hL,hR]
  rw [integral_sub (hLeft ru v) (hLeft u rv),integral_sub (hRight u rv) (hRight ru v)]
  change (∫ x, conj (ru x)*firstOrderAction a v x) -
      (∫ x, conj (u x)*firstOrderAction a rv x) = _
  rw [hSym ru v,hSym u rv]
  exact (neg_sub _ _).symm

end Burnett.Analysis.FirstOrderDyadic
