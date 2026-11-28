import Burnett.Analysis.TransportWard.Weyl.PrincipalVariationDensityBridge
import Burnett.Analysis.TransportWard.Weyl.ThirdVariationCubicDensity

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

/-- The variable-coefficient third action is the A03 principal density
plus the actual terms containing the background first jet. -/
theorem coordinateActionThirdVariationDensity_eq_A03_principal_add_background
    {J : Type} [Fintype J] (S : J → Mat) (g : E → J → ℝ) (z w : RealEnergyField J)
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (x : E) (hx : x ∈ U)
    (hG : (assembleMetricComponents S (g x)).det ≠ 0) :
    let h (y : E) (i : J) := (z.val i y).re
    let k (y : E) (i : J) := (w.val i y).re
    let G := assembleMetricComponents S (g x)
    let H := assembleMetricComponents S (h x)
    let K := assembleMetricComponents S (k x)
    let p := coordinateMetricFirstJet g x
    let q := coordinateMetricFirstJet h x
    let v := coordinateMetricFirstJet k x
    let C (s t : ActionSlot J) := metricActionCoefficient S s t
    let CK (s t : ActionSlot J) (A : Mat) := fderiv ℝ (C s t) A K
    coordinateActionThirdVariationDensity S g h k x =
      (principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x).re +
      ∑ s, ∑ t, (secondFDeriv (C s t) G H H * v s * p t +
        fderiv ℝ (CK s t) G H * (q s * p t + p s * q t) +
        (1 / 2 : ℝ) * secondFDeriv (CK s t) G H H * p s * p t) := by
  intro h k G H K p q v C CK
  have hh : ContDiff ℝ ∞ h := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (z.val i).smooth'
  have hk : ContDiff ℝ ∞ k := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (w.val i).smooth'
  have hExact := coordinateActionThirdVariationDensity_eq_cubic_and_background S g h k x
    ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    (hh.differentiable (by simp) x) (hk.differentiable (by simp) x) hG
  have hPrincipal := principalVariationDensity_eq_actualLeadingThirdVariation S g z w x
  dsimp only at hExact hPrincipal
  rw [hExact, hPrincipal, Complex.ofReal_re]

end Burnett.V03.Palatini
