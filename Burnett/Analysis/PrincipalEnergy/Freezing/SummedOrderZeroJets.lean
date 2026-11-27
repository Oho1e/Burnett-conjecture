import Burnett.Analysis.PrincipalEnergy.Freezing.SummedFourierAction
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedTestComparison
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal BigOperators

/-- The actual coordinate jet of the input-dependent output. -/
def actualCoordinateJet (W : E → ℂ) (j : Index) (x : E) : ℂ :=
  fderiv ℝ W x (EuclideanSpace.single j 1)

/-- Real order-zero value and first-jet estimates for a literal Schwartz-input
action. The two constants distinguish derivatives of the input from derivatives
of the coefficients. -/
def SchwartzOrderZeroJetBound (Q : SchwartzMap E ℂ → E → ℂ) (A B : ℝ≥0∞) : Prop :=
  ∀ u : SchwartzMap E ℂ, let p := ENNReal.ofReal 3
    let W := Q u
    MemLp W p volume ∧ eLpNorm W p volume ≤ A * eLpNorm (u : E → ℂ) p volume ∧
      Differentiable ℝ W ∧
      ∀ j : Index, let d := actualCoordinateJet W j
        MemLp d p volume ∧
        eLpNorm d p volume ≤ A * eLpNorm (energyPartial j u : E → ℂ) p volume +
          B * eLpNorm (u : E → ℂ) p volume

private theorem coordinate_jet_bounds_operator_norm (L : E →L[ℝ] ℂ) (a : ℝ) (a0 : 0 ≤ a)
    (h : ∀ j : Index, ‖L (EuclideanSpace.single j 1)‖ ≤ a) : ‖L‖ ≤ 4 * a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  let bas := EuclideanSpace.basisFun Index ℝ
  have decomp : L y = ∑ j, bas.repr y j • L (EuclideanSpace.single j 1) := by
    have yEq : y = ∑ j, bas.repr y j • EuclideanSpace.single j 1 := by
      simpa only [bas, EuclideanSpace.basisFun_apply] using ((EuclideanSpace.basisFun Index ℝ).sum_repr y).symm
    calc
      L y = L (∑ j, bas.repr y j • EuclideanSpace.single j 1) := congrArg (fun v => L v) yEq
      _ = _ := by simp only [map_sum, map_smul]
  rw [decomp]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Index, ‖y‖ * a := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      have c : ‖bas.repr y j‖ ≤ ‖y‖ := (PiLp.norm_apply_le (bas.repr y) j).trans_eq (bas.repr.norm_map y)
      exact mul_le_mul c (h j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [Burnett.RicciSymbol.Index]; ring

/-- Real differentiability and actual coordinate-jet identities for a
pointwise absolutely summable family. -/
theorem actual_coordinate_jet_tsum {ι : Type} (G : ι → E → ℂ)
    (hG : ∀ k, Differentiable ℝ (G k)) (w : ι → ℝ) (hw : Summable w) (w0 : ∀ k, 0 ≤ w k)
    (M : ℝ) (M0 : 0 ≤ M)
    (bound : ∀ k x, ‖G k x‖ ≤ w k * M)
    (boundD : ∀ k j x, ‖actualCoordinateJet (G k) j x‖ ≤ w k * M) :
    Differentiable ℝ (fun x => ∑' k, G k x) ∧
      ∀ j : Index, actualCoordinateJet (fun x => ∑' k, G k x) j =
        (fun x => ∑' k, actualCoordinateJet (G k) j x) := by
  have hM := hw.mul_right M
  have hM4 := hM.mul_left 4
  have op (k : ι) (x : E) : ‖fderiv ℝ (G k) x‖ ≤ 4 * (w k * M) :=
    coordinate_jet_bounds_operator_norm _ _ (mul_nonneg (w0 k) M0) fun j => boundD k j x
  have start : Summable (fun k => G k 0) := Summable.of_norm_bounded hM (fun k => bound k 0)
  have hd (x : E) :=
    hasFDerivAt_tsum hM4 (fun k y => (hG k y).hasFDerivAt) op start x
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  intro j
  funext x
  let L := ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j (1 : ℝ))
  have H : Summable (fun k => fderiv ℝ (G k) x) := Summable.of_norm_bounded hM4 (fun k => op k x)
  change L (fderiv ℝ (fun y => ∑' k, G k y) x) = ∑' k, L (fderiv ℝ (G k) x)
  rw [(hd x).fderiv, L.map_tsum H]

/-- Sum exact physical values and first jets with one summable budget.
The input norms are kept independent of the number of Fourier modes. -/
theorem summed_order_zero_coordinate_L3 {ι : Type} [Countable ι]
    (G : ι → E → ℂ) (hG : ∀ k, Differentiable ℝ (G k))
    (hC : ∀ k j, Continuous (actualCoordinateJet (G k) j))
    (w : ι → ℝ) (hw : Summable w) (w0 : ∀ k, 0 ≤ w k) (M : ℝ) (M0 : 0 ≤ M)
    (bound : ∀ k x, ‖G k x‖ ≤ w k * M)
    (boundD : ∀ k j x, ‖actualCoordinateJet (G k) j x‖ ≤ w k * M)
    (Y : ℝ≥0∞) (Yfin : Y < ⊤) (X : Index → ℝ≥0∞) (Xfin : ∀ j, X j < ⊤)
    (hv : ∀ k, MemLp (G k) (ENNReal.ofReal 3) volume ∧
      eLpNorm (G k) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (w k) * Y)
    (hj : ∀ k j, MemLp (actualCoordinateJet (G k) j) (ENNReal.ofReal 3) volume ∧
      eLpNorm (actualCoordinateJet (G k) j) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (w k) * (X j + Y)) :
    let p := ENNReal.ofReal 3
    let A := ENNReal.ofReal (∑' k, w k)
    let W (x : E) := ∑' k, G k x
    MemLp W p volume ∧ eLpNorm W p volume ≤ A * Y ∧ Differentiable ℝ W ∧
      ∀ j : Index, let d := actualCoordinateJet W j
        MemLp d p volume ∧ eLpNorm d p volume ≤ A * X j + A * Y := by
  intro p A W
  obtain ⟨hW, jets⟩ := actual_coordinate_jet_tsum G hG w hw w0 M M0 bound boundD
  obtain ⟨WL, WB⟩ := patch_summed_L3_bound G W hW.continuous (fun _ => rfl) w hw w0 M bound Y Yfin hv
  refine ⟨WL, WB, hW, ?_⟩
  intro j d
  let D := fun k => actualCoordinateJet (G k) j
  have DiffC : Continuous (fun x => ∑' k, D k x) :=
    continuous_tsum (fun k => hC k j) (hw.mul_right M) (fun k x => boundD k j x)
  have dj : d = (fun x => ∑' k, D k x) := jets j
  have h := patch_summed_L3_bound D d (dj.symm ▸ DiffC) (fun x => congrFun dj x)
    w hw w0 M (fun k x => boundD k j x) (X j + Y) (ENNReal.add_lt_top.mpr ⟨Xfin j,Yfin⟩)
    (fun k => hj k j)
  exact ⟨h.1, h.2.trans_eq (mul_add A (X j) Y)⟩

end Burnett.A03
