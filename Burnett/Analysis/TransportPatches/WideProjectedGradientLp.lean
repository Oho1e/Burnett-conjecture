import Burnett.Analysis.TransportPatches.WideBaselineL2
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

/-! The same full errors act on derivatives of the original projected field. -/
set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 7100000

noncomputable section

namespace Burnett.C02

open Set Metric Filter MeasureTheory Burnett.Fourier Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E homogeneous_multiplier_all_Lp_sphere_bound)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix projectionMatrixDerivative projectionFullSchwartz
  projectionFullSchwartz_coordinateDerivative)
open scoped BigOperators ContDiff ENNReal Topology

private theorem lpFinsetSum_ae {ι : Type*} {p : ℝ≥0∞} (J : Finset ι)
    (u : ι → Lp ℂ p (volume : Measure E)) :
    ((∑ j ∈ J, u j : Lp ℂ p (volume : Measure E)) : E → ℂ) =ᵐ[volume] fun ξ => ∑ j ∈ J, u j ξ := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℂ p (volume : Measure E)
  | insert j J hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (u j) (∑ i ∈ J, u i), ih] with x hx hy
      rw [hx, Pi.add_apply, hy]

private theorem exists_angularOutput_finiteLp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : RealOrderedAngularMatrix) (J : ℝ), 0 ≤ J →
      (∀ (k i : OrderedPair) (n : ℕ), n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n (fun η : E => S.matrix η k i) ξ‖ ≤ J) →
      ∀ (u : OrderedPair → SchwartzMap E ℂ) (k : OrderedPair),
      let P := ENNReal.ofReal p
      let v := S.output (fun i => (u i).toLp 2 volume) k
      MemLp (v : E → ℂ) P volume ∧ eLpNorm (v : E → ℂ) P volume ≤
        ENNReal.ofReal (C * J) * ∑ i : OrderedPair, eLpNorm (u i : E → ℂ) P volume := by
  obtain ⟨C, hC, hMikhlin⟩ := homogeneous_multiplier_all_Lp_sphere_bound p hp
  let P := ENNReal.ofReal p
  have hp₁ : 1 ≤ P := by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  letI : Fact (1 ≤ P) := ⟨hp₁⟩
  refine ⟨C, hC, ?_⟩
  intro S J hJ hJets u k P' v
  choose a T ha hT hL2 hSchwartz using fun i : OrderedPair =>
    hMikhlin (fun η => S.matrix η k i) (S.smooth k i)
      (fun t ht η => congrFun (congrFun (S.degree t ht η) k) i) J hJ (hJets k i)
  let A (i : OrderedPair) := T i ((u i).toLp P volume)
  let F (i : OrderedPair) := fourierMultiplier (S.coefficient k i) ((u i).toLp 2 volume)
  have hAgree (i : OrderedPair) : (A i : E → ℂ) =ᵐ[volume] (F i : E → ℂ) := by
    have h := hL2 i (u i) ((u i).memLp 2 volume) ((u i).memLp P volume)
    rw [fourierMultiplier_congr_ae (a i) _ (Eventually.of_forall fun ξ =>
      (ha i ξ).trans (S.coefficient_apply k i ξ).symm)] at h
    exact h
  have hAll : ∀ᵐ x ∂(volume : Measure E), ∀ i, A i x = F i x := ae_all_iff.mpr hAgree
  have hSum : ((∑ i : OrderedPair, A i : Lp ℂ P volume) : E → ℂ) =ᵐ[volume] (v : E → ℂ) := by
    filter_upwards [lpFinsetSum_ae Finset.univ A, lpFinsetSum_ae Finset.univ F, hAll]
      with x hA hF hPoint
    change (∑ i : OrderedPair, A i) x = (∑ i : OrderedPair, F i) x
    rw [hA, hF]
    exact Finset.sum_congr rfl (fun i _ => hPoint i)
  refine ⟨(memLp_congr_ae hSum).1 (Lp.memLp _), ?_⟩
  have hRow (i : OrderedPair) :
      eLpNorm (A i : E → ℂ) P volume ≤ ENNReal.ofReal (C * J) * eLpNorm (u i : E → ℂ) P volume := by
    have hR : ENNReal.ofReal (C * J) * eLpNorm (u i : E → ℂ) P volume ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((u i).memLp P volume).eLpNorm_lt_top).ne
    rw [← ENNReal.toReal_le_toReal (Lp.eLpNorm_lt_top (A i)).ne hR, ← Lp.norm_def,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC hJ),
      ← eLpNorm_congr_ae ((u i).coeFn_toLp P volume), ← Lp.norm_def]
    exact hT i _
  calc
    eLpNorm (v : E → ℂ) P volume = eLpNorm (fun x => ∑ i : OrderedPair, A i x) P volume :=
      eLpNorm_congr_ae (hSum.symm.trans (lpFinsetSum_ae Finset.univ A))
    _ ≤ ∑ i : OrderedPair, eLpNorm (A i : E → ℂ) P volume := by
      rw [show (fun x => ∑ i : OrderedPair, A i x) = ∑ i : OrderedPair, (A i : E → ℂ) from
        funext (fun x => (Finset.sum_apply _ _ _).symm)]
      exact eLpNorm_sum_le (fun i _ => Lp.aestronglyMeasurable (A i)) hp₁
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hRow i)

/-- The row bound uses the actual derivative of the projected field. Both
operators multiply that same field, with the same fixed infrared factor. -/
theorem exists_actualWide_projectedGradient_Lp (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (inner outer : ℝ) (m : ScreenMatrix)
      (hm : WideScreenFrequencySmooth inner outer m) (J : ℝ), 0 ≤ J →
      (∀ k i : OrderedPair, ∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1,
        ‖iteratedFDeriv ℝ n (fun η : E => (frozenScreenErrorAngular inner outer m hm).matrix η k i) ξ‖ ≤ J ∧
        ‖iteratedFDeriv ℝ n (fun η : E => (frozenPhaseErrorAngular inner outer m hm).matrix η k i) ξ‖ ≤ J) →
      ∀ (z : ProjectionSchwartzMatrix) (b : Index) (k : OrderedPair),
      let P := ENNReal.ofReal p
      let v₁ := multiplierCoordinateDerivative (actualFrozenScreenErrorMultiplier inner outer m hm) z b k
      let v₂ := multiplierCoordinateDerivative (actualFrozenPhaseErrorMultiplier inner outer m hm) z b k
      let R := ∑ i : OrderedPair, eLpNorm
        (projectionMatrixDerivative b (projectionFullSchwartz z) i.1 i.2 : E → ℂ) P volume
      (MemLp (v₁ : E → ℂ) P volume ∧ eLpNorm (v₁ : E → ℂ) P volume ≤ ENNReal.ofReal (C * J) * R) ∧
      (MemLp (v₂ : E → ℂ) P volume ∧ eLpNorm (v₂ : E → ℂ) P volume ≤ ENNReal.ofReal (C * J) * R) := by
  obtain ⟨C, hC, hRows⟩ := exists_angularOutput_finiteLp p hp
  refine ⟨C, hC, ?_⟩
  intro inner outer m hm J hJ hJet z b k P v₁ v₂ R
  let S₁ := frozenScreenErrorAngular inner outer m hm
  let S₂ := frozenPhaseErrorAngular inner outer m hm
  let f (i : OrderedPair) := projectionMatrixDerivative b (projectionFullSchwartz z) i.1 i.2
  let u (i : OrderedPair) := ((projectionMatrixDerivative b z) i.1 i.2).toLp 2 volume
  have hProjected (i : OrderedPair) : originalProjectedMatrixMultiplier.output u i = (f i).toLp 2 volume := by
    rw [show originalProjectedMatrixMultiplier.output u i =
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier z b i from rfl,
      originalProjectedMatrixMultiplier_derivative_eq_schwartz, projectionFullSchwartz_coordinateDerivative]
  have h₁ : v₁ = S₁.output (fun i => (f i).toLp 2 volume) k := by
    change (actualFrozenScreenErrorMultiplier inner outer m hm).output u k = _
    rw [(actualFrozenWideErrors_originalProjectedOutput inner outer m hm u k).1, funext hProjected]
  have h₂ : v₂ = S₂.output (fun i => (f i).toLp 2 volume) k := by
    change (actualFrozenPhaseErrorMultiplier inner outer m hm).output u k = _
    rw [(actualFrozenWideErrors_originalProjectedOutput inner outer m hm u k).2, funext hProjected]
  rw [h₁, h₂]
  exact ⟨hRows S₁ J hJ (fun l i n hn ξ hξ => (hJet l i n hn ξ hξ).1) f k,
    hRows S₂ J hJ (fun l i n hn ξ hξ => (hJet l i n hn ξ hξ).2) f k⟩

end Burnett.C02
