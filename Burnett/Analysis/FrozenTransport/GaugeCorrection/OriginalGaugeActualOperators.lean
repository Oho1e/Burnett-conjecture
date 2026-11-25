import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeA08Jets
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeOutputCutoff
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeMixedSource

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4500

noncomputable section
namespace Burnett.V08

open Set Metric Matrix MeasureTheory Burnett.P01 Burnett.A06 Burnett.A07 Burnett.A08
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Matrix ENNReal ComplexConjugate

local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A bounded-norm forward L² representative for each actual raw entry. The
constant is independent of the original low tensor and of both high fields. -/
theorem exists_originalGaugeRawEntry_operator (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16) (hCut : ∀ t : ℝ, 1 ≤ t → θ t = 0)
    (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0})
    (hOdd : ∀ x, a (-x) = -a x) (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen)
    (hSD : ∀ i j, ContDiffOn ℝ ∞ (fun x => S x i j) {x : E | x ≠ 0})
    (hS : ∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x) (i j : TensorSlot) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ProjectionSchwartzMatrix, ∃ T : SchwartzMap E ℂ → FirstOrderLp 2,
      (∀ u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T u) =
        originalGaugeRadianPair θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m w a C S z i j u v) ∧
      ∀ u : SchwartzMap E ℂ, ‖T u‖ ≤ D * (∑ k : TensorSlot, ‖(Burnett.C03.projectedGaugeComplement z k.1 k.2).toLp 4 volume‖) *
        highDerivativeLp4Sum u := by
  classical
  let η := gaugeCorrectionInfrared
  have η0 := gaugeCorrectionInfrared_zero 0 (by norm_num)
  let F (k : TensorSlot) := gaugeTriadAngularProfile θ κ m w a C S k i j
  obtain ⟨A,hA,build⟩ := exists_originalAngular_coordinateDerivative_commutator η gaugeRatioGuard
    (r:=1/2) (ρ:=1/4) (R:=1) (by norm_num) (by norm_num) (by norm_num) le_rfl
    gaugeCorrectionInfrared_smooth gaugeCorrectionInfrared_zero gaugeCorrectionInfrared_one
    gaugeRatioGuard_smooth (fun _ h => gaugeRatioGuard_vanishes h)
  have row (k : TensorSlot) : ∃ M : ℝ, 0 ≤ M ∧
      ∃ T : SchwartzMap E ℂ → (FirstOrderLp 4 →L[ℂ] FirstOrderLp 2),
        (∀ u H, ‖T u H‖ ≤ A * M * ‖H‖ * highDerivativeLp4Sum u) ∧
        ∀ H u v : SchwartzMap E ℂ, inner ℂ (v.toLp 2 volume) (T u (H.toLp 4 volume)) =
          radianHighPair (originalRegularizedAngularSymbol η gaugeRatioGuard (F k)) H u v := by
    obtain ⟨W,M,hW,sub,smooth,hM,jets⟩ := exists_gaugeTriadAngularProfile_jet_bound θ hθ κ hκ
      m w a ha C S hSD k i j 27
    obtain ⟨T,hT,hPair,_⟩ := build hW sub smooth M hM (fun n hn p hp x => jets n hn (p,(x:E)) ⟨hp,x.property⟩)
    exact ⟨M,hM,T,hT,hPair⟩
  choose M hM op bound pair using row
  let M0 := ∑ k : TensorSlot, M k
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg (fun k _ => hM k)
  let R := gaugeCorrectionOutputL2.adjoint
  let D := ‖R‖ * A * M0
  refine ⟨D,mul_nonneg (mul_nonneg (norm_nonneg R) hA) hM0,?_⟩
  intro z
  let G (k : TensorSlot) := Burnett.C03.projectedGaugeComplement z k.1 k.2
  let U (k : TensorSlot) (u : SchwartzMap E ℂ) := op k u ((G k).toLp 4 volume)
  let T (u : SchwartzMap E ℂ) := ∑ k : TensorSlot, R (U k u)
  refine ⟨T,?_,?_⟩
  · intro u v
    change inner ℂ (v.toLp 2 volume) (∑ k, R (U k u)) = ∑ k, _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro k _
    have action : inner ℂ (v.toLp 2 volume) (R (U k u)) =
        radianHighPair (originalRegularizedAngularSymbol η gaugeRatioGuard (F k)) (G k) u (gaugeCorrectionInfraredSchwartz v) := by
      rw [show inner ℂ (v.toLp 2 volume) (R (U k u)) = inner ℂ (gaugeCorrectionOutputL2 (v.toLp 2 volume)) (U k u)
        from gaugeCorrectionOutputL2.adjoint_inner_right _ _, gaugeCorrectionOutputL2_schwartz]
      exact pair k _ _ _
    have sym : gaugeRawEntry θ η η κ m w a C S k i j = fun x : Joint => (η ‖x.2+x.1‖ : ℂ) *
        originalRegularizedAngularSymbol η gaugeRatioGuard (F k) x :=
      funext (gaugeRawEntry_eq_filtered_A08 θ η η κ hκ hSmall hCut η0 m w a ha hOdd hHom C S hS k i j)
    rw [sym, gaugeCorrectionOutput_move]
    exact action
  · intro u
    have compare (k : TensorSlot) : ‖R (U k u)‖ ≤ D * ‖(G k).toLp 4 volume‖ * highDerivativeLp4Sum u := by
      have hk : M k ≤ M0 := Finset.single_le_sum (fun l _ => hM l) (Finset.mem_univ k)
      calc
        _ ≤ ‖R‖ * ‖U k u‖ := R.le_opNorm _
        _ ≤ ‖R‖ * (A * M0 * ‖(G k).toLp 4 volume‖ * highDerivativeLp4Sum u) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact (bound k u _).trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hA) (norm_nonneg _))
            (highDerivativeLp4Sum_nonneg u))
        _ = _ := by dsimp only [D]; ring
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k _ => compare k)).trans_eq (by rw [← Finset.sum_mul, ← Finset.mul_sum]))

end Burnett.V08
