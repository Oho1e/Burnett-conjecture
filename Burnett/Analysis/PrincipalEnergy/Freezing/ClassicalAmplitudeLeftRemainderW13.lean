import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeJointReduction
import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalLeftWeylComparison

set_option autoImplicit false
set_option maxHeartbeats 4400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

/-- The complete left symbol computed from the physical input Fourier
profile of the same compact amplitude. -/
def compactRadianReducedAmplitudeSymbol (A : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne A Rx Ry) : E → E → ℂ :=
  radianAmplitudeReduced (radianSchwartzAmplitudeProfile (compactRadianTwoPointSlice A Rx Ry h))

/-- The action computed by reducing the compact amplitude and adding
its actual compact smoothing kernel. -/
def compactRadianAmplitudeTestAction (A : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne A Rx Ry) (K : E → E → ℂ)
    (u : SchwartzMap E ℂ) : E → ℂ :=
  radianLeftQuantization (compactRadianReducedAmplitudeSymbol A Rx Ry h) u + compactKernelAction K u

theorem compact_radian_amplitude_diagonal_smooth (A : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne A Rx Ry) :
    ContDiff ℝ ∞ (fun p : E × E => A p.1 p.1 p.2) := by
  let arg (p : E × E) : E × E × E := (p.1,p.1,p.2)
  have c : ContDiff ℝ ∞ arg := contDiff_fst.prodMk (contDiff_fst.prodMk contDiff_snd)
  change ContDiff ℝ ∞ ((fun p : E × E × E => A p.1 p.2.1 p.2.2) ∘ arg)
  exact h.jointSmooth.comp c

private theorem radian_diagonal_amplitude_symbol_growth (A : E → E → E → ℂ) (Rx Ry : ℝ)
    (h : CompactRadianTwoPointOrderOne A Rx Ry) :
    RadianLeftSymbolGrowth (fun x ξ => A x x ξ) := by
  obtain ⟨D,D0,b⟩ := h.orderOneInputDeriv 0
  intro x
  have c : Continuous (fun ξ : E => A x x ξ) :=
    ((compact_radian_amplitude_diagonal_smooth A Rx Ry h).continuous.comp
      (continuous_const.prodMk continuous_id))
  refine ⟨c.measurable,D,D0,fun ξ => ?_⟩
  simpa only [norm_iteratedFDeriv_zero] using b x x ξ

/-- The physically cut off action with its smoothing kernel converges
to the actual action of the independently reduced left symbol. -/
theorem compact_radian_amplitude_test_action_tendsto
    (A : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne A Rx Ry)
    (K : E → E → ℂ) (κ : ℕ → SchwartzMap E ℂ)
    (κB : ∀ n ξ, ‖κ n ξ‖ ≤ 1) (κlimit : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1))
    (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => radianTwoPointCutoffAction A (κ n) u x + compactKernelAction K u x)
      atTop (𝓝 (compactRadianAmplitudeTestAction A Rx Ry h K u x)) := by
  have t := compact_radian_two_point_amplitude_cutoff_tendsto_left A Rx Ry h κ κB κlimit u x
  have b : Tendsto (fun _ : ℕ => compactKernelAction K u x) atTop (𝓝 (compactKernelAction K u x)) :=
    tendsto_const_nhds
  exact t.add b

/-- The literal operator difference from the diagonal left model is
the actual compact order-zero left remainder in both L³ and W¹,³. -/
theorem exists_compact_radian_amplitude_diagonal_difference_W13
    (P Rx Ry : ℝ) (hP : 0 < P) (hRP : Rx < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (ρone : ∀ x ∈ closedBall (0 : E) Rx, ρ x = 1)
    (A : E → E → E → ℂ) (h : CompactRadianTwoPointOrderOne A Rx Ry)
    (directions : RadianOrdinaryDirectionalAmplitudeBounds A) (K : E → E → ℂ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound (fun u =>
      compactRadianAmplitudeTestAction A Rx Ry h K u -
      classicalLocalLeftAction (fun x ξ => A x x ξ) K u) C C := by
  let b := compactRadianReducedAmplitudeSymbol A Rx Ry h
  let d (x ξ : E) := A x x ξ
  let r (x ξ : E) := b x ξ - d x ξ
  have scaled := compact_radian_scaled_order_one_of_directional A Rx Ry h directions
  have rS : RadianOrderZeroSymbolSeminorms r :=
    compact_radian_two_point_left_diagonal_remainder_order_zero A Rx Ry scaled
  have supp (x ξ : E) (outside : x ∉ closedBall (0 : E) Rx) : r x ξ = 0 := by
    have z : b x ξ = 0 := compact_radian_two_point_amplitude_reduced_support A Rx Ry h x ξ outside
    simp only [r,d,z,h.outputSupport x x ξ outside,sub_self]
  obtain ⟨C,Cf,CB⟩ := exists_radian_classical_order_zero_left_W13 P Rx hP hRP ρ hρ hS ρone r supp rS
  have rG : RadianLeftSymbolGrowth r := radian_left_symbol_growth_of_order_zero r rS
  have dG : RadianLeftSymbolGrowth d := radian_diagonal_amplitude_symbol_growth A Rx Ry h
  have split : (fun x ξ => r x ξ + d x ξ) = b := by
    funext x ξ
    exact sub_add_cancel (b x ξ) (d x ξ)
  have eq : (fun u => compactRadianAmplitudeTestAction A Rx Ry h K u - classicalLocalLeftAction d K u) =
      radianLeftQuantization r := by
    funext u
    have th := radian_left_quantization_add_actual r d rG dG u
    rw [split] at th
    change (radianLeftQuantization b u + compactKernelAction K u) -
      (radianLeftQuantization d u + compactKernelAction K u) = _
    rw [th]
    abel
  exact ⟨C,Cf,eq.symm ▸ CB⟩

end Burnett.A03
