import Burnett.Analysis.TransportWard.Weyl.EulerWeylImaginaryPairing
import Burnett.Analysis.PrincipalEnergy.Energy.CompactFourierNorms
import Burnett.Analysis.PrincipalEnergy.Fourier.FrequencyWeights

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.V03

open Filter Set MeasureTheory Burnett.Fourier
open Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.SymmetricEnergy (coordinateH1)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped BigOperators ComplexConjugate InnerProductSpace Topology

open private integrable_schwartz_pair integral_on_chart_eq_of_zeroOutside from Burnett.Analysis.TransportWard.Weyl.EulerWeylImaginaryPairing

/-- Compact support of the actual test permits reading a cutoff pairing
as the original coordinate pairing on its chart. -/
theorem compactMatrixTest_inner_eq_chart_of_plateau {ι : Type*} [Fintype ι]
    {U V : Set Space} (hU : IsOpen U) (hVU : V ⊆ U)
    (f g : CompactSchwartzComponents ι) (h : Space → ι → ℂ)
    (hf : ∀ i, tsupport (f.val i : Space → ℂ) ⊆ V)
    (hg : ∀ x ∈ V, ∀ i, g.val i x = h x i) :
    ⟪compactMatrixTestEquiv ι f, compactMatrixTestEquiv ι g⟫_ℂ =
      ∫ x in U, ∑ i, conj (f.val i x) * h x i := by
  rw [compactMatrixTestEquiv_inner]
  have h0 (x : Space) (hx : x ∉ V) (i : ι) : f.val i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hy => hx (hf i hy))
  calc
    _ = ∫ x, ∑ i, conj (f.val i x) * g.val i x := by
      symm
      exact integral_finset_sum _ (fun i _ => integrable_schwartz_pair (g.val i) (f.val i))
    _ = ∫ x in U, ∑ i, conj (f.val i x) * g.val i x := by
      symm
      apply integral_on_chart_eq_of_zeroOutside hU
      intro x hx
      simp only [h0 x (fun hV => hx (hVU hV)), map_zero, zero_mul, Finset.sum_const_zero]
    _ = _ := integral_congr_ae (.of_forall fun x => Finset.sum_congr rfl (fun i _ => by
      by_cases hx : x ∈ V
      · rw [hg x hx i]
      · simp only [h0 x hx i, map_zero, zero_mul]))

theorem tendsto_compactMatrixTestEquiv_zero {ι : Type*} [Fintype ι]
    (f : ℕ → CompactSchwartzComponents ι)
    (h : ∀ i, Tendsto (fun n => ‖((f n).val i).toLp 2 volume‖) atTop (𝓝 0)) :
    Tendsto (fun n => compactMatrixTestEquiv ι (f n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsum : Tendsto (fun n => ∑ i, ‖((f n).val i).toLp 2 volume‖ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] using
      (tendsto_finset_sum Finset.univ (fun i _ => (h i).pow 2))
  have he (n : ℕ) : ‖compactMatrixTestEquiv ι (f n)‖ =
      Real.sqrt (∑ i, ‖((f n).val i).toLp 2 volume‖ ^ 2) := by
    rw [compactMatrixTestEquiv_norm, matrixSchwartzL2Norm, PiLp.norm_eq_of_L2]
    rfl
  simpa only [he, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsum

theorem compactMatrixCoordinateH1_le_of_component_schwartzH1Energy {ι : Type*} [Fintype ι]
    (f : CompactSchwartzComponents ι) (C : ι → ℝ)
    (h : ∀ i, Real.sqrt (schwartzH1Energy (f.val i)) ≤ C i) :
    compactMatrixCoordinateH1 f ≤ Real.sqrt (∑ i, (C i) ^ 2) := by
  rw [compactMatrixCoordinateH1, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖schwartzCoordinateJet (f.val i)‖ ^ 2 ≤ C i ^ 2
  rw [schwartzCoordinateJet_norm]
  have he : coordinateH1 (f.val i) = Real.sqrt (schwartzH1Energy (f.val i)) := rfl
  rw [he]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (h i) 2

end Burnett.V03
