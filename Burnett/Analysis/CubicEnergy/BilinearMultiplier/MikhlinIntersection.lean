import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinFinite
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.MikhlinStrong

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.DyadicSquare (rescaleSymbol)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open Burnett.Analysis.SignedFourierWindow
open Finset MeasureTheory Filter Burnett.Fourier
open scoped Topology ContDiff ENNReal

/-- A genuine whole-space scalar multiplier estimate for every L² ∩ Lᵖ input
with the original Fourier transform on L². -/
theorem homogeneous_multiplier_intersection_bound (m : E → ℝ)
    (hm : ContDiffOn ℝ ∞ m {ξ | ξ ≠ 0}) (hh : ∀ t : ℝ, 0<t → ∀ ξ, m (t • ξ) = m ξ)
    (M : BoundedSymbol E) (hM : ∀ ξ, M ξ = (m ξ : ℂ)) (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (f : E → ℂ) (hf : MemLp f 2 volume),
      MemLp f (ENNReal.ofReal p) volume →
      eLpNorm (fourierMultiplier M (hf.toLp f) : E → ℂ) (ENNReal.ofReal p) volume ≤
        C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨a,ha,ac,cut⟩ := mikhlin_profile_exists m hm
  obtain ⟨C,hC,bound⟩ := signed_window_all_Lp a ac cut p hp
  refine ⟨C,hC,?_⟩
  intro f hf hfp
  let t := fun N : ℕ => ((2:ℝ)^N)⁻¹
  have ht (N : ℕ) : 0<t N := inv_pos.mpr (pow_pos (by norm_num) _)
  let I := fun N : ℕ => range (N+N)
  let A := fun n => mikhlinBands a cut (t n) (ht n) (I n)
  let F := hf.toLp f
  have ev : ∀ᵐ ξ ∂(volume : Measure E), ∀ᶠ N : ℕ in atTop, A N ξ = M ξ := by
    filter_upwards [(Set.countable_singleton (0:E)).ae_notMem volume] with ξ hx
    filter_upwards [mikhlin_scale_partition m hh a ha ξ hx] with n hn
    simpa only [A,t,I,mikhlinBands_eval,hM,bandFactor] using hn
  have conv := mikhlin_strong_L2 M A (2*SchwartzMap.seminorm ℝ 0 0 a) (fun n ξ => (A n).norm_le ξ) ev F
  obtain ⟨ns,_,aeLim⟩ := (tendstoInMeasure_of_tendsto_Lp conv).exists_seq_tendsto_ae
  have bn (n : ℕ) : eLpNorm (fourierMultiplier (A n) F : E → ℂ) (ENNReal.ofReal p) volume ≤
      C * eLpNorm f (ENNReal.ofReal p) volume := by
    rw [eLpNorm_congr_ae (mikhlinBands_all_L2 a ac cut (t n) (ht n) (I n) f hf)]
    simpa using bound (t n) (ht n) 0 (I n) (fun _ => 1) (by simp) f hfp
  exact (Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun n => Lp.aestronglyMeasurable (fourierMultiplier (A (ns n)) F)) _ aeLim).trans
    ((liminf_le_liminf (Eventually.of_forall (fun n => bn (ns n)))).trans_eq (liminf_const _))

end Burnett.A02.FrequencySplit
