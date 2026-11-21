import Burnett.Analysis.PrincipalEnergy.Commutator.SchwartzWaveletAction
import Burnett.Analysis.PrincipalEnergy.Commutator.ReproductionL2
import Burnett.Analysis.PrincipalEnergy.Energy.CoordinateH1Energy

set_option autoImplicit false
set_option maxHeartbeats 3400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open Burnett.Analysis.SymmetricEnergy (coordinateDirection coordinateH1)
open scoped Topology BigOperators

private theorem reproducingScale_positive {t : ℝ} (ht : 0<t) (N j : ℕ) : 0<reproducingScale t N j := by
  unfold reproducingScale compactWaveletScale
  positivity

/-- The finite reconstruction as an actual Schwartz function, with the two
scale cutoffs from the original L² resolution. -/
def reproducingPartialSchwartz (ψ θ : SchwartzMap Space ℂ) (t : ℝ) (ht : 0<t) (N : ℕ)
    (f : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  ∑ j ∈ Finset.range (N+N), schwartzWaveletAction θ (reproducingScale t N j) (reproducingScale_positive ht N j)
    (schwartzWaveletAction ψ (reproducingScale t N j) (reproducingScale_positive ht N j) f)

theorem reproducingPartialSchwartz_toLp (ψ θ : SchwartzMap Space ℂ) (t : ℝ) (ht : 0<t) (N : ℕ)
    (f : SchwartzMap Space ℂ) :
    (reproducingPartialSchwartz ψ θ t ht N f).toLp 2 volume=
      reproducingPartialAction ψ θ t N (f.toLp 2 volume) := by
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
  change J (reproducingPartialSchwartz ψ θ t ht N f)=_
  rw [reproducingPartialSchwartz,reproducingPartialAction,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (schwartzWaveletAction θ _ _ (schwartzWaveletAction ψ _ _ f)).toLp 2 volume=_
  rw [schwartzWaveletAction_toLp,schwartzWaveletAction_toLp]

theorem reproducingPartialSchwartz_pderiv (ψ θ : SchwartzMap Space ℂ) (t : ℝ) (ht : 0<t) (N : ℕ)
    (f : SchwartzMap Space ℂ) (v : Space) :
    SchwartzMap.pderivCLM ℂ v (reproducingPartialSchwartz ψ θ t ht N f)=
      reproducingPartialSchwartz ψ θ t ht N (SchwartzMap.pderivCLM ℂ v f) := by
  rw [reproducingPartialSchwartz,reproducingPartialSchwartz,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartzWaveletAction_pderiv,schwartzWaveletAction_pderiv]

/-- The same actual two-window resolution converges in all four first
derivatives as well as in L² on the original Schwartz tests. -/
theorem reproducing_windows_coordinateH1_tendsto (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : (∫ x, φ x)=1) (hF : WaveletFactorization φ ψ θ) (t : ℝ) (ht : 0<t)
    (f : SchwartzMap Space ℂ) :
    Tendsto (fun N => coordinateH1 (reproducingPartialSchwartz ψ θ t ht N f-f)) atTop (𝓝 0) := by
  let S := reproducingPartialSchwartz ψ θ t ht
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)
  let D (i : Fin 4) : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
    SchwartzMap.pderivCLM ℂ (coordinateDirection i)
  have hVal (u : SchwartzMap Space ℂ) : Tendsto (fun N => ‖J (S N u-u)‖) atTop (𝓝 0) := by
    have h := tendsto_iff_norm_sub_tendsto_zero.mp
      (reproducing_windows_L2_tendsto φ ψ θ hφ hF t ht (u.toLp 2 volume))
    apply h.congr
    intro N
    rw [map_sub]
    change ‖reproducingPartialAction ψ θ t N (u.toLp 2 volume)-u.toLp 2 volume‖=
      ‖(S N u).toLp 2 volume-u.toLp 2 volume‖
    rw [reproducingPartialSchwartz_toLp]
  have hDer (i : Fin 4) : Tendsto (fun N => ‖J (D i (S N f-f))‖) atTop (𝓝 0) := by
    apply (hVal (D i f)).congr
    intro N
    have hComm : D i (S N f)=S N (D i f) :=
      reproducingPartialSchwartz_pderiv ψ θ t ht N f (coordinateDirection i)
    rw [map_sub (D i),hComm]
  have hSum : Tendsto (fun N => ∑ i : Fin 4, ‖J (D i (S N f-f))‖^2) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin 4)) (fun i _ => (hDer i).pow 2)
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0),Finset.sum_const_zero] using h
  have h := (((hVal f).pow 2).add hSum).sqrt
  simpa only [coordinateH1,S,J,D,SchwartzMap.toLpCLM_apply,zero_pow (by decide : (2:ℕ) ≠ 0),
    add_zero,Real.sqrt_zero] using h

end Burnett.Analysis.CarlesonEmbedding
