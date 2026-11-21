import Burnett.Analysis.PrincipalEnergy.Paraproduct.CompactWaveletConvolution
import Burnett.Analysis.PrincipalEnergy.Commutator.ReproductionL2

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier
open scoped BigOperators Topology

/-- The two-window paraproduct with actual physical convolutions at each
retained scale. The averaging window is φ, the analysis window is ψ, and θ
is the synthesis window. The formula also makes sense on constant inputs. -/
def compactWaveletParaproductTruncation (φ ψ θ : SchwartzMap Space ℂ) (t : ℝ) (N : ℕ)
    (b f : Space → ℂ) (x : Space) : ℂ :=
  ∑ j ∈ Finset.range (N+N), compactWaveletAction θ (reproducingScale t N j)
    (fun y => compactWaveletAction ψ (reproducingScale t N j) b y *
      compactWaveletAction φ (reproducingScale t N j) f y) x

private theorem reproducingScale_pos (t : ℝ) (ht : 0<t) (N j : ℕ) : 0<reproducingScale t N j :=
  div_pos (mul_pos ht (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)

private theorem two_filter_action (ψ θ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    (b : Space → ℂ) (hb₁ : Integrable b volume) (hb₂ : MemLp b 2 volume) :
    (fourierMultiplier (waveletSymbol θ s) (fourierMultiplier (waveletSymbol ψ s) (hb₂.toLp b)) :
      Space → ℂ) =ᵐ[volume] compactWaveletAction θ s (compactWaveletAction ψ s b) := by
  let v := fourierMultiplier (waveletSymbol ψ s) (hb₂.toLp b)
  let q := compactWaveletAction ψ s b
  have hv : (v : Space → ℂ) =ᵐ[volume] q := waveletMultiplier_ae_eq_action ψ s hs b hb₁ hb₂
  have hq₁ : Integrable q volume := compactWaveletAction_integrable ψ s hs hb₁
  have hq₂ : MemLp q 2 volume := MemLp.ae_eq hv (Lp.memLp v)
  have hEq : v = hq₂.toLp q := Lp.ext (hv.trans (MemLp.coeFn_toLp hq₂).symm)
  change (fourierMultiplier (waveletSymbol θ s) v : Space → ℂ) =ᵐ[volume] _
  rw [hEq]
  exact waveletMultiplier_ae_eq_action θ s hs q hq₁ hq₂

/-- On constant input one, the finite physical paraproduct is the exact
wavelet reconstruction sum on its coefficient. -/
theorem compactWaveletParaproductTruncation_one_ae (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : (∫ x, φ x)=1) (t : ℝ) (ht : 0<t) (N : ℕ)
    (b : Space → ℂ) (hb₁ : Integrable b volume) (hb₂ : MemLp b 2 volume) :
    (reproducingPartialAction ψ θ t N (hb₂.toLp b) : Space → ℂ) =ᵐ[volume]
      compactWaveletParaproductTruncation φ ψ θ t N b (fun _ => 1) := by
  let s := reproducingScale t N
  let term (j : ℕ) := fourierMultiplier (waveletSymbol θ (s j))
    (fourierMultiplier (waveletSymbol ψ (s j)) (hb₂.toLp b))
  let physical (j : ℕ) := compactWaveletAction θ (s j)
    (fun y => compactWaveletAction ψ (s j) b y * compactWaveletAction φ (s j) (fun _ => 1) y)
  have hEq (j : ℕ) : (term j : Space → ℂ) =ᵐ[volume] physical j := by
    have hs := reproducingScale_pos t ht N j
    have hInput : (fun y => compactWaveletAction ψ (s j) b y * compactWaveletAction φ (s j) (fun _ => 1) y) =
        compactWaveletAction ψ (s j) b := by
      funext y
      rw [compactWaveletAction_one φ (s j) hs y,hφ,mul_one]
    unfold physical
    rw [hInput]
    exact two_filter_action ψ θ (s j) hs b hb₁ hb₂
  have hSum (J : Finset ℕ) :
      ((∑ j ∈ J, term j : ComplexL2 Space) : Space → ℂ) =ᵐ[volume] fun x => ∑ j ∈ J, physical j x := by
    classical
    induction J using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure Space))
    | insert j J hj ih =>
        simp only [Finset.sum_insert hj]
        filter_upwards [Lp.coeFn_add (term j) (∑ j ∈ J, term j), hEq j, ih] with x hv h₁ h₂
        rw [hv,Pi.add_apply,h₁,h₂]
  exact hSum _

/-- The finite physical paraproducts of the constant input one recover the
coefficient strongly in L² along the same two-ended cutoffs. -/
theorem compactWaveletParaproductTruncation_one_tendsto (φ ψ θ : SchwartzMap Space ℂ)
    (hφ : (∫ x, φ x)=1) (hFact : WaveletFactorization φ ψ θ) (t : ℝ) (ht : 0<t)
    (b : Space → ℂ) (hb₁ : Integrable b volume) (hb₂ : MemLp b 2 volume) :
    ∃ hN : ∀ N, MemLp (compactWaveletParaproductTruncation φ ψ θ t N b (fun _ => 1)) 2 volume,
      Tendsto (fun N => (hN N).toLp (compactWaveletParaproductTruncation φ ψ θ t N b (fun _ => 1)))
        atTop (𝓝 (hb₂.toLp b)) := by
  have hEq (N : ℕ) := compactWaveletParaproductTruncation_one_ae φ ψ θ hφ t ht N b hb₁ hb₂
  let hN (N : ℕ) := MemLp.ae_eq (hEq N) (Lp.memLp _)
  refine ⟨hN,(reproducing_windows_L2_tendsto φ ψ θ hφ hFact t ht (hb₂.toLp b)).congr (fun N => ?_)⟩
  exact Lp.ext ((hEq N).trans (MemLp.coeFn_toLp (hN N)).symm)

/-- The adjoint constant test is exactly zero at every finite cut,
because each opened synthesis convolution has zero mass. -/
theorem compactWaveletParaproductTruncation_integral_eq_zero (φ ψ θ : SchwartzMap Space ℂ)
    (hθ : (∫ x, θ x)=0) (t : ℝ) (ht : 0<t) (N : ℕ)
    (b f : Space → ℂ) (hb : Integrable b volume) (hf : Integrable f volume) :
    (∫ x, compactWaveletParaproductTruncation φ ψ θ t N b f x)=0 := by
  let s := reproducingScale t N
  let G (j : ℕ) (y : Space) := compactWaveletAction ψ (s j) b y * compactWaveletAction φ (s j) f y
  let F (j : ℕ) := compactWaveletAction θ (s j) (G j)
  have hG (j : ℕ) : Integrable (G j) volume := by
    have hs := reproducingScale_pos t ht N j
    have hb' := compactWaveletAction_integrable ψ (s j) hs hb
    have hC : AEStronglyMeasurable (compactWaveletAction φ (s j) f) (volume : Measure Space) :=
      (compactWaveletAction_continuous φ (s j) hs f hf).aestronglyMeasurable
    have h := hb'.bdd_mul hC ⟨_, compactWaveletAction_norm_le_integral_norm φ (s j) hf⟩
    simpa only [G,mul_comm] using h
  have hF (j : ℕ) : Integrable (F j) volume :=
    compactWaveletAction_integrable θ (s j) (reproducingScale_pos t ht N j) (hG j)
  change (∫ x, ∑ j ∈ Finset.range (N+N), F j x) = 0
  rw [integral_finset_sum _ (fun j _ => hF j)]
  apply Finset.sum_eq_zero
  intro j _
  change (∫ x, compactWaveletAction θ (s j) (G j) x)=0
  rw [compactWaveletAction_integral θ (s j) (reproducingScale_pos t ht N j) (hG j), hθ, zero_mul]

end Burnett.Analysis.CarlesonEmbedding
