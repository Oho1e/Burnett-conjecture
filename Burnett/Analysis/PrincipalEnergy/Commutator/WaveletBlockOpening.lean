import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletJetIntegral
import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletEnvelopeSchur

set_option autoImplicit false
set_option maxHeartbeats 4100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateH1)
open scoped ComplexConjugate InnerProductSpace

private theorem schwartzWaveletAction_left_open
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (D : ℝ) (hR : ∀ f g, ‖R f g‖≤D*coordinateH1 f*coordinateH1 g)
    (θ : SchwartzMap Space ℂ) (hθ : ∀ z, 1<‖z‖ → θ z=0) (s : ℝ) (hs : 0<s)
    (f g : SchwartzMap Space ℂ) :
    R (schwartzWaveletAction θ s hs f) g=∫ y, f y*R (centeredWavelet θ hθ s hs y) g := by
  obtain ⟨L,hL⟩ := exists_schwartzPair_left_coordinateH1_form R hLin D hR g
  obtain ⟨hI,hJ⟩ := schwartzWaveletAction_coordinateH1_integral θ hθ s hs f
  let V (y : Space) := f y • schwartzIntoCoordinateH1 (centeredWavelet θ hθ s hs y)
  calc
    _ = L (schwartzIntoCoordinateH1 (schwartzWaveletAction θ s hs f)) := (hL _).symm
    _ = L (∫ y, V y) := congrArg L hJ.symm
    _ = ∫ y, L (V y) := (L.integral_comp_comm hI).symm
    _ = _ := by simp only [V,map_smul,hL,smul_eq_mul]

/-- The two actual spatial convolutions inside the same test pairing open
as an iterated integral of the translated packet pairing. -/
theorem schwartzWaveletPair_double_integral
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (hSkew : ∀ f g, R g f= -conj (R f g))
    (D : ℝ) (hR : ∀ f g, ‖R f g‖≤D*coordinateH1 f*coordinateH1 g)
    (θ η : SchwartzMap Space ℂ)
    (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0)
    (s t : ℝ) (hs : 0<s) (ht : 0<t) (f g : SchwartzMap Space ℂ) :
    R (schwartzWaveletAction θ t ht f) (schwartzWaveletAction η s hs g) =
      ∫ x, conj (g x)*(∫ y,
        R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x)*f y) := by
  let T := schwartzWaveletAction θ t ht f
  let S := schwartzWaveletAction η s hs g
  let v := centeredWavelet η hη s hs
  have hLeft := schwartzWaveletAction_left_open R hLin D hR η hη s hs g T
  change R S T=∫ x, g x*R (v x) T at hLeft
  calc
    R T S = -conj (R S T) := hSkew _ _
    _ = -conj (∫ x, g x*R (v x) T) := by rw [hLeft]
    _ = ∫ x, conj (g x)*R T (v x) := by
      rw [← integral_conj,← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_mul,hSkew (v x) T]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      rw [schwartzWaveletAction_left_open R hLin D hR θ hθ t ht f (v x)]
      apply integral_congr_ae
      filter_upwards with y
      exact mul_comm _ _

/-- Ordered two-scale block bound with the genuine synthesis on both
Schwartz tests and the actual numerical Schur constant. -/
theorem schwartzWaveletPair_block_bound
    (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
    (hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
    (hSkew : ∀ f g, R g f= -conj (R f g))
    (D : ℝ) (hR : ∀ f g, ‖R f g‖≤D*coordinateH1 f*coordinateH1 g)
    (θ η : SchwartzMap Space ℂ)
    (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (s t : ℝ) (hs : 0<s) (ht : 0<t) (hst : s≤t)
    (hNear : ∀ x y : Space, ‖x-y‖≤4*t →
      ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x)‖≤A*Real.sqrt (s/t)*(t^4)⁻¹)
    (hFar : ∀ x y : Space, 4*t≤‖x-y‖ →
      ‖R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x)‖≤B*s*(‖x-y‖^5)⁻¹)
    (f g : SchwartzMap Space ℂ) :
    ‖R (schwartzWaveletAction θ t ht f) (schwartzWaveletAction η s hs g)‖≤
      (A*(∫ z, waveletNearCutoff 1 z)+B*(∫ z, inverseFifthTail 1 z)/4)*
        Real.sqrt (s/t)*‖f.toLp 2 volume‖*‖g.toLp 2 volume‖ := by
  let K (x y : Space) := R (centeredWavelet θ hθ t ht y) (centeredWavelet η hη s hs x)
  have hkM : Measurable (Function.uncurry K) :=
    (continuous_centeredWaveletPair_of_H1_bound R hLin hSkew D hR θ η hθ hη s t hs ht).measurable
  let F (x : Space) := ∫ y, K x y*f y
  obtain ⟨hF,hBound⟩ := twoScaleWaveletEnvelope_schur K hkM A B hA hB s t hs ht hst hNear hFar f
  have hEq : R (schwartzWaveletAction θ t ht f) (schwartzWaveletAction η s hs g)=
      ⟪g.toLp 2 volume,hF.toLp F⟫_ℂ := by
    rw [schwartzWaveletPair_double_integral R hLin hSkew D hR θ η hθ hη s t hs ht f g,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 volume,MemLp.coeFn_toLp hF] with x hg hu
    rw [hg,hu,RCLike.inner_apply']
  rw [hEq]
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left hBound (norm_nonneg _)).trans_eq (by ring))

end Burnett.Analysis.CarlesonEmbedding
