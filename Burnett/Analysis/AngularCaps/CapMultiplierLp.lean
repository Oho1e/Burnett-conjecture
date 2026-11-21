import Burnett.Analysis.AngularCaps.CapSphereJets
import Burnett.Analysis.AngularCaps.LinearLpPullback
import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeMikhlinApplications

set_option autoImplicit false
set_option maxHeartbeats 1250000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set Filter Metric
open scoped ENNReal ContDiff
open Burnett.Fourier Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit
  (radianAction mikhlin_bounded_symbol mikhlin_action_test homogeneous_multiplier_all_Lp_sphere_bound)

/-- The bounded extension of a named cap action, with its identification on
both Schwartz functions and the actual Plancherel multiplier. -/
structure CapLpRealization (p : ℝ≥0∞) [Fact (1 ≤ p)] (b : Space → ℝ) (C : ℝ) where
  symbol : BoundedSymbol Space
  symbol_eq : ∀ ξ, symbol ξ = (b ξ : ℂ)
  action : ComplexLp p →L[ℂ] ComplexLp p
  norm_le : ∀ f, ‖action f‖ ≤ C * ‖f‖
  intersection_eq : ∀ (f : Space → ℂ) (h₂ : MemLp f 2 volume) (hp : MemLp f p volume),
    (action (hp.toLp f) : Space → ℂ) =ᵐ[volume]
      (fourierMultiplier symbol (h₂.toLp f) : Space → ℂ)
  schwartz_eq : ∀ f : SchwartzMap Space ℂ,
    (action (f.toLp p volume) : Space → ℂ) =ᵐ[volume] radianAction b f

private def conjugateLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (D : Space ≃L[ℝ] Space)
    (T : ComplexLp p →L[ℂ] ComplexLp p) : ComplexLp p →L[ℂ] ComplexLp p :=
  (linearLpPullback hp D).comp (T.comp (linearLpPullback hp D.symm))

private theorem conjugateLp_schwartz {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (A : Space ≃L[ℝ] Space) (b : Space → ℝ) (T : ComplexLp p →L[ℂ] ComplexLp p)
    (hT : ∀ f : SchwartzMap Space ℂ,
      (T (f.toLp p volume) : Space → ℂ) =ᵐ[volume] radianAction (b ∘ A) f)
    (f : SchwartzMap Space ℂ) :
    (conjugateLp hp (physicalDualEquiv A) T (f.toLp p volume) : Space → ℂ) =ᵐ[volume]
      radianAction b f := by
  let D := physicalDualEquiv A
  let g := pullbackSchwartz D.symm f
  have hIn : linearLpPullback hp D.symm (f.toLp p volume) = g.toLp p volume :=
    linearLpPullback_toLp hp D.symm (f.memLp p volume)
  change (linearLpPullback hp D (T (linearLpPullback hp D.symm (f.toLp p volume))) : Space → ℂ)
    =ᵐ[volume] radianAction b f
  rw [hIn]
  refine (linearLpPullback_ae hp D _).trans
    (((quasiMeasurePreserving_linear D).ae_eq_comp (hT g)).trans ?_)
  exact Eventually.of_forall (radianAction_linear_conjugation A b f)

private theorem conjugateLp_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Space ≃L[ℝ] Space) (T : ComplexLp p →L[ℂ] ComplexLp p)
    {C : ℝ} (hT : ∀ f, ‖T f‖ ≤ C * ‖f‖) (f : ComplexLp p) :
    ‖conjugateLp hp D T f‖ ≤ C * ‖f‖ := by
  let g := linearLpPullback hp D.symm f
  have hg : ‖g‖ = (pullbackNormFactor D.symm p).toReal * ‖f‖ :=
    linearLpPullback_norm hp D.symm f
  change ‖linearLpPullback hp D (T g)‖ ≤ _
  calc
    _ = (pullbackNormFactor D p).toReal * ‖T g‖ := linearLpPullback_norm hp D (T g)
    _ ≤ (pullbackNormFactor D p).toReal * (C * ‖g‖) :=
      mul_le_mul_of_nonneg_left (hT g) ENNReal.toReal_nonneg
    _ = C * ((pullbackNormFactor D p).toReal * (pullbackNormFactor D.symm p).toReal) * ‖f‖ := by rw [hg]; ring
    _ = _ := by rw [pullbackNormFactor_symm_mul,mul_one]

private theorem conjugateLp_intersection {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Space ≃L[ℝ] Space) (T : ComplexLp p →L[ℂ] ComplexLp p)
    (U : ComplexLp 2 →L[ℂ] ComplexLp 2)
    (hT : ∀ (f : Space → ℂ) (h₂ : MemLp f 2 volume) (hp' : MemLp f p volume),
      (T (hp'.toLp f) : Space → ℂ) =ᵐ[volume] (U (h₂.toLp f) : Space → ℂ))
    (f : Space → ℂ) (h₂ : MemLp f 2 volume) (hp' : MemLp f p volume) :
    (conjugateLp hp D T (hp'.toLp f) : Space → ℂ) =ᵐ[volume]
      (conjugateLp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) D U (h₂.toLp f) : Space → ℂ) := by
  let hTwo : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  change (linearLpPullback hp D (T (linearLpPullback hp D.symm (hp'.toLp f))) : Space → ℂ)
    =ᵐ[volume] (linearLpPullback hTwo D (U (linearLpPullback hTwo D.symm (h₂.toLp f))) : Space → ℂ)
  rw [linearLpPullback_toLp hp D.symm hp',linearLpPullback_toLp hTwo D.symm h₂]
  exact (linearLpPullback_ae hp D _).trans <|
    ((quasiMeasurePreserving_linear D).ae_eq_comp
      (hT (f ∘ D.symm) (memLp_comp_linearEquiv D.symm h₂) (memLp_comp_linearEquiv D.symm hp'))).trans
      (linearLpPullback_ae hTwo D _).symm

theorem conjugate_fourierMultiplier (A : Space ≃L[ℝ] Space) (b : Space → ℝ)
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = b ξ)
    (homA : ∀ t : ℝ, 0 < t → ∀ ξ, (b ∘ A) (t • ξ) = (b ∘ A) ξ)
    (M N : BoundedSymbol Space)
    (hM : ∀ ξ, M ξ = (b ξ : ℂ)) (hN : ∀ ξ, N ξ = ((b ∘ A) ξ : ℂ)) :
    conjugateLp (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (physicalDualEquiv A) (fourierMultiplier N) =
      fourierMultiplier M := by
  let hTwo : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  let T := conjugateLp hTwo (physicalDualEquiv A) (fourierMultiplier N)
  apply ContinuousLinearMap.ext
  intro u
  change T u = fourierMultiplier M u
  apply (schwartz_toLp_denseRange (V := Space)).induction_on
    (p := fun v => T v = fourierMultiplier M v) u
  · exact isClosed_eq T.continuous (fourierMultiplier M).continuous
  · intro f
    apply Lp.ext
    exact (conjugateLp_schwartz hTwo A b (fourierMultiplier N)
      (mikhlin_action_test (b ∘ A) N hN homA) f).trans (mikhlin_action_test b M hM hom f).symm

/-- Consume the existing quantitative Mikhlin estimate on a normalized
frequency sphere, then recover the original Fourier multiplier on Lᵖ. -/
theorem quantitative_mikhlin_linear_conjugation (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Space ≃L[ℝ] Space) (b : Space → ℝ),
      ContDiffOn ℝ ∞ b puncturedFrequency →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = b ξ) →
      ∀ J : ℝ, 0 ≤ J →
      (∀ j : ℕ, j ≤ 6 → ∀ ξ ∈ sphere (0 : Space) 1, ‖iteratedFDeriv ℝ j (b ∘ A) ξ‖ ≤ J) →
      let P := ENNReal.ofReal p
      letI : Fact (1 ≤ P) :=
        ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
      Nonempty (CapLpRealization P b (C * J)) := by
  obtain ⟨C,hC,hApply⟩ := homogeneous_multiplier_all_Lp_sphere_bound p hp
  refine ⟨C,hC,?_⟩
  intro A b hb hom J hJ jets P
  letI : Fact (1 ≤ P) :=
    ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  have hbA : ContDiffOn ℝ ∞ (b ∘ A) puncturedFrequency := by
    apply hb.comp A.toContinuousLinearMap.contDiff.contDiffOn
    intro x hx e
    exact hx (A.injective (e.trans A.map_zero.symm))
  have homA (t : ℝ) (ht : 0 < t) (ξ : Space) : (b ∘ A) (t • ξ) = (b ∘ A) ξ := by
    simpa only [Function.comp_apply,A.map_smul] using hom t ht (A ξ)
  obtain ⟨N,T,hN,hT,hIntersection,hSchwartz⟩ := hApply (b ∘ A) hbA homA J hJ jets
  obtain ⟨M,hM⟩ := mikhlin_bounded_symbol b hb hom
  let hP : P ≠ ⊤ := ENNReal.ofReal_ne_top
  let D := physicalDualEquiv A
  refine ⟨⟨M,hM,conjugateLp hP D T,conjugateLp_norm_le hP D T hT,?_,
    conjugateLp_schwartz hP A b T hSchwartz⟩⟩
  intro f h2 hf
  have h := conjugateLp_intersection hP D T (fourierMultiplier N) hIntersection f h2 hf
  rw [conjugate_fourierMultiplier A b hom homA M N hM hN] at h
  exact h

/-- Each actual base and enlarged cap multiplier of the same selected family
has the original uniform Lᵖ bound, for every finite real p greater than one. -/
theorem exists_uniform_actual_capMultiplier_Lp {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (hND : ∀ m ∈ K, Nondegenerate m)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ D c₀ δ₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ C : {p : ℝ // 1 < p} → ℝ, (∀ p, 0 ≤ C p) ∧
        ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∃ S : SmoothThinConeCaps m δ (c*κ*δ^2) inner outer enlarged D,
            ∀ w ∈ S.centers, ∀ p : {p : ℝ // 1 < p},
              let P := ENNReal.ofReal p.val
              letI : Fact (1 ≤ P) :=
                ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal p.property.le⟩
              Nonempty (CapLpRealization P
                (capMultiplier S.centers m δ (c*κ*δ^2) inner outer w) (C p)) ∧
              Nonempty (CapLpRealization P
                (enlargedCapMultiplier m δ (c*κ*δ^2) outer enlarged w) (C p)) := by
  obtain ⟨D,c₀,δ₀,hD,hc₀,hδ₀,hδOne,hJets⟩ :=
    exists_uniform_capMultiplier_sphere_jets hK hFrame hND hIn hIO hOE
  choose Cp hCp hMultiplier using fun p : {p : ℝ // 1 < p} =>
    quantitative_mikhlin_linear_conjugation p.val p.property
  refine ⟨D,c₀,δ₀,hD,hc₀,hδ₀,hδOne,?_⟩
  intro κ hκ hκsmall c hc hcSmall
  obtain ⟨J,hJ,hFamily⟩ := hJets κ hκ hκsmall c hc hcSmall
  refine ⟨fun p => Cp p * J,fun p => mul_nonneg (hCp p) hJ,?_⟩
  intro m hm δ hδ hδsmall
  obtain ⟨S,hS⟩ := hFamily m hm δ hδ hδsmall
  refine ⟨S,?_⟩
  intro w hw
  obtain ⟨F,hF⟩ := hS w hw
  intro p
  let A := capFrequencyEquiv F hδ.ne'
  have hs := S.smoothness w hw
  have hh := S.degree_zero w hw
  exact ⟨hMultiplier p A _ hs.1 (fun t ht => hh.1 t ht.ne') J hJ (fun j hj ξ hξ => (hF j hj ξ hξ).1),
    hMultiplier p A _ hs.2 (fun t ht => hh.2 t ht.ne') J hJ (fun j hj ξ hξ => (hF j hj ξ hξ).2)⟩

end Burnett.Analysis.CapFourier
