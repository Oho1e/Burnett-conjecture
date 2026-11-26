import Burnett.Analysis.CubicEnergy.AngularHarmonics.JointAngularOpenNeighborhood

set_option autoImplicit false
set_option maxHeartbeats 8200000

noncomputable section

namespace Burnett.A06

open Filter Metric MeasureTheory Set
open scoped ContDiff Topology

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The same spherical coefficient integral for an actual complex symbol. -/
def jointSphereHarmonicCoefficientComplex (F : E × RotationSpace → ℂ)
    (i : SphereHarmonicIndex) (p : E) : ℂ :=
  ∫ x : RoundSphere3, F (p,x) * (sphereHarmonicFamily i x : ℂ) ∂roundSphere3Measure

private def embedImag : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem jointSphereHarmonicCoefficientComplex_eq {F : E × RotationSpace → ℂ}
    {p : E} (hF : Continuous fun x : RoundSphere3 => F (p,x)) (i : SphereHarmonicIndex) :
    jointSphereHarmonicCoefficientComplex F i p =
      Complex.ofRealCLM (jointSphereHarmonicCoefficient (Complex.reCLM ∘ F) i p) +
        embedImag (jointSphereHarmonicCoefficient (Complex.imCLM ∘ F) i p) := by
  let g (x : RoundSphere3) := F (p,x) * (sphereHarmonicFamily i x : ℂ)
  have hg : Continuous g :=
    hF.mul (Complex.continuous_ofReal.comp (sphereHarmonicFamily i).continuous)
  have hgi : Integrable g roundSphere3Measure :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hR : (jointSphereHarmonicCoefficientComplex F i p).re =
      jointSphereHarmonicCoefficient (Complex.reCLM ∘ F) i p := by
    have h := (Complex.reCLM.integral_comp_comm hgi).symm
    simpa [jointSphereHarmonicCoefficientComplex, jointSphereHarmonicCoefficient, g,
      Function.comp_apply, Complex.mul_re] using h
  have hI : (jointSphereHarmonicCoefficientComplex F i p).im =
      jointSphereHarmonicCoefficient (Complex.imCLM ∘ F) i p := by
    have h := (Complex.imCLM.integral_comp_comm hgi).symm
    simpa [jointSphereHarmonicCoefficientComplex, jointSphereHarmonicCoefficient, g,
      Function.comp_apply, Complex.mul_im] using h
  rw [← hR, ← hI, Complex.ofRealCLM_apply, embedImag, ContinuousLinearMap.smul_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, mul_comm Complex.I]
  exact (Complex.re_add_im _).symm

private theorem norm_iteratedFDeriv_complex_projection_le (L : ℂ →L[ℝ] ℝ)
    {F : E × RotationSpace → ℂ} {n : ℕ} {z : E × RotationSpace}
    (hF : ContDiffAt ℝ n F z) :
    ‖iteratedFDeriv ℝ n (L ∘ F) z‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n F z‖ := by
  rw [L.iteratedFDeriv_comp_left hF le_rfl]
  exact L.norm_compContinuousMultilinearMap_le _

/-- The actual complex coefficient is Cʳ with the same degree decay for its
parameter derivatives, controlled by the original complex mixed jet bound. -/
theorem exists_jointSphereHarmonicCoefficientComplex_on_open_neighborhood [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : E × RotationSpace → ℂ} {W : Set (E × RotationSpace)} {K : Set E},
      IsOpen W → IsCompact K → K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W →
      ∀ r : ℕ, ContDiffOn ℝ (r+12 : ℕ) F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ r+12 → ∀ p ∈ K, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) →
      ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧
      ∀ i : SphereHarmonicIndex, ContDiffOn ℝ r (jointSphereHarmonicCoefficientComplex F i) U ∧
      ∀ (j : ℕ), j ≤ r → ∀ p ∈ K,
        ‖iteratedFDeriv ℝ j (jointSphereHarmonicCoefficientComplex F i) p‖ ≤
          C * (((i.1 : ℝ) + 1)^12)⁻¹ * M := by
  obtain ⟨C,hC,hreal⟩ := exists_jointSphereHarmonicCoefficient_on_open_neighborhood (E := E)
  let A := Complex.ofRealCLM
  let B := embedImag
  refine ⟨C*(‖A‖*‖Complex.reCLM‖ + ‖B‖*‖Complex.imCLM‖),by positivity,?_⟩
  intro F W K hW hK hKW r hf M hM hjet
  let Fr := Complex.reCLM ∘ F
  let Fi := Complex.imCLM ∘ F
  have hj (L : ℂ →L[ℝ] ℝ) k (hk : k ≤ r+12) p (hp : p ∈ K) (x : RoundSphere3) :
      ‖iteratedFDeriv ℝ k (L ∘ F) (p,(x : RotationSpace))‖ ≤ ‖L‖*M := by
    have hz : (p,(x : RotationSpace)) ∈ W := hKW ⟨hp,x.property⟩
    have hd := (hf.contDiffAt (hW.mem_nhds hz)).of_le (show (k : WithTop ℕ∞) ≤ (r+12 : ℕ) by exact_mod_cast hk)
    exact (norm_iteratedFDeriv_complex_projection_le L hd).trans
       (mul_le_mul_of_nonneg_left (hjet k hk p hp x) (norm_nonneg _))
  obtain ⟨Ur,hUr,hKr,hr⟩ := hreal (F := Fr) hW hK hKW r
    (Complex.reCLM.contDiff.comp_contDiffOn hf) (‖Complex.reCLM‖*M) (by positivity) (hj Complex.reCLM)
  obtain ⟨Ui,hUi,hKi,hi⟩ := hreal (F := Fi) hW hK hKW r
    (Complex.imCLM.contDiff.comp_contDiffOn hf) (‖Complex.imCLM‖*M) (by positivity) (hj Complex.imCLM)
  obtain ⟨U₀,hU₀,hK₀,V,hV,hVS,hP⟩ := exists_jointAngular_open_product hK hW hKW
  let U := Ur ∩ Ui ∩ U₀
  have hU : IsOpen U := (hUr.inter hUi).inter hU₀
  have hKU : K ⊆ U := fun _ hp => ⟨⟨hKr hp,hKi hp⟩,hK₀ hp⟩
  refine ⟨U,hU,hKU,fun i => ?_⟩
  let cr := jointSphereHarmonicCoefficient Fr i
  let ci := jointSphereHarmonicCoefficient Fi i
  have hcR : ContDiffOn ℝ r cr U := (hr i).1.mono (fun _ h => h.1.1)
  have hcI : ContDiffOn ℝ r ci U := (hi i).1.mono (fun _ h => h.1.2)
  have hcA : ContDiffOn ℝ r (A ∘ cr) U := A.contDiff.comp_contDiffOn hcR
  have hcB : ContDiffOn ℝ r (B ∘ ci) U := B.contDiff.comp_contDiffOn hcI
  have heq : EqOn (jointSphereHarmonicCoefficientComplex F i)
      (fun p => A (cr p) + B (ci p)) U := by
    intro p hp
    have hx : Continuous fun x : RoundSphere3 => F (p,x) :=
      hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_subtype_val)
        (fun x => hP ⟨hp.2,hVS x.property⟩)
    exact jointSphereHarmonicCoefficientComplex_eq hx i
  refine ⟨(hcA.add hcB).congr heq,?_⟩
  intro j hj p hp
  have hpU : p ∈ U := hKU hp
  have he := heq.iteratedFDerivWithin (𝕜 := ℝ) j hpU
  rw [iteratedFDerivWithin_of_isOpen j hU hpU,iteratedFDerivWithin_of_isOpen j hU hpU] at he
  have hnj : (j : WithTop ℕ∞) ≤ r := by exact_mod_cast hj
  have hA := (hcA.contDiffAt (hU.mem_nhds hpU)).of_le hnj
  have hB := (hcB.contDiffAt (hU.mem_nhds hpU)).of_le hnj
  have hAc := (hcR.contDiffAt (hU.mem_nhds hpU)).of_le hnj
  have hBc := (hcI.contDiffAt (hU.mem_nhds hpU)).of_le hnj
  rw [he]
  change ‖iteratedFDeriv ℝ j (fun q => (A ∘ cr) q + (B ∘ ci) q) p‖ ≤ _
  rw [iteratedFDeriv_add_apply' hA hB,
      A.iteratedFDeriv_comp_left hAc le_rfl, B.iteratedFDeriv_comp_left hBc le_rfl]
  calc
    _ ≤ ‖A.compContinuousMultilinearMap (iteratedFDeriv ℝ j cr p)‖ +
        ‖B.compContinuousMultilinearMap (iteratedFDeriv ℝ j ci p)‖ := norm_add_le _ _
    _ ≤ ‖A‖ * (C * (((i.1 : ℝ) + 1)^12)⁻¹ * (‖Complex.reCLM‖*M)) +
        ‖B‖ * (C * (((i.1 : ℝ) + 1)^12)⁻¹ * (‖Complex.imCLM‖*M)) :=
      add_le_add ((A.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left ((hr i).2 j hj p hp) (norm_nonneg A)))
        ((B.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left ((hi i).2 j hj p hp) (norm_nonneg B)))
    _ = _ := by ring

end Burnett.A06
