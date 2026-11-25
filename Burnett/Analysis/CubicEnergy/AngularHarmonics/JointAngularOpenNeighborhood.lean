import Burnett.Analysis.CubicEnergy.AngularHarmonics.JointSphereHarmonicMixedEstimate
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option maxHeartbeats 8200000

noncomputable section

namespace Burnett.A06

open Filter Metric MeasureTheory Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A common ambient neighborhood of the compact original parameter region
times the whole actual sphere contains a product of open neighborhoods. -/
theorem exists_jointAngular_open_product {K : Set E} (hK : IsCompact K)
    {W : Set (E × RotationSpace)} (hW : IsOpen W)
    (hKW : K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W) :
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧
      ∃ V : Set RotationSpace, IsOpen V ∧ sphere (0 : RotationSpace) 1 ⊆ V ∧ U ×ˢ V ⊆ W := by
  obtain ⟨δ,hδ,hTW⟩ := (hK.prod (isCompact_sphere (0 : RotationSpace) 1)).exists_thickening_subset_open hW hKW
  let U := thickening (δ/2) K
  let V := thickening (δ/2) (sphere (0 : RotationSpace) 1)
  have hδ₂ : 0 < δ/2 := half_pos hδ
  refine ⟨U,isOpen_thickening,fun y hy => mem_thickening_iff.mpr ⟨y,hy,by simpa only [dist_self] using hδ₂⟩,
    V,isOpen_thickening,fun y hy => mem_thickening_iff.mpr ⟨y,hy,by simpa only [dist_self] using hδ₂⟩,?_⟩
  intro z hz
  obtain ⟨p,hp,hpz⟩ := mem_thickening_iff.mp hz.1
  obtain ⟨x,hx,hxz⟩ := mem_thickening_iff.mp hz.2
  apply hTW
  refine mem_thickening_iff.mpr ⟨(p,x),⟨hp,hx⟩,?_⟩
  rw [Prod.dist_eq]
  exact max_lt (hpz.trans (half_lt_self hδ)) (hxz.trans (half_lt_self hδ))

private theorem angular_dist_to_unit_direction {x : RotationSpace} (hx : x ≠ 0) :
    dist x (‖x‖⁻¹ • x) = dist ‖x‖ (1 : ℝ) := by
  have h : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have eq : x - ‖x‖⁻¹ • x = (1 - ‖x‖⁻¹) • x := by rw [sub_smul,one_smul]
  calc
    _ = |1-‖x‖⁻¹| * ‖x‖ := by rw [dist_eq_norm,eq,norm_smul,Real.norm_eq_abs]
    _ = |(1-‖x‖⁻¹)*‖x‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg x)]
    _ = _ := by
      rw [Real.dist_eq]
      congr 1
      field_simp

/-- A cutoff supported in a radial collar extends the angular representative
and agrees with it on a full neighborhood of every original sphere point. -/
theorem exists_jointAngular_ambient_cutoff {F : E × RotationSpace → ℝ} (n : ℕ)
    {U : Set E} {V : Set RotationSpace} (hU : IsOpen U) (hV : IsOpen V)
    (hs : sphere (0 : RotationSpace) 1 ⊆ V) (hF : ContDiffOn ℝ n F (U ×ˢ V)) :
    ∃ G : E × RotationSpace → ℝ,
      ContDiffOn ℝ n G (U ×ˢ (univ : Set RotationSpace)) ∧
      ∀ (p : E) (x : RoundSphere3), G =ᶠ[𝓝 (p,(x : RotationSpace))] F := by
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_sphere (0 : RotationSpace) 1).exists_thickening_subset_open hV hs
  let a := min δ 1
  have ha : 0 < a := lt_min hδ zero_lt_one
  have haδ : a ≤ δ := min_le_left _ _
  have ha₁ : a ≤ 1 := min_le_right _ _
  let χ : ContDiffBump (1 : ℝ) := ⟨a/4,a/2,by positivity,by linarith⟩
  let G (z : E × RotationSpace) := χ ‖z.2‖ * F z
  refine ⟨G,?_,?_⟩
  · intro z hz
    by_cases ht : dist ‖z.2‖ 1 ≤ χ.rOut
    · have hz₂ : z.2 ≠ 0 := by
        intro ez
        have hd : dist ‖z.2‖ 1 = 1 := by simp [ez]
        rw [hd] at ht
        change 1 ≤ a/2 at ht
        linarith
      have hn : z.2 ∈ V := by
        apply hδV
        refine mem_thickening_iff.mpr ⟨‖z.2‖⁻¹ • z.2,?_,?_⟩
        · exact mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hz₂)
        · rw [angular_dist_to_unit_direction hz₂]
          have ht' : dist ‖z.2‖ 1 ≤ a/2 := ht
          linarith
      have hχ : ContDiffAt ℝ n (fun w : E × RotationSpace => χ ‖w.2‖) z :=
        χ.contDiff.contDiffAt.comp z ((contDiffAt_norm ℝ hz₂).comp z contDiffAt_snd)
      have hf := hF.contDiffAt ((hU.prod hV).mem_nhds ⟨hz.1,hn⟩)
      exact (hχ.mul hf).contDiffWithinAt
    · have hop : IsOpen {w : E × RotationSpace | χ.rOut < dist ‖w.2‖ 1} :=
        isOpen_lt continuous_const ((continuous_norm.comp continuous_snd).dist continuous_const)
      have hzLt : z ∈ {w : E × RotationSpace | χ.rOut < dist ‖w.2‖ 1} := lt_of_not_ge ht
      have hEq : G =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [hop.mem_nhds hzLt] with w hw
        change χ ‖w.2‖ * F w = 0
        rw [χ.zero_of_le_dist hw.le,zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq hEq).contDiffWithinAt
  · intro p x
    have hop : IsOpen {w : E × RotationSpace | dist ‖w.2‖ 1 < χ.rIn} :=
      isOpen_lt ((continuous_norm.comp continuous_snd).dist continuous_const) continuous_const
    have hx : (p,(x : RotationSpace)) ∈ {w : E × RotationSpace | dist ‖w.2‖ 1 < χ.rIn} := by
      change dist ‖(x : RotationSpace)‖ 1 < χ.rIn
      rw [mem_sphere_zero_iff_norm.mp x.property,dist_self]
      exact χ.rIn_pos
    filter_upwards [hop.mem_nhds hx] with w hw
    change χ ‖w.2‖ * F w = F w
    rw [χ.one_of_mem_closedBall hw.le,one_mul]

private theorem iteratedFDeriv_eq_of_germ {F G : E × RotationSpace → ℝ} {q : E × RotationSpace}
    (heq : G =ᶠ[𝓝 q] F) (n : ℕ) :
    iteratedFDeriv ℝ n G q = iteratedFDeriv ℝ n F q := by
  have h : G =ᶠ[𝓝[univ] q] F := by simpa only [nhdsWithin_univ] using heq
  simpa only [iteratedFDerivWithin_univ] using
    h.iteratedFDerivWithin_eq (𝕜 := ℝ) heq.eq_of_nhds n

/-- For the actual real symbol on a common open neighborhood of K × S³,
the verified estimate uses only its original mixed jets on K × S³. -/
theorem exists_jointSphereHarmonicCoefficient_on_open_neighborhood [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : E × RotationSpace → ℝ} {W : Set (E × RotationSpace)} {K : Set E},
      IsOpen W → IsCompact K → K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W →
      ∀ r : ℕ, ContDiffOn ℝ (r+12 : ℕ) F W →
      ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ r+12 → ∀ p ∈ K, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) →
      ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧
      ∀ i : SphereHarmonicIndex, ContDiffOn ℝ r (jointSphereHarmonicCoefficient F i) U ∧
      ∀ (j : ℕ), j ≤ r → ∀ p ∈ K,
        ‖iteratedFDeriv ℝ j (jointSphereHarmonicCoefficient F i) p‖ ≤
          C * (((i.1 : ℝ) + 1)^12)⁻¹ * M := by
  obtain ⟨C,hC,h⟩ := exists_jointSphereHarmonicCoefficient_uniform_mixed_bound (E := E)
  refine ⟨C,hC,?_⟩
  intro F W K hW hK hKW r hf M hM hB
  obtain ⟨U,hU,hKU,V,hV,hVS,hWV⟩ := exists_jointAngular_open_product hK hW hKW
  obtain ⟨G,hG,hEq⟩ := exists_jointAngular_ambient_cutoff (r+12) hU hV hVS (hf.mono hWV)
  have hBG k (hk : k ≤ r+12) p (hp : p ∈ K) (x : RoundSphere3) :
      ‖iteratedFDeriv ℝ k G (p,(x : RotationSpace))‖ ≤ M := by
    rw [iteratedFDeriv_eq_of_germ (hEq p x)]
    exact hB k hk p hp x
  have coeffEq (i : SphereHarmonicIndex) :
      jointSphereHarmonicCoefficient G i = jointSphereHarmonicCoefficient F i := by
    funext p
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (· * sphereHarmonicFamily i x) (hEq p x).eq_of_nhds
  refine ⟨U,hU,hKU,fun i => ?_⟩
  rw [← coeffEq i]
  exact h hU hKU r hG M hM hBG i

/-- The r=15 instance on the actual four z and four θ coordinates. -/
theorem exists_jointSphereHarmonicCoefficient_fifteen :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {F : (RotationSpace × RotationSpace) × RotationSpace → ℝ}
        {W : Set ((RotationSpace × RotationSpace) × RotationSpace)}
        {K : Set (RotationSpace × RotationSpace)},
      IsOpen W → IsCompact K → K ×ˢ sphere (0 : RotationSpace) 1 ⊆ W →
      ContDiffOn ℝ 27 F W → ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ 27 → ∀ p ∈ K, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) →
      ∃ U : Set (RotationSpace × RotationSpace), IsOpen U ∧ K ⊆ U ∧
      ∀ i : SphereHarmonicIndex, ContDiffOn ℝ 15 (jointSphereHarmonicCoefficient F i) U ∧
      ∀ (j : ℕ), j ≤ 15 → ∀ p ∈ K,
        ‖iteratedFDeriv ℝ j (jointSphereHarmonicCoefficient F i) p‖ ≤
          C * (((i.1 : ℝ) + 1)^12)⁻¹ * M := by
  obtain ⟨C,hC,h⟩ := exists_jointSphereHarmonicCoefficient_on_open_neighborhood
    (E := RotationSpace × RotationSpace)
  refine ⟨C,hC,?_⟩
  intro F W K hW hK hKW hf M hM hB
  exact h hW hK hKW 15 hf M hM hB

end Burnett.A06
