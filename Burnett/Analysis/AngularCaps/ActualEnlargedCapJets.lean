import Burnett.Analysis.AngularCaps.ParabolicProfileJets
import Burnett.Analysis.AngularCaps.SmoothCapSupport

set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Filter Function
open scoped ContDiff Topology BigOperators

theorem parabolicRescale_dilation {δ : ℝ} (hδ : δ ≠ 0) (u : NullFrequencyCoordinates) :
    parabolicRescale δ (parabolicDilation δ u) = u := by
  rcases u with ⟨s,t,z⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [parabolicDilation,parabolicRescale]
      rw [mul_comm,mul_div_cancel_right₀ _ (pow_ne_zero _ hδ)]
    · simp [parabolicDilation,parabolicRescale,smul_smul,hδ]

theorem parabolicDilation_smul (δ a : ℝ) (u : NullFrequencyCoordinates) :
    parabolicDilation δ (a • u) = a • parabolicDilation δ u := by
  rcases u with ⟨s,t,z⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [parabolicDilation,mul_left_comm]
    · simp [parabolicDilation,smul_smul,mul_comm]

def chartScaledFrequency {m : Form} {w : Vec} (F : NullCapChart m w) (δ : ℝ)
    (u : NullFrequencyCoordinates) : Vec := F.toFrequency (parabolicDilation δ u)

theorem chartScaledFrequency_contDiff {m : Form} {w : Vec} (F : NullCapChart m w) (δ : ℝ) :
    ContDiff ℝ ∞ (chartScaledFrequency F δ) :=
  F.toFrequency.toContinuousLinearMap.contDiff.comp
    (contDiffOn_univ.mp (parabolicDilation_contDiffOn (S := univ) contDiffOn_const contDiffOn_id))

theorem chartScaledFrequency_smul {m : Form} {w : Vec} (F : NullCapChart m w) (δ a : ℝ)
    (u : NullFrequencyCoordinates) : chartScaledFrequency F δ (a • u) = a • chartScaledFrequency F δ u := by
  simp [chartScaledFrequency,parabolicDilation_smul]

theorem chartScaledFrequency_rescale {m : Form} {w : Vec} (F : NullCapChart m w) {δ : ℝ}
    (hδ : δ ≠ 0) (u : NullFrequencyCoordinates) :
    parabolicRescale δ (F.toFrequency.symm (chartScaledFrequency F δ u)) = u := by
  rw [chartScaledFrequency,F.toFrequency.symm_apply_apply,parabolicRescale_dilation hδ]

theorem chartScaledFrequency_ne_zero {m : Form} {w : Vec} (F : NullCapChart m w) {δ : ℝ}
    (hδ : δ ≠ 0) {u : NullFrequencyCoordinates} (hu : u ≠ 0) : chartScaledFrequency F δ u ≠ 0 := by
  intro h
  apply hu
  calc
    u = parabolicRescale δ (F.toFrequency.symm (chartScaledFrequency F δ u)) :=
      (chartScaledFrequency_rescale F hδ u).symm
    _ = 0 := by rw [h,map_zero]; simp [parabolicRescale]

theorem homogeneous_zero_iteratedFDeriv_norm_scale {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hSmooth : ContDiffOn ℝ ∞ f {x | x ≠ 0})
    (hDegree : ∀ (a : ℝ), a ≠ 0 → ∀ x, f (a • x) = f x)
    {a : ℝ} (ha : 0 < a) {x : E} (hx : x ≠ 0) (j : ℕ) :
    ‖iteratedFDeriv ℝ j f x‖ = a^j*‖iteratedFDeriv ℝ j f (a • x)‖ := by
  let L : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  let U : Set E := {y | y ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hLU : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hxL : L x ∈ U := smul_ne_zero ha.ne' hx
  have h := L.iteratedFDerivWithin_comp_right hSmooth hU.uniqueDiffOn hLU.uniqueDiffOn hxL
    (i := j) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen j hLU (x := x) hxL,
    iteratedFDerivWithin_of_isOpen j hU (x := L x) hxL] at h
  have hF : f ∘ L = f := funext (hDegree a ha.ne')
  rw [hF] at h
  have hMap : (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) =
      a^j • iteratedFDeriv ℝ j f (L x) := by
    ext v
    change iteratedFDeriv ℝ j f (L x) (fun i => a • v i) = a^j • iteratedFDeriv ℝ j f (L x) v
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (iteratedFDeriv ℝ j f (L x)).map_smul_univ (fun _ => a) v
  rw [hMap] at h
  change iteratedFDeriv ℝ j f x = a^j • iteratedFDeriv ℝ j f (a • x) at h
  rw [h,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ha.le j)]

theorem weighted_iteratedFDeriv_le_of_unitSphere {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hSmooth : ContDiffOn ℝ ∞ f {x | x ≠ 0})
    (hDegree : ∀ (a : ℝ), a ≠ 0 → ∀ x, f (a • x) = f x)
    {j : ℕ} {C : ℝ} (hOnSphere : ∀ v : E, ‖v‖ = 1 → ‖iteratedFDeriv ℝ j f v‖ ≤ C)
    {u : E} (hu : u ≠ 0) : ‖u‖^j*‖iteratedFDeriv ℝ j f u‖ ≤ C := by
  let v := ‖u‖⁻¹ • u
  have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hBack : ‖u‖ • v = u := by
    change ‖u‖ • (‖u‖⁻¹ • u) = u
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu),one_smul]
  have hScale := homogeneous_zero_iteratedFDeriv_norm_scale hSmooth hDegree (norm_pos_iff.mpr hu) hv0 j
  rw [hBack] at hScale
  exact hScale.symm.le.trans (hOnSphere v hv)

theorem normalized_null_coordinate_lower {u : NullFrequencyCoordinates} (hu : ‖u‖ = 1)
    {Z T M : ℝ} (hM : 0 < M) (hOne : 1 ≤ M) (hZM : Z ≤ M) (hTM : T ≤ M)
    (hZ : ‖u.2.2‖ ≤ Z*|u.1|) (hT : |u.2.1| ≤ T*|u.1|) :
    1/M ≤ |u.1| := by
  have hz := hZ.trans (mul_le_mul_of_nonneg_right hZM (abs_nonneg _))
  have ht := hT.trans (mul_le_mul_of_nonneg_right hTM (abs_nonneg _))
  have hs := mul_le_mul_of_nonneg_right hOne (abs_nonneg u.1)
  have h : ‖u‖ ≤ M*|u.1| := by
    rw [Prod.norm_def,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    exact max_le (by simpa only [one_mul] using hs) (max_le ht hz)
  apply (div_le_iff₀ hM).mpr
  rwa [hu,mul_comm] at h

/-- The actual enlarged multiplier satisfies the rescaled Mikhlin derivative
bound at every nonzero frequency, uniformly over all charts with the stated
common norm bounds and over the scale `δ`. -/
theorem actual_enlargedCapMultiplier_parabolic_jets (B outer enlarged : ℝ) {a : ℝ}
    (ha : 0 < a) (hOut : 0 ≤ outer) (hOE : outer < enlarged) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : Form) (w : Vec) (F : NullCapChart m w),
      ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
      ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
      ∀ u : NullFrequencyCoordinates, u ≠ 0 →
        ‖u‖^j*‖iteratedFDeriv ℝ j (fun v =>
          enlargedCapMultiplier m δ (a*δ^2) outer enlarged w (F.toFrequency (parabolicDilation δ v))) u‖ ≤ C := by
  let Z := 4*B*5
  let T := Z^2+4*(enlarged*a)
  let M := max 1 (max Z T)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨C,hC,hJ⟩ := parabolicEnlargedProfile_uniformJets outer enlarged B ha.ne'
    (one_div_pos.mpr hM) j
  refine ⟨C,hC,?_⟩
  intro m w F hw hF hI δ hδ hδone hSmall
  let mapFreq := chartScaledFrequency F δ
  let P(u : NullFrequencyCoordinates) := enlargedCapMultiplier m δ (a*δ^2) outer enlarged w (mapFreq u)
  have hη : 0 < a*δ^2 := mul_pos ha (pow_pos hδ _)
  have hw0 : w ≠ 0 := by intro hw0; simp [hw0] at hw
  have hMap : ContDiff ℝ ∞ mapFreq := chartScaledFrequency_contDiff F δ
  have hMapNZ (u : NullFrequencyCoordinates) (hu : u ≠ 0) : mapFreq u ≠ 0 :=
    chartScaledFrequency_ne_zero F hδ.ne' hu
  have hSmoothP : ContDiffOn ℝ ∞ P {u | u ≠ 0} :=
    (enlargedCapMultiplier_contDiffOn m δ hη outer enlarged hw0).comp hMap.contDiffOn
      (fun u hu => hMapNZ u hu)
  have hDegreeP (t : ℝ) (ht : t ≠ 0) (u : NullFrequencyCoordinates) : P (t • u) = P u := by
    change enlargedCapMultiplier m δ (a*δ^2) outer enlarged w
      (chartScaledFrequency F δ (t • u)) = P u
    rw [chartScaledFrequency_smul]
    exact enlargedCapMultiplier_degreeZero m δ (a*δ^2) outer enlarged w t ht (mapFreq u)
  have hOnSphere (u : NullFrequencyCoordinates) (hu : ‖u‖ = 1) :
      ‖iteratedFDeriv ℝ j P u‖ ≤ C := by
    have hu0 : u ≠ 0 := by intro h; simp [h] at hu
    let x := mapFreq u
    have hx := hMapNZ u hu0
    by_cases hs : x ∈ tsupport (enlargedCapMultiplier m δ (a*δ^2) outer enlarged w)
    · have hSupp := enlargedCapMultiplier_tsupport_bounds hδ hη hOut hOE hw0 hx hs
      have hCone : |quadratic m x| ≤ (enlarged*a)*δ^2*‖x‖^2 := by
        convert hSupp.2 using 1
        ring
      have hE : 0 ≤ enlarged*a := mul_nonneg (hOut.trans hOE.le) ha.le
      have hBounds := scaled_cap_coordinate_bounds F hI (show (0 : ℝ) ≤ 5 by norm_num) hδ hE
        hSmall hw hx hSupp.1 hCone
      change let v := parabolicRescale δ (F.toFrequency.symm (mapFreq u))
        ‖x‖ ≤ 2*|v.1| ∧ |v.1| ≤ B*‖x‖ ∧ ‖v.2.2‖ ≤ (4*B*5)*|v.1| ∧
          |v.2.1| ≤ ((4*B*5)^2+4*(enlarged*a))*|v.1| at hBounds
      have hBack : parabolicRescale δ (F.toFrequency.symm (mapFreq u)) = u :=
        chartScaledFrequency_rescale F hδ.ne' u
      dsimp only at hBounds
      rw [hBack] at hBounds
      have hS := normalized_null_coordinate_lower hu hM (le_max_left _ _)
        ((le_max_left Z T).trans (le_max_right _ _)) ((le_max_right Z T).trans (le_max_right _ _))
        hBounds.2.2.1 hBounds.2.2.2
      have huS : u.1 ≠ 0 := abs_pos.mp ((one_div_pos.mpr hM).trans_le hS)
      have hNear : ∀ᶠ v in 𝓝 u, v.1 ≠ 0 :=
        (isOpen_ne_fun (continuous_fst : Continuous fun v : NullFrequencyCoordinates => v.1)
          (continuous_const (y := (0:ℝ)))).mem_nhds huS
      have hLoc : P =ᶠ[𝓝 u] parabolicEnlargedProfile F.toFrequency.toContinuousLinearMap a δ outer enlarged :=
        hNear.mono fun _ hv => enlargedCapMultiplier_parabolic_eq F a outer enlarged hδ.ne' hv
      have hDeriv := (hLoc.iteratedFDeriv ℝ j).eq_of_nhds
      rw [hDeriv]
      exact hJ _ (chart_mem_boundedNullCoordinateMaps F hF hI) δ ⟨hδ.le,hδone⟩ u hu hS
    · have hZero := notMem_tsupport_iff_eventuallyEq.mp hs
      have hLoc : P =ᶠ[𝓝 u] (fun _ => 0) := hZero.comp_tendsto hMap.continuous.continuousAt
      rw [(hLoc.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_zero_fun]
      simpa only [Pi.zero_apply,norm_zero] using hC.le
  exact fun _ hu => weighted_iteratedFDeriv_le_of_unitSphere hSmoothP hDegreeP hOnSphere hu

end Burnett.Analysis.ProjectiveNullCaps
