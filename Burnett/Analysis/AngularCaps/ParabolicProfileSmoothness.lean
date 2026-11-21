import Burnett.Analysis.AngularCaps.ParabolicCapAlgebra

set_option autoImplicit false
set_option maxHeartbeats 9500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Finset
open scoped ContDiff BigOperators

abbrev NullCoordinateMap := NullFrequencyCoordinates →L[ℝ] Vec

section ParameterSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

theorem parabolicDilation_contDiffOn {δ : E → ℝ} {u : E → NullFrequencyCoordinates}
    (hδ : ContDiffOn ℝ ∞ δ S) (hu : ContDiffOn ℝ ∞ u S) :
    ContDiffOn ℝ ∞ (fun x => parabolicDilation (δ x) (u x)) S :=
  hu.fst.prodMk (((hδ.pow 2).mul hu.snd.fst).prodMk (hδ.smul hu.snd.snd))

private theorem parabolicRemainder_contDiffOn {δ : E → ℝ} {u : E → NullFrequencyCoordinates}
    (hδ : ContDiffOn ℝ ∞ δ S) (hu : ContDiffOn ℝ ∞ u S) :
    ContDiffOn ℝ ∞ (fun x => parabolicRemainder (δ x) (u x)) S :=
  contDiffOn_const.prodMk ((hδ.mul hu.snd.fst).prodMk hu.snd.snd)

private theorem wedgeComponent_contDiffOn {u v : E → Vec} (hu : ContDiffOn ℝ ∞ u S)
    (hv : ContDiffOn ℝ ∞ v S) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => wedgeComponent (u x) (v x) i j) S := by
  have hProj (k : Index) : ContDiff ℝ ∞ (fun x : Vec => x k) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Index => ℝ) k).contDiff
  exact (((hProj i).comp_contDiffOn hu).mul ((hProj j).comp_contDiffOn hv)).sub
    (((hProj j).comp_contDiffOn hu).mul ((hProj i).comp_contDiffOn hv))

theorem parabolicConeRatio_contDiffOn {F : E → NullCoordinateMap} {a δ : E → ℝ}
    {u : E → NullFrequencyCoordinates} (hF : ContDiffOn ℝ ∞ F S)
    (ha : ContDiffOn ℝ ∞ a S) (hδ : ContDiffOn ℝ ∞ δ S) (hu : ContDiffOn ℝ ∞ u S)
    (hNZ : ∀ x ∈ S, a x ≠ 0 ∧ F x (parabolicDilation (δ x) (u x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => parabolicConeRatio (F x) (a x) (δ x) (u x)) S := by
  have hNum : ContDiffOn ℝ ∞ (fun x => nullCoordinateQuadratic (u x)) S :=
    ((hu.fst.mul hu.snd.fst).neg).add (hu.snd.snd.norm_sq ℝ)
  have hDen := ha.mul ((hF.clm_apply (parabolicDilation_contDiffOn hδ hu)).norm_sq ℝ)
  exact hNum.div hDen (fun x hx => mul_ne_zero (hNZ x hx).1
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (hNZ x hx).2)))

theorem parabolicWedgeRatio_contDiffOn {F : E → NullCoordinateMap} {δ : E → ℝ}
    {u v : E → NullFrequencyCoordinates} (hF : ContDiffOn ℝ ∞ F S)
    (hδ : ContDiffOn ℝ ∞ δ S) (hu : ContDiffOn ℝ ∞ u S) (hv : ContDiffOn ℝ ∞ v S)
    (hNZ : ∀ x ∈ S, F x (parabolicDilation (δ x) (u x)) ≠ 0 ∧
      F x (parabolicDilation (δ x) (v x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => parabolicWedgeRatio (F x) (δ x) (u x) (v x)) S := by
  have hAxis : ContDiffOn ℝ ∞ (fun x => F x nullAxis) S := hF.clm_apply contDiffOn_const
  have hVR := hF.clm_apply (parabolicRemainder_contDiffOn hδ hv)
  have hUR := hF.clm_apply (parabolicRemainder_contDiffOn hδ hu)
  have hComponent (i j : Index) :
      ContDiffOn ℝ ∞ (fun x => parabolicWedgeComponent (F x) (δ x) (u x) (v x) i j) S :=
    ((hu.fst.mul (wedgeComponent_contDiffOn hAxis hVR i j)).add
      (hv.fst.mul (wedgeComponent_contDiffOn hUR hAxis i j))).add
      (hδ.mul (wedgeComponent_contDiffOn hUR hVR i j))
  have hNum : ContDiffOn ℝ ∞
      (fun x => (∑ i : Index, ∑ j : Index, (parabolicWedgeComponent (F x) (δ x) (u x) (v x) i j)^2)/2) S :=
    (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hComponent i j).pow 2).div_const 2
  have hDen := ((hF.clm_apply (parabolicDilation_contDiffOn hδ hu)).norm_sq ℝ).mul
    ((hF.clm_apply (parabolicDilation_contDiffOn hδ hv)).norm_sq ℝ)
  exact hNum.div hDen (fun x hx => mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hNZ x hx).1))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (hNZ x hx).2)))

end ParameterSmoothness

/-- This denominator is uniformly positive on all genuine or zero-padded
nonnegative angular weights. -/
def regularizedAngularSum (S : ℝ) : ℝ := S+descendingProfile (1/4) (1/2) S

theorem regularizedAngularSum_lower {S : ℝ} (hS : 0 ≤ S) : 1/4 ≤ regularizedAngularSum S := by
  by_cases h : S ≤ 1/4
  · rw [regularizedAngularSum,descendingProfile_eq_one (by norm_num) h]
    linarith
  · unfold regularizedAngularSum
    have hPos := (descendingProfile_range (1/4) (1/2) S).1
    linarith only [lt_of_not_ge h,hPos]

theorem regularizedAngularSum_contDiff : ContDiff ℝ ∞ regularizedAngularSum :=
  contDiff_id.add (descendingProfile_contDiff _ _)

def parabolicAngularFactor (F : NullCoordinateMap) (δ inner outer : ℝ)
    (u v : NullFrequencyCoordinates) : ℝ :=
  descendingProfile (inner^2) (outer^2) (parabolicWedgeRatio F δ u v)

def parabolicConeFactor (F : NullCoordinateMap) (a δ inner outer : ℝ)
    (u : NullFrequencyCoordinates) : ℝ :=
  descendingProfile (inner^2) (outer^2) ((parabolicConeRatio F a δ u)^2)

def parabolicEnlargedProfile (F : NullCoordinateMap) (a δ outer enlarged : ℝ)
    (u : NullFrequencyCoordinates) : ℝ :=
  parabolicConeFactor F a δ outer enlarged u * parabolicAngularFactor F δ 4 5 u nullAxis

/-- The actual enlarged symbol in the coordinates of its own center. -/
theorem enlargedCapMultiplier_parabolic_eq {m : Form} {w : Vec} (F : NullCapChart m w)
    (a outer enlarged : ℝ) {δ : ℝ} (hδ : δ ≠ 0) {u : NullFrequencyCoordinates} (hu : u.1 ≠ 0) :
    enlargedCapMultiplier m δ (a*δ^2) outer enlarged w (F.toFrequency (parabolicDilation δ u)) =
      parabolicEnlargedProfile F.toFrequency.toContinuousLinearMap a δ outer enlarged u := by
  have hx : F.toFrequency (parabolicDilation δ u) ≠ 0 := by
    intro h
    exact parabolicDilation_ne_zero_of_s hu (F.toFrequency.injective (by simpa only [map_zero] using h))
  have hAng := capAngularProfile_parabolic F.toFrequency.toContinuousLinearMap hδ 4 5 u nullAxis
  simp only [parabolicDilation_nullAxis] at hAng
  change capAngularProfile δ 4 5 (F.toFrequency nullAxis) (F.toFrequency (parabolicDilation δ u)) = _ at hAng
  rw [F.center_eq] at hAng
  rw [enlargedCapMultiplier_at_nonzero _ _ _ _ _ _ hx,thinConeProfile_parabolic F a hδ,hAng]
  rfl

/-- The actual angular sum in any one null chart, once every retained center
is represented by its scaled coordinates in that chart. -/
theorem capAngularMass_parabolic_eq {t : Finset Vec} (F : NullCoordinateMap)
    {δ : ℝ} (hδ : δ ≠ 0) (u : NullFrequencyCoordinates) (v : Vec → NullFrequencyCoordinates)
    (hCenters : ∀ w ∈ t, F (parabolicDilation δ (v w)) = w) :
    capAngularMass t δ (F (parabolicDilation δ u)) =
      ∑ w ∈ t, parabolicAngularFactor F δ (3/4) 1 u (v w) := by
  apply Finset.sum_congr rfl
  intro w hw
  calc
    capAngularProfile δ (3/4) 1 w (F (parabolicDilation δ u)) =
        capAngularProfile δ (3/4) 1 (F (parabolicDilation δ (v w))) (F (parabolicDilation δ u)) :=
      congrArg (fun z => capAngularProfile δ (3/4) 1 z (F (parabolicDilation δ u))) (hCenters w hw).symm
    _ = _ := capAngularProfile_parabolic F hδ _ _ u (v w)

theorem capMultiplier_parabolic_eq {m : Form} {w : Vec} (F : NullCapChart m w)
    (t : Finset Vec) (a inner outer : ℝ) {δ : ℝ} (hδ : δ ≠ 0)
    {u : NullFrequencyCoordinates} (hu : u.1 ≠ 0) (v : Vec → NullFrequencyCoordinates)
    (hCenters : ∀ z ∈ t, F.toFrequency (parabolicDilation δ (v z)) = z) :
    capMultiplier t m δ (a*δ^2) inner outer w (F.toFrequency (parabolicDilation δ u)) =
      parabolicConeFactor F.toFrequency.toContinuousLinearMap a δ inner outer u *
        (parabolicAngularFactor F.toFrequency.toContinuousLinearMap δ (3/4) 1 u nullAxis /
          regularizedAngularSum (∑ z ∈ t, parabolicAngularFactor
            F.toFrequency.toContinuousLinearMap δ (3/4) 1 u (v z))) := by
  have hx : F.toFrequency (parabolicDilation δ u) ≠ 0 := by
    intro h
    exact parabolicDilation_ne_zero_of_s hu (F.toFrequency.injective (by simpa only [map_zero] using h))
  have hAng := capAngularProfile_parabolic F.toFrequency.toContinuousLinearMap hδ (3/4) 1 u nullAxis
  simp only [parabolicDilation_nullAxis] at hAng
  change capAngularProfile δ (3/4) 1 (F.toFrequency nullAxis) (F.toFrequency (parabolicDilation δ u)) = _ at hAng
  rw [F.center_eq] at hAng
  have hSum := capAngularMass_parabolic_eq F.toFrequency.toContinuousLinearMap hδ u v hCenters
  change capAngularMass t δ (F.toFrequency (parabolicDilation δ u)) = _ at hSum
  rw [capMultiplier_at_nonzero _ _ _ _ _ _ _ hx,thinConeProfile_parabolic F a hδ,hAng,capDenominator,hSum]
  rfl

end Burnett.Analysis.ProjectiveNullCaps
