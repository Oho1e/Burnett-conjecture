import Burnett.Analysis.AngularCaps.SmoothCapSymbols

set_option autoImplicit false
set_option maxHeartbeats 6500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open scoped BigOperators

abbrev NullScreenSpace := EuclideanSpace ℝ (Fin 2)
abbrev NullFrequencyCoordinates := ℝ × ℝ × NullScreenSpace

def nullAxis : NullFrequencyCoordinates := (1,0,0)

def nullCoordinateQuadratic (u : NullFrequencyCoordinates) : ℝ :=
  -(u.1*u.2.1)+‖u.2.2‖^2

/-- A chart adapted to a null covector, with the exact null-coordinate form
of the original quadratic symbol. -/
structure NullCapChart (m : Form) (w : Vec) where
  toFrequency : NullFrequencyCoordinates ≃L[ℝ] Vec
  center_eq : toFrequency nullAxis = w
  quadratic_eq : ∀ u, quadratic m (toFrequency u) = nullCoordinateQuadratic u

/-- Inverse of the manuscript's parabolic rescaling, including its extension
to `δ=0` used for checking normalized profiles. -/
def parabolicDilation (δ : ℝ) (u : NullFrequencyCoordinates) : NullFrequencyCoordinates :=
  (u.1,δ^2*u.2.1,δ • u.2.2)

def parabolicRemainder (δ : ℝ) (u : NullFrequencyCoordinates) : NullFrequencyCoordinates :=
  (0,δ*u.2.1,u.2.2)

theorem parabolicDilation_split (δ : ℝ) (u : NullFrequencyCoordinates) :
    parabolicDilation δ u = u.1 • nullAxis + δ • parabolicRemainder δ u := by
  rcases u with ⟨s,t,z⟩
  apply Prod.ext
  · simp [parabolicDilation,parabolicRemainder,nullAxis]
  · apply Prod.ext
    · simp [parabolicDilation,parabolicRemainder,nullAxis,pow_two,mul_assoc]
    · simp [parabolicDilation,parabolicRemainder,nullAxis]

@[simp] theorem parabolicDilation_nullAxis (δ : ℝ) : parabolicDilation δ nullAxis = nullAxis := by
  simp [parabolicDilation,nullAxis]

theorem chart_parabolic_quadratic {m : Form} {w : Vec} (F : NullCapChart m w)
    (δ : ℝ) (u : NullFrequencyCoordinates) :
    quadratic m (F.toFrequency (parabolicDilation δ u)) = δ^2*nullCoordinateQuadratic u := by
  rw [F.quadratic_eq]
  simp only [nullCoordinateQuadratic,parabolicDilation,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

def parabolicConeRatio (F : NullFrequencyCoordinates →L[ℝ] Vec) (a δ : ℝ)
    (u : NullFrequencyCoordinates) : ℝ :=
  nullCoordinateQuadratic u/(a*‖F (parabolicDilation δ u)‖^2)

theorem scaledConeRatio_parabolic {m : Form} {w : Vec} (F : NullCapChart m w)
    (a : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (u : NullFrequencyCoordinates) :
    scaledConeRatio m (a*δ^2) (F.toFrequency (parabolicDilation δ u)) =
      parabolicConeRatio F.toFrequency.toContinuousLinearMap a δ u := by
  unfold scaledConeRatio parabolicConeRatio
  rw [chart_parabolic_quadratic F,show a*δ^2*‖F.toFrequency (parabolicDilation δ u)‖^2 =
    δ^2*(a*‖F.toFrequency (parabolicDilation δ u)‖^2) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hδ)

def wedgeComponent (x y : Vec) (i j : Index) : ℝ := x i*y j-x j*y i

/-- A divided wedge component with no negative powers of the cap scale. -/
def parabolicWedgeComponent (F : NullFrequencyCoordinates →L[ℝ] Vec) (δ : ℝ)
    (u v : NullFrequencyCoordinates) (i j : Index) : ℝ :=
  u.1*wedgeComponent (F nullAxis) (F (parabolicRemainder δ v)) i j +
  v.1*wedgeComponent (F (parabolicRemainder δ u)) (F nullAxis) i j +
  δ*wedgeComponent (F (parabolicRemainder δ u)) (F (parabolicRemainder δ v)) i j

theorem wedgeComponent_parabolic (F : NullFrequencyCoordinates →L[ℝ] Vec) (δ : ℝ)
    (u v : NullFrequencyCoordinates) (i j : Index) :
    wedgeComponent (F (parabolicDilation δ u)) (F (parabolicDilation δ v)) i j =
      δ*parabolicWedgeComponent F δ u v i j := by
  rw [parabolicDilation_split δ u,parabolicDilation_split δ v]
  simp only [map_add,map_smul,parabolicWedgeComponent,wedgeComponent,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

/-- The rescaled squared wedge angle, with its removable powers of `δ`
cancelled. Both radial-coordinate norms remain actual Euclidean norms. -/
def parabolicWedgeRatio (F : NullFrequencyCoordinates →L[ℝ] Vec) (δ : ℝ)
    (u v : NullFrequencyCoordinates) : ℝ :=
  ((∑ i : Index, ∑ j : Index, (parabolicWedgeComponent F δ u v i j)^2)/2) /
    (‖F (parabolicDilation δ u)‖^2*‖F (parabolicDilation δ v)‖^2)

theorem projectiveWedgeSq_parabolic_div (F : NullFrequencyCoordinates →L[ℝ] Vec)
    {δ : ℝ} (hδ : δ ≠ 0) (u v : NullFrequencyCoordinates) :
    projectiveWedgeSq (F (parabolicDilation δ u)) (F (parabolicDilation δ v))/δ^2 =
      parabolicWedgeRatio F δ u v := by
  have hW : coordinateWedgeSq (F (parabolicDilation δ u)) (F (parabolicDilation δ v)) =
      δ^2*((∑ i : Index, ∑ j : Index, (parabolicWedgeComponent F δ u v i j)^2)/2) := by
    unfold coordinateWedgeSq
    change ((∑ i : Index, ∑ j : Index,
      wedgeComponent (F (parabolicDilation δ u)) (F (parabolicDilation δ v)) i j ^ 2)/2) = _
    simp only [wedgeComponent_parabolic,mul_pow,← Finset.mul_sum,mul_div_assoc]
  unfold parabolicWedgeRatio projectiveWedgeSq
  rw [hW,mul_div_assoc,mul_comm (δ^2),mul_div_cancel_right₀ _ (pow_ne_zero _ hδ)]

theorem parabolicDilation_ne_zero_of_s {δ : ℝ} {u : NullFrequencyCoordinates} (hu : u.1 ≠ 0) :
    parabolicDilation δ u ≠ 0 := by
  intro h
  exact hu (congrArg Prod.fst h)

/-- The base and enlarged angular profiles use this fixed smooth rational
argument in the coordinates of the same cap. -/
theorem capAngularProfile_parabolic (F : NullFrequencyCoordinates →L[ℝ] Vec)
    {δ : ℝ} (hδ : δ ≠ 0) (inner outer : ℝ) (u v : NullFrequencyCoordinates) :
    capAngularProfile δ inner outer (F (parabolicDilation δ v)) (F (parabolicDilation δ u)) =
      descendingProfile (inner^2) (outer^2) (parabolicWedgeRatio F δ u v) := by
  unfold capAngularProfile
  rw [projectiveWedgeSq_parabolic_div F hδ]

theorem thinConeProfile_parabolic {m : Form} {w : Vec} (F : NullCapChart m w)
    (a : ℝ) {δ : ℝ} (hδ : δ ≠ 0) (inner outer : ℝ) (u : NullFrequencyCoordinates) :
    thinConeProfile m (a*δ^2) inner outer (F.toFrequency (parabolicDilation δ u)) =
      descendingProfile (inner^2) (outer^2)
        ((parabolicConeRatio F.toFrequency.toContinuousLinearMap a δ u)^2) := by
  unfold thinConeProfile
  rw [scaledConeRatio_parabolic F a hδ]

end Burnett.Analysis.ProjectiveNullCaps
