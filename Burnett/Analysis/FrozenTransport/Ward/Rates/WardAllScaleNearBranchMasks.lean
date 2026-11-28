import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicMasks
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePurePhysicalDecomposition
import Burnett.Analysis.AngularCaps.ComparableTriadAngle

set_option autoImplicit false
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.C02

open Set Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff

def wardParabolicLowNearBranchWeight (ϑ : ℝ → ℝ) (F : NullCoordinateMap) (δ κ ρ : ℝ)
    (u v w : NullFrequencyCoordinates) : ℝ :=
  let L := wardParabolicLowSlotWeight ϑ F δ κ ρ u v w
  let A := wardParabolicAngularNearWeight ϑ F δ u v w
  L * (1-L+L*A)

def wardParabolicComparableNearBranchWeight (ϑ : ℝ → ℝ) (F : NullCoordinateMap) (δ κ : ℝ)
    (u v w : NullFrequencyCoordinates) : ℝ :=
  let L (a b c : NullFrequencyCoordinates) := wardParabolicLowSlotWeight ϑ F δ κ 1 a b c
  let A (a b c : NullFrequencyCoordinates) := wardParabolicAngularNearWeight ϑ F δ a b c
  let C := 1-L u v w-L v w u-L w u v
  C * (C+L u v w*A u v w+L v w u*A v w u+L w u v*A w u v)

private theorem wardPurePhysicalNearWeight_mul_firstLow (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) {κ δ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ < 1/16) (x : Joint)
    (hp : x.1 ≠ 0) (hq : x.2 ≠ 0) (hr : -(x.1+x.2) ≠ 0) :
    let r := -(x.1+x.2)
    let L := lowSlotWeight ϑ κ x.1 x.2 r
    L * wardPurePhysicalNearWeight ϑ κ δ x =
      L * (1-L+L*angularNearWeight ϑ δ x.1 x.2 r) := by
  intro r L
  by_cases hL : L = 0
  · rw [hL,zero_mul,zero_mul]
  · have hSum : x.1+x.2+r = 0 := add_neg_cancel (x.1+x.2)
    obtain ⟨h₂,h₃⟩ := lowSlotWeight_nonzero_other_two_zero hCut hκ hκsmall hp hq hr hSum hL
    unfold wardPurePhysicalNearWeight comparableSlotWeight
    change L * (1-L-lowSlotWeight ϑ κ x.2 r x.1-lowSlotWeight ϑ κ r x.1 x.2 +
      L*angularNearWeight ϑ δ x.1 x.2 r+lowSlotWeight ϑ κ x.2 r x.1*angularNearWeight ϑ δ x.2 r x.1+
      lowSlotWeight ϑ κ r x.1 x.2*angularNearWeight ϑ δ r x.1 x.2) = _
    linear_combination (L*(angularNearWeight ϑ δ x.2 r x.1-1))*h₂ +
      (L*(angularNearWeight ϑ δ r x.1 x.2-1))*h₃

/-- The low branch keeps the outer radial split and the exact original
near weight, including the radial transition to comparable frequencies. -/
theorem wardParabolicLowNearBranchWeight_eq_actual (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) {κ δ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (F : NullCoordinateMap) (hδ : δ ≠ 0) (ρ : ℝ) (hρ : ρ ≠ 0)
    (u v : NullFrequencyCoordinates) :
    let A (s : NullFrequencyCoordinates) := F (parabolicDilation δ s)
    let p := ρ • A u
    let q := A v
    let r := -(A (v+ρ • u))
    p+q+r = 0 → p ≠ 0 → q ≠ 0 → r ≠ 0 →
    wardParabolicLowNearBranchWeight ϑ F δ κ ρ u v (v+ρ • u) =
      lowSlotWeight ϑ κ p q r * wardPurePhysicalNearWeight ϑ κ δ (p,q) := by
  intro A p q r hSum hp hq hr
  have hr' : -(p+q) = r := (triad_third_eq_neg_add hSum).symm
  have hL := wardParabolicLowSlotWeight_eq_actual ϑ F δ κ ρ u v (v+ρ • u)
  change _ = lowSlotWeight ϑ κ p q (A (v+ρ • u)) at hL
  have hThird : A (v+ρ • u) = -r := (neg_neg _).symm
  rw [hThird] at hL
  have hA := wardParabolicAngularNearWeight_eq_scaled_low ϑ F δ hδ ρ hρ u v (v+ρ • u)
  change _ = angularNearWeight ϑ δ p q r at hA
  have e := wardPurePhysicalNearWeight_mul_firstLow ϑ hCut hκ hκsmall (δ := δ)
    (p,q) hp hq (hr'.symm ▸ hr)
  dsimp only at e
  rw [hr'] at e
  unfold wardParabolicLowNearBranchWeight
  rw [hL,hA]
  simpa only [lowSlotWeight,norm_neg] using e.symm

/-- The comparable branch uses the same three actual angular windows and
the same complementary radial window as the original near Fourier form. -/
theorem wardParabolicComparableNearBranchWeight_eq_actual (ϑ : ℝ → ℝ)
    (F : NullCoordinateMap) (δ κ : ℝ) (hδ : δ ≠ 0) (u v w : NullFrequencyCoordinates) :
    let A (s : NullFrequencyCoordinates) := F (parabolicDilation δ s)
    let p := A u
    let q := A v
    let r := A w
    p+q+r = 0 →
    wardParabolicComparableNearBranchWeight ϑ F δ κ u v w =
      comparableSlotWeight ϑ κ p q r * wardPurePhysicalNearWeight ϑ κ δ (p,q) := by
  intro A p q r hSum
  have hL (s t z : NullFrequencyCoordinates) :
      wardParabolicLowSlotWeight ϑ F δ κ 1 s t z = lowSlotWeight ϑ κ (A s) (A t) (A z) := by
    simpa only [one_smul] using wardParabolicLowSlotWeight_eq_actual ϑ F δ κ 1 s t z
  have hr : -(p+q) = r := (triad_third_eq_neg_add hSum).symm
  change _ = comparableSlotWeight ϑ κ p q r * (comparableSlotWeight ϑ κ p q (-(p+q)) +
    lowSlotWeight ϑ κ p q (-(p+q))*angularNearWeight ϑ δ p q (-(p+q)) +
    lowSlotWeight ϑ κ q (-(p+q)) p*angularNearWeight ϑ δ q (-(p+q)) p +
    lowSlotWeight ϑ κ (-(p+q)) p q*angularNearWeight ϑ δ (-(p+q)) p q)
  rw [hr]
  simp only [wardParabolicComparableNearBranchWeight,hL,
    wardParabolicAngularNearWeight_eq_actual ϑ F δ hδ,comparableSlotWeight,p,q,r,A]

section Smooth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem wardParabolicLowNearBranchWeight_contDiffOn (V : Set X)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (F : X → NullCoordinateMap) (δ ρ : X → ℝ)
    (κ : ℝ) (hκ : κ ≠ 0) (u v w : X → NullFrequencyCoordinates)
    (hF : ContDiffOn ℝ ∞ F V) (hδ : ContDiffOn ℝ ∞ δ V) (hρ : ContDiffOn ℝ ∞ ρ V)
    (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V) (hw : ContDiffOn ℝ ∞ w V)
    (hNZ : ∀ x ∈ V, F x (parabolicDilation (δ x) (u x)) ≠ 0 ∧
      F x (parabolicDilation (δ x) (v x)) ≠ 0 ∧ F x (parabolicDilation (δ x) (w x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => wardParabolicLowNearBranchWeight ϑ (F x) (δ x) κ (ρ x) (u x) (v x) (w x)) V := by
  have hL := wardParabolicLowSlotWeight_contDiffOn V ϑ hϑ F δ (fun _ => κ) ρ u v w
    hF hδ contDiffOn_const hρ hu hv hw (fun x hx => ⟨hκ,(hNZ x hx).2.1⟩)
  have hA := wardParabolicAngularNearWeight_contDiffOn V ϑ hϑ F δ u v w hF hδ hu hv hw hNZ
  exact hL.mul ((contDiffOn_const.sub hL).add (hL.mul hA))

theorem wardParabolicComparableNearBranchWeight_contDiffOn (V : Set X)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (F : X → NullCoordinateMap) (δ : X → ℝ)
    (κ : ℝ) (hκ : κ ≠ 0) (u v w : X → NullFrequencyCoordinates)
    (hF : ContDiffOn ℝ ∞ F V) (hδ : ContDiffOn ℝ ∞ δ V)
    (hu : ContDiffOn ℝ ∞ u V) (hv : ContDiffOn ℝ ∞ v V) (hw : ContDiffOn ℝ ∞ w V)
    (hNZ : ∀ x ∈ V, F x (parabolicDilation (δ x) (u x)) ≠ 0 ∧
      F x (parabolicDilation (δ x) (v x)) ≠ 0 ∧ F x (parabolicDilation (δ x) (w x)) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => wardParabolicComparableNearBranchWeight ϑ (F x) (δ x) κ (u x) (v x) (w x)) V := by
  have lo (a b c : X → NullFrequencyCoordinates) (ha : ContDiffOn ℝ ∞ a V)
      (hb : ContDiffOn ℝ ∞ b V) (hc : ContDiffOn ℝ ∞ c V)
      (hB : ∀ x ∈ V, F x (parabolicDilation (δ x) (b x)) ≠ 0) :=
    wardParabolicLowSlotWeight_contDiffOn V ϑ hϑ F δ (fun _ => κ) (fun _ => 1) a b c
      hF hδ contDiffOn_const contDiffOn_const ha hb hc (fun x hx => ⟨hκ,hB x hx⟩)
  have hL₀ := lo u v w hu hv hw (fun x hx => (hNZ x hx).2.1)
  have hL₁ := lo v w u hv hw hu (fun x hx => (hNZ x hx).2.2)
  have hL₂ := lo w u v hw hu hv (fun x hx => (hNZ x hx).1)
  have hA₀ := wardParabolicAngularNearWeight_contDiffOn V ϑ hϑ F δ u v w hF hδ hu hv hw hNZ
  have hA₁ := wardParabolicAngularNearWeight_contDiffOn V ϑ hϑ F δ v w u hF hδ hv hw hu
    (fun x hx => ⟨(hNZ x hx).2.1,(hNZ x hx).2.2,(hNZ x hx).1⟩)
  have hA₂ := wardParabolicAngularNearWeight_contDiffOn V ϑ hϑ F δ w u v hF hδ hw hu hv
    (fun x hx => ⟨(hNZ x hx).2.2,(hNZ x hx).1,(hNZ x hx).2.1⟩)
  have hOne : ContDiffOn ℝ ∞ (fun _ : X => (1:ℝ)) V := contDiffOn_const
  have hC := ((hOne.sub hL₀).sub hL₁).sub hL₂
  exact hC.mul (((hC.add (hL₀.mul hA₀)).add (hL₁.mul hA₁)).add (hL₂.mul hA₂))

end Smooth

end Burnett.C02
