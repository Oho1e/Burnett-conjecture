import Burnett.Geometry.Causality.IntrinsicPiecewiseStrongCausality

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section
namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CotangentHamiltonCauchySlice

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The regular convention for a future causal `C¹` segment, including
the one-sided derivatives at the endpoints. -/
def HasRegularIntrinsicFutureCausalSegment {g : Field (M := M)} (o : TimeOrientation g) (p q : M) : Prop :=
  ∃ (a b : ℝ) (γ : ℝ → M), a < b ∧ γ a = p ∧ γ b = q ∧
    ContMDiffOn 𝓘(ℝ) Model 1 γ (Icc a b) ∧
    ∀ t ∈ Icc a b, ∃ v : TangentSpace Model (γ t),
      HasMFDerivWithinAt 𝓘(ℝ) Model γ (Icc a b) t ((1 : ℝ →L[ℝ] ℝ).smulRight v) ∧
      v ≠ 0 ∧ g (γ t) v v ≤ 0 ∧ g (γ t) (o.vector (γ t)) v < 0

def regularIntrinsicPiecewiseCausalRelation {g : Field (M := M)} (o : TimeOrientation g) : Set (M × M) :=
  {z | Relation.ReflTransGen (HasRegularIntrinsicFutureCausalSegment o) z.1 z.2}

private theorem intrinsicRegularFutureCausalSegment_of_timelikeChord {g : Field (M := M)}
    (o : TimeOrientation g) {p q : M} (h : FutureTimelikeChartChord o p q) :
    HasRegularIntrinsicFutureCausalSegment o p q := by
  obtain ⟨c, hp, hq, hChord⟩ := h
  let e := chartAt E c
  let y : ℝ → E := AffineMap.lineMap (e p) (e q)
  let v := e q - e p
  let γ := e.symm ∘ y
  have hY : ContDiff ℝ 1 y := by
    change ContDiff ℝ 1 (fun t : ℝ => AffineMap.lineMap (e p) (e q) t)
    simp only [AffineMap.lineMap_apply_module']
    exact (contDiff_id.smul contDiff_const).add contDiff_const
  have hp₀ : γ 0 = p := by simpa only [γ, Function.comp_apply, y, AffineMap.lineMap_apply_zero] using e.left_inv hp
  have hq₁ : γ 1 = q := by simpa only [γ, Function.comp_apply, y, AffineMap.lineMap_apply_one] using e.left_inv hq
  refine ⟨0, 1, γ, zero_lt_one, hp₀, hq₁, ?_, ?_⟩
  · exact (contMDiffOn_chart_symm (I := Model)).comp hY.contDiffOn.contMDiffOn (fun _ ht => (hChord _ ht).1)
  intro t ht
  obtain ⟨hy, hQ, hT⟩ := hChord t ht
  let w := tangentFrame c (γ t) v
  have hFrame := ChartDifferential.tangentFrame_eq_mfderiv_symm c (e.symm (y t)) (e.symm_mapsTo hy)
  rw [e.right_inv hy] at hFrame
  have hd : HasDerivWithinAt y v (Icc 0 1) t := AffineMap.hasDerivWithinAt_lineMap
  have hInv := ((mdifferentiable_chart (I := Model) c).mdifferentiableAt_symm hy).hasMFDerivAt
  have hDeriv := hInv.comp_hasMFDerivWithinAt t hd.hasFDerivWithinAt.hasMFDerivWithinAt
  have hLinear : (mfderiv Model Model e.symm (y t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v) =
      (1 : ℝ →L[ℝ] ℝ).smulRight w := by
    rw [← hFrame]
    apply ContinuousLinearMap.ext
    intro k
    exact map_smul (tangentFrame c (e.symm (y t))) k v
  rw [hLinear] at hDeriv
  have hTimelike : g (γ t) w w < 0 := hQ
  have hw : w ≠ 0 := by
    intro hz
    simp [hz] at hTimelike
  change g (γ t) (tangentFrame c (γ t) (ChartVectorField.coordinateVector o.vector c (y t))) w < 0 at hT
  have hVector : tangentFrame c (γ t) (ChartVectorField.coordinateVector o.vector c (y t)) = o.vector (γ t) :=
    ChartVectorField.tangentFrame_coordinateVector o.vector c hy
  rw [hVector] at hT
  exact ⟨w, hDeriv, hw, hTimelike.le, hT⟩

private theorem chartChronology_subset_regularIntrinsicPiecewiseCausalRelation {g : Field (M := M)}
    (o : TimeOrientation g) : chartChronology o ⊆ regularIntrinsicPiecewiseCausalRelation o := by
  rintro ⟨p, q⟩ h
  change Relation.TransGen (FutureTimelikeChartChord o) p q at h
  change Relation.ReflTransGen (HasRegularIntrinsicFutureCausalSegment o) p q
  induction h with
  | single h => exact Relation.ReflTransGen.single (intrinsicRegularFutureCausalSegment_of_timelikeChord o h)
  | tail _ h ih => exact Relation.ReflTransGen.tail ih (intrinsicRegularFutureCausalSegment_of_timelikeChord o h)

private theorem regularIntrinsicPiecewiseCausalRelation_subset_intrinsic {g : Field (M := M)}
    (o : TimeOrientation g) : regularIntrinsicPiecewiseCausalRelation o ⊆ intrinsicPiecewiseCausalRelation o := by
  rintro ⟨p, q⟩ h
  change Relation.ReflTransGen (HasRegularIntrinsicFutureCausalSegment o) p q at h
  change Relation.ReflTransGen (HasIntrinsicFutureCausalSegment o) p q
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih =>
      obtain ⟨a, b, γ, hab, h₀, h₁, hγ, hd⟩ := h
      refine Relation.ReflTransGen.tail ih ⟨a, b, γ, hab, h₀, h₁, hγ, fun t ht => ?_⟩
      obtain ⟨v, hv, _, hQ, hT⟩ := hd t ht
      exact ⟨v, hv, hQ, hT.le⟩

/-- When the regular endpoint relation has compact diamonds, allowing zero
velocity at individual times gives the same endpoint relation. -/
theorem chartCausalRelation_eq_regularIntrinsicPiecewiseCausalRelation_of_compactDiamonds [T2Space M]
    {g : Field (M := M)} (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ regularIntrinsicPiecewiseCausalRelation o ∧
      (z, b) ∈ regularIntrinsicPiecewiseCausalRelation o}) :
    chartCausalRelation o = regularIntrinsicPiecewiseCausalRelation o := by
  have hI := chartChronology_subset_regularIntrinsicPiecewiseCausalRelation o
  have hJ := isClosed_causalRelation_of_compact_diamonds hg o hI
    (fun _ _ _ h₁ h₂ => Relation.ReflTransGen.trans h₁ h₂) hDiam
  apply Subset.antisymm
  · rintro ⟨p, q⟩ hpq
    rw [← hJ.closure_eq]
    apply mem_closure_iff_nhds.mpr
    intro V hV
    have hNear : (fun x : M => (x, q)) ⁻¹' V ∈ 𝓝 p :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hV
    obtain ⟨a, _, ha, _, hap, _⟩ := exists_past_future_chords_mem_nhds hg o p hNear
    have haq : (a, q) ∈ chartChronology o :=
      (chartCausalRelation_chronological_inclusions hg hL o hpq).1 (Relation.TransGen.single hap)
    exact ⟨(a, q), ha, hI haq⟩
  · exact (regularIntrinsicPiecewiseCausalRelation_subset_intrinsic o).trans
      (intrinsicPiecewiseCausalRelation_subset_chartCausalRelation hg hL o)

/-- The usual compact diamonds and strong causality premises from regular
piecewise `C¹` causal curves supply the precise chart hypotheses for the lift. -/
theorem chartGlobalHyperbolicity_of_regularIntrinsicPiecewise [T2Space M]
    {g : Field (M := M)} (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ regularIntrinsicPiecewiseCausalRelation o ∧
      (z, b) ∈ regularIntrinsicPiecewiseCausalRelation o})
    (hStrong : LocallyNoCausalReturn (regularIntrinsicPiecewiseCausalRelation o)) : ChartGlobalHyperbolicity o := by
  apply (chartGlobalHyperbolicity_iff_intrinsicPiecewise hg hL o).2
  have hEq := (chartCausalRelation_eq_intrinsicPiecewiseCausalRelation hg hL o).symm.trans
    (chartCausalRelation_eq_regularIntrinsicPiecewiseCausalRelation_of_compactDiamonds hg hL o hDiam)
  exact ⟨by simpa only [hEq] using hDiam, by simpa only [hEq] using hStrong⟩

end Burnett.Geometry.FiniteCausalVolume
