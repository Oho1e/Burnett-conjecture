import Burnett.Geometry.Cotangent.CanonicalTrajectories

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.CotangentHamiltonPhaseEndpoint

open Set Filter
open scoped Topology

private theorem monotoneOn_of_hasDeriv_nonneg {I : Set ℝ} (hI : Convex ℝ I)
    {f u : ℝ → ℝ} (hd : ∀ t ∈ I, HasDerivAt f (u t) t)
    (hn : ∀ t ∈ I, 0 ≤ u t) : MonotoneOn f I :=
  monotoneOn_of_deriv_nonneg hI
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact hn t (interior_subset ht))

/-- The temporal velocity stays between strictly positive finite constants from time t₀ onward. -/
theorem temporalVelocity_bounds (I : Set ℝ) (hI : Convex ℝ I)
    (τ w u : ℝ → ℝ) {t₀ T K : ℝ} (ht₀ : t₀ ∈ I) (hK : 0 ≤ K)
    (hτ : ∀ t ∈ I, HasDerivAt τ (w t) t) (hw : ∀ t ∈ I, HasDerivAt w (u t) t)
    (hpos : ∀ t ∈ I, 0 < w t) (htime : ∀ t ∈ I, τ t ≤ T)
    (hacc : ∀ t ∈ I, |u t| ≤ K * w t ^ 2) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ t ∈ I, t₀ ≤ t → m ≤ w t ∧ w t ≤ M := by
  let L := Real.log (w t₀)
  let R := K * (T - τ t₀)
  refine ⟨Real.exp (L - R), Real.exp (L + R), Real.exp_pos _, Real.exp_pos _, ?_⟩
  have hlog (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun s => Real.log (w s)) (u t / w t) t :=
    (hw t ht).log (hpos t ht).ne'
  have hratio (t : ℝ) (ht : t ∈ I) : -(K * w t) ≤ u t / w t ∧ u t / w t ≤ K * w t := by
    have hb := abs_le.mp (hacc t ht)
    constructor
    · apply (le_div_iff₀ (hpos t ht)).mpr
      calc
        -(K * w t) * w t = -(K * w t ^ 2) := by ring
        _ ≤ u t := hb.1
    · apply (div_le_iff₀ (hpos t ht)).mpr
      calc
        u t ≤ K * w t ^ 2 := hb.2
        _ = (K * w t) * w t := by ring
  have hplus : MonotoneOn (fun t => K * τ t + Real.log (w t)) I :=
    monotoneOn_of_hasDeriv_nonneg hI (fun t ht => ((hτ t ht).const_mul K).add (hlog t ht))
      (fun t ht => by linarith [(hratio t ht).1])
  have hminus : MonotoneOn (fun t => K * τ t - Real.log (w t)) I :=
    monotoneOn_of_hasDeriv_nonneg hI (fun t ht => ((hτ t ht).const_mul K).sub (hlog t ht))
      (fun t ht => by linarith [(hratio t ht).2])
  intro t ht htt
  have hp := hplus ht₀ ht htt
  have hm := hminus ht₀ ht htt
  have hb : K * τ t ≤ K * T := mul_le_mul_of_nonneg_left (htime t ht) hK
  dsimp only at hp hm
  exact ⟨(Real.le_log_iff_exp_le (hpos t ht)).mp (by dsimp [L, R]; linarith),
    (Real.log_le_iff_le_exp (hpos t ht)).mp (by dsimp [L, R]; linarith)⟩

/-- Finite temporal range and the lower temporal velocity bound force finite affine length. -/
theorem affineTime_sub_le_of_temporalVelocity_lower (I : Set ℝ) (hI : Convex ℝ I)
    (τ w : ℝ → ℝ) {t₀ T m : ℝ} (ht₀ : t₀ ∈ I) (hm : 0 < m)
    (hτ : ∀ t ∈ I, HasDerivAt τ (w t) t)
    (htime : ∀ t ∈ I, τ t ≤ T)
    (hmin : ∀ t ∈ I, t₀ ≤ t → m ≤ w t) :
    ∀ t ∈ I, t₀ ≤ t → t - t₀ ≤ (T - τ t₀) / m := by
  let J := I ∩ Ici t₀
  have hJ : Convex ℝ J := hI.inter (convex_Ici t₀)
  have hf : ContinuousOn τ J := fun t ht => (hτ t ht.1).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ τ (interior J) :=
    fun t ht => (hτ t (interior_subset ht).1).differentiableAt.differentiableWithinAt
  have hl : ∀ t ∈ interior J, m ≤ deriv τ t := by
    intro t ht
    have hj := interior_subset ht
    rw [(hτ t hj.1).deriv]
    exact hmin t hj.1 hj.2
  intro t ht hle
  have ht₀J : t₀ ∈ J := ⟨ht₀, mem_Ici.mpr le_rfl⟩
  have h := hJ.mul_sub_le_image_sub_of_le_deriv hf hd hl t₀ ht₀J t ⟨ht, hle⟩ hle
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm]
  exact h.trans (sub_le_sub_right (htime t ht) _)

end Burnett.Geometry.CotangentHamiltonPhaseEndpoint

namespace Burnett.Geometry.CotangentHamiltonPhaseEndpoint

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bounded derivative on a convex left tail gives a genuine left limit in the complete space. -/
theorem tendsto_left_of_bounded_hasDeriv (J : Set ℝ) (hJ : Convex ℝ J)
    (f f' : ℝ → E) {b K : ℝ} (hK : 0 ≤ K) (hnear : J ∈ 𝓝[<] b)
    (hd : ∀ t ∈ J, HasDerivAt f (f' t) t) (hbound : ∀ t ∈ J, ‖f' t‖ ≤ K) :
    ∃ q : E, Tendsto f (𝓝[<] b) (𝓝 q) := by
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro ε hε
  let δ := ε / (2 * (K + 1))
  have hC : 0 < K + 1 := by linarith
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hεeq : (K + 1) * (2 * δ) = ε := by
    dsimp [δ]
    field_simp
  let U := Metric.ball b δ ∩ J
  have hU : U ∈ 𝓝[<] b :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds b hδ)) hnear
  refine ⟨f '' U, image_mem_map hU, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxb : dist x b < δ := hx.1
  have hyb : dist y b < δ := hy.1
  have hxy : dist x y < 2 * δ := by
    have h := dist_triangle x b y
    rw [dist_comm b y] at h
    linarith
  have hd' (t : ℝ) (ht : t ∈ J) : ‖deriv f t‖ ≤ K := by
    rw [(hd t ht).deriv]
    exact hbound t ht
  calc
    dist (f x) (f y) ≤ K * dist x y := by
      simpa only [dist_eq_norm] using
        Convex.norm_image_sub_le_of_norm_deriv_le (fun t ht => (hd t ht).differentiableAt)
          hd' hJ hy.2 hx.2
    _ ≤ (K + 1) * dist x y := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := (mul_lt_mul_of_pos_left hxy hC).trans_eq hεeq

private theorem rightTail_of_bddAbove_open_interval {I : Set ℝ} (hI : IsOpen I)
    (hconn : I.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hb : BddAbove I) :
    t₀ < sSup I ∧ I ∩ Ici t₀ ∈ 𝓝[<] sSup I := by
  obtain ⟨l, r, hlt, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds ht₀)
  let u := (t₀ + r) / 2
  have htr : t₀ < r := hlt.2
  have htu : t₀ < u := by dsimp [u]; linarith
  have huI : u ∈ I := hsub ⟨hlt.1.trans htu, by dsimp [u]; linarith⟩
  have htSup := lt_csSup_of_lt hb huI htu
  refine ⟨htSup, mem_of_superset (Ioo_mem_nhdsLT htSup) ?_⟩
  intro t ht
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨t₀, ht₀⟩ ht.2
  exact ⟨hconn.out ht₀ hs ⟨ht.1.le, hts.le⟩, ht.1.le⟩

/-- The actual affine time has finite supremum and the chart position and velocity have finite
left limits. The temporal component of the limiting velocity is still strictly positive. -/
theorem finite_affine_phase_endpoint (I : Set ℝ) (hI : IsOpen I) (hconn : I.OrdConnected)
    (x v a : ℝ → E) (τcoord : E →L[ℝ] ℝ) {t₀ T C A : ℝ}
    (ht₀ : t₀ ∈ I) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hx : ∀ t ∈ I, HasDerivAt x (v t) t) (hv : ∀ t ∈ I, HasDerivAt v (a t) t)
    (hpos : ∀ t ∈ I, 0 < τcoord (v t)) (htime : ∀ t ∈ I, τcoord (x t) ≤ T)
    (hcone : ∀ t ∈ I, ‖v t‖ ≤ C * τcoord (v t))
    (hacc : ∀ t ∈ I, ‖a t‖ ≤ A * ‖v t‖ ^ 2) :
    BddAbove I ∧ t₀ < sSup I ∧ ∃ xEnd vEnd : E,
      Tendsto x (𝓝[<] sSup I) (𝓝 xEnd) ∧ Tendsto v (𝓝[<] sSup I) (𝓝 vEnd) ∧
      0 < τcoord vEnd ∧ vEnd ≠ 0 := by
  let τ (t : ℝ) := τcoord (x t)
  let w (t : ℝ) := τcoord (v t)
  let u (t : ℝ) := τcoord (a t)
  let K := ‖τcoord‖ * A * C ^ 2
  have hconv := convex_iff_ordConnected.mpr hconn
  have hτ (t : ℝ) (ht : t ∈ I) : HasDerivAt τ (w t) t :=
    τcoord.hasFDerivAt.comp_hasDerivAt t (hx t ht)
  have hw (t : ℝ) (ht : t ∈ I) : HasDerivAt w (u t) t :=
    τcoord.hasFDerivAt.comp_hasDerivAt t (hv t ht)
  have htemporal (t : ℝ) (ht : t ∈ I) : |u t| ≤ K * w t ^ 2 := by
    have hsq : ‖v t‖ ^ 2 ≤ (C * w t) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcone t ht) 2
    calc
      |u t| = ‖τcoord (a t)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖τcoord‖ * ‖a t‖ := τcoord.le_opNorm _
      _ ≤ ‖τcoord‖ * (A * (C * w t) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ((hacc t ht).trans ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hsq hA
      _ = K * w t ^ 2 := by dsimp [K]; ring
  obtain ⟨m, M, hm, hM, hb⟩ :=
    temporalVelocity_bounds I hconv τ w u ht₀ (by dsimp [K]; positivity)
      hτ hw hpos htime htemporal
  have hlength := affineTime_sub_le_of_temporalVelocity_lower I hconv τ w ht₀ hm hτ htime
    (fun t ht ht' => (hb t ht ht').1)
  have hrange : 0 ≤ (T - τ t₀) / m := div_nonneg (sub_nonneg.mpr (htime t₀ ht₀)) hm.le
  have hIbound : BddAbove I := by
    refine ⟨t₀ + (T - τ t₀) / m, fun t ht => ?_⟩
    rcases le_total t₀ t with h | h
    · linarith [hlength t ht h]
    · linarith
  obtain ⟨htSup, hJnear⟩ := rightTail_of_bddAbove_open_interval hI hconn ht₀ hIbound
  let J := I ∩ Ici t₀
  have hJconv : Convex ℝ J := hconv.inter (convex_Ici t₀)
  have hV (t : ℝ) (ht : t ∈ J) : ‖v t‖ ≤ C * M :=
    (hcone t ht.1).trans (mul_le_mul_of_nonneg_left (hb t ht.1 ht.2).2 hC)
  have hAcc (t : ℝ) (ht : t ∈ J) : ‖a t‖ ≤ A * (C * M) ^ 2 :=
    (hacc t ht.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hV t ht) 2) hA)
  obtain ⟨xEnd, hxEnd⟩ := tendsto_left_of_bounded_hasDeriv J hJconv x v
    (mul_nonneg hC hM.le) hJnear (fun t ht => hx t ht.1) hV
  obtain ⟨vEnd, hvEnd⟩ := tendsto_left_of_bounded_hasDeriv J hJconv v a
    (by positivity) hJnear (fun t ht => hv t ht.1) hAcc
  have hwLimit : Tendsto w (𝓝[<] sSup I) (𝓝 (τcoord vEnd)) :=
    τcoord.continuous.continuousAt.tendsto.comp hvEnd
  have hlow : m ≤ τcoord vEnd := by
    apply ge_of_tendsto hwLimit
    filter_upwards [hJnear] with t ht
    exact (hb t ht.1 ht.2).1
  have hposEnd := hm.trans_le hlow
  exact ⟨hIbound, htSup, xEnd, vEnd, hxEnd, hvEnd, hposEnd, fun hv0 => by
    rw [hv0, map_zero] at hposEnd
    exact lt_irrefl _ hposEnd⟩

end Burnett.Geometry.CotangentHamiltonPhaseEndpoint

namespace Burnett.Geometry.CotangentHamiltonPhaseEndpoint

open Set Filter Finset
open scoped Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

/-- The coordinate geodesic equation and bounded connection coefficients give a quadratic
bound in the actual Euclidean speed. -/
theorem geodesicAcceleration_norm_le (Γ : Connection) {G : ℝ} (hG : 0 ≤ G)
    (hΓ : ∀ i j k, ‖Γ i j k‖ ≤ G) (v a : CoordinateSpace)
    (heq : ∀ i, a i + (∑ j, ∑ k, Γ i j k * (v j * v k)) = 0) :
    ‖a‖ ≤ (32 * G) * ‖v‖ ^ 2 := by
  let D : ℝ := G * ‖v‖ ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hterm (i j k : Index) : ‖Γ i j k * (v j * v k)‖ ≤ D := by
    rw [norm_mul, norm_mul]
    have hv : ‖v j‖ * ‖v k‖ ≤ ‖v‖ ^ 2 := by
      rw [pow_two]
      exact mul_le_mul (PiLp.norm_apply_le v j) (PiLp.norm_apply_le v k)
        (norm_nonneg _) (norm_nonneg _)
    exact mul_le_mul (hΓ i j k) hv (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hG
  have hentry (i : Index) : ‖a i‖ ≤ 16 * D := by
    have hi : a i = -(∑ j, ∑ k, Γ i j k * (v j * v k)) := by linarith [heq i]
    rw [hi, norm_neg]
    calc
      ‖∑ j, ∑ k, Γ i j k * (v j * v k)‖ ≤ ∑ j, ‖∑ k, Γ i j k * (v j * v k)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Index, ∑ _k : Index, D := by
        apply Finset.sum_le_sum
        intro j _
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm i j k)
      _ = 16 * D := by simp [Index]; ring
  have hplane : ‖a‖ ≤ 32 * D := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity : 0 ≤ 32 * D)]
    calc
      (∑ i, ‖a i‖ ^ 2) ≤ ∑ _i : Index, (16 * D) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i) 2
      _ = (32 * D) ^ 2 := by simp [Index]; ring
  convert hplane using 1
  dsimp [D]
  ring

/-- The finite chart endpoint estimate with the actual four coordinate components and
the geodesic equation. -/
theorem finite_geodesic_chart_endpoint (I : Set ℝ) (hI : IsOpen I) (hconn : I.OrdConnected)
    (x v a : ℝ → CoordinateSpace) (Γ : CoordinateSpace → Connection)
    (τcoord : CoordinateSpace →L[ℝ] ℝ)
    {t₀ T C G : ℝ} (ht₀ : t₀ ∈ I) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hx : ∀ t ∈ I, HasDerivAt x (v t) t) (hv : ∀ t ∈ I, HasDerivAt v (a t) t)
    (hgeo : ∀ t ∈ I, ∀ i, a t i + (∑ j, ∑ k, Γ (x t) i j k * (v t j * v t k)) = 0)
    (hΓ : ∀ t ∈ I, ∀ i j k, ‖Γ (x t) i j k‖ ≤ G)
    (hpos : ∀ t ∈ I, 0 < τcoord (v t)) (htime : ∀ t ∈ I, τcoord (x t) ≤ T)
    (hcone : ∀ t ∈ I, ‖v t‖ ≤ C * τcoord (v t)) :
    BddAbove I ∧ t₀ < sSup I ∧ ∃ xEnd vEnd : CoordinateSpace,
      Tendsto x (𝓝[<] sSup I) (𝓝 xEnd) ∧ Tendsto v (𝓝[<] sSup I) (𝓝 vEnd) ∧
      0 < τcoord vEnd ∧ vEnd ≠ 0 :=
  finite_affine_phase_endpoint I hI hconn x v a τcoord ht₀ hC
    (mul_nonneg (by norm_num) hG) hx hv hpos htime hcone
    (fun t ht => geodesicAcceleration_norm_le (Γ (x t)) hG (hΓ t ht) (v t) (a t) (hgeo t ht))

end Burnett.Geometry.CotangentHamiltonPhaseEndpoint

namespace Burnett.Geometry.CotangentHamiltonPhaseEndpoint

open Set Filter
open scoped Topology BigOperators Manifold ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldVolumeRegularity
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonGeodesic
open Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The position and velocity of the same canonical trajectory converge at a finite
time when its actual chart satisfies the temporal and connection bounds. -/
theorem canonicalTrajectory_finite_chart_velocity (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) {p : CotangentBundle M}
    (A : CanonicalTrajectory g p) (c : M) (I : Set ℝ)
    (hI : IsOpen I) (hconn : I.OrdConnected) (hsub : I ⊆ A.domain)
    (hchart : MapsTo A.curve I (cotangentSource c)) (τcoord : CoordinateSpace →L[ℝ] ℝ)
    {t₀ T C G : ℝ} (ht₀ : t₀ ∈ I) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hΓ : ∀ t ∈ I, ∀ i j k,
      ‖computedConnection (coordinateBilinear g c) (cotangentChart c (A.curve t)).1 i j k‖ ≤ G)
    (hpos : ∀ t ∈ I, 0 < τcoord (deriv (fun s => (cotangentChart c (A.curve s)).1) t))
    (htime : ∀ t ∈ I, τcoord (cotangentChart c (A.curve t)).1 ≤ T)
    (hcone : ∀ t ∈ I, ‖deriv (fun s => (cotangentChart c (A.curve s)).1) t‖ ≤
      C * τcoord (deriv (fun s => (cotangentChart c (A.curve s)).1) t)) :
    let x : ℝ → CoordinateSpace := fun s => (cotangentChart c (A.curve s)).1
    BddAbove I ∧ t₀ < sSup I ∧ ∃ xEnd vEnd : CoordinateSpace,
      Tendsto x (𝓝[<] sSup I) (𝓝 xEnd) ∧
      Tendsto (deriv x) (𝓝[<] sSup I) (𝓝 vEnd) ∧ 0 < τcoord vEnd ∧ vEnd ≠ 0 := by
  intro x
  let v := deriv x
  let a := deriv v
  let Γ := computedConnection (coordinateBilinear g c)
  have hcan := canonicalCurve_in_chart g hg hn hs c A.curve I hI (A.integral.mono hsub) hchart
  have hreplay (t : ℝ) (ht : t ∈ I) :
      HasDerivAt x (v t) t ∧ HasDerivAt v (a t) t ∧
      ∀ i, a t i + (∑ j, ∑ k, Γ (x t) i j k * (v t j * v t k)) = 0 := by
    obtain ⟨v₀, a₀, hx₀, ha₀, hGeo⟩ :=
      hamiltonCurve_projected_geodesic g hg hn hs c A.curve I hI hcan t ht
    have hev : v t = v₀ := hx₀.deriv
    have hea : a t = a₀ := ha₀.deriv
    rw [hev, hea]
    exact ⟨hx₀, ha₀, hGeo⟩
  exact finite_geodesic_chart_endpoint I hI hconn x v a Γ τcoord ht₀ hC hG
    (fun t ht => (hreplay t ht).1) (fun t ht => (hreplay t ht).2.1)
    (fun t ht => (hreplay t ht).2.2) hΓ hpos htime hcone

private theorem chart_velocity_cotangent_lower (g : Field (M := M))
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (c : M) (γ : ℝ → CotangentBundle M) (I : Set ℝ) (h : IsHamiltonCurveInChart g c γ I)
    (t : ℝ) (ht : t ∈ I) :
    let x : ℝ → CoordinateSpace := fun s => (cotangentChart c (γ s)).1
    (cotangentChart c (γ t)).2 =
      lower (metricComponents (coordinateBilinear g c) (x t)) (fun j => deriv x t j) := by
  intro x
  let z := cotangentChart c (γ t)
  have hd : HasDerivAt x (hamiltonVector (chartInverse g c) z).1 t :=
    (ContinuousLinearMap.fst ℝ CoordinateSpace Covector).hasFDerivAt.comp_hasDerivAt t (h.2 t ht)
  rw [hd.deriv, hamiltonVector_fst_eq_raise _ _ (chartInverse_symm g hs c z.1)]
  have hz := (cotangentChart_mapsTo c (h.1 t ht)).1
  exact (lower_raise _ (coordinate_det_ne_zero g hn c hz) z.2).symm

private theorem tendsto_chart_lower {l : Filter ℝ} (x v : ℝ → CoordinateSpace)
    (G : CoordinateSpace → Tensor2) {xEnd vEnd : CoordinateSpace}
    (hx : Tendsto x l (𝓝 xEnd)) (hv : Tendsto v l (𝓝 vEnd))
    (hG : ∀ j k, ContinuousAt (fun y => G y j k) xEnd) :
    Tendsto (fun t => lower (G (x t)) (fun j => v t j)) l
      (𝓝 (lower (G xEnd) (fun j => vEnd j))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simp only [lower, raiseCovector]
  apply tendsto_finset_sum
  intro j _
  have hj : Tendsto (fun t => v t j) l (𝓝 (vEnd j)) :=
    (EuclideanSpace.proj j).continuous.continuousAt.tendsto.comp hv
  exact ((hG i j).tendsto.comp hx).mul hj

/-- If the base limit is in this chart, the actual canonical trajectory has a genuine
nonzero null cotangent limit with its original affine time. -/
theorem canonicalTrajectory_null_phase_limit_in_chart (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (hnp : dualEnergy g hn p = 0)
    (c : M) (I : Set ℝ) (hI : IsOpen I) (hconn : I.OrdConnected)
    (hsub : I ⊆ A.domain) (hchart : MapsTo A.curve I (cotangentSource c))
    (τcoord : CoordinateSpace →L[ℝ] ℝ) {t₀ T C G : ℝ} (ht₀ : t₀ ∈ I) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hΓ : ∀ t ∈ I, ∀ i j k,
      ‖computedConnection (coordinateBilinear g c) (cotangentChart c (A.curve t)).1 i j k‖ ≤ G)
    (hpos : ∀ t ∈ I, 0 < τcoord (deriv (fun s => (cotangentChart c (A.curve s)).1) t))
    (htime : ∀ t ∈ I, τcoord (cotangentChart c (A.curve t)).1 ≤ T)
    (hcone : ∀ t ∈ I, ‖deriv (fun s => (cotangentChart c (A.curve s)).1) t‖ ≤
      C * τcoord (deriv (fun s => (cotangentChart c (A.curve s)).1) t))
    {xEnd : CoordinateSpace} (hxTarget : xEnd ∈ (chartAt CoordinateSpace c).target)
    (hxLimit : Tendsto (fun t => (cotangentChart c (A.curve t)).1) (𝓝[<] sSup I) (𝓝 xEnd)) :
    BddAbove I ∧ t₀ < sSup I ∧ ∃ q : CotangentBundle M,
      Tendsto A.curve (𝓝[<] sSup I) (𝓝 q) ∧ q ∈ cotangentSource c ∧
      (cotangentChart c q).1 = xEnd ∧ q ∈ puncturedCotangent ∧ dualEnergy g hn q = 0 := by
  let x : ℝ → CoordinateSpace := fun t => (cotangentChart c (A.curve t)).1
  let ξ : ℝ → Covector := fun t => (cotangentChart c (A.curve t)).2
  let v := deriv x
  let B := metricComponents (coordinateBilinear g c)
  obtain ⟨hIbound, htSup, xLim, vEnd, hxLim, hvEnd, _, hvNonzero⟩ :=
    canonicalTrajectory_finite_chart_velocity g hg hn hs A c I hI hconn hsub
      hchart τcoord ht₀ hC hG hΓ hpos htime hcone
  have hxc : xLim = xEnd := tendsto_nhds_unique hxLim hxLimit
  subst xLim
  let ξEnd := lower (B xEnd) (fun j => vEnd j)
  have hξ0 : ξEnd ≠ 0 := by
    intro hzero
    have h := raise_lower (B xEnd) (coordinate_det_ne_zero g hn c hxTarget) (fun j => vEnd j)
    change raiseCovector (matrixInverse (B xEnd)) ξEnd = (fun j => vEnd j) at h
    rw [hzero] at h
    apply hvNonzero
    ext i
    have hi := congrFun h i
    simpa [raiseCovector] using hi.symm
  obtain ⟨_, hnear⟩ := rightTail_of_bddAbove_open_interval hI hconn ht₀ hIbound
  have hcan := canonicalCurve_in_chart g hg hn hs c A.curve I hI (A.integral.mono hsub) hchart
  have hlower : ξ =ᶠ[𝓝[<] sSup I] (fun t => lower (B (x t)) (fun j => v t j)) := by
    filter_upwards [hnear] with t ht
    exact chart_velocity_cotangent_lower g hn hs c A.curve I hcan t ht.1
  have hξLim : Tendsto ξ (𝓝[<] sSup I) (𝓝 ξEnd) := by
    apply (tendsto_chart_lower x v B hxLimit hvEnd ?_).congr' hlower.symm
    intro i j
    exact (contDiffOn_metricComponents g hg c i j).continuousOn.continuousAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hxTarget)
  let zEnd : Phase := (xEnd, ξEnd)
  let q := cotangentChartInverse c zEnd
  have hzTarget : zEnd ∈ phaseTarget c := ⟨hxTarget, trivial⟩
  have hqSource : q ∈ cotangentSource c := cotangentChartInverse_mapsTo c hzTarget
  have hqChart : cotangentChart c q = zEnd := cotangentChart_right_inv c hzTarget
  have hzLim : Tendsto (fun t => cotangentChart c (A.curve t)) (𝓝[<] sSup I) (𝓝 zEnd) :=
    hxLimit.prodMk_nhds hξLim
  have hqLim : Tendsto A.curve (𝓝[<] sSup I) (𝓝 q) := by
    have hd := (contMDiffOn_cotangentChartInverse c).continuousOn.continuousAt
      ((isOpen_phaseTarget c).mem_nhds hzTarget)
    apply (hd.tendsto.comp hzLim).congr'
    filter_upwards [hnear] with t ht
    exact cotangentChart_left_inv c (hchart ht.1)
  have hPpos : Tendsto (fun t => coordinateP (chartInverse g c) (cotangentChart c (A.curve t)))
      (𝓝[<] sSup I) (𝓝 (coordinateP (chartInverse g c) zEnd)) :=
    (((contDiffOn_coordinateP_chartInverse g hg hn c).continuousOn.continuousAt
      ((isOpen_phaseTarget c).mem_nhds hzTarget)).tendsto.comp hzLim)
  have hPzero : (fun t => coordinateP (chartInverse g c) (cotangentChart c (A.curve t))) =ᶠ[
      𝓝[<] sSup I] (fun _ => 0) := by
    filter_upwards [hnear] with t ht
    rw [coordinateP_cotangentChart g hn hs c (hchart ht.1),
      (A.dualEnergy_constant g hg hn hs (hsub ht.1)).trans hnp, zero_div]
  have hP : coordinateP (chartInverse g c) zEnd = 0 :=
    tendsto_nhds_unique hPpos (tendsto_const_nhds.congr' hPzero.symm)
  rw [← hqChart, coordinateP_cotangentChart g hn hs c hqSource] at hP
  exact ⟨hIbound, htSup, q, hqLim, hqSource, congrArg Prod.fst hqChart,
    cotangentChartInverse_mem_punctured ⟨hzTarget, hξ0⟩, by linarith⟩

end Burnett.Geometry.CotangentHamiltonPhaseEndpoint

namespace Burnett.Geometry.CotangentHamiltonTemporalCone

open Bundle Module Set Filter
open scoped BigOperators ContDiff Manifold Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldBilinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The normal form on the actual tangent fiber transfers to the given atlas chart. -/
theorem exists_lorentzBasis_coordinateBilinear (g : Field (M := M))
    (hL : HasLorentzSignature g) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    ∃ b : Basis Index ℝ CoordinateSpace,
      ∀ a d, coordinateBilinear g c y (b a) (b d) = TensorFrame.standardInverse a d := by
  let p := (chartAt CoordinateSpace c).symm y
  have hp : p ∈ (chartAt CoordinateSpace c).source :=
    (chartAt CoordinateSpace c).symm_mapsTo hy
  let e := (trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ p hp
  obtain ⟨b, hb⟩ := hL p
  refine ⟨b.map e.toLinearEquiv, ?_⟩
  intro a d
  change g p (e.symm ((b.map e.toLinearEquiv) a)) (e.symm ((b.map e.toLinearEquiv) d)) = _
  rw [Basis.map_apply, Basis.map_apply]
  change g p (e.symm (e (b a))) (e.symm (e (b d))) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact hb a d

private theorem fiber_self_eq_signature_sum (B : LinearMap.BilinForm ℝ CoordinateSpace)
    (b : Basis Index ℝ CoordinateSpace)
    (hb : ∀ i j, B (b i) (b j) = TensorFrame.standardInverse i j) (v : CoordinateSpace) :
    B v v = ∑ i, TensorFrame.signature i * (b.repr v i) ^ 2 := by
  have h := congrArg (B v) (b.sum_repr v)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hc : b.repr v i = TensorFrame.signature i * B v (b i) :=
    BasisFrame.coordinate_eq_signature_pairing B b hb v i
  have hs := BasisFrame.signature_sq i
  have ht : B v (b i) = TensorFrame.signature i * b.repr v i := by
    rw [hc, ← mul_assoc, hs, one_mul]
  rw [ht]
  ring

/-- A normal-form Lorentz metric has a normalized timelike metric dual and
a temporal linear form with strictly spacelike kernel. -/
theorem exists_temporal_covector_of_lorentzBasis (B : LinearMap.BilinForm ℝ CoordinateSpace)
    (hSym : B.IsSymm) (b : Basis Index ℝ CoordinateSpace)
    (hb : ∀ i j, B (b i) (b j) = TensorFrame.standardInverse i j) :
    ∃ n : CoordinateSpace, ∃ L : CoordinateSpace →L[ℝ] ℝ,
      B n n = -1 ∧ (∀ v, L v = -B n v) ∧
      ∀ v, v ≠ 0 → L v = 0 → 0 < B v v := by
  let L := (b.coord 0).toContinuousLinearMap
  refine ⟨b 0, L, ?_, ?_, ?_⟩
  · simpa [TensorFrame.standardInverse, TensorFrame.signature] using hb 0 0
  · intro v
    have h : b.repr v 0 = TensorFrame.signature 0 * B v (b 0) :=
      BasisFrame.coordinate_eq_signature_pairing B b hb v 0
    change b.repr v 0 = -B (b 0) v
    rw [hSym.eq (b 0) v]
    simpa [TensorFrame.signature] using h
  · intro v hne hL
    change b.repr v 0 = 0 at hL
    rw [fiber_self_eq_signature_sum B b hb]
    have hterm (i : Index) : TensorFrame.signature i * (b.repr v i) ^ 2 = (b.repr v i) ^ 2 := by
      by_cases hi : i = 0
      · subst i
        simp [hL]
      · simp [TensorFrame.signature, hi]
    simp_rw [hterm]
    have hn : ∃ i, b.repr v i ≠ 0 := by
      by_contra! he
      apply hne
      apply b.repr.injective
      ext i
      simpa only [map_zero, Finsupp.zero_apply] using he i
    obtain ⟨i, hi⟩ := hn
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩

/-- The selected covector and its unit timelike metric dual on an arbitrary given atlas chart. -/
theorem exists_temporal_covector_coordinateBilinear (g : Field (M := M)) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    ∃ n : CoordinateSpace, ∃ L : CoordinateSpace →L[ℝ] ℝ,
      coordinateBilinear g c y n n = -1 ∧
      (∀ v, L v = -coordinateBilinear g c y n v) ∧
      ∀ v, v ≠ 0 → L v = 0 → 0 < coordinateBilinear g c y v v := by
  obtain ⟨b, hb⟩ := exists_lorentzBasis_coordinateBilinear g hL c hy
  exact exists_temporal_covector_of_lorentzBasis _ (coordinateBilinear_symmetric g hs c y) b hb

end Burnett.Geometry.CotangentHamiltonTemporalCone

namespace Burnett.Geometry.CotangentHamiltonTemporalCone

open Set Filter
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

private theorem quadratic_eq_coordinate_sum (B : LinearMap.BilinForm ℝ CoordinateSpace)
    (v : CoordinateSpace) :
    B v v = ∑ i, ∑ j, B (coordinateBasis i) (coordinateBasis j) * (v i * v j) := by
  have hv : v = ∑ i, v i • coordinateBasis i := (coordinateBasis.sum_repr v).symm
  calc
    B v v = B (∑ i, v i • coordinateBasis i) (∑ j, v j • coordinateBasis j) :=
      congrArg₂ (fun u w : CoordinateSpace => B u w) hv hv
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem continuousAt_quadratic_of_components (B : CoordinateSpace →
    LinearMap.BilinForm ℝ CoordinateSpace) {y₀ : CoordinateSpace} (v : CoordinateSpace)
    (hB : ∀ i j, ContinuousAt (fun y => B y (coordinateBasis i) (coordinateBasis j)) y₀) :
    ContinuousAt (fun z : CoordinateSpace × CoordinateSpace => B z.2 z.1 z.1) (v, y₀) := by
  simp_rw [quadratic_eq_coordinate_sum]
  unfold ContinuousAt
  apply tendsto_finset_sum
  intro i _
  apply tendsto_finset_sum
  intro j _
  have hC : ContinuousAt (fun z : CoordinateSpace × CoordinateSpace =>
      B z.2 (coordinateBasis i) (coordinateBasis j)) (v, y₀) := by
    have hp : ContinuousAt (Prod.snd : CoordinateSpace × CoordinateSpace → CoordinateSpace)
        (v, y₀) := continuous_snd.continuousAt
    exact (hB i j).tendsto.comp hp.tendsto
  have hi : ContinuousAt (fun z : CoordinateSpace × CoordinateSpace => z.1 i) (v, y₀) :=
    (EuclideanSpace.proj i).continuous.continuousAt.comp
    (continuous_fst.continuousAt (x := (v, y₀)))
  have hj : ContinuousAt (fun z : CoordinateSpace × CoordinateSpace => z.1 j) (v, y₀) :=
    (EuclideanSpace.proj j).continuous.continuousAt.comp
    (continuous_fst.continuousAt (x := (v, y₀)))
  exact (hC.mul (hi.mul hj)).tendsto

/-- A fixed temporal functional separates every nearby null direction from zero,
uniformly over the normalized directions of the actual coordinate null cone. -/
theorem exists_uniform_local_null_cone_bound (B : CoordinateSpace →
    LinearMap.BilinForm ℝ CoordinateSpace) {y₀ : CoordinateSpace} (L : CoordinateSpace →L[ℝ] ℝ)
    (hB : ∀ i j, ContinuousAt (fun y => B y (coordinateBasis i) (coordinateBasis j)) y₀)
    (hker : ∀ v, v ≠ 0 → L v = 0 → 0 < B y₀ v v) :
    ∃ C > (0 : ℝ), ∀ᶠ y in 𝓝 y₀,
      ∀ v, B y v v = 0 → ‖v‖ ≤ C * |L v| := by
  let S := Metric.sphere (0 : CoordinateSpace) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hSnonempty : S.Nonempty :=
    ⟨EuclideanSpace.single (0 : Index) (1 : ℝ), by
      simp [S, EuclideanSpace.norm_single]⟩
  let F (z : CoordinateSpace × CoordinateSpace) := |L z.1| + |B z.2 z.1 z.1|
  have hF (v : CoordinateSpace) : ContinuousAt F (v, y₀) :=
    ((L.continuous.continuousAt.comp continuous_fst.continuousAt).abs).add
      (continuousAt_quadratic_of_components B v hB).abs
  have hFpos (v : CoordinateSpace) (hv : v ∈ S) : 0 < F (v, y₀) := by
    have hvnorm : ‖v‖ = 1 := by simpa only [S, Metric.mem_sphere, dist_zero_right] using hv
    by_cases hl : L v = 0
    · have hq := hker v (norm_ne_zero_iff.mp (hvnorm.symm ▸ one_ne_zero)) hl
      exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr hq.ne')
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hl) (abs_nonneg _)
  have hFc : Continuous (fun v : CoordinateSpace => F (v, y₀)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hpair : ContinuousAt (fun z : CoordinateSpace => (z, y₀)) v :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact (hF v).tendsto.comp hpair.tendsto
  obtain ⟨v₀, hv₀, hmin⟩ := hS.exists_isMinOn hSnonempty hFc.continuousOn
  let ε := F (v₀, y₀) / 2
  have hε : 0 < ε := half_pos (hFpos v₀ hv₀)
  let P : Set (CoordinateSpace × CoordinateSpace) := {z | ε < F z}
  have hP : P ∈ (𝓝ˢ S) ×ˢ (𝓝 y₀) := by
    apply hS.mem_nhdsSet_prod_of_forall
    intro v hv
    rw [← nhds_prod_eq]
    have hv' : ε < F (v, y₀) := (half_lt_self (hFpos v₀ hv₀)).trans_le (hmin hv)
    exact (hF v).preimage_mem_nhds (Ioi_mem_nhds hv')
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.mp hP
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  filter_upwards [hV] with y hy
  intro v hnull
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r := ‖v‖⁻¹
  have hr : 0 < r := inv_pos.mpr hvnorm
  have hw : r • v ∈ S := by
    change r • v ∈ Metric.sphere (0 : CoordinateSpace) 1
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_cancel₀ hvnorm.ne'
  have hwU : r • v ∈ U := mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hU _ hw)
  have hpos : ε < F (r • v, y) := hUV ⟨hwU, hy⟩
  have hl : |L (r • v)| = r * |L v| := by
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos hr]
  have hz : B y (r • v) (r • v) = 0 := by
    simp [hnull]
  have hpos' : ε < |L v| / ‖v‖ := by
    change ε < |L (r • v)| + |B y (r • v) (r • v)| at hpos
    rw [hl, hz, abs_zero, add_zero] at hpos
    simpa only [r, div_eq_mul_inv, mul_comm] using hpos
  have hscaled := (lt_div_iff₀ hvnorm).mp hpos'
  have hfinal : ‖v‖ < |L v| / ε :=
    (lt_div_iff₀ hε).mpr (by simpa only [mul_comm] using hscaled)
  simpa [div_eq_mul_inv, mul_comm] using hfinal.le

/-- A nonvanishing temporal component has one sign on a connected time interval. -/
theorem orient_temporal_functional_on_interval (I : Set ℝ) (hI : I.OrdConnected)
    (v : ℝ → CoordinateSpace) (hv : ContinuousOn v I) (L : CoordinateSpace →L[ℝ] ℝ)
    (hL : ∀ t ∈ I, L (v t) ≠ 0) {C : ℝ}
    (hC : ∀ t ∈ I, ‖v t‖ ≤ C * |L (v t)|) (t₀ : ℝ) (ht₀ : t₀ ∈ I) :
    ∃ L' : CoordinateSpace →L[ℝ] ℝ, (L' = L ∨ L' = -L) ∧
      ∀ t ∈ I, 0 < L' (v t) ∧ ‖v t‖ ≤ C * L' (v t) := by
  let w (t : ℝ) := L (v t)
  have hconn : OrdConnected (w '' I) :=
    isPreconnected_iff_ordConnected.mp
      (hI.isPreconnected.image w (L.continuous.comp_continuousOn hv))
  have hno : (0 : ℝ) ∉ w '' I := by
    rintro ⟨t, ht, he⟩
    exact hL t ht he
  rcases (hL t₀ ht₀).lt_or_gt with hneg | hpos
  · refine ⟨-L, Or.inr rfl, ?_⟩
    intro t ht
    have hn : w t < 0 := by
      by_contra! hl
      exact hno (hconn.out ⟨t₀, ht₀, rfl⟩ ⟨t, ht, rfl⟩ ⟨hneg.le, hl⟩)
    have hb := hC t ht
    change ‖v t‖ ≤ C * |w t| at hb
    exact ⟨by simpa only [ContinuousLinearMap.neg_apply] using neg_pos.mpr hn,
      by simpa only [abs_of_neg hn, ContinuousLinearMap.neg_apply] using hb⟩
  · refine ⟨L, Or.inl rfl, ?_⟩
    intro t ht
    have hp : 0 < w t := by
      by_contra! hl
      exact hno (hconn.out ⟨t, ht, rfl⟩ ⟨t₀, ht₀, rfl⟩ ⟨hl, hpos.le⟩)
    have hb := hC t ht
    change ‖v t‖ ≤ C * |w t| at hb
    exact ⟨hp, by simpa only [abs_of_pos hp] using hb⟩

end Burnett.Geometry.CotangentHamiltonTemporalCone

namespace Burnett.Geometry.CotangentHamiltonTemporalCone

open Set Filter
open scoped Topology Manifold ContDiff BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.BackgroundConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

private theorem norm_connection_le_norm_sum (K : Connection) (i j k : Index) :
    ‖K i j k‖ ≤ ∑ a, ∑ b, ∑ d, ‖K a b d‖ := by
  calc
    ‖K i j k‖ ≤ ∑ d, ‖K i j d‖ :=
      Finset.single_le_sum (fun a _ => norm_nonneg (K i j a)) (Finset.mem_univ k)
    _ ≤ ∑ b, ∑ d, ‖K i b d‖ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun d _ => norm_nonneg (K i a d))
        (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ∑ d, ‖K a b d‖ :=
      Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun d _ => norm_nonneg (K a b d))
        (Finset.mem_univ i)

/-- One open neighborhood of the given base point has a stable null cone,
bounded absolute temporal coordinate, and uniform bound on all actual Christoffel entries. -/
theorem exists_stable_temporal_chart_region (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    (c : M) {y₀ : CoordinateSpace} (hy₀ : y₀ ∈ (chartAt CoordinateSpace c).target) :
    ∃ U : Set CoordinateSpace, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (chartAt CoordinateSpace c).target ∧
      ∃ n : CoordinateSpace, ∃ L : CoordinateSpace →L[ℝ] ℝ,
      ∃ C G T : ℝ, 0 < C ∧ 0 < G ∧ 0 < T ∧
        coordinateBilinear g c y₀ n n = -1 ∧ (∀ v, L v = -coordinateBilinear g c y₀ n v) ∧
        ∀ y ∈ U,
          (∀ v, coordinateBilinear g c y v v = 0 → ‖v‖ ≤ C * |L v|) ∧
          (∀ i j k, ‖computedConnection (coordinateBilinear g c) y i j k‖ ≤ G) ∧
          |L y| ≤ T := by
  let B := coordinateBilinear g c
  let Γ := computedConnection B
  have ht := (chartAt CoordinateSpace c).open_target.mem_nhds hy₀
  obtain ⟨n, L, hn₀, hdual, hker⟩ := exists_temporal_covector_coordinateBilinear g hs hL c hy₀
  have hB (i j : Index) : ContinuousAt (fun y => B y (coordinateBasis i) (coordinateBasis j)) y₀ :=
    (contDiffOn_coordinateBilinear_apply g hg c (coordinateBasis i) (coordinateBasis j)).continuousOn.continuousAt ht
  obtain ⟨C, hC, hcone⟩ := exists_uniform_local_null_cone_bound B L hB hker
  let G := (∑ a, ∑ b, ∑ d, ‖Γ y₀ a b d‖) + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hΓ : ContinuousAt Γ y₀ :=
    (SmoothMetricConnection.contDiffOn_coordinateBilinear_connection g hg hn c).continuousOn.continuousAt ht
  have hΓbound : ∀ᶠ y in 𝓝 y₀, ∀ i j k, ‖Γ y i j k‖ ≤ G := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
    have h₁ : ContinuousAt (fun y => Γ y i j k) y₀ :=
      (continuous_apply k).continuousAt.comp
        ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hΓ))
    have h₂ : ‖Γ y₀ i j k‖ < G := by
      exact (norm_connection_le_norm_sum (Γ y₀) i j k).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    have h₃ : ∀ᶠ y in 𝓝 y₀, ‖Γ y i j k‖ < G :=
      h₁.norm.preimage_mem_nhds (Iio_mem_nhds h₂)
    exact h₃.mono fun _ hy => hy.le
  let T := |L y₀| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have htime : ∀ᶠ y in 𝓝 y₀, |L y| ≤ T := by
    have hlt : |L y₀| < T := by dsimp [T]; linarith
    have h₁ : ∀ᶠ y in 𝓝 y₀, |L y| < T :=
      L.continuous.continuousAt.abs.preimage_mem_nhds (Iio_mem_nhds hlt)
    exact h₁.mono fun _ hy => hy.le
  obtain ⟨U, hU, hUopen, hU₀⟩ := mem_nhds_iff.mp (inter_mem ht (inter_mem hcone (inter_mem hΓbound htime)))
  exact ⟨U, hUopen, hU₀, fun _ hy => (hU hy).1, n, L, C, G, T, hC, hG, hT, hn₀, hdual,
    fun y hy => (hU hy).2⟩

end Burnett.Geometry.CotangentHamiltonTemporalCone

namespace Burnett.Geometry.CotangentHamiltonTemporalCone

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonPhaseEndpoint

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- In the actual chart there is a neighborhood on which the analytic endpoint
estimates apply to every connected tail of an actual nonzero null trajectory. -/
theorem exists_temporal_chart_neighborhood_for_null_phase_endpoint [T2Space M]
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (c : M) {y₀ : CoordinateSpace}
    (hy₀ : y₀ ∈ (chartAt CoordinateSpace c).target) :
    ∃ U : Set CoordinateSpace, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (chartAt CoordinateSpace c).target ∧
      ∀ (p : CotangentBundle M) (A : CanonicalTrajectory g p),
        p ∈ puncturedCotangent → dualEnergy g hn p = 0 →
        ∀ (I : Set ℝ), IsOpen I → I.OrdConnected → I ⊆ A.domain →
          MapsTo A.curve I (cotangentSource c) → ∀ t₀ ∈ I,
          let x : ℝ → CoordinateSpace := fun t => (cotangentChart c (A.curve t)).1
          MapsTo x I U →
            BddAbove I ∧ t₀ < sSup I ∧
              (Tendsto x (𝓝[<] sSup I) (𝓝 y₀) →
                ∃ q : CotangentBundle M,
                  Tendsto A.curve (𝓝[<] sSup I) (𝓝 q) ∧ q ∈ cotangentSource c ∧
                  (cotangentChart c q).1 = y₀ ∧ q ∈ puncturedCotangent ∧ dualEnergy g hn q = 0) := by
  obtain ⟨U, hUopen, hU₀, hUtarget, _, L, C, G, T, hC, hG, _, _, _, hU⟩ :=
    exists_stable_temporal_chart_region g hg hn hs hL c hy₀
  refine ⟨U, hUopen, hU₀, hUtarget, ?_⟩
  intro p A hp hnull I hI hIconn hsub hchart t₀ ht₀ x hx
  let v := deriv x
  have hvel (t : ℝ) (ht : t ∈ I) :
      v t ≠ 0 ∧ coordinateBilinear g c (x t) (v t) (v t) = 0 ∧ ContinuousAt v t := by
    obtain ⟨v₀, a, hd, hderiv, hne, hq, _⟩ :=
      A.projected_null_geodesic g hg hn hs hp hnull c t (hsub ht) (hchart ht)
    have hv₀ : v t = v₀ := hd.deriv
    rw [hv₀]
    exact ⟨hne, hq, hderiv.continuousAt⟩
  have hvcont : ContinuousOn v I :=
    fun t ht => (hvel t ht).2.2.continuousWithinAt
  have hc (t : ℝ) (ht : t ∈ I) : ‖v t‖ ≤ C * |L (v t)| :=
    (hU (x t) (hx ht)).1 (v t) (hvel t ht).2.1
  have hLnonzero (t : ℝ) (ht : t ∈ I) : L (v t) ≠ 0 := by
    intro he
    have hh := hc t ht
    rw [he, abs_zero, mul_zero] at hh
    exact (hvel t ht).1 (norm_le_zero_iff.mp hh)
  obtain ⟨L', hL', hv'⟩ := orient_temporal_functional_on_interval I hIconn v hvcont
    L hLnonzero hc t₀ ht₀
  have htime (t : ℝ) (ht : t ∈ I) : L' (x t) ≤ T := by
    have hh := (hU (x t) (hx ht)).2.2
    rcases hL' with h | h
    · rw [h]
      exact (le_abs_self _).trans hh
    · rw [h, ContinuousLinearMap.neg_apply]
      exact (neg_le_abs _).trans hh
  have hΓ (t : ℝ) (ht : t ∈ I) (i j k : Index) :
      ‖computedConnection (coordinateBilinear g c) (x t) i j k‖ ≤ G :=
    (hU (x t) (hx ht)).2.1 i j k
  have hpos (t : ℝ) (ht : t ∈ I) : 0 < L' (v t) := (hv' t ht).1
  have hcone (t : ℝ) (ht : t ∈ I) : ‖v t‖ ≤ C * L' (v t) := (hv' t ht).2
  obtain ⟨hbounded, htSup, _⟩ := canonicalTrajectory_finite_chart_velocity g hg hn hs
    A c I hI hIconn hsub hchart L' ht₀ hC.le hG.le hΓ hpos htime hcone
  exact ⟨hbounded, htSup, fun hlimit =>
    (canonicalTrajectory_null_phase_limit_in_chart g hg hn hs A hnull c I hI hIconn hsub
      hchart L' ht₀ hC.le hG.le hΓ hpos htime hcone hy₀ hlimit).2.2⟩

end Burnett.Geometry.CotangentHamiltonTemporalCone

namespace Burnett.Geometry.CotangentHamiltonAffineExtension

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original left derivative and the right derivative agree at the junction
of the piecewise path, in the original real parameter. -/
theorem hasDerivAt_join_of_left_derivative_limit
    (γ ζ : ℝ → E) (b : ℝ) (V : E) (I : Set ℝ)
    (hI : I ∈ 𝓝[<] b) (hsub : I ⊆ Iio b)
    (hγ : ∀ t ∈ I, DifferentiableAt ℝ γ t)
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 (ζ b)))
    (hdlim : Tendsto (deriv γ) (𝓝[<] b) (𝓝 V))
    (hζ : HasDerivAt ζ V b) :
    HasDerivAt (fun t => if t < b then γ t else ζ t) V b := by
  let η (t : ℝ) := if t < b then γ t else ζ t
  have hηb : η b = ζ b := if_neg (lt_irrefl _)
  have hη (t : ℝ) (ht : t < b) : η =ᶠ[𝓝 t] γ := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact if_pos hs
  have hd (t : ℝ) (ht : t ∈ I) : HasDerivAt η (deriv γ t) t :=
    (hγ t ht).hasDerivAt.congr_of_eventuallyEq (hη t (hsub ht))
  have he : η =ᶠ[𝓝[<] b] γ := by
    filter_upwards [hI] with t ht
    exact if_pos (hsub ht)
  have hcont : ContinuousWithinAt η I b := by
    change Tendsto η (𝓝[I] b) (𝓝 (η b))
    rw [hηb]
    exact (hlim.congr' he.symm).mono_left (nhdsWithin_mono _ hsub)
  have hde : deriv η =ᶠ[𝓝[<] b] deriv γ := by
    filter_upwards [hI] with t ht
    exact (hd t ht).deriv
  have hl : HasDerivWithinAt η V (Iic b) b :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      hcont hI (hdlim.congr' hde.symm)
  have hr : HasDerivWithinAt η V (Ici b) b :=
    hζ.hasDerivWithinAt.congr (fun t ht => if_neg (not_lt.mpr ht)) hηb
  have hh := hl.union hr
  rw [Iic_union_Ici] at hh
  exact hh.hasDerivAt univ_mem

end Burnett.Geometry.CotangentHamiltonAffineExtension

namespace Burnett.Geometry.CotangentHamiltonAffineExtension

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullAngular Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- If a left Hamilton curve reaches the initial phase point of a right Hamilton curve,
their piecewise union is a chart Hamilton curve on an open neighborhood of the junction. -/
theorem exists_hamiltonChart_join_near (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (c : M) (γ ζ : ℝ → CotangentBundle M)
    (b : ℝ) (I J : Set ℝ) (hI : I ∈ 𝓝[<] b) (hIleft : I ⊆ Iio b)
    (hJ : IsOpen J) (hbJ : b ∈ J)
    (hγ : IsHamiltonCurveInChart g c γ I) (hζ : IsHamiltonCurveInChart g c ζ J)
    (hlim : Tendsto γ (𝓝[<] b) (𝓝 (ζ b))) :
    ∃ K : Set ℝ, IsOpen K ∧ b ∈ K ∧
      IsHamiltonCurveInChart g c (fun t => if t < b then γ t else ζ t) K := by
  let zL := cotangentChart c ∘ γ
  let zR := cotangentChart c ∘ ζ
  let H := hamiltonVector (chartInverse g c)
  let η (t : ℝ) : CotangentBundle M := if t < b then γ t else ζ t
  have hsrc := hζ.1 b hbJ
  have htgt := cotangentChart_mapsTo c hsrc
  have hc : ContinuousAt (cotangentChart c) (ζ b) :=
    (contMDiffOn_cotangentChart c).continuousOn.continuousAt ((isOpen_cotangentSource c).mem_nhds hsrc)
  have hH : ContinuousAt H (zR b) :=
    (contDiffOn_hamiltonVector_chartInverse g hg hn c).continuousOn.continuousAt
      ((isOpen_phaseTarget c).mem_nhds htgt)
  have hzlim : Tendsto zL (𝓝[<] b) (𝓝 (zR b)) := hc.tendsto.comp hlim
  have hzde : deriv zL =ᶠ[𝓝[<] b] H ∘ zL := by
    filter_upwards [hI] with t ht
    exact (hγ.2 t ht).deriv
  have hdlim : Tendsto (deriv zL) (𝓝[<] b) (𝓝 (H (zR b))) :=
    (hH.tendsto.comp hzlim).congr' hzde.symm
  have hd : HasDerivAt (fun t => cotangentChart c (η t)) (H (zR b)) b := by
    have h := hasDerivAt_join_of_left_derivative_limit zL zR b (H (zR b)) I hI hIleft
      (fun t ht => (hγ.2 t ht).differentiableAt) hzlim hdlim (hζ.2 b hbJ)
    convert h using 1
    funext t
    by_cases ht : t < b <;> simp [η, ht, zL, zR]
  obtain ⟨l, hl, hleft⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hI
  obtain ⟨a, r, hbr, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds hbJ)
  refine ⟨Ioo l r, isOpen_Ioo, ⟨hl, hbr.2⟩, ?_, ?_⟩
  · intro t ht
    by_cases hl' : t < b
    · simpa only [if_pos hl'] using hγ.1 t (hleft ⟨ht.1, hl'⟩)
    · simpa only [if_neg hl'] using hζ.1 t (hright ⟨hbr.1.trans_le (le_of_not_gt hl'), ht.2⟩)
  · intro t ht
    rcases lt_trichotomy t b with ht' | ht' | ht'
    · have he : (fun s => cotangentChart c (η s)) =ᶠ[𝓝 t] zL := by
        filter_upwards [Iio_mem_nhds ht'] with s hs
        simp only [η, zL, Function.comp_apply, if_pos (mem_Iio.mp hs)]
      simpa only [η, if_pos ht'] using (hγ.2 t (hleft ⟨ht.1, ht'⟩)).congr_of_eventuallyEq he
    · subst t
      simpa only [η, if_neg (lt_irrefl _), zR, Function.comp_apply] using hd
    · have he : (fun s => cotangentChart c (η s)) =ᶠ[𝓝 t] zR := by
        filter_upwards [Ioi_mem_nhds ht'] with s hs
        simp only [η, zR, Function.comp_apply, if_neg (not_lt.mpr (mem_Ioi.mp hs).le)]
      simpa only [η, if_neg (not_lt.mpr ht'.le)] using
        (hζ.2 t (hright ⟨hbr.1.trans ht', ht.2⟩)).congr_of_eventuallyEq he

end Burnett.Geometry.CotangentHamiltonAffineExtension

namespace Burnett.Geometry.CotangentHamiltonAffineExtension

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- A bounded open interval lies strictly below its right endpoint. -/
theorem lt_sSup_of_mem_open_interval {I : Set ℝ} (hI : IsOpen I)
    (hbd : BddAbove I) {t : ℝ} (ht : t ∈ I) : t < sSup I := by
  obtain ⟨a, r, har, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds ht)
  have h₁ : t < (t + r) / 2 := by linarith [har.2]
  have h₂ : (t + r) / 2 ∈ I := hsub ⟨har.1.trans h₁, by linarith [har.2]⟩
  exact lt_csSup_of_lt hbd h₂ h₁

/-- A nonempty bounded open interval contains a full left neighborhood of its right endpoint. -/
theorem open_interval_mem_nhdsLT_sSup {I : Set ℝ} (hI : IsOpen I) (hconn : I.OrdConnected)
    (hbd : BddAbove I) (hIne : I.Nonempty) : I ∈ 𝓝[<] sSup I := by
  obtain ⟨a, ha⟩ := hIne
  have ha' := lt_sSup_of_mem_open_interval hI hbd ha
  refine mem_of_superset (Ioo_mem_nhdsLT ha') ?_
  intro t ht
  obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨a, ha⟩ ht.2
  exact hconn.out ha hs ⟨ht.1.le, hts.le⟩

/-- A genuine nonzero null cotangent limit at finite affine time gives an actual
extension containing the entire original interval and its right endpoint. -/
theorem exists_right_extension_of_null_phase_limit (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (hbounded : BddAbove A.domain)
    (q : CotangentBundle M) (hq : q ∈ puncturedCotangent) (hnull : dualEnergy g hn q = 0)
    (hlim : Tendsto A.curve (𝓝[<] sSup A.domain) (𝓝 q)) :
    ∃ D : CanonicalTrajectory g p, A.domain ⊆ D.domain ∧
      EqOn D.curve A.curve A.domain ∧ sSup A.domain ∈ D.domain ∧ D.curve (sSup A.domain) = q := by
  let b := sSup A.domain
  let c := q.1
  have hqsrc : q ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  have hlt (t : ℝ) (ht : t ∈ A.domain) : t < b :=
    lt_sSup_of_mem_open_interval A.domain_open hbounded ht
  have hAnear : A.domain ∈ 𝓝[<] b :=
    open_interval_mem_nhdsLT_sSup A.domain_open A.domain_interval hbounded ⟨0, A.zero_mem⟩
  let I := A.domain ∩ A.curve ⁻¹' cotangentSource c
  have hI : I ∈ 𝓝[<] b :=
    inter_mem hAnear (hlim ((isOpen_cotangentSource c).mem_nhds hqsrc))
  have hIopen : IsOpen I :=
    A.integral.continuousOn.isOpen_inter_preimage A.domain_open (isOpen_cotangentSource c)
  have hIleft : I ⊆ Iio b := fun t ht => hlt t ht.1
  have hAl : IsHamiltonCurveInChart g c A.curve I :=
    canonicalCurve_in_chart g hg hn hs c A.curve I hIopen (A.integral.mono inter_subset_left)
      inter_subset_right
  obtain ⟨δ, hδ, ζ, hζ₀, hζ, _, hζnull⟩ := exists_local_null_canonicalCurve g hg hn hs q hq hnull
  let R := shiftedDomain (-b) (Ioo (-δ) δ)
  let ρ := shiftedCurve (-b) ζ
  have hRopen : IsOpen R := isOpen_Ioo.preimage (continuous_id.add continuous_const)
  have hρ : IsHamiltonCurveInChart g c ρ R :=
    shiftedCurve_hamilton g c ζ _ hζ (-b)
  have hbR : b ∈ R := by
    change b + -b ∈ Ioo (-δ) δ
    simpa only [add_neg_cancel] using (show (0 : ℝ) ∈ Ioo (-δ) δ from ⟨by linarith, hδ⟩)
  have hρb : ρ b = q := by simpa only [ρ, shiftedCurve, add_neg_cancel] using hζ₀
  have hRh : IsMIntegralCurveOn (I := CotangentModelWithCorners) ρ (canonicalHamilton g) R :=
    hamiltonCurve_canonical_integralOn g hg hn hs c ρ R hRopen hρ
      (fun t ht => (hζnull (t + -b) ht).1)
  let η (t : ℝ) : CotangentBundle M := if t < b then A.curve t else ρ t
  have hjoin : ∃ K : Set ℝ, IsOpen K ∧ b ∈ K ∧ IsHamiltonCurveInChart g c η K :=
    exists_hamiltonChart_join_near g hg hn c A.curve ρ b I R hI hIleft hRopen hbR hAl hρ
      (hρb.symm ▸ hlim)
  obtain ⟨K, hK, hbK, hKcurve⟩ := hjoin
  have hbderiv : HasMFDerivAt 𝓘(ℝ) CotangentModelWithCorners η b
      ((1 : ℝ →L[ℝ] ℝ).smulRight (canonicalHamilton g (η b))) := by
    have d := ((hamiltonCurve_actual_integralOn g c η K hK hKcurve) b hbK).hasMFDerivAt
      (hK.mem_nhds hbK)
    have he : intrinsicHamilton g c (η b) = canonicalHamilton g (η b) :=
      intrinsicHamilton_chart_independent_all g hg hn hs c (η b).1 (η b)
        (hKcurve.1 b hbK) (mem_chart_source CoordinateSpace _)
    rw [← he]
    exact d
  obtain ⟨l, hl, hleft⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hI
  let S := A.domain ∪ Ioo l (b + δ)
  have hS : IsOpen S := A.domain_open.union isOpen_Ioo
  have hmem (t : ℝ) (ht : t ∈ A.domain) : t ∈ S := Or.inl ht
  have hbS : b ∈ S := Or.inr ⟨hl, lt_add_of_pos_right _ hδ⟩
  have hSconn : S.OrdConnected := by
    let t := (l + b) / 2
    have hl' : l < b := mem_Iio.mp hl
    have ht : t ∈ Ioo l b := by dsimp [t]; constructor <;> linarith [hl']
    have he : (A.domain ∩ Ioo l (b + δ)).Nonempty :=
      ⟨t, (hleft ht).1, ht.1, ht.2.trans (lt_add_of_pos_right _ hδ)⟩
    exact isPreconnected_iff_ordConnected.mp
      (A.domain_interval.isPreconnected.union' he isPreconnected_Ioo)
  have hSderiv : IsMIntegralCurveOn (I := CotangentModelWithCorners) η (canonicalHamilton g) S := by
    intro t ht
    rcases lt_trichotomy t b with htb | htb | htb
    · have htA : t ∈ A.domain := ht.elim id (fun h => (hleft ⟨h.1, htb⟩).1)
      have hf : η =ᶠ[𝓝 t] A.curve := by
        filter_upwards [Iio_mem_nhds htb] with s hs'
        exact if_pos hs'
      have hd := ((A.integral t htA).hasMFDerivAt (A.domain_open.mem_nhds htA)).congr_of_eventuallyEq hf
      rw [show η t = A.curve t from if_pos htb]
      exact hd.hasMFDerivWithinAt
    · subst t
      exact hbderiv.hasMFDerivWithinAt
    · have htS : t ∈ Ioo l (b + δ) := ht.elim (fun he => (htb.not_gt (hlt t he)).elim) id
      have htR : t ∈ R := by
        change t + -b ∈ Ioo (-δ) δ
        exact ⟨by linarith, by linarith [htS.2]⟩
      have hf : η =ᶠ[𝓝 t] ρ := by
        filter_upwards [Ioi_mem_nhds htb] with s hs'
        exact if_neg (not_lt.mpr (le_of_lt hs'))
      have hd := ((hRh t htR).hasMFDerivAt (hRopen.mem_nhds htR)).congr_of_eventuallyEq hf
      rw [show η t = ρ t from if_neg (not_lt.mpr htb.le)]
      exact hd.hasMFDerivWithinAt
  have hηA : EqOn η A.curve A.domain := fun t ht => if_pos (hlt t ht)
  have hη₀ : η 0 = p := (hηA A.zero_mem).trans A.initial
  have hηb : η b = q := (if_neg (lt_irrefl _)).trans hρb
  exact ⟨⟨S, η, hS, hSconn, hmem 0 A.zero_mem, hη₀, hSderiv⟩, hmem, hηA, hbS, hηb⟩

/-- Maximality rules out a finite nonzero null phase endpoint. -/
theorem maximal_right_no_null_phase_limit (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain)
    (hbounded : BddAbove A.domain) (q : CotangentBundle M)
    (hq : q ∈ puncturedCotangent) (hnull : dualEnergy g hn q = 0) :
    ¬ Tendsto A.curve (𝓝[<] sSup A.domain) (𝓝 q) := by
  intro hlim
  obtain ⟨D, _, _, hb, _⟩ := exists_right_extension_of_null_phase_limit g hg hn hs
    A hbounded q hq hnull hlim
  exact (lt_irrefl (sSup A.domain))
    (lt_sSup_of_mem_open_interval A.domain_open hbounded (hmax D hb))

end Burnett.Geometry.CotangentHamiltonAffineExtension

namespace Burnett.Geometry.CotangentHamiltonAffineExtension

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentHamiltonMaximalCurve Burnett.Geometry.CotangentHamiltonTemporalCone

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- An actual base neighborhood admits the temporal estimates for every true
nonzero null Hamilton trajectory that lies over it. -/
theorem exists_base_neighborhood_for_null_phase_endpoint (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (m : M) :
    ∃ W : Set M, W ∈ 𝓝 m ∧
      ∀ (p : CotangentBundle M) (A : CanonicalTrajectory g p),
        p ∈ puncturedCotangent → dualEnergy g hn p = 0 →
        ∀ I : Set ℝ, IsOpen I → I.OrdConnected → I ⊆ A.domain →
          ∀ t₀ ∈ I, MapsTo (fun t => (A.curve t).1) I W →
            BddAbove I ∧ t₀ < sSup I ∧
              (Tendsto (fun t => (A.curve t).1) (𝓝[<] sSup I) (𝓝 m) →
                ∃ q : CotangentBundle M, Tendsto A.curve (𝓝[<] sSup I) (𝓝 q) ∧
                  q ∈ puncturedCotangent ∧ dualEnergy g hn q = 0) := by
  let φ := chartAt CoordinateSpace m
  let y := φ m
  have hm : m ∈ φ.source := mem_chart_source CoordinateSpace _
  have hy : y ∈ φ.target := φ.map_source hm
  have hφ : ContinuousAt φ m := φ.continuousAt hm
  obtain ⟨U, hUopen, hyU, _, hU⟩ :=
    exists_temporal_chart_neighborhood_for_null_phase_endpoint g hg hn hs hL m hy
  let W := φ.source ∩ φ ⁻¹' U
  have hW : W ∈ 𝓝 m := inter_mem (φ.open_source.mem_nhds hm) (hφ.preimage_mem_nhds (hUopen.mem_nhds hyU))
  refine ⟨W, hW, ?_⟩
  intro p A hp hnull I hI hconn hsub t₀ ht₀ hMaps
  have hchart : MapsTo A.curve I (cotangentSource m) :=
    fun _ ht => (hMaps ht).1
  have hx : MapsTo (fun t => (cotangentChart m (A.curve t)).1) I U :=
    fun _ ht => (hMaps ht).2
  obtain ⟨hbd, hEnd, hpLim⟩ := hU p A hp hnull I hI hconn hsub hchart t₀ ht₀ hx
  refine ⟨hbd, hEnd, fun hlim => ?_⟩
  have hyLim : Tendsto (fun t => (cotangentChart m (A.curve t)).1) (𝓝[<] sSup I) (𝓝 y) :=
    hφ.tendsto.comp hlim
  obtain ⟨q, hqLim, _, _, hq, hqnull⟩ := hpLim hyLim
  exact ⟨q, hqLim, hq, hqnull⟩

/-- The base of a maximal nonzero null Hamilton trajectory has no limit at
its finite right affine endpoint. -/
theorem maximal_right_no_base_limit_of_bddAbove (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain)
    (hbounded : BddAbove A.domain) (m : M) :
    ¬ Tendsto (fun t => (A.curve t).1) (𝓝[<] sSup A.domain) (𝓝 m) := by
  intro hlim
  obtain ⟨W, hW, htail⟩ := exists_base_neighborhood_for_null_phase_endpoint g hg hn hs hL m
  let b := sSup A.domain
  have hA : A.domain ∈ 𝓝[<] b :=
    open_interval_mem_nhdsLT_sSup A.domain_open A.domain_interval hbounded ⟨0, A.zero_mem⟩
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (inter_mem hA (hlim hW))
  let I := Ioo l b
  have hl' : l < b := mem_Iio.mp hl
  let t₀ := (l + b) / 2
  have ht₀ : t₀ ∈ I := by
    change l < t₀ ∧ t₀ < b
    dsimp [t₀]
    constructor <;> linarith
  have hIend : sSup I = b := csSup_Ioo hl'
  have hIlim : Tendsto (fun t => (A.curve t).1) (𝓝[<] sSup I) (𝓝 m) := by
    rw [hIend]
    exact hlim
  have h := htail p A hp hnull I isOpen_Ioo ordConnected_Ioo
    (hsub.trans inter_subset_left) t₀ ht₀ (hsub.trans inter_subset_right)
  obtain ⟨q, hqLim, hq, hqnull⟩ := h.2.2 hIlim
  rw [hIend] at hqLim
  exact maximal_right_no_null_phase_limit g hg hn hs A hmax hbounded q hq hqnull hqLim

/-- A nonzero null Hamilton trajectory with affine time unbounded to the right
has no base limit as its parameter tends to infinity. -/
theorem right_no_base_limit_of_unbounded (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (hunbounded : ¬ BddAbove A.domain) (m : M) :
    ¬ Tendsto (fun t => (A.curve t).1) atTop (𝓝 m) := by
  intro hlim
  obtain ⟨W, hW, htail⟩ := exists_base_neighborhood_for_null_phase_endpoint g hg hn hs hL m
  obtain ⟨l, hl⟩ := eventually_atTop.mp (hlim hW)
  let I := A.domain ∩ Ioi l
  obtain ⟨t₀, ht₀, hlt⟩ := not_bddAbove_iff.mp hunbounded l
  have ht₀I : t₀ ∈ I := ⟨ht₀, mem_Ioi.mpr hlt⟩
  have hmaps : MapsTo (fun t => (A.curve t).1) I W :=
    fun _ ht => hl _ (mem_Ioi.mp ht.2).le
  have h := htail p A hp hnull I (A.domain_open.inter isOpen_Ioi)
    (A.domain_interval.inter ordConnected_Ioi) inter_subset_left t₀ ht₀I hmaps
  obtain ⟨C, hC⟩ := h.1
  apply hunbounded
  refine ⟨max l C, fun t ht => ?_⟩
  by_cases hlt : l < t
  · exact (hC (show t ∈ I from ⟨ht, mem_Ioi.mpr hlt⟩)).trans (le_max_right l C)
  · exact (le_of_not_gt hlt).trans (le_max_left l C)

/-- The upper affine-end filter uses a left neighborhood at a finite endpoint
and the atTop filter when the interval is unbounded above. -/
noncomputable def rightAffineEndFilter (I : Set ℝ) : Filter ℝ := by
  classical
  exact if BddAbove I then 𝓝[<] sSup I else atTop

/-- The base of a maximal genuine nonzero null canonical orbit has no limit at its right affine end. -/
theorem maximal_right_no_base_limit (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnull : dualEnergy g hn p = 0)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain) (m : M) :
    ¬ Tendsto (fun t => (A.curve t).1) (rightAffineEndFilter A.domain) (𝓝 m) := by
  classical
  by_cases hb : BddAbove A.domain
  · simpa only [rightAffineEndFilter, if_pos hb] using
      maximal_right_no_base_limit_of_bddAbove g hg hn hs hL A hp hnull hmax hb m
  · simpa only [rightAffineEndFilter, if_neg hb] using
      right_no_base_limit_of_unbounded g hg hn hs hL A hp hnull hb m

end Burnett.Geometry.CotangentHamiltonAffineExtension

namespace Burnett.Geometry.CotangentHamiltonTimeReversal

open Set Filter
open scoped Manifold ContDiff Topology Pointwise
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The canonical quadratic Hamilton equation has the same scaling rule for
every nonzero signed scale, including simultaneous time and fiber reversal. -/
theorem scaledCurve_hamilton_of_ne_zero (g : Field (M := M)) (c : M)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hγ : IsHamiltonCurveInChart g c γ I)
    {a : ℝ} (ha : a ≠ 0) :
    IsHamiltonCurveInChart g c (scaledCurve a γ) (scaledDomain a I) := by
  constructor
  · intro t ht
    exact hγ.1 (a * t) ht
  · intro t ht
    have htime : HasDerivAt (fun s : ℝ => a * s) a t :=
      by simpa using (hasDerivAt_id t).const_mul a
    have h := (phaseScale a).hasFDerivAt.comp_hasDerivAt t
      ((hγ.2 (a * t) ht).scomp t htime)
    simpa only [scaledCurve, cotangentChart_scale, map_smul, hamiltonVector_scale _ _ ha] using h

/-- Signed scaling of a true canonical trajectory is a true canonical trajectory on the
pulled-back time interval. The chart does not restrict the trajectory. -/
theorem canonicalIntegralCurve_scaled_of_ne_zero (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (γ : ℝ → CotangentBundle M) (I : Set ℝ) (hI : IsOpen I)
    (hγ : IsMIntegralCurveOn (I := CotangentModelWithCorners) γ (canonicalHamilton g) I)
    {a : ℝ} (ha : a ≠ 0) :
    IsMIntegralCurveOn (I := CotangentModelWithCorners) (scaledCurve a γ) (canonicalHamilton g)
      (scaledDomain a I) := by
  intro t ht
  let c := (γ (a * t)).1
  have hc : γ (a * t) ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨J, hJ, htJ, _, hchart⟩ :=
    canonicalCurve_chart_near g hg hn hs c γ I hI hγ (a * t) ht hc
  have hJo : IsOpen (scaledDomain a J) :=
    hJ.preimage (continuous_const.mul continuous_id)
  have hS := scaledCurve_hamilton_of_ne_zero g c γ J hchart ha
  have hderiv := ((hamiltonCurve_actual_integralOn g c (scaledCurve a γ) (scaledDomain a J)
    hJo hS) t htJ).hasMFDerivAt (hJo.mem_nhds htJ)
  let q := scaledCurve a γ t
  have he : intrinsicHamilton g c q = canonicalHamilton g q :=
    intrinsicHamilton_chart_independent_all g hg hn hs c q.1 q
      (hS.1 t htJ) (mem_chart_source CoordinateSpace _)
  change HasMFDerivAt 𝓘(ℝ) CotangentModelWithCorners (scaledCurve a γ) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (intrinsicHamilton g c q)) at hderiv
  rw [he] at hderiv
  exact hderiv.hasMFDerivWithinAt

/-- Time reversal pulls back the domain by negation, equivalently it is the negated set. -/
theorem scaledDomain_neg_one_eq_neg (I : Set ℝ) : scaledDomain (-1) I = -I := by
  ext t
  change (-1 : ℝ) * t ∈ I ↔ t ∈ -I
  rw [neg_one_mul, Set.mem_neg]

/-- Simultaneous time reversal and fiber negation of an actual trajectory. -/
def CanonicalTrajectory.timeReverse (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) :
    CanonicalTrajectory g (cotangentScale (-1) p) where
  domain := scaledDomain (-1) A.domain
  curve := scaledCurve (-1) A.curve
  domain_open := A.domain_open.preimage (continuous_const.mul continuous_id)
  domain_interval := by
    refine ⟨fun t ht u hu s hs' => ?_⟩
    change (-1 : ℝ) * t ∈ A.domain at ht
    change (-1 : ℝ) * u ∈ A.domain at hu
    change (-1 : ℝ) * s ∈ A.domain
    rw [neg_one_mul] at ht hu ⊢
    exact A.domain_interval.out hu ht ⟨neg_le_neg hs'.2, neg_le_neg hs'.1⟩
  zero_mem := by simpa [scaledDomain] using A.zero_mem
  initial := (scaledCurve_initial (-1) A.curve).trans (congrArg (cotangentScale (-1)) A.initial)
  integral := canonicalIntegralCurve_scaled_of_ne_zero g hg hn hs A.curve A.domain A.domain_open
    A.integral (by norm_num)

theorem timeReverse_domain (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) :
    (CanonicalTrajectory.timeReverse g hg hn hs A).domain = -A.domain :=
  scaledDomain_neg_one_eq_neg A.domain

theorem timeReverse_curve (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (t : ℝ) :
    (CanonicalTrajectory.timeReverse g hg hn hs A).curve t = cotangentScale (-1) (A.curve (-t)) := by
  change cotangentScale (-1) (A.curve ((-1 : ℝ) * t)) = _
  rw [neg_one_mul]

theorem timeReverse_base (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p) (t : ℝ) :
    ((CanonicalTrajectory.timeReverse g hg hn hs A).curve t).1 = (A.curve (-t)).1 := by
  rw [timeReverse_curve, cotangentScale_projection]

theorem cotangent_negScale_involutive (p : CotangentBundle M) :
    cotangentScale (-1) (cotangentScale (-1) p) = p := by
  rw [cotangentScale_mul]
  norm_num [cotangentScale_one]

/-- The reversed trajectory is maximal among genuine canonical trajectories through the reversed
phase point, since every competitor can be reversed again in its full domain. -/
theorem timeReverse_domain_maximal (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain)
    (D : CanonicalTrajectory g (cotangentScale (-1) p)) :
    D.domain ⊆ (CanonicalTrajectory.timeReverse g hg hn hs A).domain := by
  let D' := CanonicalTrajectory.timeReverse g hg hn hs D
  let E : CanonicalTrajectory g p :=
    ⟨D'.domain, D'.curve, D'.domain_open, D'.domain_interval, D'.zero_mem,
      D'.initial.trans (cotangent_negScale_involutive p), D'.integral⟩
  intro t ht
  have ht' : -t ∈ D'.domain := by
    change (-1 : ℝ) * (-t) ∈ D.domain
    simpa only [neg_one_mul, neg_neg] using ht
  have he := hmax E (show -t ∈ E.domain from ht')
  change (-1 : ℝ) * t ∈ A.domain
  simpa only [neg_one_mul] using he

end Burnett.Geometry.CotangentHamiltonTimeReversal

namespace Burnett.Geometry.CotangentHamiltonTimeReversal

open Set Filter
open scoped Manifold ContDiff Topology Pointwise
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentHamiltonMaximalCurve Burnett.Geometry.CotangentHamiltonAffineExtension

/-- The lower affine-end filter uses a right neighborhood at a finite endpoint
and the atBot filter when the interval is unbounded below. -/
noncomputable def leftAffineEndFilter (I : Set ℝ) : Filter ℝ := by
  classical
  exact if BddBelow I then 𝓝[>] sInf I else atBot

private theorem sup_neg_eq_neg_inf (I : Set ℝ) (hI : I.Nonempty) (hb : BddBelow I) :
    sSup (-I) = -sInf I := by
  have hb' : BddAbove (-I) := bddAbove_neg.mpr hb
  apply le_antisymm
  · apply csSup_le (Set.nonempty_neg.mpr hI)
    intro t ht
    have h := neg_le_neg (csInf_le hb (Set.mem_neg.mp ht))
    simpa only [neg_neg] using h
  · have h : -sSup (-I) ≤ sInf I := by
      apply le_csInf hI
      intro t ht
      have ht' : -t ∈ -I := by simpa only [Set.mem_neg, neg_neg] using ht
      have hh := neg_le_neg (le_csSup hb' ht')
      simpa only [neg_neg] using hh
    simpa only [neg_neg] using neg_le_neg h

/-- Negation sends the right affine end of the reversed time interval to the
left affine end of the original interval, in both finite and infinite cases. -/
theorem tendsto_neg_at_affine_ends (I : Set ℝ) (hI : I.Nonempty) :
    Tendsto (fun t : ℝ => -t) (rightAffineEndFilter (-I)) (leftAffineEndFilter I) := by
  classical
  by_cases h : BddBelow I
  · have h' : BddAbove (-I) := bddAbove_neg.mpr h
    rw [rightAffineEndFilter, leftAffineEndFilter, if_pos h', if_pos h, sup_neg_eq_neg_inf I hI h]
    exact tendsto_neg_nhdsLT_neg
  · have h' : ¬ BddAbove (-I) := mt bddAbove_neg.mp h
    rw [rightAffineEndFilter, leftAffineEndFilter, if_neg h', if_neg h]
    exact tendsto_neg_atTop_atBot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- Fiber negation preserves the actual punctured null cotangent cone. -/
theorem negScale_punctured_null (g : Field (M := M)) (hn : IsNondegenerate g)
    {p : CotangentBundle M} (hp : p ∈ puncturedCotangent) (hnp : dualEnergy g hn p = 0) :
    cotangentScale (-1) p ∈ puncturedCotangent ∧ dualEnergy g hn (cotangentScale (-1) p) = 0 := by
  refine ⟨smul_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) hp, ?_⟩
  rw [dualEnergy_cotangentScale, hnp, mul_zero]

variable [T2Space M]

/-- The base of a maximal genuine nonzero null canonical orbit cannot converge
at its left affine end. -/
theorem maximal_left_no_base_limit (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnp : dualEnergy g hn p = 0)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain) (m : M) :
    ¬ Tendsto (fun t => (A.curve t).1) (leftAffineEndFilter A.domain) (𝓝 m) := by
  intro hlim
  let R := CanonicalTrajectory.timeReverse g hg hn hs A
  obtain ⟨hpun, hnull⟩ := negScale_punctured_null g hn hp hnp
  have hRd : R.domain = -A.domain := timeReverse_domain g hg hn hs A
  have hRmax (D : CanonicalTrajectory g (cotangentScale (-1) p)) : D.domain ⊆ R.domain :=
    timeReverse_domain_maximal g hg hn hs A hmax D
  have htime : Tendsto (fun t : ℝ => -t) (rightAffineEndFilter R.domain) (leftAffineEndFilter A.domain) := by
    rw [hRd]
    exact tendsto_neg_at_affine_ends A.domain ⟨0, A.zero_mem⟩
  have hproj : (fun t => (R.curve t).1) = (fun t => (A.curve t).1) ∘ fun t => -t := by
    funext t
    exact timeReverse_base g hg hn hs A t
  apply maximal_right_no_base_limit g hg hn hs hL R hpun hnull hRmax m
  rw [hproj]
  exact hlim.comp htime

/-- Neither affine end of the same maximal nonzero null orbit has a manifold base limit. -/
theorem maximal_no_base_limit_at_affine_ends (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnp : dualEnergy g hn p = 0)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain) (m : M) :
    (¬ Tendsto (fun t => (A.curve t).1) (leftAffineEndFilter A.domain) (𝓝 m)) ∧
    (¬ Tendsto (fun t => (A.curve t).1) (rightAffineEndFilter A.domain) (𝓝 m)) :=
  ⟨maximal_left_no_base_limit g hg hn hs hL A hp hnp hmax m,
    maximal_right_no_base_limit g hg hn hs hL A hp hnp hmax m⟩

end Burnett.Geometry.CotangentHamiltonTimeReversal

namespace Burnett.Geometry.CotangentHamiltonAffineReparam

open Set Filter
open scoped Topology
open Burnett.Geometry.CotangentHamiltonAffineExtension
open Burnett.Geometry.CotangentHamiltonTimeReversal

private theorem sInf_lt_of_mem_open_interval {I : Set ℝ} (hI : IsOpen I)
    (hb : BddBelow I) {t : ℝ} (ht : t ∈ I) : sInf I < t := by
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds ht)
  have h₁ : (l + t) / 2 < t := by linarith [hlr.1]
  have h₂ : (l + t) / 2 ∈ I := hsub ⟨by linarith [hlr.1], h₁.trans hlr.2⟩
  exact csInf_lt_of_lt hb h₂ h₁

/-- Both affine end filters eventually lie inside the original interval. -/
theorem affineEndFilters_eventually_mem (I : Set ℝ) (hI : IsOpen I)
    (hconn : I.OrdConnected) (hIne : I.Nonempty) :
    (∀ᶠ t in leftAffineEndFilter I, t ∈ I) ∧
      (∀ᶠ t in rightAffineEndFilter I, t ∈ I) := by
  classical
  obtain ⟨a, ha⟩ := hIne
  constructor
  · by_cases hb : BddBelow I
    · rw [leftAffineEndFilter, if_pos hb]
      have ha' := sInf_lt_of_mem_open_interval hI hb ha
      refine mem_of_superset (Ioo_mem_nhdsGT ha') ?_
      intro t ht
      obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt ⟨a, ha⟩ ht.1
      exact hconn.out hs ha ⟨hst.le, ht.2.le⟩
    · rw [leftAffineEndFilter, if_neg hb]
      filter_upwards [eventually_le_atBot a] with t ht
      obtain ⟨s, hs, hst⟩ := not_bddBelow_iff.mp hb t
      exact hconn.out hs ha ⟨hst.le, ht⟩
  · by_cases hb : BddAbove I
    · rw [rightAffineEndFilter, if_pos hb]
      exact open_interval_mem_nhdsLT_sSup hI hconn hb ⟨a, ha⟩
    · rw [rightAffineEndFilter, if_neg hb]
      filter_upwards [eventually_ge_atTop a] with t ht
      obtain ⟨s, hs, hts⟩ := not_bddAbove_iff.mp hb t
      exact hconn.out ha hs ⟨ht, hts.le⟩

private theorem rightAffineEndFilter_eventually_gt {I : Set ℝ} (hI : IsOpen I)
    {s : ℝ} (hs : s ∈ I) : ∀ᶠ t in rightAffineEndFilter I, s < t := by
  classical
  by_cases hb : BddAbove I
  · rw [rightAffineEndFilter, if_pos hb]
    exact mem_of_superset (Ioo_mem_nhdsLT (lt_sSup_of_mem_open_interval hI hb hs))
      Ioo_subset_Ioi_self
  · rw [rightAffineEndFilter, if_neg hb]
    exact eventually_gt_atTop _

private theorem leftAffineEndFilter_eventually_lt {I : Set ℝ} (hI : IsOpen I)
    {s : ℝ} (hs : s ∈ I) : ∀ᶠ t in leftAffineEndFilter I, t < s := by
  classical
  by_cases hb : BddBelow I
  · rw [leftAffineEndFilter, if_pos hb]
    exact mem_of_superset (Ioo_mem_nhdsGT (sInf_lt_of_mem_open_interval hI hb hs))
      Ioo_subset_Iio_self
  · rw [leftAffineEndFilter, if_neg hb]
    exact eventually_lt_atBot _

/-- An increasing reparametrization approaches the supremum of its image
at the right affine end, whenever the image is bounded above. -/
theorem tendsto_monotoneOn_rightAffineEndFilter (I : Set ℝ) (hI : IsOpen I)
    (hconn : I.OrdConnected) (hIne : I.Nonempty) (r : ℝ → ℝ) (hr : MonotoneOn r I)
    (hbound : BddAbove (r '' I)) :
    Tendsto r (rightAffineEndFilter I) (𝓝 (sSup (r '' I))) := by
  have hmem := (affineEndFilters_eventually_mem I hI hconn hIne).2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨_, ⟨s, hs, rfl⟩, hsa⟩ := exists_lt_of_lt_csSup (hIne.image r) ha
    filter_upwards [hmem, rightAffineEndFilter_eventually_gt hI hs] with t ht hst
    exact hsa.trans_le (hr hs ht hst.le)
  · intro a ha
    filter_upwards [hmem] with t ht
    exact (le_csSup hbound ⟨t, ht, rfl⟩).trans_lt ha

/-- An increasing reparametrization approaches the infimum of its image
at the left affine end, whenever the image is bounded below. -/
theorem tendsto_monotoneOn_leftAffineEndFilter (I : Set ℝ) (hI : IsOpen I)
    (hconn : I.OrdConnected) (hIne : I.Nonempty) (r : ℝ → ℝ) (hr : MonotoneOn r I)
    (hbound : BddBelow (r '' I)) :
    Tendsto r (leftAffineEndFilter I) (𝓝 (sInf (r '' I))) := by
  have hmem := (affineEndFilters_eventually_mem I hI hconn hIne).1
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hmem] with t ht
    exact ha.trans_le (csInf_le hbound ⟨t, ht, rfl⟩)
  · intro a ha
    obtain ⟨_, ⟨s, hs, rfl⟩, hsa⟩ := exists_lt_of_csInf_lt (hIne.image r) ha
    filter_upwards [hmem, leftAffineEndFilter_eventually_lt hI hs] with t ht hts
    exact (hr ht hs hts.le).trans_lt hsa

end Burnett.Geometry.CotangentHamiltonAffineReparam

namespace Burnett.Geometry.CotangentHamiltonAffineReparam

open Set Filter
open scoped Topology
open Burnett.Geometry.CotangentHamiltonAffineExtension
open Burnett.Geometry.CotangentHamiltonTimeReversal

variable {X : Type*} [TopologicalSpace X]

/-- A path has a continuous extension after increasing reparametrization if its
reparametrized image interval is properly contained in a larger time interval
and a continuous path on the larger interval agrees with its reparametrization. -/
def HasIncreasingContinuousExtension (γ : ℝ → X) (I : Set ℝ) : Prop :=
  ∃ (J : Set ℝ) (r : ℝ → ℝ) (η : ℝ → X),
    J.OrdConnected ∧ StrictMonoOn r I ∧ ContinuousOn r I ∧
    r '' I ⊂ J ∧ ContinuousOn η J ∧ EqOn γ (η ∘ r) I

/-- A genuine continuous extension after increasing reparametrization gives a
manifold base limit at one of the original path's affine ends. -/
theorem exists_affineEnd_limit_of_increasing_continuous_extension
    (γ : ℝ → X) (I : Set ℝ) (hI : IsOpen I) (hconn : I.OrdConnected)
    (hIne : I.Nonempty) (hext : HasIncreasingContinuousExtension γ I) :
    ∃ x : X, Tendsto γ (leftAffineEndFilter I) (𝓝 x) ∨
      Tendsto γ (rightAffineEndFilter I) (𝓝 x) := by
  obtain ⟨J, r, η, hJ, hrmono, hrcont, hsub, hη, hEq⟩ := hext
  let S := r '' I
  have hSne : S.Nonempty := hIne.image r
  have hSconn : S.OrdConnected :=
    isPreconnected_iff_ordConnected.mp (hconn.isPreconnected.image r hrcont)
  obtain ⟨d, hdJ, hdS⟩ := Set.exists_of_ssubset (show S ⊂ J from hsub)
  have hγLimit {l : Filter ℝ} {a : ℝ} (hIev : ∀ᶠ t in l, t ∈ I)
      (haJ : a ∈ J) (hrlim : Tendsto r l (𝓝 a)) :
      Tendsto γ l (𝓝 (η a)) := by
    have hrwithin : Tendsto r l (𝓝[J] a) := tendsto_nhdsWithin_iff.mpr
      ⟨hrlim, hIev.mono fun t ht => hsub.le ⟨t, ht, rfl⟩⟩
    have hηlim : Tendsto η (𝓝[J] a) (𝓝 (η a)) := hη a haJ
    have he : γ =ᶠ[l] η ∘ r := hIev.mono fun _ ht => hEq ht
    exact (hηlim.comp hrwithin).congr' he.symm
  have hfilters := affineEndFilters_eventually_mem I hI hconn hIne
  by_cases hl : ∃ a ∈ S, a < d
  · obtain ⟨a, haS, had⟩ := hl
    have hupper : ∀ s ∈ S, s ≤ d := by
      intro s hs
      by_contra! hds
      exact hdS (hSconn.out haS hs ⟨had.le, hds.le⟩)
    have hb : BddAbove S := ⟨d, hupper⟩
    have heJ : sSup S ∈ J :=
      hJ.out (hsub.le haS) hdJ ⟨le_csSup hb haS, csSup_le hSne hupper⟩
    have hrLim := tendsto_monotoneOn_rightAffineEndFilter I hI hconn hIne
      r hrmono.monotoneOn hb
    exact ⟨η (sSup S), Or.inr (hγLimit hfilters.2 heJ hrLim)⟩
  · have hlower : ∀ s ∈ S, d ≤ s := by
      intro s hs
      exact le_of_not_gt fun h => hl ⟨s, hs, h⟩
    have hb : BddBelow S := ⟨d, hlower⟩
    obtain ⟨a, haS⟩ := hSne
    have heJ : sInf S ∈ J :=
      hJ.out hdJ (hsub.le haS) ⟨le_csInf ⟨a, haS⟩ hlower, csInf_le hb haS⟩
    have hrLim := tendsto_monotoneOn_leftAffineEndFilter I hI hconn hIne
      r hrmono.monotoneOn hb
    exact ⟨η (sInf S), Or.inl (hγLimit hfilters.1 heJ hrLim)⟩

/-- The absence of base limits at both affine ends is a chart-independent
obstruction to any continuous extension after increasing reparametrization. -/
theorem no_increasing_continuous_extension_of_no_affineEnd_limits
    (γ : ℝ → X) (I : Set ℝ) (hI : IsOpen I) (hconn : I.OrdConnected)
    (hIne : I.Nonempty)
    (hno : ∀ x, (¬ Tendsto γ (leftAffineEndFilter I) (𝓝 x)) ∧
      (¬ Tendsto γ (rightAffineEndFilter I) (𝓝 x))) :
    ¬ HasIncreasingContinuousExtension γ I := by
  intro hExt
  obtain ⟨x, hlim | hlim⟩ := exists_affineEnd_limit_of_increasing_continuous_extension
    γ I hI hconn hIne hExt
  · exact (hno x).1 hlim
  · exact (hno x).2 hlim

end Burnett.Geometry.CotangentHamiltonAffineReparam

namespace Burnett.Geometry.CotangentHamiltonAffineReparam

open Set Filter
open scoped Topology Manifold ContDiff
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.CotangentHamiltonMaximalCurve Burnett.Geometry.CotangentHamiltonTimeReversal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- The projection of an actual maximal nonzero null orbit is inextendible
even among continuous paths after increasing reparametrization. -/
theorem maximal_null_base_no_increasing_continuous_extension (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g) (hL : HasLorentzSignature g)
    {p : CotangentBundle M} (A : CanonicalTrajectory g p)
    (hp : p ∈ puncturedCotangent) (hnp : dualEnergy g hn p = 0)
    (hmax : ∀ D : CanonicalTrajectory g p, D.domain ⊆ A.domain) :
    ¬ HasIncreasingContinuousExtension (fun t => (A.curve t).1) A.domain :=
  no_increasing_continuous_extension_of_no_affineEnd_limits (fun t => (A.curve t).1)
    A.domain A.domain_open A.domain_interval ⟨0, A.zero_mem⟩
    (maximal_no_base_limit_at_affine_ends g hg hn hs hL A hp hnp hmax)

end Burnett.Geometry.CotangentHamiltonAffineReparam
