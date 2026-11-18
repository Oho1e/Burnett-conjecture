import Burnett.Counterexamples.Rosen.Example
import Burnett.Geometry.AuxiliaryConnection
import Burnett.Geometry.CovariantTensorNorm

/-!
# Rosen multiscale example

The covariant derivative in the flat auxiliary metric and its compact-set bounds.
-/

set_option autoImplicit false

noncomputable section

noncomputable section

namespace Burnett.RosenMultiscale

open Set Matrix MeasureTheory Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.CovariantTensorNorm Burnett.Geometry.GramCoordinateBound
open Burnett.Geometry.AuxiliaryConnection
open scoped BigOperators ContDiff Topology Kronecker ENNReal

def rosenEuclideanAuxiliary (_ : CoordinateSpace) :
    LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis (1 : Matrix Index Index ℝ)

theorem rosenEuclideanAuxiliary_eq_inner (x u v : CoordinateSpace) :
    rosenEuclideanAuxiliary x u v = @inner ℝ CoordinateSpace _ u v := by
  have hb (w : CoordinateSpace) (i : Index) : coordinateBasis.repr w i = w i := rfl
  rw [rosenEuclideanAuxiliary, Matrix.toBilin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp [hb, Matrix.one_apply, dotProduct, mul_ite, mul_comm]

theorem rosenEuclideanAuxiliary_components :
    metricComponents rosenEuclideanAuxiliary = fun _ => (1 : Matrix Index Index ℝ) := by
  funext x
  calc
    metricComponents rosenEuclideanAuxiliary x =
        BilinForm.toMatrix coordinateBasis (rosenEuclideanAuxiliary x) := by
      ext a b
      simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, BilinForm.toMatrix_apply]
    _ = _ := BilinForm.toMatrix_toBilin coordinateBasis _

theorem rosenEuclideanAuxiliary_posDef (x : CoordinateSpace) :
    Matrix.PosDef (metricComponents rosenEuclideanAuxiliary x) := by
  rw [rosenEuclideanAuxiliary_components]
  exact Matrix.PosDef.one

theorem rosenEuclideanAuxiliary_connection_zero (x : CoordinateSpace) :
    computedConnection rosenEuclideanAuxiliary x = 0 := by
  have hJ : coordinateJet (fun _ => (1 : Matrix Index Index ℝ)) x = 0 := by
    funext k i j
    simp [coordinateJet]
  unfold computedConnection
  rw [rosenEuclideanAuxiliary_components, hJ]
  funext i j k
  simp [christoffel, koszul]

def rosenBilinearInCoordinates (pulled : Bool) (B ψ : ℝ → ℝ) :
    CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace :=
  if pulled then
    pulledScreenBilinear B (fun u => screenX (B u) (ψ u)) (fun u => screenZ (B u) (ψ u))
  else originalRosenBilinear B ψ

theorem rosenBilinearInCoordinates_components (pulled : Bool) (B ψ : ℝ → ℝ) :
    metricComponents (rosenBilinearInCoordinates pulled B ψ) =
      fun x : CoordinateSpace => rosenMetricInCoordinates pulled B ψ (WithLp.ofLp x) := by
  funext x
  cases pulled
  · exact originalRosenBilinear_components B ψ x
  · exact pulledScreen_specialize B ψ x

theorem rosenCoordinateJet_eq_deriv_update (F : (Fin 4 → ℝ) → Tensor2)
    (x : CoordinateSpace) (k i j : Index)
    (hd : DifferentiableAt ℝ (fun y : CoordinateSpace => F (WithLp.ofLp y) i j) x) :
    coordinateJet (fun y : CoordinateSpace => F (WithLp.ofLp y)) x k i j =
      deriv (fun t => F (Function.update (WithLp.ofLp x) k t) i j) (x k) := by
  let e : CoordinateSpace := EuclideanSpace.single k 1
  let L : ℝ → CoordinateSpace := fun t => x + (t - x k) • e
  have hL : HasDerivAt L e (x k) := by
    simpa only [L, id_eq, one_smul] using
      (((hasDerivAt_id (x k)).sub_const (x k)).smul_const e).const_add x
  have hLx : L (x k) = x := by simp [L]
  have hfun (t : ℝ) : WithLp.ofLp (L t) = Function.update (WithLp.ofLp x) k t := by
    funext m
    change x m + (t - x k) * (EuclideanSpace.single k (1 : ℝ)) m =
      Function.update (WithLp.ofLp x) k t m
    by_cases h : m = k
    · subst m
      simp [EuclideanSpace.single_apply]
    · simp [EuclideanSpace.single_apply, h]
  have heq : (fun t => F (WithLp.ofLp (L t)) i j) =
      fun t => F (Function.update (WithLp.ofLp x) k t) i j := by
    funext t
    rw [hfun t]
  have hFD : HasFDerivAt (fun y : CoordinateSpace => F (WithLp.ofLp y) i j)
      (fderiv ℝ (fun y : CoordinateSpace => F (WithLp.ofLp y) i j) x) (L (x k)) := by
    rw [hLx]
    exact hd.hasFDerivAt
  rw [← heq]
  exact (hFD.comp_hasDerivAt (x k) hL).deriv.symm

theorem rosenEuclidean_norm3_eq_sqrt_sum (T : FirstJet) :
    norm3 (1 : Matrix Index Index ℝ) T = Real.sqrt (∑ i, ∑ j, ∑ k, T i j k ^ 2) := by
  have hGram : gram3 (1 : Matrix Index Index ℝ) = 1 := by
    simp only [gram3, gram2, inv_one, Matrix.one_kronecker_one]
  rw [norm3_eq_gramNorm, hGram]
  simp [gramNorm, gramEnergy, flatten3, dotProduct, Fintype.sum_prod_type, pow_two]

theorem rosenEuclidean_norm3_le_of_entry_bound (T : FirstJet) {C : ℝ}
    (hC : 0 ≤ C) (hT : ∀ i j k, |T i j k| ≤ C) :
    norm3 (1 : Matrix Index Index ℝ) T ≤ 8 * C := by
  have hSum : (∑ i, ∑ j, ∑ k, T i j k ^ 2) ≤ (8 * C)^2 := by
    calc
      _ ≤ ∑ _i : Index, ∑ _j : Index, ∑ _k : Index, C^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        have h := (sq_le_sq₀ (abs_nonneg (T i j k)) hC).mpr (hT i j k)
        simpa only [sq_abs] using h
      _ = _ := by
        norm_num [Index, Finset.sum_const]
        ring
  rw [rosenEuclidean_norm3_eq_sqrt_sum]
  exact (Real.sqrt_le_sqrt hSum).trans_eq (Real.sqrt_sq (by positivity))

def rosenEuclideanDh (pulled : Bool) (B : ℕ → ℝ → ℝ) (n : ℕ)
    (x : CoordinateSpace) : FirstJet :=
  auxiliaryPerturbationJet rosenEuclideanAuxiliary
    (rosenBilinearInCoordinates pulled Real.cos (fun _ => 0))
    (rosenBilinearInCoordinates pulled (B n) (rosenExamplePhase n)) x

private theorem rosen_covariantJet_zero_eq (G : Tensor2) (J : FirstJet) :
    covariantJet 0 G J = J := by
  funext k i j
  simp [covariantJet]

theorem rosenEuclideanDh_eq_coordinateJet (pulled : Bool) (B : ℕ → ℝ → ℝ) (n : ℕ)
    (x : CoordinateSpace) :
    rosenEuclideanDh pulled B n x =
      coordinateJet (fun y : CoordinateSpace =>
        rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n) (WithLp.ofLp y) -
          rosenMetricInCoordinates pulled Real.cos (fun _ => 0) (WithLp.ofLp y)) x := by
  unfold rosenEuclideanDh auxiliaryPerturbationJet
  simp [rosenEuclideanAuxiliary_connection_zero, rosenBilinearInCoordinates_components,
    rosen_covariantJet_zero_eq]

end Burnett.RosenMultiscale

noncomputable section

namespace Burnett.RosenMultiscale

open Set Matrix MeasureTheory Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.BackgroundConnection
open Burnett.Geometry.CovariantTensorNorm Burnett.Geometry.GramCoordinateBound
open Burnett.Geometry.AuxiliaryConnection
open scoped BigOperators ContDiff Topology Kronecker ENNReal

private abbrev rosenForgetLp : CoordinateSpace ≃L[ℝ] (Fin 4 → ℝ) :=
  PiLp.continuousLinearEquiv (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 4 => ℝ)

theorem rosen_limit_components_contDiff (pulled : Bool) (i j : Index) :
    ContDiff ℝ ∞ (fun x : CoordinateSpace =>
      rosenMetricInCoordinates pulled Real.cos (fun _ => 0) (WithLp.ofLp x) i j) := by
  have h := rosenMetricFields_smooth Real.cos (fun _ => 0) (Set.univ : Set ℝ)
    isOpen_univ Real.contDiff_cos.contDiffOn contDiffOn_const
  have hRaw : ContDiff ℝ ∞
      (fun x : Fin 4 → ℝ => rosenMetricInCoordinates pulled Real.cos (fun _ => 0) x i j) := by
    apply contDiffOn_univ.mp
    cases pulled
    · simpa [rosenMetricInCoordinates] using h.1 i j
    · simpa [rosenMetricInCoordinates] using h.2 i j
  exact hRaw.comp rosenForgetLp.contDiff

private theorem rosen_limit_jet_continuous (pulled : Bool) :
    Continuous (coordinateJet (fun x : CoordinateSpace =>
      rosenMetricInCoordinates pulled Real.cos (fun _ => 0) (WithLp.ofLp x))) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((rosen_limit_components_contDiff pulled i j).continuous_fderiv (by simp)).clm_apply
    continuous_const

theorem RosenMultiscaleSequence.euclidean_metric_and_Dh_norm_on_compact
    {B : ℕ → ℝ → ℝ} (h : RosenMultiscaleSequence B) (pulled : Bool)
    {K : Set CoordinateSpace} (hK : IsCompact K)
    (hspace : K ⊆ {x | x 0 ∈ rosenExampleOpenInterval}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : CoordinateSpace), x ∈ K →
      let G := rosenBilinearInCoordinates pulled (B n) (rosenExamplePhase n)
      let r := rosenEuclideanAuxiliary
      norm3 (metricComponents r x)
          (covariantJet (computedConnection r x) (metricComponents G x)
            (coordinateJet (metricComponents G) x)) ≤ C ∧
      norm3 (metricComponents r x) (rosenEuclideanDh pulled B n x) ≤ C := by
  let G : ℕ → CoordinateSpace → Tensor2 := fun n x =>
    rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n) (WithLp.ofLp x)
  let G0 : CoordinateSpace → Tensor2 := fun x =>
    rosenMetricInCoordinates pulled Real.cos (fun _ => 0) (WithLp.ofLp x)
  let imageK : Set (Fin 4 → ℝ) := WithLp.ofLp '' K
  have hImage : IsCompact imageK := hK.image rosenForgetLp.continuous
  have hImageKm : imageK ⊆ {x | x 0 ∈ rosenExampleOpenInterval} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hspace hx
  obtain ⟨C1, hC1, hLine⟩ := (h.on_compact pulled hImage hImageKm).2
  obtain ⟨C0, hC0⟩ := hK.bddAbove_image
    (rosen_limit_jet_continuous pulled).norm.continuousOn
  let C0' := max C0 0
  have hC0' : 0 ≤ C0' := le_max_right _ _
  refine ⟨8 * (C1 + C0'), by positivity, ?_⟩
  intro n x hx
  let U : Set CoordinateSpace := {y | y 0 ∈ rosenExampleOpenInterval}
  have hU : IsOpen U := isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Index)).continuous
  have hGnD (i j : Index) : DifferentiableAt ℝ (fun y => G n y i j) x := by
    have hGnSm : ContDiffOn ℝ ∞ (fun y => G n y i j) U :=
      (h.metricSmooth n pulled i j).comp rosenForgetLp.contDiff.contDiffOn (fun _ hy => hy)
    exact (hGnSm.contDiffAt (hU.mem_nhds (hspace hx))).differentiableAt (by simp)
  have hG0D (i j : Index) : DifferentiableAt ℝ (fun y => G0 y i j) x :=
    (rosen_limit_components_contDiff pulled i j).differentiable (by simp) x
  have hGn (k i j : Index) : |coordinateJet (G n) x k i j| ≤ C1 := by
    obtain ⟨d, hd, hb⟩ := hLine n (WithLp.ofLp x) (mem_image_of_mem _ hx) i j k
    change HasDerivAt _ d (x k) at hd
    have hh := rosenCoordinateJet_eq_deriv_update
      (rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n)) x k i j (hGnD i j)
    change |coordinateJet (fun y => rosenMetricInCoordinates pulled (B n) (rosenExamplePhase n)
      (WithLp.ofLp y)) x k i j| ≤ C1
    rw [hh, hd.deriv]
    exact hb
  have hG0 (k i j : Index) : |coordinateJet G0 x k i j| ≤ C0' := by
    calc
      _ = ‖coordinateJet G0 x k i j‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖coordinateJet G0 x k i‖ := norm_le_pi_norm _ j
      _ ≤ ‖coordinateJet G0 x k‖ := norm_le_pi_norm _ i
      _ ≤ ‖coordinateJet G0 x‖ := norm_le_pi_norm _ k
      _ ≤ C0 := hC0 (mem_image_of_mem _ hx)
      _ ≤ C0' := le_max_left _ _
  have hDiff (k i j : Index) :
      rosenEuclideanDh pulled B n x k i j =
        coordinateJet (G n) x k i j - coordinateJet G0 x k i j := by
    rw [rosenEuclideanDh_eq_coordinateJet]
    change (fderiv ℝ ((fun y => G n y i j) - fun y => G0 y i j) x)
        (EuclideanSpace.single k 1) = _
    rw [fderiv_sub (hGnD i j) (hG0D i j)]
    rfl
  dsimp only
  rw [rosenEuclideanAuxiliary_components, rosenEuclideanAuxiliary_connection_zero,
    rosenBilinearInCoordinates_components, rosen_covariantJet_zero_eq]
  refine ⟨rosenEuclidean_norm3_le_of_entry_bound _ (by positivity) (fun k i j =>
    (hGn k i j).trans (le_add_of_nonneg_right hC0')), ?_⟩
  apply rosenEuclidean_norm3_le_of_entry_bound _ (by positivity)
  intro k i j
  rw [hDiff]
  exact (abs_sub _ _).trans (add_le_add (hGn k i j) (hG0 k i j))

theorem RosenMultiscaleSequence.euclideanDh_norm_on_compact {B : ℕ → ℝ → ℝ}
    (h : RosenMultiscaleSequence B) (pulled : Bool) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hspace : K ⊆ {x | x 0 ∈ rosenExampleOpenInterval}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : CoordinateSpace), x ∈ K →
      norm3 (metricComponents rosenEuclideanAuxiliary x) (rosenEuclideanDh pulled B n x) ≤ C := by
  obtain ⟨C, hC, hBoth⟩ := h.euclidean_metric_and_Dh_norm_on_compact pulled hK hspace
  exact ⟨C, hC, fun n x hx => (hBoth n x hx).2⟩

theorem RosenMultiscaleSequence.euclideanDh_eLpNorm_on_compact {B : ℕ → ℝ → ℝ}
    (h : RosenMultiscaleSequence B) (pulled : Bool) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hspace : K ⊆ {x | x 0 ∈ rosenExampleOpenInterval})
    (μ : Measure CoordinateSpace) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      eLpNorm (fun x =>
        norm3 (metricComponents rosenEuclideanAuxiliary x) (rosenEuclideanDh pulled B n x))
        ⊤ (μ.restrict K) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hPoint⟩ := h.euclideanDh_norm_on_compact pulled hK hspace
  refine ⟨C, hC, fun n => ?_⟩
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
  have hz : 0 ≤ norm3 (metricComponents rosenEuclideanAuxiliary x) (rosenEuclideanDh pulled B n x) :=
    Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hz]
  exact hPoint n x hx

end Burnett.RosenMultiscale
