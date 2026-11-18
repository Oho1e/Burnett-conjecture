import Burnett.Counterexamples.Bianchi.Evolution
import Burnett.Counterexamples.Bianchi.Geometry
import Burnett.Counterexamples.Bianchi.Transport
import Burnett.Counterexamples.Bianchi.RayIdentification
import Burnett.Counterexamples.Bianchi.UnitNormalization

set_option autoImplicit false

noncomputable section

namespace Burnett.Bianchi

open Matrix Set MeasureTheory
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open Burnett.RotatingNullMoments.MeasureModel (UnitPhase)
open scoped ContDiff Matrix.Norms.Elementwise

def rotatingEnergy (γ : ℝ → SpatialMatrix) (t : ℝ) : ℝ :=
  spatialQuadratic ((γ t)⁻¹) (Transport.rotatingP t)

theorem rotatingEnergy_eq_ode (γ : ℝ → SpatialMatrix) (t : ℝ) :
    rotatingEnergy γ t = ODE.inverseEnergy (γ t) (ODE.direction t) := by
  change spatialQuadratic ((γ t)⁻¹) (Transport.rotatingP t) = _
  rw [← Transport.directionSquare_eq_spatialQuadratic]
  change Transport.spatialValue ((γ t)⁻¹) (Transport.rotatingP t) = _
  rfl

theorem rotatingEnergy_pos (γ : ℝ → SpatialMatrix) (t : ℝ) (hγ : (γ t).PosDef) :
    0 < rotatingEnergy γ t := by
  rw [rotatingEnergy_eq_ode]
  exact ODE.inverseEnergy_pos hγ (ODE.direction_ne_zero t)

theorem symm_entries {C : SpatialMatrix} (hC : C.IsSymm) (i j : Spatial) : C i j = C j i := by
  have hCt : C.transpose = C := hC
  exact (congrArg (fun D : SpatialMatrix ↦ D i j) hCt).symm

theorem positive_symm_entries {C : SpatialMatrix} (hC : C.PosDef)
    (i j : Spatial) : C i j = C j i := by
  have hc : C.conjTranspose = C := hC.1
  have ht : C.transpose = C := by simpa [Matrix.conjTranspose, Matrix.transpose] using hc
  exact symm_entries ht i j

theorem isUnit_of_posDef {C : SpatialMatrix} (hC : C.PosDef) : IsUnit C :=
  (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC.det_pos.ne')

/-- The genuine coordinate Ricci tensor directly from the single ODE witness. -/
theorem computedRicci_of_constrained_flow (I : Set ℝ) (hI : IsOpen I)
    (γ A : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (hγP : ∀ t ∈ I, (γ t).PosDef) (hAS : ∀ t ∈ I, (A t).IsSymm)
    (hγ' : ∀ t ∈ I, HasDerivAt γ ((2 : ℝ) • A t) t)
    (hA' : ∀ t ∈ I, HasDerivAt A (ODE.rateA (γ t) (A t) (ρ t) (ODE.direction t)) t)
    (hK' : ∀ t ∈ I, HasDerivAt (fun s ↦ ODE.K (γ s) (A s))
      (ρ t • ODE.W (γ t) (ODE.direction t) -
        (ODE.K (γ t) (A t)).trace • ODE.K (γ t) (A t)) t)
    (hθ' : ∀ t ∈ I, HasDerivAt (fun s ↦ (ODE.K (γ s) (A s)).trace)
      (ρ t - (ODE.K (γ t) (A t)).trace ^ 2) t)
    (hC : ∀ t ∈ I, (ODE.K (γ t) (A t)).trace ^ 2 -
      ((ODE.K (γ t) (A t)) * (ODE.K (γ t) (A t))).trace = 2 * ρ t)
    (x : CoordinateSpace) (hx : x 0 ∈ I) :
    coordinateRicci (computedConnection (metric γ)) x =
      sourceTensor (ρ (x 0)) (rotatingEnergy γ (x 0)) (Transport.rotatingP (x 0)) := by
  let K : ℝ → SpatialMatrix := fun t ↦ ODE.K (γ t) (A t)
  let t := x 0
  let Ad := ODE.rateA (γ t) (A t) (ρ t) (ODE.direction t)
  let Kd := ρ t • ODE.W (γ t) (ODE.direction t) - (K t).trace • K t
  have had : ∀ i j, HasDerivAt (fun s ↦ A s i j) (Ad i j) t :=
    fun i j ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp (hA' t hx) i) j
  have hkd : ∀ i j, HasDerivAt (fun s ↦ K s i j) (Kd i j) t :=
    fun i j ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp (hK' t hx) i) j
  have htheta : Kd.trace = ρ t - (K t).trace ^ 2 :=
    (ODE.hasDerivAt_trace_matrix (hK' t hx)).deriv.symm.trans (hθ' t hx).deriv
  have hG' (s : ℝ) (hs : s ∈ I) (i j : Spatial) :
      HasDerivAt (fun a ↦ γ a i j) (2 * A s i j) s := by
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp (hγ' s hs) i) j
  have hadEq : Ad = (2 : ℝ) • (A t * K t) - (K t).trace • A t +
      (ρ t / rotatingEnergy γ t : ℝ) • rankOne (Transport.rotatingP t) := by
    simp only [Ad, ODE.rateA, rotatingEnergy_eq_ode, K, ODE.K, Matrix.mul_assoc]
    rfl
  have hconstraint : (K t).trace ^ 2 - (K t * K t).trace - 2 * ρ t = 0 :=
    sub_eq_zero.mpr (hC t hx)
  exact computedRicci_eq_source I hI γ A K x hx
    (fun s hs ↦ isUnit_of_posDef (hγP s hs)) (positive_symm_entries (hγP t hx))
    (fun s hs ↦ symm_entries (hAS s hs)) hG' (fun _ _ ↦ rfl)
    Ad Kd had hkd _ _ _ hadEq htheta hconstraint

def HasCoordinateNullRayRepresentation (τ : ℝ) (γ : ℝ → SpatialMatrix)
    (G : CoordinateSpace → Tensor2) : Prop :=
  ∃ μ : Measure (UnitPhase (Transport.domain τ)),
    IsLocallyFiniteMeasure μ ∧
    (∀ᵐ p ∂μ, Transport.metricHamiltonian γ p.val.1 p.val.2 = 0) ∧
    Transport.HasTensorMoments τ ((Burnett.Geometry.LorentzVolume.coordinateMeasure
      (metricComponents (metric γ))).restrict (Transport.baseDomain τ)) G μ ∧
    (∀ a : CoordinateSpace → Covector → ℝ, Transport.IsTransportTest τ a →
      ∫ p, Transport.metricHamiltonTransport γ a p.val.1 p.val.2 ∂μ = 0)

/-- The Einstein source and the transport obstruction hold for the same local metric. -/
theorem exists_coordinate_bianchi_counterexample {H : ℝ} (hH : 0 < H) :
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi / 4 ∧ ∃ (γ : ℝ → SpatialMatrix) (ρ : ℝ → ℝ),
      ContDiffOn ℝ ∞ γ (Transport.domain τ) ∧
      ContDiffOn ℝ ∞ ρ (Transport.domain τ) ∧
      (∀ t ∈ Transport.domain τ, (γ t).PosDef ∧ 0 < ρ t) ∧
      (∀ x ∈ Transport.baseDomain τ, coordinateScalar γ x = 0 ∧
        coordinateEinstein γ x = sourceTensor (ρ (x 0)) (rotatingEnergy γ (x 0))
          (Transport.rotatingP (x 0))) ∧
      ¬ HasCoordinateNullRayRepresentation τ γ (coordinateEinstein γ) := by
  obtain ⟨τ, hτ, hτ', γ, A, ρ, _, _, _, hγ, _, hρ, hSys⟩ :=
    ODE.exists_bianchi_constrained_flow hH
  have hγP (t : ℝ) (ht : t ∈ Transport.domain τ) := (hSys t ht).1
  have hρP (t : ℝ) (ht : t ∈ Transport.domain τ) := (hSys t ht).2.2.1
  have hRicci (x : CoordinateSpace) (hx : x ∈ Transport.baseDomain τ) :=
    computedRicci_of_constrained_flow (Transport.domain τ) isOpen_Ioo γ A ρ hγP
      (fun t ht ↦ (hSys t ht).2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.2.2.2.2) x hx
  have hE (x : CoordinateSpace) (hx : x ∈ Transport.baseDomain τ) :
      coordinateScalar γ x = 0 ∧ coordinateEinstein γ x =
        sourceTensor (ρ (x 0)) (rotatingEnergy γ (x 0)) (Transport.rotatingP (x 0)) :=
    coordinateEinstein_eq_source_of_Ricci γ x (isUnit_of_posDef (hγP _ hx)) _ _ _
      (rotatingEnergy_pos γ _ (hγP _ hx)) rfl (hRicci x hx)
  refine ⟨τ, hτ, hτ', γ, ρ, hγ, hρ, fun t ht ↦ ⟨hγP t ht, hρP t ht⟩, hE, ?_⟩
  exact Transport.no_representation_for_coordinate_metric τ hτ hτ' γ ρ hγ hγP
    hρ.continuousOn hρP _ (fun x hx ↦ (hE x hx).2)

end Burnett.Bianchi

namespace Burnett.Bianchi

open Matrix Filter Set
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.InverseField
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

/-- The contraction g^{ad} (∇_d T)_{ab} in a genuine coordinate chart. -/
def contractedCovariantJet (gInv T : Tensor2) (Γ : Connection) (D : FirstJet)
    (b : Index) : ℝ :=
  ∑ a, ∑ d, gInv a d * covariantJet Γ T D d a b

theorem contractedCovariantJet_time (B A K L : SpatialMatrix) (ρ ρdot : ℝ) (D : FirstJet)
    (h0 : D 0 0 0 = ρdot) (hs : ∀ j a b, D (Fin.succ j) a b = 0) :
    contractedCovariantJet (block (-1) B) (block ρ L) (connection A K) D 0 =
      -ρdot + ∑ i : Spatial, ∑ j : Spatial,
        B i j * (-(A j i * ρ) - ∑ k : Spatial, K k j * L i k) := by
  simp only [contractedCovariantJet, covariantJet, Fin.sum_univ_succ (n := 3),
    block_time_time, block_space_time, block_time_space, block_space_space,
    connection_000, connection_00s, connection_0s0, connection_0ss, connection_s00,
    connection_ss0, h0, hs, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, sub_zero, zero_sub, neg_one_mul]

theorem contractedCovariantJet_space (B A K L : SpatialMatrix) (ρ : ℝ) (D : FirstJet)
    (h0 : ∀ b : Spatial, D 0 0 b.succ = 0) (hs : ∀ j a b, D (Fin.succ j) a b = 0)
    (b : Spatial) :
    contractedCovariantJet (block (-1) B) (block ρ L) (connection A K) D b.succ = 0 := by
  simp only [contractedCovariantJet, covariantJet, Fin.sum_univ_succ (n := 3),
    block_time_time, block_space_time, block_time_space, block_space_space,
    connection_00s, connection_0ss, connection_s00,
    connection_s0s, connection_ss0, connection_sss, h0, hs, mul_zero, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, sub_zero]

theorem trace_rotating_source_term (B K : SpatialMatrix) (hB : ∀ i j, B i j = B j i)
    (ρ d : ℝ) (p : Spatial → ℝ) :
    (∑ i : Spatial, ∑ j : Spatial,
      B i j * (∑ k : Spatial, K k j * (((ρ / d : ℝ) • rankOne p) i k))) =
        ρ * Matrix.trace (K * (d⁻¹ • (B * rankOne p))) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.smul_apply,
    smul_eq_mul, rankOne, Fin.sum_univ_three, div_eq_mul_inv]
  rw [hB 0 1, hB 0 2, hB 1 2]
  ring

theorem contracted_source_zero (B A : SpatialMatrix) (hB : ∀ i j, B i j = B j i)
    (ρ d : ℝ) (p : Spatial → ℝ) (D : FirstJet)
    (h0 : D 0 0 0 = -ρ * ((B * A).trace +
      ((B * A) * (d⁻¹ • (B * rankOne p))).trace))
    (hTimeSpace : ∀ b : Spatial, D 0 0 b.succ = 0)
    (hspatial : ∀ j a b, D (Fin.succ j) a b = 0) (b : Index) :
    contractedCovariantJet (block (-1) B) (sourceTensor ρ d p) (connection A (B * A)) D b = 0 := by
  refine Fin.cases ?_ (fun j ↦ ?_) b
  · rw [sourceTensor, contractedCovariantJet_time _ _ _ _ _ _ _ h0 hspatial]
    have hsum : (∑ i : Spatial, ∑ j : Spatial, B i j * (A j i * ρ)) =
        (B * A).trace * ρ := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, mul_assoc]
    simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [hsum, trace_rotating_source_term B _ hB]
    ring
  · exact contractedCovariantJet_space _ _ _ _ _ _ hTimeSpace hspatial j

private theorem time_coordinate_add_spatial (x : CoordinateSpace) (d : Spatial) (s : ℝ) :
    (x + s • EuclideanSpace.single d.succ 1 : CoordinateSpace) 0 = x 0 := by
  simp [EuclideanSpace.single_apply, Ne.symm (Fin.succ_ne_zero d)]

theorem coordinateJet_time_dependent_spatial (T : ℝ → Tensor2)
    (x : CoordinateSpace) (d : Spatial) (a b : Index) :
    coordinateJet (fun y ↦ T (y 0)) x d.succ a b = 0 := by
  let F : CoordinateSpace → ℝ := fun y ↦ T (y 0) a b
  change fderiv ℝ F x (EuclideanSpace.single d.succ 1) = 0
  by_cases hf : DifferentiableAt ℝ F x
  · let v : CoordinateSpace := EuclideanSpace.single d.succ 1
    have hline : HasDerivAt (fun s : ℝ ↦ x + s • v) v 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x |>.congr_deriv (one_smul ℝ v)
    have hxf : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • v) := by
      simpa using hf.hasFDerivAt
    have hcomp := hxf.comp_hasDerivAt 0 hline
    change HasDerivAt (fun s : ℝ ↦ F (x + s • v)) (fderiv ℝ F x v) 0 at hcomp
    have hconst : (fun s : ℝ ↦ F (x + s • v)) = fun _ ↦ F x := by
      funext s
      exact congrArg (fun a0 : ℝ ↦ T a0 a b) (time_coordinate_add_spatial x d s)
    rw [hconst] at hcomp
    exact hcomp.deriv.symm.trans (hasDerivAt_const 0 (F x)).deriv
  · simp [fderiv_zero_of_not_differentiableAt hf]

def tensorDivergence (g : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (T : CoordinateSpace → Tensor2) (x : CoordinateSpace) (b : Index) : ℝ :=
  contractedCovariantJet (matrixInverse (metricComponents g x)) (T x)
    (computedConnection g x) (coordinateJet T x) b

theorem coordinate_source_divergence_zero (I : Set ℝ)
    (γ A : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (hγP : ∀ t ∈ I, (γ t).PosDef) (hAS : ∀ t ∈ I, (A t).IsSymm)
    (hγ' : ∀ t ∈ I, HasDerivAt γ ((2 : ℝ) • A t) t)
    (hρ' : ∀ t ∈ I, HasDerivAt ρ (ODE.rateRho (γ t) (A t) (ρ t) (ODE.direction t)) t)
    (x : CoordinateSpace) (hx : x 0 ∈ I) (b : Index) :
    tensorDivergence (metric γ)
      (fun y ↦ sourceTensor (ρ (y 0)) (rotatingEnergy γ (y 0)) (Transport.rotatingP (y 0)))
      x b = 0 := by
  let S : ℝ → Tensor2 := fun t ↦ sourceTensor (ρ t) (rotatingEnergy γ t) (Transport.rotatingP t)
  let t := x 0
  let B := (γ t)⁻¹
  let p := Transport.rotatingP t
  have hΓ := computedConnection_metric γ (A t) x (isUnit_of_posDef (hγP t hx))
    (symm_entries (hAS t hx)) (fun i j ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp (hγ' t hx) i) j)
  have hB := inverse_symmetric (γ t) (positive_symm_entries (hγP t hx))
  have hD0 : coordinateJet (fun y ↦ S (y 0)) x 0 0 0 = ODE.rateRho (γ t) (A t) (ρ t) p := by
    change fderiv ℝ (fun y : CoordinateSpace ↦ ρ (y 0)) x (EuclideanSpace.single 0 1) = _
    have h := (hρ' t hx).hasFDerivAt.comp x (EuclideanSpace.proj (𝕜 := ℝ) (0 : Index)).hasFDerivAt
    change fderiv ℝ (ρ ∘ (EuclideanSpace.proj (𝕜 := ℝ) (0 : Index))) x _ = _
    rw [h.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      EuclideanSpace.single_apply, p, Transport.rotatingP, ODE.direction]
  have hTimeSpace (j : Spatial) : coordinateJet (fun y ↦ S (y 0)) x 0 0 j.succ = 0 := by
    change fderiv ℝ (fun _ : CoordinateSpace ↦ (0 : ℝ)) x (EuclideanSpace.single 0 1) = 0
    simp
  change contractedCovariantJet (matrixInverse (metricComponents (metric γ) x)) (S t)
    (computedConnection (metric γ) x) (coordinateJet (fun y ↦ S (y 0)) x) b = 0
  rw [hΓ, metric_components, matrixInverse_block _ (isUnit_of_posDef (hγP t hx))]
  apply contracted_source_zero B (A t) hB (ρ t) (rotatingEnergy γ t) p _ _ hTimeSpace
    (coordinateJet_time_dependent_spatial S x) b
  rw [hD0, rotatingEnergy_eq_ode]
  rfl

theorem coordinateEinstein_divergence_zero_of_germ (I : Set ℝ) (hI : IsOpen I)
    (γ A : ℝ → SpatialMatrix) (ρ : ℝ → ℝ)
    (hγP : ∀ t ∈ I, (γ t).PosDef) (hAS : ∀ t ∈ I, (A t).IsSymm)
    (hγ' : ∀ t ∈ I, HasDerivAt γ ((2 : ℝ) • A t) t)
    (hρ' : ∀ t ∈ I, HasDerivAt ρ (ODE.rateRho (γ t) (A t) (ρ t) (ODE.direction t)) t)
    (hE : ∀ y : CoordinateSpace, y 0 ∈ I →
      coordinateEinstein γ y = sourceTensor (ρ (y 0)) (rotatingEnergy γ (y 0)) (Transport.rotatingP (y 0)))
    (x : CoordinateSpace) (hx : x 0 ∈ I) (b : Index) :
    tensorDivergence (metric γ) (coordinateEinstein γ) x b = 0 := by
  let S : CoordinateSpace → Tensor2 := fun y ↦
    sourceTensor (ρ (y 0)) (rotatingEnergy γ (y 0)) (Transport.rotatingP (y 0))
  have hor : IsOpen {y : CoordinateSpace | y 0 ∈ I} :=
    hI.preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Index)).continuous
  have heq : (coordinateEinstein γ : CoordinateSpace → Tensor2) =ᶠ[𝓝 x] S :=
    Filter.eventually_of_mem (hor.mem_nhds hx) hE
  unfold tensorDivergence
  rw [heq.self_of_nhds, coordinateJet_congr _ _ x heq]
  exact coordinate_source_divergence_zero I γ A ρ hγP hAS hγ' hρ' x hx b

end Burnett.Bianchi

namespace Burnett.Bianchi

open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

private theorem update_slot_one {E : Type*} (X V U Y : E) :
    Function.update (![X,V,U] : Fin 3 → E) 1 Y = ![X,Y,U] := by
  funext i
  fin_cases i <;> simp

private theorem update_slot_two {E : Type*} (X V U Y : E) :
    Function.update (![X,V,U] : Fin 3 → E) 2 Y = ![X,V,Y] := by
  funext i
  fin_cases i <;> simp

private theorem curvatureEnd_add_left (B : Field (M := M)) (m : M)
    (U U' V : TangentSpace Model m) :
    IntrinsicRicciTrace.curvatureEnd B m (U + U') V =
      IntrinsicRicciTrace.curvatureEnd B m U V + IntrinsicRicciTrace.curvatureEnd B m U' V := by
  ext X
  simp only [IntrinsicRicciTrace.curvatureEnd_apply, LinearMap.add_apply]
  simpa only [update_slot_two] using
    (CurvatureFiberTensor.tensor B m).map_update_add ![X,V,U] 2 U U'

private theorem curvatureEnd_add_right (B : Field (M := M)) (m : M)
    (U V V' : TangentSpace Model m) :
    IntrinsicRicciTrace.curvatureEnd B m U (V + V') =
      IntrinsicRicciTrace.curvatureEnd B m U V + IntrinsicRicciTrace.curvatureEnd B m U V' := by
  ext X
  simp only [IntrinsicRicciTrace.curvatureEnd_apply, LinearMap.add_apply]
  simpa only [update_slot_one] using
    (CurvatureFiberTensor.tensor B m).map_update_add ![X,V,U] 1 V V'

private theorem curvatureEnd_smul_left (B : Field (M := M)) (m : M)
    (r : ℝ) (U V : TangentSpace Model m) :
    IntrinsicRicciTrace.curvatureEnd B m (r • U) V = r • IntrinsicRicciTrace.curvatureEnd B m U V := by
  ext X
  simp only [IntrinsicRicciTrace.curvatureEnd_apply, LinearMap.smul_apply]
  simpa only [update_slot_two] using
    (CurvatureFiberTensor.tensor B m).map_update_smul ![X,V,U] 2 r U

private theorem curvatureEnd_smul_right (B : Field (M := M)) (m : M)
    (r : ℝ) (U V : TangentSpace Model m) :
    IntrinsicRicciTrace.curvatureEnd B m U (r • V) = r • IntrinsicRicciTrace.curvatureEnd B m U V := by
  ext X
  simp only [IntrinsicRicciTrace.curvatureEnd_apply, LinearMap.smul_apply]
  simpa only [update_slot_one] using
    (CurvatureFiberTensor.tensor B m).map_update_smul ![X,V,U] 1 r V

/-- The trace of actual intrinsic curvature as a fiberwise bilinear form. -/
def intrinsicRicciForm (B : Field (M := M)) (m : M) : LinearMap.BilinForm ℝ (TangentSpace Model m) :=
  LinearMap.mk₂ ℝ (IntrinsicRicciTrace.ricci B m)
    (fun U U' V ↦ by simp only [IntrinsicRicciTrace.ricci, curvatureEnd_add_left, map_add])
    (fun r U V ↦ by simp only [IntrinsicRicciTrace.ricci, curvatureEnd_smul_left, map_smul])
    (fun U V V' ↦ by simp only [IntrinsicRicciTrace.ricci, curvatureEnd_add_right, map_add])
    (fun r U V ↦ by simp only [IntrinsicRicciTrace.ricci, curvatureEnd_smul_right, map_smul])

/-- Bundle the evaluation of the same genuine Einstein tensor. -/
def intrinsicEinsteinForm (B : Field (M := M)) (m : M) : LinearMap.BilinForm ℝ (TangentSpace Model m) :=
  intrinsicRicciForm B m - (intrinsicScalar B m / 2) •
    LinearMap.mk₂ ℝ (fun U V ↦ B m U V)
      (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])

@[simp] theorem intrinsicEinsteinForm_apply (B : Field (M := M)) (m : M)
    (U V : TangentSpace Model m) :
    intrinsicEinsteinForm B m U V = intrinsicEinstein B m U V := by
  rfl

theorem intrinsicEinstein_on_frame (B : Field (M := M)) (m : M) (u v : CoordinateSpace) :
    intrinsicEinstein B m (tangentFrame m m u) (tangentFrame m m v) =
      Matrix.toBilin coordinateBasis (intrinsicEinsteinMatrix B m) u v := by
  let F := tangentFrame m m
  let E : LinearMap.BilinForm ℝ CoordinateSpace :=
    (intrinsicEinsteinForm B m).comp F.toLinearMap F.toLinearMap
  have hM : BilinForm.toMatrix coordinateBasis E = intrinsicEinsteinMatrix B m := by
    ext i j
    rw [BilinForm.toMatrix_apply]
    simp only [E, LinearMap.BilinForm.comp_apply, F, ContinuousLinearMap.coe_coe,
      intrinsicEinsteinForm_apply, intrinsicEinsteinMatrix, coordinateBasis,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have hE : Matrix.toBilin coordinateBasis (intrinsicEinsteinMatrix B m) = E := by
    rw [← hM, ← Matrix.toBilin_symm, LinearEquiv.apply_symm_apply]
  rw [hE]
  exact (intrinsicEinsteinForm_apply B m _ _).symm

theorem intrinsicEinstein_from_matrix (B : Field (M := M)) (m : M)
    (U V : TangentSpace Model m) :
    intrinsicEinstein B m U V =
      Matrix.toBilin coordinateBasis (intrinsicEinsteinMatrix B m)
        (mfderiv Model Model (chartAt CoordinateSpace m) m U)
        (mfderiv Model Model (chartAt CoordinateSpace m) m V) := by
  have hm := mem_chart_source CoordinateSpace m
  obtain ⟨u, rfl⟩ := tangentFrame_surjective m m hm U
  obtain ⟨v, rfl⟩ := tangentFrame_surjective m m hm V
  rw [IntrinsicRicciTrace.forward_tangentFrame _ _ hm, IntrinsicRicciTrace.forward_tangentFrame _ _ hm]
  exact intrinsicEinstein_on_frame B m _ _

end Burnett.Bianchi

namespace Burnett.Bianchi

open Matrix Set Bundle
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.InverseField (matrixInverse)
open Burnett.Geometry.UnitNullCompactness (CotangentBundle CotangentModel covectorCLM
  covectorCLM_apply_basis cotangentCoords cotangentTrivialization_apply dualEnergy dualEnergy_chart)
open scoped BigOperators ContDiff Manifold Topology Matrix.Norms.Elementwise

theorem covectorCLM_apply (ξ : Covector) (u : CoordinateSpace) :
    covectorCLM ξ u = ∑ i : Index, ξ i * u i := by
  simp only [covectorCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rfl

private theorem slab_cotangentCoords (I : Set ℝ) (hI : IsOpen I)
    (m : spacetime I hI) (ξ : Covector) :
    cotangentCoords m (TotalSpace.mk' CotangentModel m (covectorCLM ξ)) = ξ := by
  funext i
  rw [cotangentCoords, cotangentTrivialization_apply]
  change covectorCLM ξ (tangentFrame m m (coordinateBasis i)) = ξ i
  rw [spacetime_tangentFrame, covectorCLM_apply_basis]

private theorem slab_derivative_chart (I : Set ℝ) (hI : IsOpen I)
    (m : spacetime I hI) (u : TangentSpace Model m) :
    mfderiv Model Model (chartAt CoordinateSpace m) m u = u := by
  have hm := mem_chart_source CoordinateSpace m
  calc
    mfderiv Model Model (chartAt CoordinateSpace m) m u =
        mfderiv Model Model (chartAt CoordinateSpace m) m (tangentFrame m m u) := by
      rw [spacetime_tangentFrame]
    _ = u := IntrinsicRicciTrace.forward_tangentFrame m m hm u

def HasTwoPositiveNullSquares {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold Model ∞ M] (B : Field (M := M)) (hND : IsNondegenerate B) (m : M) : Prop :=
  ∃ (weight : ℝ) (ξ₁ ξ₂ : TangentSpace Model m →L[ℝ] ℝ),
    0 < weight ∧ ξ₁ ≠ 0 ∧ ξ₂ ≠ 0 ∧
    dualEnergy B hND (TotalSpace.mk' CotangentModel m ξ₁) = 0 ∧
    dualEnergy B hND (TotalSpace.mk' CotangentModel m ξ₂) = 0 ∧
    ∀ u v : TangentSpace Model m, intrinsicEinstein B m u v =
      weight * (ξ₁ u * ξ₁ v + ξ₂ u * ξ₂ v)

theorem twoPositiveNullSquares_of_source (I : Set ℝ) (hI : IsOpen I)
    (c m : spacetime I hI) (γ : ℝ → SpatialMatrix) (hG : ∀ t ∈ I, (γ t).PosDef)
    (ρ d : ℝ) (p : Spatial → ℝ) (hρ : 0 < ρ) (hd : 0 < d)
    (hdEq : d = spatialQuadratic ((γ ((m : CoordinateSpace) 0))⁻¹) p)
    (hE : intrinsicEinsteinMatrix (openMetric I hI c γ) m = sourceTensor ρ d p) :
    HasTwoPositiveNullSquares (openMetric I hI c γ) (openMetric_isNondegenerate I hI c γ hG) m := by
  let B := openMetric I hI c γ
  let hND := openMetric_isNondegenerate I hI c γ hG
  let s₁ := nullCovector d p 1
  let s₂ := nullCovector d p (-1)
  have hneq (s : ℝ) : covectorCLM (nullCovector d p s) ≠ 0 := by
    intro h
    have hh := congrArg (fun f : CotangentModel ↦ f (coordinateBasis 0)) h
    change covectorCLM (nullCovector d p s) (coordinateBasis 0) = 0 at hh
    rw [covectorCLM_apply_basis] at hh
    change -Real.sqrt d = 0 at hh
    linarith [Real.sqrt_pos.mpr hd]
  have hn (s : ℝ) (hs : s^2 = 1) :
      dualEnergy B hND (TotalSpace.mk' CotangentModel m (covectorCLM (nullCovector d p s))) = 0 := by
    have hm := mem_chart_source CoordinateSpace m
    rw [dualEnergy_chart B hND (openMetric_isSymmetric I hI c γ hG) m _ hm, slab_cotangentCoords]
    have hc := (openMetric_coordinate_germ_at I hI c m γ).self_of_nhds
    change symbolNorm (matrixInverse (FiberMetric.covariant
      (coordinateBilinear B m (chartAt CoordinateSpace m m)) coordinateBasis))
        (nullCovector d p s) = 0
    change coordinateBilinear B m (chartAt CoordinateSpace m m) = _ at hc
    rw [hc, spacetime_chart_apply]
    change symbolNorm (matrixInverse (metricComponents (metric γ) m)) (nullCovector d p s) = 0
    rw [metric_components, matrixInverse_block _ (isUnit_of_posDef (hG _ m.property))]
    exact nullCovector_null _ p d s hd hdEq hs
  refine ⟨ρ / (2 * d), covectorCLM s₁, covectorCLM s₂, div_pos hρ (mul_pos (by norm_num) hd),
    hneq _, hneq _, hn 1 (by norm_num), hn (-1) (by norm_num), ?_⟩
  intro u v
  rw [intrinsicEinstein_from_matrix, hE, slab_derivative_chart, slab_derivative_chart,
    source_null_squares ρ d p hd]
  let U : CoordinateSpace := u
  let V : CoordinateSpace := v
  let w : ℝ := ρ / (2 * d)
  rw [Matrix.toBilin_apply]
  change (∑ i : Index, ∑ j : Index,
    U i * (w * (s₁ i * s₁ j + s₂ i * s₂ j)) * V j) =
      w * (covectorCLM s₁ U * covectorCLM s₁ V + covectorCLM s₂ U * covectorCLM s₂ V)
  have hpair (s : Covector) :
      (∑ i : Index, ∑ j : Index, U i * (w * (s i * s j)) * V j) =
        w * (covectorCLM s U * covectorCLM s V) := by
    rw [covectorCLM_apply, covectorCLM_apply]
    conv_rhs =>
      rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_add, add_mul, Finset.sum_add_distrib, hpair]

theorem positiveSemidefinite_of_positiveNullSquares {M : Type*}
    [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
    {B : Field (M := M)} {hND : IsNondegenerate B} {m : M}
    (h : HasTwoPositiveNullSquares B hND m) (u : TangentSpace Model m) :
    0 ≤ intrinsicEinstein B m u u := by
  obtain ⟨c, ξ, ζ, hc, _, _, _, _, hE⟩ := h
  rw [hE]
  exact mul_nonneg hc.le (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

end Burnett.Bianchi

namespace Burnett.Bianchi

open Matrix Set Filter
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.BackgroundConnection Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.InverseField (matrixInverse)
open scoped BigOperators ContDiff Manifold Topology Matrix.Norms.Elementwise

def intrinsicEinsteinTrace {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold Model ∞ M] (B : Field (M := M)) (m : M) : ℝ :=
  traceWith (matrixInverse (metricComponents (coordinateBilinear B m) (chartAt CoordinateSpace m m)))
    (intrinsicEinsteinMatrix B m)

theorem intrinsicEinsteinTrace_openMetric_source (I : Set ℝ) (hI : IsOpen I)
    (c m : spacetime I hI) (γ : ℝ → SpatialMatrix) (hG : (γ ((m : CoordinateSpace) 0)).PosDef)
    (ρ d : ℝ) (p : Spatial → ℝ) (hd : 0 < d) (hdEq : d = spatialQuadratic ((γ ((m : CoordinateSpace) 0))⁻¹) p)
    (hE : intrinsicEinsteinMatrix (openMetric I hI c γ) m = sourceTensor ρ d p) :
    intrinsicEinsteinTrace (openMetric I hI c γ) m = 0 := by
  have hc := (openMetric_coordinate_germ_at I hI c m γ).self_of_nhds
  change coordinateBilinear (openMetric I hI c γ) m (chartAt CoordinateSpace m m) = _ at hc
  unfold intrinsicEinsteinTrace
  simp only [metricComponents]
  rw [hc, spacetime_chart_apply]
  change traceWith (matrixInverse (metricComponents (metric γ) m))
    (intrinsicEinsteinMatrix (openMetric I hI c γ) m) = 0
  rw [metric_components, matrixInverse_block _ (isUnit_of_posDef hG), hE]
  exact source_trace_zero _ ρ d p hd hdEq

/-- Construct the actual metric and its source on the same product as the coordinate obstruction. -/
theorem exists_bianchi_openMetric_with_coordinate_obstruction {H : ℝ} (hH : 0 < H) :
    ∃ (τ : ℝ), 0 < τ ∧ τ < Real.pi / 4 ∧
      ∃ (c : spacetime (Transport.domain τ) isOpen_Ioo) (γ : ℝ → SpatialMatrix) (ρ : ℝ → ℝ),
        let B := openMetric (Transport.domain τ) isOpen_Ioo c γ
        IsSmooth B ∧ IsSymmetric B ∧
        ∃ hND : IsNondegenerate B,
          (∀ m, FieldHasLorentzSignature B m ∧ intrinsicEinsteinTrace B m = 0 ∧
            HasTwoPositiveNullSquares B hND m ∧
            (∀ u : TangentSpace Model m, 0 ≤ intrinsicEinstein B m u u) ∧
            intrinsicEinsteinMatrix B m = coordinateEinstein γ (m : CoordinateSpace)) ∧
          (∀ x ∈ Transport.baseDomain τ, ∀ b : Index,
            tensorDivergence (metric γ) (coordinateEinstein γ) x b = 0) ∧
          (∀ t ∈ Transport.domain τ, (γ t).PosDef ∧ 0 < ρ t) ∧
          ¬ HasCoordinateNullRayRepresentation τ γ (coordinateEinstein γ) := by
  obtain ⟨τ, hτ, hτ', γ, A, ρ, _, _, _, hγ, _, hρ, hSys⟩ :=
    ODE.exists_bianchi_constrained_flow hH
  let I := Transport.domain τ
  have hI : IsOpen I := isOpen_Ioo
  let c : spacetime I hI := ⟨0, ⟨neg_neg_of_pos hτ, hτ⟩⟩
  have hG (t : ℝ) (ht : t ∈ I) := (hSys t ht).1
  have hρP (t : ℝ) (ht : t ∈ I) := (hSys t ht).2.2.1
  have hAS (t : ℝ) (ht : t ∈ I) := (hSys t ht).2.1
  have hdG (t : ℝ) (ht : t ∈ I) := (hSys t ht).2.2.2.1
  have hdρ (t : ℝ) (ht : t ∈ I) := (hSys t ht).2.2.2.2.2.1
  have hγs (i j : Spatial) : ContDiffOn ℝ ∞ (fun t ↦ γ t i j) I :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hγ i) j
  have hRicci (x : CoordinateSpace) (hx : x 0 ∈ I) :=
    computedRicci_of_constrained_flow I hI γ A ρ hG hAS hdG
      (fun t ht ↦ (hSys t ht).2.2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.2.2.2.1)
      (fun t ht ↦ (hSys t ht).2.2.2.2.2.2.2.2) x hx
  have hE (x : CoordinateSpace) (hx : x 0 ∈ I) :
      coordinateEinstein γ x =
        sourceTensor (ρ (x 0)) (rotatingEnergy γ (x 0)) (Transport.rotatingP (x 0)) :=
    (coordinateEinstein_eq_source_of_Ricci γ x (isUnit_of_posDef (hG _ hx)) _ _ _
      (rotatingEnergy_pos γ _ (hG _ hx)) rfl (hRicci x hx)).2
  let B := openMetric I hI c γ
  let hND := openMetric_isNondegenerate I hI c γ hG
  refine ⟨τ, hτ, hτ', c, γ, ρ, openMetric_isSmooth I hI c γ hγs,
    openMetric_isSymmetric I hI c γ hG, hND, ?_, ?_, ?_, ?_⟩
  · intro m
    let t := (m : CoordinateSpace) 0
    let p := Transport.rotatingP t
    let d := rotatingEnergy γ t
    have ht : t ∈ I := m.property
    have hd : 0 < d := rotatingEnergy_pos γ t (hG t ht)
    have hESource : intrinsicEinsteinMatrix B m = sourceTensor (ρ t) d p :=
      (intrinsicEinstein_openMetric_source I hI c γ hγs hG m (ρ t) d p hd rfl
        (hRicci m ht)).2
    have hNull := twoPositiveNullSquares_of_source I hI c m γ hG (ρ t) d p
      (hρP t ht) hd rfl hESource
    refine ⟨openMetric_hasLorentzSignature I hI c m γ (hG t ht),
      intrinsicEinsteinTrace_openMetric_source I hI c m γ (hG t ht) (ρ t) d p hd rfl hESource,
      hNull, positiveSemidefinite_of_positiveNullSquares hNull, hESource.trans (hE m ht).symm⟩
  · exact coordinateEinstein_divergence_zero_of_germ I hI γ A ρ hG hAS hdG hdρ hE
  · exact fun t ht ↦ ⟨hG t ht, hρP t ht⟩
  · exact Transport.no_representation_for_coordinate_metric τ hτ hτ' γ ρ hγ hG
      hρ.continuousOn hρP _ hE

end Burnett.Bianchi

namespace Burnett.Bianchi

open Bundle Set Filter MeasureTheory
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.BackgroundConnection
open scoped ContDiff Manifold Topology Matrix.Norms.Elementwise

def HasIntrinsicEuclideanNullRayRepresentation {τ : ℝ} (c : RayIdentification.slab τ)
    (B : Field (M := RayIdentification.slab τ)) (hND : IsNondegenerate B) : Prop :=
  ∃ μ : Measure (RayIdentification.CotangentUnit τ), IsLocallyFiniteMeasure μ ∧
    (∀ᵐ p : RayIdentification.CotangentUnit τ ∂μ,
      RayIdentification.intrinsicHamiltonian B hND p.val = 0) ∧
    RayIdentification.HasIntrinsicTensorMoments c B (intrinsicEinsteinForm B) μ ∧
    (∀ a, RayIdentification.IntrinsicTransportTest τ a →
      ∫ p : RayIdentification.CotangentUnit τ,
        RayIdentification.intrinsicHamiltonDerivative c B hND a p.val ∂μ = 0)

theorem coordinateNullRayRepresentation_of_intrinsic {τ : ℝ}
    (c : RayIdentification.slab τ) (γ : ℝ → SpatialMatrix)
    (B : Field (M := RayIdentification.slab τ)) (hND : IsNondegenerate B) (hS : IsSymmetric B)
    (hG : ∀ x ∈ (RayIdentification.slab τ : Set CoordinateSpace),
      metricComponents (coordinateBilinear B c) x = metricComponents (metric γ) x)
    (hE : ∀ m : RayIdentification.slab τ,
      intrinsicEinsteinMatrix B m = coordinateEinstein γ (m : CoordinateSpace))
    (hrep : HasIntrinsicEuclideanNullRayRepresentation c B hND) :
    HasCoordinateNullRayRepresentation τ γ (coordinateEinstein γ) := by
  obtain ⟨μ, hloc, hn, hmom, ht⟩ := hrep
  letI : IsLocallyFiniteMeasure μ := hloc
  refine ⟨RayIdentification.coordinateUnitMeasure c μ,
    RayIdentification.coordinateUnitMeasure_locallyFinite c μ, ?_, ?_, ?_⟩
  · exact RayIdentification.coordinateUnitMeasure_intrinsicNull c B hND hS _ hG μ hn
  · have hf (m : RayIdentification.slab τ) :
        RayIdentification.covariantTensorComponents c (intrinsicEinsteinForm B) m =
          coordinateEinstein γ (m : CoordinateSpace) := by
      funext i j
      have h := congrFun (congrFun (hE m) i) j
      change intrinsicEinstein B m (tangentFrame m m (EuclideanSpace.single i 1))
        (tangentFrame m m (EuclideanSpace.single j 1)) = _ at h
      rw [RayIdentification.slab_tangentFrame, RayIdentification.slab_tangentFrame] at h
      simpa only [RayIdentification.covariantTensorComponents, intrinsicEinsteinForm_apply,
        RayIdentification.slab_tangentFrame, coordinateBasis, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply] using h
    exact RayIdentification.coordinateUnitMeasure_intrinsicMoments c B _ _ hG μ _ hf hmom
  · intro a ha
    exact RayIdentification.coordinateUnitMeasure_intrinsicTransport c B hND hS _ hG μ ht a
      (RayIdentification.pullbackTest_intrinsic c a ha.1 ha.2.1 ha.2.2)

theorem no_intrinsicEuclidean_representation_of_openMetric {τ : ℝ}
    (c : RayIdentification.slab τ) (γ : ℝ → SpatialMatrix)
    (B : Field (M := RayIdentification.slab τ))
    (hB : B = openMetric (Transport.domain τ) isOpen_Ioo c γ)
    (hND : IsNondegenerate B) (hS : IsSymmetric B)
    (hE : ∀ m : RayIdentification.slab τ,
      intrinsicEinsteinMatrix B m = coordinateEinstein γ (m : CoordinateSpace))
    (hno : ¬ HasCoordinateNullRayRepresentation τ γ (coordinateEinstein γ)) :
    ¬ HasIntrinsicEuclideanNullRayRepresentation c B hND := by
  intro hr
  apply hno (coordinateNullRayRepresentation_of_intrinsic c γ B hND hS ?_ hE hr)
  intro x hx
  rw [hB]
  exact congrArg (fun f : LinearMap.BilinForm ℝ CoordinateSpace => FiberMetric.covariant f coordinateBasis)
    (openMetric_coordinateBilinear (Transport.domain τ) isOpen_Ioo c γ x hx)

/-- An actual smooth Lorentzian counterexample on the open product, with Euclidean ray normalization. -/
theorem exists_bianchi_intrinsic_counterexample_euclidean_rays {H : ℝ} (hH : 0 < H) :
    ∃ (τ : ℝ), 0 < τ ∧ τ < Real.pi / 4 ∧
      ∃ (c : RayIdentification.slab τ) (γ : ℝ → SpatialMatrix)
        (B : Field (M := RayIdentification.slab τ)),
        B = openMetric (Transport.domain τ) isOpen_Ioo c γ ∧ IsSmooth B ∧ IsSymmetric B ∧
        ∃ hND : IsNondegenerate B,
          (∀ m, FieldHasLorentzSignature B m ∧ intrinsicEinsteinTrace B m = 0 ∧
            HasTwoPositiveNullSquares B hND m ∧
            (∀ u : TangentSpace Model m, 0 ≤ intrinsicEinstein B m u u)) ∧
          (∀ x ∈ Transport.baseDomain τ, ∀ b : Index,
            tensorDivergence (metric γ) (coordinateEinstein γ) x b = 0) ∧
          ¬ HasIntrinsicEuclideanNullRayRepresentation c B hND := by
  obtain ⟨τ, hτ, hτ', c, γ, _, hSmooth, hS, hND, hP, hDiv, _, hno⟩ :=
    exists_bianchi_openMetric_with_coordinate_obstruction hH
  let B := openMetric (Transport.domain τ) isOpen_Ioo c γ
  refine ⟨τ, hτ, hτ', c, γ, B, rfl, hSmooth, hS, hND, ?_, hDiv, ?_⟩
  · intro m
    obtain ⟨hLor, hT, hN, hpos, _⟩ := hP m
    exact ⟨hLor, hT, hN, hpos⟩
  · exact no_intrinsicEuclidean_representation_of_openMetric c γ B rfl hND hS
      (fun m ↦ (hP m).2.2.2.2) hno

end Burnett.Bianchi

namespace Burnett.Bianchi

open Bundle Set Filter MeasureTheory
open Burnett.RicciSymbol Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.CotangentUnitNormalization
open Burnett.Geometry.UnitNullCompactness (CotangentBundle cotangentScale dualEnergy)
open Burnett.Geometry.CotangentAngularExtension (puncturedCotangent)
open scoped ContDiff Manifold Topology BigOperators Matrix.Norms.Elementwise

local instance unitShellMeasurable (τ : ℝ) (r : Metric (M := RayIdentification.slab τ)) :
    MeasurableSpace (unitShell r) := borel _

local instance unitShellBorel (τ : ℝ) (r : Metric (M := RayIdentification.slab τ)) :
    BorelSpace (unitShell r) := ⟨rfl⟩

def HasIntrinsicNullRayRepresentation {τ : ℝ} (c : RayIdentification.slab τ)
    (r : Metric (M := RayIdentification.slab τ))
    (B : Field (M := RayIdentification.slab τ)) (hND : IsNondegenerate B) : Prop :=
  ∃ μ : Measure (unitShell r), IsLocallyFiniteMeasure μ ∧
    (∀ᵐ p : unitShell r ∂μ, RayIdentification.intrinsicHamiltonian B hND p.val = 0) ∧
    (∀ T : RayIdentification.ContravariantField τ, RayIdentification.IntrinsicTensorTest τ T →
      (∫ p : unitShell r, T p.val.proj p.val.2 p.val.2 ∂μ) =
        ∫ x : RayIdentification.slab τ, (∑ i, ∑ j,
          RayIdentification.covariantTensorComponents c (intrinsicEinsteinForm B) x i j *
            RayIdentification.tensorTestComponents c T x i j) ∂ManifoldVolume.geometricMeasure B) ∧
    (∀ a, RayIdentification.IntrinsicTransportTest τ a →
      ∫ p : unitShell r, RayIdentification.intrinsicHamiltonDerivative c B hND a p.val ∂μ = 0)

/-- Both moments and transport are pushed forward using the same positive squared reweighting. -/
theorem intrinsicEuclideanNullRayRepresentation_of_auxiliary {τ : ℝ} (c : RayIdentification.slab τ)
    (r : Metric (M := RayIdentification.slab τ))
    (B : Field (M := RayIdentification.slab τ)) (hND : IsNondegenerate B)
    (hrep : HasIntrinsicNullRayRepresentation c r B hND) :
    HasIntrinsicEuclideanNullRayRepresentation c B hND := by
  obtain ⟨μ, hloc, hnull, hmom, htransport⟩ := hrep
  letI : IsLocallyFiniteMeasure μ := hloc
  let e := RayIdentification.slabEuclideanMetric τ
  let F := unitShellHomeomorph r e
  let weight := shellScale r e
  let ν := NormChange.rescaled μ F weight
  have hIntegrals (q : CotangentBundle (RayIdentification.slab τ) → ℝ)
      (hq : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), q (cotangentScale t p) = t^2 * q p) :
      (∫ p : unitShell e, q p.val ∂ν) = ∫ p : unitShell r, q p.val ∂μ := by
    apply (NormChange.divided_quadratic_test_preserved μ F weight
      (shellScale_continuous r e) (shellScale_pos r e)
      (fun p : unitShell e ↦ q p.val) (fun p : unitShell r ↦ q p.val) ?_).2
    intro p
    change q ((unitShellHomeomorph r e p).val) = _ / (weight p)^2
    rw [unitShellHomeomorph_value,
      hq p.val (unitShell_punctured r p.property) _ (inv_pos.mpr (shellScale_pos r e p)), inv_pow]
    exact (div_eq_inv_mul _ _).symm
  refine ⟨ν, NormChange.rescaled_locallyFinite μ F weight (shellScale_continuous r e), ?_, ?_, ?_⟩
  · have hzero (p : CotangentBundle (RayIdentification.slab τ)) :
        RayIdentification.intrinsicHamiltonian B hND p = 0 ↔ dualEnergy B hND p = 0 := by
      unfold RayIdentification.intrinsicHamiltonian
      constructor
      · intro hp
        linarith
      · intro hp
        simp [hp]
    rw [ae_iff] at hnull ⊢
    let Z : Set (unitShell e) := {p | RayIdentification.intrinsicHamiltonian B hND p.val ≠ 0}
    suffices ν Z = 0 by exact this
    apply (NormChange.rescaled_null_iff μ F weight (shellScale_continuous r e)
      (shellScale_pos r e) Z).mpr
    have hz : F ⁻¹' Z =
        {p : unitShell r | RayIdentification.intrinsicHamiltonian B hND p.val ≠ 0} := by
      ext p
      change ¬RayIdentification.intrinsicHamiltonian B hND (unitShellHomeomorph r e p).val = 0 ↔
        ¬RayIdentification.intrinsicHamiltonian B hND p.val = 0
      simp only [hzero, unitShellHomeomorph_null_iff]
    rw [hz]
    exact hnull
  · intro T hT
    let q : CotangentBundle (RayIdentification.slab τ) → ℝ := fun p ↦ T p.proj p.2 p.2
    have hq : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), q (cotangentScale t p) = t^2 * q p :=
      fun p _ t _ ↦ RayIdentification.tensorContraction_scale T p t
    change (∫ p : unitShell e, q p.val ∂ν) = _
    rw [hIntegrals q hq]
    exact hmom T hT
  · intro a ha
    let q := RayIdentification.intrinsicHamiltonDerivative c B hND a
    have hq : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), q (cotangentScale t p) = t^2 * q p :=
      fun p hp t ht ↦ RayIdentification.intrinsicHamiltonDerivative_scale c B hND a ha p hp t ht
    change (∫ p : unitShell e, q p.val ∂ν) = 0
    rw [hIntegrals q hq]
    exact htransport a ha

/-- Geometric nonrepresentability for the actual Einstein tensor on an open product. -/
theorem exists_bianchi_intrinsic_counterexample {H : ℝ} (hH : 0 < H) :
    ∃ (τ : ℝ), 0 < τ ∧ τ < Real.pi / 4 ∧
      ∃ (c : RayIdentification.slab τ) (γ : ℝ → SpatialMatrix)
        (B : Field (M := RayIdentification.slab τ)),
        B = openMetric (Transport.domain τ) isOpen_Ioo c γ ∧ IsSmooth B ∧ IsSymmetric B ∧
        ∃ hND : IsNondegenerate B,
          (∀ m, FieldHasLorentzSignature B m ∧ intrinsicEinsteinTrace B m = 0 ∧
            HasTwoPositiveNullSquares B hND m ∧
            (∀ u : TangentSpace Model m, 0 ≤ intrinsicEinstein B m u u)) ∧
          (∀ x ∈ Transport.baseDomain τ, ∀ b : Index,
            tensorDivergence (metric γ) (coordinateEinstein γ) x b = 0) ∧
          ∀ r : Metric (M := RayIdentification.slab τ), ¬ HasIntrinsicNullRayRepresentation c r B hND := by
  obtain ⟨τ, hτ, hτ', c, γ, B, hB, hSmooth, hS, hND, hP, hDiv, hNo⟩ :=
    exists_bianchi_intrinsic_counterexample_euclidean_rays hH
  refine ⟨τ, hτ, hτ', c, γ, B, hB, hSmooth, hS, hND, hP, hDiv, ?_⟩
  exact fun r hrep ↦ hNo (intrinsicEuclideanNullRayRepresentation_of_auxiliary c r B hND hrep)

end Burnett.Bianchi
