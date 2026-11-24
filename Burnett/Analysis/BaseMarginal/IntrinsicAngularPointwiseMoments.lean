import Burnett.Analysis.BaseMarginal.IntrinsicAngularFrameMoments
import Burnett.Geometry.SmoothTangentValueExtension

/-! The Einstein moment holds for all vectors in the actual tangent fiber on one full measure set. -/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 4500000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory ProbabilityTheory Module Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open scoped ContDiff Manifold ProbabilityTheory Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Evaluate the actual covector on two vectors in its own fiber, extended by zero off that fiber. -/
def fiberQuadraticPhase {r : Metric (M := M)} (x : M) (u v : TangentSpace Model x)
    (p : Cosphere r) : ℝ := by
  classical
  exact if h : projection p = x then
    p.val.2 (cast (congrArg (TangentSpace Model) h.symm) u) *
      p.val.2 (cast (congrArg (TangentSpace Model) h.symm) v)
  else 0

private theorem fiberQuadraticPhase_eq_frameSum {r : Metric (M := M)}
    (c x : M) (φ : M → ℝ) (hφ : φ x = 1)
    (hx : x ∈ (chartAt CoordinateSpace c).source)
    (u v : TangentSpace Model x) (p : Cosphere r) (hpx : projection p = x) :
    let b := tensorTangentBasis c x hx
    fiberQuadraticPhase x u v p =
      ∑ i, ∑ j, (b.repr u i * b.repr v j) *
        (p.val.2 (supportedFrameVector c φ i (projection p)) *
          p.val.2 (supportedFrameVector c φ j (projection p))) := by
  subst x
  intro b
  rw [fiberQuadraticPhase, dif_pos rfl]
  change p.val.2 u * p.val.2 v = _
  have hEval (w : TangentSpace Model (projection p)) :
      p.val.2 w = ∑ i, b.repr w i * p.val.2 (supportedFrameVector c φ i (projection p)) := by
    calc
      _ = p.val.2 (∑ i, b.repr w i • b i) := congrArg p.val.2 (b.sum_repr w).symm
      _ = _ := by
        simp only [map_sum, map_smul, smul_eq_mul, supportedFrameVector, hφ, one_smul]
        rfl
  rw [hEval u, hEval v, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem bilinForm_eq_frameSum (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source)
    (G : LinearMap.BilinForm ℝ (TangentSpace Model x)) (u v : TangentSpace Model x) :
    let b := tensorTangentBasis c x hx
    G u v = ∑ i, ∑ j, (b.repr u i * b.repr v j) * G (b i) (b j) := by
  intro b
  calc
    _ = G (∑ i, b.repr u i • b i) (∑ j, b.repr v j • b j) := by rw [b.sum_repr, b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Given the actual reconstructed angular kernel, its conditional moment is the Einstein tensor
simultaneously on every pair of tangent vectors for almost every base point. -/
theorem ae_intrinsicEinstein_eq_angularFiberMoment (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hn : IsNondegenerate B) (hSymm : ∀ x, (intrinsicEinstein B hn x).IsSymm)
    (μ : Measure (Cosphere r)) (hMom : HasCosphereEinsteinMoments r B hn μ)
    (κ : Kernel M (Cosphere r)) [IsSFiniteKernel κ]
    (hLaw : ManifoldVolume.geometricMeasure B ⊗ₘ κ = μ.map (fun p => (projection p, p)))
    (hFiber : ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, κ x {p | projection p ≠ x} = 0) :
    ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, ∀ u v : TangentSpace Model x,
      Integrable (fiberQuadraticPhase x u v) (κ x) ∧
        intrinsicEinstein B hn x u v = ∫ p : Cosphere r, fiberQuadraticPhase x u v p ∂κ x := by
  classical
  by_cases hne : Nonempty M
  swap
  · haveI : IsEmpty M := not_nonempty_iff.mp hne
    exact Eventually.of_forall fun x => isEmptyElim x
  letI : Nonempty M := hne
  let f (c : M) : SmoothBumpFunction Model c := Classical.choice inferInstance
  let U (c : M) : Set M := interior {x | f c x = 1}
  have hU (c : M) : c ∈ U c := mem_interior_iff_mem_nhds.mpr (f c).eventuallyEq_one
  obtain ⟨c, hCover⟩ := isLindelof_univ.indexed_countable_subcover U (fun _ => isOpen_interior)
    (show (univ : Set M) ⊆ ⋃ c, U c from fun x _ => mem_iUnion.mpr ⟨x, hU x⟩)
  have hRows := ae_all_iff.mpr (fun k : ℕ =>
    ae_intrinsicAngularFrameMoments r B hB hn μ hMom κ hLaw (c k) (f (c k))
      (f (c k)).contMDiff (f (c k)).hasCompactSupport (f (c k)).tsupport_subset_chartAt_source)
  filter_upwards [hRows, hFiber] with x hAt hSupp u v
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hCover (mem_univ x))
  let φ : M → ℝ := f (c k)
  have hOneMem : x ∈ {y : M | f (c k) y = 1} := interior_subset hk
  have hOne : φ x = 1 := hOneMem
  have hx : x ∈ (chartAt CoordinateSpace (c k)).source :=
    (f (c k)).tsupport_subset_chartAt_source (subset_tsupport _ (by simp [hOne] : φ x ≠ 0))
  let b := tensorTangentBasis (c k) x hx
  let Z (i j : Index) (p : Cosphere r) :=
    p.val.2 (supportedFrameVector (c k) φ i (projection p)) *
      p.val.2 (supportedFrameVector (c k) φ j (projection p))
  let a (i j : Index) := b.repr u i * b.repr v j
  let G := intrinsicEinstein B hn x
  have hF (i j : Index) : Integrable (Z i j) (κ x) := (hAt k i j).1
  have hComponent (i j : Index) : (∫ p, Z i j p ∂κ x) = G (b i) (b j) := by
    have h := (hAt k i j).2 hx hOne
    change ((G (b i) (b j) + G (b j) (b i)) / 2) = _ at h
    rw [show G (b j) (b i) = G (b i) (b j) from (hSymm x).eq _ _] at h
    calc
      _ = (G (b i) (b j) + G (b i) (b j)) / 2 := h.symm
      _ = _ := by ring
  have hPointwise : fiberQuadraticPhase x u v =ᵐ[κ x] fun p => ∑ i, ∑ j, a i j * Z i j p := by
    have hBase : ∀ᵐ p : Cosphere r ∂κ x, projection p = x := ae_iff.mpr hSupp
    exact hBase.mono fun p hp => fiberQuadraticPhase_eq_frameSum (c k) x φ hOne hx u v p hp
  have hRow (i : Index) : Integrable (fun p => ∑ j, a i j * Z i j p) (κ x) :=
    integrable_finset_sum _ fun j _ => (hF i j).const_mul (a i j)
  refine ⟨(integrable_finset_sum _ fun i _ => hRow i).congr hPointwise.symm, ?_⟩
  calc
    _ = ∑ i, ∑ j, a i j * G (b i) (b j) := bilinForm_eq_frameSum (c k) x hx G u v
    _ = ∑ i, ∫ p, (∑ j, a i j * Z i j p) ∂κ x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum _ (fun j _ => (hF i j).const_mul (a i j))]
      simp only [integral_const_mul, hComponent]
    _ = ∫ p, (∑ i, ∑ j, a i j * Z i j p) ∂κ x :=
      (integral_finset_sum _ (fun i _ => hRow i)).symm
    _ = _ := integral_congr_ae hPointwise.symm

end Burnett.F08.IntrinsicBaseMarginal
