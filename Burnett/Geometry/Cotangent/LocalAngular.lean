import Burnett.Geometry.SmoothMetricConnection
import Burnett.Geometry.ManifoldVolumeRegularity
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.UnitNullAngular

open Matrix Set LinearMap
open scoped BigOperators ContDiff Manifold
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InverseField (matrixInverse)

def dualPair (A : Tensor2) : LinearMap.BilinForm ℝ Covector :=
  Matrix.toBilin (Pi.basisFun ℝ Index) A

theorem dualPair_apply (A : Tensor2) (u v : Covector) :
    dualPair A u v = ∑ i, ∑ j, A i j * u i * v j := by
  simp only [dualPair, Matrix.toBilin_apply, Pi.basisFun_repr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dualPair_self (A : Tensor2) (v : Covector) :
    dualPair A v v = symbolNorm A v := dualPair_apply A v v

theorem dualPair_symm (A : Tensor2) (hA : IsSymmetricTensor A)
    (u v : Covector) : dualPair A u v = dualPair A v u := by
  rw [dualPair_apply, dualPair_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i]
  ring

theorem dualPair_add_smul_self (A : Tensor2) (hA : IsSymmetricTensor A)
    (u v : Covector) (a : ℝ) :
    dualPair A (u + a • v) (u + a • v) =
      dualPair A u u + 2 * dualPair A u v * a + dualPair A v v * a^2 := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [dualPair_symm A hA v u]
  ring

theorem dualPair_smul_self (A : Tensor2) (v : Covector) (a : ℝ) :
    dualPair A (a • v) (a • v) = a^2 * dualPair A v v := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem exists_dualPair_pos (A : Tensor2) (hA : Matrix.det A ≠ 0) {u : Covector} (hu : u ≠ 0) :
    ∃ v, 0 < dualPair A u v := by
  have hn : (dualPair A).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ (Pi.basisFun ℝ Index) (by
      rw [dualPair, ← BilinForm.toMatrix_symm, LinearEquiv.apply_symm_apply]
      exact hA)
  by_contra! hnpos
  apply hu
  apply hn
  intro v
  have h := hnpos v
  have h' := hnpos (-v)
  rw [map_neg] at h'
  linarith

def correction (b c d : ℝ) : ℝ := -c / (b + Real.sqrt (b^2 - d*c))

theorem correction_zero (b d : ℝ) : correction b 0 d = 0 := by
  simp [correction]

theorem correction_quadratic (b c d : ℝ) (hb : 0 < b) (hΔ : 0 < b^2 - d*c) :
    c + 2*b*correction b c d + d*(correction b c d)^2 = 0 := by
  let s := Real.sqrt (b^2 - d*c)
  have hs : s^2 = b^2-d*c := Real.sq_sqrt hΔ.le
  have hd : b+s ≠ 0 := (add_pos_of_pos_of_nonneg hb (Real.sqrt_nonneg _)).ne'
  change c + 2*b*(-c/(b+s)) + d*(-c/(b+s))^2 = 0
  calc
    _ = c*(s^2-b^2+d*c)/(b+s)^2 := by field_simp [hd]; ring
    _ = 0 := by rw [hs]; ring

end Burnett.Geometry.UnitNullAngular

namespace Burnett.Geometry.UnitNullAngular

open Set
open scoped BigOperators ContDiff Manifold
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InverseField (matrixInverse)

abbrev Phase := CoordinateSpace × Covector

def unitNull (R G : CoordinateSpace → Tensor2) : Set Phase :=
  {p | dualPair (R p.1) p.2 p.2 = 1 ∧ dualPair (G p.1) p.2 p.2 = 0}

theorem contDiffOn_dualPair (A : CoordinateSpace → Tensor2)
    {U : Set CoordinateSpace} {W : Set Phase}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hWU : MapsTo Prod.fst W U) {u v : Phase → Covector}
    (hu : ContDiffOn ℝ ∞ u W) (hv : ContDiffOn ℝ ∞ v W) :
    ContDiffOn ℝ ∞ (fun p => dualPair (A p.1) (u p) (v p)) W := by
  simp only [dualPair_apply]
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (((hA i j).comp contDiffOn_fst hWU).mul ((contDiff_apply ℝ ℝ i).comp_contDiffOn hu)).mul
      ((contDiff_apply ℝ ℝ j).comp_contDiffOn hv)

theorem local_unitNull_retraction (R G : CoordinateSpace → Tensor2)
    {U : Set CoordinateSpace} (hU : IsOpen U)
    (hR : ∀ i j, ContDiffOn ℝ ∞ (fun x => R x i j) U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun x => G x i j) U)
    (hGs : ∀ x ∈ U, IsSymmetricTensor (G x))
    {p₀ : Phase} (hp₀ : p₀.1 ∈ U) (hu₀ : p₀ ∈ unitNull R G) (hGdet : Matrix.det (G p₀.1) ≠ 0) :
    ∃ W : Set Phase, IsOpen W ∧ p₀ ∈ W ∧ W ⊆ U ×ˢ univ ∧
      ∃ ret : Phase → Phase, ContDiffOn ℝ ∞ ret W ∧ MapsTo ret W (unitNull R G) ∧
        (∀ p ∈ W, (ret p).1 = p.1) ∧ ∀ p ∈ W, p ∈ unitNull R G → ret p = p := by
  have hne : p₀.2 ≠ 0 := by
    intro h
    have h1 := hu₀.1
    rw [h] at h1
    simp at h1
  obtain ⟨v, hv⟩ := exists_dualPair_pos (G p₀.1) hGdet hne
  let B := fun p : Phase => dualPair (G p.1) p.2 v
  let C := fun p : Phase => dualPair (G p.1) p.2 p.2
  let D := fun p : Phase => dualPair (G p.1) v v
  let Δ := fun p : Phase => (B p)^2 - D p * C p
  let W₀ := U ×ˢ (univ : Set Covector)
  let W₁ := (W₀ ∩ B ⁻¹' Ioi 0) ∩ Δ ⁻¹' Ioi 0
  have hw₀ : IsOpen W₀ := hU.prod isOpen_univ
  have hmap : MapsTo Prod.fst W₀ U := fun p hp => hp.1
  have hB : ContDiffOn ℝ ∞ B W₀ := contDiffOn_dualPair G hG hmap contDiffOn_snd contDiffOn_const
  have hC : ContDiffOn ℝ ∞ C W₀ := contDiffOn_dualPair G hG hmap contDiffOn_snd contDiffOn_snd
  have hD : ContDiffOn ℝ ∞ D W₀ := contDiffOn_dualPair G hG hmap contDiffOn_const contDiffOn_const
  have hΔ : ContDiffOn ℝ ∞ Δ W₀ := (hB.pow 2).sub (hD.mul hC)
  have hW₀₁ : W₁ ⊆ W₀ := fun _ h => h.1.1
  have hW₁ : IsOpen W₁ :=
    (hΔ.mono inter_subset_left).continuousOn.isOpen_inter_preimage
      (hB.continuousOn.isOpen_inter_preimage hw₀ isOpen_Ioi) isOpen_Ioi
  have hC₀ : C p₀ = 0 := hu₀.2
  have hΔ₀ : 0 < Δ p₀ := by
    change 0 < (B p₀)^2 - D p₀ * C p₀
    rw [hC₀, mul_zero, sub_zero]
    exact pow_pos hv 2
  have hp₀₁ : p₀ ∈ W₁ := ⟨⟨⟨hp₀, trivial⟩, hv⟩, hΔ₀⟩
  let a := fun p : Phase => correction (B p) (C p) (D p)
  let z := fun p : Phase => p.2 + a p • v
  have hd : ContDiffOn ℝ ∞ a W₁ := by
    change ContDiffOn ℝ ∞ (fun p => -C p / (B p + Real.sqrt (Δ p))) W₁
    apply (hC.mono hW₀₁).neg.div
    · exact (hB.mono hW₀₁).add ((hΔ.mono hW₀₁).sqrt (fun p hp => (show 0 < Δ p from hp.2).ne'))
    · intro p hp
      exact (add_pos_of_pos_of_nonneg hp.1.2 (Real.sqrt_nonneg (Δ p))).ne'
  have hz : ContDiffOn ℝ ∞ z W₁ := contDiffOn_snd.add (hd.smul contDiffOn_const)
  have hzn (p : Phase) (hp : p ∈ W₁) : dualPair (G p.1) (z p) (z p) = 0 := by
    rw [show z p = p.2 + a p • v from rfl, dualPair_add_smul_self _ (hGs _ hp.1.1.1)]
    exact correction_quadratic (B p) (C p) (D p) hp.1.2 hp.2
  have hzfix (p : Phase) (hp : C p = 0) : z p = p.2 := by
    simp [z, a, hp, correction_zero]
  let E := fun p : Phase => dualPair (R p.1) (z p) (z p)
  let W := W₁ ∩ E ⁻¹' Ioi 0
  have hE : ContDiffOn ℝ ∞ E W₁ :=
    contDiffOn_dualPair R hR (fun _ hp => hp.1.1.1) hz hz
  have hW : IsOpen W := hE.continuousOn.isOpen_inter_preimage hW₁ isOpen_Ioi
  have hE₀ : E p₀ = 1 := by
    change dualPair (R p₀.1) (z p₀) (z p₀) = 1
    rw [hzfix _ hC₀]
    exact hu₀.1
  have hpW : p₀ ∈ W := ⟨hp₀₁, by change 0 < E p₀; rw [hE₀]; exact zero_lt_one⟩
  let ret := fun p : Phase => (p.1, (Real.sqrt (E p))⁻¹ • z p)
  have hr : ContDiffOn ℝ ∞ ret W := by
    apply contDiffOn_fst.prodMk
    refine (((hE.mono inter_subset_left).sqrt fun p hp => (show 0 < E p from hp.2).ne').inv
      (fun p hp => (Real.sqrt_pos.mpr hp.2).ne')).smul (hz.mono inter_subset_left)
  refine ⟨W, hW, hpW, fun p hp => hp.1.1.1, ret, hr, ?_, (fun p hp => rfl), ?_⟩
  · intro p hp
    have hEpos : 0 < E p := hp.2
    have hse : (Real.sqrt (E p))^2 = E p := Real.sq_sqrt hEpos.le
    constructor
    · change dualPair (R p.1) ((Real.sqrt (E p))⁻¹ • z p) ((Real.sqrt (E p))⁻¹ • z p) = 1
      rw [dualPair_smul_self, inv_pow, hse]
      exact inv_mul_cancel₀ hEpos.ne'
    · change dualPair (G p.1) ((Real.sqrt (E p))⁻¹ • z p) ((Real.sqrt (E p))⁻¹ • z p) = 0
      rw [dualPair_smul_self, hzn p hp.1, mul_zero]
  · intro p hp hnull
    have hz' : z p = p.2 := hzfix p hnull.2
    have hE' : E p = 1 := by
      change dualPair (R p.1) (z p) (z p) = 1
      rw [hz']
      exact hnull.1
    have hh : ret p = (p.1, (Real.sqrt (E p))⁻¹ • z p) := rfl
    rw [hh, hE', hz', Real.sqrt_one, inv_one, one_smul]

end Burnett.Geometry.UnitNullAngular

namespace Burnett.Geometry.UnitNullAngular

open Set Matrix
open scoped Manifold ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric ManifoldMetricTransition
open Burnett.Geometry.InverseField (matrixInverse)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def chartInverse (g : ManifoldBilinear.Field (M := M)) (c : M) (x : CoordinateSpace) : Tensor2 :=
  matrixInverse (metricComponents (coordinateBilinear g c) x)

theorem chartInverse_smooth (g : ManifoldBilinear.Field (M := M)) (hg : ManifoldBilinear.IsSmooth g)
    (hgn : ManifoldBilinear.IsNondegenerate g) (c : M) (i j : Index) :
    ContDiffOn ℝ ∞ (fun x => chartInverse g c x i j) (chartAt CoordinateSpace c).target :=
  SmoothMetricConnection.contDiffOn_matrixInverse
    (fun x => (metricComponents (coordinateBilinear g c) x : Matrix Index Index ℝ)) _
    (ManifoldBilinear.contDiffOn_metricComponents g hg c)
    (fun _ hx => ManifoldVolumeRegularity.coordinate_det_ne_zero g hgn c hx) i j

theorem chartInverse_symm (g : ManifoldBilinear.Field (M := M)) (hgs : ManifoldBilinear.IsSymmetric g)
    (c : M) (x : CoordinateSpace) :
    IsSymmetricTensor (chartInverse g c x) := by
  let A : Matrix Index Index ℝ := metricComponents (coordinateBilinear g c) x
  have hsym : IsSymmetricTensor A := FiberMetric.covariant_symmetric _
    (ManifoldBilinear.coordinateBilinear_symmetric g hgs c x) coordinateBasis
  have hA : Aᵀ = A := by
    ext i j
    exact hsym j i
  have hT : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hA]
  intro i j
  change A⁻¹ i j = A⁻¹ j i
  exact congrArg (fun X : Matrix Index Index ℝ => X j i) hT

private theorem matrixInverse_det_ne_zero (A : Matrix Index Index ℝ) (hA : Matrix.det A ≠ 0) :
    Matrix.det (matrixInverse A) ≠ 0 := by
  unfold matrixInverse
  exact (Matrix.isUnit_nonsing_inv_det A (isUnit_iff_ne_zero.mpr hA)).ne_zero

theorem chartInverse_det_ne_zero (g : ManifoldBilinear.Field (M := M)) (hgn : ManifoldBilinear.IsNondegenerate g)
    (c : M) (x : CoordinateSpace) (hx : x ∈ (chartAt CoordinateSpace c).target) :
    Matrix.det (chartInverse g c x) ≠ 0 := by
  unfold chartInverse
  exact matrixInverse_det_ne_zero (metricComponents (coordinateBilinear g c) x)
    (ManifoldVolumeRegularity.coordinate_det_ne_zero g hgn c hx)

def chartUnitNull (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M)) (c : M) : Set Phase :=
  unitNull (chartInverse r.inner c) (chartInverse g c) ∩
    (chartAt CoordinateSpace c).target ×ˢ (univ : Set Covector)

theorem chartUnitNull_mem (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (c : M) (p : Phase) : p ∈ chartUnitNull r g c ↔
      symbolNorm (matrixInverse (metricComponents (coordinateMetric r c) p.1)) p.2 = 1 ∧
      symbolNorm (matrixInverse (metricComponents (coordinateBilinear g c) p.1)) p.2 = 0 ∧
      p.1 ∈ (chartAt CoordinateSpace c).target := by
  simp only [chartUnitNull, unitNull, mem_inter_iff, mem_setOf_eq, dualPair_self,
    chartInverse, mem_prod, mem_univ, and_true, and_assoc]
  rfl

theorem local_chartUnitNull_retraction (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c : M) {p₀ : Phase}
    (hp₀ : p₀ ∈ chartUnitNull r g c) :
    ∃ W : Set Phase, IsOpen W ∧ p₀ ∈ W ∧ W ⊆ (chartAt CoordinateSpace c).target ×ˢ univ ∧
      ∃ ret : Phase → Phase, ContDiffOn ℝ ∞ ret W ∧ MapsTo ret W (chartUnitNull r g c) ∧
        (∀ p ∈ W, (ret p).1 = p.1) ∧ ∀ p ∈ W, p ∈ chartUnitNull r g c → ret p = p := by
  have hr : ManifoldBilinear.IsNondegenerate r.inner := by
    intro x u hu
    by_contra hn
    exact (r.pos x u hn).ne' (hu u)
  obtain ⟨W, hoo, h0, hsub, ret, hret, hmaps, hbase, hfix⟩ :=
    local_unitNull_retraction (chartInverse r.inner c) (chartInverse g c)
      (chartAt CoordinateSpace c).open_target
      (chartInverse_smooth r.inner (ManifoldBilinear.isSmooth_inner r) hr c)
      (chartInverse_smooth g hg hgn c) (fun x _ => chartInverse_symm g hgs c x)
      hp₀.2.1 hp₀.1 (chartInverse_det_ne_zero g hgn c p₀.1 hp₀.2.1)
  refine ⟨W, hoo, h0, hsub, ret, hret, ?_, hbase, fun p hp hnp => hfix p hp hnp.1⟩
  intro p hp
  refine ⟨hmaps hp, ?_⟩
  exact ⟨hbase p hp ▸ (hsub hp).1, trivial⟩

theorem local_chartUnitNull_scalar_extension (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c : M) {p₀ : Phase}
    (hp₀ : p₀ ∈ chartUnitNull r g c)
    (a : Phase → ℝ) (ha : ContDiffOn ℝ ∞ a (chartUnitNull r g c)) :
    ∃ W : Set Phase, IsOpen W ∧ p₀ ∈ W ∧ W ⊆ (chartAt CoordinateSpace c).target ×ˢ univ ∧
      ∃ ext : Phase → ℝ, ContDiffOn ℝ ∞ ext W ∧ EqOn ext a (W ∩ chartUnitNull r g c) := by
  obtain ⟨W, hWo, hW₀, hWsub, ret, hret, hmaps, _, hfix⟩ :=
    local_chartUnitNull_retraction r g hg hgn hgs c hp₀
  refine ⟨W, hWo, hW₀, hWsub, a ∘ ret, ha.comp hret hmaps, ?_⟩
  intro p hp
  exact congrArg a (hfix p hp.1 hp.2)

end Burnett.Geometry.UnitNullAngular

namespace Burnett.Geometry.UnitNullAngular

open Set
open scoped Manifold ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def chartPunctured (c : M) : Set Phase :=
  {p | p.1 ∈ (chartAt CoordinateSpace c).target ∧ p.2 ≠ 0}

/-- The angular trace of the degree-one extension on the invariant section. -/
def weightedTrace (b : Phase → ℝ) (s : Phase → ℝ) (p : Phase) : ℝ :=
  b (p.1, s p • p.2) / s p

theorem contDiffOn_weightedTrace (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (c : M) (b s : Phase → ℝ) (hb : ContDiffOn ℝ ∞ b (chartPunctured c))
    (hs : ContDiffOn ℝ ∞ s (chartUnitNull r g c)) (hpos : ∀ p ∈ chartUnitNull r g c, 0 < s p) :
    ContDiffOn ℝ ∞ (weightedTrace b s) (chartUnitNull r g c) := by
  have ht : ContDiffOn ℝ ∞ (fun p : Phase => (p.1, s p • p.2)) (chartUnitNull r g c) :=
    contDiffOn_fst.prodMk (hs.smul contDiffOn_snd)
  have hm : MapsTo (fun p : Phase => (p.1, s p • p.2)) (chartUnitNull r g c) (chartPunctured c) := by
    intro p hp
    have hn : p.2 ≠ 0 := by
      intro hz
      have h1 := hp.1.1
      rw [hz] at h1
      simp at h1
    exact ⟨hp.2.1, smul_ne_zero (hpos p hp).ne' hn⟩
  exact (hb.comp ht hm).div hs (fun p hp => (hpos p hp).ne')

theorem local_chart_weightedTrace_extension (r : Metric (M := M)) (g : ManifoldBilinear.Field (M := M))
    (hg : ManifoldBilinear.IsSmooth g) (hgn : ManifoldBilinear.IsNondegenerate g)
    (hgs : ManifoldBilinear.IsSymmetric g) (c : M) {p₀ : Phase}
    (hp₀ : p₀ ∈ chartUnitNull r g c)
    (b s : Phase → ℝ) (hb : ContDiffOn ℝ ∞ b (chartPunctured c))
    (hs : ContDiffOn ℝ ∞ s (chartUnitNull r g c)) (hpos : ∀ p ∈ chartUnitNull r g c, 0 < s p)
    (K : Set CoordinateSpace) (hsupp : ∀ p ∈ chartPunctured c, p.1 ∉ K → b p = 0) :
    ∃ W : Set Phase, IsOpen W ∧ p₀ ∈ W ∧ W ⊆ (chartAt CoordinateSpace c).target ×ˢ univ ∧
      ∃ ext : Phase → ℝ, ContDiffOn ℝ ∞ ext W ∧ EqOn ext (weightedTrace b s) (W ∩ chartUnitNull r g c) ∧
        ∀ p ∈ W, p.1 ∉ K → ext p = 0 := by
  obtain ⟨W, hWo, hW₀, hWsub, ret, hret, hmaps, hbase, hfix⟩ :=
    local_chartUnitNull_retraction r g hg hgn hgs c hp₀
  have htrace := contDiffOn_weightedTrace r g c b s hb hs hpos
  refine ⟨W, hWo, hW₀, hWsub, weightedTrace b s ∘ ret, htrace.comp hret hmaps, ?_, ?_⟩
  · intro p hp
    exact congrArg (weightedTrace b s) (hfix p hp.1 hp.2)
  · intro p hp hk
    have hp' : ret p ∈ chartUnitNull r g c := hmaps hp
    have hn : (ret p).2 ≠ 0 := by
      intro hz
      have h1 := hp'.1.1
      rw [hz] at h1
      simp at h1
    have hmp : ((ret p).1, s (ret p) • (ret p).2) ∈ chartPunctured c :=
      ⟨hp'.2.1, smul_ne_zero (hpos _ hp').ne' hn⟩
    change b ((ret p).1, s (ret p) • (ret p).2) / s (ret p) = 0
    rw [hsupp _ hmp (by simpa only [hbase p hp] using hk), zero_div]

end Burnett.Geometry.UnitNullAngular
