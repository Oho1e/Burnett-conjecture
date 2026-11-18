import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

set_option autoImplicit false

noncomputable section

open Filter Metric Set
open scoped ENNReal Matrix.Norms.Operator NNReal Topology

namespace Burnett.FlatFrame

theorem exists_uniformlyConvergentSubsequenceOn_of_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] [ProperSpace Y]
    {K : Set X} (hK : IsCompact K) (f : ℕ → X → Y) (M L : ℝ≥0)
    (hbound : ∀ n x, x ∈ K → ‖f n x‖ ≤ M)
    (hlip : ∀ n, LipschitzOnWith L (f n) K) :
    ∃ (φ : ℕ → ℕ) (g : X → Y), StrictMono φ ∧
      TendstoUniformlyOn (fun n x => f (φ n) x) g atTop K ∧
      (∀ x ∈ K, ‖g x‖ ≤ M) ∧ LipschitzOnWith L g K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F (n : ℕ) : BoundedContinuousFunction K Y := BoundedContinuousFunction.mkOfCompact
    ⟨K.restrict (f n), (hlip n).to_restrict.continuous⟩
  have hf : ∀ n (x : K), F n x = f n x := fun _ _ => rfl
  have he : Equicontinuous ((↑) : range F → K → Y) := by
    have hmod : Tendsto (fun t : ℝ => (L : ℝ) * t) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun t : ℝ => (L : ℝ) * t := continuous_const.mul continuous_id
      simpa only [mul_zero] using hc.tendsto (0 : ℝ)
    apply Metric.equicontinuous_of_continuity_modulus (fun t => (L : ℝ) * t) hmod
    intro x y i
    obtain ⟨n, hn⟩ := i.property
    rw [← hn, hf, hf]
    exact (hlip n).to_restrict.dist_le_mul x y
  have hcompact : IsCompact (closure (range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : Y) M)
      (isCompact_closedBall _ _) (range F) _ he
    rintro _ x ⟨n, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, hf] using hbound n x x.property
  obtain ⟨G, _, φ, hφ, hG⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  classical
  let g (x : X) : Y := if hx : x ∈ K then G ⟨x, hx⟩ else 0
  have hg : ∀ (x : K), g x = G x := fun x => dif_pos x.property
  have ht : TendstoUniformlyOn (fun n x => f (φ n) x) g atTop K := by
    rw [tendstoUniformlyOn_iff_restrict]
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hG
    change TendstoUniformly (fun n (x : K) => f (φ n) x) (fun x : K => g x) atTop
    simpa only [Function.comp_apply, hf, hg] using h
  refine ⟨φ, g, hφ, ht, ?_, ?_⟩
  · intro x hx
    exact le_of_tendsto (ht.tendsto_at hx).norm (Eventually.of_forall fun n => hbound (φ n) x hx)
  · refine lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy => ?_
    apply le_of_tendsto ((ht.tendsto_at hx).dist (ht.tendsto_at hy))
    exact Eventually.of_forall fun n => (hlip (φ n)).dist_le_mul x hx y hy

variable {ι X : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixInv_dist_le_of_bounds {A B : Matrix ι ι ℝ} (hA : IsUnit A) (hB : IsUnit B)
    (M : ℝ≥0) (hAm : ‖A⁻¹‖ ≤ M) (hBm : ‖B⁻¹‖ ≤ M) :
    dist A⁻¹ B⁻¹ ≤ ((M : ℝ) * M) * dist A B := by
  have hAB : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
    rw [mul_sub, sub_mul, mul_assoc A⁻¹ B B⁻¹,
      B.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det B).mp hB),
      mul_one, A.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det A).mp hA), one_mul]
  rw [dist_eq_norm, hAB, dist_eq_norm]
  calc
    ‖A⁻¹ * (B - A) * B⁻¹‖ ≤ ‖A⁻¹ * (B - A)‖ * ‖B⁻¹‖ := norm_mul_le _ _
    _ ≤ (‖A⁻¹‖ * ‖B - A‖) * ‖B⁻¹‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((M : ℝ) * ‖B - A‖) * M :=
      mul_le_mul (mul_le_mul_of_nonneg_right hAm (norm_nonneg _)) hBm
        (norm_nonneg _) (mul_nonneg M.coe_nonneg (norm_nonneg _))
    _ = ((M : ℝ) * M) * ‖A - B‖ := by rw [norm_sub_rev B A, mul_right_comm]

theorem exists_uniformFrameSubsequenceOn_of_lipschitz [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) (E : ℕ → X → Matrix ι ι ℝ) (M N L : ℝ≥0)
    (hE : ∀ n x, x ∈ K → IsUnit (E n x))
    (hbound : ∀ n x, x ∈ K → ‖E n x‖ ≤ M)
    (hinv : ∀ n x, x ∈ K → ‖(E n x)⁻¹‖ ≤ N)
    (hlip : ∀ n, LipschitzOnWith L (E n) K) :
    ∃ (φ : ℕ → ℕ) (F : X → Matrix ι ι ℝ), StrictMono φ ∧
      TendstoUniformlyOn (fun n x => E (φ n) x) F atTop K ∧
      TendstoUniformlyOn (fun n x => (E (φ n) x)⁻¹) (fun x => (F x)⁻¹) atTop K ∧
      (∀ x ∈ K, IsUnit (F x) ∧ ‖F x‖ ≤ M ∧ ‖(F x)⁻¹‖ ≤ N) ∧
      LipschitzOnWith L F K ∧
      LipschitzOnWith (N * N * L) (fun x => (F x)⁻¹) K := by
  have hil (n : ℕ) : LipschitzOnWith (N * N * L) (fun x => (E n x)⁻¹) K := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy => ?_
    calc
      dist (E n x)⁻¹ (E n y)⁻¹ ≤ ((N : ℝ) * N) * dist (E n x) (E n y) :=
        matrixInv_dist_le_of_bounds (hE n x hx) (hE n y hy) N (hinv n x hx) (hinv n y hy)
      _ ≤ ((N : ℝ) * N) * ((L : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left ((hlip n).dist_le_mul x hx y hy) (mul_nonneg N.coe_nonneg N.coe_nonneg)
      _ = ↑(N * N * L) * dist x y := by simp only [NNReal.coe_mul, mul_assoc]
  let P (n : ℕ) (x : X) := (E n x, (E n x)⁻¹)
  have hab : ∀ n x, x ∈ K → ‖P n x‖ ≤ (max M N : ℝ≥0) := by
    intro n x hx
    exact max_le_max (hbound n x hx) (hinv n x hx)
  have hal : ∀ n, LipschitzOnWith (max L (N * N * L)) (P n) K := by
    intro n
    refine lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy => ?_
    change max (dist (E n x) (E n y)) (dist (E n x)⁻¹ (E n y)⁻¹) ≤ _
    exact max_le
      (((hlip n).dist_le_mul x hx y hy).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left L (N * N * L)) dist_nonneg))
      (((hil n).dist_le_mul x hx y hy).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right L (N * N * L)) dist_nonneg))
  obtain ⟨φ, G, hφ, hG, _, _⟩ :=
    exists_uniformlyConvergentSubsequenceOn_of_lipschitz hK P (max M N) (max L (N * N * L)) hab hal
  let F := Prod.fst ∘ G
  let H := Prod.snd ∘ G
  have htF : TendstoUniformlyOn (fun n x => E (φ n) x) F atTop K :=
    uniformContinuous_fst.comp_tendstoUniformlyOn hG
  have htH : TendstoUniformlyOn (fun n x => (E (φ n) x)⁻¹) H atTop K :=
    uniformContinuous_snd.comp_tendstoUniformlyOn hG
  have hprod : ∀ x ∈ K, H x * F x = 1 := by
    intro x hx
    have hlim := (htH.tendsto_at hx).mul (htF.tendsto_at hx)
    have hone : (fun n => (E (φ n) x)⁻¹ * E (φ n) x) = (fun _ => (1 : Matrix ι ι ℝ)) := by
      funext n
      exact (E (φ n) x).nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det _).mp (hE (φ n) x hx))
    rw [hone] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hinvEq (x : X) (hx : x ∈ K) : (F x)⁻¹ = H x := Matrix.inv_eq_left_inv (hprod x hx)
  have htInv : TendstoUniformlyOn (fun n x => (E (φ n) x)⁻¹) (fun x => (F x)⁻¹) atTop K :=
    htH.congr_right (fun x hx => (hinvEq x hx).symm)
  refine ⟨φ, F, hφ, htF, htInv, ?_, ?_, ?_⟩
  · intro x hx
    have hu : IsUnit (F x) := ⟨⟨F x, H x, Matrix.mul_eq_one_comm.mp (hprod x hx), hprod x hx⟩, rfl⟩
    exact ⟨hu,
      le_of_tendsto (htF.tendsto_at hx).norm (Eventually.of_forall fun n => hbound (φ n) x hx),
      le_of_tendsto (htInv.tendsto_at hx).norm (Eventually.of_forall fun n => hinv (φ n) x hx)⟩
  · refine lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy => ?_
    exact le_of_tendsto ((htF.tendsto_at hx).dist (htF.tendsto_at hy))
      (Eventually.of_forall fun n => (hlip (φ n)).dist_le_mul x hx y hy)
  · refine lipschitzOnWith_iff_dist_le_mul.mpr fun x hx y hy => ?_
    exact le_of_tendsto ((htInv.tendsto_at hx).dist (htInv.tendsto_at hy))
      (Eventually.of_forall fun n => (hil (φ n)).dist_le_mul x hx y hy)

theorem exists_uniformFrameSubsequenceOn_closedBall
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    (c : V) (r : ℝ) (E : ℕ → V → Matrix ι ι ℝ) (M N L : ℝ≥0)
    (hE : ∀ n x, x ∈ closedBall c r → IsUnit (E n x))
    (hbound : ∀ n x, x ∈ closedBall c r → ‖E n x‖ ≤ M)
    (hinv : ∀ n x, x ∈ closedBall c r → ‖(E n x)⁻¹‖ ≤ N)
    (hdiff : ∀ n x, x ∈ closedBall c r → DifferentiableAt ℝ (E n) x)
    (hderiv : ∀ n x, x ∈ closedBall c r → ‖fderiv ℝ (E n) x‖₊ ≤ L) :
    ∃ (φ : ℕ → ℕ) (F : V → Matrix ι ι ℝ), StrictMono φ ∧
      TendstoUniformlyOn (fun n x => E (φ n) x) F atTop (closedBall c r) ∧
      TendstoUniformlyOn (fun n x => (E (φ n) x)⁻¹) (fun x => (F x)⁻¹) atTop (closedBall c r) ∧
      (∀ x ∈ closedBall c r, IsUnit (F x) ∧ ‖F x‖ ≤ M ∧ ‖(F x)⁻¹‖ ≤ N) ∧
      LipschitzOnWith L F (closedBall c r) ∧
      LipschitzOnWith (N * N * L) (fun x => (F x)⁻¹) (closedBall c r) :=
  exists_uniformFrameSubsequenceOn_of_lipschitz (isCompact_closedBall c r) E M N L hE hbound hinv
    fun n => (convex_closedBall c r).lipschitzOnWith_of_nnnorm_fderiv_le (hdiff n) (hderiv n)

theorem euclideanOpNorm_le_card_mul_of_basis_bound
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (D : EuclideanSpace ℝ ι →L[ℝ] Y) (L : ℝ≥0)
    (hD : ∀ a, ‖D (EuclideanSpace.single a 1)‖ ≤ L) :
    ‖D‖₊ ≤ (Fintype.card ι : ℝ≥0) * L := by
  exact_mod_cast D.opNorm_le_bound (mul_nonneg (Nat.cast_nonneg _) L.coe_nonneg) (fun v => by
    have hv : (∑ a, v a • D (EuclideanSpace.single a 1)) = D v := by
      let e := (EuclideanSpace.basisFun ι ℝ).toBasis
      have hrepr (a : ι) : e.repr v a = v a := rfl
      have hb (a : ι) : e a = EuclideanSpace.single a 1 := EuclideanSpace.basisFun_apply _ _ a
      have hsum := congrArg D (e.sum_repr v)
      simpa only [map_sum, map_smul, hrepr, hb] using hsum
    calc
      ‖D v‖ = ‖∑ a, v a • D (EuclideanSpace.single a 1)‖ := by rw [hv]
      _ ≤ ∑ a, ‖v a • D (EuclideanSpace.single a 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : ι, (L : ℝ) * ‖v‖ := by
        apply Finset.sum_le_sum
        intro a _
        rw [norm_smul, mul_comm (L : ℝ)]
        exact mul_le_mul (PiLp.norm_apply_le v a) (hD a) (norm_nonneg _) (norm_nonneg _)
      _ = ((Fintype.card ι : ℝ) * L) * ‖v‖ := by simp [mul_assoc])

theorem exists_uniformFrameSubsequenceOn_closedBall_of_parallel
    (c : EuclideanSpace ℝ ι) (r : ℝ) (E : ℕ → EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (Γ : ℕ → EuclideanSpace ℝ ι → ι → Matrix ι ι ℝ) (M N C : ℝ≥0)
    (hE : ∀ n x, x ∈ closedBall c r → IsUnit (E n x))
    (hbound : ∀ n x, x ∈ closedBall c r → ‖E n x‖ ≤ M)
    (hinv : ∀ n x, x ∈ closedBall c r → ‖(E n x)⁻¹‖ ≤ N)
    (hdiff : ∀ n x, x ∈ closedBall c r → DifferentiableAt ℝ (E n) x)
    (hΓ : ∀ n x, x ∈ closedBall c r → ∀ a, ‖Γ n x a‖ ≤ C)
    (hparallel : ∀ n x, x ∈ closedBall c r → ∀ a,
      fderiv ℝ (E n) x (EuclideanSpace.single a 1) = -(Γ n x a * E n x)) :
    ∃ (φ : ℕ → ℕ) (F : EuclideanSpace ℝ ι → Matrix ι ι ℝ), StrictMono φ ∧
      TendstoUniformlyOn (fun n x => E (φ n) x) F atTop (closedBall c r) ∧
      TendstoUniformlyOn (fun n x => (E (φ n) x)⁻¹) (fun x => (F x)⁻¹) atTop (closedBall c r) ∧
      (∀ x ∈ closedBall c r, IsUnit (F x) ∧ ‖F x‖ ≤ M ∧ ‖(F x)⁻¹‖ ≤ N) ∧
      LipschitzOnWith ((Fintype.card ι : ℝ≥0) * (C * M)) F (closedBall c r) ∧
      LipschitzOnWith (N * N * ((Fintype.card ι : ℝ≥0) * (C * M)))
        (fun x => (F x)⁻¹) (closedBall c r) := by
  apply exists_uniformFrameSubsequenceOn_closedBall c r E M N _ hE hbound hinv hdiff
  intro n x hx
  apply euclideanOpNorm_le_card_mul_of_basis_bound
  intro a
  rw [hparallel n x hx a, norm_neg, NNReal.coe_mul]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (hΓ n x hx a) (hbound n x hx) (norm_nonneg _) C.coe_nonneg)

theorem uniformFrameLimit_eq_at_fixed_point [PseudoMetricSpace X] {K : Set X}
    {E : ℕ → X → Matrix ι ι ℝ} {F : X → Matrix ι ι ℝ} {φ : ℕ → ℕ}
    (h : TendstoUniformlyOn (fun n x => E (φ n) x) F atTop K)
    {x : X} (hx : x ∈ K) {A : Matrix ι ι ℝ} (hE : ∀ n, E n x = A) : F x = A := by
  have ht := h.tendsto_at hx
  simp only [hE] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem matrixEntry_norm_le (A : Matrix ι ι ℝ) (a b : ι) : ‖A a b‖ ≤ ‖A‖ := by
  have hsum : ‖A a b‖₊ ≤ ∑ j, ‖A a j‖₊ :=
    Finset.single_le_sum (fun j _ => zero_le ‖A a j‖₊) (Finset.mem_univ b)
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast hsum.trans <| Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ a)

theorem tendstoUniformlyOn_matrixEntry [UniformSpace X] {K : Set X}
    {E : ℕ → X → Matrix ι ι ℝ} {F : X → Matrix ι ι ℝ}
    (h : TendstoUniformlyOn E F atTop K) (a b : ι) :
    TendstoUniformlyOn (fun n x => E n x a b) (fun x => F x a b) atTop K := by
  have hentry : LipschitzWith 1 (fun A : Matrix ι ι ℝ => A a b) := by
    refine lipschitzWith_iff_dist_le_mul.mpr fun A B => ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact matrixEntry_norm_le (A - B) a b
  exact hentry.uniformContinuous.comp_tendstoUniformlyOn h

theorem norm_le_on_open_of_ae {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [NormedAddCommGroup Y] (μ : MeasureTheory.Measure X)
    [μ.IsOpenPosMeasure] {U : Set X} (hU : IsOpen U) {f : X → Y} (hf : ContinuousOn f U)
    {M : ℝ} (hM : ∀ᵐ x ∂μ.restrict U, ‖f x‖ ≤ M) : ∀ x ∈ U, ‖f x‖ ≤ M := by
  have heq : (fun x => max ‖f x‖ M) =ᵐ[μ.restrict U] (fun _ => M) :=
    hM.mono fun _ hx => max_eq_right hx
  have h := MeasureTheory.Measure.eqOn_open_of_ae_eq heq hU
    (hf.norm.sup continuousOn_const) continuousOn_const
  exact fun x hx => (le_max_left ‖f x‖ M).trans_eq (h hx)

theorem norm_le_on_open_of_eLpNorm_top {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [NormedAddCommGroup Y] (μ : MeasureTheory.Measure X)
    [μ.IsOpenPosMeasure] {U : Set X} (hU : IsOpen U) {f : X → Y} (hf : ContinuousOn f U)
    {M : ℝ≥0} (hM : MeasureTheory.eLpNorm f ⊤ (μ.restrict U) ≤ (M : ℝ≥0∞)) :
    ∀ x ∈ U, ‖f x‖ ≤ M := by
  apply norm_le_on_open_of_ae μ hU hf
  rw [MeasureTheory.eLpNorm_exponent_top] at hM
  filter_upwards [MeasureTheory.enorm_ae_le_eLpNormEssSup f (μ.restrict U)] with x hx
  exact_mod_cast (show (‖f x‖₊ : ℝ≥0∞) ≤ (M : ℝ≥0∞) from hx.trans hM)

theorem continuousOn_matrixInv_of_isUnit [TopologicalSpace X] {U : Set X}
    {E : X → Matrix ι ι ℝ} (hE : ContinuousOn E U) (hu : ∀ x ∈ U, IsUnit (E x)) :
    ContinuousOn (fun x => (E x)⁻¹) U := by
  intro x hx
  apply (continuousAt_matrix_inv (E x) ?_).comp_continuousWithinAt (hE x hx)
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (hu x hx)))

theorem exists_uniformFrameSubsequenceOn_smallerClosedBall_of_parallel
    (c : EuclideanSpace ℝ ι) {r R : ℝ} (hrR : r < R)
    (E : ℕ → EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (Γ : ℕ → EuclideanSpace ℝ ι → ι → Matrix ι ι ℝ) (M N C : ℝ≥0)
    (hE : ∀ n x, x ∈ ball c R → IsUnit (E n x))
    (hdiff : ∀ n x, x ∈ ball c R → DifferentiableAt ℝ (E n) x)
    (hcontΓ : ∀ n a, ContinuousOn (fun x => Γ n x a) (ball c R))
    (hbound : ∀ n, MeasureTheory.eLpNorm (E n) ⊤
      (MeasureTheory.volume.restrict (ball c R)) ≤ (M : ℝ≥0∞))
    (hinv : ∀ n, MeasureTheory.eLpNorm (fun x => (E n x)⁻¹) ⊤
      (MeasureTheory.volume.restrict (ball c R)) ≤ (N : ℝ≥0∞))
    (hΓ : ∀ n a, MeasureTheory.eLpNorm (fun x => Γ n x a) ⊤
      (MeasureTheory.volume.restrict (ball c R)) ≤ (C : ℝ≥0∞))
    (hparallel : ∀ n x, x ∈ ball c R → ∀ a,
      fderiv ℝ (E n) x (EuclideanSpace.single a 1) = -(Γ n x a * E n x)) :
    ∃ (φ : ℕ → ℕ) (F : EuclideanSpace ℝ ι → Matrix ι ι ℝ), StrictMono φ ∧
      TendstoUniformlyOn (fun n x => E (φ n) x) F atTop (closedBall c r) ∧
      TendstoUniformlyOn (fun n x => (E (φ n) x)⁻¹) (fun x => (F x)⁻¹) atTop (closedBall c r) ∧
      (∀ x ∈ closedBall c r, IsUnit (F x) ∧ ‖F x‖ ≤ M ∧ ‖(F x)⁻¹‖ ≤ N) ∧
      LipschitzOnWith ((Fintype.card ι : ℝ≥0) * (C * M)) F (closedBall c r) ∧
      LipschitzOnWith (N * N * ((Fintype.card ι : ℝ≥0) * (C * M)))
        (fun x => (F x)⁻¹) (closedBall c r) := by
  have hs : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hc n : ContinuousOn (E n) (ball c R) :=
    fun x hx => (hdiff n x hx).continuousAt.continuousWithinAt
  apply exists_uniformFrameSubsequenceOn_closedBall_of_parallel c r E Γ M N C
    (fun n x hx => hE n x (hs hx)) ?_ ?_ (fun n x hx => hdiff n x (hs hx)) ?_
    (fun n x hx => hparallel n x (hs hx))
  · intro n x hx
    exact norm_le_on_open_of_eLpNorm_top MeasureTheory.volume isOpen_ball (hc n) (hbound n) x (hs hx)
  · intro n x hx
    have hi := continuousOn_matrixInv_of_isUnit (hc n) (hE n)
    exact norm_le_on_open_of_eLpNorm_top MeasureTheory.volume isOpen_ball hi (hinv n) x (hs hx)
  · intro n x hx a
    exact norm_le_on_open_of_eLpNorm_top MeasureTheory.volume isOpen_ball (hcontΓ n a) (hΓ n a) x (hs hx)

end Burnett.FlatFrame
