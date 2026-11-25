import Burnett.Analysis.Microlocal.Overlap.AngularOrderMinusOneQuantization
import Burnett.Analysis.Microlocal.Overlap.CompactParameterIntegral
import Burnett.Analysis.PrincipalEnergy.Localization.IntegratedSymbolJets
import Burnett.Analysis.PrincipalEnergy.Localization.ProductPartialJets

/-! The actual left Fourier symbol of a smooth compact displacement kernel. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set
open Burnett.Analysis.CarlesonEmbedding
  (contDiff_firstPartialJet contDiff_integral_of_locally_dominated_jets)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ContDiff FourierTransform InnerProduct Topology

/-- Fourier transform in the displacement `z`, with kernel action
`u ↦ ∫ z, k x z * u (x - z)`. -/
def displacementKernelLeftSymbol (k : E → E → ℂ) (x ξ : E) : ℂ :=
  𝓕 (k x) ξ

theorem displacementKernelLeftSymbol_tsupport {k : E → E → ℂ} {S T : Set E}
    (hS : IsClosed S) (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T) (ξ : E) :
    tsupport (fun x => displacementKernelLeftSymbol k x ξ) ⊆ S := by
  apply closure_minimal _ hS
  intro x hx
  by_contra hxS
  have hZero : k x = 0 := funext fun z => by
    change uncurry k (x, z) = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hxS (hSupp h).1)
  exact hx (by simp [displacementKernelLeftSymbol, hZero, Real.fourierIntegral_eq'])

theorem contDiff_displacementKernelLeftSymbol {k : E → E → ℂ} {S T : Set E}
    (hT : IsCompact T) (hK : ContDiff ℝ ∞ (uncurry k))
    (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T) :
    ContDiff ℝ ∞ (uncurry (displacementKernelLeftSymbol k)) := by
  let phase (ξ z : E) := Complex.exp ((↑(-2 * Real.pi * inner ℝ z ξ) : ℂ) * Complex.I)
  let G (q : (E × E) × E) := phase q.1.2 q.2 * k q.1.1 q.2
  have hInner : ContDiff ℝ ∞ (fun q : (E × E) × E => inner ℝ q.2 q.1.2) :=
    contDiff_snd.inner ℝ (contDiff_snd.comp contDiff_fst)
  have hArg : ContDiff ℝ ∞ (fun q : (E × E) × E => -2 * Real.pi * inner ℝ q.2 q.1.2) :=
    contDiff_const.mul hInner
  have hPhase : ContDiff ℝ ∞ (fun q : (E × E) × E => phase q.1.2 q.2) :=
    ((Complex.ofRealCLM.contDiff.comp hArg).mul contDiff_const).cexp
  have hG : ContDiff ℝ ∞ G :=
    hPhase.mul (hK.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd))
  have hI := Burnett.Analysis.contDiffOn_integral_compact_parameter (volume : Measure E)
    T hT G univ isOpen_univ hG.contDiffOn
  apply contDiffOn_univ.mp
  refine hI.congr fun q _ => ?_
  rw [uncurry, displacementKernelLeftSymbol, Real.fourierIntegral_eq']
  change (∫ z, phase q.2 z • k q.1 z) = ∫ z in T, phase q.2 z * k q.1 z
  simp only [smul_eq_mul]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
    have hZero : k q.1 z = 0 := by
      change uncurry k (q.1, z) = 0
      exact image_eq_zero_of_notMem_tsupport (fun h => hz (hSupp h).2)
    rw [hZero, mul_zero]).symm

private theorem firstPartialJet_zero_of_notMem {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × E → F) {S T : Set E} (hS : IsClosed S)
    (hSupp : ∀ q ∉ S ×ˢ T, f q = 0) (n : ℕ) {q : E × E} (hq : q ∉ S ×ˢ T) :
    iteratedFDeriv ℝ n (fun x => f (x, q.2)) q.1 = 0 := by
  by_cases hz : q.2 ∈ T
  · have hx : q.1 ∉ S := fun hx => hq ⟨hx, hz⟩
    have hS' : tsupport (fun x => f (x, q.2)) ⊆ S := by
      apply closure_minimal _ hS
      intro x hx'
      by_contra hxS
      exact hx' (hSupp (x, q.2) fun h => hxS h.1)
    by_contra hNonzero
    exact hx (hS' (support_iteratedFDeriv_subset n hNonzero))
  · have hEq : (fun x => f (x, q.2)) = fun _ => (0 : F) := funext fun x =>
      hSupp (x, q.2) fun h => hz h.2
    simp [hEq]

private theorem exists_compactKernel_majorant {F : Type*} [NormedAddCommGroup F]
    (f : E × E → F) {S T : Set E} (hS : IsCompact S) (hT : IsCompact T)
    (hF : Continuous f) (hSupp : ∀ q ∉ S ×ˢ T, f q = 0) :
    ∃ B : E → ℝ, Integrable B ∧ ∀ x z, ‖f (x, z)‖ ≤ B z := by
  obtain ⟨C, hC⟩ := ((hS.prod hT).image hF).isBounded.exists_norm_le
  let B : E → ℝ := T.indicator (fun _ => max 0 C)
  have hC' : IntegrableOn (fun _ : E => max 0 C) T := integrableOn_const hT.measure_lt_top.ne
  refine ⟨B, hC'.integrable_indicator hT.measurableSet, ?_⟩
  intro x z
  by_cases hz : z ∈ T
  · rw [show B z = max 0 C from indicator_of_mem hz _]
    by_cases hx : x ∈ S
    · exact (hC _ (mem_image_of_mem f (show (x, z) ∈ S ×ˢ T from ⟨hx, hz⟩))).trans (le_max_right _ _)
    · rw [hSupp _ (fun h => hx h.1), norm_zero]
      exact le_max_left _ _
  · rw [show B z = 0 from indicator_of_notMem hz _, hSupp _ (fun h => hz h.2), norm_zero]

private abbrev BaseJet (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ

private def kernelBaseJet (k : E → E → ℂ) (n : ℕ) (q : E × E) : BaseJet n :=
  iteratedFDeriv ℝ n (fun x => k x q.2) q.1

private theorem kernelBaseJet_zero_of_notMem {k : E → E → ℂ} {S T : Set E}
    (hS : IsClosed S) (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T)
    (n : ℕ) {q : E × E} (hq : q ∉ S ×ˢ T) : kernelBaseJet k n q = 0 :=
  firstPartialJet_zero_of_notMem (uncurry k) hS
    (fun _ hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hSupp h))) n hq

/-- Each iterated base derivative passes through the compact displacement integral. -/
theorem iteratedFDeriv_displacementKernelLeftSymbol {k : E → E → ℂ} {S T : Set E}
    (hS : IsCompact S) (hT : IsCompact T) (hK : ContDiff ℝ ∞ (uncurry k))
    (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T) (n : ℕ) (x ξ : E) :
    iteratedFDeriv ℝ n (fun y => displacementKernelLeftSymbol k y ξ) x =
      𝓕 (fun z => iteratedFDeriv ℝ n (fun y => k y z) x) ξ := by
  let phase (z : E) : ℂ := Complex.exp ((↑(-2 * Real.pi * inner ℝ z ξ) : ℂ) * Complex.I)
  let u (z y : E) : ℂ := phase z • k y z
  have hKz (z : E) : ContDiff ℝ ∞ (fun y => k y z) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  have hu (z : E) : ContDiff ℝ ∞ (u z) := (hKz z).const_smul (phase z)
  have hD (m : ℕ) (y z : E) :
      iteratedFDeriv ℝ m (u z) y = phase z • kernelBaseJet k m (y, z) := by
    have hOrder : (m : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    exact iteratedFDeriv_const_smul_apply' (a := phase z) ((hKz z).contDiffAt.of_le hOrder)
  have hJet (m : ℕ) : ContDiff ℝ ∞ (kernelBaseJet k m) := contDiff_firstPartialJet hK m
  have hPhase : Continuous phase :=
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const))
  have hMeas (m : ℕ) (y : E) :
      AEStronglyMeasurable (fun z => iteratedFDeriv ℝ m (u z) y) (volume : Measure E) := by
    simp only [hD]
    exact (hPhase.smul ((hJet m).continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  have hDom (m : ℕ) (y : E) : ∃ B : E → ℝ, Integrable B ∧
      ∀ z w, w ∈ Metric.ball y 1 → ‖iteratedFDeriv ℝ m (u z) w‖ ≤ B z := by
    obtain ⟨B, hB, hBound⟩ := exists_compactKernel_majorant (kernelBaseJet k m) hS hT
      (hJet m).continuous (fun _ h => kernelBaseJet_zero_of_notMem hS.isClosed hSupp m h)
    refine ⟨B, hB, fun z w _ => ?_⟩
    rw [hD, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hBound w z
  have hEq : (fun y => displacementKernelLeftSymbol k y ξ) = fun y => ∫ z, u z y := by
    funext y
    exact Real.fourierIntegral_eq' (k y) ξ
  rw [hEq, (contDiff_integral_of_locally_dominated_jets volume u hu hMeas hDom).2 n x,
    Real.fourierIntegral_eq']
  exact integral_congr_ae (Eventually.of_forall fun z => hD n x z)

/-- Smoothness and compact support of the kernel control the order-minus-one
estimate uniformly in the base, for every base derivative. -/
theorem orderMinusOneBounds_displacementKernelLeftSymbol {k : E → E → ℂ} {S T : Set E}
    (hS : IsCompact S) (hT : IsCompact T) (hK : ContDiff ℝ ∞ (uncurry k))
    (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T) :
    OrderMinusOneBounds (displacementKernelLeftSymbol k) := by
  intro n
  let F := kernelBaseJet k n
  have hF : ContDiff ℝ ∞ F := contDiff_firstPartialJet hK n
  have hZero (q : E × E) (hq : q ∉ S ×ˢ T) : F q = 0 :=
    kernelBaseJet_zero_of_notMem hS.isClosed hSupp n hq
  let G (m : ℕ) (q : E × E) := iteratedFDeriv ℝ m (fun z => F (q.1, z)) q.2
  have hSwap : ContDiff ℝ ∞ (Prod.swap : E × E → E × E) := contDiff_snd.prodMk contDiff_fst
  have hG (m : ℕ) : ContDiff ℝ ∞ (G m) :=
    (contDiff_firstPartialJet (hF.comp hSwap) m).comp hSwap
  have hGZero (m : ℕ) (q : E × E) (hq : q ∉ S ×ˢ T) : G m q = 0 :=
    firstPartialJet_zero_of_notMem (F ∘ Prod.swap) hT.isClosed
      (fun p hp => hZero p.swap (fun h => hp ⟨h.2, h.1⟩)) m (q := q.swap)
      (fun h => hq ⟨h.2, h.1⟩)
  have hDom (m : ℕ) := exists_compactKernel_majorant (G m) hS hT (hG m).continuous (hGZero m)
  choose B hBI hBB using hDom
  have hI (m : ℕ) (x : E) : Integrable (fun z => G m (x, z)) :=
    (hBI m).mono' (((hG m).continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => hBB m x z)
  have hInt (m : ℕ) (x : E) : (∫ z, ‖G m (x, z)‖) ≤ ∫ z, B m z :=
    integral_mono (hI m x).norm (hBI m) (hBB m x)
  have hNonneg (m : ℕ) : 0 ≤ ∫ z, B m z :=
    integral_nonneg fun z => (norm_nonneg (G m (0, z))).trans (hBB m 0 z)
  refine ⟨(∫ z, B 0 z) + 2 * ((∫ z, B 0 z) + ∫ z, B 1 z),
    add_nonneg (hNonneg 0) (mul_nonneg (by norm_num) (add_nonneg (hNonneg 0) (hNonneg 1))),
    fun x ξ => ?_⟩
  have hFx : ContDiff ℝ ∞ (fun z => F (x, z)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hDecay := Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le (K := 0) (N := ⊤)
    hFx (fun r m hr _ => by
      have hr' : (r : ℕ∞) ≤ ((0 : ℕ) : ℕ∞) := hr
      have hR : r = 0 := le_antisymm (ENat.coe_le_coe.mp hr') (Nat.zero_le r)
      subst r
      simpa only [pow_zero, one_mul] using (hI m x).norm)
    (k := 0) (n := 1) (by norm_num) (by exact le_top) ξ
  simp only [pow_one, pow_zero, one_mul, norm_iteratedFDeriv_zero, zero_add,
    Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.coeFn_mk,
    Finset.sum_range_succ, Finset.sum_singleton, Nat.cast_zero, mul_zero] at hDecay
  have hDecay' : ‖ξ‖ * ‖𝓕 (fun z => F (x, z)) ξ‖ ≤ 2 * ((∫ z, ‖G 0 (x, z)‖) + ∫ z, ‖G 1 (x, z)‖) := by
    simpa only [G, norm_iteratedFDeriv_zero] using hDecay
  have hBound : ‖𝓕 (fun z => F (x, z)) ξ‖ ≤ ∫ z, B 0 z := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
    simpa only [G, norm_iteratedFDeriv_zero] using hInt 0 x
  rw [iteratedFDeriv_displacementKernelLeftSymbol hS hT hK hSupp n x ξ, add_mul, one_mul]
  exact add_le_add hBound (hDecay'.trans (mul_le_mul_of_nonneg_left (add_le_add (hInt 0 x) (hInt 1 x)) (by norm_num)))

/-- A compact smooth displacement kernel has an exact order-minus-one symbol
with compact base support and zero principal part. -/
theorem displacementKernelLeftSymbol_properties {k : E → E → ℂ} {S T : Set E}
    (hS : IsCompact S) (hT : IsCompact T) (hK : ContDiff ℝ ∞ (uncurry k))
    (hSupp : tsupport (uncurry k) ⊆ S ×ˢ T) :
    (∀ ξ, tsupport (fun x => displacementKernelLeftSymbol k x ξ) ⊆ S) ∧
      ContDiff ℝ ∞ (uncurry (displacementKernelLeftSymbol k)) ∧
      OrderMinusOneBounds (displacementKernelLeftSymbol k) :=
  ⟨displacementKernelLeftSymbol_tsupport hS.isClosed hSupp,
    contDiff_displacementKernelLeftSymbol hT hK hSupp,
    orderMinusOneBounds_displacementKernelLeftSymbol hS hT hK hSupp⟩

/-- A compact smooth kernel in the two original spatial variables gives a
smooth displacement kernel, retaining the same compact base support. -/
theorem compactSmoothKernel_displacementSymbol_properties
    {r : E → E → ℂ} {S T : Set E} (hS : IsCompact S) (hT : IsCompact T)
    (hR : ContDiff ℝ ∞ (uncurry r)) (hSupp : tsupport (uncurry r) ⊆ S ×ˢ T) :
    let b := displacementKernelLeftSymbol (fun x z => r x (x - z))
    (∀ ξ, tsupport (fun x => b x ξ) ⊆ S) ∧ ContDiff ℝ ∞ (uncurry b) ∧ OrderMinusOneBounds b := by
  let k (x z : E) := r x (x - z)
  let U := (fun q : E × E => q.1 - q.2) '' (S ×ˢ T)
  have hU : IsCompact U := (hS.prod hT).image (continuous_fst.sub continuous_snd)
  have hK : ContDiff ℝ ∞ (uncurry k) := hR.comp (contDiff_fst.prodMk (contDiff_fst.sub contDiff_snd))
  have hSub : tsupport (uncurry k) ⊆ S ×ˢ U := by
    apply closure_minimal _ (hS.isClosed.prod hU.isClosed)
    intro q hq
    have hqt : (q.1, q.1 - q.2) ∈ tsupport (uncurry r) := subset_tsupport _ hq
    have hqST := hSupp hqt
    refine ⟨hqST.1, ⟨(q.1, q.1 - q.2), hqST, ?_⟩⟩
    exact sub_sub_cancel q.1 q.2
  exact displacementKernelLeftSymbol_properties hS hU hK hSub

end Burnett.Microlocal.Overlap
