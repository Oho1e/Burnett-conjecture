import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical
import Burnett.Analysis.Microlocal.Overlap.LeftActionPairingBounds
import Burnett.Analysis.Microlocal.SpatialSquarePartition

/-! A finite spatial partition for the actual order-zero pairings. -/

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (coeffMul coeffMul_toLp physicalCoefficient)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ComplexConjugate ContDiff FourierTransform InnerProduct Topology

open private compactOperator_tendsto_zero_of_weakL2 inner_tendsto_zero_of_bounded_of_tendsto_zero
  from Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical
open private pairing_coeffMul_left from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

private theorem coeffMul_eq_of_one_on (c : D) {K : Set E}
    (hc : ∀ x ∈ K, (c : E → ℝ) x = 1) (v : SchwartzMap E ℂ)
    (hv : tsupport (v : E → ℂ) ⊆ K) : coeffMul c v = v := by
  ext x
  change ((c : E → ℝ) x : ℂ) * v x = v x
  by_cases hx : x ∈ K
  · rw [hc x hx, Complex.ofReal_one, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hv h)), mul_zero]

/-- On a common compact base window, a real smooth partition by squares splits
one actual classical pairing into the sum of its doubly localized pairings.
The error tends to zero on the prescribed bounded and right weak-null inputs. -/
theorem tendsto_classicalPairing_sub_squareCutoffSum
    {ι : Type*} [Fintype ι] (χ : ι → D) (K : Set E) (hK : IsCompact K)
    (hSum : ∀ x ∈ K, ∑ i, (χ i : E → ℝ) x ^ 2 = 1)
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (T : ComplexL2 E →L[ℂ] ComplexL2 E) (L : Set E) (hT : HasLocalClassicalRepresentation T a L)
    (u v : ℕ → SchwartzMap E ℂ) (hUS : ∀ n, tsupport (u n : E → ℂ) ⊆ K)
    (hVS : ∀ n, tsupport (v n : E → ℂ) ⊆ K) (hVL : ∀ n, tsupport (v n : E → ℂ) ⊆ L)
    (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁)
    (hU : ∀ n, ‖(u n).toLp 2 volume‖ ≤ B₁) (hV : ∀ n, ‖(v n).toLp 2 volume‖ ≤ B₂)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((v n).toLp 2 volume)) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ ((u n).toLp 2 volume) (T ((v n).toLp 2 volume)) -
      ∑ i, inner ℂ ((coeffMul (χ i) (u n)).toLp 2 volume)
        (T ((coeffMul (χ i) (v n)).toLp 2 volume))) atTop (𝓝 0) := by
  classical
  obtain ⟨R, hR, hRep⟩ := hT
  let Q (c : D) (n : ℕ) := inner ℂ ((coeffMul c (u n)).toLp 2 volume)
    (T ((coeffMul c (v n)).toLp 2 volume))
  let P (c : D) (n : ℕ) := ∫ x, conj (coeffMul c (coeffMul c (u n)) x) * firstOrderAction a (v n) x
  have hDiff (c : D) : Tendsto (fun n => Q c n - P c n) atTop (𝓝 0) := by
    let f (n : ℕ) := (coeffMul c (u n)).toLp 2 volume
    let g (n : ℕ) := (coeffMul c (v n)).toLp 2 volume
    have hBf (n : ℕ) : ‖f n‖ ≤ (physicalCoefficient c).bound * B₁ := by
      dsimp only [f]
      rw [coeffMul_toLp]
      exact (symbolL2_norm_le _ _).trans (mul_le_mul_of_nonneg_left (hU n)
        (physicalCoefficient c).bound_nonneg)
    have hBg (n : ℕ) : ‖g n‖ ≤ (physicalCoefficient c).bound * B₂ := by
      dsimp only [g]
      rw [coeffMul_toLp]
      exact (symbolL2_norm_le _ _).trans (mul_le_mul_of_nonneg_left (hV n)
        (physicalCoefficient c).bound_nonneg)
    have hWg (w : ComplexL2 E) : Tendsto (fun n => inner ℂ w (g n)) atTop (𝓝 0) := by
      have heq (n : ℕ) : inner ℂ w (g n) = inner ℂ ((symbolCLM (physicalCoefficient c)).adjoint w)
          ((v n).toLp 2 volume) := by
        dsimp only [g]
        rw [coeffMul_toLp, ContinuousLinearMap.adjoint_inner_left]
      simpa only [heq] using hw ((symbolCLM (physicalCoefficient c)).adjoint w)
    have hSmall := inner_tendsto_zero_of_bounded_of_tendsto_zero f (fun n => R (g n)) _ hBf
      (compactOperator_tendsto_zero_of_weakL2 R hR g _ hBg hWg)
    have hPrincipal := tendsto_infraredAngularPrincipal_twoCutoff_difference a S hS hSupport hJoint
      hZero hDegree c c u v K hK hVS B₁ B₂ hB₁ hU hV hw
    have hCombined := hSmall.add hPrincipal
    rw [zero_add] at hCombined
    apply hCombined.congr
    intro n
    have hVLoc : tsupport (coeffMul c (v n) : E → ℂ) ⊆ L :=
      tsupport_mul_subset_right.trans (hVL n)
    change _ = Q c n - P c n
    dsimp only [Q, P]
    rw [hRep _ _ hVLoc, ← pairing_coeffMul_left c c a (u n) (v n)]
    dsimp only [f, g]
    ring
  obtain ⟨b, hb, hKb⟩ := hK.isBounded.subset_closedBall_lt (0 : ℝ) (0 : E)
  let e : ContDiffBump (0 : E) := ⟨b, b + 1, hb, by linarith⟩
  let cut : D := ⟨e, e.contDiff, e.hasCompactSupport⟩
  have he (x : E) (hx : x ∈ K) : (cut : E → ℝ) x = 1 := e.one_of_mem_closedBall (hKb hx)
  have hUc (n : ℕ) : coeffMul cut (u n) = u n := coeffMul_eq_of_one_on cut he (u n) (hUS n)
  have hVc (n : ℕ) : coeffMul cut (v n) = v n := coeffMul_eq_of_one_on cut he (v n) (hVS n)
  have hA := hJoint.continuousOn
  have hMeas := measurable_baseAngularSymbol
    (fun ξ => (contDiff_baseAngularSection a hJoint hZero ξ).continuous)
    (fun x => hA.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hξ => ⟨mem_univ x, hξ⟩))
  obtain ⟨C, hC⟩ := exists_uniform_baseDerivative_of_homogeneousAngular a S hS hSupport hJoint
    hZero hDegree 0
  have hNorm (x ξ : E) : ‖a x ξ‖ ≤ C := by simpa only [norm_iteratedFDeriv_zero] using hC.2 x ξ
  have hPsum (n : ℕ) : P cut n = ∑ i, P (χ i) n := by
    dsimp only [P]
    simp only [hUc n]
    rw [← integral_finset_sum]
    · apply integral_congr_ae
      filter_upwards with x
      have hf (c : D) : conj (coeffMul c (coeffMul c (u n)) x) =
          ((c : E → ℝ) x ^ 2 : ℝ) * conj (u n x) := by
        change conj (((c : E → ℝ) x : ℂ) * (((c : E → ℝ) x : ℂ) * u n x)) = _
        push_cast
        simp only [map_mul, Complex.conj_ofReal]
        ring
      simp only [hf, mul_assoc, ← Finset.sum_mul]
      by_cases hx : x ∈ K
      · have hs : ∑ i, (((χ i : E → ℝ) x ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast hSum x hx
        rw [hs, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hUS n h))]
        simp
    · exact fun i _ => integrable_tested_bounded_leftAction a hMeas C hNorm
        (v n) (coeffMul (χ i) (coeffMul (χ i) (u n)))
  have hL := (hDiff cut).sub (tendsto_finset_sum Finset.univ (fun i _ => hDiff (χ i)))
  simp only [Finset.sum_const_zero, sub_zero] at hL
  apply hL.congr
  intro n
  change (Q cut n - P cut n) - (∑ i, (Q (χ i) n - P (χ i) n)) = _
  rw [Finset.sum_sub_distrib, ← hPsum]
  have hCut : Q cut n = inner ℂ ((u n).toLp 2 volume) (T ((v n).toLp 2 volume)) := by
    dsimp only [Q]
    rw [hUc, hVc]
  rw [← hCut]
  dsimp only [Q]
  ring

/-- The spatial square cutoffs of a compact window can be chosen inside the
members of a given open cover, indexed by finitely many selected members. -/
theorem exists_squareCutoffs_subordinateTo_openCover {ι : Type*}
    (V : ι → Set E) (hV : ∀ i, IsOpen (V i)) (K : Set E) (hK : IsCompact K)
    (hCover : K ⊆ ⋃ i, V i) :
    ∃ (n : ℕ) (idx : Fin n → ι) (χ : Fin n → D),
      (∀ i, tsupport (χ i : E → ℝ) ⊆ V (idx i)) ∧
      (∀ x ∈ K, ∑ i, (χ i : E → ℝ) x ^ 2 = 1) := by
  classical
  choose idx hidx using fun x : K => mem_iUnion.mp (hCover x.property)
  let U (x : E) := if hx : x ∈ K then V (idx ⟨x, hx⟩) else ∅
  have hU (x : E) (hx : x ∈ K) : U x ∈ 𝓝 x := by
    change (if h : x ∈ K then V (idx ⟨x, h⟩) else ∅) ∈ 𝓝 x
    rw [dif_pos hx]
    exact (hV _).mem_nhds (hidx ⟨x, hx⟩)
  obtain ⟨n, c, χ, hc, hd, hcs, hsub, hsum⟩ :=
    Burnett.Microlocal.SmoothSquarePartition.exists_subordinate_smooth_square_partition K hK U hU
  refine ⟨n, fun i => idx ⟨c i, hc i⟩, fun i => ⟨χ i, hd i, hcs i⟩, ?_, hsum⟩
  intro i
  simpa only [U, dif_pos (hc i)] using hsub i

end Burnett.Microlocal.Overlap
