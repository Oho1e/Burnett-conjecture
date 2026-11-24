import Burnett.Analysis.Microlocal.Overlap.ReceivingChartRepresentedPairing

/-! Cross-chart comparison for two separately localized inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.SeparablePositive (conjugateSymbol separableOperator)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The actual separated receiving-chart operator on two transported inputs
has, up to an error tending to zero, the source left Fourier action with
the moving inverse-adjoint covector. Both input cutoffs can be prescribed. -/
theorem tendsto_receivingSeparablePairing_sub_sourceAngularAction
    (c d : AtlasChart M) (S : Set E) (hK : IsCompact S)
    (hKU : S ⊆ (c.transition d).source) (hConv : Convex ℝ S)
    (a b m : BoundedSymbol E) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (haS : tsupport (a : E → ℂ) ⊆ S)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (u v : ℕ → SchwartzMap E ℂ) (hUS : ∀ n, tsupport (u n : E → ℂ) ⊆ S)
    (hVS : ∀ n, tsupport (v n : E → ℂ) ⊆ S)
    (hPull : ∀ n x, x ∈ tsupport (u n : E → ℂ) → a x = b (c.transition d x))
    (C₀ C₁ : ℝ) (hU : ∀ n, ‖(u n).toLp 2 volume‖ ≤ C₀) (hV : ∀ n, ‖(v n).toLp 2 volume‖ ≤ C₁)
    (hWeak : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((v n).toLp 2 volume)) atTop (𝓝 0)) :
    let U (n : ℕ) := (transportedHalfDensitySchwartz c d S hK hKU (u n) (hUS n)).toLp 2 volume
    let V (n : ℕ) := (transportedHalfDensitySchwartz c d S hK hKU (v n) (hVS n)).toLp 2 volume
    Tendsto (fun n => inner ℂ (U n) (separableOperator b (normalizedAngularSymbol m) (V n)) -
      ∫ x, conj (u n x) * firstOrderAction (fun y ξ => movingChartAngularSymbol c d a m (y, ξ)) (v n) x)
      atTop (𝓝 0) := by
  intro U₀ V₀
  let p (x ξ : E) := movingChartAngularSymbol c d a m (x,ξ)
  let l := movingChartLowSymbol c d a m
  have hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    contDiffOn_movingChartAngularSymbol c d a m ha (haS.trans hKU) hm
  have hZero : ContDiff ℝ ∞ (fun x => p x 0) := by
    simp only [p, movingChartAngularSymbol, map_zero]
    exact ha.mul contDiff_const
  have hSupp (ξ : E) : tsupport (fun x => p x ξ) ⊆ S := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra ho
    have hax : a x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := (a : E → ℂ)) (fun h => ho (haS h))
    exact hx (by simp only [p, movingChartAngularSymbol, hax, zero_mul])
  have hp : Measurable (uncurry p) :=
    measurable_baseAngularSymbol
      (fun ξ => (contDiff_baseAngularSection p hJoint hZero ξ).continuous)
      (fun x => hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hξ => ⟨mem_univ x, hξ⟩))
  have hl : Measurable (uncurry l) :=
    measurable_movingChartLowSymbol c d a m S hK hKU haS ha hm
  have hInd (n : ℕ) : S.indicator (v n : E → ℂ) = v n := by
    funext x
    by_cases hx : x ∈ S
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hVS n h))).symm
  have hF (n : ℕ) : Integrable (𝓕 (S.indicator (v n : E → ℂ))) := by
    rw [hInd]
    exact (SchwartzMap.fourierTransformCLM ℂ (v n)).integrable
  have hTf (n : ℕ) : Integrable (𝓕 (transportedHalfDensity c d S (v n))) :=
    (SchwartzMap.fourierTransformCLM ℂ
      (transportedHalfDensitySchwartz c d S hK hKU (v n) (hVS n))).integrable
  obtain ⟨L, hL, hLt⟩ := exists_movingChartLowAction_strongZero c d a m S hK hKU haS ha hm
    v C₁ hV hWeak
  obtain ⟨D, hD, hDt⟩ := exists_localizedNormalizedAngularDifference_strongZero c d S
    hK hKU hConv m hm hd v hF hTf C₁ hV hWeak
  let V (n : ℕ) : ComplexL2 E := symbolL2 (conjugateSymbol a) ((u n).toLp 2 volume)
  let test (n : ℕ) (x : E) := conj (a x) * u n x
  let error (n : ℕ) := localizedNormalizedAngularDifference c d S hKU m (v n)
  have hV (n : ℕ) : V n =ᵐ[volume] test n := by
    filter_upwards [symbolL2_ae (conjugateSymbol a) ((u n).toLp 2 volume),
      (u n).coeFn_toLp 2 volume] with x hx hy
    rw [hx, hy]
    rfl
  have hVN (n : ℕ) : ‖V n‖ ≤ a.bound * C₀ :=
    (symbolL2_norm_le (conjugateSymbol a) ((u n).toLp 2 volume)).trans
      (mul_le_mul_of_nonneg_left (hU n) a.bound_nonneg)
  have hLD := tendsto_tested_strongZero (fun n => (u n : E → ℂ)) (fun n => (u n).toLp 2 volume)
    (fun n => (u n).coeFn_toLp 2 volume) C₀ hU
    (fun n => firstOrderAction l (v n)) L hL hLt
  have hDD := tendsto_tested_strongZero test V hV (a.bound * C₀) hVN error D hD hDt
  have hEq (n : ℕ) (x : E) :
      conj (u n x) * (a x * localizedTransportedAngularAction c d S m (v n) x) =
      conj (u n x) * firstOrderAction p (v n) x -
        conj (u n x) * firstOrderAction l (v n) x + conj (test n x) * error n x := by
    by_cases hx : x ∈ S
    · simp only [test, map_mul, Complex.conj_conj, error, localizedNormalizedAngularDifference,
        dif_pos hx, hInd, localizedTransportedAngularAction, indicator_of_mem hx]
      have he := weighted_frozenAction_eq c d a m x (hKU hx) hp hl (v n)
      dsimp only [p,l] at he ⊢
      rw [← mul_sub, ← he]
      ring
    · have h0 : u n x = 0 :=
        image_eq_zero_of_notMem_tsupport (f := (u n : E → ℂ)) (fun h => hx (hUS n h))
      simp only [test, h0, mul_zero, map_zero, zero_mul, sub_zero, add_zero]
  have hIntegral (n : ℕ) :
      (∫ x, conj (u n x) * (a x * localizedTransportedAngularAction c d S m (v n) x)) =
      (∫ x, conj (u n x) * firstOrderAction p (v n) x) -
        (∫ x, conj (u n x) * firstOrderAction l (v n) x) + ∫ x, conj (test n x) * error n x := by
    have Ip := integrable_tested_bounded_leftAction p hp (a.bound * m.bound)
      (fun y ξ => movingChartAngularSymbol_norm_le c d a m (y,ξ)) (v n) (u n)
    have Il := integrable_testedL2_representatives (u n) (firstOrderAction l (v n))
      ((u n).toLp 2 volume) (L n) ((u n).coeFn_toLp 2 volume) (hL n)
    have Id := integrable_testedL2_representatives (test n) (error n) (V n) (D n) (hV n) (hD n)
    calc
      _ = ∫ x, (conj (u n x) * firstOrderAction p (v n) x -
          conj (u n x) * firstOrderAction l (v n) x) + conj (test n x) * error n x :=
        integral_congr_ae (Eventually.of_forall (hEq n))
      _ = _ := (integral_add (Ip.sub Il) Id).trans
        (congrArg (fun z => z + ∫ x, conj (test n x) * error n x) (integral_sub Ip Il))
  have hSmall := hDD.sub hLD
  rw [sub_zero] at hSmall
  refine hSmall.congr (fun n => ?_)
  dsimp only
  rw [show inner ℂ (U₀ n) (separableOperator b (normalizedAngularSymbol m) (V₀ n)) = _ from
    transportedSeparable_pairing_eq c d S hK hKU a b m (v n) (u n) (hVS n) (hUS n) (hPull n),
    hIntegral n]
  ring

end Burnett.Microlocal.AtlasOverlapKernel
