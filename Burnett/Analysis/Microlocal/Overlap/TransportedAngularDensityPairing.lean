import Burnett.Analysis.Microlocal.Overlap.CompactAngularDensityPairing
import Burnett.Analysis.Microlocal.Overlap.LeftActionPairingBounds
import Burnett.Analysis.Microlocal.Overlap.MovingChartLowAction
import Burnett.Analysis.Microlocal.Overlap.NormalizedConjugationWeakLimit
import Burnett.Analysis.Microlocal.Overlap.TransportedHalfDensitySchwartz

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapGradient (overlapJacobianWeight overlapTransition)
open Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.SeparablePositive (conjugateSymbol)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The actual transported multiplier, pulled back with the half-density
weight and restricted to the same compact overlap window. -/
def localizedTransportedAngularAction (c d : M) (S : Set E) (m : BoundedSymbol E)
    (f : E → ℂ) (x : E) : ℂ :=
  S.indicator (fun y => overlapJacobianWeight c d y •
    (𝓕⁻ (fun ξ => normalizedAngularSymbol m ξ * (𝓕 (transportedHalfDensity c d S f)) ξ))
      (overlapTransition c d y)) x

variable [IsManifold Model ∞ M]

private theorem weighted_frozenAction_eq
    (c d : M) (a m : BoundedSymbol E) (x : E) (hx : x ∈ (chartTransition c d).source)
    (hp : Measurable (movingChartAngularSymbol c d a m))
    (hl : Measurable (uncurry (movingChartLowSymbol c d a m))) (f : SchwartzMap E ℂ) :
    a x * (𝓕⁻ (fun ξ => normalizedAngularSymbol m (frozenChartFrequency c d hx ξ) *
      (𝓕 (f : E → ℂ)) ξ)) x =
      firstOrderAction (fun y ξ => movingChartAngularSymbol c d a m (y,ξ)) f x -
        firstOrderAction (movingChartLowSymbol c d a m) f x := by
  let p (y ξ : E) := movingChartAngularSymbol c d a m (y,ξ)
  let l := movingChartLowSymbol c d a m
  have hP := bounded_leftAction_integrand_integrable p hp (a.bound * m.bound)
    (fun y ξ => movingChartAngularSymbol_norm_le c d a m (y,ξ)) f x
  have hL := bounded_leftAction_integrand_integrable l hl (a.bound * m.bound)
    (movingChartLowSymbol_norm_le c d a m) f x
  change _ = firstOrderAction p f x - firstOrderAction l f x
  rw [firstOrderAction_integrand_eq, firstOrderAction_integrand_eq, ← integral_sub hP hL,
    Real.fourierIntegralInv_eq', ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  change a x * (baseFourierPhase ξ x *
    (normalizedAngularSymbol m (frozenChartFrequency c d hx ξ) * (𝓕 (f : E → ℂ)) ξ)) =
      baseFourierPhase ξ x * (p x ξ * (𝓕 (f : E → ℂ)) ξ) -
        baseFourierPhase ξ x * (l x ξ * (𝓕 (f : E → ℂ)) ξ)
  calc
    _ = baseFourierPhase ξ x *
      ((a x * normalizedAngularSymbol m (frozenChartFrequency c d hx ξ)) * (𝓕 (f : E → ℂ)) ξ) := by ring
    _ = _ := by
      rw [movingChart_normalizedAngular_eq_principal_sub_low c d a m hx ξ]
      dsimp only [p,l]
      ring

/-- The transported Fourier pairing reads the represented source-chart
matrix measure with precisely the moving inverse-adjoint angular symbol. -/
theorem tendsto_transportedAngularPairings_of_matrixDensity
    (B : Field (M := M)) (hB : IsSmooth B) (hnB : IsNondegenerate B)
    (c d : M) (K : BallData) (hKU : K.closedBall ⊆ (chartTransition c d).source)
    (a m : BoundedSymbol E) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (haS : tsupport (a : E → ℂ) ⊆ K.closedBall)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (f : ℕ → JetSlot → SchwartzMap E ℂ) (hS : ∀ n i, tsupport (f n i : E → ℂ) ⊆ K.closedBall)
    (C : ℝ) (hC : ∀ n i, ‖(f n i).toLp 2 volume‖ ≤ C)
    (hw : ∀ i (w : ComplexL2 E),
      Tendsto (fun n => inner ℂ w ((f n i).toLp 2 volume)) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings K (fun n i => (f n i).toLp 2 volume) σ ν hfin)
    (i j : JetSlot) :
    Tendsto (fun n => ∫ x, conj (f (σ n) i x) *
      (a x * localizedTransportedAngularAction c d K.closedBall m (f (σ n) j) x))
      atTop (𝓝 (∫ x : Chart K, movingChartAngularSymbol c d a m (x.1,x.2) *
        density ν hfin x i j ∂traceMeasure ν)) := by
  let S := K.closedBall
  have hK : IsCompact S := isCompact_closedBall _ _
  let u (n : ℕ) := f (σ n) i
  let v (n : ℕ) := f (σ n) j
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
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC 0 i)
  have hPw := tendsto_compactAngularAction_pairings_of_matrixDensity K f σ ν hfin hRep p S hK hSupp
    hJoint hZero (movingChartAngularSymbol_degreeZero c d a m hd) i j (C * C)
    (fun n => mul_le_mul (hC (σ n) i) (hC (σ n) j) (norm_nonneg _) hC₀)
  have hInd (n : ℕ) : S.indicator (v n : E → ℂ) = v n := by
    funext x
    by_cases hx : x ∈ S
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hS (σ n) j h))).symm
  have hF (n : ℕ) : Integrable (𝓕 (S.indicator (v n : E → ℂ))) := by
    rw [hInd]
    exact (SchwartzMap.fourierTransformCLM ℂ (v n)).integrable
  have hTf (n : ℕ) : Integrable (𝓕 (transportedHalfDensity c d S (v n))) :=
    (SchwartzMap.fourierTransformCLM ℂ
      (transportedHalfDensitySchwartz c d S hK hKU (v n) (hS (σ n) j))).integrable
  have hWeak (w : ComplexL2 E) :
      Tendsto (fun n => inner ℂ w ((v n).toLp 2 volume)) atTop (𝓝 0) :=
    (hw j w).comp hσ.tendsto_atTop
  obtain ⟨L, hL, hLt⟩ := exists_movingChartLowAction_strongZero c d a m S hK hKU haS ha hm
    v C (fun n => hC (σ n) j) hWeak
  obtain ⟨D, hD, hDt⟩ := exists_localizedNormalizedAngularDifference_strongZero B hB hnB c d S
    hK hKU (convex_closedBall _ _) m hm hd v hF hTf C (fun n => hC (σ n) j) hWeak
  let V (n : ℕ) : ComplexL2 E := symbolL2 (conjugateSymbol a) ((u n).toLp 2 volume)
  let test (n : ℕ) (x : E) := conj (a x) * u n x
  let error (n : ℕ) := localizedNormalizedAngularDifference c d S hKU m (v n)
  have hV (n : ℕ) : V n =ᵐ[volume] test n := by
    filter_upwards [symbolL2_ae (conjugateSymbol a) ((u n).toLp 2 volume),
      (u n).coeFn_toLp 2 volume] with x hx hy
    rw [hx, hy]
    rfl
  have hVN (n : ℕ) : ‖V n‖ ≤ a.bound * C :=
    (symbolL2_norm_le (conjugateSymbol a) ((u n).toLp 2 volume)).trans
      (mul_le_mul_of_nonneg_left (hC (σ n) i) a.bound_nonneg)
  have hLD := tendsto_tested_strongZero (fun n => (u n : E → ℂ)) (fun n => (u n).toLp 2 volume)
    (fun n => (u n).coeFn_toLp 2 volume) C (fun n => hC (σ n) i)
    (fun n => firstOrderAction l (v n)) L hL hLt
  have hDD := tendsto_tested_strongZero test V hV (a.bound * C) hVN error D hD hDt
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
        image_eq_zero_of_notMem_tsupport (f := (u n : E → ℂ)) (fun h => hx (hS (σ n) i h))
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
  change Tendsto (fun n => ∫ x, conj (u n x) * (a x * localizedTransportedAngularAction c d S m (v n) x))
    atTop (𝓝 (∫ x : Chart K, p x.1 x.2 * density ν hfin x i j ∂traceMeasure ν))
  simp_rw [hIntegral]
  simpa only [sub_zero, add_zero] using (hPw.sub hLD).add hDD

end Burnett.Microlocal.Overlap
