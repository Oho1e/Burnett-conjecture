import Burnett.Analysis.Microlocal.Overlap.ReceivingChartFourierLimit
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartMovedSymbols
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartHalfDensity
import Burnett.Analysis.Microlocal.Overlap.CompactAngularDensityPairing
import Burnett.Analysis.Microlocal.Overlap.LeftActionPairingBounds
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput

/-! The actual receiving Fourier multiplier on transported original inputs,
read from the very same original chart covariance. -/

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.SeparablePositive (conjugateSymbol)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The actual transported multiplier, pulled back with the half-density
weight and restricted to the same compact overlap window. -/
def localizedTransportedAngularAction (c d : AtlasChart M) (S : Set E) (m : BoundedSymbol E)
    (f : E → ℂ) (x : E) : ℂ :=
  S.indicator (fun y => overlapJacobianWeight c d y •
    (𝓕⁻ (fun ξ => normalizedAngularSymbol m ξ * (𝓕 (transportedHalfDensity c d S f)) ξ))
      (overlapTransition c d y)) x


theorem weighted_frozenAction_eq
    (c d : AtlasChart M) (a m : BoundedSymbol E) (x : E) (hx : x ∈ (c.transition d).source)
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
    (c d : AtlasChart M) (K : BallData) (hKU : K.closedBall ⊆ (c.transition d).source)
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
  obtain ⟨D, hD, hDt⟩ := exists_localizedNormalizedAngularDifference_strongZero c d S
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

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

theorem transportedSeparable_pairing_eq
    (c d : AtlasChart M) (S : Set E) (hS : IsCompact S) (hSU : S ⊆ (c.transition d).source)
    (a b m : BoundedSymbol E)
    (f v : SchwartzMap E ℂ) (hf : tsupport (f : E → ℂ) ⊆ S) (hv : tsupport (v : E → ℂ) ⊆ S)
    (ha : ∀ x ∈ tsupport (v : E → ℂ), a x = b (c.transition d x)) :
    let F := transportedHalfDensitySchwartz c d S hS hSU f hf
    let V := transportedHalfDensitySchwartz c d S hS hSU v hv
    inner ℂ (V.toLp 2 volume) (separableOperator b (normalizedAngularSymbol m) (F.toLp 2 volume)) =
      ∫ x, conj (v x) * (a x * localizedTransportedAngularAction c d S m f x) := by
  intro F V
  let D (y : E) := (𝓕⁻ (fun ξ => normalizedAngularSymbol m ξ * (𝓕 (F : E → ℂ)) ξ)) y
  have hI : inner ℂ (V.toLp 2 volume)
      (separableOperator b (normalizedAngularSymbol m) (F.toLp 2 volume)) =
      ∫ y, conj (transportedHalfDensity c d S v y) * (b y * D y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [V.coeFn_toLp 2 volume,
      symbolL2_ae b (fourierMultiplier (normalizedAngularSymbol m) (F.toLp 2 volume)),
      Burnett.Microlocal.AngularDyadicKernel.fourierMultiplier_schwartz_eq_inverse_mul_ae
        (normalizedAngularSymbol m) F] with y hV hB hD
    change inner ℂ ((V.toLp 2 volume : E → ℂ) y)
      (symbolL2 b (fourierMultiplier (normalizedAngularSymbol m) (F.toLp 2 volume)) y) = _
    rw [RCLike.inner_apply', hV, hB, hD]
    rfl
  rw [hI, integral_transportHalfDensity_pairing c d S hS hSU]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ S
  · by_cases hxv : x ∈ tsupport (v : E → ℂ)
    · simp only [localizedTransportedAngularAction, indicator_of_mem hx, ha x hxv,
        overlapTransition_eq c d (hSU hx)]
      rfl
    · simp only [image_eq_zero_of_notMem_tsupport hxv, map_zero, zero_mul]
  · simp only [localizedTransportedAngularAction, indicator_of_notMem hx, mul_zero]

/-- The separated test in target coordinates has the transported limit
on the same source-chart density. The base tests agree on the window. -/
theorem tendsto_targetSeparablePairings_of_sourceMatrixDensity
    (c d : AtlasChart M) (K : BallData) (hKU : K.closedBall ⊆ (c.transition d).source)
    (a b m : BoundedSymbol E) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (haS : tsupport (a : E → ℂ) ⊆ K.closedBall)
    (hPull : ∀ x ∈ K.closedBall, a x = b (c.transition d x))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hd : DegreeZero (m : E → ℂ))
    (f : ℕ → JetSlot → SchwartzMap E ℂ) (hS : ∀ n i, tsupport (f n i : E → ℂ) ⊆ K.closedBall)
    (C : ℝ) (hC : ∀ n i, ‖(f n i).toLp 2 volume‖ ≤ C)
    (hw : ∀ i (w : ComplexL2 E),
      Tendsto (fun n => inner ℂ w ((f n i).toLp 2 volume)) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings K (fun n i => (f n i).toLp 2 volume) σ ν hfin)
    (i j : JetSlot) :
    let F (n : ℕ) (k : JetSlot) := transportedHalfDensitySchwartz c d K.closedBall
      (isCompact_closedBall _ _) hKU (f (σ n) k) (hS (σ n) k)
    Tendsto (fun n => inner ℂ ((F n i).toLp 2 volume)
      (separableOperator b (normalizedAngularSymbol m) ((F n j).toLp 2 volume)))
      atTop (𝓝 (∫ x : Chart K, movingChartAngularSymbol c d a m (x.1,x.2) *
        density ν hfin x i j ∂traceMeasure ν)) := by
  intro F
  have hEq (n : ℕ) : inner ℂ ((F n i).toLp 2 volume)
      (separableOperator b (normalizedAngularSymbol m) ((F n j).toLp 2 volume)) =
      ∫ x, conj (f (σ n) i x) *
        (a x * localizedTransportedAngularAction c d K.closedBall m (f (σ n) j) x) :=
    transportedSeparable_pairing_eq c d K.closedBall (isCompact_closedBall _ _) hKU
      a b m (f (σ n) j) (f (σ n) i) (hS (σ n) j) (hS (σ n) i)
      (fun x hx => hPull x (hS (σ n) i hx))
  simp_rw [hEq]
  exact tendsto_transportedAngularPairings_of_matrixDensity c d K hKU a m ha haS
    hm hd f hS C hC hw σ hσ ν hfin hRep i j

end Burnett.Microlocal.AtlasOverlapKernel

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Microlocal.AtlasOverlapKernel

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.Overlap (exists_originalVolume_weakL2_representatives)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.Geometry.MaximalChart (AtlasChart)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On every represented subsequence, the transported tests of the actual
volume-weighted coordinate gradient read the same source chart measure. -/
theorem exists_originalVolume_transportedAngularPairings_of_matrixDensity
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (d : AtlasChart M)
    (hKU : q.ball.closedBall ⊆ ((AtlasChart.atPoint q.center).transition d).source) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
    ∃ f : ℕ → JetSlot → SchwartzMap E ℂ,
      (∀ n i, (f n i).toLp 2 volume = w n i) ∧
      ∀ (σ : ℕ → ℕ) (_ : StrictMono σ) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfin : ∀ v, IsFiniteMeasure (ν v)) (_ : RepresentsCompactJetPairings q.ball w σ ν hfin)
        (a m : BoundedSymbol E) (_ : ContDiff ℝ ∞ (a : E → ℂ))
        (_ : tsupport (a : E → ℂ) ⊆ q.ball.closedBall)
        (_ : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (_ : DegreeZero (m : E → ℂ))
        (i j : JetSlot),
        Tendsto (fun n => ∫ x, conj (f (σ n) i x) *
          (a x * localizedTransportedAngularAction (AtlasChart.atPoint q.center) d q.ball.closedBall m (f (σ n) j) x))
          atTop (𝓝 (∫ x : Chart q.ball, movingChartAngularSymbol (AtlasChart.atPoint q.center) d a m (x.1,x.2) *
            density ν hfin x i j ∂traceMeasure ν)) := by
  intro w
  obtain ⟨f, C, _, hIdent, hS, hC, hw⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  refine ⟨f, hIdent, ?_⟩
  intro σ hσ ν hfin hRep a m ha haS hm hd i j
  have hEq : (fun n j => (f n j).toLp 2 volume) = w := funext fun n => funext (hIdent n)
  have hRepf : RepresentsCompactJetPairings q.ball (fun n i => (f n i).toLp 2 volume) σ ν hfin := by
    rw [hEq]
    exact hRep
  exact tendsto_transportedAngularPairings_of_matrixDensity (AtlasChart.atPoint q.center) d q.ball hKU
    a m ha haS hm hd f hS C hC hw σ hσ ν hfin hRepf i j

/-- On the already represented original subsequence, the actual target
operator on the transported original gradients reads the source density. -/
theorem exists_originalVolume_targetSeparablePairings_of_sourceMatrixDensity
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (d : AtlasChart M)
    (hKU : q.ball.closedBall ⊆ ((AtlasChart.atPoint q.center).transition d).source) :
    let w := originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
      (q.cutoff_support.trans q.ball_in_chart)
    ∃ (f : ℕ → JetSlot → SchwartzMap E ℂ) (hS : ∀ n i, tsupport (f n i : E → ℂ) ⊆ q.ball.closedBall),
      (∀ n i, (f n i).toLp 2 volume = w n i) ∧
      ∀ (σ : ℕ → ℕ) (_ : StrictMono σ) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfin : ∀ v, IsFiniteMeasure (ν v)) (_ : RepresentsCompactJetPairings q.ball w σ ν hfin)
        (a b m : BoundedSymbol E) (_ : ContDiff ℝ ∞ (a : E → ℂ))
        (_ : tsupport (a : E → ℂ) ⊆ q.ball.closedBall)
        (_ : ∀ x ∈ q.ball.closedBall, a x = b ((AtlasChart.atPoint q.center).transition d x))
        (_ : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (_ : DegreeZero (m : E → ℂ))
        (i j : JetSlot),
        let F (n : ℕ) (k : JetSlot) := transportedHalfDensitySchwartz (AtlasChart.atPoint q.center) d q.ball.closedBall
          (isCompact_closedBall _ _) hKU (f (σ n) k) (hS (σ n) k)
        Tendsto (fun n => inner ℂ ((F n i).toLp 2 volume)
          (separableOperator b (normalizedAngularSymbol m) ((F n j).toLp 2 volume)))
          atTop (𝓝 (∫ x : Chart q.ball, movingChartAngularSymbol (AtlasChart.atPoint q.center) d a m (x.1,x.2) *
            density ν hfin x i j ∂traceMeasure ν)) := by
  intro w
  obtain ⟨f, C, _, hIdent, hS, hC, hw⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hnB hconv hb q
  refine ⟨f, hS, hIdent, ?_⟩
  intro σ hσ ν hfin hRep a b m ha haS hPull hm hd i j
  have hEq : (fun n k => (f n k).toLp 2 volume) = w := funext fun n => funext (hIdent n)
  have hRepf : RepresentsCompactJetPairings q.ball (fun n k => (f n k).toLp 2 volume) σ ν hfin := by
    rw [hEq]
    exact hRep
  exact tendsto_targetSeparablePairings_of_sourceMatrixDensity (AtlasChart.atPoint q.center) d q.ball hKU
    a b m ha haS hPull hm hd f hS C hC hw σ hσ ν hfin hRepf i j

end Burnett.Microlocal.AtlasOverlapKernel
