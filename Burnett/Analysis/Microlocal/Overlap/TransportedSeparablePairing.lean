import Burnett.Analysis.Microlocal.Overlap.HalfDensityScalarPairing
import Burnett.Analysis.Microlocal.Overlap.TransportedAngularDensityPairing

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapGradient (overlapTransition overlapTransition_eq)
open Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem transportedSeparable_pairing_eq
    (c d : M) (S : Set E) (hS : IsCompact S) (hSU : S ⊆ (chartTransition c d).source)
    (a b m : BoundedSymbol E) (ha : ∀ x ∈ S, a x = b (chartTransition c d x))
    (f v : SchwartzMap E ℂ) (hf : tsupport (f : E → ℂ) ⊆ S) (hv : tsupport (v : E → ℂ) ⊆ S) :
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
  · simp only [localizedTransportedAngularAction, indicator_of_mem hx, ha x hx,
      overlapTransition_eq c d (hSU hx)]
    rfl
  · simp only [localizedTransportedAngularAction, indicator_of_notMem hx, mul_zero]

/-- The separated test in target coordinates has the transported limit
on the same source-chart density. The base tests agree on the window. -/
theorem tendsto_targetSeparablePairings_of_sourceMatrixDensity
    (B : Field (M := M)) (hB : IsSmooth B) (hnB : IsNondegenerate B)
    (c d : M) (K : BallData) (hKU : K.closedBall ⊆ (chartTransition c d).source)
    (a b m : BoundedSymbol E) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (haS : tsupport (a : E → ℂ) ⊆ K.closedBall)
    (hPull : ∀ x ∈ K.closedBall, a x = b (chartTransition c d x))
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
      a b m hPull (f (σ n) j) (f (σ n) i) (hS (σ n) j) (hS (σ n) i)
  simp_rw [hEq]
  exact tendsto_transportedAngularPairings_of_matrixDensity B hB hnB c d K hKU a m ha haS
    hm hd f hS C hC hw σ hσ ν hfin hRep i j

end Burnett.Microlocal.Overlap
