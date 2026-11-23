import Burnett.Analysis.Microlocal.Overlap.BaseFourierAngularRegularity
import Burnett.Analysis.Microlocal.Overlap.CompactAngularBaseBounds
import Burnett.Analysis.Microlocal.Overlap.IntegratedSymbolPairing

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped ComplexConjugate ContDiff FourierTransform InnerProduct Topology

/-- An actual compactly based left Fourier action of degree zero reads the
already represented matrix measure on the same subsequence. -/
theorem tendsto_compactAngularAction_pairings_of_matrixDensity
    (K : BallData) (f : ℕ → JetSlot → SchwartzMap E ℂ)
    (σ : ℕ → ℕ) (ν : (JetSlot → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings K (fun n i => (f n i).toLp 2 volume) σ ν hfin)
    (p : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hSupport : ∀ ξ, tsupport (fun x => p x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => p x 0)) (hDegree : ∀ x, DegreeZero (p x))
    (i j : JetSlot) (B : ℝ)
    (hB : ∀ n, ‖(f (σ n) i).toLp 2 volume‖ * ‖(f (σ n) j).toLp 2 volume‖ ≤ B) :
    Tendsto (fun n => ∫ x, conj (f (σ n) i x) * firstOrderAction p (f (σ n) j) x)
      atTop (𝓝 (∫ x : Chart K, p x.1 x.2 * density ν hfin x i j ∂traceMeasure ν)) := by
  have hSmooth := contDiff_baseAngularSection p hJoint hZero
  have hAngular (x : E) : ContinuousOn (p x) ({0}ᶜ : Set E) :=
    hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hξ => ⟨mem_univ x, hξ⟩)
  have hOrder := exists_uniform_baseDerivative_of_homogeneousAngular p S hS hSupport hJoint hZero hDegree
  obtain ⟨m, b, hb, hbound, hcoeff, hPair⟩ :=
    exists_compactBaseAngular_leftFourier_pairing ⟨S, hS, hSupport⟩ hSmooth hOrder hAngular
  have P (n : ℕ) := hPair (f (σ n) j) (f (σ n) i)
  have hm (k : E) : (m k : E → ℂ) = baseFourierCoefficient p k := funext (hcoeff k)
  have hSmoothM (k : E) : ContDiffOn ℝ ∞ (m k : E → ℂ) ({0}ᶜ : Set E) := by
    rw [hm]
    exact contDiffOn_baseFourierCoefficient p S hS hSupport hJoint k
  have hDegreeM (k : E) : DegreeZero (m k : E → ℂ) := by
    rw [hm]
    exact degreeZero_baseFourierCoefficient hDegree k
  let τ := traceMeasure ν
  letI : IsFiniteMeasure τ := hRep.2.1
  have hBaseCoord : Measurable (fun x : Chart K => (x.1 : E)) :=
    measurable_subtype_coe.comp measurable_fst
  have hAngCoord : Measurable (fun x : Chart K => (x.2 : E)) :=
    measurable_subtype_coe.comp measurable_snd
  let baseMap (q : E × Chart K) : E × E := (q.1,q.2.1)
  let angMap (q : E × Chart K) : E × E := (q.1,q.2.2)
  have hBaseMap : Measurable baseMap := measurable_fst.prodMk (hBaseCoord.comp measurable_snd)
  have hAngMap : Measurable angMap := measurable_fst.prodMk (hAngCoord.comp measurable_snd)
  have hPhaseMeas : Measurable (uncurry baseFourierPhase) :=
    baseFourierPhase_continuous.measurable
  have hJointPhase : Measurable (fun q : E × Chart K => baseFourierPhase q.1 q.2.1) := by
    have heq : (fun q : E × Chart K => baseFourierPhase q.1 q.2.1) =
        uncurry baseFourierPhase ∘ baseMap := funext fun q => rfl
    rw [heq]
    exact hPhaseMeas.comp hBaseMap
  have hCoeffMeas : Measurable (uncurry (baseFourierCoefficient p)) :=
    measurable_baseFourierCoefficient
      (measurable_baseAngularSymbol (fun ξ => (hSmooth ξ).continuous) hAngular)
  have hJointM : Measurable (fun q : E × Chart K => m q.1 q.2.2) := by
    have heq : (fun q : E × Chart K => m q.1 q.2.2) =
        uncurry (baseFourierCoefficient p) ∘ angMap := funext fun q => hcoeff q.1 q.2.2
    rw [heq]
    exact hCoeffMeas.comp hAngMap
  have hJointAll : AEStronglyMeasurable
      (fun q : E × Chart K => baseFourierPhase q.1 q.2.1 * m q.1 q.2.2 * density ν hfin q.2 i j)
      ((volume : Measure E).prod τ) :=
    (hJointPhase.aestronglyMeasurable.mul hJointM.aestronglyMeasurable).mul
      (integrable_density_entry ν hfin i j).aestronglyMeasurable.comp_snd
  have hT := tendsto_integrated_separablePairings_of_matrixDensity (volume : Measure E) K
    (fun n i => (f n i).toLp 2 volume) σ ν hfin hRep baseFourierPhaseSymbol m
    (fun k => baseFourierPhase_continuous_apply continuous_const continuous_id) hSmoothM hDegreeM
    i j B hB b hb (fun k => by
      change 1 * (m k).bound ≤ b k
      rw [one_mul, hbound])
    (fun n => (P n).1.aestronglyMeasurable) hJointAll
  have hLeft : (fun n => ∫ x, conj (f (σ n) i x) * firstOrderAction p (f (σ n) j) x) =
      fun n => ∫ k, inner ℂ ((f (σ n) i).toLp 2 volume)
        (separableOperator (baseFourierPhaseSymbol k) (m k) ((f (σ n) j).toLp 2 volume)) :=
    funext fun n => (P n).2
  have hInv (x ξ : E) : (∫ k, baseFourierPhaseSymbol k x * m k ξ) = p x ξ := by
    have h := baseFourierCoefficient_inverse (p := p)
      (compactBaseOrderOne_frequencyWeight ⟨S, hS, hSupport⟩ hSmooth hOrder) x ξ
    rw [Real.fourierIntegralInv_eq'] at h
    simpa only [baseFourierPhaseSymbol, baseFourierPhase, hcoeff, smul_eq_mul] using h
  rw [hLeft]
  simpa only [hInv] using hT

end Burnett.Microlocal.Overlap
