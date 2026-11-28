import Burnett.Analysis.TransportWard.Weyl.OriginalLocalizedWeylInputBounds
import Burnett.Analysis.TransportWard.Weyl.PrincipalWeylCubicPartitionLimit
import Burnett.Analysis.TransportWard.Weyl.OriginalChartCubicInputBounds
import Burnett.Analysis.TransportWard.Weyl.OriginalChartPrincipalComparisons
import Burnett.Analysis.TransportWard.Weyl.CompactWindowedWeylJets
import Burnett.Analysis.TransportWard.Weyl.ActualWeylOutputL2
import Burnett.Analysis.TransportWard.Weyl.DirectionalBoundsFromScaled
import Burnett.Analysis.TransportWard.Weyl.RealEnergyFieldJets
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.V03

open Filter Function MeasureTheory Metric Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.A03 Burnett.A02.FrequencySplit Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff ENNReal Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original windowed Weyl action can be reapplied on the actual
receiving cutoff fields of the cubic partition without changing the
limiting principal variation. All fields use the original refinement. -/
theorem tendsto_originalWeyl_retested_cubic_partition_error_zero {L : Type}
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (s : Finset L) (d : L → D)
    (hd : ∀ l ∈ s, tsupport (d l : E → ℝ) ⊆ c.chart.target)
    (hPlateau : ∀ l ∈ s, ∀ x ∈ tsupport (d l : E → ℝ), (χ : E → ℝ) x = 1)
    (a : E → E → ℝ) (S : Set E) (hS : IsCompact S) (ha : ∀ x ∉ S, ∀ ξ, a x ξ = 0)
    (hHom : ∀ (t : ℝ), 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (cut : SchwartzMap E ℂ) (hCut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hLow : ∀ ξ : E, ‖ξ‖ ≤ 1 / 2 → fixedRadianProfile cut ξ = 1)
    (hHigh : ∀ ξ : E, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (hβ : ContDiff ℝ ∞ (uncurry (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ))))
    (θ : SchwartzMap E ℝ) (hθc : HasCompactSupport (θ : E → ℝ))
    (hθS : ∀ x ∈ S, θ x = 1) (hχθ : ∀ x ∈ tsupport (θ : E → ℝ), (χ : E → ℝ) x = 1)
    (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hCube : ∀ x ∈ thickening ℓ (tsupport (θ : E → ℝ)), ∑ l ∈ s, (d l : E → ℝ) x ^ 3 = 1)
    (R : ℝ) (hAmp : CompactRadianTwoPointOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (fixedInfraredSymbol cut 0 (a x) ξ : ℂ))) R R)
    (C : Index → Index → OrderedPair → OrderedPair → OrderedPair → SchwartzMap E ℂ)
    (A : ℝ≥0∞) (hA : A < ⊤) (hC : ∀ p q i j k, eLpNorm (C p q i j k : E → ℂ) ⊤ volume ≤ A)
    (w : ℕ → RealEnergyField OrderedPair)
    (hSupp : ∀ n i, tsupport ((w n).val i : E → ℂ) ⊆ tsupport (θ : E → ℝ)) :
    let Z n := fixedWeylPerturbationSchwartz B g hB hg c χ hχ (σ n)
    let T (u : SchwartzMap E ℂ) (x : E) := (-Complex.I) * firstOrderAction
      (windowedWeylLeftSymbol θ (fun y ξ => (fixedInfraredSymbol cut 0 (a y) ξ : ℂ)) R hAmp) u x
    (∀ n i x, (w n).val i x = T (Z n i) x) →
    let U n l i := energyProduct (Burnett.C01.realTestComplexSchwartz (d l)) (Z n i)
    let c' (p q : Index) (i j k : OrderedPair) : E → ℂ := C p q i j k
    Tendsto (fun n => (∑ l ∈ s, ∫ x, (principalVariationDensity c' (U n l)
      (fun i => T (U n l i)) x).re) - ∫ x in tsupport (θ : E → ℝ),
        (principalVariationDensity c' (Z n) (fun i => (w n).val i) x).re) atTop (𝓝 0) := by
  classical
  intro Z T hTest U c'
  let β (x ξ : E) := (fixedInfraredSymbol cut 0 (a x) ξ : ℂ)
  let P := windowedWeylLeftSymbol θ β R hAmp
  let K := tsupport (θ : E → ℝ)
  let η (l : L) := Burnett.C01.realTestComplexSchwartz (d l)
  have hβoff (x : E) (hx : x ∉ S) (ξ : E) : β x ξ = 0 := by
    simp only [β, fixedInfraredSymbol, ha x hx ξ, mul_zero, fixedRadianProfile,
      SchwartzMap.zero_apply, Complex.zero_re, add_zero, Complex.ofReal_zero]
  have hβhigh (x ξ : E) (hξ : 1 < ‖ξ‖) : β x ξ = (a x ξ : ℂ) := by
    exact congrArg Complex.ofReal (fixedInfraredSymbol_outside cut 0 (a x) ξ (hHigh ξ hξ)
      (by simp only [fixedRadianProfile, SchwartzMap.zero_apply, Complex.zero_re]))
  have hTail (x ξ : E) (hξ : 1 < ‖ξ‖) (t : ℝ) (ht : 1 ≤ t) : β x (t • ξ) = t • β x ξ := by
    have ht₀ : 0 < t := zero_lt_one.trans_le ht
    have hLarge : 1 < ‖t • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht₀.le]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht) (norm_nonneg ξ)]
    rw [hβhigh x _ hLarge, hβhigh x ξ hξ, hHom t ht₀, Complex.ofReal_mul, Complex.real_smul]
  have hWindow (x ξ : E) (hx : β x ξ ≠ 0) : θ x = 1 :=
    hθS x (by by_contra hs; exact hx (hβoff x hs ξ))
  obtain ⟨R', hR'⟩ := hθc.isCompact.isBounded.subset_closedBall (0 : E)
  have hθoff (x : E) (hx : x ∉ closedBall 0 R') : θ x = 0 := by
    by_contra hn
    exact hx (hR' (subset_tsupport (θ : E → ℝ) hn))
  have hScaled := compactWindowedWeylAmplitude_scaled_orderOne θ β (θ.smooth _) hβ R' hθoff hTail
  have hDir := radianOrdinaryDirectionalAmplitudeBounds_of_scaled _ _ _ hScaled
  have hNormalized := scaledJointOrderOne_of_compactRadianSymbol β hβ hS hβoff hTail
  obtain ⟨Q, hQ, _, _⟩ := exists_windowedWeylSchwartz_selfAdjoint θ β R hAmp hDir hWindow
    θ.continuous hθc hNormalized (fun x ξ => Complex.conj_ofReal _)
  have hT (u : SchwartzMap E ℂ) : Differentiable ℝ (T u) := by
    have hEq : T u = fun x => (-Complex.I) * Q u x := by
      funext x
      exact congrArg ((-Complex.I) * ·) (hQ u x).symm
    rw [hEq]
    exact (differentiable_const (-Complex.I)).mul (Q u).differentiable
  obtain ⟨_, _, hRaw⟩ := exists_original_fixedWeylPerturbationSchwartz_bounds
    r B g hB hg hn hconv hb c χ hχ
  choose m hm hValue hGradient using hRaw
  let m₀ := ∑ i, m i
  have hm₀ : 0 ≤ m₀ := Finset.sum_nonneg fun i _ => hm i
  have hmi (i : OrderedPair) : m i ≤ m₀ := Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)
  have hBound (n : ℕ) (i : OrderedPair) : ‖(Z n i).toLp 2 volume‖ ≤ m₀ :=
    (hValue i (σ n)).trans (hmi i)
  let m₁ := Real.sqrt (m₀ ^ 2 + ∑ _a : Index, m₀ ^ 2)
  have hEnergy (n : ℕ) (i : OrderedPair) : Real.sqrt (schwartzH1Energy (Z n i)) ≤ m₁ := by
    apply Real.sqrt_le_sqrt
    change ‖(Z n i).toLp 2 volume‖ ^ 2 + ∑ a, ‖(energyPartial a (Z n i)).toLp 2 volume‖ ^ 2 ≤ _
    refine add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hBound n i) _) ?_
    exact Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
      ((hGradient i k (σ n)).trans (hmi i)) _
  obtain ⟨b, hb₀, hbTest⟩ := exists_windowedWeylRealOutput_L2_bound θ β R hAmp hDir hWindow hθc hNormalized
  let m₂ := max m₀ (b * m₁)
  have hW (n : ℕ) (i : OrderedPair) : ‖((w n).val i).toLp 2 volume‖ ≤ m₂ := by
    have hSupport : HasCompactSupport (Z n i : E → ℂ) := by
      apply (test_compactSupport χ).of_isClosed_subset isClosed_closure
      apply closure_minimal _ (isClosed_tsupport _)
      intro x hx
      by_contra hx'
      apply hx
      change Complex.ofReal ((χ : E → ℝ) x * fixedComponent B g c (σ n) i x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, Complex.ofReal_zero]
    exact ((hbTest (Z n i) ((w n).val i) hSupport (hTest n i)).trans
      (mul_le_mul_of_nonneg_left (hEnergy n i) hb₀)).trans (le_max_right _ _)
  obtain ⟨e, he, ht, hSmall⟩ := exists_originalWeylCutoff_value_uniform_modulus r B g hB hg hconv c χ hχ
  have hcubed : ∀ x ∈ K, (fun y => ∑ l ∈ s, η l y ^ 3) =ᶠ[𝓝 x] fun _ : E => (1 : ℂ) := by
    intro x hx
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hℓ K hx)] with y hy
    change ∑ l ∈ s, (Complex.ofReal ((d l : E → ℝ) y)) ^ 3 = 1
    rw [← Complex.ofReal_one, ← hCube y hy, Complex.ofReal_sum]
    simp only [Complex.ofReal_pow]
  obtain ⟨hc, _⟩ := originalChartWeyl_cutoff_and_frozen_comparisons a S hS ha hHom cut hCut
    hLow hHigh hβ θ (θ.smooth _) hθc hθS R hAmp
  have hComm (l : L) (_ : l ∈ s) : ∃ D : ℝ≥0∞, D < ⊤ ∧ SchwartzOrderZeroJetBound
      (fun u x => T (energyProduct (η l) u) x - η l x * T u x) D D := by
    obtain ⟨D, hD, hQC⟩ := hc (η l)
    have hSigned := schwartz_order_zero_jet_bound_const_mul _ D D hQC (-Complex.I)
    have hI : ‖-Complex.I‖ₑ = 1 := by simp [← ofReal_norm_eq_enorm]
    rw [hI, one_mul] at hSigned
    refine ⟨D, hD, ?_⟩
    convert hSigned using 1
    funext u x
    change (-Complex.I) * firstOrderAction P (energyProduct (η l) u) x -
      η l x * ((-Complex.I) * firstOrderAction P u x) =
      (-Complex.I) * (firstOrderAction P (energyProduct (η l) u) x - η l x * firstOrderAction P u x)
    ring
  exact Burnett.C01.tendsto_principalVariation_retested_cubic_partition_error_zero
    s η C A hA hC T hT Z (fun n i => (w n).val i) (fun n i => funext (hTest n i))
    (fun n i x => by
      change Complex.ofReal (Complex.ofReal ((χ : E → ℝ) x * fixedComponent B g c (σ n) i x)).re = _
      rw [Complex.ofReal_re]
      rfl)
    (fun n i x => Palatini.coe_re_eq_of_conj_eq _ ((w n).property i x))
    K hθc hSupp hcubed χ (test_smooth χ) (test_compactSupport χ) hχθ
    (e ∘ σ) (fun n => he (σ n)) (ht.comp hσ.tendsto_atTop) (fun n => hSmall (σ n))
    m₂ (hm₀.trans (le_max_left _ _)) (fun n i => (hBound n i).trans (le_max_left _ _)) hW hComm
    (fun l hl => exists_originalWeylCutoff_and_patch_component_L3 r B g hB hg hn hconv hb c
      χ (d l) hχ (hd l hl) (hPlateau l hl) σ hσ)

end Burnett.V03
