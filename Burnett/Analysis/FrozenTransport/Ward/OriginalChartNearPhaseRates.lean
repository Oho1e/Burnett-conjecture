import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearC04PatchInput
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLocalTest
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformTensorPatch
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleSamePatchPhaseConsumer
import Burnett.Analysis.FrozenTransport.PatchCorrection.IntrinsicCommonWideCorrectionJets

set_option autoImplicit false
set_option maxRecDepth 10600
set_option maxHeartbeats 16000000

noncomputable section

namespace Burnett.V03

open Set Filter Metric MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.C02 Burnett.C03 Burnett.V06
open Burnett.Fourier
open ConnectionDifference InverseField ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.A02.FrequencySplit (E Joint tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix)
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols
open private chartInverseMetric_isUnit from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz
open private contDiffOn_metricDensity from Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The actual near and phase terms on the chosen chart and joint screen.
The near cutoff and its coefficient are selected before `δ`. The phase
coefficient multiplies the supplied pair of C02 gradient tails. -/
theorem exists_originalChartWardNearPhaseRates
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K V : Set E) (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVU : V ⊆ c.chart.target)
    (wi wo : ℝ) (joint : HasJointWideScreen B c wi wo V)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a (V ×ˢ {ξ : E | ξ ≠ 0}))
    (odd : ∀ x ∈ K, ∀ ξ, a (x, -ξ) = -a (x, ξ))
    (hom : ∀ x ∈ K, ∀ t : ℝ, 0 < t → ∀ ξ, a (x, t • ξ) = t * a (x, ξ))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ i o q Cp : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1 / 16) (hi : 0 ≤ i) (hio : i < o)
    (hq : 3 < q) (hCp : 0 ≤ Cp) :
    let G := metricComponents (fixedForm B c)
    let m := chartInverseMetric B c
    let wide (x : E) (hx : x ∈ K) : WideScreenFrequencySmooth wi wo (m x) :=
      wideScreen_frequencySmooth_of_joint joint (hKV hx)
    ∃ c₀ δ₀ Cphase : ℝ, 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 ≤ Cphase ∧
      ∀ (cThin : ℝ) (hcThin : 0 < cThin), cThin ≤ c₀ → ∃ Cnear : ℝ, 0 ≤ Cnear ∧
      ∀ (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) δ₀),
      let η := cThin * κ * δ^2
      let hη : 0 < η := mul_pos (mul_pos hcThin hκ) (pow_pos hδ.1 _)
      ∀ (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ), ℓ ≤ 1 →
      let x₀ (j : s) := patchCenter ℓ j
      let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
      ∀ (hPatch : ∀ j ∈ s, P j ⊆ K)
        (Z : LatticeIndex → ℕ → ProjectionSchwartzMatrix) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
        (σ : ℕ → ℕ) (hσ : StrictMono σ),
      (∀ j ∈ s, ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (Z j n) (P j) (Cp * e n) (Cp * (1 + e n / ℓ))) →
      let hCenter (j : s) : x₀ j ∈ K := hPatch j j.property (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le))
      let z (j : s) (n : ℕ) := Z j (σ n)
      let T (j : s) := actualThinScreenMultiplier (m (x₀ j)) wi wo (wide (x₀ j) (hCenter j)) hη i o
      let diff (j : s) (n : ℕ) (k : Index × OrderedPair) :=
        multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z j n) k.1 k.2 -
          multiplierCoordinateDerivative (T j) (z j n) k.1 k.2
      let gradPhase (j : s) (n : ℕ) (k : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar (m (x₀ j)))
        (multiplierCoordinateDerivative (T j) (z j n) k.1 k.2)
      let H (j : s) (n : ℕ) := wardActualThinSpectrum (m (x₀ j)) wi wo (wide (x₀ j) (hCenter j)) hη i o (z j n)
      let near (j : s) (n : ℕ) : ℂ := ((tau^8)⁻¹ : ℝ) • ∫ y,
        (wardPurePhysicalNearWeight ϑ κ δ y : ℂ) * wardCyclicCubicWeight (G (x₀ j)) (fun ξ => a (x₀ j, ξ))
          (H j n) (H j n) (H j n) y
      let phase (j : s) (n : ℕ) := wardPhysicalPhaseRemainder ϑ κ (m (x₀ j)) (metricDensity (G (x₀ j)))
        (fun ξ => a (x₀ j, ξ)) wi wo (wide (x₀ j) (hCenter j)) hη i o (z j n)
      let mass (j : s) := ((volume : Measure E) (P j)).toReal
      (∀ j : s, ∀ᶠ n in atTop, |(near j n).re| ≤ Cnear * δ^(2*(q-3)/(q-2)) * mass j) ∧
      (∀ (j : s) (n : ℕ) (k : Fin 7), Integrable (wardActualTensorWeight (m (x₀ j)) (wardPhysicalPhaseSlots k)
        (wardPhysicalPhaseTensorSymbol ϑ κ (m (x₀ j)) (metricDensity (G (x₀ j))) (fun ξ => a (x₀ j, ξ)) k)
        wi wo (wide (x₀ j) (hCenter j)) hη i o (z j n))) ∧
      ∀ (Ce α : ℝ), 0 ≤ Ce → 0 ≤ α →
      (∀ j : s, ∀ ε > 0, ∀ᶠ n in atTop,
        (eLpNorm (orderedGradientValue (diff j n)) 3 volume).toReal ≤ Ce * ℓ^α * (mass j)^ (1 / 3 : ℝ) + ε ∧
        (eLpNorm (orderedGradientValue (gradPhase j n)) 3 volume).toReal ≤ Ce * ℓ^α * (mass j)^ (1 / 3 : ℝ) + ε) →
      ∀ ε > 0, ∀ᶠ n in atTop,
      (∑ j : s, ‖phase j n‖) ≤ (Cphase * Ce * (128 * (2 * Cp) + Ce)^2) * ℓ^α *
        ((17 ^ 4 : ℝ) * (volume K).toReal) + ε := by
  classical
  intro G m wide
  have hKU : K ⊆ c.chart.target := hKV.trans hVU
  have hG : ContDiffOn ℝ ∞ G V := contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
    (fixedForm_components_smooth B hB c i j).mono hVU
  have hND (x : E) (hx : x ∈ V) : Matrix.det (G x) ≠ 0 :=
    fixedForm_det_ne_zero B hSig.isNondegenerate c (hVU hx)
  have hm (i j : Index) : ContDiffOn ℝ ∞ (fun x => m x i j) V :=
    contDiffOn_pi.mp (contDiffOn_pi.mp ((chartInverseMetric_smooth B hB hSig.isNondegenerate c).mono hVU) i) j
  have hw : ContDiffOn ℝ ∞ (fun x => metricDensity (G x)) V := contDiffOn_metricDensity.comp hG hND
  have hInv (x : E) (hx : x ∈ K) : IsUnit (Matrix.det (m x)) :=
    chartInverseMetric_isUnit B hSig.isNondegenerate c (hKU hx)
  have hGeoND (x : E) (hx : x ∈ K) : Burnett.Analysis.ProjectiveNullCaps.Nondegenerate (m x) := by
    intro y hrow
    let u : Index → ℝ := fun j => y j
    have hMu : (m x)ᵀ *ᵥ u = 0 := funext hrow
    have hInvT : IsUnit (Matrix.det (m x)ᵀ) := by rw [det_transpose]; exact hInv x hx
    have injective : Function.Injective (mulVec (m x)ᵀ) :=
      mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det ((m x)ᵀ)).mpr hInvT)
    have hu : u = 0 := injective (by rw [hMu, mulVec_zero])
    ext j
    exact congrFun hu j
  have hSym (x : E) (_ : x ∈ K) : IsSymmetricTensor (m x) := by
    have hGT : (G x)ᵀ = G x := funext fun i => funext fun j => hSig.isSymmetric (c.chart.symm x) _ _
    have hMT : (m x)ᵀ = m x := by
      change (matrixInverse (G x))ᵀ = matrixInverse (G x)
      unfold matrixInverse
      rw [Matrix.transpose_nonsing_inv, hGT]
    exact fun i j => congrFun (congrFun hMT j) i
  obtain ⟨_, hFrames⟩ := Burnett.V11.compact_chartInverseMetric_family B hB hSig c K hK hKU
  have hFrame (x : E) (hx : x ∈ K) : Nonempty (TensorFrame.LorentzFrame (m x)) := hFrames _ ⟨x, hx, rfl⟩
  let W (y ξ : E) (k j : OrderedPair) :=
    globalAngularScreenSymbol wi wo (m y) (orderedBasis j) (fun s => ξ s) k.1 k.2
  have hW (k j : OrderedPair) : ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}) :=
    joint (orderedBasis j) k.1 k.2
  have hWide (y : E) (hy : y ∈ K) (ξ : E) (k j : OrderedPair) :
      W y ξ k j = (wideScreenAngular wi wo (m y) (wide y hy)).matrix ξ k j := rfl
  obtain ⟨c₀, δ₀, hc₀, hδ₀, hδ₁, hN⟩ := exists_wardActualNear_originalPatchRate_localTest K V V hK hV hKV hV hKV
    G hG hND hFrame hGeoND a ha odd hom wi wo wide W hW hWide ϑ hϑ hRange hCut hFlat κ i o q hκ hκsmall hi hio hq
  obtain ⟨aG, haG, hOddG, hHomG, hSame⟩ := exists_wardRealOddChartTest_extension K V hK hV hKV a ha odd hom
  obtain ⟨_, _, hSeven⟩ := exists_wardPhysicalPhaseTensor_compactPatchUniform K V hK hV hKV m (metricDensity ∘ G)
    hm hw hSym aG haG hOddG hHomG ϑ hϑ hCut hFlat κ hκ hκsmall
  obtain ⟨Cphase, hCphase, hP⟩ := exists_wardPhysicalPhase_originalPatchFamily K V hK hV hKV m (metricDensity ∘ G)
    hm hw hSym aG haG hOddG hHomG ϑ hϑ hCut hFlat κ hκ hκsmall
  refine ⟨c₀, δ₀, Cphase, hc₀, hδ₀, hδ₁, hCphase, ?_⟩
  intro cThin hcThin hcThin₀
  obtain ⟨CN, hCN, nearBound⟩ := hN cThin hcThin hcThin₀
  refine ⟨CN * ((Fintype.card WardNearSlot : ℝ) * (2 * Cp))^3, by positivity, ?_⟩
  intro δ hδ η hη s ℓ hℓ hℓ₁ x₀ P hPatch Z e he σ hσ hRaw hCenter z T diff gradPhase H near phase mass
  have nearActual := (nearBound δ hδ s ℓ hℓ hPatch Z e he Cp hCp hRaw).2
  have sameTest (x : E) (hx : x ∈ K) : (fun ξ => aG (x, ξ)) = fun ξ => a (x, ξ) := funext (hSame x hx)
  refine ⟨fun j => ?_, fun j n k => ?_, ?_⟩
  · filter_upwards [hσ.tendsto_atTop.eventually (nearActual j j.property)] with n hn
    have hc : patchCenter ℓ (j : LatticeIndex) ∈ K := hCenter j
    simpa only [dif_pos hc, wardActualNearCubicForm, near, H, z, x₀, mass, P] using hn
  · have h := (hSeven (x₀ j) (hCenter j) k).1 wi wo (wide (x₀ j) (hCenter j)) η hη i o (z j n)
    rw [sameTest (x₀ j) (hCenter j)] at h
    exact h
  intro Ce α hCe hα hGrad ε hε
  let Zσ (j : LatticeIndex) (n : ℕ) := Z j (σ n)
  have hRawσ (j : LatticeIndex) (hj : j ∈ s) : ∀ᶠ n in atTop,
      ProjectedPatchLpBounds 3 (Zσ j n) (P j) (Cp * e (σ n)) (Cp * (1 + e (σ n) / ℓ)) :=
    hσ.tendsto_atTop.eventually (hRaw j hj)
  have hPhase := hP wi wo wide η hη i o s ℓ hℓ hℓ₁ hPatch Zσ (e ∘ σ) (he.comp hσ.tendsto_atTop) Cp Ce α
    hCp hCe hα hRawσ (fun j hj => hGrad ⟨j,hj⟩) ε hε
  filter_upwards [hPhase] with n hn
  let Φ (j : LatticeIndex) : ℂ := if hc : patchCenter ℓ j ∈ K then
      wardPhysicalPhaseRemainder ϑ κ (m (patchCenter ℓ j)) (metricDensity (G (patchCenter ℓ j)))
        (fun ξ => aG (patchCenter ℓ j, ξ)) wi wo (wide (patchCenter ℓ j) hc) hη i o (Zσ j n) else 0
  have hEq (j : s) : Φ j = phase j n := by
    dsimp only [Φ]
    rw [dif_pos (hCenter j), sameTest (x₀ j) (hCenter j)]
  change (∑ j ∈ s, ‖Φ j‖) ≤ _ at hn
  rw [← Finset.sum_coe_sort] at hn
  simp only [hEq] at hn
  convert hn using 1
  ring

end Burnett.V03
