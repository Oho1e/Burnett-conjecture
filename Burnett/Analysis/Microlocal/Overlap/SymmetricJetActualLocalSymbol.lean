import Burnett.Analysis.Microlocal.Overlap.CompactLeftClassicalOperator
import Burnett.Analysis.Microlocal.Overlap.SymmetricJetChartCompression
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly

/-! The near limit of the actual bundle form follows directly from its chart symbols. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 6100000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.Microlocal.AtlasVolumeGradient
  (fixedVolumeCovariantGradientSchwartz fixedVolumeCovariantGradientSchwartz_tsupport)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

open private firstOrderAction_mul_base from Burnett.Analysis.Microlocal.Overlap.AngularBilateralPrincipal

local notation "E" => CoordinateSpace

private theorem classicalLeftPairing_leftCutoff_eq (χ : D) (b : E → E → ℂ) (f w : SchwartzMap E ℂ)
    (hχ : ∀ x ∈ tsupport (f : E → ℂ), (χ : E → ℝ) x = 1) :
    classicalLeftPairing (leftCutoffClassicalSymbol χ b) f w = classicalLeftPairing b f w := by
  unfold classicalLeftPairing
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change conj (f x) * Burnett.Analysis.FirstOrderDyadic.firstOrderAction
      (fun y ξ => physicalCoefficient χ y * b y ξ) w x = _
    rw [firstOrderAction_mul_base]
    by_cases hx : x ∈ tsupport (f : E → ℂ)
    · simp [physicalCoefficient, hχ x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]

private theorem linearArrayPairing_eq_sum
    {ι P X Y : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid P] [Module ℂ P]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (Q : X →ₗ⋆[ℂ] (Y →ₗ[ℂ] ℂ)) (L : (ι → P) →ₗ[ℂ] X) (R : (ι → P) →ₗ[ℂ] Y)
    (u w : ι → P) :
    Q (L u) (R w) = ∑ i, ∑ j, Q (L (Pi.single i (u i))) (R (Pi.single j (w j))) := by
  let u' (i : ι) := L (Pi.single i (u i))
  let w' (j : ι) := R (Pi.single j (w j))
  have hU : ∑ i, u' i = L u := by simp only [u', ← map_sum, LinearMap.sum_single_apply]
  have hW : ∑ j, w' j = R w := by simp only [w', ← map_sum, LinearMap.sum_single_apply]
  change Q (L u) (R w) = ∑ i, ∑ j, Q (u' i) (w' j)
  rw [← hU, ← hW]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]

attribute [local irreducible] compactSymmetricJetChartTestLinear

/-- For one actual compact-section form with the indicated full-symbol action
near the chosen windows, the same original covariance yields its local limit.
The bounded Euclidean operators are constructed from the full symbols. -/
theorem tendsto_originalVolume_actualSymmetricJetLocalSymbol
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hLocal : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (Q : SymmetricJetGlobalForm M) (c : AtlasChart M)
    (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (η₀ η₁ ρ₀ ρ₁ : D)
    (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K) (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (hρ₀ : tsupport (ρ₀ : E → ℝ) ⊆ c.chart.target) (hρ₁ : tsupport (ρ₁ : E → ℝ) ⊆ c.chart.target)
    (b a : JetSlot → JetSlot → E → E → ℂ)
    (hbDiff : ∀ i j, ContDiffOn ℝ ∞ (uncurry (b i j)) (c.chart.target ×ˢ univ))
    (haDiff : ∀ i j, ContDiffOn ℝ ∞ (uncurry (a i j)) (c.chart.target ×ˢ ({0}ᶜ : Set E)))
    (hDegree : ∀ i j x, x ∈ c.chart.target → ∀ (s : ℝ), 0 < s → ∀ ξ : E,
      ξ ≠ 0 → a i j x (s • ξ) = a i j x ξ)
    (hLarge : ∀ i j (S : Set E), IsCompact S → S ⊆ c.chart.target → ∃ R : ℝ,
      ∀ m : ℕ, ∃ Bm : ℝ, 0 ≤ Bm ∧ ∀ x ∈ S, ∀ ξ : E, R ≤ ‖ξ‖ →
        (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => b i j y ξ - a i j y ξ) x‖ ≤ Bm)
    (hActual : ∀ i j (f w : SchwartzMap E ℂ), tsupport (f : E → ℂ) ⊆ tsupport (η₀ : E → ℝ) →
      tsupport (w : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) →
      Q (compactSymmetricJetChartTestLinear B hB hn c ρ₀ hρ₀ (Pi.single i f))
        (compactSymmetricJetChartTestLinear B hB hn c ρ₁ hρ₁ (Pi.single j w)) =
        classicalLeftPairing (b i j) f w) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₀ h₀c
    let w := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c η₁ h₁c
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let G (p : Cosphere r) :=
      let z := fixedChartPhase c p.val
      ∑ i : JetSlot, ∑ j : JetSlot,
        conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a i j z.1 (WithLp.toLp 2 z.2)) *
          atlasOrderedJetEntry c A.density p j i
    Integrable G τ ∧
    Tendsto (fun n => conj (Q (compactSymmetricJetChartTestLinear B hB hn c ρ₀ hρ₀ (u (σ n)))
        (compactSymmetricJetChartTestLinear B hB hn c ρ₁ hρ₁ (w (σ n))))) atTop (𝓝 (∫ p, G p ∂τ)) := by
  intro h₀c h₁c u w τ G
  have hK' : IsCompact (c.chart '' K) := hK.image_of_continuousOn (c.chart.continuousOn.mono hKc)
  have hKt : c.chart '' K ⊆ c.chart.target := image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc)
  obtain ⟨J, _, _, hJ, α, hα, hαC, hαS, _, hαK⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK' c.chart.open_target hKt
  let χ : D := ⟨α, hα, hαC⟩
  have hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target := hαS.trans hJ
  let F (i j : JetSlot) (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a i j z.1 (WithLp.toLp 2 z.2)) *
      atlasOrderedJetEntry c A.density p j i
  have hEntry (i j : JetSlot) : Integrable (F i j) τ ∧
      Tendsto (fun n => conj (Q (compactSymmetricJetChartTestLinear B hB hn c ρ₀ hρ₀ (Pi.single i (u (σ n) i)))
          (compactSymmetricJetChartTestLinear B hB hn c ρ₁ hρ₁ (Pi.single j (w (σ n) j)))))
        atTop (𝓝 (∫ p, F i j p ∂τ)) := by
    obtain ⟨R, hR⟩ := hLarge i j _ (test_compactSupport χ) hχ
    obtain ⟨T, hT, _, hDecay⟩ := exists_compactLeftClassicalOperator c.chart.target c.chart.open_target χ hχ
      (b i j) (a i j) (hbDiff i j) (haDiff i j) (hDegree i j) R hR
    let b' := leftCutoffClassicalSymbol χ (b i j)
    let a' := leftCutoffClassicalSymbol χ (a i j)
    have hb' := (leftCutoffClassicalSymbol_smoothOn χ c.chart.open_target isOpen_univ hχ
      (hbDiff i j)).mono (Set.prod_mono (subset_univ c.chart.target) Subset.rfl)
    have ha' := (leftCutoffClassicalSymbol_smoothOn χ c.chart.open_target isOpen_compl_singleton hχ
      (haDiff i j)).mono (Set.prod_mono (subset_univ c.chart.target) Subset.rfl)
    have hDeg' (x : E) (hx : x ∈ c.chart.target) (s : ℝ) (hs : 0 < s) (ξ : E) (hξ : ξ ≠ 0) :
        a' x (s • ξ) = a' x ξ := by
      change physicalCoefficient χ x * a i j x (s • ξ) = physicalCoefficient χ x * a i j x ξ
      rw [hDegree i j x hx s hs ξ hξ]
    have hLarge' (S : Set E) (_ : IsCompact S) (_ : S ⊆ c.chart.target) : ∃ R' : ℝ,
        ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ : E, R' ≤ ‖ξ‖ →
          (1 + ‖ξ‖) * ‖iteratedFDeriv ℝ m (fun y => b' y ξ - a' y ξ) x‖ ≤ C := by
      refine ⟨max 1 R, fun m => ?_⟩
      obtain ⟨C, hC, hL⟩ := hDecay m
      exact ⟨C, hC, fun x _ ξ hξ => hL x ξ hξ⟩
    obtain ⟨hI, hLim⟩ := hLocal c K hK hKc η₀ η₁ h₀ h₁ T b' a' hb' ha' hDeg' hLarge'
      (fun f z _ _ => hT f z) i j
    let F' (p : Cosphere r) :=
      let z := fixedChartPhase c p.val
      conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a' z.1 (WithLp.toLp 2 z.2)) *
        atlasOrderedJetEntry c A.density p j i
    have hAE : F' =ᵐ[τ] F i j := by
      filter_upwards [ae_restrict_mem (μ := A.control) (measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet)]
        with p hp
      have hz : (fixedChartPhase c p.val).1 ∈ c.chart '' K := by
        rw [fixedChartPhase_of_mem c p.val (hKc hp)]
        exact mem_image_of_mem _ hp
      have hχz : (χ : E → ℝ) (fixedChartPhase c p.val).1 = 1 := hαK _ hz
      simp only [F', F, a', leftCutoffClassicalSymbol, physicalCoefficient, hχz, Complex.ofReal_one, one_mul]
    change Integrable F' τ at hI
    change Tendsto (fun n => inner ℂ (T ((w (σ n) j).toLp 2 volume)) ((u (σ n) i).toLp 2 volume))
      atTop (𝓝 (∫ p, F' p ∂τ)) at hLim
    rw [integral_congr_ae hAE] at hLim
    refine ⟨hI.congr hAE, hLim.congr fun n => ?_⟩
    have hU := fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c η₀ h₀c (σ n) i
    have hW := fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c η₁ h₁c (σ n) j
    rw [← inner_conj_symm, hT, classicalLeftPairing_leftCutoff_eq, hActual i j _ _ hU hW]
    exact fun x hx => hαK x (h₀ (hU hx))
  have hRow (i : JetSlot) : Integrable (fun p => ∑ j : JetSlot, F i j p) τ :=
    integrable_finset_sum _ (fun j _ => (hEntry i j).1)
  refine ⟨integrable_finset_sum _ (fun i _ => hRow i), ?_⟩
  have hIntegral : (∫ p, G p ∂τ) = ∑ i : JetSlot, ∑ j : JetSlot, ∫ p, F i j p ∂τ :=
    (integral_finset_sum _ (fun i _ => hRow i)).trans
      (Finset.sum_congr rfl (fun i _ => integral_finset_sum _ (fun j _ => (hEntry i j).1)))
  rw [hIntegral]
  apply (tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun j _ => (hEntry i j).2))).congr
  intro n
  rw [linearArrayPairing_eq_sum]
  simp only [map_sum]

end Burnett.Microlocal.Overlap
