import Burnett.Analysis.TransportWard.Weyl.ActualQuadraticThirdVariation
import Burnett.Analysis.TransportWard.Weyl.ActualWeylOutputL2
import Burnett.Analysis.TransportWard.Weyl.CompactMetricSegment
import Burnett.Analysis.TransportWard.Weyl.NormalizedWeylPerturbationBounds
import Burnett.Analysis.TransportWard.Weyl.OrderedCubicPrincipalVariation
import Burnett.Analysis.TransportWard.Weyl.ThirdBackgroundLimit

set_option autoImplicit false
set_option maxHeartbeats 8200000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence MaximalChart
open Burnett.A03 Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol Burnett.C02
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix.Norms.Elementwise Topology

local notation "I" => SymmetricMetricSlot
local notation "J" => OrderedPair

private theorem schwartzH1Energy_controls_value_and_partial (f : SchwartzMap E ℂ) :
    ‖f.toLp 2 volume‖ ≤ Real.sqrt (schwartzH1Energy f) ∧
    ∀ a : Index, ‖(energyPartial a f).toLp 2 volume‖ ≤ Real.sqrt (schwartzH1Energy f) := by
  let L (j : Index) := ‖(energyPartial j f).toLp 2 volume‖ ^ 2
  have hS : 0 ≤ ∑ j, L j := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : schwartzH1Energy f = ‖f.toLp 2 volume‖ ^ 2 + ∑ j, L j := rfl
  refine ⟨?_, fun j => ?_⟩
  · rw [← Real.sqrt_sq (norm_nonneg (f.toLp 2 volume))]
    exact Real.sqrt_le_sqrt ((le_add_of_nonneg_right hS).trans_eq hE.symm)
  · rw [← Real.sqrt_sq (norm_nonneg ((energyPartial j f).toLp 2 volume))]
    apply Real.sqrt_le_sqrt
    calc
      _ = L j := rfl
      _ ≤ ∑ k, L k := Finset.single_le_sum (f := L) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ‖f.toLp 2 volume‖ ^ 2 + ∑ k, L k := le_add_of_nonneg_left (sq_nonneg _)
      _ = _ := hE.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The tested original quadratic Euler expression and the true A03
principal density on ordered receiving components differ by a sequence
tending to zero, with the same physical Weyl action in both expressions. -/
theorem exists_originalWeylQuadraticPrincipalLimit
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hgs : ∀ n, IsSymmetric (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ (chartAt E c).target)
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (hAmp : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hDir : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hθβ : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (hReal : ∀ x ξ, conj (β x ξ) = β x ξ) (hOdd : ∀ x ξ, β x (-ξ) = -β x ξ)
    (hPlateau : ∀ x ∈ tsupport θ, (χ : E → ℝ) =ᶠ[𝓝 x] fun _ : E => (1 : ℝ)) :
    let U := (chartAt E c).target
    let S := orthonormalMetricDirection
    let b := normalizedChartMetric B c
    let h (n : ℕ) := normalizedChartPerturbation B (g n) c
    let P := windowedWeylLeftSymbol θ β R hAmp
    let Z₀ := fixedWeylPerturbationSchwartz B g hB hg (AtlasChart.atPoint c) χ hχ
    let b' (x : E) (i : J) := assembleMetricComponents S (b x) i.1 i.2
    let C (a d : Index) (i j k : J) (x : E) :=
      Complex.ofReal (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b'
        (χ : E → ℝ) a d i j k x)
    ∃ Z W : ℕ → RealEnergyField J,
      (∀ n i, (Z n).val i = Z₀ n i) ∧
      (∀ n i x, (W n).val i x = (-Complex.I) * firstOrderAction P (Z₀ n i) x) ∧
      (∀ n i, tsupport ((W n).val i : E → ℂ) ⊆ tsupport θ) ∧
      Tendsto (fun n =>
        (∫ x in U, ∑ i : I, conj ((-Complex.I) *
          firstOrderAction P ((symmetricMetricScale i : ℂ) • Z₀ n i.val) x) *
          Complex.ofReal (deriv (deriv (fun t : ℝ =>
            coordinateDensityEuler S (fun y => b y + t • h n y) x i)) 0)).re -
        ∫ x, (principalVariationDensity C (Z n).val (fun i => (W n).val i) x).re) atTop (𝓝 0) := by
  classical
  intro U S b h P Z₀ b' C
  let U₀ := AtlasChart.atPoint c
  let K := tsupport θ
  let L := tsupport (χ : E → ℝ)
  have hU : IsOpen U := (chartAt E c).open_target
  have hK : IsCompact K := hθc.isCompact
  have hL : IsCompact L := (test_compactSupport χ).isCompact
  have hOne (x : E) (hx : x ∈ K) : (χ : E → ℝ) x = 1 := (hPlateau x hx).eq_of_nhds
  have hKU : K ⊆ U := fun x hx => hχ (subset_tsupport (χ : E → ℝ)
    (show (χ : E → ℝ) x ≠ 0 by rw [hOne x hx]; exact one_ne_zero))
  have hnd (x : E) (hx : x ∈ U) : assembleMetricComponents S (b x) ∈ nonsingularMetricDomain := by
    change (assembledCoordinateMetric S b x).det ≠ 0
    rw [show assembledCoordinateMetric S b =
        metricComponents (ManifoldMetricTransition.coordinateBilinear B c) from
      assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric c]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c hx
  have hbs : ContDiffOn ℝ ∞ b U := contDiffOn_normalizedChartMetric B hB c
  obtain ⟨z,w,hz,hw,hws,hThird⟩ := exists_originalWeylQuadraticThirdVariation
    B g hB hg hSig c χ hχ θ β R hAmp hDir hθβ hθ hθc hβ hReal hOdd hPlateau
  have hzPoint (n : ℕ) (i : I) (x : E) : (z n).val i x =
      (symmetricMetricScale i : ℂ) * Complex.ofReal ((χ : E → ℝ) x * fixedComponent B g U₀ n i.val x) :=
    DFunLike.congr_fun (hz n i) x
  have hzs (n : ℕ) (i : I) : HasCompactSupport ((z n).val i : E → ℂ) := by
    apply hL.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hOut
    apply hx
    rw [hzPoint, image_eq_zero_of_notMem_tsupport hOut, zero_mul, Complex.ofReal_zero, mul_zero]
  choose e he heLim heBound using fun i : I => exists_compact_uniform_zero_norm_modulus hL
    (fun n => fixedComponent B g U₀ n i.val)
    (fun n => (fixedComponent_smooth B g hB hg U₀ n i.val).continuousOn.mono hχ)
    (fixedComponent_localUniform r B g hconv U₀ i.val L hL hχ)
  let ρ := (test_compactSupport χ).toSchwartzMap (test_smooth χ)
  let A (i : I) := ‖(symmetricMetricScale i : ℂ)‖ * SchwartzMap.seminorm ℝ 0 0 ρ
  have hA (i : I) : 0 ≤ A i := mul_nonneg (norm_nonneg _) (apply_nonneg _ _)
  let ε (n : ℕ) := ∑ i, A i * e i n
  have hε (n : ℕ) : 0 ≤ ε n := Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (he i n)
  have hεLim : Tendsto ε atTop (𝓝 0) := by
    have hLim := tendsto_finset_sum Finset.univ (fun i _ => (heLim i).const_mul (A i))
    simpa only [ε, mul_zero, Finset.sum_const_zero] using hLim
  have hSmall (n : ℕ) (i : I) (x : E) : ‖(z n).val i x‖ ≤ ε n := by
    rw [hzPoint, norm_mul, Complex.norm_real
      ((χ : E → ℝ) x * fixedComponent B g U₀ n i.val x), norm_mul, ← mul_assoc]
    by_cases hx : x ∈ L
    · have hχnorm : ‖(χ : E → ℝ) x‖ ≤ SchwartzMap.seminorm ℝ 0 0 ρ :=
        SchwartzMap.norm_le_seminorm ℝ ρ x
      have hF := mul_le_mul (mul_le_mul_of_nonneg_left hχnorm (norm_nonneg _)) (heBound i n x hx)
        (norm_nonneg _) (hA i)
      exact hF.trans (Finset.single_le_sum (fun j _ => mul_nonneg (hA j) (he j n)) (Finset.mem_univ i))
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, mul_zero, zero_mul]
      exact hε n
  choose L₀ hL₀ using fun i => (exists_original_normalizedWeylPerturbation_bounds
    r B g hB hg hSig.isNondegenerate hconv hb U₀ χ hχ i).1
  let D₀ := ∑ i, max 0 (L₀ i)
  have hD₀ : 0 ≤ D₀ := Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hE (n : ℕ) (i : I) : Real.sqrt (schwartzH1Energy ((z n).val i)) ≤ D₀ := by
    rw [hz]
    exact (hL₀ i n).trans ((le_max_right _ _).trans
      (Finset.single_le_sum (fun _ _ => le_max_left 0 _) (Finset.mem_univ i)))
  obtain ⟨Cw,hCw,hBw⟩ := Burnett.V03.exists_windowedWeylRealOutput_L2_bound θ β R hAmp hDir hθβ hθc hβ
  let T := max D₀ (Cw * D₀)
  have hT : 0 ≤ T := hD₀.trans (le_max_left _ _)
  have hVz (n : ℕ) (i : I) : ‖((z n).val i).toLp 2 volume‖ ≤ T :=
    (schwartzH1Energy_controls_value_and_partial ((z n).val i)).1.trans
      ((hE n i).trans (le_max_left _ _))
  have hDz (n : ℕ) (s : ActionSlot I) : ‖(energyPartial s.1 ((z n).val s.2)).toLp 2 volume‖ ≤ T :=
    ((schwartzH1Energy_controls_value_and_partial ((z n).val s.2)).2 s.1).trans
      ((hE n s.2).trans (le_max_left _ _))
  have hVw (n : ℕ) (i : I) : ‖((w n).val i).toLp 2 volume‖ ≤ T :=
    (hBw _ _ (hzs n i) (fun x => by rw [hw, hz])).trans
      ((mul_le_mul_of_nonneg_left (hE n i) hCw).trans (le_max_right _ _))
  have hTail := tendsto_thirdVariation_sub_localizedPrincipal_zero S b hU hbs hnd hK hKU (χ : E → ℝ)
    (test_smooth χ) hχ (test_compactSupport χ) hOne z w hws ε hε hεLim hSmall T hT hVz hDz hVw
  let Z (n : ℕ) := orderedRealEnergyField S (z n)
  let W (n : ℕ) := orderedRealEnergyField S (w n)
  have hOrd (n : ℕ) := orderedRealEnergyField_eq_originalWeylFields B g hB hg hSig.isSymmetric hgs c χ hχ
    P (windowedWeyl_leftSymbol_scaled_order_one θ β R hAmp hDir hθβ hβ).firstBaseFrequency.frequency n
    (z n) (w n) (hz n) (fun i x => by rw [hw, hz])
  have hWS (n : ℕ) (i : J) : tsupport ((W n).val i : E → ℂ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hOut
    have hzW (j : I) : (w n).val j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hOut (hws n j h))
    apply hx
    change (orderedRealEnergyField S (w n)).val (i.1,i.2) x = 0
    rw [orderedRealEnergyField_apply]
    change SchwartzMap.delta ℂ ℂ x (∑ j : I, (S j i.1 i.2 : ℂ) • (w n).val j) = 0
    simp only [map_sum, map_smul, SchwartzMap.delta_apply, smul_eq_mul, hzW, mul_zero, Finset.sum_const_zero]
  have hOrdQ (n : ℕ) :
      (∫ x, (principalVariationDensity
        (fun a d i j k x => Complex.ofReal (localizedEulerPrincipalVariationCoefficient S b
          (χ : E → ℝ) a d i j k x)) (z n).val (fun i => (w n).val i) x).re) =
        ∫ x, (principalVariationDensity C (Z n).val (fun i => (W n).val i) x).re := by
    rw [← setIntegral_principalVariationDensity_re_eq_localizedEulerCoefficient S b (χ : E → ℝ)
      (z n).val (fun i => (w n).val i) hOne (hws n)]
    change _ = ∫ x, (principalVariationDensity
      (fun a d i j k x => Complex.ofReal (localizedEulerPrincipalVariationCoefficient frozenActionOrderedBasis b'
        (χ : E → ℝ) a d i j k x)) (Z n).val (fun i => (W n).val i) x).re
    rw [← setIntegral_principalVariationDensity_re_eq_localizedEulerCoefficient frozenActionOrderedBasis b'
      (χ : E → ℝ) (Z n).val (fun i => (W n).val i) hOne (hWS n)]
    exact setIntegral_congr_fun hK.measurableSet fun x hx =>
      principalVariationDensity_re_eq_ordered S b (z n) (w n) x (hnd x (hKU hx))
  refine ⟨Z,W,fun n i => (hOrd n).1 i.1 i.2,fun n i => (hOrd n).2 i.1 i.2,hWS,?_⟩
  exact hTail.congr fun n => congrArg₂ (· - ·) (hThird n).symm (hOrdQ n)

end Burnett.V03.Palatini
