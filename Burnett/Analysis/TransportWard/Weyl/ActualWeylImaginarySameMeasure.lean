import Burnett.Analysis.TransportWard.Weyl.EulerWeylDifferentialComm
import Burnett.Analysis.TransportWard.Weyl.EulerWeylImaginaryPairing
import Burnett.Analysis.TransportWard.Weyl.EulerWeylLocality
import Burnett.Analysis.TransportWard.Weyl.ActualWeylSameMeasureContraction
import Burnett.Analysis.TransportWard.Weyl.QuadraticClassicalProfile
import Burnett.Analysis.TransportWard.Weyl.ActualCanonicalWeylRegularity
import Burnett.Analysis.TransportWard.Weyl.CanonicalWeylPrincipalSameMeasureLimit
import Burnett.Analysis.TransportWard.Weyl.NormalizedWeylPerturbationBounds
import Burnett.Analysis.TransportWard.Weyl.WindowedWeylSchwartzAction

set_option autoImplicit false
set_option maxHeartbeats 6900000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference ManifoldMetric
open ManifoldBilinear ManifoldMetricSequence MaximalChart Burnett.RicciSymbol Burnett.V02 Burnett.A03
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction scalarSchwartzProduct)
open Burnett.A02.FrequencySplit (tau)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.AtlasVolumeGradient (fixedComponent)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped ContDiff Topology Manifold BigOperators ComplexConjugate

open private lowerZeroTerm lowerFirstTerm from Burnett.Analysis.TransportWard.Weyl.EulerWeylDifferentialComm

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "J" => Fin 4 × Fin 4

private theorem eulerWeylDifferentialField_eq_complexEulerCoefficientAction {ι : Type*} [Fintype ι]
    (c₀ : ι → ι → SchwartzMap E₀ ℂ) (c₁ : ι → ActionSlot ι → SchwartzMap E₀ ℂ)
    (c₂ : ι → ι → J → SchwartzMap E₀ ℂ) (u : ι → SchwartzMap E₀ ℂ) (i : ι) :
    eulerWeylDifferentialField c₀ (fun i j k => c₁ i (k,j)) c₂ u i =
      schwartzComplexEulerCoefficientAction c₀ c₁ c₂ u i := by
  unfold eulerWeylDifferentialField schwartzComplexEulerCoefficientAction
    lowerZeroTerm lowerFirstTerm variableDensityPrincipalSchwartzField
  simp only [Fintype.sum_prod_type,neg_one_smul,Finset.sum_neg_distrib,sub_eq_add_neg,
    frozenSchwartzCoordinatePartial]
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset (Fin 4)))]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The actual nested-cutoff local Weyl test of the genuine density Euler
variation has the factor-four limit on the same F05 physical measure. -/
theorem tendsto_preferredLocalizedEulerWeylImaginaryPair_sameMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (μ : Measure (Cosphere r)) (hμ : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (K : Set M) (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus)
    (χ : D) (hχ : tsupport (χ : E₀ → ℝ) ⊆ (AtlasChart.atPoint q.center).chart '' K)
    (a β : E₀ → Covector → ℝ) (L : Set E₀) (hL : IsCompact L)
    (hLU : L ⊆ (chartAt E₀ q.center).target)
    (haS : ∀ x ∉ L, ∀ ξ, a x ξ = 0) (hβS : ∀ x ∉ L, ∀ ξ, β x ξ = 0)
    (haDiff : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set Covector)))
    (hβDiff : ContDiff ℝ ∞ (uncurry β))
    (haD : ∀ x (s : ℝ), 0 < s → ∀ ξ : Covector, ξ ≠ 0 → a x (s • ξ) = s * a x ξ)
    (R₀ : ℝ) (hMatch : ∀ y ξ, R₀ ≤ ‖(WithLp.toLp 2 ξ : E₀)‖ → β y ξ = a y ξ)
    (θ : E₀ → ℝ) (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hθL : ∀ x ∈ L, θ x = 1)
    (hχθ : ∀ x ∈ tsupport θ, (χ : E₀ → ℝ) =ᶠ[𝓝 x] fun _ : E₀ => (1 : ℝ))
    (R : ℝ)
    (hAmpCompact : CompactRadianTwoPointOrderOne
      (windowedWeylAmplitude θ (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ))) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds
      (windowedWeylAmplitude θ (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ))))
    (hβscaled : ScaledJointOrderOne (normalizedWeylSymbol (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ)))) :
    let c := AtlasChart.atPoint q.center
    let U := (chartAt E₀ q.center).target
    let C := orthonormalMetricDirection
    let b := normalizeMetricComponents ∘ symmetricChartMetricComponents B q.center
    let G := chartLowerMetric B q.center
    let hχc : tsupport (χ : E₀ → ℝ) ⊆ c.chart.target :=
      hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left (fun _ hy => (hSub hy).1)))
    let w (n : ℕ) (i : I) := (symmetricMetricScale i : ℂ) •
      fixedWeylPerturbationSchwartz B g hB hg c χ hχc (σ n) i.val
    let u (n : ℕ) (y : E₀) (i : I) : ℂ :=
      (symmetricMetricScale i * fixedComponent B g c (σ n) i.val y : ℝ)
    let P := windowedWeylLeftSymbol θ (fun x ξ => (β x (WithLp.ofLp ξ) : ℂ)) R hAmpCompact
    let H (p : Cosphere r) :=
      canonicalBracket (coordinateHamiltonian G) a (c.chart (projection p)) (atlasChartUnitCovector c p)
    Tendsto (fun n => 2 * (∫ x in U, ∑ i : I,
      conj (firstOrderAction P (w n i) x) *
      complexLinearizedCoordinateDensityEuler C b (u n) x i).im) atTop
      (𝓝 (4 * ∫ p, H p ∂(μ.restrict (amplitudeCosphereWindow r K)))) := by
  intro c U C b G hχc w u P H
  let Kχ := tsupport (χ : E₀ → ℝ)
  have hKU : Kχ ⊆ U := hχc
  have hKχ : IsCompact Kχ := test_compactSupport χ
  have hθχ : tsupport θ ⊆ Kχ := fun x hx =>
    subset_tsupport (χ : E₀ → ℝ) (by
      change (χ : E₀ → ℝ) x ≠ 0
      rw [(hχθ x hx).self_of_nhds]
      exact one_ne_zero)
  have hχL (x : E₀) (hx : x ∈ L) : (χ : E₀ → ℝ) x = 1 :=
    (hχθ x (subset_tsupport θ (by change θ x ≠ 0; rw [hθL x hx]; exact one_ne_zero))).self_of_nhds
  let βᵣ (x ξ : E₀) : ℝ := β x (WithLp.ofLp ξ)
  let β𝒸 (x ξ : E₀) : ℂ := βᵣ x ξ
  have hβᵣ : ContDiff ℝ ∞ (uncurry βᵣ) := by
    let Q : E₀ ≃L[ℝ] Covector := PiLp.continuousLinearEquiv 2 ℝ _
    have hQ : ContDiff ℝ ∞ (fun p : E₀ × E₀ => (p.1, Q p.2)) :=
      contDiff_fst.prodMk (Q.contDiff.comp contDiff_snd)
    exact hβDiff.comp hQ
  have hθβᵣ (x ξ : E₀) (hx : βᵣ x ξ ≠ 0) : θ x = 1 :=
    hθL x (by by_contra hm; exact hx (hβS x hm (WithLp.ofLp ξ)))
  have hθβ (x ξ : E₀) (hx : β𝒸 x ξ ≠ 0) : θ x = 1 :=
    hθβᵣ x ξ (fun hz => hx (by simp only [β𝒸,hz,Complex.ofReal_zero]))
  have hβReal (x ξ : E₀) : conj (β𝒸 x ξ) = β𝒸 x ξ := Complex.conj_ofReal _
  obtain ⟨Bₐ,hBₐ,hBₐSup,hBₐSym⟩ := exists_windowedWeylSchwartz_selfAdjoint
    θ β𝒸 R hAmpCompact hAmp hθβ hθ hθc hβscaled hβReal
  obtain ⟨V,hV,hKV,hVU,c₀,c₁,c₂,hCoeffs,hE⟩ :=
    exists_actualNormalizedEulerWeylCoefficientPacket B hB hSig q.center Kχ hKχ hKU
  have hGc : assembledCoordinateMetric C b = G :=
    assembledCoordinateMetric_orthonormalMetricComponents B hSig.isSymmetric q.center
  have hbs : ContDiffOn ℝ ∞ b U := by
    apply contDiffOn_pi.mpr
    intro i
    change ContDiffOn ℝ ∞ (fun x => symmetricMetricScale i * G x i.val.1 i.val.2) U
    exact contDiffOn_const.mul (ManifoldBilinear.contDiffOn_metricComponents B hB q.center i.val.1 i.val.2)
  have hDet (x : E₀) (hx : x ∈ V) : Matrix.det (assembleMetricComponents C (b x)) ≠ 0 := by
    change (assembledCoordinateMetric C b x).det ≠ 0
    rw [hGc]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate q.center (hVU hx)
  have hSch (n : ℕ) (i : I) : tsupport (w n i : E₀ → ℂ) ⊆ Kχ := by
    apply closure_minimal _ (isClosed_tsupport (χ : E₀ → ℝ))
    intro x hx
    by_contra hOut
    apply hx
    have h0 : (χ : E₀ → ℝ) x = 0 := image_eq_zero_of_notMem_tsupport hOut
    change (symmetricMetricScale i : ℂ) * ((χ : E₀ → ℝ) x * fixedComponent B g c (σ n) i.val x : ℝ) = 0
    simp only [h0,zero_mul,Complex.ofReal_zero,mul_zero]
  have hSchB (n : ℕ) (i : I) : tsupport (Bₐ (w n i) : E₀ → ℂ) ⊆ Kχ :=
    (hBₐSup _).trans hθχ
  have hUbound (i : I) : ∃ C : ℝ, ∀ n, Real.sqrt (schwartzH1Energy (w n i)) ≤ C := by
    obtain ⟨⟨C,hC⟩,_⟩ := exists_original_normalizedWeylPerturbation_bounds
      r B g hB hg hSig.isNondegenerate hconv hb c χ hχc i
    exact ⟨C,fun n => hC (σ n)⟩
  have hVbound (i : I) : Tendsto (fun n => ‖(w n i).toLp 2 volume‖) atTop (𝓝 0) :=
    (exists_original_normalizedWeylPerturbation_bounds r B g hB hg hSig.isNondegenerate hconv hb c χ hχc i).2.comp
      hσ.tendsto_atTop
  let Lsch := schwartzComplexEulerCoefficientAction c₀ c₁ c₂
  have hLsch : eulerWeylDifferentialField c₀ (fun i j k => c₁ i (k,j)) c₂ = Lsch :=
    funext (fun f => funext (eulerWeylDifferentialField_eq_complexEulerCoefficientAction c₀ c₁ c₂ f))
  have hLim := tendsto_preferredLocalizedCanonicalWeylPrincipalPair_sameMeasure
    r B g hB hSig hg hsG hnG hconv hb hv σ hσ A hA μ hμ q ν hf hRep K hK hSub
    χ hχ a β L hL hLU haS hβS hχL haDiff hβDiff haD R₀ hMatch
  have hComm := tendsto_eulerWeylDifferentialComm_of_canonicalPair C G c₀ (fun i j k => c₁ i (k,j)) c₂
    θ βᵣ R hθc hβᵣ hAmpCompact hAmp hθβᵣ hβscaled
    (fun y hy i j d => (hCoeffs y (hKV (hθχ hy)) i j d).1)
    (fun y hy i j d => (hCoeffs y (hKV (hθχ hy)) i j d).2)
    Bₐ hBₐ w w hUbound hVbound (4 * ∫ p, (H p : ℂ) ∂(μ.restrict (amplitudeCosphereWindow r K)))
    hLim
  dsimp only at hComm
  rw [hLsch] at hComm
  have hAt (x : E₀) (hx : x ∈ V) (i : I) (f : E₀ → I → ℝ) (hfs : ContDiff ℝ ∞ f) :=
    hE f hfs.contDiffOn x hx i
  have hGreen (n : ℕ) := integral_complexEulerWeyl_commutator_eq_two_im C b hV hKχ hKV
    (hbs.mono hVU) hDet c₀ c₁ c₂ hAt Bₐ hBₐSym (w n) (hSch n) (hSchB n)
  have hPair (n : ℕ) :
      (∫ x, ∑ i : I, conj (Bₐ (w n i) x) * Lsch (w n) i x) =
      ∫ x in U, ∑ i : I, conj (firstOrderAction P (w n i) x) *
        complexLinearizedCoordinateDensityEuler C b (fun y j => w n j y) x i := by
    rw [← integral_indicator (chartAt E₀ q.center).open_target.measurableSet]
    apply integral_congr_ae
    exact .of_forall fun x => by
      by_cases hx : x ∈ V
      · rw [indicator_of_mem (hVU hx)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hEq := schwartzComplexEulerCoefficientAction_eq_complexified C b univ x i c₀ c₁ c₂
          (fun f hf => hAt x hx i f (contDiffOn_univ.mp hf)) (w n)
        rw [hBₐ,show Lsch (w n) i x = _ from hEq]
      · have hZ (i : I) : Bₐ (w n i) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hx' => hx (hKV (hSchB n i hx')))
        have hZ' (i : I) : firstOrderAction P (w n i) x = 0 :=
          (hBₐ (w n i) x).symm.trans (hZ i)
        by_cases hu : x ∈ U
        · rw [indicator_of_mem hu]
          simp only [hZ,hZ',map_zero,zero_mul,Finset.sum_const_zero]
        · rw [indicator_of_notMem hu]
          simp only [hZ,map_zero,zero_mul,Finset.sum_const_zero]
  have hCplx : Tendsto (fun n => Complex.ofReal (2 * (∫ x in U, ∑ i : I,
      conj (firstOrderAction P (w n i) x) *
      complexLinearizedCoordinateDensityEuler C b (fun y j => w n j y) x i).im)) atTop
      (𝓝 (4 * ∫ p, (H p : ℂ) ∂(μ.restrict (amplitudeCosphereWindow r K)))) := by
    refine hComm.congr (fun n => ?_)
    have hg' := hGreen n
    change (∫ x : E₀, ∑ i : I, conj (w n i x) *
      (Complex.I * (Lsch (fun j => Bₐ (w n j)) i x - Bₐ (Lsch (w n) i) x))) =
      Complex.ofReal (2 * (∫ x : E₀, ∑ i : I, conj (Bₐ (w n i) x) * Lsch (w n) i x).im) at hg'
    exact hg'.trans (congrArg (fun z : ℂ => Complex.ofReal (2 * z.im)) (hPair n))
  have hRemove (n : ℕ) :
      (∫ x in U, ∑ i : I, conj (firstOrderAction P (w n i) x) *
        complexLinearizedCoordinateDensityEuler C b (fun y j => w n j y) x i) =
      ∫ x in U, ∑ i : I, conj (firstOrderAction P (w n i) x) *
        complexLinearizedCoordinateDensityEuler C b (u n) x i := by
    apply integral_eulerPair_congr_on_test_support C b U (tsupport θ)
    · intro i x hx
      exact (hBₐ (w n i) x).symm.trans (image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (hBₐSup (w n i) hx')))
    · intro x hx
      filter_upwards [hχθ x hx] with y hy
      funext i
      change (symmetricMetricScale i : ℂ) *
          ((χ : E₀ → ℝ) y * fixedComponent B g c (σ n) i.val y : ℝ) =
        ((symmetricMetricScale i * fixedComponent B g c (σ n) i.val y : ℝ) : ℂ)
      rw [hy,one_mul,Complex.ofReal_mul]
  simp only [hRemove] at hCplx
  have hTarget : Complex.ofReal (4 * ∫ p, H p ∂(μ.restrict (amplitudeCosphereWindow r K))) =
      4 * ∫ p, (H p : ℂ) ∂(μ.restrict (amplitudeCosphereWindow r K)) := by
    rw [integral_complex_ofReal, Complex.ofReal_mul]
    norm_num
  rw [← hTarget] at hCplx
  have hRe := (Complex.continuous_re.tendsto _).comp hCplx
  simpa only [Function.comp_apply,Complex.ofReal_re] using hRe

end Burnett.V03.Palatini
