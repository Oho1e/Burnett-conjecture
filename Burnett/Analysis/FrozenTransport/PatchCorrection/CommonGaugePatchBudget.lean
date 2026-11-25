import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalGaugePatchEnvelope
import Burnett.Analysis.TransportPatches.OriginalProjectedPatchSource

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxRecDepth 6500
noncomputable section
namespace Burnett.V11

open Set Metric Filter MeasureTheory Matrix Burnett.P01 Burnett.RicciSymbol Burnett.V08 Burnett.C03 Burnett.Geometry
open ConnectionDifference CurvatureDifference InverseField
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.TransportWardSymbol (metricDensity)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ContDiff Topology ENNReal Matrix BigOperators

def originalMetricGaugeEnergy (θ : ℝ → ℝ) (κ : ℝ) (g₀ : E → Tensor2) (a : Joint → ℝ) (S : E → GaugeScreen)
    (x : E) (z : ProjectionSchwartzMatrix) : ℂ :=
  let m := matrixInverse (g₀ x)
  originalGaugePatchEnergy θ κ m (metricDensity (g₀ x)) (fun ξ => a (x,ξ)) (gaugeFrozenContraction m) (S x) z

def GaugePatchCoefficientBounds (B ℓ e : ℝ) (d : Index → Index → SchwartzMap E ℝ) (z : ProjectionSchwartzMatrix) (W : Set E) : Prop :=
  (∀ i k x, |d i k x| ≤ B*(ℓ+e)) ∧ (∀ i k x, ‖fderiv ℝ (d i k : E → ℝ) x‖ ≤ B*(1+e/ℓ)) ∧
  (∃ v, ProjectedPatchLpBounds 2 z W v ((B/4)*(1+e/ℓ))) ∧ ProjectedPatchLpBounds 4 z W (B*e) ((B/4)*(1+e/ℓ))

/-- The scalar source and the gauge energy belong to the very same C03
field. Both cutoffs, the original coefficient extension and the strict
subsequence appear explicitly. The constants precede the patch size. -/
theorem exists_commonGaugePatchBudget
    (U K Kplus : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKplus : IsCompact Kplus)
    (hNested : K ⊆ interior Kplus) (hKU : Kplus ⊆ U) (g₀ : E → Tensor2) (g : ℕ → E → Tensor2)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U) (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hND₀ : ∀ x ∈ U, Matrix.det (g₀ x) ≠ 0) (hND : ∀ n x, x ∈ U → Matrix.det (g n x) ≠ 0)
    (hSym₀ : ∀ x ∈ U, IsSymmetricTensor (g₀ x)) (hSym : ∀ n x, x ∈ U → IsSymmetricTensor (g n x))
    (hVac : ∀ n x, x ∈ U → ∀ i j, coordinateRicci (fun y => christoffel (projectedChartInverse (g n) y) (coordinateJet (g n) y)) x i j = 0)
    (hConv : TendstoUniformlyOn g g₀ atTop Kplus) (D : ℝ) (hD : 0 ≤ D) (hJet : ∀ n x, x ∈ Kplus → ‖coordinateJet (g n) x‖ ≤ D)
    (e : ℕ → ℝ) (he₀ : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0)) (hError : ∀ n x, x ∈ Kplus → ‖g n x-g₀ x‖ ≤ e n)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (θ : ℝ → ℝ) (hcut : ∀ t : ℝ, 1 ≤ t → θ t=0) (κ : ℝ) (hκ : 0<κ) (hsmall : κ<1/16)
    (a : Joint → ℝ) (ha : ∀ x ∈ Kplus, ContDiffOn ℝ ∞ (fun ξ => a (x,ξ)) {ξ : E | ξ ≠ 0})
    (odd : ∀ x ∈ Kplus, ∀ ξ, a (x,-ξ) = -a (x,ξ)) (hom : ∀ x ∈ Kplus, ∀ t : ℝ, 0<t → ∀ ξ, a (x,t • ξ) = t*a (x,ξ))
    (S : E → GaugeScreen) (deg : ∀ x ∈ Kplus, ∀ t : ℝ, 0<t → ∀ ξ, S x (t • ξ)=S x ξ)
    (jets : ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Kplus, ∀ k I J,
      GaugeProfileBound N M (gaugeTriadAngularProfile θ κ (matrixInverse (g₀ x)) (metricDensity (g₀ x)) (fun ξ => a (x,ξ))
        (gaugeFrozenContraction (matrixInverse (g₀ x))) (S x) k I J)) :
    ∃ ℓ₀ B : ℝ, 0<ℓ₀ ∧ 1≤B ∧ ∀ ℓ : ℝ, 0<ℓ → ℓ<ℓ₀ →
      ∃ (s : Finset LatticeIndex) (χ χplus : LatticeIndex → E → ℝ),
      let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6*ℓ)
      (∀ x ∈ thickening ℓ K, ∑ j ∈ s, χ j x^3=1) ∧
      (∀ x ∈ thickening ℓ K, ∀ v : E, ∑ j ∈ s, χ j x^2*fderiv ℝ (χ j) x v=0) ∧
      (∑ j ∈ s, volume (W j)) ≤ ((17^4:ℕ):ℝ≥0∞)*volume Kplus ∧
      (∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ ContDiff ℝ ∞ (χplus j) ∧ tsupport (χ j) ⊆ closedBall (patchCenter ℓ j) (4*ℓ) ∧
        tsupport (χplus j) ⊆ W j ∧ W j ⊆ interior Kplus ∧ ∀ x ∈ thickening ℓ (tsupport (χ j)), χplus j x=1) ∧
      Tendsto (fun n => Burnett.C04.correctionEnvelope ℓ (e (σ n))) atTop (𝓝 ℓ) ∧
      ∀ᶠ n in atTop, ∀ j ∈ s,
        let x₀ := patchCenter ℓ j
        let m := matrixInverse (g₀ x₀)
        ∃ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) (d : Index → Index → SchwartzMap E ℝ),
        (∀ i k x, z i k x = ((χ j x*(g (σ n) x i k-g₀ x i k) : ℝ) : ℂ)) ∧
        (∀ i k x, A.entry i k x = ((m i k+d i k x : ℝ) : ℂ)) ∧
        (∀ i k x, d i k x = correctionCoefficientPart (χplus j) (matrixInverse ∘ g (σ n)) m x i k) ∧
        (∀ i k, d i k = d k i) ∧
        GaugePatchCoefficientBounds B ℓ (e (σ n)) d z (W j) ∧
        (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤ B*(volume (W j)^((1:ℝ)/2)).toReal*(1+ℓ⁻¹+(ℓ^2)⁻¹*e (σ n))) ∧
        ‖originalMetricGaugeEnergy θ κ g₀ a S x₀ z‖ ≤ (16^3:ℝ)*(3*B^5)*(volume (W j)).toReal*Burnett.C04.correctionEnvelope ℓ (e (σ n)) := by
  obtain ⟨N,Co,Cw,ho,hw,op⟩ := exists_originalGauge_patchEnvelope
  obtain ⟨M,hM,jetsM⟩ := jets N
  obtain ⟨ℓ₀,Msrc,C,Ccut,Cp,hℓ₀,hSrc,hC,_,hCp,patches⟩ := exists_original_projectedPatchSource_family
    U K Kplus hU hK hKplus hNested hKU g₀ g hg₀ hg hND₀ hND hSym₀ hSym hVac hConv D hD hJet e he₀ he hError
  let p₂ : {p : ℝ // 1 < p} := ⟨2,by norm_num⟩
  let p₄ : {p : ℝ // 1 < p} := ⟨4,by norm_num⟩
  let B := 1 + Co*M+2*Cw*M+Msrc+4*C+4*Cp p₂+4*Cp p₄
  have bnds : 1≤B ∧ Co*M≤B ∧ 2*Cw*M≤B ∧ Msrc≤B ∧ C≤B ∧ 4*C≤B ∧ Cp p₂≤B/4 ∧ Cp p₄≤B/4 ∧ Cp p₄≤B := by
    dsimp [B]; have a₁ := mul_nonneg ho hM; have a₂ := mul_nonneg hw hM; have a₃ := hCp p₂; have a₄ := hCp p₄
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [a₁,a₂,hSrc,hC,a₃,a₄]
  obtain ⟨B1,Bo,Bw,Bsrc,Bc,Bc₄,B₂,B₄,B₄'⟩ := bnds
  refine ⟨ℓ₀,B,hℓ₀,B1,?_⟩
  intro ℓ hℓ hℓ'
  obtain ⟨s,χ,χplus,cube,der,vol,regular,tail⟩ := patches ℓ hℓ hℓ'
  let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6*ℓ)
  refine ⟨s,χ,χplus,cube,der,vol,?_,Burnett.C04.tendsto_correctionEnvelope ℓ _ (he.comp hσ.tendsto_atTop),?_⟩
  · intro j hj; obtain ⟨d₀,d₁,_,i,o,w,p,_⟩ := regular j hj; exact ⟨d₀,d₁,i,o,w,p⟩
  filter_upwards [hσ.tendsto_atTop.eventually tail] with n hn
  intro j hj x₀ m
  have hx : x₀ ∈ Kplus := interior_subset ((regular j hj).2.2.2.2.2.1 (mem_closedBall_self (by positivity)))
  have err := he₀ (σ n)
  have hs : 0≤1+e (σ n)/ℓ := by positivity
  obtain ⟨A,z,d,field,extension,symm,mag,slope,orig,src,lp⟩ := hn j hj
  have source : ‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤ B*(volume (W j)^((1:ℝ)/2)).toReal*(1+ℓ⁻¹+(ℓ^2)⁻¹*e (σ n)) :=
    src.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right Bsrc ENNReal.toReal_nonneg) (by positivity))
  have controls : GaugePatchCoefficientBounds B ℓ (e (σ n)) d z (W j) :=
    ⟨fun i k x => (mag i k x).trans (mul_le_mul_of_nonneg_right Bc (by positivity)),
     fun i k x => (slope i k x).trans (mul_le_mul_of_nonneg_right Bc₄ hs),
     ⟨_,(lp p₂).mono le_rfl (mul_le_mul_of_nonneg_right B₂ hs)⟩,
     (lp p₄).mono (mul_le_mul_of_nonneg_right B₄' err) (mul_le_mul_of_nonneg_right B₄ hs)⟩
  refine ⟨A,z,d,orig,field,extension,symm,controls,source,?_⟩
  exact op θ hcut κ hκ hsmall m (metricDensity (g₀ x₀)) (fun ξ => a (x₀,ξ)) (ha x₀ hx) (odd x₀ hx) (hom x₀ hx)
    (gaugeFrozenContraction m) (S x₀) (deg x₀ hx) M hM (jetsM x₀ hx) d A z (W j) B ℓ (e (σ n)) B1 hℓ err Bo Bw symm field
    controls.1 controls.2.1 source controls.2.2.1 controls.2.2.2

end Burnett.V11
