import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFieldUniform
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLocalTest

set_option autoImplicit false
set_option maxRecDepth 9600
set_option maxHeartbeats 16000000

noncomputable section

namespace Burnett.C02

open Set Filter Metric MeasureTheory Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps (Nondegenerate)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.P01 (ProjectionSchwartzMatrix)
open scoped ContDiff Matrix.Norms.Elementwise Topology

/-- The actual signed near summand of the C04 residual satisfies the
individual volume-weighted tail on the original C03 patches. The
same projected fluctuation, test, and thin screen define the sum. -/
theorem exists_wardActualNear_originalPatchRate_localTest (K V U : Set E)
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hU : IsOpen U) (hKU : K ⊆ U)
    (G : E → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ c ∈ V, Matrix.det (G c) ≠ 0)
    (hFrame : ∀ c ∈ K, Nonempty (TensorFrame.LorentzFrame (inverseMatrix (G c))))
    (hGeoND : ∀ c ∈ K, Nondegenerate (inverseMatrix (G c)))
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a (U ×ˢ {ξ : E | ξ ≠ 0}))
    (hOdd : ∀ c ∈ K, ∀ ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ c ∈ K, ∀ t : ℝ, 0 < t → ∀ ξ, a (c,t • ξ) = t*a (c,ξ))
    (wi wo : ℝ) (hm : ∀ c ∈ K, WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (hWide : ∀ c (hc : c ∈ K) ξ k j, W c ξ k j =
      (wideScreenAngular wi wo (inverseMatrix (G c)) (hm c hc)).matrix ξ k j)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ ti thinOut q : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hti : 0 ≤ ti) (hThin : ti < thinOut) (hq : 3 < q) :
    ∃ c₀ δ₀ : ℝ, 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (cScale : ℝ) (hcScale : 0 < cScale), cScale ≤ c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ δ (hδ : δ ∈ Ioc (0 : ℝ) δ₀) (s : Finset LatticeIndex) (ℓ : ℝ) (_ : 0 < ℓ),
      let x₀ := patchCenter ℓ
      let P (j : LatticeIndex) := closedBall (x₀ j) (6*ℓ)
      ∀ (hPatch : ∀ j ∈ s, P j ⊆ K)
        (Z : LatticeIndex → ℕ → ProjectionSchwartzMatrix) (e : ℕ → ℝ)
        (he : Tendsto e atTop (𝓝 0)) (Cp : ℝ), 0 ≤ Cp →
      (∀ j ∈ s, ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (Z j n) (P j) (Cp*e n) (Cp*(1+e n/ℓ))) →
      let hη : 0 < cScale*κ*δ^2 := mul_pos (mul_pos hcScale hκ) (pow_pos hδ.1 _)
      let near (n : ℕ) (j : LatticeIndex) : ℝ := by
        classical
        exact if hc : x₀ j ∈ K then (wardActualNearCubicForm (G (x₀ j)) (fun ξ => a (x₀ j,ξ))
          ϑ κ δ wi wo (hm (x₀ j) hc) hη ti thinOut (Z j n)).re else 0
      (∀ (j : LatticeIndex) (hj : j ∈ s) (n : ℕ),
        let hc := hPatch j hj (mem_closedBall_self (by positivity : 0 ≤ 6*ℓ))
        let H := wardActualThinSpectrum (inverseMatrix (G (x₀ j))) wi wo (hm (x₀ j) hc) hη ti thinOut (Z j n)
        Integrable (fun y => (wardPurePhysicalNearWeight ϑ κ δ y : ℂ) *
          wardCyclicCubicWeight (G (x₀ j)) (fun ξ => a (x₀ j,ξ)) H H H y)) ∧
      ∀ j ∈ s, ∀ᶠ n in atTop, |near n j| ≤
        C*((Fintype.card WardNearSlot : ℝ)*(2*Cp))^3*
          δ^(2*(q-3)/(q-2))*((volume : Measure E) (P j)).toReal := by
  classical
  obtain ⟨b,hb,hbOdd,hbHom,hSame⟩ := exists_wardRealOddChartTest_extension K U hK hU hKU a ha hOdd hHom
  obtain ⟨c₀,δ₀,hc₀,hδ₀,hδ₀₁,hField⟩ := exists_wardActualNearField_uniform K V hK hV hKV
    G hG hND hFrame hGeoND b hb hbOdd hbHom wi wo hm W hW hWide ϑ hϑ hRange hCut hFlat
    κ ti thinOut q hκ hκsmall hti hThin hq
  refine ⟨c₀,δ₀,hc₀,hδ₀,hδ₀₁,?_⟩
  intro cScale hcScale hScale
  obtain ⟨C,hC,hResult⟩ := hField cScale hcScale hScale
  refine ⟨C,hC,?_⟩
  intro δ hδ s ℓ hℓ x₀ P hPatch Z e he Cp hCp hRaw hη near
  have hCenter (j : LatticeIndex) (hj : j ∈ s) : x₀ j ∈ K :=
    hPatch j hj (mem_closedBall_self (by positivity))
  have hEq (j : LatticeIndex) (hj : j ∈ s) :
      (fun ξ => b (x₀ j,ξ)) = fun ξ => a (x₀ j,ξ) :=
    funext (hSame (x₀ j) (hCenter j hj))
  have hActual (j : LatticeIndex) (hj : j ∈ s) (n : ℕ) := by
    have h := hResult (x₀ j) (hCenter j hj) δ hδ (Z j n)
    rw [hEq j hj] at h
    exact h
  refine ⟨fun j hj n => (hActual j hj n).1,?_⟩
  intro j hj
  have hSmall : ∀ᶠ n in atTop, e n ≤ ℓ := ((tendsto_order.1 he).2 ℓ hℓ).mono (fun _ hn => hn.le)
  filter_upwards [hRaw j hj,hSmall] with n hn hs
  have hCutoff : Cp*(1+e n/ℓ) ≤ 2*Cp := by
    have h := mul_le_mul_of_nonneg_left (add_le_add_left ((div_le_one hℓ).mpr hs) 1) hCp
    linarith only [h]
  let N := wardActualNearCubicForm (G (x₀ j)) (fun ξ => a (x₀ j,ξ))
    ϑ κ δ wi wo (hm (x₀ j) (hCenter j hj)) hη ti thinOut (Z j n)
  have hNorm := wardActualNear_patch_rate_of_fieldL3 (Z j n) (P j) N (Cp*e n) (2*Cp)
    C δ (2*(q-3)/(q-2)) hC hδ.1.le (hn.mono le_rfl hCutoff) (hActual j hj n).2
  simpa only [near,dif_pos (hCenter j hj),N] using (Complex.abs_re_le_norm N).trans hNorm

end Burnett.C02
