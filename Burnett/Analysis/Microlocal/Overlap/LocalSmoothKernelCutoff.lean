import Burnett.Analysis.Microlocal.Overlap.LocalClassicalFullSymbol

/-! Localize an ordinary smooth kernel on both actual chart test slots. -/
set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Geometry
open ConnectionDifference
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open scoped ContDiff Topology

local notation "E" => CoordinateSpace

/-- The same cutoff is a plateau on the two compact test slots. Its globally
smooth kernel can replace the local kernel throughout the window. -/
theorem exists_compactSmoothKernel_eq_on_window
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : E → E → ℂ) (hR : ContDiffOn ℝ ∞ (uncurry R) (U ×ˢ U)) :
    ∃ (S : Set E) (k : E → E → ℂ), IsCompact S ∧ ContDiff ℝ ∞ (uncurry k) ∧
      tsupport (uncurry k) ⊆ S ×ˢ S ∧
      ∀ (w : SchwartzMap E ℂ), tsupport (w : E → ℂ) ⊆ K → ∀ x ∈ K,
        (∫ y, k x y * w y) = ∫ y, R x y * w y := by
  obtain ⟨J, _, _, hJU, α, hα, hαc, hαJ, _, hOne⟩ :=
    FlatRigidity.exists_smooth_cutoff_on_compact_chart hK hU hKU
  let χ : D := ⟨α, hα, hαc⟩
  let S := tsupport (χ : E → ℝ)
  let P := leftCutoffClassicalSymbol χ R
  let Q (y x : E) := P x y
  let W := leftCutoffClassicalSymbol χ Q
  let k (x y : E) := W y x
  have hS : IsCompact S := test_compactSupport χ
  have hχ : S ⊆ U := hαJ.trans hJU
  have hSwap : ContDiff ℝ ∞ (Prod.swap : E × E → E × E) := contDiff_snd.prodMk contDiff_fst
  have hP : ContDiffOn ℝ ∞ (uncurry P) (univ ×ˢ U) :=
    leftCutoffClassicalSymbol_smoothOn χ hU hU hχ hR
  have hQ : ContDiffOn ℝ ∞ (uncurry Q) (U ×ˢ univ) :=
    hP.comp hSwap.contDiffOn (fun _ hz => ⟨hz.2, hz.1⟩)
  have hW : ContDiff ℝ ∞ (uncurry W) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using
      leftCutoffClassicalSymbol_smoothOn χ hU isOpen_univ hχ hQ
  have hZero (x : E) (hx : x ∉ S) : physicalCoefficient χ x = 0 := by
    change ((χ : E → ℝ) x : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero]
  refine ⟨S, k, hS, hW.comp hSwap, ?_, ?_⟩
  · apply closure_minimal _ (hS.isClosed.prod hS.isClosed)
    intro z hz
    have hx : z.1 ∈ S := by
      by_contra h
      exact hz (by change physicalCoefficient χ z.2 * (physicalCoefficient χ z.1 * R z.1 z.2) = 0
                   rw [hZero z.1 h, zero_mul, mul_zero])
    have hy : z.2 ∈ S := by
      by_contra h
      exact hz (by change physicalCoefficient χ z.2 * (physicalCoefficient χ z.1 * R z.1 z.2) = 0
                   rw [hZero z.2 h, zero_mul])
    exact ⟨hx, hy⟩
  · intro w hw x hx
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      by_cases hy : y ∈ K
      · change (physicalCoefficient χ y * (physicalCoefficient χ x * R x y)) * w y = _
        simp [physicalCoefficient, χ, hOne x hx, hOne y hy]
      · have h := image_eq_zero_of_notMem_tsupport (f := (w : E → ℂ)) (fun he => hy (hw he))
        change k x y * w y = R x y * w y
        simp only [h, mul_zero]

end Burnett.Microlocal.Overlap
