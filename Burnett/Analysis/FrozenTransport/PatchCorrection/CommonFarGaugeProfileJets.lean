import Burnett.Analysis.FrozenTransport.PatchCorrection.JointFarProfileJets
import Burnett.Analysis.FrozenTransport.PatchCorrection.JointGaugeProfile

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V11

open Set Matrix Burnett.C02 Burnett.V03 Burnett.V08
open Burnett.V10.OriginalGaugeCompatibility
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix metricDensity)
open scoped ContDiff Matrix.Norms.Elementwise
open private smooth_det_on from Burnett.Analysis.TransportPatches.ScreenSmoothSupport

/-- The two actual corrections use the same screen columns and the same open
window around the frozen centers. One jet bound works for both families. -/
theorem exists_commonFarGauge_profile_jets (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (g : E → Mat) (hg : ContDiffOn ℝ ∞ g U) (hn : ∀ x ∈ U, g x ∈ nonsingularMetricDomain)
    (hm : ∀ a b, ContDiffOn ℝ ∞ (fun x => inverseMatrix (g x) a b) U)
    (S : E → GaugeScreen) (hS : ∀ k j, ContDiffOn ℝ ∞ (fun x : Joint => S x.1 x.2 k j)
      (U ×ˢ {v : E | v ≠ 0}))
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) (δ b i o : ℝ)
    (wide : ∀ x ∈ K, WideScreenFrequencySmooth i o (inverseMatrix (g x)))
    {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (same : ∀ x (hx : x ∈ K), S x = (thinScreenAngular (inverseMatrix (g x)) i o (wide x hx) hη inn out).matrix)
    (N : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x (hx : x ∈ K), ∀ k j l,
      GaugeProfileBound N B (gaugeTriadAngularProfile ϑ κ (inverseMatrix (g x)) (metricDensity (g x))
        (fun ξ => a (x, ξ)) (gaugeFrozenContraction (inverseMatrix (g x))) (S x) k l j) ∧
      GaugeProfileBound N B (actualFarAngularProfile (g x) (fun ξ => a (x, ξ)) ϑ κ δ b i o
        (wide x hx) hη inn out k j l) := by
  have hEntry (i j : Fin 4) : ContDiffOn ℝ ∞ (fun x => g x i j) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp hg i) j
  have hDet (x : E) (hx : x ∈ U) : Matrix.det (g x) ≠ 0 := hn x hx
  have hDensity : ContDiffOn ℝ ∞ (fun x => metricDensity (g x)) U :=
    ((smooth_det_on U g hEntry).abs hDet).sqrt (fun x hx => abs_ne_zero.mpr (hDet x hx))
  obtain ⟨BG, hBG, bG⟩ := exists_actualGauge_compact_jets U K hU hK hKU ϑ hϑ κ hκ
    (fun x => inverseMatrix (g x)) hm (fun x => metricDensity (g x)) hDensity a ha S hS N
  obtain ⟨BF, hBF, bF⟩ := exists_jointFarProfile_jets U K hU hK hKU g hg hn hm S hS a ha ϑ hϑ κ hκ δ b N
  refine ⟨BG + BF, add_nonneg hBG hBF, ?_⟩
  intro x hx k j l
  have profile : (fun y => jointFarProfile g S a ϑ κ δ b k j l (x, y)) =
      actualFarAngularProfile (g x) (fun ξ => a (x, ξ)) ϑ κ δ b i o (wide x hx) hη inn out k j l := by
    funext y
    simp only [jointFarProfile, actualFarAngularProfile, same x hx]
    rfl
  obtain ⟨W, hW, sub, smooth, jet⟩ := bG x hx k l j
  have far := bF x hx k j l
  rw [profile] at far
  obtain ⟨V, hV, inc, diff, est⟩ := far
  exact ⟨⟨W, hW, sub, smooth, fun n hn y hy => (jet n hn y hy).trans (le_add_of_nonneg_right hBF)⟩,
    ⟨V, hV, inc, diff, fun n hn y hy => (est n hn y hy).trans (le_add_of_nonneg_left hBG)⟩⟩

end Burnett.V11
