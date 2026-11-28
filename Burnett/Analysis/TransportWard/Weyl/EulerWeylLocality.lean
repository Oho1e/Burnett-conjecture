import Burnett.Analysis.TransportWard.Weyl.ComplexEulerFormalSymmetry
import Burnett.Analysis.TransportWard.Weyl.ActualEulerWeylCoefficientPacket
import Burnett.Analysis.TransportWard.Weyl.ComplexEulerCoefficientAction

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference
open Burnett.Analysis.TransportWardSymbol
open Burnett.RicciSymbol
open scoped BigOperators Topology ComplexConjugate

local notation "E₀" => CoordinateSpace

private theorem coordinateDensityEuler_eq_of_germ {ι : Type*} [Fintype ι]
    (S : ι → Mat) {f g : E₀ → ι → ℝ} {x : E₀} (h : f =ᶠ[𝓝 x] g) (i : ι) :
    coordinateDensityEuler S f x i = coordinateDensityEuler S g x i := by
  have hF := h.fderiv (𝕜 := ℝ)
  have hJet (s : ActionSlot ι) : coordinateMetricFirstJet f x s = coordinateMetricFirstJet g x s := by
    rw [coordinateMetricFirstJet,coordinateMetricFirstJet,h.fderiv_eq]
  have hFlux (k : Fin 4) (s : ActionSlot ι) :
      (fun y => metricActionCoefficient S (k,i) s (assembleMetricComponents S (f y)) *
          coordinateMetricFirstJet f y s) =ᶠ[𝓝 x]
        (fun y => metricActionCoefficient S (k,i) s (assembleMetricComponents S (g y)) *
          coordinateMetricFirstJet g y s) := by
    filter_upwards [h,hF] with y hy hd
    simp only [hy,coordinateMetricFirstJet,hd]
  have hD (k : Fin 4) (s : ActionSlot ι) := (hFlux k s).fderiv_eq (𝕜 := ℝ)
  simp only [coordinateDensityEuler,h.self_of_nhds,hJet,hD]

private theorem linearizedCoordinateDensityEuler_eq_of_germ {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) {u v : E₀ → ι → ℝ} {x : E₀}
    (h : u =ᶠ[𝓝 x] v) (i : ι) :
    linearizedCoordinateDensityEuler S g u x i = linearizedCoordinateDensityEuler S g v x i := by
  unfold linearizedCoordinateDensityEuler
  apply congrArg (fun f : ℝ → ℝ => deriv f 0)
  funext t
  apply coordinateDensityEuler_eq_of_germ S _ i
  filter_upwards [h] with y hy
  rw [hy]

/-- The true density Euler variation only reads the germ of its input. -/
theorem complexLinearizedCoordinateDensityEuler_eq_of_germ {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) {u v : E₀ → ι → ℂ} {x : E₀}
    (h : u =ᶠ[𝓝 x] v) (i : ι) :
    complexLinearizedCoordinateDensityEuler S g u x i =
      complexLinearizedCoordinateDensityEuler S g v x i := by
  have hr : (fun y j => (u y j).re) =ᶠ[𝓝 x] (fun y j => (v y j).re) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hi : (fun y j => (u y j).im) =ᶠ[𝓝 x] (fun y j => (v y j).im) := by
    filter_upwards [h] with y hy
    rw [hy]
  unfold complexLinearizedCoordinateDensityEuler
  rw [linearizedCoordinateDensityEuler_eq_of_germ S g hr i,
    linearizedCoordinateDensityEuler_eq_of_germ S g hi i]

/-- A cutoff that equals one near the support of the Weyl output can be
removed exactly from the input of the local Euler variation. -/
theorem integral_eulerPair_congr_on_test_support {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) (U K : Set E₀)
    (test : ι → E₀ → ℂ) (hTest : ∀ i x, x ∉ K → test i x = 0)
    (u v : E₀ → ι → ℂ) (h : ∀ x ∈ K, u =ᶠ[𝓝 x] v) :
    (∫ x in U, ∑ i, conj (test i x) * complexLinearizedCoordinateDensityEuler S g u x i) =
      ∫ x in U, ∑ i, conj (test i x) * complexLinearizedCoordinateDensityEuler S g v x i := by
  apply integral_congr_ae
  exact .of_forall fun x => by
    by_cases hx : x ∈ K
    · exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => conj (test i x) * z)
        (complexLinearizedCoordinateDensityEuler_eq_of_germ S g (h x hx) i))
    · simp only [hTest _ x hx,map_zero,zero_mul,Finset.sum_const_zero]

end Burnett.V03.Palatini
