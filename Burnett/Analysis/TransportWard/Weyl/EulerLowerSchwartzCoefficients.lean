import Burnett.Analysis.TransportWard.Weyl.EulerLowerCoefficientDecomposition
import Burnett.Analysis.TransportWard.Weyl.LocalSchwartzCoefficients

set_option autoImplicit false
set_option maxHeartbeats 1550000
set_option maxRecDepth 1600

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Filter Burnett.Geometry.ConnectionDifference Burnett.Analysis.TransportWardSymbol
open scoped ContDiff Topology Matrix.Norms.Elementwise

local notation "E₀" => CoordinateSpace

open private contDiffOn_coordinateMetricFirstJet from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

def coordinateEulerBackgroundJet {ι : Type*} [Fintype ι] (S : ι → Mat) (g : E₀ → ι → ℝ)
    (x : E₀) : EulerBackgroundJet ι :=
  (assembleMetricComponents S (g x),coordinateMetricFirstJet g x,coordinateMetricSecondJet g x)

theorem contDiffOn_coordinateEulerBackgroundJet {ι : Type*} [Fintype ι] (S : ι → Mat) (g : E₀ → ι → ℝ)
    {U : Set E₀} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (coordinateEulerBackgroundJet S g) U := by
  have hFirst (s : ActionSlot ι) : ContDiffOn ℝ ∞ (fun y => coordinateMetricFirstJet g y s) U :=
    contDiffOn_coordinateMetricFirstJet hU g hg s
  have hSecond (a : Fin 4) (s : ActionSlot ι) :
      ContDiffOn ℝ ∞ (fun y => coordinateMetricSecondJet g y a s) U :=
    ((hFirst s).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  exact (((assembleMetricComponents S).contDiff).comp_contDiffOn hg).prodMk
    ((contDiffOn_pi.mpr hFirst).prodMk (contDiffOn_pi.mpr fun a => contDiffOn_pi.mpr (hSecond a)))

theorem linearizedCoordinateDensityEuler_eq_explicit_lower_coefficients {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S : ι → Mat) (g h : E₀ → ι → ℝ) {U : Set E₀}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (x : E₀) (hx : x ∈ U) (hDet : (assembleMetricComponents S (g x)).det ≠ 0) (i : ι) :
    let p := coordinateEulerBackgroundJet S g x
    linearizedCoordinateDensityEuler S g h x i =
      ((∑ j, h x j * actualEulerZeroOrderCoefficient S i j p) +
        ∑ s, coordinateMetricFirstJet h x s * actualEulerFirstOrderCoefficient S i s p) -
      ∑ a, ∑ s, metricActionCoefficient S (a,i) s p.1 * coordinateMetricSecondJet h x a s := by
  intro p
  rw [linearizedCoordinateDensityEuler_eq_lower_sub_secondJet S g h hU hg hh x hx hDet i,
    metricEulerJetLowerLinearization_eq_coefficients S _ _ _ _ _ i hDet]
  rfl

/-- All actual lower-order coefficients have a single common plateau on
the Weyl window in the chart. The coefficient extension retains both
zero- and first-order germs on the entire open neighborhood. -/
theorem exists_actualEulerLowerCoefficients_schwartz_near {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) {K U : Set E₀}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hg : ContDiffOn ℝ ∞ g U)
    (hDet : ∀ x ∈ U, (assembleMetricComponents S (g x)).det ≠ 0) :
    ∃ V : Set E₀, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∃ c₀ : ι → ι → SchwartzMap E₀ ℂ, ∃ c₁ : ι → ActionSlot ι → SchwartzMap E₀ ℂ,
        (∀ i j x, x ∈ V → (fun y : E₀ => c₀ i j y) =ᶠ[𝓝 x]
          fun y => (actualEulerZeroOrderCoefficient S i j (coordinateEulerBackgroundJet S g y) : ℂ)) ∧
        (∀ i s x, x ∈ V → (fun y : E₀ => c₁ i s y) =ᶠ[𝓝 x]
          fun y => (actualEulerFirstOrderCoefficient S i s (coordinateEulerBackgroundJet S g y) : ℂ)) := by
  let j := coordinateEulerBackgroundJet S g
  let a₀ (k : ι × ι) (x : E₀) := actualEulerZeroOrderCoefficient S k.1 k.2 (j x)
  let a₁ (k : ι × ActionSlot ι) (x : E₀) := actualEulerFirstOrderCoefficient S k.1 k.2 (j x)
  let A : (ι × ι) ⊕ (ι × ActionSlot ι) → E₀ → ℝ := Sum.elim a₀ a₁
  have hj : ContDiffOn ℝ ∞ j U := contDiffOn_coordinateEulerBackgroundJet S g hU hg
  have hMaps : MapsTo j U (eulerBackgroundJetDomain ι) := fun x hx => hDet x hx
  have hA (k : (ι × ι) ⊕ (ι × ActionSlot ι)) : ContDiffOn ℝ ∞ (A k) U := by
    rcases k with k | k
    · exact (contDiffOn_actualEulerZeroOrderCoefficient S k.1 k.2).comp hj hMaps
    · exact (contDiffOn_actualEulerFirstOrderCoefficient S k.1 k.2).comp hj hMaps
  obtain ⟨V,hV,hKV,hVU,c,hc⟩ := exists_schwartzCoefficients_complex_near A hK hU hKU hA
  exact ⟨V,hV,hKV,hVU,fun i j => c (.inl (i,j)),fun i s => c (.inr (i,s)),
    fun i j x hx => hc (.inl (i,j)) x hx,fun i s x hx => hc (.inr (i,s)) x hx⟩

end Burnett.V03.Palatini
