import Burnett.Analysis.TransportWard.Weyl.ComplexEulerFormalSymmetry
import Burnett.Analysis.TransportWard.Weyl.ActualEulerWeylCoefficientPacket
import Burnett.Analysis.TransportWard.Weyl.ComplexEulerCoefficientAction

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2500

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter MeasureTheory Set Burnett.Geometry ConnectionDifference
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.RicciSymbol
open scoped ContDiff BigOperators ComplexConjugate

local notation "E₀" => CoordinateSpace
local notation "J" => Fin 4 × Fin 4

private theorem integrable_schwartz_pair (u v : SchwartzMap E₀ ℂ) :
    Integrable (fun x => conj (v x) * u x) volume := by
  let C := SchwartzMap.seminorm ℝ 0 0 u
  have hu (x : E₀) : ‖u x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u 0 x
  refine (v.integrable.norm.mul_const C).mono'
    ((Complex.continuous_conj.comp v.continuous).mul u.continuous).aestronglyMeasurable ?_
  exact .of_forall fun x => by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hu x) (norm_nonneg _)

private theorem integral_on_chart_eq_of_zeroOutside {U : Set E₀} (hU : IsOpen U)
    {f : E₀ → ℂ} (h0 : ∀ x ∉ U, f x = 0) :
    (∫ x in U, f x) = ∫ x, f x := by
  rw [← integral_indicator hU.measurableSet]
  apply integral_congr_ae
  exact .of_forall fun x => by
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,h0 x hx]

/-- On the same compact Schwartz test domain, formal symmetry of the
actual Euler variation and of the Weyl action identifies the tested full
commutator with the paper's positive twice-imaginary pairing. -/
theorem integral_complexEulerWeyl_commutator_eq_two_im {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g : E₀ → ι → ℝ) {U K : Set E₀}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hn : ∀ x ∈ U, Matrix.det (assembleMetricComponents S (g x)) ≠ 0)
    (c₀ : ι → ι → SchwartzMap E₀ ℂ) (c₁ : ι → ActionSlot ι → SchwartzMap E₀ ℂ)
    (c₂ : ι → ι → J → SchwartzMap E₀ ℂ)
    (hAt : ∀ (x : E₀), x ∈ U → ∀ i : ι, ∀ h : E₀ → ι → ℝ, ContDiff ℝ ∞ h →
      (linearizedCoordinateDensityEuler S g h x i : ℂ) =
        ((∑ j, (h x j : ℂ) * c₀ i j x) + ∑ s : ActionSlot ι, (coordinateMetricFirstJet h x s : ℂ) * c₁ i s x) -
          ∑ a, ∑ s : ActionSlot ι, c₂ i s.2 (a,s.1) x * (coordinateMetricSecondJet h x a s : ℂ))
    (B : SchwartzMap E₀ ℂ → SchwartzMap E₀ ℂ)
    (hB : ∀ f v : SchwartzMap E₀ ℂ, (∫ x, conj (v x) * B f x) = ∫ x, conj (B v x) * f x)
    (u : ι → SchwartzMap E₀ ℂ)
    (hSup : ∀ i, tsupport (u i : E₀ → ℂ) ⊆ K)
    (hBSup : ∀ i, tsupport (B (u i) : E₀ → ℂ) ⊆ K) :
    let L := schwartzComplexEulerCoefficientAction c₀ c₁ c₂
    let F := fun i => B (u i)
    (∫ x, ∑ i, conj (u i x) * (Complex.I * (L F i x - B (L u i) x))) =
      ((2 * (∫ x, ∑ i, conj (F i x) * L u i x).im : ℝ) : ℂ) := by
  intro L F
  let u' (x : E₀) (i : ι) := u i x
  let F' (x : E₀) (i : ι) := F i x
  have hUs : ContDiff ℝ ∞ u' := contDiff_pi.mpr fun i => (u i).smooth'
  have hFs : ContDiff ℝ ∞ F' := contDiff_pi.mpr fun i => (F i).smooth'
  have hZeroU (x : E₀) (hx : x ∉ K) (i : ι) : u i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hSup i hs))
  have hZeroF (x : E₀) (hx : x ∉ K) (i : ι) : F i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hBSup i hs))
  have he0 (x : E₀) (hx : x ∈ U \ K) : u' x = 0 := funext (hZeroU x hx.2)
  have hf0 (x : E₀) (hx : x ∈ U \ K) : F' x = 0 := funext (hZeroF x hx.2)
  have hExact (w : ι → SchwartzMap E₀ ℂ) (x : E₀) (hx : x ∈ U) (i : ι) :
      L w i x = complexLinearizedCoordinateDensityEuler S g (fun y j => w j y) x i :=
    schwartzComplexEulerCoefficientAction_eq_complexified S g univ x i c₀ c₁ c₂
      (fun h hh => hAt x hx i h (contDiffOn_univ.mp hh)) w
  let P (x : E₀) := ∑ i, conj (u i x) * L F i x
  let Q (x : E₀) := ∑ i, conj (u i x) * B (L u i) x
  let W (x : E₀) := ∑ i, conj (F i x) * L u i x
  have hP : (∫ x, P x) = conj (∫ x, W x) := by
    have hOffP (x : E₀) (hx : x ∉ U) : P x = 0 := by
      simp only [P,hZeroU x (fun hy => hx (hKU hy)),map_zero,zero_mul,Finset.sum_const_zero]
    have hOffW (x : E₀) (hx : x ∉ U) : W x = 0 := by
      simp only [W,hZeroF x (fun hy => hx (hKU hy)),map_zero,zero_mul,Finset.sum_const_zero]
    rw [← integral_on_chart_eq_of_zeroOutside hU hOffP,← integral_on_chart_eq_of_zeroOutside hU hOffW]
    have hPa : EqOn P (fun x => ∑ i, conj (u' x i) * complexLinearizedCoordinateDensityEuler S g F' x i) U := by
      intro x hx
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => conj (u i x) * z) (hExact F x hx i))
    have hWa : EqOn W (fun x => ∑ i, conj (F' x i) * complexLinearizedCoordinateDensityEuler S g u' x i) U := by
      intro x hx
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => conj (F i x) * z) (hExact u x hx i))
    rw [setIntegral_congr_fun hU.measurableSet hPa,setIntegral_congr_fun hU.measurableSet hWa]
    exact integral_complexLinearizedCoordinateDensityEuler_hermitian S g F' u' hU hK hKU hg
      hFs.contDiffOn hUs.contDiffOn hn hf0 he0
  have hQ : (∫ x, Q x) = ∫ x, W x := by
    unfold Q W
    rw [integral_finset_sum _ (fun i _ => integrable_schwartz_pair (B (L u i)) (u i)),
      integral_finset_sum _ (fun i _ => integrable_schwartz_pair (L u i) (F i))]
    exact Finset.sum_congr rfl fun i _ => hB (L u i) (u i)
  have hPI : Integrable P volume := integrable_finset_sum _ (fun i _ => integrable_schwartz_pair (L F i) (u i))
  have hQI : Integrable Q volume := integrable_finset_sum _ (fun i _ => integrable_schwartz_pair (B (L u i)) (u i))
  have hEq (x : E₀) : (∑ i, conj (u i x) * (Complex.I * (L F i x - B (L u i) x))) =
      Complex.I * (P x - Q x) := by
    simp only [P,Q,Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp only [hEq]
  rw [integral_const_mul,integral_sub hPI hQI,hP,hQ]
  let z : ℂ := ∫ x, W x
  change Complex.I * (conj z - z) = ((2 * z.im : ℝ) : ℂ)
  apply Complex.ext
  · simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.sub_re,Complex.sub_im,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,zero_mul,one_mul]
    ring
  · simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.sub_re,Complex.conj_re,
      Complex.ofReal_im,zero_mul,one_mul,sub_self,add_zero]

end Burnett.V03.Palatini
