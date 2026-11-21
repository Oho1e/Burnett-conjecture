import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutatorSlots
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualInputPairing
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Finset Burnett.Fourier Burnett.RicciSymbol
open scoped ContDiff FourierTransform

def paperLowSymbol (b : E → ℝ) (j : Index) (p : Joint) : ℝ :=
  lowSymbol b j p.1 p.2

def paperProductSymbol (j : Index) (p : Joint) : ℝ :=
  productSymbol j p.1 p.2

def paperInputSymbol (j : Index) (p : Joint) : ℝ :=
  inputSymbol j p.1 p.2

def paperAngularProduct (b : E → ℝ) (j : Index) (p : Joint) : ℝ :=
  angularComponent b j (p.1+p.2) * paperProductSymbol j p

theorem paperLowSymbol_regular (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (j : Index) :
    ContDiffOn ℝ ∞ (paperLowSymbol b j) {p | p ≠ 0} ∧
      ∀ t : ℝ, 0 < t → ∀ p, paperLowSymbol b j (t • p) = paperLowSymbol b j p :=
  ⟨lowSymbol_contDiffOn b hb j, fun t ht p => lowSymbol_scale hb hom j t ht p.1 p.2⟩

theorem paperProductSymbol_regular (j : Index) :
    ContDiffOn ℝ ∞ (paperProductSymbol j) {p | p ≠ 0} ∧
      ∀ t : ℝ, 0 < t → ∀ p, paperProductSymbol j (t • p) = paperProductSymbol j p :=
  ⟨productSymbol_contDiffOn j, fun t ht p => (highSymbols_scale j t ht p.1 p.2).1⟩

theorem paperInputSymbol_regular (j : Index) :
    ContDiffOn ℝ ∞ (paperInputSymbol j) {p | p ≠ 0} ∧
      ∀ t : ℝ, 0 < t → ∀ p, paperInputSymbol j (t • p) = paperInputSymbol j p :=
  ⟨inputSymbol_contDiffOn j, fun t ht p => (highSymbols_scale j t ht p.1 p.2).2⟩

private theorem paperAngularProduct_bounded (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (j : Index) :
    Measurable (paperAngularProduct b j) ∧ ∃ D : ℝ, ∀ p, ‖paperAngularProduct b j p‖ ≤ D := by
  have aSmooth := angularComponent_contDiffOn b hb j
  have aMeas : Measurable (angularComponent b j) :=
    measurable_of_continuousOn_compl_singleton 0 aSmooth.continuousOn
  obtain ⟨M, hM⟩ := mikhlin_bounded_symbol _ aSmooth (angularComponent_scale hom j)
  obtain ⟨pMeas, D, pBound⟩ := homogeneous_joint_symbol_measurable_bounded _
    (paperProductSymbol_regular j).1 (paperProductSymbol_regular j).2
  refine ⟨(aMeas.comp (measurable_fst.add measurable_snd)).mul pMeas, M.bound * D, ?_⟩
  intro p
  have c : ‖angularComponent b j (p.1+p.2)‖ ≤ M.bound := by
    simpa only [hM, Complex.norm_real] using M.norm_le (p.1+p.2)
  unfold paperAngularProduct
  rw [norm_mul]
  exact mul_le_mul c (pBound p) (norm_nonneg _) M.bound_nonneg

/-- The actual physical commutator has the sum of the three bilinear operator
pairings against each Schwartz test. The product slot carries its angular
multiplier on the sum frequency, while the last slot acts on the input spectrum. -/
theorem radian_commutator_three_pairings (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f g h : SchwartzMap E ℂ) :
    (∫ x, radianCommutator b f g x * h x) =
      (∑ j, ∫ x, jointBilinear (paperLowSymbol b j) (mikhlinDerivative j f) g x * h x) +
      (∑ j, ∫ x, jointSpectralBilinear (paperAngularProduct b j) (radianActionSpectrum (fun z => ‖z‖) f)
        (𝓕 (g : E → ℂ)) x * h x) -
      ∑ j, ∫ x, jointSpectralBilinear (paperInputSymbol j) (radianActionSpectrum (fun z => ‖z‖) f)
        (radianActionSpectrum (angularComponent b j) g) x * h x := by
  let G := 𝓕 (g : E → ℂ)
  let H := 𝓕 (h : E → ℂ)
  let F := radianActionSpectrum (fun z => ‖z‖) f
  let V (j : Index) := radianActionSpectrum (angularComponent b j) g
  let L (j : Index) := bilinearFourierWeight (paperLowSymbol b j) (mikhlinDerivative j f) g h
  let P (j : Index) (y : Joint) := (paperAngularProduct b j y : ℂ) * F y.1 * G y.2 * H (-(y.1+y.2))
  let N (j : Index) (y : Joint) := (paperInputSymbol j y : ℂ) * F y.1 * V j y.2 * H (-(y.1+y.2))
  have iF : Integrable F := (radianActionSpectrum_radial_data f).2.1
  have iG : Integrable G := (SchwartzMap.fourierTransformCLM ℂ g).integrable
  have iV (j : Index) : Integrable (V j) := (radianActionSpectrum_angular_data b hb hom j g).2.1
  have lowPair (j : Index) :
      Integrable (fun x => jointBilinear (paperLowSymbol b j) (mikhlinDerivative j f) g x * h x) ∧
      Integrable (L j) ∧ (∫ x, jointBilinear (paperLowSymbol b j) (mikhlinDerivative j f) g x * h x) =
        ∫ y, L j y := by
    obtain ⟨hm, _, hD⟩ := homogeneous_joint_symbol_measurable_bounded _ (paperLowSymbol_regular b hb hom j).1
      (paperLowSymbol_regular b hb hom j).2
    exact jointBilinear_schwartz_pairing (paperLowSymbol b j) hm hD (mikhlinDerivative j f) g h
  have prodPair (j : Index) :
      Integrable (fun x => jointSpectralBilinear (paperAngularProduct b j) F G x * h x) ∧
      Integrable (P j) ∧ (∫ x, jointSpectralBilinear (paperAngularProduct b j) F G x * h x) =
        ∫ y, P j y := by
    obtain ⟨hm, _, hD⟩ := paperAngularProduct_bounded b hb hom j
    exact jointSpectralBilinear_pairing (paperAngularProduct b j) hm hD F G iF iG h
  have inPair (j : Index) :
      Integrable (fun x => jointSpectralBilinear (paperInputSymbol j) F (V j) x * h x) ∧
      Integrable (N j) ∧ (∫ x, jointSpectralBilinear (paperInputSymbol j) F (V j) x * h x) =
        ∫ y, N j y := by
    obtain ⟨hm, _, hD⟩ := homogeneous_joint_symbol_measurable_bounded _ (paperInputSymbol_regular j).1
      (paperInputSymbol_regular j).2
    exact jointSpectralBilinear_pairing (paperInputSymbol j) hm hD F (V j) iF (iV j) h
  have iL : ∀ j : Index, Integrable (L j) := fun j => (lowPair j).2.1
  have iP : ∀ j : Index, Integrable (P j) := fun j => (prodPair j).2.1
  have iN : ∀ j : Index, Integrable (N j) := fun j => (inPair j).2.1
  rw [(radian_commutator_pairing b hb hom f g h).2.2, radianWeight_integral]
  calc
    _ = ∫ y : Joint, (∑ j, L j y) + (∑ j, P j y) - ∑ j, N j y := by
      apply integral_congr_ae
      filter_upwards with y
      have diff := radian_commutator_symbol_split b hb hom y.1 y.2
      change bilinearFourierWeight (fun z => b ((tau • z).1+(tau • z).2)-b (tau • z).2) f g h y = _
      simp only [bilinearFourierWeight, Prod.smul_fst, Prod.smul_snd, ← smul_add, diff, Complex.ofReal_sub,
        Complex.ofReal_add, Complex.ofReal_sum, Finset.sum_mul, add_mul, sub_mul]
      have l (j : Index) :
          (↑((tau * y.1 j) * lowSymbol b j y.1 y.2) : ℂ) * 𝓕 (f : E → ℂ) y.1 * G y.2 * H (-(y.1+y.2)) = L j y := by
        simp only [L, bilinearFourierWeight, paperLowSymbol, mikhlinDerivative_fourier, Complex.ofReal_mul]
        ring
      have p (j : Index) :
          (↑(angularComponent b j (y.1+y.2) * productSymbol j y.1 y.2 * ‖tau • y.1‖) : ℂ) *
            𝓕 (f : E → ℂ) y.1 * G y.2 * H (-(y.1+y.2)) = P j y := by
        simp only [P, paperAngularProduct, paperProductSymbol, F, radianActionSpectrum, Complex.ofReal_mul]
        ring
      have n (j : Index) :
          (↑(inputSymbol j y.1 y.2 * ‖tau • y.1‖ * angularComponent b j y.2) : ℂ) *
            𝓕 (f : E → ℂ) y.1 * G y.2 * H (-(y.1+y.2)) = N j y := by
        simp only [N, paperInputSymbol, F, V, radianActionSpectrum, G, angularComponent_scale hom j tau
          (mul_pos (by norm_num) Real.pi_pos), Complex.ofReal_mul]
        ring
      exact congrArg₂ Sub.sub (congrArg₂ HAdd.hAdd
        (Finset.sum_congr rfl (fun j _ => l j)) (Finset.sum_congr rfl (fun j _ => p j)))
        (Finset.sum_congr rfl (fun j _ => n j))
    _ = (∑ j, ∫ y : Joint, L j y) + (∑ j, ∫ y : Joint, P j y) -
        ∑ j, ∫ y : Joint, N j y := by
      have ls := integrable_finset_sum (univ : Finset Index) (fun j _ => iL j)
      have ps := integrable_finset_sum (univ : Finset Index) (fun j _ => iP j)
      have ns := integrable_finset_sum (univ : Finset Index) (fun j _ => iN j)
      have split := integral_sub (ls.add ps) ns
      simp only [Pi.add_apply] at split
      rw [split, integral_add ls ps, integral_finset_sum _ (fun j _ => iL j),
        integral_finset_sum _ (fun j _ => iP j), integral_finset_sum _ (fun j _ => iN j)]
    _ = _ := by
      simp only [← fun j => (lowPair j).2.2, ← fun j => (prodPair j).2.2,
        ← fun j => (inPair j).2.2, L, P, N, V, F, G, H]

end Burnett.A02.FrequencySplit
