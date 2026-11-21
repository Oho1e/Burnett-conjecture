import Burnett.Analysis.CubicEnergy.CompleteEnergy.LowerOrderCompleteCubic
import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormLow

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset Metric Burnett.RicciSymbol
open scoped BigOperators ContDiff ComplexConjugate ENNReal

private abbrev P : ℝ≥0∞ := ENNReal.ofReal 3

private theorem linear_mass_lt_top {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ) :
    (∑ k, ∑ j, ‖c k j‖ₑ) < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ =>
  ENNReal.sum_lt_top.mpr fun _ _ => enorm_lt_top

/-- The additive fixed real profile has an actual complete lower-order
cubic map with the manuscript's physical energy as its diagonal. -/
theorem fixed_profile_complete_cubic_W13_bound (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (q : Index → Index → J → J → J → ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∃ T : MultilinearMap ℝ (fun _ : Fin 3 => RealEnergyField J) ℝ,
      (∀ u : RealEnergyField J, T (fun _ => u) = completeCubicEnergy c q (fixedRadianProfile a) u) ∧
      (∀ v : Fin 3 → RealEnergyField J, ‖T v‖ₑ ≤
        C * ∏ i, fieldInhomogeneousNorm (v i : J → SchwartzMap E ℂ)) := by
  obtain ⟨K,hK,est⟩ := fixedRadianProfile_Lp a areal 3 (by norm_num)
  let m := fixedRadianProfile a
  have hs := fixed_profile_spectrum_integrable a areal
  let C := 2*K*(∑ k, ∑ j, ‖c k j‖ₑ) + 2*semilinearCoefficientMass q*K
  have hf : C < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hK) (linear_mass_lt_top c),
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (semilinearCoefficientMass_finite q)) hK⟩
  exact ⟨C,hf,lowerOrderCompleteCubicMap c q m hs K est,
    lower_order_complete_cubic_map_diag c q m hs K est,
    lower_order_complete_cubic_map_W13_bound c q m hs K est⟩

/-- The actual fixed cutoff multiplied by the degree-one symbol admits a
complete lower-order cubic map and a uniform linear jet coefficient. -/
theorem fixed_cut_complete_cubic_W13_sphere_bound (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) {J : Type} [Fintype J]
    (c : EnergyIndex J → J → ℝ) (q : Index → Index → J → J → J → ℝ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 6 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∃ T : MultilinearMap ℝ (fun _ : Fin 3 => RealEnergyField J) ℝ,
        (∀ u : RealEnergyField J, T (fun _ => u) =
          completeCubicEnergy c q (fun ζ => fixedRadianProfile a ζ * b ζ) u) ∧
        (∀ v : Fin 3 → RealEnergyField J, ‖T v‖ₑ ≤
          C * ENNReal.ofReal D * ∏ i, fieldInhomogeneousNorm (v i : J → SchwartzMap E ℂ)) := by
  obtain ⟨K,hK,est⟩ := fixed_infrared_sphere_bound a areal 3 (by norm_num)
  let C := 2*K*(∑ k, ∑ j, ‖c k j‖ₑ) + 2*semilinearCoefficientMass q*K
  have hf : C < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hK) (linear_mass_lt_top c),
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (semilinearCoefficientMass_finite q)) hK⟩
  refine ⟨C,hf,?_⟩
  intro b hb hom D hD jet
  let m := fun ζ => fixedRadianProfile a ζ * b ζ
  have hs := fixed_cut_spectrum_integrable a areal b hb hom
  have hm := est b hb hom D hD jet
  refine ⟨lowerOrderCompleteCubicMap c q m hs (K*ENNReal.ofReal D) hm,
    lower_order_complete_cubic_map_diag c q m hs _ hm,?_⟩
  intro v
  exact (lower_order_complete_cubic_map_W13_bound c q m hs _ hm v).trans_eq (by unfold C; ring)

private def finiteHermitianTests {I : Type} [Fintype I] (m : E → ℝ)
    (F G : I → SchwartzMap E ℂ) : ℂ :=
  ∑ i, ∫ x, F i x * conj (radianAction m (G i) x)

private theorem finite_hermitian_tests_split {I : Type} [Fintype I] (m b l a : E → ℝ)
    (act : ∀ g : SchwartzMap E ℂ, radianAction m g = radianAction b g - radianAction l g + radianAction a g)
    (hB : ∀ g : SchwartzMap E ℂ, MemLp (radianAction b g) P volume)
    (hL : ∀ g : SchwartzMap E ℂ, MemLp (radianAction l g) P volume)
    (hA : ∀ g : SchwartzMap E ℂ, MemLp (radianAction a g) P volume) (F G : I → SchwartzMap E ℂ) :
    finiteHermitianTests m F G = finiteHermitianTests b F G - finiteHermitianTests l F G +
      finiteHermitianTests a F G := by
  have each (i : I) : (∫ x, F i x * conj (radianAction m (G i) x)) =
      (∫ x, F i x * conj (radianAction b (G i) x)) -
      (∫ x, F i x * conj (radianAction l (G i) x)) +
      ∫ x, F i x * conj (radianAction a (G i) x) := by
    have iB := radian_test_integrable_of_L3 b (F i) (G i) (hB _)
    have iL := radian_test_integrable_of_L3 l (F i) (G i) (hL _)
    have iA := radian_test_integrable_of_L3 a (F i) (G i) (hA _)
    have point (x : E) : radianAction m (G i) x =
        radianAction b (G i) x - radianAction l (G i) x + radianAction a (G i) x :=
      congrFun (act (G i)) x
    simp only [point,map_add,map_sub,mul_add,mul_sub]
    have split := integral_add (iB.sub iL) iA
    simp only [Pi.sub_apply] at split
    rw [split,integral_sub iB iL]
  unfold finiteHermitianTests
  simp_rw [each,Finset.sum_add_distrib,Finset.sum_sub_distrib]

private def derivativeSchwartzArray {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ)
    (u v : J → SchwartzMap E ℂ) (k : J) : SchwartzMap E ℂ :=
  ∑ i : (Index × J) × (Index × J), q i.1.1 i.2.1 i.1.2 i.2.2 k •
    energyProduct (energyPartial i.1.1 (u i.1.2)) (energyPartial i.2.1 (v i.2.2))

private theorem derivativeSchwartzArray_apply {J : Type} [Fintype J] (q : Index → Index → J → J → J → ℝ)
    (u v : J → SchwartzMap E ℂ) (k : J) (x : E) :
    derivativeSchwartzArray q u v k x = semilinearDerivativeTerm q u v k x := by
  let ev : SchwartzMap E ℂ →+ ℂ :=
    {toFun := fun s => s x,map_zero' := rfl,map_add' := fun _ _ => rfl}
  change ev (∑ i : (Index × J) × (Index × J), q i.1.1 i.2.1 i.1.2 i.2.2 k •
    energyProduct (energyPartial i.1.1 (u i.1.2)) (energyPartial i.2.1 (v i.2.2))) = _
  rw [map_sum]
  unfold semilinearDerivativeTerm
  apply Finset.sum_congr rfl
  intro i _
  change ((q i.1.1 i.2.1 i.1.2 i.2.2 k : ℝ) : ℂ) *
    (energyPartial i.1.1 (u i.1.2) x * energyPartial i.2.1 (v i.2.2) x) = _
  change _ = (q i.1.1 i.2.1 i.1.2 i.2.2 k : ℂ) *
    energyPartial i.1.1 (u i.1.2) x * energyPartial i.2.1 (v i.2.2) x
  ring

/-- The actual regularized diagonal is the homogeneous diagonal with
the two true lower-order diagonals subtracted and added, respectively. -/
theorem complete_cubic_energy_fixed_infrared_split {J : Type} [Fintype J] (c : EnergyIndex J → J → ℝ)
    (q : Index → Index → J → J → J → ℝ) (cut add : SchwartzMap E ℂ)
    (hcut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ) (hadd : ∀ ξ, ((add ξ).re : ℂ) = add ξ)
    (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (u : RealEnergyField J) :
    completeCubicEnergy c q (fixedInfraredSymbol cut add b) u =
      completeCubicEnergy c q b u -
        completeCubicEnergy c q (fun ζ=>fixedRadianProfile cut ζ * b ζ) u +
        completeCubicEnergy c q (fixedRadianProfile add) u := by
  let m := fixedInfraredSymbol cut add b
  let l := fun ζ => fixedRadianProfile cut ζ * b ζ
  let a := fixedRadianProfile add
  have act := fixedInfraredSymbol_action cut add hcut hadd b hb hom
  obtain ⟨_,_,boundB⟩ := radian_degree_one_gradient_bound 3 (by norm_num) b hb hom
  obtain ⟨D,hD,jet⟩ := compact_sphere_jet 6 b hb
  obtain ⟨_,_,boundL⟩ := fixed_infrared_sphere_bound cut hcut 3 (by norm_num)
  obtain ⟨_,_,boundA⟩ := fixedRadianProfile_Lp add hadd 3 (by norm_num)
  have hB (g : SchwartzMap E ℂ) := (boundB g).1
  have hL (g : SchwartzMap E ℂ) := (boundL b hb hom D hD jet g).1
  have hA (g : SchwartzMap E ℂ) := (boundA g).1
  let U : J → SchwartzMap E ℂ := u
  let H := linearEnergyCoefficient c U
  let F (k : EnergyIndex J) := energyProduct (H k) (energyPartial k.1.1 (energyPartial k.1.2 (U k.2.2)))
  let G (k : EnergyIndex J) := U k.2.1
  let S (k : J) := derivativeSchwartzArray q U U k
  have qu (d : E → ℝ) : quasilinearPairing d H U = finiteHermitianTests d F G := by
    simp only [quasilinearPairing,finiteHermitianTests,F,G,energyProduct_apply]
  have se (d : E → ℝ) : semilinearHermitianPairing q d U U U = finiteHermitianTests d S U := by
    simp only [semilinearHermitianPairing,finiteHermitianTests,S,derivativeSchwartzArray_apply]
  have Q := finite_hermitian_tests_split m b l a act hB hL hA F G
  have S₁ := finite_hermitian_tests_split m b l a act hB hL hA S U
  change 2 * (quasilinearPairing m H U + semilinearHermitianPairing q m U U U).im =
    2 * (quasilinearPairing b H U + semilinearHermitianPairing q b U U U).im -
      2 * (quasilinearPairing l H U + semilinearHermitianPairing q l U U U).im +
        2 * (quasilinearPairing a H U + semilinearHermitianPairing q a U U U).im
  simp only [qu,se,Q,S₁,Complex.add_im,Complex.sub_im]
  ring

end Burnett.A02.FrequencySplit
