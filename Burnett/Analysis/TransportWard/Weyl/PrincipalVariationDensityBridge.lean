import Burnett.Analysis.TransportWard.Weyl.RealEnergyFieldJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.LocalizedPrincipalTest

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.V03.Palatini

open Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ComplexConjugate Matrix.Norms.Elementwise

def eulerPrincipalVariationCoefficient {J : Type*} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (a d : Index) (i j k : J) (x : E) : ℂ :=
  fderiv ℝ (metricActionCoefficient S (a,j) (d,k)) (assembleMetricComponents S (g x)) (S i)

private theorem principalVariation_sum_reindex {J : Type*} [Fintype J]
    (F : ActionSlot J → ActionSlot J → J → ℂ) :
    (∑ a : Index, ∑ d : Index, ∑ i : J, ∑ j : J, ∑ k : J, F (a,j) (d,k) i) =
      ∑ s : ActionSlot J, ∑ t : ActionSlot J, ∑ i : J, F s t i := by
  let π : (Index × Index × J × J × J) ≃ (ActionSlot J × ActionSlot J × J) :=
    { toFun := fun k => ((k.1,k.2.2.2.1),(k.2.1,k.2.2.2.2),k.2.2.1)
      invFun := fun k => (k.1.1,k.2.1.1,k.2.2,k.1.2,k.2.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let φ (k : ActionSlot J × ActionSlot J × J) := F k.1 k.2.1 k.2.2
  simpa only [Fintype.sum_prod_type, π, φ] using
    Fintype.sum_equiv π (fun k => φ (π k)) φ (fun _ => rfl)

/-- The A03 principal variation is the actual leading third action density.
The multiplicity two comes from the two differentiated test placements. -/
theorem principalVariationDensity_eq_actualLeadingThirdVariation {J : Type} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (z w : RealEnergyField J) (x : E) :
    let G := assembleMetricComponents S (g x)
    let h (y : E) (i : J) := (z.val i y).re
    let v (y : E) (i : J) := (w.val i y).re
    let H := assembleMetricComponents S (h x)
    let K := assembleMetricComponents S (v x)
    let p := coordinateMetricFirstJet h x
    let q := coordinateMetricFirstJet v x
    principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x =
      Complex.ofReal (∑ s : ActionSlot J, ∑ t : ActionSlot J, (
        fderiv ℝ (metricActionCoefficient S s t) G K * p s * p t +
          2 * fderiv ℝ (metricActionCoefficient S s t) G H * q s * p t)) := by
  intro G h v H K p q
  let C (s t : ActionSlot J) (i : J) : ℂ := eulerPrincipalVariationCoefficient S g s.1 t.1 i s.2 t.2 x
  let A (s : ActionSlot J) := energyPartial s.1 (z.val s.2) x
  let B (s : ActionSlot J) := energyPartial s.1 (w.val s.2) x
  let u (i : J) := z.val i x
  let k (i : J) := w.val i x
  have hA (s : ActionSlot J) : Complex.ofReal (p s) = A s := (realEnergyField_jets z).1 x s
  have hB (s : ActionSlot J) : Complex.ofReal (q s) = B s := (realEnergyField_jets w).1 x s
  have hCoe (f : RealEnergyField J) (s t : ActionSlot J) :
      Complex.ofReal (fderiv ℝ (metricActionCoefficient S s t) G
          (assembleMetricComponents S (fun i => (f.val i x).re))) =
        ∑ i, C s t i * f.val i x := by
    rw [assembleMetricComponents_apply, map_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, Complex.ofReal_mul, coe_re_eq_of_conj_eq _ (f.property i x)]
    change f.val i x * C s t i = _
    exact mul_comm _ _
  have hSwap (s t : ActionSlot J) (i : J) : C s t i = C t s i := by
    change Complex.ofReal (fderiv ℝ (metricActionCoefficient S s t) G (S i)) =
      Complex.ofReal (fderiv ℝ (metricActionCoefficient S t s) G (S i))
    rw [metricActionCoefficient_swap S s t]
  have hThird : (∑ s, ∑ t, ∑ i, C s t i * (u i * A s * B t)) =
      ∑ s, ∑ t, ∑ i, C s t i * (u i * B s * A t) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    rw [hSwap t s i]
    ring
  have hP : principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x =
      ∑ s, ∑ t, ∑ i, C s t i * (k i * A s * A t + u i * B s * A t + u i * A s * B t) := by
    unfold principalVariationDensity
    exact principalVariation_sum_reindex (fun s t i => C s t i *
      (k i * A s * A t + u i * B s * A t + u i * A s * B t))
  have hFirst (s t : ActionSlot J) : Complex.ofReal (fderiv ℝ (metricActionCoefficient S s t) G K * p s * p t) =
      ∑ i, C s t i * (k i * A s * A t) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hA, hA, hCoe w, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hSecond (s t : ActionSlot J) : Complex.ofReal (fderiv ℝ (metricActionCoefficient S s t) G H * q s * p t) =
      ∑ i, C s t i * (u i * B s * A t) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hB, hA, hCoe z, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hRight (s t : ActionSlot J) : Complex.ofReal (fderiv ℝ (metricActionCoefficient S s t) G K * p s * p t +
      2 * fderiv ℝ (metricActionCoefficient S s t) G H * q s * p t) =
      (∑ i, C s t i * (k i * A s * A t)) + 2 * ∑ i, C s t i * (u i * B s * A t) := by
    have hm : (2 : ℝ) * fderiv ℝ (metricActionCoefficient S s t) G H * q s * p t =
        2 * (fderiv ℝ (metricActionCoefficient S s t) G H * q s * p t) := by ring
    rw [hm, Complex.ofReal_add, hFirst, Complex.ofReal_mul, hSecond]
    norm_num
  rw [hP]
  simp only [Complex.ofReal_sum, hRight]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hThird]
  simp only [← Finset.mul_sum]
  ring

end Burnett.V03.Palatini
