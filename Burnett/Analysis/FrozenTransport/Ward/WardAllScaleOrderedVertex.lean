import Burnett.Analysis.FrozenTransport.FrozenCubicCoefficientV03Bridge
import Burnett.Analysis.TransportWard.ComplexWard
import Burnett.Analysis.FrozenTransport.CompactReceivingCubicCoefficients

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol Burnett.V03
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped Matrix

open private orderedTensorBasis from Burnett.Analysis.FrozenTransport.CompactReceivingCubicCoefficients
open private frozenActionAxisJet_eq_plane from Burnett.Analysis.FrozenTransport.FrozenCubicCoefficientV03Bridge

private abbrev WardActionAxis := ActionSlot OrderedPair
abbrev WardActionEntry := OrderedPair × WardActionAxis × WardActionAxis

private theorem wardMetricBasis_expand (H : Mat) :
    (∑ k : OrderedPair, H k.1 k.2 • frozenActionOrderedBasis k) = H := by
  simpa only [Fintype.sum_prod_type, frozenActionOrderedBasis, orderedTensorBasis, Matrix.smul_single,
    smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single H).symm

private theorem wardPlaneJet_expand (q : Cov) (J : Mat) :
    (∑ k : WardActionAxis, (q k.1 * J k.2.1 k.2.2) • metricAxisJet frozenActionOrderedBasis k) =
      planeJet q J := by
  change metricJetOfComponents frozenActionOrderedBasis (fun k => q k.1 * J k.2.1 k.2.2) = _
  funext d
  rw [metricJetOfComponents_apply]
  change (∑ k : OrderedPair, (q d * J k.1 k.2) • frozenActionOrderedBasis k) = q d • J
  simp only [mul_smul, ← Finset.smul_sum, wardMetricBasis_expand]

/-- The actual ordered coefficient array between the two differentiated
slots and the undifferentiated slot. -/
def wardActionEntryCoefficient (G : Mat) (k : WardActionEntry) : ℝ :=
  frozenActionCubicLinear G ((k.2.1.1,k.2.2.1),(k.2.1.2,k.2.2.2)) k.1

private theorem wardRealPrincipalLeg_eq_ordered (G : Mat) (hG : Matrix.det G ≠ 0)
    (H : Mat) (q r : Cov) (J L : Mat) :
    principalLeg G H (planeJet q J) (planeJet r L) =
      ∑ k : WardActionEntry, wardActionEntryCoefficient G k * H k.1.1 k.1.2 *
        (q k.2.1.1 * J k.2.1.2.1 k.2.1.2.2) * (r k.2.2.1 * L k.2.2.2.1 k.2.2.2.2) := by
  let D (X Y : Jet) : Mat →ₗ[ℝ] ℝ := {
    toFun H' := principalLeg G H' X Y
    map_add' H₁ H₂ := principalLeg_add_metric_direction G H₁ H₂ hG X Y
    map_smul' t H' := principalLeg_smul_metric_direction G H' hG t X Y }
  let X (H' : Mat) (Y : Jet) : Jet →ₗ[ℝ] ℝ := {
    toFun X' := principalLeg G H' X' Y
    map_add' X₁ X₂ := principalLeg_add_left_jet G H' hG X₁ X₂ Y
    map_smul' t X' := principalLeg_smul_left_jet G H' hG X' Y t }
  let Y (H' : Mat) (X' : Jet) : Jet →ₗ[ℝ] ℝ := {
    toFun Y' := principalLeg G H' X' Y'
    map_add' Y₁ Y₂ := principalLeg_add_right_jet G H' hG X' Y₁ Y₂
    map_smul' t Y' := principalLeg_smul_right_jet G H' hG X' Y' t }
  let B := metricAxisJet frozenActionOrderedBasis
  let Q (k : WardActionAxis) := q k.1 * J k.2.1 k.2.2
  let R (k : WardActionAxis) := r k.1 * L k.2.1 k.2.2
  have hD (X' Y' : Jet) :
      principalLeg G H X' Y' = ∑ k : OrderedPair, H k.1 k.2 * principalLeg G (frozenActionOrderedBasis k) X' Y' := by
    change D X' Y' H = ∑ k : OrderedPair, H k.1 k.2 * D X' Y' (frozenActionOrderedBasis k)
    conv_lhs => rw [← wardMetricBasis_expand H]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hX (H' : Mat) (Y' : Jet) :
      principalLeg G H' (planeJet q J) Y' = ∑ k, Q k * principalLeg G H' (B k) Y' := by
    change X H' Y' (planeJet q J) = ∑ k, Q k * X H' Y' (B k)
    rw [← wardPlaneJet_expand q J]
    simp only [map_sum, map_smul, smul_eq_mul, Q, B]
  have hY (H' : Mat) (X' : Jet) :
      principalLeg G H' X' (planeJet r L) = ∑ k, R k * principalLeg G H' X' (B k) := by
    change Y H' X' (planeJet r L) = ∑ k, R k * Y H' X' (B k)
    rw [← wardPlaneJet_expand r L]
    simp only [map_sum, map_smul, smul_eq_mul, R, B]
  have sumEntry (F : WardActionEntry → ℝ) :
      (∑ k, F k) = ∑ l : OrderedPair, ∑ s : WardActionAxis, ∑ t : WardActionAxis, F (l,s,t) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    rw [Fintype.sum_prod_type]
  rw [hD]
  simp_rw [hX, hY, Finset.mul_sum]
  rw [sumEntry]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  have hc : principalLeg G (frozenActionOrderedBasis k) (B s) (B t) =
      wardActionEntryCoefficient G (k,s,t) := by
    change principalLeg G (frozenActionOrderedBasis k) (metricAxisJet frozenActionOrderedBasis (s.1,s.2))
      (metricAxisJet frozenActionOrderedBasis (t.1,t.2)) = _
    simp only [frozenActionAxisJet_eq_plane, wardActionEntryCoefficient, frozenActionCubicLinear,
      frozenActionOrderedBasis]
  rw [hc]
  dsimp only [Q, R]
  ring

/-- The same ordered principal leg in complex Fourier amplitudes. -/
def wardOrderedPrincipalLeg (G : Mat) (H : ComplexTensor2) (q r : Cov) (J L : ComplexTensor2) : ℂ :=
  ∑ k : WardActionEntry, (wardActionEntryCoefficient G k : ℂ) * H k.1.1 k.1.2 *
    ((q k.2.1.1 : ℂ) * J k.2.1.2.1 k.2.1.2.2) * ((r k.2.2.1 : ℂ) * L k.2.2.2.1 k.2.2.2.2)

private theorem wardOrderedPrincipalLeg_complexify (G : Mat) (hG : Matrix.det G ≠ 0)
    (H : ComplexTensor2) (q r : Cov) (J L : ComplexTensor2) :
    let P (H' J' L' : Mat) := principalLeg G H' (planeJet q J') (planeJet r L')
    ((P (realAmplitude H) (realAmplitude J) (realAmplitude L) -
      P (realAmplitude H) (imagAmplitude J) (imagAmplitude L) -
      P (imagAmplitude H) (realAmplitude J) (imagAmplitude L) -
      P (imagAmplitude H) (imagAmplitude J) (realAmplitude L) : ℝ) : ℂ) +
    Complex.I * ((P (imagAmplitude H) (realAmplitude J) (realAmplitude L) +
      P (realAmplitude H) (imagAmplitude J) (realAmplitude L) +
      P (realAmplitude H) (realAmplitude J) (imagAmplitude L) -
      P (imagAmplitude H) (imagAmplitude J) (imagAmplitude L) : ℝ) : ℂ) =
    wardOrderedPrincipalLeg G H q r J L := by
  intro P
  simp only [P, wardRealPrincipalLeg_eq_ordered G hG, wardOrderedPrincipalLeg, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    realAmplitude, imagAmplitude, tensorRe, tensorIm] <;> ring

/-- The genuine complex Ward vertex is the same symmetric signed sum of
the coordinate coefficients already used by the physical cubic energy. -/
theorem wardComplexPrincipalVertex_eq_ordered (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : ComplexTensor2) (q : Cov) (J : ComplexTensor2) (r : Cov) (L : ComplexTensor2) :
    complexPrincipalVertex G p H q J r L =
      -(wardOrderedPrincipalLeg G H q r J L + wardOrderedPrincipalLeg G J p r H L +
        wardOrderedPrincipalLeg G L p q H J) := by
  have h₀ := wardOrderedPrincipalLeg_complexify G hG H q r J L
  have h₁ := wardOrderedPrincipalLeg_complexify G hG J p r H L
  have h₂ := wardOrderedPrincipalLeg_complexify G hG L p q H J
  dsimp only at h₀ h₁ h₂
  simp only [complexPrincipalVertex, principalVertex, Complex.ofReal_neg, Complex.ofReal_sub, Complex.ofReal_add]
  push_cast at h₀ h₁ h₂
  linear_combination -h₀ - h₁ - h₂

end Burnett.C02
