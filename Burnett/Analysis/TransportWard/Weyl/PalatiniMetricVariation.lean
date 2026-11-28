import Burnett.Analysis.TransportWard.Weyl.EHCoordinateDensity
import Burnett.Analysis.TransportWard.Amplitude

/-! Actual parameter derivatives of the computed connection and inverse density. -/

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03.Palatini

open Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

local notation "E" => CoordinateSpace

/-- The same affine lower-metric variation in every space and parameter slot. -/
def metricAffineVariation (g h : E → Mat) (t : ℝ) (x : E) : Mat := g x + t • h x

theorem metricAffineVariation_zero (g h : E → Mat) : metricAffineVariation g h 0 = g := by
  funext x
  simp only [metricAffineVariation, zero_smul, add_zero]

theorem coordinateJet_metricAffineVariation (g h : E → Mat) (x : E)
    (hg : DifferentiableComponentsAt g x) (hh : DifferentiableComponentsAt h x) (t : ℝ) :
    coordinateJet (metricAffineVariation g h t) x = coordinateJet g x + t • coordinateJet h x := by
  funext a b c
  have hd := ((hg b c).hasFDerivAt.fun_add ((hh b c).hasFDerivAt.fun_const_smul t)).fderiv
  change fderiv ℝ (fun y => g y b c + t • h y b c) x (EuclideanSpace.single a 1) =
    fderiv ℝ (fun y => g y b c) x (EuclideanSpace.single a 1) +
      t • fderiv ℝ (fun y => h y b c) x (EuclideanSpace.single a 1)
  rw [hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-- The derivative of the actual Christoffel symbols along the metric variation. -/
def coordinateConnectionVariation (g h : E → Mat) (x : E) : Connection :=
  connectionVariation (g x) (h x) (coordinateJet g x) +
    christoffel (inverseMatrix (g x)) (coordinateJet h x)

theorem hasDerivAt_coordinateConnection_metricAffineVariation (g h : E → Mat) (x : E)
    (hg : DifferentiableComponentsAt g x) (hh : DifferentiableComponentsAt h x)
    (hn : Matrix.det (g x) ≠ 0) (a b c : Index) :
    HasDerivAt (fun t => coordinateConnectionFromMetric (metricAffineVariation g h t) x a b c)
      (coordinateConnectionVariation g h x a b c) 0 := by
  have heq (t : ℝ) : coordinateConnectionFromMetric (metricAffineVariation g h t) x a b c =
      christoffel (inverseMatrix (g x + t • h x)) (coordinateJet g x) a b c +
        t * christoffel (inverseMatrix (g x + t • h x)) (coordinateJet h x) a b c := by
    simp only [coordinateConnectionFromMetric, coordinateJet_metricAffineVariation g h x hg hh t,
      christoffel_add_jet, christoffel_smul_jet, metricAffineVariation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hg0 := hasDerivAt_christoffel_inverse_path (g x) (h x) hn (coordinateJet g x) a b c
  have hh0 := hasDerivAt_christoffel_inverse_path (g x) (h x) hn (coordinateJet h x) a b c
  simpa only [heq, coordinateConnectionVariation, Pi.add_apply, id_eq, zero_smul, add_zero,
    zero_mul, one_mul, zero_add] using hg0.add ((hasDerivAt_id (0 : ℝ)).mul hh0)

theorem coordinateConnectionVariation_symmetric (g h : E → Mat) (x : E)
    (hg : ∀ a, IsSymmetricTensor (coordinateJet g x a))
    (hh : ∀ a, IsSymmetricTensor (coordinateJet h x a)) (a b c : Index) :
    coordinateConnectionVariation g h x a b c = coordinateConnectionVariation g h x a c b := by
  simp only [coordinateConnectionVariation, connectionVariation, Pi.add_apply,
    christoffel_torsion_free (inverseVariation (g x) (h x)) (coordinateJet g x) hg a b c,
    christoffel_torsion_free (inverseMatrix (g x)) (coordinateJet h x) hh a b c]

/-- Variation of the actual densitized inverse metric. -/
def inverseMetricDensityVariation (g h : E → Mat) (x : E) : Mat :=
  fun b c => (metricDensity (g x) / 2 * traceVariation (g x) (h x)) * inverseMatrix (g x) b c +
    metricDensity (g x) * inverseVariation (g x) (h x) b c

theorem hasDerivAt_inverseMetricDensity_metricAffineVariation (g h : E → Mat) (x : E)
    (hn : Matrix.det (g x) ≠ 0) (b c : Index) :
    HasDerivAt (fun t => inverseMetricDensity (metricAffineVariation g h t) x b c)
      (inverseMetricDensityVariation g h x b c) 0 := by
  have hw := hasDerivAt_metricDensity_path (g x) (h x) hn
  have hB := hasDerivAt_inverseMatrix_entry_path (g x) (h x) hn b c
  simpa only [inverseMetricDensityVariation, inverseMetricDensity, metricAffineVariation,
    zero_smul, add_zero] using hw.mul hB

private theorem traceVariation_eq_metricTrace (G H : Mat) (hG : IsSymmetricTensor G) :
    traceVariation G H = metricTrace (inverseMatrix G) H := by
  have hB := inverseMatrix_symmetric G hG
  simp only [traceVariation, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, metricTrace]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hB b a, mul_comm]

private theorem metricTrace_inverseVariation (G H R : Mat) (hG : IsSymmetricTensor G) :
    metricTrace (inverseVariation G H) R = -tensorPairing (inverseMatrix G) R H := by
  have hB := inverseMatrix_symmetric G hG
  simp only [metricTrace, inverseVariation_apply, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_mul, tensorPairing]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hB j b]
  ring

/-- The coefficient part of varying the negative curvature density is
exactly the weighted trace-reversed Ricci pairing with the lower variation. -/
theorem neg_metricTrace_inverseMetricDensityVariation_eq_physicalPairing
    (g h : E → Mat) (x : E) (hG : IsSymmetricTensor (g x)) (R : Mat) :
    -metricTrace (inverseMetricDensityVariation g h x) R =
      metricDensity (g x) * physicalPairing (inverseMatrix (g x)) R (h x) := by
  let w := metricDensity (g x)
  let t := traceVariation (g x) (h x)
  let B := inverseMatrix (g x)
  let dB := inverseVariation (g x) (h x)
  have hpart : metricTrace (inverseMetricDensityVariation g h x) R =
      (w / 2 * t) * metricTrace B R + w * metricTrace dB R := by
    simp only [w, t, B, dB, inverseMetricDensityVariation, metricTrace, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hpart]
  change -((w / 2 * t) * metricTrace B R + w * metricTrace (inverseVariation (g x) (h x)) R) = _
  rw [metricTrace_inverseVariation (g x) (h x) R hG, physicalPairing]
  change -((w / 2 * traceVariation (g x) (h x)) * metricTrace B R +
    w * (-tensorPairing B R (h x))) =
      w * (tensorPairing B R (h x) - metricTrace B R * metricTrace B (h x) / 2)
  rw [traceVariation_eq_metricTrace (g x) (h x) hG]
  ring

/-- The signed Einstein–Hilbert density on the actual coordinate metric. -/
def einsteinHilbertDensity (g : E → Mat) (x : E) : ℝ :=
  -(metricDensity (g x) * coordinateScalarCurvature g x)

/-- Product rule for the real scalar-curvature density, upon supplying the
entrywise derivative of the actual Ricci tensor along the same metric path. -/
theorem hasDerivAt_einsteinHilbertDensity_of_RicciVariation (g h : E → Mat) (x : E)
    (hn : Matrix.det (g x) ≠ 0) (Q : Mat)
    (hQ : ∀ b c, HasDerivAt
      (fun t => coordinateRicci (coordinateConnectionFromMetric (metricAffineVariation g h t)) x b c)
      (Q b c) 0) :
    HasDerivAt (fun t => einsteinHilbertDensity (metricAffineVariation g h t) x)
      (-metricTrace (inverseMetricDensityVariation g h x)
        (coordinateRicci (coordinateConnectionFromMetric g) x) -
      metricTrace (inverseMetricDensity g x) Q) 0 := by
  have hFn : (fun t => einsteinHilbertDensity (metricAffineVariation g h t) x) =
      (fun t => -(∑ b, ∑ c, inverseMetricDensity (metricAffineVariation g h t) x b c *
        coordinateRicci (coordinateConnectionFromMetric (metricAffineVariation g h t)) x b c)) := by
    funext t
    simp only [einsteinHilbertDensity, coordinateScalarCurvature, inverseMetricDensity, metricTrace,
      Finset.mul_sum, mul_assoc]
  have h := (HasDerivAt.fun_sum fun b (_ : b ∈ Finset.univ) =>
    HasDerivAt.fun_sum fun c (_ : c ∈ Finset.univ) =>
      (hasDerivAt_inverseMetricDensity_metricAffineVariation g h x hn b c).mul (hQ b c)).neg
  rw [hFn]
  refine h.congr_deriv ?_
  simp only [metricAffineVariation_zero, metricTrace, Finset.sum_add_distrib]
  ring

end Burnett.V03.Palatini
