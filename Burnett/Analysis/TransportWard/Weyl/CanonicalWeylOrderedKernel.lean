import Burnett.Analysis.TransportWard.Weyl.CanonicalWeylCompression
import Burnett.Analysis.Microlocal.PhysicalDensity

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 1900

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Bundle Burnett.RicciSymbol Burnett.Geometry Burnett.V02
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear UnitNullCompactness
open Burnett.Microlocal.PhysicalDensity (tensorOfVector)
open Burnett.Bianchi.RayIdentification (coordinateHamiltonian canonicalBracket)
open scoped ContDiff Manifold ComplexConjugate BigOperators

local notation "E₀" => CoordinateSpace
local notation "I" => SymmetricMetricSlot
local notation "J" => Fin 4 × Fin 4

/-- Selecting the independent entries with their Euclidean scales and
assembling in the paper basis recovers every ordered entry of a symmetric tensor. -/
theorem assembleComplexMetricComponents_of_ordered (k : J → ℂ)
    (hk : IsSymmetricComplexTensor (tensorOfVector k)) :
    assembleComplexMetricComponents orthonormalMetricDirection
      (fun i : I => (symmetricMetricScale i : ℂ) * k i.val) =
      tensorOfVector k := by
  let u (i : I) := (symmetricMetricScale i : ℂ) * k i.val
  let A := assembleComplexMetricComponents orthonormalMetricDirection u
  have hA := assembleComplexMetricComponents_isSymmetric orthonormalMetricDirection
    orthonormalMetricDirection_isSymmetric u
  have hUpper {a b : Fin 4} (hab : a ≤ b) : A a b = k (a,b) := by
    let i : I := ⟨(a,b),hab⟩
    have hre : (fun j : I => (u j).re) = normalizeMetricComponents (fun j => (k j.val).re) := by
      funext j
      simp only [u,normalizeMetricComponents,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have him : (fun j : I => (u j).im) = normalizeMetricComponents (fun j => (k j.val).im) := by
      funext j
      simp only [u,normalizeMetricComponents,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    apply Complex.ext
    · change assembleMetricComponents orthonormalMetricDirection (fun j => (u j).re) a b = _
      rw [hre]
      exact assemble_orthonormalMetricDirection_at_slot (fun j => (k j.val).re) i
    · change assembleMetricComponents orthonormalMetricDirection (fun j => (u j).im) a b = _
      rw [him]
      exact assemble_orthonormalMetricDirection_at_slot (fun j => (k j.val).im) i
  funext a b
  change A a b = k (a,b)
  rcases le_total a b with hab | hba
  · exact hUpper hab
  · exact (hA a b).trans ((hUpper hba).trans (hk b a))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E₀ M] [IsManifold Model ∞ M]

/-- The already verified Weyl Poisson compression uses the same ordered
kernel vector and quarter physical contraction as the F05 covariance. -/
theorem canonicalBracket_actualDensityWeyl_rankOne_orderedKernel
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : M) (p : CotangentBundle M) (hp : p.proj ∈ (chartAt E₀ c).source)
    (hξ : cotangentCoords c p ≠ 0) (k : J → ℂ)
    (hk : IsSymmetricComplexTensor (tensorOfVector k))
    (hK : ∀ i j, complexRicciSymbol
      (phaseInverse (chartLowerMetric B c) (chartAt E₀ c p.proj,cotangentCoords c p))
      (cotangentCoords c p) (tensorOfVector k) i j = 0)
    (test : E₀ → Covector → ℝ) :
    let G := chartLowerMetric B c
    let z : Phase := (chartAt E₀ c p.proj,cotangentCoords c p)
    let u (i : I) := (symmetricMetricScale i : ℂ) * k i.val
    (∑ i, ∑ j, (canonicalBracket (fun y q => frozenDensityPrincipalPhase orthonormalMetricDirection (G y) q i j)
        test z.1 z.2 : ℂ) * u j * conj (u i)) =
      if dualEnergy B hSig.isNondegenerate p = 0 then
        4 * (phaseDensity G z : ℂ) * (canonicalBracket (coordinateHamiltonian G) test z.1 z.2 : ℂ) *
          ((1 / 4 : ℂ) * hermitianPhysicalPairing (phaseInverse G z) (tensorOfVector k) (tensorOfVector k))
      else 0 := by
  intro G z u
  have he : assembleComplexMetricComponents orthonormalMetricDirection u = tensorOfVector k :=
    assembleComplexMetricComponents_of_ordered k hk
  have hU : ∀ i j, complexRicciSymbol (phaseInverse G z) z.2
      (assembleComplexMetricComponents orthonormalMetricDirection u) i j = 0 := by
    rw [he]
    exact hK
  have h := canonicalBracket_actualDensityWeylMatrix_pairing_RicciKernel B hB hSig c p hp hξ u u hU hU test
  simpa only [he,physicalForm,div_eq_mul_inv,one_mul,mul_comm] using h

end Burnett.V03.Palatini
