import Burnett.Analysis.Microlocal.RicciJetSymbol
import Burnett.Analysis.Microlocal.CoordinateRicciPrincipalRow
import Burnett.Analysis.Microlocal.RowKernelDensity

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.RicciRow

open Burnett.F05.CoordinateCurl (JetIndex)
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.CurlDensity
open Burnett.Microlocal.RowKernelDensity
open Burnett.Microlocal.BesselLocalization
open Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.X02.SobolevTestJet (D Space)
open scoped BigOperators Matrix

/-- The finite coordinate divergence row has the negative sign of the
Ricci jet convention used in the factorization package. -/
theorem principalTermFrequencySum_eq_neg_ricciJetSymbol
    (G : Tensor2) (ξ : Covector) (u : JetIndex → ℂ) (b d : Index) :
    (∑ s : PrincipalTerm, (termCoefficient G s : ℂ) *
      (ξ (termDirection d s) : ℂ) * u (termInput b d s)) =
      -ricciJetSymbol G ξ u (b,d) := by
  unfold ricciJetSymbol
  simp only [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [jetConnection, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp [Fin.sum_univ_two, Fin.sum_univ_three, termCoefficient, termDirection, termInput]
  ring

/-- The grouped round Bessel row equals the exact matrix row, including the
fixed spatial cutoff and the Fourier sign. The hypothesis evaluates the
actual physical coefficients at the chart point. -/
theorem roundBesselCoefficient_eq_ricciJetMatrix
    (K : BallData) (b d : Index) (a : PrincipalTerm → D) (G : Tensor2) (θ : ℝ)
    (x : Chart K)
    (ha : ∀ s, (a s : Space → ℝ) x.1 = θ * termCoefficient G s) :
    separableRowCoefficients K (termInput b d)
      (fun s => physicalCoefficient (a s))
      (fun s => angularDirectionSymbol (EuclideanSpace.single (termDirection d s) 1)) x =
        fun j => (-Complex.I * (θ : ℂ)) *
          ricciJetMatrix G (fun k => (x.2 : Space) k) (b,d) j := by
  classical
  funext j
  rw [rowPrincipalCoefficients_eq_round]
  let ξ : Covector := fun k => (x.2 : Space) k
  have hInner (s : PrincipalTerm) :
      inner ℝ (x.2 : Space) (EuclideanSpace.single (termDirection d s) 1) =
        ξ (termDirection d s) := by
    simp [EuclideanSpace.inner_single_right, ξ]
  have hBasis := principalTermFrequencySum_eq_neg_ricciJetSymbol G ξ (Pi.single j 1) b d
  rw [← ricciJetMatrix_mulVec] at hBasis
  have hEntry : (ricciJetMatrix G ξ *ᵥ Pi.single j 1) (b,d) =
      ricciJetMatrix G ξ (b,d) j := by
    simp
  rw [hEntry] at hBasis
  have hExpand :
      (∑ s : PrincipalTerm, if termInput b d s = j then
        ((((a s : Space → ℝ) x.1) *
          inner ℝ (x.2 : Space) (EuclideanSpace.single (termDirection d s) 1) : ℝ) : ℂ)
        else 0) =
      (θ : ℂ) * ∑ s : PrincipalTerm, (termCoefficient G s : ℂ) *
        (ξ (termDirection d s) : ℂ) *
          (Pi.single j (1 : ℂ) : JetIndex → ℂ) (termInput b d s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hj : termInput b d s = j
    · rw [if_pos hj, ha s, hInner s, hj]
      simp only [Complex.ofReal_mul, Pi.single_eq_same, mul_one]
      ring
    · rw [if_neg hj, Pi.single_eq_of_ne hj, mul_zero, mul_zero]
  rw [hExpand, hBasis]
  change Complex.I * ((θ : ℂ) * -ricciJetMatrix G ξ (b,d) j) = _
  ring

/-- Evaluation of the very same grouped coefficient row on an arbitrary
ordered complex first jet. -/
theorem roundBesselCoefficient_action_eq_ricciJetSymbol
    (K : BallData) (b d : Index) (a : PrincipalTerm → D) (G : Tensor2) (θ : ℝ)
    (x : Chart K)
    (ha : ∀ s, (a s : Space → ℝ) x.1 = θ * termCoefficient G s)
    (u : JetIndex → ℂ) :
    (∑ j, separableRowCoefficients K (termInput b d)
      (fun s => physicalCoefficient (a s))
      (fun s => angularDirectionSymbol (EuclideanSpace.single (termDirection d s) 1)) x j * u j) =
        (-Complex.I * (θ : ℂ)) * ricciJetSymbol G (fun k => (x.2 : Space) k) u (b,d) := by
  rw [roundBesselCoefficient_eq_ricciJetMatrix K b d a G θ x ha, ← ricciJetMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Where the outer spatial cutoff is equal to one, the physical grouped
row is the Ricci matrix row times the nonzero scalar \(-i\). -/
theorem roundBesselCoefficient_eq_ricciJetMatrix_of_cutoff_eq_one
    (K : BallData) (b d : Index) (a : PrincipalTerm → D) (G : Tensor2) (θ : D)
    (x : Chart K)
    (ha : ∀ s, (a s : Space → ℝ) x.1 = (θ : Space → ℝ) x.1 * termCoefficient G s)
    (hθ : (θ : Space → ℝ) x.1 = 1) :
    separableRowCoefficients K (termInput b d)
      (fun s => physicalCoefficient (a s))
      (fun s => angularDirectionSymbol (EuclideanSpace.single (termDirection d s) 1)) x =
        fun j => -Complex.I * ricciJetMatrix G (fun k => (x.2 : Space) k) (b,d) j := by
  rw [roundBesselCoefficient_eq_ricciJetMatrix K b d a G _ x ha, hθ]
  simp

end Burnett.Microlocal.RicciRow
