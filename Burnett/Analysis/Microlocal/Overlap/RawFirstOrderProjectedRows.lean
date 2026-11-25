import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderCompactTests
import Burnett.Analysis.Microlocal.Overlap.RawFirstOrderSymmetricProjection

/-! Compose an actual local first-order row with the canonical symmetric projection. -/
set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped BigOperators

local notation "E" => CoordinateSpace

def projectedRowSlot {J : Type*} (i : J → JetSlot) (h : J × Fin 2) : JetSlot :=
  if h.2 = 0 then i h.1 else jetPairSwap (i h.1)

/-- The two halves of a row are the coordinate expression of its composition
with the true pointwise symmetric projection. The derivative directions
and the original coefficients are retained. -/
theorem receivingRawFirstOrderRow_projected
    {J L : Type*} [Fintype J] [Fintype L]
    (a : J → E → ℝ) (v : J → E) (i : J → JetSlot)
    (b : L → E → ℝ) (j : L → JetSlot) (u : JetSlot → E → ℂ) (x : E)
    (hu : ∀ k, DifferentiableAt ℝ (u k) x) :
    receivingRawFirstOrderRow (fun h y => a h.1 y / 2) (fun h => v h.1) (projectedRowSlot i)
      (fun h y => b h.1 y / 2) (projectedRowSlot j) u x =
    receivingRawFirstOrderRow a v i b j (fun k y => symmetrizeOrderedJet (fun l => u l y) k) x := by
  have hDeriv (k : JetSlot) (direction : E) :
      fderiv ℝ (fun y => symmetrizeOrderedJet (fun l => u l y) k) x direction =
        (2 : ℂ)⁻¹ * (fderiv ℝ (u k) x direction + fderiv ℝ (u (jetPairSwap k)) x direction) := by
    change fderiv ℝ (((2 : ℂ)⁻¹) • (u k + u (jetPairSwap k))) x direction = _
    have h := ((hu k).hasFDerivAt.add (hu (jetPairSwap k)).hasFDerivAt).const_smul ((2 : ℂ)⁻¹)
    rw [h.fderiv]
    rfl
  simp only [receivingRawFirstOrderRow, Fintype.sum_prod_type, Fin.sum_univ_two, hDeriv]
  simp [projectedRowSlot, symmetrizeOrderedJet]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro h _
    ring
  · apply Finset.sum_congr rfl
    intro h _
    ring

end Burnett.Microlocal.Overlap
