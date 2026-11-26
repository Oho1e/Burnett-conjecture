import Burnett.Analysis.TransportPatches.OriginalC03PatchFiniteEndpoints

set_option autoImplicit false

noncomputable section

namespace Burnett.V11

open Set Filter Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.C02 (receivingCutoffFluctuation_eq_originalSourceInput)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- For the original C03 cutoffs, one whole-sequence Schwartz family supplies
the literal V11 input and the canonical C02 receiving field. The raw (L^p)
bounds stay on those very fields, including after the given refinement. -/
theorem exists_receivingPatchFields_of_originalCutoffs
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (s : Finset LatticeIndex) (χ : LatticeIndex → E → ℝ)
    (hχ : ∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ c.chart.target)
    (W : LatticeIndex → Set E) (ℓ : ℝ) (e : ℕ → ℝ) (Cp : {p : ℝ // 1 < p} → ℝ)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    let g₀ := metricComponents (fixedForm B c)
    let G (n : ℕ) := metricComponents (fixedForm (g n) c)
    (∀ j ∈ s, ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
      (∀ i k x, z i k x = ((χ j x * (G n x i k - g₀ x i k) : ℝ) : ℂ)) ∧
      ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j)
        (Cp p * e n) (Cp p * (1 + e n / ℓ))) →
    ∃ Z : ℕ → LatticeIndex → ProjectionSchwartzMatrix,
      (∀ n j, j ∈ s → ∀ i k x, Z n j i k x = ((χ j x * (G n x i k - g₀ x i k) : ℝ) : ℂ)) ∧
      (∀ n j, j ∈ s → ∀ z : ProjectionSchwartzMatrix,
        (∀ i k x, z i k x = ((χ j x * (G n x i k - g₀ x i k) : ℝ) : ℂ)) → Z n j = z) ∧
      (∀ j ∈ s, ∀ (dχ : D) (hχU : tsupport (dχ : E → ℝ) ⊆ c.chart.target),
        (dχ : E → ℝ) = χ j → ∀ n, receivingCutoffFluctuation B g hB hg c dχ hχU n = Z n j) ∧
      (∀ j ∈ s, ∀ᶠ n in atTop, ∀ p : {p : ℝ // 1 < p},
        ProjectedPatchLpBounds p.val (Z n j) (W j) (Cp p * e n) (Cp p * (1 + e n / ℓ))) ∧
      ∀ᶠ n in atTop, ∀ j ∈ s, ∀ p : {p : ℝ // 1 < p},
        ProjectedPatchLpBounds p.val (Z (σ n) j) (W j) (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ)) := by
  classical
  intro g₀ G hRaw
  let d (j : LatticeIndex) (hj : j ∈ s) : D := ⟨χ j, (hχ j hj).1, (hχ j hj).2.1⟩
  have hSupp (j : LatticeIndex) (hj : j ∈ s) : tsupport (d j hj : E → ℝ) ⊆ c.chart.target :=
    (hχ j hj).2.2
  let Z (n : ℕ) (j : LatticeIndex) : ProjectionSchwartzMatrix :=
    if hj : j ∈ s then receivingCutoffFluctuation B g hB hg c (d j hj) (hSupp j hj) n else 0
  have same (n j) (hj : j ∈ s) (i k : Index) (x : E) :
      Z n j i k x = ((χ j x * (G n x i k - g₀ x i k) : ℝ) : ℂ) := by
    have eq : Z n j = receivingCutoffFluctuation B g hB hg c (d j hj) (hSupp j hj) n := dif_pos hj
    exact congrArg (fun f : ProjectionSchwartzMatrix => f i k x) eq
  have unique (n j) (hj : j ∈ s) (z : ProjectionSchwartzMatrix)
      (hz : ∀ i k x, z i k x = ((χ j x * (G n x i k - g₀ x i k) : ℝ) : ℂ)) : Z n j = z := by
    funext i k
    apply SchwartzMap.ext
    intro x
    exact (same n j hj i k x).trans (hz i k x).symm
  have allP (j : LatticeIndex) (hj : j ∈ s) : ∀ᶠ n in atTop, ∀ p : {p : ℝ // 1 < p},
      ProjectedPatchLpBounds p.val (Z n j) (W j) (Cp p * e n) (Cp p * (1 + e n / ℓ)) := by
    filter_upwards [hRaw j hj] with n hn
    obtain ⟨z, hz, hLp⟩ := hn
    rw [unique n j hj z hz]
    exact hLp
  refine ⟨Z, same, unique, ?_, allP, hσ.tendsto_atTop.eventually ((s.eventually_all).2 allP)⟩
  intro j hj dχ hχU hEq n
  apply receivingCutoffFluctuation_eq_originalSourceInput B g hB hg c dχ hχU n (Z n j)
  intro i k x
  rw [same n j hj i k x, hEq]

end Burnett.V11
