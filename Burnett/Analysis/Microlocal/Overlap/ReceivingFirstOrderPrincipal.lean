import Burnett.Analysis.Microlocal.Overlap.ReceivingRowLocalization

/-! The exact local H-minus input for a finite first-order row of the original gradient. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open Burnett.Analysis.HminusWeightedDual (negativeEnergy)
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase_of_mem)
open Burnett.F05.CoordinateCurl (localizedGradientTest localizedGradient_tsupport
  localizedGradientTest_test_tendsto_zero exists_outerCutoff_on_tsupport)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz fixedVolumeGradient_weak_and_uniform_L2
  fixedWeightedCutoff fixedComponent fixedComponent_smooth fixedComponent_localUniform)
open Burnett.Microlocal.BesselLocalization (firstOrderRow rowPrincipal rowPrincipal_tendsto_zero_of_negativeEnergy_tendsto_zero
  physicalCoefficient angularDirection angularDirectionSymbol angularDirection_degreeZero)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.RowKernelDensity (groupRow)
open Burnett.X02.SobolevTestJet (D test_smooth test_memLp)
open scoped BigOperators ContDiff InnerProduct Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Strong negative energy of a finite coordinate row gives the actual
strong-zero homogeneous principal action in the receiving chart. -/
theorem fixedVolumeRowPrincipal_tendsto_zero_of_negativeEnergy {J L : Type*} [Fintype J] [Fintype L]
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (a : J → D) (v : J → E) (i : J → JetSlot) (b : L → D) (j : L → JetSlot)
    (hA : Tendsto (fun n => negativeEnergy (firstOrderRow a v i b j
      (fixedVolumeGradientSchwartz B g hB hg hnB c χ hχ n))) atTop (𝓝 0)) :
    Tendsto (fun n => rowPrincipal a v i (fixedVolumeGradientSchwartz B g hB hg hnB c χ hχ n)) atTop (𝓝 0) := by
  let w := fixedWeightedCutoff B hB hnB c χ hχ
  have hw : tsupport (w : E → ℝ) ⊆ c.chart.target := tsupport_mul_subset_left.trans hχ
  let f (n : ℕ) (k : JetSlot) : D := localizedGradientTest c.chart.open_target w hw
    (fixedComponent_smooth B g hB hg c n k.2) k.1
  let u := fixedVolumeGradientSchwartz B g hB hg hnB c χ hχ
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport w
  have hOne (n : ℕ) (k : JetSlot) (x : E) (hx : (f n k : E → ℝ) x ≠ 0) : (θ : E → ℝ) x = 1 :=
    hθ x (localizedGradient_tsupport w (fixedComponent B g c n k.2) k.1 (subset_tsupport _ hx))
  have hEq (n : ℕ) (k : JetSlot) : sourceSchwartz (test_smooth (f n k)) θ (hOne n k) = u n k :=
    SchwartzMap.ext fun _ => rfl
  obtain ⟨C, _, hU, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb c χ hχ
  have hReal (n : ℕ) (k : JetSlot) : ‖(test_memLp (f n k)).toLp (f n k : E → ℝ)‖ ≤ C := by
    have hNorm : ‖(u n k).toLp 2 volume‖ = ‖(test_memLp (f n k)).toLp (f n k : E → ℝ)‖ := by
      rw [← hEq n k]
      simp only [SchwartzMap.toLp, Lp.norm_toLp]
      congr 1
      exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real ((f n k : E → ℝ) x))
    exact hNorm ▸ hU n k
  have hTest (k : JetSlot) (φ : D) : Tendsto (fun n => ∫ x, (f n k : E → ℝ) x * (φ : E → ℝ) x) atTop (𝓝 0) :=
    localizedGradientTest_test_tendsto_zero c.chart.open_target w hw (fun n => fixedComponent B g c n k.2)
      (fun n => fixedComponent_smooth B g hB hg c n k.2)
      (fixedComponent_localUniform r B g hconv c k.2) k.1 φ
  have h := rowPrincipal_tendsto_zero_of_negativeEnergy_tendsto_zero a v i b j
    (fun n k => (f n k : E → ℝ)) (fun n k => test_smooth (f n k)) (fun n k => test_memLp (f n k))
    θ hOne C hReal hTest (by simpa only [hEq, u] using hA)
  simpa only [hEq, u] using h

/-- The real-coordinate principal row at the actual auxiliary unit covector,
with the common imaginary Fourier factor omitted. -/
def receivingFirstOrderSymbol {r : Metric (M := M)} {J : Type} [Fintype J]
    (c : AtlasChart M) (a : J → D) (v : J → E) (i : J → JetSlot) (p : Cosphere r) : JetSlot → ℂ :=
  let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let x := c.chart (projection p)
  groupRow i (fun s => physicalCoefficient (a s) x * (inner ℝ ξ (v s) : ℂ))

def receivingFirstOrderNormalization {r : Metric (M := M)} (c : AtlasChart M) (χ : D)
    (p : Cosphere r) : ℂ :=
  physicalCoefficient χ (c.chart (projection p)) * Complex.I *
    (‖WithLp.toLp 2 (atlasChartUnitCovector c p)‖ : ℂ)⁻¹

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
theorem receivingFirstOrderNormalization_ne_zero {r : Metric (M := M)} (c : AtlasChart M) (χ : D)
    (p : Cosphere r) (hp : projection p ∈ c.chart.source) (hχ : (χ : E → ℝ) (c.chart (projection p)) ≠ 0) :
    receivingFirstOrderNormalization c χ p ≠ 0 := by
  have hξ : WithLp.toLp 2 (atlasChartUnitCovector c p) ≠ 0 := by
    intro hz
    exact atlasChartUnitCovector_ne_zero c p hp (congrArg WithLp.ofLp hz)
  unfold receivingFirstOrderNormalization
  exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hχ) Complex.I_ne_zero)
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)))

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
theorem receivingPrincipalRow_eq_firstOrderSymbol {r : Metric (M := M)} {J : Type} [Fintype J]
    (c : AtlasChart M) (χ : D) (a : J → D) (v : J → E) (i : J → JetSlot)
    (p : Cosphere r) (hp : projection p ∈ c.chart.source) :
    receivingPrincipalRow c χ i (fun s => physicalCoefficient (a s)) (fun s => angularDirectionSymbol (v s)) p =
      receivingFirstOrderNormalization c χ p • receivingFirstOrderSymbol c a v i p := by
  let z := atlasAngularPhaseCode c p
  let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
  have hx : z.1 = c.chart (projection p) := by
    change (FixedCotangentChart.fixedChartPhase c p.val).1 = _
    rw [fixedChartPhase_of_mem c p.val hp]
    rfl
  have hz (s : J) : angularDirectionSymbol (v s) z.2.val = angularDirection (v s) ξ :=
    atlasAngularPhaseCode_symbol_eq_unitCovector c p hp (fun _ y => angularDirection (v s) y)
      (fun _ => angularDirection_degreeZero (v s))
  funext k
  simp only [receivingFirstOrderNormalization, receivingFirstOrderSymbol, receivingPrincipalRow, Pi.smul_apply,
    smul_eq_mul, ← hx, ← show ξ = WithLp.toLp 2 (atlasChartUnitCovector c p) from rfl, groupRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : i s = k
  · have hDir : angularDirectionSymbol (v s) (atlasAngularPhaseCode c p).2.val = angularDirection (v s) ξ := hz s
    simp only [if_pos h, hDir, angularDirection, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, z]
    ring
  · simp only [if_neg h, mul_zero]

end Burnett.Microlocal.Overlap
