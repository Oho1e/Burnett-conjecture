import Burnett.Analysis.PrincipalEnergy.Density.FixedChartDensitySymbolProfile

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff Topology

theorem fixedChart_densitySquare_complex_jet_bounds {S : Set Space} (hS : IsCompact S)
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ q) (hqoff : ∀ x ∉ S, q x = 1) :
    ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ n (fun y => (q y : ℂ)^2) x‖ ≤ M := by
  let w (x : Space) := (q x : ℂ)^2
  have hw : ContDiff ℝ ∞ w := (Complex.ofRealCLM.contDiff.comp hq).pow 2
  intro n
  have hcont : Continuous (iteratedFDeriv ℝ n w) :=
    (hw.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).continuous_iteratedFDeriv'
  obtain ⟨C, hC⟩ := (hS.image hcont).isBounded.exists_norm_le
  refine ⟨max C 1, zero_le_one.trans (le_max_right _ _), fun x => ?_⟩
  by_cases hx : x ∈ S
  · exact (hC _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · have he : w =ᶠ[𝓝 x] fun _ : Space => (1:ℂ) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [w, hqoff y hy]
    change ‖iteratedFDeriv ℝ n w x‖ ≤ _
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ he n).eq_of_nhds]
    apply LE.le.trans _ (le_max_right C 1)
    by_cases hn : n = 0
    · subst n
      simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
    · rw [iteratedFDeriv_const_of_ne hn]
      simp

/-- On the fixed chart the exact weighted pairing can also be written using
the same square-root conjugate with a factor of the root on each side. -/
theorem fixedChartDensity_weightedPairing_eq_lebesgueLocalizedAction {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    {K : Set Space} (ρ q : Space → ℝ) (hEq : EqOn (fun x => (q x)^2) ρ K)
    (ψ : SchwartzMap Space ℂ) (hOne : ∀ x ∈ K, ψ x = 1)
    (f : ι → SchwartzMap Space ℂ) (hF : ∀ i, tsupport (f i : Space → ℂ) ⊆ K)
    (v : ι → Space → ℂ) (hV : ∀ i x, x ∉ K → v i x = 0) :
    (∑ i, ∫ x, (ρ x : ℂ) * (conj (matrixFirstOrderAction a f i x) * v i x)) =
      ∑ i, ∫ x, conj (matrixFirstOrderAction
        (fun j k => fixedChartDensityConjugateSymbol (a j k) q ψ) f i x) * v i x := by
  have hIn (i : ι) : scalarSchwartzProduct ψ (f i) = f i := by
    ext x
    rw [scalarSchwartzProduct_apply]
    by_cases hx : f i x = 0
    · simp only [hx, mul_zero]
    · rw [hOne x (hF i (subset_closure hx)), one_mul]
  have hAt (i : ι) (x : Space) :
      matrixFirstOrderAction (fun j k => fixedChartDensityConjugateSymbol (a j k) q ψ) f i x =
        ((q x : ℂ)^2*ψ x)*matrixFirstOrderAction a f i x := by
    unfold matrixFirstOrderAction
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change firstOrderAction (fun y ξ => (q y : ℂ)^2 * cutoffSandwichSymbol (a i j) ψ y ξ) (f j) x = _
    rw [firstOrderAction_leftFactor, firstOrderAction_cutoffSandwichSymbol (ha i j), hIn j, mul_assoc]
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · have hC : (q x : ℂ)^2 = (ρ x : ℂ) := by exact_mod_cast hEq hx
    rw [hAt, hOne x hx, mul_one, hC, map_mul, Complex.conj_ofReal, mul_assoc]
  · simp only [hV i x hx, mul_zero]

end Burnett.Analysis.CarlesonEmbedding
