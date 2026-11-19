import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormSphere
import Burnett.Analysis.CubicEnergy.JointMultiplier.SymbolSeminormCutoff

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Metric Set Burnett.RicciSymbol
open scoped ContDiff

/-- For homogeneous joint symbols the reference shell jet is itself bounded
by the ambient derivatives on the eight-dimensional unit sphere, uniformly
over the symbol family. -/
theorem symbol_joint_sphere_moment (j k : ℕ) : ∃ C : ℝ, 0≤C ∧
    ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {z | z ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ z, m (t • z)=m z) → ∀ (D : ℝ), 0≤D →
      (∀ i : ℕ, i≤j+k+9 → ∀ ξ ∈ sphere (0:Freq8) 1,
        ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
      (∫ y : Joint, (1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel (symbolBlock m) y‖) ≤ C*D := by
  obtain ⟨K,hK,mass⟩ := symbol_joint_annular_moment j k
  obtain ⟨L,hL,shell⟩ := symbol_sphere_jet_to_annulus (X := Freq8) 0 (j+k+9) (1/2) 2 (by norm_num) (by norm_num)
  refine ⟨K*L,mul_nonneg hK hL,?_⟩
  intro m hm hh D hd bd
  have h0 : ContDiffOn ℝ ∞ (fun u => m (splitFreq u)) {u | u ≠ 0} :=
    hm.comp splitFreq.contDiff.contDiffOn (fun z hz he => hz (splitFreq.injective (he.trans splitFreq.map_zero.symm)))
  have hom (t : ℝ) (ht : 0<t) (z : Freq8) : m (splitFreq (t • z)) = t^0 * m (splitFreq z) := by
    rw [map_smul,hh t ht,pow_zero,one_mul]
  exact (mass m hm (L*D) (mul_nonneg hL hd) (fun i hi ξ hξ => shell _ h0 hom D hd bd i hi ξ hξ.1 hξ.2)).trans_eq
    (mul_assoc ..).symm

/-- Total degree seven in the two translation weights costs at most sixteen
Cartesian symbol derivatives in the joint reference chart. -/
theorem paper_joint_window_cost (j k : ℕ) (cost : j+k ≤ 7) :
    ∃ C : ℝ, 0≤C ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0<t → ∀ ξ, b (t • ξ)=t*b ξ) →
      ∀ (l : Index) (m : Joint → ℝ), (m = (fun z => lowSymbol b l z.1 z.2) ∨
        m = (fun z => productSymbol l z.1 z.2) ∨ m = (fun z => inputSymbol l z.1 z.2)) →
      ∀ (D : ℝ), 0≤D →
      (∀ i : ℕ, i≤16 → ∀ ξ ∈ sphere (0:Freq8) 1, ‖iteratedFDeriv ℝ i (fun u => m (splitFreq u)) ξ‖ ≤ D) →
      (∫ y : Joint, (1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel (symbolBlock m) y‖) ≤ C*D := by
  obtain ⟨K,hK,est⟩ := symbol_joint_sphere_moment j k
  refine ⟨K,hK,?_⟩
  intro b hb bh l m h D hd bd
  have hand := (commutator_symbol_decomposition b hb bh).1 l
  apply est m _ _ D hd (fun i hi => bd i (by omega))
  · rcases h with rfl|rfl|rfl
    · exact hand.1.1
    · exact hand.2.1.1
    · exact hand.2.2.1.1
  · intro t ht z
    rcases h with rfl|rfl|rfl
    · exact lowSymbol_scale hb bh l t ht z.1 z.2
    · exact (highSymbols_scale l t ht z.1 z.2).1
    · exact (highSymbols_scale l t ht z.1 z.2).2

end Burnett.A02.FrequencySplit
