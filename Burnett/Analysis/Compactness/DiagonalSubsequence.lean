import Burnett.Analysis.Compactness.CountableTests

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Set Filter Topology

/-- Countably many sequential extraction problems can be solved on one
diagonal. Each tail is a strict subsequence of the actual witness sequence
chosen at the corresponding stage. -/
theorem exists_diagonal_with_subsequence_tails (P : ℕ → (ℕ → ℕ) → Prop)
    (hStep : ∀ (k : ℕ) (f : ℕ → ℕ), StrictMono f →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P k (f ∘ ψ)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ k, ∃ τ ρ : ℕ → ℕ, StrictMono τ ∧ StrictMono ρ ∧
        P k τ ∧ ∀ n, σ (n + k) = τ (ρ n) := by
  classical
  let S := { f : ℕ → ℕ // StrictMono f }
  have hNext (k : ℕ) (f : S) : ∃ ψ, StrictMono ψ ∧ P k (f.val ∘ ψ) := hStep k f.val f.property
  choose next hNextMono hNextP using hNext
  let stages : ℕ → S := Nat.rec ⟨id, strictMono_id⟩
    (fun k f => ⟨f.val ∘ next k f, f.property.comp (hNextMono k f)⟩)
  have hStage (k : ℕ) : (stages (k + 1)).val = (stages k).val ∘ next k (stages k) := rfl
  have hNested (k : ℕ) : Set.range (stages (k + 1)).val ⊆ Set.range (stages k).val := by
    rw [hStage]
    exact Set.range_comp_subset_range _ _
  have hRange (k l : ℕ) : Set.range (stages (k + l)).val ⊆ Set.range (stages k).val := by
    induction l with
    | zero => simp
    | succ l ih => exact (hNested (k + l)).trans ih
  let σ (n : ℕ) := (stages (n + 1)).val n
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change (stages (n + 1)).val n < (stages (n + 1 + 1)).val (n + 1)
    rw [hStage (n + 1), Function.comp_apply]
    exact (stages (n + 1)).property
      (lt_of_lt_of_le (Nat.lt_succ_self n) ((hNextMono (n + 1) (stages (n + 1))).id_le (n + 1)))
  refine ⟨σ, hσ, fun k => ?_⟩
  have hTail (n : ℕ) : ∃ j, (stages (k + 1)).val j = σ (n + k) := by
    have hIncl := hRange (k + 1) n
    have hIndex : k + 1 + n = n + k + 1 := by omega
    rw [hIndex] at hIncl
    exact hIncl ⟨n + k, rfl⟩
  choose ρ hρ using hTail
  have hρMono : StrictMono ρ := by
    intro i j hij
    apply lt_of_not_ge
    intro hle
    have hl := (stages (k + 1)).property.monotone hle
    rw [hρ, hρ] at hl
    exact (not_le_of_gt (hσ (Nat.add_lt_add_right hij k))) hl
  refine ⟨(stages (k + 1)).val, ρ, (stages (k + 1)).property, hρMono, ?_, fun n => (hρ n).symm⟩
  rw [hStage]
  exact hNextP k (stages k)

/-- A countable index type needs no supplied enumeration or choice of a
preferred input. The stage index is the offset used for its actual tail. -/
theorem exists_diagonal_with_countable_tails {ι : Type*} [Countable ι]
    (P : ι → (ℕ → ℕ) → Prop)
    (hStep : ∀ (i : ι) (f : ℕ → ℕ), StrictMono f →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P i (f ∘ ψ)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∃ (k : ℕ) (τ ρ : ℕ → ℕ), StrictMono τ ∧ StrictMono ρ ∧
        P i τ ∧ ∀ n, σ (n + k) = τ (ρ n) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI : IsEmpty ι := h
    exact ⟨id, strictMono_id, isEmptyElim⟩
  | inr h =>
    letI : Encodable ι := Encodable.ofCountable ι
    let e (k : ℕ) : ι := (Encodable.decode k : Option ι).getD (Classical.choice h)
    obtain ⟨σ, hσ, hChoices⟩ :=
      exists_diagonal_with_subsequence_tails (fun k => P (e k)) (fun k => hStep (e k))
    refine ⟨σ, hσ, fun i => ?_⟩
    have he : e (Encodable.encode i) = i := by
      simp only [e, Encodable.encodek, Option.getD_some]
    obtain ⟨τ, ρ, hτ, hρ, hP, hTail⟩ := hChoices (Encodable.encode i)
    exact ⟨Encodable.encode i, τ, ρ, hτ, hρ, he ▸ hP, hTail⟩

/-- Passing from a local chosen subsequence to a strict subsequence tail of it
keeps its existing limit, including for a target in an arbitrary filter. -/
theorem tendsto_of_strictSubsequence_tail {X : Type*} (a : ℕ → X) (l : Filter X)
    (σ τ ρ : ℕ → ℕ) (k : ℕ) (hρ : StrictMono ρ)
    (hTail : ∀ n, σ (n + k) = τ (ρ n))
    (hLimit : Tendsto (fun n => a (τ n)) atTop l) :
    Tendsto (fun n => a (σ n)) atTop l := by
  apply (tendsto_add_atTop_iff_nat k).mp
  exact (hLimit.comp hρ.tendsto_atTop).congr (fun n => by
    change a (τ (ρ n)) = a (σ (n + k))
    rw [hTail])

end Burnett.Microlocal.CountableAuxiliaryCharts
