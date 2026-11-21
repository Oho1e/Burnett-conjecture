import Burnett.Analysis.CubicEnergy.CompleteEnergy.SymbolSeminormLowSegment
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Metric Set Finset Burnett.RicciSymbol
open scoped ContDiff Topology

theorem compact_derivative_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (N : ℕ) {S U : Set X} (SCompact : IsCompact S) (UOpen : IsOpen U) (sub : S ⊆ U)
    (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ N → ∀ x ∈ S,
      ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  classical
  have existsBound (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S,
      ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    have order : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have smooth : ContinuousOn (iteratedFDeriv ℝ i f) U :=
      (hf.continuousOn_iteratedFDerivWithin order UOpen.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen i UOpen hx).symm)
    obtain ⟨C, bound⟩ := SCompact.bddAbove_image (smooth.norm.mono sub)
    exact ⟨max 0 C, le_max_left _ _, fun x hx => (bound (mem_image_of_mem _ hx)).trans (le_max_right _ _)⟩
  choose C C0 bound using existsBound
  refine ⟨∑ i ∈ range (N+1), C i, sum_nonneg (fun i _ => C0 i), ?_⟩
  intro i hi x hx
  exact (bound i x hx).trans (single_le_sum (fun k _ => C0 k) (Finset.mem_range.mpr (by omega : i < N+1)))

/-- Every prescribed finite ambient jet of a fixed punctured-smooth scalar function
is bounded on the unit sphere. -/
theorem compact_sphere_jet {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [ProperSpace X] (N : ℕ) (f : X → ℝ) (hf : ContDiffOn ℝ ∞ f {x | x ≠ 0}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ N → ∀ x ∈ sphere (0 : X) 1,
      ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  compact_derivative_bound N (isCompact_sphere (0 : X) 1) isClosed_singleton.isOpen_compl
    (fun x hx h0 => by
      have e : x = 0 := h0
      simp [e] at hx) f hf

theorem product_jet_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {V : Set X}
    (VOpen : IsOpen V) {f g : X → ℝ} (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    {x : X} (hx : x ∈ V) {i N : ℕ} (hi : i ≤ N) {A B : ℝ} (A0 : 0 ≤ A) (B0 : 0 ≤ B)
    (massF : ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (massG : ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ i (fun x => f x * g x) x‖ ≤ (2 : ℝ)^N * A * B := by
  have order : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have product := norm_iteratedFDerivWithin_mul_le hf hg VOpen.uniqueDiffOn hx order
  simp only [iteratedFDerivWithin_of_isOpen _ VOpen hx] at product
  refine product.trans ?_
  have choices : (∑ k ∈ range (i+1), (i.choose k : ℝ)) = (2 : ℝ)^i := by
    exact_mod_cast Nat.sum_range_choose i
  calc
    _ ≤ ∑ k ∈ range (i+1), (i.choose k : ℝ) * A * B := by
      apply sum_le_sum
      intro k hk
      have hkN : k ≤ N := by
        have hh := Finset.mem_range.mp hk
        omega
      exact mul_le_mul (mul_le_mul_of_nonneg_left (massF k hkN) (Nat.cast_nonneg _))
        (massG (i-k) (by omega)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) A0)
    _ = (2 : ℝ)^i * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, choices]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hi) A0) B0

/-- Multiplication by the fixed low-frequency cutoff preserves the finite jet
dependence on the original degree-one symbol, also on the zero side of the cutoff. -/
theorem low_symbol_sphere_jet (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ (s : ℝ), 0 < s → ∀ x, b (s • x) = s * b x) → ∀ (D : ℝ), 0 ≤ D →
      (∀ i : ℕ, i ≤ N+1 → ∀ x ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ i b x‖ ≤ D) →
      ∀ (j : Index) (i : ℕ), i ≤ N → ∀ u ∈ sphere (0 : Freq8) 1,
      ‖iteratedFDeriv ℝ i (fun w => lowSymbol b j (splitFreq w).1 (splitFreq w).2) u‖ ≤ K * D := by
  let U : Set Freq8 := {u | u ≠ 0}
  let w := fun u : Freq8 => lowWeight (splitFreq u).1 (splitFreq u).2
  have wSmooth : ContDiffOn ℝ ∞ w U := lowWeight_contDiffOn.comp splitFreq.contDiff.contDiffOn
    (fun u hu he => hu (splitFreq.injective (he.trans splitFreq.map_zero.symm)))
  have safeSub : lowJetSafe ⊆ U := by
    intro u hu hu0
    change u = 0 at hu0
    simp [lowJetSafe, hu0] at hu
  obtain ⟨C, C0, wBound⟩ := compact_sphere_jet N w wSmooth
  obtain ⟨K, K0, averageBound⟩ := low_derivative_average_jet N
  refine ⟨(2:ℝ)^N * C * K, mul_nonneg (mul_nonneg (by positivity) C0) K0, ?_⟩
  intro b hb hom D D0 db j i hi u un
  by_cases uSafe : u ∈ lowJetSafe
  · let A := fun v : Freq8 => derivComponent b j (splitFreq v).1 (splitFreq v).2
    have smA : ContDiffOn ℝ ∞ A lowJetSafe := low_derivative_average_contDiffOn b hb j
    change ‖iteratedFDeriv ℝ i (fun v => w v * A v) u‖ ≤ _
    have bound := product_jet_bound lowJetSafe_open (wSmooth.mono safeSub) smA uSafe hi C0 (mul_nonneg K0 D0)
      (fun k hk => wBound k hk u un) (fun k hk => averageBound b hb hom D D0 db j k hk u un uSafe)
    exact bound.trans_eq (mul_assoc ..).symm
  · let W : Set Freq8 := {v | ‖(splitFreq v).2‖ < 4 * ‖(splitFreq v).1‖}
    have WOpen : IsOpen W := isOpen_lt (continuous_snd.comp splitFreq.continuous).norm
      (continuous_const.mul (continuous_fst.comp splitFreq.continuous).norm)
    have hn : ‖(splitFreq u).2‖ ≤ 2 * ‖(splitFreq u).1‖ := le_of_not_gt uSafe
    have etaPos : 0 < ‖(splitFreq u).1‖ := by
      by_contra! h
      have e₁ : (splitFreq u).1 = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
      rw [e₁, norm_zero, mul_zero] at hn
      have e₂ : (splitFreq u).2 = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
      have e : u = 0 := splitFreq.injective ((Prod.ext e₁ e₂).trans splitFreq.map_zero.symm)
      simp [e] at un
    have uW : u ∈ W := show ‖(splitFreq u).2‖ < 4 * ‖(splitFreq u).1‖ by linarith
    have zeroOn : EqOn (fun v => lowSymbol b j (splitFreq v).1 (splitFreq v).2)
        (fun _ : Freq8 => (0:ℝ)) W := by
      intro v hv
      change ‖(splitFreq v).2‖ < 4 * ‖(splitFreq v).1‖ at hv
      simp [lowSymbol, lowWeight_eq_zero hv.le]
    have same := iteratedFDerivWithin_congr (𝕜 := ℝ) zeroOn uW i
    rw [iteratedFDerivWithin_of_isOpen i WOpen uW, iteratedFDerivWithin_of_isOpen i WOpen uW] at same
    rw [same]
    have zero : iteratedFDeriv ℝ i (fun _ : Freq8 => (0 : ℝ)) u = 0 := by
      cases i with
      | zero =>
        ext z
        simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.zero_apply]
      | succ i => exact congrFun (iteratedFDeriv_succ_const (𝕜 := ℝ) (E := Freq8) i (0 : ℝ)) u
    rw [zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) C0) K0) D0

/-- The factors kept in the separate linear multipliers have the same finite
ambient derivative dependence on the original symbol as multiplication by a fixed factor. -/
theorem angular_component_sphere_jet (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} → ∀ (D : ℝ), 0 ≤ D →
      (∀ i : ℕ, i ≤ N → ∀ x ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ i b x‖ ≤ D) →
      ∀ (j : Index) (i : ℕ), i ≤ N → ∀ x ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ i (angularComponent b j) x‖ ≤ K * D := by
  classical
  let U : Set E := {x | x ≠ 0}
  have UOpen : IsOpen U := isClosed_singleton.isOpen_compl
  let factor (j : Index) := fun x : E => x j / ‖x‖^2
  have sm (j : Index) : ContDiffOn ℝ ∞ (factor j) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffOn.div (contDiff_norm_sq ℝ).contDiffOn
      (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
  choose C C0 mass using fun j => compact_sphere_jet N (factor j) (sm j)
  let A := ∑ j, C j
  have A0 : 0 ≤ A := sum_nonneg (fun j _ => C0 j)
  refine ⟨(2 : ℝ)^N * A, mul_nonneg (by positivity) A0, ?_⟩
  intro b hb D D0 bd j i hi x hx
  have xU : x ∈ U := by intro e; simp [e] at hx
  have eq : angularComponent b j = fun x => factor j x * b x := by
    funext x
    change b x * x j / ‖x‖^2 = x j / ‖x‖^2 * b x
    rw [mul_div_assoc, mul_comm (b x)]
  rw [eq]
  exact product_jet_bound UOpen (sm j) hb xU hi A0 D0 (fun k hk =>
    (mass j k hk x hx).trans (single_le_sum (fun l _ => C0 l) (mem_univ j))) (fun k hk => bd k hk x hx)

/-- The two high-input symbols are fixed independently of the original b. -/
theorem high_symbols_sphere_jet (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Index) (i : ℕ), i ≤ N → ∀ x ∈ sphere (0 : Freq8) 1,
      ‖iteratedFDeriv ℝ i (fun u => productSymbol j (splitFreq u).1 (splitFreq u).2) x‖ ≤ K ∧
      ‖iteratedFDeriv ℝ i (fun u => inputSymbol j (splitFreq u).1 (splitFreq u).2) x‖ ≤ K := by
  classical
  have toNonzero : MapsTo splitFreq {u | u ≠ 0} {p | p ≠ 0} :=
    fun u hu he => hu (splitFreq.injective (he.trans splitFreq.map_zero.symm))
  choose C C0 cMass using fun j => compact_sphere_jet N _ ((productSymbol_contDiffOn j).comp
    splitFreq.contDiff.contDiffOn toNonzero)
  choose D D0 dMass using fun j => compact_sphere_jet N _ ((inputSymbol_contDiffOn j).comp
    splitFreq.contDiff.contDiffOn toNonzero)
  refine ⟨∑ j, (C j + D j), sum_nonneg (fun j _ => add_nonneg (C0 j) (D0 j)), ?_⟩
  intro j i hi x hx
  have term : C j + D j ≤ ∑ l, (C l + D l) :=
    single_le_sum (fun l _ => add_nonneg (C0 l) (D0 l)) (mem_univ j)
  exact ⟨(cMass j i hi x hx).trans ((le_add_of_nonneg_right (D0 j)).trans term),
    (dMass j i hi x hx).trans ((le_add_of_nonneg_left (C0 j)).trans term)⟩

end Burnett.A02.FrequencySplit
