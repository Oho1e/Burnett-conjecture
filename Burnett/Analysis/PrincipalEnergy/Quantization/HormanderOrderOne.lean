import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCoordinateActionBounds

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ContDiff

private def symbolDirection (frequency : Bool) : Space →L[ℝ] Space × Space :=
  if frequency then ContinuousLinearMap.inr ℝ Space Space
  else ContinuousLinearMap.inl ℝ Space Space

/-- The number of frequency derivatives in a list of base or frequency directions. -/
def symbolFrequencyDegree {n : ℕ} (frequency : Fin n → Bool) : ℕ :=
  ∑ i, if frequency i then 1 else 0

/-- Restrict the slots of the full derivative to base or frequency directions. -/
def mixedSymbolJet (a : Space → Space → ℂ) {n : ℕ} (frequency : Fin n → Bool)
    (x ξ : Space) : Space[×n]→L[ℝ] ℂ :=
  (iteratedFDeriv ℝ n (uncurry a) (x, ξ)).compContinuousLinearMap
    (fun i => symbolDirection (frequency i))

/-- The global smooth Hörmander class `S¹₁,₀` in mixed Fréchet seminorms.
Each frequency slot decreases the order by one, and base slots leave it unchanged. -/
structure HormanderOrderOne (a : Space → Space → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ (uncurry a)
  order : ∀ (n : ℕ) (frequency : Fin n → Bool), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖mixedSymbolJet a frequency x ξ‖ * (1 + ‖ξ‖) ^ symbolFrequencyDegree frequency ≤ C * (1 + ‖ξ‖)

private theorem iteratedFDeriv_affineSection {f : Space × Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (c : Space × Space) (L : Space →L[ℝ] Space × Space)
    (n : ℕ) (x : Space) :
    iteratedFDeriv ℝ n (fun y => f (c + L y)) x =
      (iteratedFDeriv ℝ n f (c + L x)).compContinuousLinearMap (fun _ => L) := by
  have hs : ContDiff ℝ ∞ (fun y => f (c + y)) := hf.comp (contDiff_const.add contDiff_id)
  change iteratedFDeriv ℝ n ((fun y => f (c + y)) ∘ L) x = _
  rw [L.iteratedFDeriv_comp_right hs x (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]

private theorem iteratedFDeriv_frequencySection {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (n : ℕ) (x ξ : Space) :
    iteratedFDeriv ℝ n (a x) ξ = mixedSymbolJet a (fun _ : Fin n => true) x ξ := by
  simpa [mixedSymbolJet, symbolDirection, uncurry] using iteratedFDeriv_affineSection ha
    (x, 0) (ContinuousLinearMap.inr ℝ Space Space) n ξ

private theorem iteratedFDeriv_baseSection {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (n : ℕ) (x ξ : Space) :
    iteratedFDeriv ℝ n (fun y => a y ξ) x = mixedSymbolJet a (fun _ : Fin n => false) x ξ := by
  simpa [mixedSymbolJet, symbolDirection, uncurry] using iteratedFDeriv_affineSection ha
    (0, ξ) (ContinuousLinearMap.inl ℝ Space Space) n x

private theorem symbolFrequencyDegree_cons_base {n : ℕ} (frequency : Fin n → Bool) :
    symbolFrequencyDegree (Fin.cons false frequency) = symbolFrequencyDegree frequency := by
  unfold symbolFrequencyDegree
  rw [Fin.sum_univ_succ]
  simp

private theorem symbolFrequencyDegree_snoc_base {n : ℕ} (frequency : Fin n → Bool) :
    symbolFrequencyDegree (Fin.snoc frequency false) = symbolFrequencyDegree frequency := by
  unfold symbolFrequencyDegree
  rw [Fin.sum_univ_castSucc]
  simp

private theorem frequencySection_hasFDerivAt {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (n : ℕ) (x ξ : Space) :
    HasFDerivAt (fun y => iteratedFDeriv ℝ n (a y) ξ)
      (mixedSymbolJet a (Fin.cons false (fun _ : Fin n => true)) x ξ).curryLeft x := by
  let L := ContinuousLinearMap.inl ℝ Space Space
  let R : ((Space × Space)[×n]→L[ℝ] ℂ) →L[ℝ] (Space[×n]→L[ℝ] ℂ) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => ContinuousLinearMap.inr ℝ Space Space)
  have hLine : HasFDerivAt (fun y => (y, ξ)) L x := by
    simpa [L] using L.hasFDerivAt.add_const (0, ξ)
  have hSmooth := ha.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast WithTop.coe_lt_top n)
  have hJet := (hSmooth (x, ξ)).hasFDerivAt.comp x hLine
  have hComp := R.hasFDerivAt.comp x hJet
  have hEq : (fun y => iteratedFDeriv ℝ n (a y) ξ) =
      R ∘ iteratedFDeriv ℝ n (uncurry a) ∘ (fun y => (y, ξ)) := by
    funext y
    exact iteratedFDeriv_frequencySection ha n y ξ
  rw [hEq]
  convert hComp using 1

/-- The ordinary first and mixed frequency symbol estimates follow from `S¹₁,₀`. -/
theorem HormanderOrderOne.firstBaseFrequencyOrderOne {a : Space → Space → ℂ}
    (ha : HormanderOrderOne a) : FirstBaseFrequencyOrderOne a where
  frequency :=
    { smooth := fun x => ha.smooth.comp (contDiff_const.prodMk contDiff_id)
      order := fun n => by
        obtain ⟨C, hC, hBound⟩ := ha.order n (fun _ => true)
        refine ⟨C, hC, fun x ξ => ?_⟩
        rw [iteratedFDeriv_frequencySection ha.smooth]
        simpa [symbolFrequencyDegree] using hBound x ξ }
  baseDiff n ξ x := (frequencySection_hasFDerivAt ha.smooth n x ξ).differentiableAt
  order n := by
    obtain ⟨C, hC, hBound⟩ := ha.order (n + 1) (Fin.cons false (fun _ => true))
    refine ⟨C, hC, fun x ξ => ?_⟩
    rw [(frequencySection_hasFDerivAt ha.smooth n x ξ).fderiv, ContinuousMultilinearMap.curryLeft_norm]
    rw [symbolFrequencyDegree_cons_base] at hBound
    simpa [symbolFrequencyDegree] using hBound x ξ

/-- The pure base derivatives use the undiminished order-one weight. -/
theorem HormanderOrderOne.pureBase {a : Space → Space → ℂ} (ha : HormanderOrderOne a)
    (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖) := by
  obtain ⟨C, hC, hBound⟩ := ha.order n (fun _ => false)
  refine ⟨C, hC, fun x ξ => ?_⟩
  rw [iteratedFDeriv_baseSection ha.smooth]
  simpa [symbolFrequencyDegree] using hBound x ξ

private theorem uncurry_baseDirectionSymbol {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (e : Space) :
    uncurry (baseDirectionSymbol a e) = fun p => fderiv ℝ (uncurry a) p (e, 0) := by
  funext p
  let L := ContinuousLinearMap.inl ℝ Space Space
  have hLine : HasFDerivAt (fun y => (y, p.2)) L p.1 := by
    simpa [L] using L.hasFDerivAt.add_const (0, p.2)
  have hD := ((ha.differentiable (by simp)) p).hasFDerivAt.comp p.1 hLine
  change fderiv ℝ (uncurry a ∘ (fun y => (y, p.2))) p.1 e = _
  rw [hD.fderiv]
  rfl

private theorem mixedSymbolJet_baseDirection_apply {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) {n : ℕ} (frequency : Fin n → Bool)
    (x ξ e : Space) (v : Fin n → Space) :
    mixedSymbolJet (baseDirectionSymbol a e) frequency x ξ v =
      (mixedSymbolJet a (Fin.snoc frequency false) x ξ).curryRight v e := by
  have hSmooth : ContDiff ℝ ∞ (fderiv ℝ (uncurry a)) := ha.fderiv_right (by simp)
  rw [ContinuousMultilinearMap.curryRight_apply]
  unfold mixedSymbolJet
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, uncurry_baseDirectionSymbol ha,
    iteratedFDeriv_clm_apply_const_apply hSmooth (by exact_mod_cast le_top : (n : ℕ∞) ≤ ∞),
    iteratedFDeriv_succ_apply_right]
  simp [Fin.init_def, symbolDirection]

/-- Base differentiation preserves the full smooth order-one class without any
extra symbol assumptions. -/
theorem HormanderOrderOne.baseDirection {a : Space → Space → ℂ}
    (ha : HormanderOrderOne a) (e : Space) : HormanderOrderOne (baseDirectionSymbol a e) where
  smooth := baseDirectionSymbol_joint_smooth ha.smooth e
  order n frequency := by
    obtain ⟨C, hC, hBound⟩ := ha.order (n + 1) (Fin.snoc frequency false)
    refine ⟨C * ‖e‖, mul_nonneg hC (norm_nonneg e), fun x ξ => ?_⟩
    let A := mixedSymbolJet a (Fin.snoc frequency false) x ξ
    have hNorm : ‖mixedSymbolJet (baseDirectionSymbol a e) frequency x ξ‖ ≤ ‖A‖ * ‖e‖ := by
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro v
      rw [mixedSymbolJet_baseDirection_apply ha.smooth]
      exact calc
        ‖A.curryRight v e‖ ≤ ‖A.curryRight v‖ * ‖e‖ := (A.curryRight v).le_opNorm e
        _ ≤ (‖A.curryRight‖ * ∏ i, ‖v i‖) * ‖e‖ :=
          mul_le_mul_of_nonneg_right (A.curryRight.le_opNorm v) (norm_nonneg e)
        _ = (‖A‖ * ‖e‖) * ∏ i, ‖v i‖ := by rw [ContinuousMultilinearMap.curryRight_norm]; ring
    calc
      _ ≤ (‖A‖ * ‖e‖) * (1 + ‖ξ‖) ^ symbolFrequencyDegree frequency :=
        mul_le_mul_of_nonneg_right hNorm (by positivity)
      _ = (‖A‖ * (1 + ‖ξ‖) ^ symbolFrequencyDegree (Fin.snoc frequency false)) * ‖e‖ := by
        rw [symbolFrequencyDegree_snoc_base]; ring
      _ ≤ (C * (1 + ‖ξ‖)) * ‖e‖ := mul_le_mul_of_nonneg_right (hBound x ξ) (norm_nonneg e)
      _ = _ := by ring

/-- An expanding frequency dilation preserves the global order-one symbol class. -/
theorem HormanderOrderOne.frequencyDilation {a : Space → Space → ℂ}
    (ha : HormanderOrderOne a) {s : ℝ} (hs : 1 ≤ s) :
    HormanderOrderOne (fun x ξ => a x (s • ξ)) := by
  let D := (ContinuousLinearMap.fst ℝ Space Space).prod (s • ContinuousLinearMap.snd ℝ Space Space)
  have hD : uncurry (fun (x ξ : Space) => a x (s • ξ)) = uncurry a ∘ D := rfl
  refine ⟨hD ▸ ha.smooth.comp D.contDiff, ?_⟩
  intro n frequency
  obtain ⟨C, hC, hBound⟩ := ha.order n frequency
  have hs₀ : 0 ≤ s := zero_le_one.trans hs
  refine ⟨C * s ^ (n + 1), by positivity, fun x ξ => ?_⟩
  let L (i : Fin n) : Space →L[ℝ] Space :=
    (if frequency i then s else 1) • ContinuousLinearMap.id ℝ Space
  let A := mixedSymbolJet a frequency x (s • ξ)
  have hJet : mixedSymbolJet (fun x ζ => a x (s • ζ)) frequency x ξ = A.compContinuousLinearMap L := by
    unfold mixedSymbolJet A
    rw [hD, D.iteratedFDeriv_comp_right ha.smooth (x, ξ) (by exact_mod_cast le_top)]
    apply ContinuousMultilinearMap.ext
    intro v
    apply congrArg (fun h : Fin n → Space × Space => iteratedFDeriv ℝ n (uncurry a) (x, s • ξ) h)
    funext i
    cases hi : frequency i <;> simp [D, L, symbolDirection, hi]
  have hL : ∏ i, ‖L i‖ ≤ s ^ n := by
    have hEach (i : Fin n) : ‖L i‖ ≤ s := by
      change ‖(if frequency i then s else 1) • ContinuousLinearMap.id ℝ Space‖ ≤ s
      cases hi : frequency i
      · simpa only [hi, Bool.false_eq_true, ↓reduceIte, one_smul] using
          (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Space)).trans hs
      · simp only [↓reduceIte, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs₀]
        exact mul_le_of_le_one_right hs₀ ContinuousLinearMap.norm_id_le
    simpa using Finset.prod_le_prod (s := Finset.univ) (fun i _ => norm_nonneg (L i)) (fun i _ => hEach i)
  have hNorm : ‖mixedSymbolJet (fun x ζ => a x (s • ζ)) frequency x ξ‖ ≤ ‖A‖ * s ^ n := by
    rw [hJet]
    exact (A.norm_compContinuousLinearMap_le L).trans (mul_le_mul_of_nonneg_left hL (norm_nonneg A))
  have hW₁ : 1 + ‖ξ‖ ≤ 1 + ‖s • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs₀]
    nlinarith [norm_nonneg ξ]
  have hW₂ : 1 + ‖s • ξ‖ ≤ s * (1 + ‖ξ‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs₀]
    nlinarith
  calc
    _ ≤ (‖A‖ * s ^ n) * (1 + ‖ξ‖) ^ symbolFrequencyDegree frequency :=
      mul_le_mul_of_nonneg_right hNorm (by positivity)
    _ ≤ (‖A‖ * s ^ n) * (1 + ‖s • ξ‖) ^ symbolFrequencyDegree frequency :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hW₁ _) (by positivity)
    _ = s ^ n * (‖A‖ * (1 + ‖s • ξ‖) ^ symbolFrequencyDegree frequency) := by ring
    _ ≤ s ^ n * (C * (1 + ‖s • ξ‖)) := mul_le_mul_of_nonneg_left (hBound x (s • ξ)) (by positivity)
    _ ≤ s ^ n * (C * (s * (1 + ‖ξ‖))) := by gcongr
    _ = _ := by rw [pow_succ]; ring

end Burnett.Analysis.CarlesonEmbedding
