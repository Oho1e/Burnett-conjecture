import Burnett.Analysis.CubicEnergy.AngularHarmonics.JointSphereHarmonicCoefficient
import Burnett.Analysis.CubicEnergy.AngularHarmonics.HarmonicAmbientRotationJets

set_option autoImplicit false
set_option maxHeartbeats 8500000

noncomputable section

namespace Burnett.A06

open Fin Filter Metric MeasureTheory Set
open scoped BigOperators ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem angularSlice_contDiff (p : E) {U : Set E} (hp : p ∈ U)
    {F : E × RotationSpace → ℝ} {n : ℕ}
    (hF : ContDiffOn ℝ n F (U ×ˢ (univ : Set RotationSpace))) :
    ContDiff ℝ n (fun x => F (p,x)) := by
  exact contDiffOn_univ.mp
    (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨hp,mem_univ x⟩))

private theorem angularSlice_jet_norm_le {U : Set E} (hU : IsOpen U) {p : E}
    (hp : p ∈ U) {F : E × RotationSpace → ℝ} {n : ℕ}
    (hF : ContDiffOn ℝ n F (U ×ˢ (univ : Set RotationSpace)))
    (x : RoundSphere3) {M : ℝ} (hB : ∀ k : ℕ, k ≤ n →
      ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun z => F (p,z)) x‖ ≤ (n.factorial : ℝ) * M := by
  let I := ContinuousLinearMap.inr ℝ E RotationSpace
  let S := U ×ˢ (univ : Set RotationSpace)
  let g (z : RotationSpace) := (p,z)
  have hS : IsOpen S := hU.prod isOpen_univ
  have hI : ‖I‖ ≤ 1 := I.opNorm_le_bound zero_le_one fun z => by
    simp [I, ContinuousLinearMap.inr_apply, Prod.norm_def]
  have hD : fderiv ℝ g = fun _ => I := by
    funext z
    exact ((hasFDerivAt_const (𝕜 := ℝ) p z).prodMk (hasFDerivAt_id z)).fderiv
  have hg : ContDiff ℝ n g := contDiff_const.prodMk contDiff_id
  have hC k (hk : k ≤ n) : ‖iteratedFDerivWithin ℝ k F S (g x)‖ ≤ M := by
    rw [iteratedFDerivWithin_of_isOpen k hS (show g x ∈ S from ⟨hp,mem_univ _⟩)]
    exact hB k hk
  have hG k (hk : 1 ≤ k) (_ : k ≤ n) :
      ‖iteratedFDerivWithin ℝ k g univ x‖ ≤ (1 : ℝ)^k := by
    rw [iteratedFDerivWithin_univ,one_pow]
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [← norm_iteratedFDeriv_fderiv, hD]
    cases m with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hI
    | succ m => simp only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m),Pi.zero_apply,norm_zero,zero_le_one]
  have h := norm_iteratedFDerivWithin_comp_le hF hg.contDiffOn le_rfl hS.uniqueDiffOn
    uniqueDiffOn_univ (show MapsTo g univ S from fun z _ => ⟨hp,mem_univ z⟩)
    (mem_univ (x : RotationSpace)) hC hG
  simpa only [iteratedFDerivWithin_univ,one_pow,mul_one,g,Function.comp_def] using h

private theorem jointAngularParameterDerivative_jet_le {U : Set E} (hU : IsOpen U)
    {p : E} (hp : p ∈ U) {F : E × RotationSpace → ℝ} {n : ℕ}
    (hF : ContDiffOn ℝ (n+1 : ℕ) F (U ×ˢ (univ : Set RotationSpace)))
    (x : RoundSphere3) (v : E) :
    ‖iteratedFDeriv ℝ n (jointAngularParameterDerivative v F) (p,(x : RotationSpace))‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n+1) F (p,(x : RotationSpace))‖ := by
  have hS : IsOpen (U ×ˢ (univ : Set RotationSpace)) := hU.prod isOpen_univ
  have hFD : ContDiffAt ℝ n (fderiv ℝ F) (p,(x : RotationSpace)) :=
    (hF.contDiffAt (hS.mem_nhds ⟨hp,mem_univ _⟩)).fderiv_right
      (by simp only [Nat.cast_succ,le_refl])
  have h := norm_iteratedFDeriv_clm_apply_const (c := (v,(0 : RotationSpace))) hFD le_rfl
  rw [norm_iteratedFDeriv_fderiv,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] at h
  exact h

/-- On the common open parameter domain, actual joint ambient derivatives
through order j+12 on the same sphere give (d+1)⁻¹² decay for the j-th
parameter derivative of the actual coefficient integral. -/
theorem exists_jointSphereHarmonicCoefficient_mixed_bound [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : E × RotationSpace → ℝ} {U : Set E}, IsOpen U →
      ∀ (j : ℕ), ContDiffOn ℝ (j+12 : ℕ) F (U ×ˢ (univ : Set RotationSpace)) →
      ∀ {p : E}, p ∈ U → ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ j+12 → ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) →
      ∀ i : SphereHarmonicIndex,
      ‖iteratedFDeriv ℝ j (jointSphereHarmonicCoefficient F i) p‖ ≤
        C * (((i.1 : ℝ) + 1)^12)⁻¹ * M := by
  obtain ⟨A,hA,hrot⟩ := exists_roundRotationJetBound_of_ambientJets
  obtain ⟨B,hB,hdec⟩ := exists_roundSphereHarmonicCoefficient_rotationJetBound
  let C := B*A*((12 : ℕ).factorial : ℝ)
  have hC : 0 ≤ C := by positivity
  refine ⟨C,hC,?_⟩
  intro F U hU j
  induction j generalizing F with
  | zero =>
    intro hF p hp M hM h i
    have hf := angularSlice_contDiff p hp hF
    let r := (((12 : ℕ).factorial : ℝ) * M)
    have r₀ : 0 ≤ r := by positivity
    have hr (k : ℕ) (hk : k ≤ 12) (x : RoundSphere3) :
        ‖iteratedFDeriv ℝ k (fun y => F (p,y)) x‖ ≤ r := by
      have hkf : ContDiffOn ℝ k F (U ×ˢ (univ : Set RotationSpace)) :=
        hF.of_le (by exact_mod_cast hk)
      exact (angularSlice_jet_norm_le hU hp hkf x (fun l hl => h l (hl.trans hk) x)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hk) hM)
    have hj := hrot hf r r₀ hr
    have hd := hdec hf (A*r) (mul_nonneg hA r₀) hj i
    rw [norm_iteratedFDeriv_zero]
    calc
      _ ≤ B * (((i.1 : ℝ) + 1)^12)⁻¹ * (A*r) := hd
      _ = _ := by dsimp [C,r]; ring
  | succ n ih =>
    intro hF p hp M hM h i
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
    let w := v (Fin.last n)
    let G := jointAngularParameterDerivative w F
    have h₁ : ContDiffOn ℝ 1 F (U ×ˢ (univ : Set RotationSpace)) :=
      hF.of_le (by exact_mod_cast (show 1 ≤ n.succ+12 by omega))
    have ha : (n+12)+1 = n.succ+12 := by omega
    have hG : ContDiffOn ℝ (n+12 : ℕ) G (U ×ˢ (univ : Set RotationSpace)) :=
      jointAngularParameterDerivative_contDiffOn (n+12) (by rwa [ha]) hU isOpen_univ w
    have hm k (hk : k ≤ n+12) (x : RoundSphere3) :
        ‖iteratedFDeriv ℝ k G (p,(x : RotationSpace))‖ ≤ M*‖w‖ := by
      have hf' : ContDiffOn ℝ (k+1 : ℕ) F (U ×ˢ (univ : Set RotationSpace)) :=
        hF.of_le (by exact_mod_cast (show k+1 ≤ n.succ+12 by omega))
      have ht := jointAngularParameterDerivative_jet_le hU hp hf' x w
      exact ht.trans (by rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (h _ (by omega) x) (norm_nonneg w))
    have hBnd := ih hG hp (M*‖w‖) (by positivity) hm i
    let J := ContinuousLinearMap.apply ℝ ℝ w
    let c := jointSphereHarmonicCoefficient F i
    have hc : ContDiffAt ℝ (n+1 : ℕ) c p := by
      apply ContDiffOn.contDiffAt _ (hU.mem_nhds hp)
      exact jointSphereHarmonicCoefficient_contDiffOn (n+1)
        (hF.of_le (by exact_mod_cast (show n+1+1 ≤ n.succ+12 by omega)))
        hU isOpen_univ (subset_univ _) i
    have hdc : ContDiffAt ℝ n (fderiv ℝ c) p :=
      hc.fderiv_right (by simp only [Nat.cast_succ,le_refl])
    have heq : EqOn (J ∘ fderiv ℝ c) (jointSphereHarmonicCoefficient G i) U :=
      fun q hq => jointSphereHarmonicCoefficient_fderiv_apply h₁ hU isOpen_univ (subset_univ _) i hq w
    have he := heq.iteratedFDerivWithin (𝕜 := ℝ) n hp
    rw [iteratedFDerivWithin_of_isOpen n hU hp, iteratedFDerivWithin_of_isOpen n hU hp] at he
    have hcomp := J.iteratedFDeriv_comp_left hdc (i := n) le_rfl
    rw [he] at hcomp
    have hval : iteratedFDeriv ℝ (n+1) c p v =
        iteratedFDeriv ℝ n (jointSphereHarmonicCoefficient G i) p (Fin.init v) := by
      rw [iteratedFDeriv_succ_apply_right, hcomp]
      rfl
    rw [hval]
    calc
      _ ≤ ‖iteratedFDeriv ℝ n (jointSphereHarmonicCoefficient G i) p‖ *
          ∏ a, ‖Fin.init v a‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (C * (((i.1 : ℝ) + 1)^12)⁻¹ * (M*‖w‖)) * ∏ a, ‖Fin.init v a‖ :=
          mul_le_mul_of_nonneg_right hBnd (by positivity)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.init, w]; ring

/-- The real C^K coefficient estimate on the same compact parameter region as
the supplied mixed jets of the original joint ambient extension. -/
theorem exists_jointSphereHarmonicCoefficient_uniform_mixed_bound [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : E × RotationSpace → ℝ} {U K : Set E},
      IsOpen U → K ⊆ U → ∀ r : ℕ,
      ContDiffOn ℝ (r+12 : ℕ) F (U ×ˢ (univ : Set RotationSpace)) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ k : ℕ, k ≤ r+12 → ∀ p ∈ K, ∀ x : RoundSphere3,
        ‖iteratedFDeriv ℝ k F (p,(x : RotationSpace))‖ ≤ M) →
      ∀ i : SphereHarmonicIndex,
      ContDiffOn ℝ r (jointSphereHarmonicCoefficient F i) U ∧
      ∀ (j : ℕ), j ≤ r → ∀ p ∈ K,
        ‖iteratedFDeriv ℝ j (jointSphereHarmonicCoefficient F i) p‖ ≤
          C * (((i.1 : ℝ) + 1)^12)⁻¹ * M := by
  obtain ⟨C,hC,h⟩ := exists_jointSphereHarmonicCoefficient_mixed_bound (E := E)
  refine ⟨C,hC,?_⟩
  intro F U K hU hKU r hF M hM hB i
  refine ⟨?_,?_⟩
  · exact jointSphereHarmonicCoefficient_contDiffOn r
      (hF.of_le (by exact_mod_cast (show r+1 ≤ r+12 by omega))) hU isOpen_univ (subset_univ _) i
  · intro j hj p hp
    exact h hU j (hF.of_le (by exact_mod_cast (show j+12 ≤ r+12 by omega)))
      (hKU hp) M hM (fun k hk x => hB k (by omega) p hp x) i

end Burnett.A06
