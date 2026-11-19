import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

open Matrix Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace Burnett.Bianchi.ODE

abbrev Spatial := Fin 3
abbrev Mat := Matrix Spatial Spatial ℝ
abbrev State := ℝ × Mat × Mat × ℝ

def symmPart (B : Mat) : Mat := (1 / 2 : ℝ) • (B + B.transpose)

theorem symmPart_isSymm (B : Mat) : (symmPart B).IsSymm := by
  change (symmPart B).transpose = symmPart B
  simp [symmPart, add_comm]

theorem symmPart_of_isSymm {B : Mat} (hB : B.IsSymm) : symmPart B = B := by
  have h : B.transpose = B := hB
  simp [symmPart, h, ← two_smul ℝ B, smul_smul]

def symmPartCLM : Mat →L[ℝ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := symmPart
      map_add' := fun B C ↦ by simp [symmPart, smul_add, add_add_add_comm]
      map_smul' := fun a B ↦ by simp [symmPart, smul_add, smul_smul, mul_comm] }

def direction (t : ℝ) : Spatial → ℝ := ![Real.cos t, Real.sin t, 0]

def outer (p : Spatial → ℝ) : Mat := Matrix.vecMulVec p p

@[simp] theorem outer_apply (p : Spatial → ℝ) (i j : Spatial) : outer p i j = p i * p j := rfl

theorem outer_isSymm (p : Spatial → ℝ) : (outer p).IsSymm := by
  change (outer p).transpose = outer p
  ext i j
  simp [mul_comm]

def inverseEnergy (G : Mat) (p : Spatial → ℝ) : ℝ := p ⬝ᵥ (G⁻¹ *ᵥ p)

def K (G A : Mat) : Mat := G⁻¹ * A

def W (G : Mat) (p : Spatial → ℝ) : Mat := (inverseEnergy G p)⁻¹ • (G⁻¹ * outer p)

def rateA (G A : Mat) (ρ : ℝ) (p : Spatial → ℝ) : Mat :=
  (2 : ℝ) • (A * G⁻¹ * A) - (K G A).trace • A +
    (ρ / inverseEnergy G p) • outer p

def rateRho (G A : Mat) (ρ : ℝ) (p : Spatial → ℝ) : ℝ :=
  -ρ * ((K G A).trace + ((K G A) * W G p).trace)

theorem rateA_isSymm {G A : Mat} (hG : G.IsSymm) (hA : A.IsSymm) (ρ : ℝ)
    (p : Spatial → ℝ) : (rateA G A ρ p).IsSymm := by
  change (rateA G A ρ p).transpose = rateA G A ρ p
  have hG' : G.transpose = G := hG
  have hA' : A.transpose = A := hA
  have hp : (outer p).transpose = outer p := outer_isSymm p
  simp [rateA, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hG', hA', hp,
    mul_assoc]

def gamma (z : State) : Mat := symmPart z.2.1

def secondForm (z : State) : Mat := symmPart z.2.2.1

def density (z : State) : ℝ := z.2.2.2

def rhs (z : State) : State :=
  let G := gamma z
  let A := secondForm z
  let ρ := density z
  let p := direction z.1
  (1, (2 : ℝ) • A, rateA G A ρ p, rateRho G A ρ p)

def initialState (H : ℝ) : State := (0, (1 : Mat), H • (1 : Mat), 3 * H ^ 2)

theorem gamma_initialState (H : ℝ) : gamma (initialState H) = 1 := by
  apply symmPart_of_isSymm
  exact Matrix.isSymm_one

theorem secondForm_initialState (H : ℝ) : secondForm (initialState H) = H • (1 : Mat) := by
  apply symmPart_of_isSymm
  change (H • (1 : Mat)).transpose = H • (1 : Mat)
  simp

theorem direction_ne_zero (t : ℝ) : direction t ≠ 0 := by
  intro hf
  have hc := congrFun hf (0 : Spatial)
  have hs := congrFun hf (1 : Spatial)
  simp [direction] at hc hs
  have h := Real.cos_sq_add_sin_sq t
  rw [hc, hs] at h
  norm_num at h

theorem inverseEnergy_pos {G : Mat} (hG : G.PosDef) {p : Spatial → ℝ} (hp : p ≠ 0) :
    0 < inverseEnergy G p := by
  have h := hG.inv.2 p hp
  simpa [inverseEnergy] using h

end Burnett.Bianchi.ODE


namespace Burnett.Bianchi.ODE

theorem contDiffOn_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Mat} {U : Set E}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ f x i j) U) :
    ContDiffOn ℝ ∞ (fun x ↦ (f x).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum (fun σ _ ↦ contDiffOn_const.mul
    (contDiffOn_prod (fun i _ ↦ hf (σ i) i)))

theorem contDiffOn_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Mat} {U : Set E}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ f x i j) U)
    (hn : ∀ x ∈ U, (f x).det ≠ 0) (i j : Spatial) :
    ContDiffOn ℝ ∞ (fun x ↦ (f x)⁻¹ i j) U := by
  have hadj : ContDiffOn ℝ ∞ (fun x ↦ (f x).adjugate i j) U := by
    simp only [Matrix.adjugate_apply]
    apply contDiffOn_det (f := fun x ↦ (f x).updateRow j (Pi.single i (1 : ℝ)))
    intro a b
    by_cases ha : a = j
    · subst a
      simpa using (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : E ↦ (Pi.single i (1 : ℝ) : Spatial → ℝ) b) U)
    · simpa [Matrix.updateRow_apply, ha] using hf a b
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul] using
    ((contDiffOn_det hf).inv hn).mul hadj

theorem contDiff_gamma : ContDiff ℝ ∞ gamma :=
  symmPartCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)

theorem contDiff_secondForm : ContDiff ℝ ∞ secondForm :=
  symmPartCLM.contDiff.comp (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))

theorem contDiff_density : ContDiff ℝ ∞ density :=
  contDiff_snd.comp (contDiff_snd.comp contDiff_snd)

theorem contDiff_direction : ContDiff ℝ ∞ direction := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id.cos
  · exact contDiff_id.sin
  · exact contDiff_const

theorem rhs_contDiffOn {U : Set State}
    (hn : ∀ z ∈ U, (gamma z).det ≠ 0)
    (hd : ∀ z ∈ U, inverseEnergy (gamma z) (direction z.1) ≠ 0) :
    ContDiffOn ℝ ∞ rhs U := by
  have hg : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ gamma z i j) U :=
    fun i j ↦ (contDiff_pi.mp (contDiff_pi.mp contDiff_gamma i) j).contDiffOn
  have hA : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ secondForm z i j) U :=
    fun i j ↦ (contDiff_pi.mp (contDiff_pi.mp contDiff_secondForm i) j).contDiffOn
  have hρ : ContDiffOn ℝ ∞ density U := contDiff_density.contDiffOn
  have hp (i : Spatial) : ContDiffOn ℝ ∞ (fun z : State ↦ direction z.1 i) U :=
    ((contDiff_pi.mp contDiff_direction i).comp contDiff_fst).contDiffOn
  have hgInv := contDiffOn_inv hg hn
  have hE : ContDiffOn ℝ ∞ (fun z ↦ inverseEnergy (gamma z) (direction z.1)) U := by
    simp only [inverseEnergy, dotProduct, Matrix.mulVec]
    exact ContDiffOn.sum fun i _ ↦ (hp i).mul
      (ContDiffOn.sum fun j _ ↦ (hgInv i j).mul (hp j))
  have hout (i j : Spatial) :
      ContDiffOn ℝ ∞ (fun z : State ↦ outer (direction z.1) i j) U := by
    simpa only [outer_apply] using (hp i).mul (hp j)
  have hK (i j : Spatial) : ContDiffOn ℝ ∞ (fun z ↦ K (gamma z) (secondForm z) i j) U := by
    simp only [K, Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ ↦ (hgInv i k).mul (hA k j)
  have hW (i j : Spatial) : ContDiffOn ℝ ∞ (fun z ↦ W (gamma z) (direction z.1) i j) U := by
    simp only [W, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    exact (hE.inv hd).mul (ContDiffOn.sum fun k _ ↦ (hgInv i k).mul (hout k j))
  have hθ : ContDiffOn ℝ ∞ (fun z ↦ (K (gamma z) (secondForm z)).trace) U := by
    exact ContDiffOn.sum fun i _ ↦ hK i i
  have hKW : ContDiffOn ℝ ∞ (fun z : State ↦
      (K (gamma z) (secondForm z) * W (gamma z) (direction z.1)).trace) U := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact ContDiffOn.sum fun i _ ↦
      ContDiffOn.sum fun j _ ↦ (hK i j).mul (hW j i)
  have hgA : ContDiffOn ℝ ∞ (fun z ↦ (2 : ℝ) • secondForm z) U :=
    contDiffOn_const.smul contDiff_secondForm.contDiffOn
  have hRA : ContDiffOn ℝ ∞ (fun z ↦ rateA (gamma z) (secondForm z) (density z) (direction z.1)) U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    simp only [rateA, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    apply ContDiffOn.add
    · apply ContDiffOn.sub
      · exact contDiffOn_const.mul (ContDiffOn.sum fun k _ ↦
          (ContDiffOn.sum fun l _ ↦ (hA i l).mul (hgInv l k)).mul (hA k j))
      · exact hθ.mul (hA i j)
    · exact (hρ.div hE hd).mul (hout i j)
  have hRρ : ContDiffOn ℝ ∞
      (fun z ↦ rateRho (gamma z) (secondForm z) (density z) (direction z.1)) U :=
    hρ.neg.mul (hθ.add hKW)
  exact contDiffOn_const.prodMk (hgA.prodMk (hRA.prodMk hRρ))

end Burnett.Bianchi.ODE



set_option autoImplicit false

open Filter Metric Set
open scoped ContDiff Topology NNReal

namespace Burnett.Bianchi.ODE

theorem smooth_integral_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {u : Set E} {v : Set ℝ} {a : ℝ → E}
    (hF : ContDiffOn ℝ ∞ F u) (hv : IsOpen v) (ha : MapsTo a v u)
    (ha' : ∀ t ∈ v, HasDerivAt a (F (a t)) t) :
    ContDiffOn ℝ ∞ a v := by
  have hdiff : DifferentiableOn ℝ a v :=
    fun t ht ↦ (ha' t ht).differentiableAt.differentiableWithinAt
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero =>
    exact contDiffOn_zero.mpr hdiff.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hv]
    refine ⟨hdiff, by simp, ?_⟩
    exact ((contDiffOn_infty.mp hF n).comp ih ha).congr
      (fun t ht ↦ (ha' t ht).deriv)

theorem exists_smooth_integral_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : E → E} {u : Set E} {a₀ : E} (hu : IsOpen u) (ha₀ : a₀ ∈ u)
    (hF : ContDiffOn ℝ ∞ F u) {cap : ℝ} (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ < cap ∧ ∃ a : ℝ → E, a 0 = a₀ ∧
      MapsTo a (Ioo (-τ) τ) u ∧ ContDiffOn ℝ ∞ a (Ioo (-τ) τ) ∧
      ∀ t ∈ Ioo (-τ) τ, HasDerivAt a (F (a t)) t := by
  have hF₀ : ContDiffAt ℝ 1 F a₀ :=
    ((contDiffOn_infty.mp hF 1)).contDiffAt (hu.mem_nhds ha₀)
  obtain ⟨a, ha₀', ε, hε, hder⟩ :=
    hF₀.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hder
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hn : a ⁻¹' u ∈ 𝓝 (0 : ℝ) := (hder 0 hzero).continuousAt
    (hu.mem_nhds (ha₀'.symm ▸ ha₀))
  obtain ⟨δ, hδ, hδa⟩ := Metric.mem_nhds_iff.mp hn
  let τ := min (min ε δ) (cap / 2)
  have hp : 0 < τ := lt_min (lt_min hε hδ) (half_pos hcap)
  have hτε : τ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hτδ : τ ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hτcap : τ < cap := (min_le_right _ _).trans_lt (half_lt_self hcap)
  have hsub : Ioo (-τ) τ ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (neg_le_neg hτε) hτε
  have hmap : MapsTo a (Ioo (-τ) τ) u := by
    intro t ht
    apply hδa
    rw [Real.ball_eq_Ioo, zero_sub, zero_add]
    exact Ioo_subset_Ioo (neg_le_neg hτδ) hτδ ht
  have hlocal : ∀ t ∈ Ioo (-τ) τ, HasDerivAt a (F (a t)) t :=
    fun t ht ↦ hder t (hsub ht)
  exact ⟨τ, hp, hτcap, a, ha₀', hmap, smooth_integral_curve hF isOpen_Ioo hmap hlocal, hlocal⟩

theorem scalar_constraint_persists {a b t₀ : ℝ} {c q : ℝ → ℝ} {K : ℝ≥0}
    (ht₀ : t₀ ∈ Ioo a b) (hc : ∀ t ∈ Ioo a b, |c t| ≤ K)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (c t * q t) t) (hq₀ : q t₀ = 0) :
    ∀ t ∈ Ioo a b, q t = 0 := by
  have hlip (t : ℝ) (ht : t ∈ Ioo a b) :
      LipschitzOnWith K (fun x : ℝ ↦ c t * x) univ := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (hc t ht) (abs_nonneg _)
  have hzero (t : ℝ) (_ : t ∈ Ioo a b) :
      HasDerivAt (0 : ℝ → ℝ) (c t * (0 : ℝ → ℝ) t) t ∧ (0 : ℝ → ℝ) t ∈ univ := by
    simpa using hasDerivAt_const t (0 : ℝ)
  have heq := ODE_solution_unique_of_mem_Ioo hlip ht₀
    (fun t ht ↦ ⟨hq t ht, mem_univ _⟩) hzero hq₀
  exact fun t ht ↦ heq ht

end Burnett.Bianchi.ODE


namespace Burnett.Bianchi.ODE

theorem posDef_of_close_to_identity {G : Mat} (hG : G.IsSymm)
    (hclose : ∀ i j : Spatial, |G i j - (1 : Mat) i j| < 1 / 6) : G.PosDef := by
  have hsym : G.transpose = G := hG
  refine ⟨by simpa [Matrix.IsHermitian, Matrix.conjTranspose, Matrix.transpose] using hsym, ?_⟩
  intro x hx
  change 0 < (star x) ⬝ᵥ (G *ᵥ x)
  have hsx : star x = x := by ext i; simp
  rw [hsx]
  have hxpos : 0 < ∑ i : Spatial, x i ^ 2 := by
    have hex : ∃ i, x i ≠ 0 := by
      by_contra! h
      exact hx (funext h)
    obtain ⟨i, hi⟩ := hex
    exact (sq_pos_of_ne_zero hi).trans_le
      (Finset.single_le_sum (f := fun j : Spatial ↦ x j ^ 2)
        (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i))
  have hterm (i j : Spatial) :
      -(x i ^ 2 + x j ^ 2) / 12 ≤ x i * (G i j - (1 : Mat) i j) * x j := by
    have hbound : |x i * (G i j - (1 : Mat) i j) * x j| ≤ (x i ^ 2 + x j ^ 2) / 12 := by
      rw [abs_mul, abs_mul]
      calc
        |x i| * |G i j - (1 : Mat) i j| * |x j| ≤ |x i| * (1 / 6) * |x j| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_of_lt (hclose i j)) (abs_nonneg _)) (abs_nonneg _)
        _ ≤ _ := by nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have hlow := (neg_le_neg hbound).trans (neg_abs_le _)
    linarith
  have hbound : -(∑ i : Spatial, x i ^ 2) / 2 ≤
      ∑ i : Spatial, ∑ j : Spatial, x i * (G i j - (1 : Mat) i j) * x j := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Spatial))
      (fun i _ ↦ Finset.sum_le_sum (s := (Finset.univ : Finset Spatial))
        (fun j _ ↦ hterm i j))
    refine le_trans (le_of_eq ?_) hsum
    simp only [Fin.sum_univ_three]
    ring
  have hdiff : G *ᵥ x = x + (G - (1 : Mat)) *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hexp : x ⬝ᵥ (G *ᵥ x) = (∑ i : Spatial, x i ^ 2) +
      ∑ i : Spatial, ∑ j : Spatial, x i * (G i j - (1 : Mat) i j) * x j := by
    rw [hdiff]
    simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib, pow_two,
      Matrix.mulVec, Matrix.sub_apply, Finset.mul_sum, mul_assoc]
  rw [hexp]
  linarith

end Burnett.Bianchi.ODE


namespace Burnett.Bianchi.ODE

def stateDomain : Set State :=
  {z | 0 < density z ∧ ∀ i j : Spatial, |gamma z i j - (1 : Mat) i j| < 1 / 6}

theorem isOpen_stateDomain : IsOpen stateDomain := by
  have hρ : IsOpen {z : State | 0 < density z} :=
    isOpen_lt continuous_const contDiff_density.continuous
  have hg (i j : Spatial) : IsOpen {z : State | |gamma z i j - (1 : Mat) i j| < 1 / 6} :=
    isOpen_lt (((contDiff_pi.mp (contDiff_pi.mp contDiff_gamma i) j).continuous.sub
      continuous_const).abs) continuous_const
  have h := hρ.inter (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦ hg i j)
  convert h using 1
  ext z
  simp [stateDomain]

theorem initialState_mem_stateDomain {H : ℝ} (hH : 0 < H) : initialState H ∈ stateDomain := by
  change 0 < 3 * H ^ 2 ∧ ∀ i j : Spatial,
    |gamma (initialState H) i j - (1 : Mat) i j| < 1 / 6
  refine ⟨mul_pos (by norm_num) (sq_pos_of_pos hH), ?_⟩
  rw [gamma_initialState]
  norm_num

theorem gamma_posDef {z : State} (hz : z ∈ stateDomain) : (gamma z).PosDef :=
  posDef_of_close_to_identity (symmPart_isSymm _) hz.2

theorem exists_bianchi_local_flow {H : ℝ} (hH : 0 < H) :
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi / 4 ∧
      ∃ (G A : ℝ → Mat) (ρ : ℝ → ℝ),
        G 0 = 1 ∧ A 0 = H • (1 : Mat) ∧ ρ 0 = 3 * H ^ 2 ∧
        ContDiffOn ℝ ∞ G (Ioo (-τ) τ) ∧ ContDiffOn ℝ ∞ A (Ioo (-τ) τ) ∧
        ContDiffOn ℝ ∞ ρ (Ioo (-τ) τ) ∧
        ∀ t ∈ Ioo (-τ) τ,
          (G t).PosDef ∧ (A t).IsSymm ∧ 0 < ρ t ∧
          HasDerivAt G ((2 : ℝ) • A t) t ∧
          HasDerivAt A (rateA (G t) (A t) (ρ t) (direction t)) t ∧
          HasDerivAt ρ (rateRho (G t) (A t) (ρ t) (direction t)) t := by
  have hs := rhs_contDiffOn
    (U := stateDomain) (fun z hz ↦ (gamma_posDef hz).det_pos.ne')
    (fun z hz ↦ (inverseEnergy_pos (gamma_posDef hz) (direction_ne_zero z.1)).ne')
  obtain ⟨τ, hτ, hτπ, z, hz₀, hzm, hz, hz'⟩ :=
    exists_smooth_integral_curve isOpen_stateDomain (initialState_mem_stateDomain hH) hs
      (div_pos Real.pi_pos (by norm_num : 0 < (4 : ℝ)))
  let time : State →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ _ _
  let sp : State →L[ℝ] Mat × Mat × ℝ := ContinuousLinearMap.snd ℝ _ _
  let aa : Mat × Mat × ℝ →L[ℝ] Mat × ℝ := ContinuousLinearMap.snd ℝ _ _
  let gproj : State →L[ℝ] Mat :=
    symmPartCLM.comp ((ContinuousLinearMap.fst ℝ _ _).comp sp)
  let aproj : State →L[ℝ] Mat :=
    symmPartCLM.comp ((ContinuousLinearMap.fst ℝ _ _).comp (aa.comp sp))
  let rproj : State →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ _ _).comp (aa.comp sp)
  have ht' (t : ℝ) (ht : t ∈ Ioo (-τ) τ) : HasDerivAt (fun s ↦ (z s).1) 1 t :=
    time.hasFDerivAt.comp_hasDerivAt t (hz' t ht)
  have ht (t : ℝ) (ht : t ∈ Ioo (-τ) τ) : (z t).1 = t := by
    have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨neg_neg_of_pos hτ, hτ⟩
    apply (isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      (fun s hs ↦ (ht' s hs).differentiableAt.differentiableWithinAt)
      differentiable_id.differentiableOn
      (fun s hs ↦ (ht' s hs).deriv.trans (hasDerivAt_id s).deriv.symm)
      h0 (by rw [hz₀]; rfl)) ht
  refine ⟨τ, hτ, hτπ, gamma ∘ z, secondForm ∘ z, density ∘ z,
    by simp [hz₀, gamma_initialState], by simp [hz₀, secondForm_initialState],
    by simp [hz₀, density, initialState], contDiff_gamma.comp_contDiffOn hz,
    contDiff_secondForm.comp_contDiffOn hz, contDiff_density.comp_contDiffOn hz, ?_⟩
  intro t hti
  have hgpos := gamma_posDef (hzm hti)
  have hAsymm : (secondForm (z t)).IsSymm := symmPart_isSymm _
  refine ⟨hgpos, hAsymm, (hzm hti).1, ?_, ?_, ?_⟩
  · have h := gproj.hasFDerivAt.comp_hasDerivAt t (hz' t hti)
    change HasDerivAt (gamma ∘ z) (symmPart ((2 : ℝ) • secondForm (z t))) t at h
    have hsymm : ((2 : ℝ) • secondForm (z t)).IsSymm := by
      change ((2 : ℝ) • secondForm (z t)).transpose = (2 : ℝ) • secondForm (z t)
      rw [Matrix.transpose_smul, show (secondForm (z t)).transpose = _ from hAsymm]
    rwa [symmPart_of_isSymm hsymm] at h
  · have h := aproj.hasFDerivAt.comp_hasDerivAt t (hz' t hti)
    change HasDerivAt (secondForm ∘ z) (symmPart (rateA (gamma (z t)) (secondForm (z t))
      (density (z t)) (direction (z t).1))) t at h
    have hGamma : (gamma (z t)).IsSymm := symmPart_isSymm _
    have hrate := rateA_isSymm hGamma hAsymm (density (z t)) (direction (z t).1)
    rwa [symmPart_of_isSymm hrate, ht _ hti] at h
  · have h := rproj.hasFDerivAt.comp_hasDerivAt t (hz' t hti)
    change HasDerivAt (density ∘ z) (rateRho (gamma (z t)) (secondForm (z t))
      (density (z t)) (direction (z t).1)) t at h
    rwa [ht _ hti] at h

end Burnett.Bianchi.ODE


namespace Burnett.Bianchi.ODE

theorem hasDerivAt_mul_matrix {B C : ℝ → Mat} {B' C' : Mat} {t : ℝ}
    (hB : HasDerivAt B B' t) (hC : HasDerivAt C C' t) :
    HasDerivAt (fun s ↦ B s * C s) (B' * C t + B t * C') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hC k) j))

theorem hasDerivAt_trace_matrix {B : ℝ → Mat} {B' : Mat} {t : ℝ}
    (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s ↦ (B s).trace) B'.trace t := by
  simp only [Matrix.trace, Matrix.diag]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) i)

theorem trace_W (G : Mat) (p : Spatial → ℝ) (hd : inverseEnergy G p ≠ 0) :
    (W G p).trace = 1 := by
  rw [W, Matrix.trace_smul, outer, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm, ← inverseEnergy, smul_eq_mul, inv_mul_cancel₀ hd]

theorem hasDerivAt_K {G A : ℝ → Mat} {p : Spatial → ℝ} {ρ t : ℝ}
    (hgInv : DifferentiableAt ℝ (fun s ↦ (G s)⁻¹) t)
    (hg : ∀ᶠ s in 𝓝 t, (G s).det ≠ 0)
    (hG : HasDerivAt G ((2 : ℝ) • A t) t)
    (hA : HasDerivAt A (rateA (G t) (A t) ρ p) t) :
    HasDerivAt (fun s ↦ K (G s) (A s))
      (ρ • W (G t) p - (K (G t) (A t)).trace • K (G t) (A t)) t := by
  let κ := K (G t) (A t)
  let kd := deriv (fun s ↦ K (G s) (A s)) t
  have hkD := (hasDerivAt_mul_matrix hgInv.hasDerivAt hA).differentiableAt
  change DifferentiableAt ℝ (fun s ↦ K (G s) (A s)) t at hkD
  have hk : HasDerivAt (fun s ↦ K (G s) (A s)) kd t := hkD.hasDerivAt
  have hmul : (fun s ↦ G s * K (G s) (A s)) =ᶠ[𝓝 t] A := by
    filter_upwards [hg] with s hs
    rw [K, ← Matrix.mul_assoc, (G s).mul_nonsing_inv (isUnit_iff_ne_zero.mpr hs), one_mul]
  have heq : ((2 : ℝ) • A t) * κ + G t * kd = rateA (G t) (A t) ρ p :=
    (hasDerivAt_mul_matrix hG hk).deriv.symm.trans ((hA.congr_of_eventuallyEq hmul).deriv)
  have he : G t * kd =
      -(κ.trace • A t) + (ρ / inverseEnergy (G t) p) • outer p := by
    have h := heq
    change ((2 : ℝ) • A t) * κ + G t * kd = rateA (G t) (A t) ρ p at h
    rw [rateA, Matrix.smul_mul, Matrix.mul_assoc] at h
    rw [sub_eq_add_neg] at h
    exact add_left_cancel (h.trans (add_assoc _ _ _))
  have hGzero := hg.self_of_nhds
  have hGinv := (G t).nonsing_inv_mul (isUnit_iff_ne_zero.mpr hGzero)
  have hd := congrArg (fun v : Mat ↦ (G t)⁻¹ * v) he
  change (G t)⁻¹ * (G t * kd) =
    (G t)⁻¹ * (-(κ.trace • A t) + (ρ / inverseEnergy (G t) p) • outer p) at hd
  rw [← Matrix.mul_assoc, hGinv, one_mul, Matrix.mul_add, Matrix.mul_neg,
    Matrix.mul_smul, Matrix.mul_smul] at hd
  change kd = -(κ.trace • κ) + (ρ / inverseEnergy (G t) p) • ((G t)⁻¹ * outer p) at hd
  rw [W, smul_smul, ← div_eq_mul_inv]
  simpa [hd, sub_eq_add_neg, add_comm] using hk

def constraint (G A : Mat) (ρ : ℝ) : ℝ :=
  (K G A).trace ^ 2 - ((K G A) * (K G A)).trace - 2 * ρ

theorem hasDerivAt_constraint {G A : ℝ → Mat} {ρ : ℝ → ℝ}
    {p : Spatial → ℝ} {t : ℝ}
    (hd : inverseEnergy (G t) p ≠ 0)
    (hk : HasDerivAt (fun s ↦ K (G s) (A s))
      (ρ t • W (G t) p - (K (G t) (A t)).trace • K (G t) (A t)) t)
    (hρ : HasDerivAt ρ (rateRho (G t) (A t) (ρ t) p) t) :
    HasDerivAt (fun s ↦ constraint (G s) (A s) (ρ s))
      (-2 * (K (G t) (A t)).trace * constraint (G t) (A t) (ρ t)) t := by
  have h1 := hasDerivAt_trace_matrix hk
  have h2 := hasDerivAt_trace_matrix (hasDerivAt_mul_matrix hk hk)
  have hc := (h1.pow 2).sub h2 |>.sub (hρ.const_mul 2)
  change HasDerivAt (fun s ↦ constraint (G s) (A s) (ρ s)) _ t at hc
  convert hc using 1
  simp only [constraint, rateRho, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    trace_W _ _ hd, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_mul_comm (W (G t) p) (K (G t) (A t))]
  ring

end Burnett.Bianchi.ODE


namespace Burnett.Bianchi.ODE

theorem initial_constraint (H : ℝ) :
    constraint (1 : Mat) (H • (1 : Mat)) (3 * H ^ 2) = 0 := by
  simp only [constraint, K, inv_one, one_mul, Matrix.trace_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_eq_mul]
  norm_num [Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_three]
  ring

theorem exists_bianchi_constrained_flow {H : ℝ} (hH : 0 < H) :
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi / 4 ∧
      ∃ (G A : ℝ → Mat) (ρ : ℝ → ℝ),
        G 0 = 1 ∧ A 0 = H • (1 : Mat) ∧ ρ 0 = 3 * H ^ 2 ∧
        ContDiffOn ℝ ∞ G (Ioo (-τ) τ) ∧ ContDiffOn ℝ ∞ A (Ioo (-τ) τ) ∧
        ContDiffOn ℝ ∞ ρ (Ioo (-τ) τ) ∧
        ∀ t ∈ Ioo (-τ) τ,
          (G t).PosDef ∧ (A t).IsSymm ∧ 0 < ρ t ∧
          HasDerivAt G ((2 : ℝ) • A t) t ∧
          HasDerivAt A (rateA (G t) (A t) (ρ t) (direction t)) t ∧
          HasDerivAt ρ (rateRho (G t) (A t) (ρ t) (direction t)) t ∧
          HasDerivAt (fun s ↦ K (G s) (A s))
            (ρ t • W (G t) (direction t) - (K (G t) (A t)).trace • K (G t) (A t)) t ∧
          HasDerivAt (fun s ↦ (K (G s) (A s)).trace)
            (ρ t - (K (G t) (A t)).trace ^ 2) t ∧
          (K (G t) (A t)).trace ^ 2 - ((K (G t) (A t)) * (K (G t) (A t))).trace = 2 * ρ t := by
  obtain ⟨τ, hτ, hτπ, G, A, ρ, hG₀, hA₀, hρ₀, hG, hA, hρ, hsys⟩ :=
    exists_bianchi_local_flow hH
  let U := Ioo (-τ) τ
  have hU : IsOpen U := isOpen_Ioo
  have h0 : (0 : ℝ) ∈ U := ⟨neg_neg_of_pos hτ, hτ⟩
  have hdet (t : ℝ) (ht : t ∈ U) : (G t).det ≠ 0 := (hsys t ht).1.det_pos.ne'
  have hd (t : ℝ) (ht : t ∈ U) : inverseEnergy (G t) (direction t) ≠ 0 :=
    (inverseEnergy_pos (hsys t ht).1 (direction_ne_zero t)).ne'
  have hinv := contDiffOn_inv (fun i j ↦ contDiffOn_pi.mp (contDiffOn_pi.mp hG i) j) hdet
  have hinvAll : ContDiffOn ℝ ∞ (fun t ↦ (G t)⁻¹) U :=
    contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr (hinv i)
  have hK' (t : ℝ) (ht : t ∈ U) : HasDerivAt (fun s ↦ K (G s) (A s))
      (ρ t • W (G t) (direction t) - (K (G t) (A t)).trace • K (G t) (A t)) t := by
    obtain ⟨_, _, _, hdG, hdA, _⟩ := hsys t ht
    exact hasDerivAt_K
      ((hinvAll.differentiableOn (by simp) t ht).differentiableAt (hU.mem_nhds ht))
      (Filter.eventually_of_mem (hU.mem_nhds ht) fun s hs ↦ hdet s hs) hdG hdA
  have hθ (t : ℝ) (ht : t ∈ U) :
      HasDerivAt (fun s ↦ (K (G s) (A s)).trace) (ρ t - (K (G t) (A t)).trace ^ 2) t := by
    simpa [Matrix.trace_sub, Matrix.trace_smul, trace_W _ _ (hd t ht), pow_two] using
      hasDerivAt_trace_matrix (hK' t ht)
  let c : ℝ → ℝ := fun t ↦ -2 * (K (G t) (A t)).trace
  have hc₀ : ContinuousAt c 0 := (hθ 0 h0).continuousAt.const_mul _
  have Hbound : {t : ℝ | |c t| < |c 0| + 1} ∈ 𝓝 (0 : ℝ) :=
    hc₀.abs (Iio_mem_nhds (by linarith : |c 0| < |c 0| + 1))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhds_iff.mp Hbound
  let σ := min δ τ
  have hσ : 0 < σ := lt_min hδ hτ
  have hσπ : σ < Real.pi / 4 := (min_le_right _ _).trans_lt hτπ
  have hsub : Ioo (-σ) σ ⊆ U :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  let M : ℝ≥0 := ⟨|c 0| + 1, by positivity⟩
  have hc (t : ℝ) (ht : t ∈ Ioo (-σ) σ) : |c t| ≤ (M : ℝ) := by
    have htδ : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Real.ball_eq_Ioo, zero_sub, zero_add]
      exact Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _) ht
    exact le_of_lt (hδbound htδ)
  have hcons := scalar_constraint_persists (K := M) (a := -σ) (b := σ)
    (t₀ := 0) (q := fun t ↦ constraint (G t) (A t) (ρ t)) (c := c)
    ⟨neg_neg_of_pos hσ, hσ⟩ hc
    (fun t ht ↦ hasDerivAt_constraint (hd t (hsub ht)) (hK' t (hsub ht)) (hsys t (hsub ht)).2.2.2.2.2)
    (by
      change constraint (G 0) (A 0) (ρ 0) = 0
      rw [hG₀, hA₀, hρ₀, initial_constraint])
  refine ⟨σ, hσ, hσπ, G, A, ρ, hG₀, hA₀, hρ₀, hG.mono hsub, hA.mono hsub, hρ.mono hsub, ?_⟩
  intro t ht
  obtain ⟨hGpos, hAsymm, hρpos, hdG, hdA, hdρ⟩ := hsys t (hsub ht)
  refine ⟨hGpos, hAsymm, hρpos, hdG, hdA, hdρ, hK' t (hsub ht), hθ t (hsub ht), ?_⟩
  have hC := hcons t ht
  dsimp only [constraint] at hC
  linarith

end Burnett.Bianchi.ODE
