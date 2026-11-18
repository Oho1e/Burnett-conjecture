import Burnett.Counterexamples.HarmonicShear.Geometry
import Burnett.Counterexamples.HarmonicShear.L2
import Burnett.Counterexamples.HarmonicShear.EuclideanReference
import Burnett.Geometry.BackgroundConnection
import Burnett.Geometry.CovariantTensorNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

namespace Burnett.HarmonicShear.Bounds

open Filter MeasureTheory Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CovariantTensorNorm Burnett.Geometry.GramCoordinateBound
open scoped ContDiff BigOperators Topology ENNReal

def frequency (n : ℕ) : ℝ := (n : ℝ) + 1
def eps (n : ℕ) : ℝ := (frequency n)⁻¹
def delta (n : ℕ) : ℝ := (frequency n ^ 3)⁻¹

def p (x : CoordinateSpace) : ℝ := x 0 - x 3
def q (x : CoordinateSpace) : ℝ := x 0 - x 1
def firstShear (n : ℕ) (u : ℝ) : ℝ := eps n ^ 2 * Real.sin (u / eps n)
def firstSlope (n : ℕ) (u : ℝ) : ℝ := eps n * Real.cos (u / eps n)
def secondSlope (n : ℕ) (u : ℝ) : ℝ := delta n * Real.cos (u / delta n)

def tag (a i : Index) : ℝ := if i = a then 1 else 0
def P (i : Index) : ℝ := tag 0 i - tag 3 i
def Q (i : Index) : ℝ := tag 0 i - tag 1 i

def phase (n : ℕ) (x : CoordinateSpace) : ℝ := q x + firstShear n (p x)
def phaseRow (n : ℕ) (x : CoordinateSpace) (i : Index) : ℝ := Q i + firstSlope n (p x) * P i
def firstRow (n : ℕ) (x : CoordinateSpace) (i : Index) : ℝ := tag 1 i - firstSlope n (p x) * P i
def secondRow (n : ℕ) (x : CoordinateSpace) (i : Index) : ℝ := tag 2 i - secondSlope n (phase n x) * phaseRow n x i

/-- Components of the pullback metric in the harmonic coordinates. -/
def components (n : ℕ) (x : CoordinateSpace) : Tensor2 := fun i j =>
  -(tag 0 i * tag 0 j) + firstRow n x i * firstRow n x j + secondRow n x i * secondRow n x j +
    tag 3 i * tag 3 j

def flatComponents : Tensor2 := fun i j =>
  -(tag 0 i * tag 0 j) + tag 1 i * tag 1 j + tag 2 i * tag 2 j + tag 3 i * tag 3 j

private theorem frequency_ge_one (n : ℕ) : 1 ≤ frequency n := le_add_of_nonneg_left (Nat.cast_nonneg n)
private theorem eps_pos (n : ℕ) : 0 < eps n := inv_pos.mpr (lt_of_lt_of_le zero_lt_one (frequency_ge_one n))
private theorem delta_pos (n : ℕ) : 0 < delta n := inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one (frequency_ge_one n)) _)
private theorem eps_le_one (n : ℕ) : eps n ≤ 1 := inv_le_one_of_one_le₀ (frequency_ge_one n)
private theorem delta_le_one (n : ℕ) : delta n ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (frequency_ge_one n))

private theorem abs_tag_le (a i : Index) : |tag a i| ≤ 1 := by by_cases h : i = a <;> simp [tag, h]
private theorem abs_P_le (i : Index) : |P i| ≤ 1 := by fin_cases i <;> norm_num [P, tag, Fin.ext_iff]
private theorem abs_Q_le (i : Index) : |Q i| ≤ 1 := by fin_cases i <;> norm_num [Q, tag]

private theorem abs_product_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

private theorem abs_firstSlope_le (n : ℕ) (u : ℝ) : |firstSlope n u| ≤ eps n := by
  unfold firstSlope
  rw [abs_mul, abs_of_pos (eps_pos n)]
  exact mul_le_of_le_one_right (eps_pos n).le (Real.abs_cos_le_one _)

private theorem abs_secondSlope_le (n : ℕ) (u : ℝ) : |secondSlope n u| ≤ delta n := by
  unfold secondSlope
  rw [abs_mul, abs_of_pos (delta_pos n)]
  exact mul_le_of_le_one_right (delta_pos n).le (Real.abs_cos_le_one _)

private theorem abs_phaseRow_le (n : ℕ) (x : CoordinateSpace) (i : Index) : |phaseRow n x i| ≤ 2 := by
  unfold phaseRow
  have h := abs_product_le ((abs_firstSlope_le n (p x)).trans (eps_le_one n)) (abs_P_le i)
  exact (abs_add_le _ _).trans (by linarith [abs_Q_le i])

private theorem abs_firstRow_le (n : ℕ) (x : CoordinateSpace) (i : Index) : |firstRow n x i| ≤ 2 := by
  unfold firstRow
  have h := abs_product_le ((abs_firstSlope_le n (p x)).trans (eps_le_one n)) (abs_P_le i)
  exact (abs_sub _ _).trans (by linarith [abs_tag_le 1 i])

private theorem abs_secondRow_le (n : ℕ) (x : CoordinateSpace) (i : Index) : |secondRow n x i| ≤ 3 := by
  unfold secondRow
  have h := abs_product_le ((abs_secondSlope_le n (phase n x)).trans (delta_le_one n)) (abs_phaseRow_le n x i)
  exact (abs_sub _ _).trans (by linarith [abs_tag_le 2 i])

private theorem abs_firstRow_sub_tag_le (n : ℕ) (x : CoordinateSpace) (i : Index) :
    |firstRow n x i - tag 1 i| ≤ eps n := by
  rw [show firstRow n x i - tag 1 i = -(firstSlope n (p x) * P i) by unfold firstRow; ring, abs_neg]
  simpa only [mul_one] using abs_product_le (abs_firstSlope_le n (p x)) (abs_P_le i)

private theorem abs_secondRow_sub_tag_le (n : ℕ) (x : CoordinateSpace) (i : Index) :
    |secondRow n x i - tag 2 i| ≤ delta n * 2 := by
  rw [show secondRow n x i - tag 2 i = -(secondSlope n (phase n x) * phaseRow n x i) by
    unfold secondRow
    ring, abs_neg]
  exact abs_product_le (abs_secondSlope_le n (phase n x)) (abs_phaseRow_le n x i)

theorem abs_perturbation_components_le (n : ℕ) (x : CoordinateSpace) (i j : Index) :
    |components n x i j - flatComponents i j| ≤ 3 * eps n + 8 * delta n := by
  let U := firstRow n x
  let V := secondRow n x
  let u := tag 1
  let v := tag 2
  have hU : |U i * U j - u i * u j| ≤ 3 * eps n := by
    rw [show U i * U j - u i * u j = (U i - u i) * U j + u i * (U j - u j) by ring]
    have hi := abs_product_le (abs_firstRow_sub_tag_le n x i) (abs_firstRow_le n x j)
    have hj := abs_product_le (abs_tag_le 1 i) (abs_firstRow_sub_tag_le n x j)
    exact (abs_add_le _ _).trans (by linarith)
  have hV : |V i * V j - v i * v j| ≤ 8 * delta n := by
    rw [show V i * V j - v i * v j = (V i - v i) * V j + v i * (V j - v j) by ring]
    have hi := abs_product_le (abs_secondRow_sub_tag_le n x i) (abs_secondRow_le n x j)
    have hj := abs_product_le (abs_tag_le 2 i) (abs_secondRow_sub_tag_le n x j)
    exact (abs_add_le _ _).trans (by linarith)
  rw [show components n x i j - flatComponents i j =
      (U i * U j - u i * u j) + (V i * V j - v i * v j) by unfold components flatComponents U V u v; ring]
  exact (abs_add_le _ _).trans (add_le_add hU hV)

private theorem firstShear_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (firstShear n) (firstSlope n u) u := by
  have h := (((hasDerivAt_id u).div_const (eps n)).sin).const_mul (eps n ^ 2)
  convert h using 1
  simp only [firstSlope, id_eq]
  field_simp [(eps_pos n).ne']

private theorem firstSlope_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (firstSlope n) (-Real.sin (u / eps n)) u := by
  have h := (((hasDerivAt_id u).div_const (eps n)).cos).const_mul (eps n)
  convert h using 1
  simp only [id_eq]
  field_simp [(eps_pos n).ne']

private theorem secondSlope_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (secondSlope n) (-Real.sin (u / delta n)) u := by
  have h := (((hasDerivAt_id u).div_const (delta n)).cos).const_mul (delta n)
  convert h using 1
  simp only [id_eq]
  field_simp [(delta_pos n).ne']

theorem components_contDiff (n : ℕ) (i j : Index) : ContDiff ℝ ∞ (fun x => components n x i j) := by
  have hproj (a : Index) : ContDiff ℝ ∞ (fun x : CoordinateSpace => x a) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := CoordinateSpace) (F := ℝ) (EuclideanSpace.proj a)
  have hp : ContDiff ℝ ∞ p := (hproj 0).sub (hproj 3)
  have hq : ContDiff ℝ ∞ q := (hproj 0).sub (hproj 1)
  have ha : ContDiff ℝ ∞ (fun x => firstSlope n (p x)) :=
    contDiff_const.mul (hp.div_const (eps n)).cos
  have hs : ContDiff ℝ ∞ (phase n) :=
    hq.add (contDiff_const.mul (hp.div_const (eps n)).sin)
  have hb : ContDiff ℝ ∞ (fun x => secondSlope n (phase n x)) :=
    contDiff_const.mul (hs.div_const (delta n)).cos
  have hU (k : Index) : ContDiff ℝ ∞ (fun x => firstRow n x k) :=
    contDiff_const.sub (ha.mul contDiff_const)
  have hS (k : Index) : ContDiff ℝ ∞ (fun x => phaseRow n x k) :=
    contDiff_const.add (ha.mul contDiff_const)
  have hV (k : Index) : ContDiff ℝ ∞ (fun x => secondRow n x k) :=
    contDiff_const.sub (hb.mul (hS k))
  exact (((contDiff_const.add ((hU i).mul (hU j))).add ((hV i).mul (hV j))).add contDiff_const)

private def line (x : CoordinateSpace) (k : Index) (t : ℝ) : CoordinateSpace :=
  x + t • EuclideanSpace.single k 1

private theorem line_apply (x : CoordinateSpace) (k i : Index) (t : ℝ) :
    line x k t i = x i + t * tag k i := by
  change x i + t * (EuclideanSpace.single k (1 : ℝ)) i = _
  simp [tag, EuclideanSpace.single_apply, eq_comm]

private theorem p_line (x : CoordinateSpace) (k : Index) (t : ℝ) : p (line x k t) = p x + t * P k := by
  have h (i : Index) : tag k i = tag i k := by simp [tag, eq_comm]
  simp only [p, P, line_apply, h 0, h 3]
  ring

private theorem q_line (x : CoordinateSpace) (k : Index) (t : ℝ) : q (line x k t) = q x + t * Q k := by
  have h (i : Index) : tag k i = tag i k := by simp [tag, eq_comm]
  simp only [q, Q, line_apply, h 0, h 1]
  ring

private theorem line_hasDerivAt (x : CoordinateSpace) (k : Index) :
    HasDerivAt (line x k) (EuclideanSpace.single k 1) 0 := by
  simpa only [line, id_eq, one_smul] using
    ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single k (1 : ℝ))).const_add x

private theorem coordinateJet_eq_deriv_line (F : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (k i j : Index) (hf : DifferentiableAt ℝ (fun y => F y i j) x) :
    coordinateJet F x k i j = deriv (fun t => F (line x k t) i j) 0 := by
  have h : HasFDerivAt (fun y => F y i j) (fderiv ℝ (fun y => F y i j) x) (line x k 0) := by
    simpa only [line, zero_smul, add_zero] using hf.hasFDerivAt
  exact (h.comp_hasDerivAt 0 (line_hasDerivAt x k)).deriv.symm

private theorem row_directional_derivatives (n : ℕ) (x : CoordinateSpace) (k : Index) :
    (∀ i, ∃ D : ℝ, HasDerivAt (fun t => firstRow n (line x k t) i) D 0 ∧ |D| ≤ 1) ∧
    (∀ i, ∃ D : ℝ, HasDerivAt (fun t => secondRow n (line x k t) i) D 0 ∧ |D| ≤ 5) := by
  let L := line x k
  have hp : HasDerivAt (fun t => p (L t)) (P k) 0 := by
    simp only [L, p_line]
    simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (P k)).const_add (p x)
  have hq : HasDerivAt (fun t => q (L t)) (Q k) 0 := by
    simp only [L, q_line]
    simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (Q k)).const_add (q x)
  let da := -Real.sin (p (L 0) / eps n) * P k
  let ds := Q k + firstSlope n (p (L 0)) * P k
  let db := -Real.sin (phase n (L 0) / delta n) * ds
  have ha : HasDerivAt (fun t => firstSlope n (p (L t))) da 0 :=
    HasDerivAt.comp (h := fun t => p (L t)) (h₂ := firstSlope n) 0 (firstSlope_hasDerivAt n (p (L 0))) hp
  have hs : HasDerivAt (fun t => phase n (L t)) ds 0 :=
    hq.add (HasDerivAt.comp (h := fun t => p (L t)) (h₂ := firstShear n) 0
      (firstShear_hasDerivAt n (p (L 0))) hp)
  have hb : HasDerivAt (fun t => secondSlope n (phase n (L t))) db 0 :=
    HasDerivAt.comp (h := fun t => phase n (L t)) (h₂ := secondSlope n) 0
      (secondSlope_hasDerivAt n (phase n (L 0))) hs
  have haBound : |da| ≤ 1 := by
    simpa only [da, abs_neg, one_mul] using
      abs_product_le (show |-Real.sin (p (L 0) / eps n)| ≤ 1 by rw [abs_neg]; exact Real.abs_sin_le_one _)
        (abs_P_le k)
  have hsb : |ds| ≤ 2 := abs_phaseRow_le n (L 0) k
  have hbBound : |db| ≤ 2 := by
    simpa only [db, one_mul] using
      abs_product_le (show |-Real.sin (phase n (L 0) / delta n)| ≤ 1 by rw [abs_neg]; exact Real.abs_sin_le_one _) hsb
  constructor
  · intro i
    refine ⟨-(da * P i), (ha.mul_const (P i)).const_sub (tag 1 i), ?_⟩
    rw [abs_neg]
    simpa only [one_mul] using abs_product_le haBound (abs_P_le i)
  · intro i
    have hS : HasDerivAt (fun t => phaseRow n (L t) i) (da * P i) 0 := (ha.mul_const (P i)).const_add (Q i)
    refine ⟨-(db * phaseRow n (L 0) i + secondSlope n (phase n (L 0)) * (da * P i)),
      (hb.mul hS).const_sub (tag 2 i), ?_⟩
    rw [abs_neg]
    have h₁ := abs_product_le hbBound (abs_phaseRow_le n (L 0) i)
    have h₂ := abs_product_le ((abs_secondSlope_le n (phase n (L 0))).trans (delta_le_one n))
      (abs_product_le haBound (abs_P_le i))
    exact (abs_add_le _ _).trans (by linarith)

/-- Every first derivative of the metric perturbation has a uniform global bound. -/
theorem abs_perturbation_jet_entry_le (n : ℕ) (x : CoordinateSpace) (k i j : Index) :
    |coordinateJet (fun y => components n y - flatComponents) x k i j| ≤ 34 := by
  obtain ⟨hU, hV⟩ := row_directional_derivatives n x k
  obtain ⟨ui, hui, huiB⟩ := hU i
  obtain ⟨uj, huj, hujB⟩ := hU j
  obtain ⟨vi, hvi, hviB⟩ := hV i
  obtain ⟨vj, hvj, hvjB⟩ := hV j
  have hd := ((((hui.mul huj).const_add (-(tag 0 i * tag 0 j))).add (hvi.mul hvj)).add_const
    (tag 3 i * tag 3 j)).sub_const (flatComponents i j)
  change HasDerivAt (fun t => (components n (line x k t) - flatComponents) i j) _ 0 at hd
  have hdiff : DifferentiableAt ℝ (fun y => (components n y - flatComponents) i j) x :=
    (((components_contDiff n i j).differentiable (by simp)).differentiableAt).sub_const _
  rw [coordinateJet_eq_deriv_line _ x k i j hdiff, hd.deriv]
  have h₁ := abs_product_le huiB (abs_firstRow_le n (line x k 0) j)
  have h₂ := abs_product_le (abs_firstRow_le n (line x k 0) i) hujB
  have h₃ := abs_product_le hviB (abs_secondRow_le n (line x k 0) j)
  have h₄ := abs_product_le (abs_secondRow_le n (line x k 0) i) hvjB
  have hFirst := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  have hSecond := (abs_add_le _ _).trans (add_le_add h₃ h₄)
  exact (abs_add_le _ _).trans ((add_le_add hFirst hSecond).trans_eq (by norm_num))

theorem euclidean_norm2_eq_sqrt_sum (T : Tensor2) :
    norm2 (1 : Matrix Index Index ℝ) T = Real.sqrt (∑ i, ∑ j, T i j ^ 2) := by
  have hGram : gram2 (1 : Matrix Index Index ℝ) = 1 := by
    simp only [gram2, inv_one, Matrix.one_kronecker_one]
  rw [norm2_eq_gramNorm, hGram]
  simp [gramNorm, gramEnergy, flatten2, dotProduct, Fintype.sum_prod_type, pow_two]

theorem euclidean_norm3_eq_sqrt_sum (T : FirstJet) :
    norm3 (1 : Matrix Index Index ℝ) T = Real.sqrt (∑ i, ∑ j, ∑ k, T i j k ^ 2) := by
  have hGram : gram3 (1 : Matrix Index Index ℝ) = 1 := by
    simp only [gram3, gram2, inv_one, Matrix.one_kronecker_one]
  rw [norm3_eq_gramNorm, hGram]
  simp [gramNorm, gramEnergy, flatten3, dotProduct, Fintype.sum_prod_type, pow_two]

theorem euclidean_perturbation_norm_le (n : ℕ) (x : CoordinateSpace) :
    norm2 (1 : Matrix Index Index ℝ) (components n x - flatComponents) ≤ 4 * (3 * eps n + 8 * delta n) := by
  let amplitude := 3 * eps n + 8 * delta n
  have hC : 0 ≤ amplitude :=
    add_nonneg (mul_nonneg (by norm_num) (eps_pos n).le) (mul_nonneg (by norm_num) (delta_pos n).le)
  have hSum : (∑ i, ∑ j, (components n x i j - flatComponents i j)^2) ≤ (4 * amplitude)^2 := by
    calc
      _ ≤ ∑ _i : Index, ∑ _j : Index, amplitude^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have h := (sq_le_sq₀ (abs_nonneg (components n x i j - flatComponents i j)) hC).mpr
          (abs_perturbation_components_le n x i j)
        simpa only [sq_abs] using h
      _ = _ := by norm_num [Index, Finset.sum_const]; ring
  rw [euclidean_norm2_eq_sqrt_sum]
  exact (Real.sqrt_le_sqrt hSum).trans_eq (Real.sqrt_sq (by positivity))

theorem euclidean_perturbation_norm_tendstoUniformly :
    TendstoUniformly (fun n x => norm2 (1 : Matrix Index Index ℝ) (components n x - flatComponents))
      (fun _ => (0 : ℝ)) atTop := by
  have heps : Tendsto eps atTop (𝓝 (0 : ℝ)) := by
    simpa only [eps, frequency, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hdelta : Tendsto delta atTop (𝓝 (0 : ℝ)) := by
    simpa only [delta, eps, inv_pow, zero_pow (show (3 : ℕ) ≠ 0 by norm_num)] using heps.pow 3
  have hErr : Tendsto (fun n => 4 * (3 * eps n + 8 * delta n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_add] using ((heps.const_mul 3).add (hdelta.const_mul 8)).const_mul 4
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hErr.eventually_lt_const hε] with n hn x
  have hn' : 0 ≤ norm2 (1 : Matrix Index Index ℝ) (components n x - flatComponents) := Real.sqrt_nonneg _
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn'] using
    (euclidean_perturbation_norm_le n x).trans_lt hn

theorem euclidean_perturbation_Dh_norm_le (n : ℕ) (x : CoordinateSpace) :
    norm3 (1 : Matrix Index Index ℝ) (coordinateJet (fun y => components n y - flatComponents) x) ≤ 272 := by
  let J := coordinateJet (fun y => components n y - flatComponents) x
  have hSum : (∑ k, ∑ i, ∑ j, J k i j ^ 2) ≤ (272 : ℝ)^2 := by
    calc
      _ ≤ ∑ _k : Index, ∑ _i : Index, ∑ _j : Index, (34 : ℝ)^2 := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        have h := (sq_le_sq₀ (abs_nonneg (J k i j)) (show (0 : ℝ) ≤ 34 by norm_num)).mpr
          (abs_perturbation_jet_entry_le n x k i j)
        simpa only [sq_abs] using h
      _ = _ := by norm_num [Index, Finset.sum_const]
  rw [euclidean_norm3_eq_sqrt_sum]
  exact (Real.sqrt_le_sqrt hSum).trans_eq (Real.sqrt_sq (by norm_num))

theorem euclidean_perturbation_Dh_eLpNorm_le (n : ℕ) (μ : Measure CoordinateSpace) :
    eLpNorm (fun x => norm3 (1 : Matrix Index Index ℝ)
      (coordinateJet (fun y => components n y - flatComponents) x)) ⊤ μ ≤ ENNReal.ofReal 272 := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards with x
  have hz : 0 ≤ norm3 (1 : Matrix Index Index ℝ)
      (coordinateJet (fun y => components n y - flatComponents) x) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hz]
  exact euclidean_perturbation_Dh_norm_le n x

end Burnett.HarmonicShear.Bounds

namespace Burnett.HarmonicShear.Bounds

open Filter MeasureTheory Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.HarmonicShear Burnett.Geometry.CovariantTensorNorm
open scoped ContDiff Topology ENNReal

private theorem frequency_geometry (n : ℕ) : HarmonicShear.frequency n = frequency n := by
  simp [HarmonicShear.frequency, frequency]

theorem pullback_components_eq (n : ℕ) (x : CoordinateSpace) :
    metricComponents (metric n) x = components n x := by
  let f := HarmonicShear.firstShear n
  let j := secondShear n
  have hf : ContDiff ℝ ∞ f := contDiff_firstShear n
  have hj : ContDiff ℝ ∞ j := contDiff_secondShear n
  have hfp : ContDiff ℝ ∞ (fun y => f (HarmonicShear.p y)) := hf.comp contDiff_p
  have hjp : ContDiff ℝ ∞ (fun y => j (HarmonicShear.phase f y)) := hj.comp (contDiff_phase hf)
  have hF (a : Index) : coordPartial a (fun y => y 1 - f (HarmonicShear.p y)) x =
      firstRow n x a := by
    rw [coordPartial_sub a (contDiff_coordinate 1) hfp, coordPartial_coordinate,
      coordPartial_comp a hf contDiff_p, coordPartial_p]
    simp only [f, deriv_firstShear, firstRow, firstSlope, tag, P, eps, HarmonicShear.eps,
      frequency_geometry]
    rfl
  have hJ (a : Index) : coordPartial a (fun y => y 2 - j (HarmonicShear.phase f y)) x =
      secondRow n x a := by
    rw [coordPartial_sub a (contDiff_coordinate 2) hjp, coordPartial_coordinate,
      coordPartial_comp a hj (contDiff_phase hf), coordPartial_phase a hf, coordPartial_p, coordPartial_q]
    simp only [f, j, deriv_secondShear, deriv_firstShear, secondRow, secondSlope, phaseRow, phase,
      firstSlope, firstShear, tag, P, Q, eps, delta,
      HarmonicShear.eps, HarmonicShear.delta, HarmonicShear.phase, HarmonicShear.firstShear, frequency_geometry]
    rfl
  ext a b
  change metricComponents (pullbackMetric f j) x a b = components n x a b
  simp only [pullbackMetric_components hf hj, coordPartial_coordinate, hF, hJ, components, tag]

theorem minkowski_components_eq (x : CoordinateSpace) :
    metricComponents (fun _ : CoordinateSpace => minkowski) x = flatComponents := by
  ext a b
  have hb (i : Index) : coordinateBasis i = EuclideanSpace.single i 1 :=
    EuclideanSpace.basisFun_apply _ _ i
  simp only [metricComponents, Burnett.Geometry.FiberMetric.covariant, hb,
    minkowski, LinearMap.mk₂_apply, minkowskiPair, flatComponents, tag, EuclideanSpace.single_apply]
  simp only [eq_comm (a := a), eq_comm (a := b)]

theorem perturbation_eq_components (n : ℕ) :
    perturbation n = fun x => components n x - flatComponents := by
  funext x
  rw [perturbation, pullback_components_eq, minkowski_components_eq]

theorem pullback_euclidean_norm_tendstoUniformly :
    TendstoUniformly (fun n x => norm2 (1 : Matrix Index Index ℝ) (perturbation n x))
      (fun _ => (0 : ℝ)) atTop := by
  simpa only [perturbation_eq_components] using euclidean_perturbation_norm_tendstoUniformly

theorem pullback_euclidean_Dh_eLpNorm_le (n : ℕ) (μ : Measure CoordinateSpace) :
    eLpNorm (fun x => norm3 (1 : Matrix Index Index ℝ) (coordinateJet (perturbation n) x)) ⊤ μ ≤
      ENNReal.ofReal 272 := by
  simpa only [perturbation_eq_components] using euclidean_perturbation_Dh_eLpNorm_le n μ

/-- The ordinary background wave operator of each tensor component of the actual perturbation. -/
def tensorBoxSource (n : ℕ) (x : CoordinateSpace) : Tensor2 :=
  fun a b => box (fun y => perturbation n y a b) x

theorem tensorBoxSource_L2_tendsto_top :
    Tendsto (fun n => eLpNorm (tensorBoxSource n) 2
      ((volume : Measure CoordinateSpace).restrict Burnett.Geometry.HarmonicShearL2.fixedBox)) atTop (𝓝 ⊤) := by
  apply Burnett.Geometry.HarmonicShearL2.tensor_source_L2_tendsto_top
  intro n x
  exact box_perturbation_21 n x

end Burnett.HarmonicShear.Bounds

namespace Burnett.HarmonicShear.Bounds

open Filter MeasureTheory Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.HarmonicShear Burnett.Geometry.CovariantTensorNorm Burnett.HarmonicShear.Reference
open Burnett.Geometry.ManifoldMetricSequence
open scoped ContDiff Topology ENNReal

/-- The pullback Minkowski metrics as actual fields on the Euclidean model manifold. -/
def shearField (n : ℕ) : Burnett.Geometry.ManifoldBilinear.Field (M := CoordinateSpace) :=
  fieldOfComponents (metricComponents (metric n))

def flatField : Burnett.Geometry.ManifoldBilinear.Field (M := CoordinateSpace) :=
  fieldOfComponents (metricComponents (fun _ => minkowski))

theorem shearField_isSmooth (n : ℕ) : Burnett.Geometry.ManifoldBilinear.IsSmooth (shearField n) :=
  fieldOfComponents_isSmooth _ (fun i j => by simp only [pullback_components_eq]; exact components_contDiff n i j)

theorem flatField_isSmooth : Burnett.Geometry.ManifoldBilinear.IsSmooth flatField :=
  fieldOfComponents_isSmooth _ (fun i j => by simp only [minkowski_components_eq]; exact contDiff_const)

theorem shearField_locallyUniformlyConverges :
    LocallyUniformlyConverges euclideanMetric shearField flatField := by
  apply locallyUniformlyConverges_fieldOfComponents
  intro S _
  simpa only [pullback_components_eq, minkowski_components_eq] using
    euclidean_perturbation_norm_tendstoUniformly.tendstoUniformlyOn (s := S)

theorem shearField_intrinsicDh_compact_bound :
    ∀ S : Set CoordinateSpace, IsCompact S → ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      eLpNorm (Burnett.Geometry.IntrinsicDhMeasure.normScalar euclideanMetric (shearField n - flatField))
        ⊤ ((Burnett.Geometry.ManifoldVolume.geometricMeasure flatField).restrict S) ≤ ENNReal.ofReal C := by
  apply intrinsicDh_compact_bounds_of_coordinateJet _ _ shearField_isSmooth flatField_isSmooth
  intro S _
  refine ⟨272, by norm_num, fun n x _ => ?_⟩
  simpa only [pullback_components_eq, minkowski_components_eq] using euclidean_perturbation_Dh_norm_le n x

theorem flatField_geometricMeasure :
    Burnett.Geometry.ManifoldVolume.geometricMeasure flatField = (volume : Measure CoordinateSpace) := by
  apply geometricMeasure_fieldOfComponents_eq_volume
  intro x
  rw [minkowski_components_eq]
  have hFlat : flatComponents = Matrix.diagonal sign := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [flatComponents, sign, tag, Matrix.diagonal_apply, Fin.ext_iff]
  rw [hFlat, Matrix.det_diagonal, Fin.prod_univ_four]
  norm_num [sign, Fin.ext_iff]

/-- Divergence also holds for the Euclidean tensor norm and the actual Minkowski geometric volume. -/
theorem tensorBoxSource_euclidean_L2_tendsto_top :
    Tendsto (fun n => eLpNorm (fun x => norm2 (1 : Matrix Index Index ℝ) (tensorBoxSource n x)) 2
      ((Burnett.Geometry.ManifoldVolume.geometricMeasure flatField).restrict
        Burnett.Geometry.HarmonicShearL2.fixedBox)) atTop (𝓝 ⊤) := by
  rw [flatField_geometricMeasure]
  apply tendsto_nhds_top_mono' Burnett.Geometry.HarmonicShearL2.source_L2_tendsto_top
  intro n
  apply eLpNorm_mono
  intro x
  have hSource : tensorBoxSource n x 2 1 = Burnett.Geometry.HarmonicShearL2.source n x :=
    box_perturbation_21 n x
  have hNonneg : 0 ≤ norm2 (1 : Matrix Index Index ℝ) (tensorBoxSource n x) := Real.sqrt_nonneg _
  rw [← hSource, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hNonneg]
  simpa only [Matrix.one_apply_eq, one_mul, Real.sqrt_one] using
    abs_entry_le_norm2 (1 : Matrix Index Index ℝ) Matrix.PosDef.one (tensorBoxSource n x) 2 1

end Burnett.HarmonicShear.Bounds

namespace Burnett.HarmonicShear.Bounds

open Burnett.RicciSymbol Burnett.HarmonicShear Burnett.HarmonicShear.Reference
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldBilinear
open scoped ContDiff Manifold

theorem fieldOfMetricComponents_apply (G : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x u v : CoordinateSpace) : fieldOfComponents (metricComponents G) x u v = G x u v := by
  rw [fieldOfComponents_apply, metricComponents_eq_toMatrix, Matrix.toBilin_toMatrix]

theorem coordinateBilinear_shearField (n : ℕ) (c : CoordinateSpace) :
    coordinateBilinear (shearField n) c = metric n := by
  funext x
  rw [shearField, coordinateBilinear_fieldOfComponents, metricComponents_eq_toMatrix, Matrix.toBilin_toMatrix]

theorem coordinateBilinear_flatField (c : CoordinateSpace) :
    coordinateBilinear flatField c = fun _ => minkowski := by
  funext x
  rw [flatField, coordinateBilinear_fieldOfComponents, metricComponents_eq_toMatrix, Matrix.toBilin_toMatrix]

/-- Pointwise equivalence to the fixed Minkowski bilinear form. -/
def HasMinkowskiSignature (g : Field (M := CoordinateSpace)) : Prop :=
  ∀ x : CoordinateSpace, ∃ A : CoordinateSpace ≃L[ℝ] CoordinateSpace,
    ∀ u v : CoordinateSpace, g x u v = minkowski (A u) (A v)

theorem shearField_hasMinkowskiSignature (n : ℕ) : HasMinkowskiSignature (shearField n) := by
  intro x
  let f := HarmonicShear.firstShear n
  let j := secondShear n
  let Y := (diffeomorph f j (contDiff_firstShear n) (contDiff_secondShear n)).symm
  let A : CoordinateSpace ≃L[ℝ] CoordinateSpace := Y.mfderivToContinuousLinearEquiv (by simp) x
  have hA : (A : CoordinateSpace →L[ℝ] CoordinateSpace) = fderiv ℝ (inverse f j) x := by
    change (Y.mfderivToContinuousLinearEquiv (by simp) x).toContinuousLinearMap = _
    rw [Diffeomorph.mfderivToContinuousLinearEquiv_coe, mfderiv_eq_fderiv]
    rfl
  refine ⟨A, fun u v => ?_⟩
  rw [shearField, fieldOfMetricComponents_apply]
  change minkowski (fderiv ℝ (inverse f j) x u) (fderiv ℝ (inverse f j) x v) = _
  rw [← hA]
  rfl

theorem flatField_hasMinkowskiSignature : HasMinkowskiSignature flatField := by
  intro x
  refine ⟨ContinuousLinearEquiv.refl ℝ CoordinateSpace, fun u v => ?_⟩
  simp only [flatField, fieldOfMetricComponents_apply, ContinuousLinearEquiv.refl_apply]

private theorem minkowski_left_nondegenerate (u : CoordinateSpace) (h : ∀ v, minkowski u v = 0) :
    u = 0 := by
  ext i
  have hv := h (EuclideanSpace.single i (1 : ℝ))
  change minkowskiPair u (EuclideanSpace.single i (1 : ℝ)) = 0 at hv
  fin_cases i <;> simpa [minkowskiPair, EuclideanSpace.single_apply, Fin.ext_iff] using hv

theorem IsSymmetric_of_hasMinkowskiSignature (g : Field (M := CoordinateSpace))
    (h : HasMinkowskiSignature g) : IsSymmetric g := by
  intro x u v
  obtain ⟨A, hA⟩ := h x
  rw [hA u v, hA v u]
  change minkowskiPair (A u) (A v) = minkowskiPair (A v) (A u)
  simp only [minkowskiPair, mul_comm]

theorem IsNondegenerate_of_hasMinkowskiSignature (g : Field (M := CoordinateSpace))
    (h : HasMinkowskiSignature g) : IsNondegenerate g := by
  intro x u hu
  obtain ⟨A, hA⟩ := h x
  apply A.injective
  rw [map_zero]
  apply minkowski_left_nondegenerate
  intro w
  obtain ⟨v, rfl⟩ := A.surjective w
  exact (hA u v).symm.trans (hu v)

end Burnett.HarmonicShear.Bounds
