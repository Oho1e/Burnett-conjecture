import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Burnett.Geometry.ConnectionDifference

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.HarmonicShearL2

open Set MeasureTheory Filter
open scoped Topology ENNReal

/-- Use the positive paper index corresponding to Lean's zero-based sequence. -/
def positiveIndex (n : ℕ) : ℕ := n + 1

def epsilon (n : ℕ) : ℝ := (positiveIndex n : ℝ)⁻¹

def delta (n : ℕ) : ℝ := ((positiveIndex n : ℝ)^3)⁻¹

def shear (n : ℕ) (p : ℝ) : ℝ := epsilon n ^ 2 * Real.sin (p / epsilon n)

/-- Source component in the variables \(p=t-z\) and \(q=t-x^1\). -/
def sourceInParameters (n : ℕ) (p q : ℝ) : ℝ :=
  (2 * epsilon n / delta n) * Real.cos (p / epsilon n) *
    Real.cos ((q + shear n p) / delta n)

theorem positiveIndex_pos (n : ℕ) : 0 < positiveIndex n := Nat.succ_pos n

theorem epsilon_pos (n : ℕ) : 0 < epsilon n :=
  inv_pos.mpr (by exact_mod_cast positiveIndex_pos n)

theorem delta_pos (n : ℕ) : 0 < delta n :=
  inv_pos.mpr (pow_pos (by exact_mod_cast positiveIndex_pos n) 3)

theorem source_amplitude (n : ℕ) :
    2 * epsilon n / delta n = 2 * (positiveIndex n : ℝ)^2 := by
  have hn : (positiveIndex n : ℝ) ≠ 0 := by exact_mod_cast (positiveIndex_pos n).ne'
  unfold epsilon delta
  field_simp

/-- An integer number of full waves gives the same squared cosine integral for every shift. -/
theorem integral_shifted_cos_sq (k : ℕ) (hk : k ≠ 0) (b : ℝ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * x + b)^2 = Real.pi := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_add (f := fun y => Real.cos y ^ 2) hkR b]
  rw [mul_zero, zero_add, add_comm ((k : ℝ) * (2 * Real.pi)) b, integral_cos_sq,
    Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, smul_eq_mul]
  field_simp; ring

theorem setIntegral_shifted_cos_sq (k : ℕ) (hk : k ≠ 0) (b : ℝ) :
    ∫ x in Icc (0 : ℝ) (2 * Real.pi), Real.cos ((k : ℝ) * x + b)^2 = Real.pi := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  exact integral_shifted_cos_sq k hk b

theorem q_cos_sq (n : ℕ) (p : ℝ) :
    ∫ q in Icc (0 : ℝ) (2 * Real.pi), Real.cos ((q + shear n p) / delta n)^2 = Real.pi := by
  have hk : positiveIndex n ^ 3 ≠ 0 := pow_ne_zero 3 (positiveIndex_pos n).ne'
  calc
    _ = ∫ q in Icc (0 : ℝ) (2 * Real.pi),
        Real.cos ((↑(positiveIndex n ^ 3) : ℝ) * q + (positiveIndex n : ℝ)^3 * shear n p)^2 := by
      apply integral_congr_ae
      exact ae_of_all _ fun q => by
        have harg : (q + shear n p) / delta n =
            (↑(positiveIndex n ^ 3) : ℝ) * q + (positiveIndex n : ℝ)^3 * shear n p := by
          simp only [delta, div_inv_eq_mul, Nat.cast_pow]
          ring
        simp only [harg]
    _ = Real.pi := setIntegral_shifted_cos_sq _ hk _

theorem p_cos_sq (n : ℕ) :
    ∫ p in Icc (0 : ℝ) (2 * Real.pi), Real.cos (p / epsilon n)^2 = Real.pi := by
  simpa only [epsilon, div_inv_eq_mul, add_zero, mul_comm] using
    setIntegral_shifted_cos_sq (positiveIndex n) (positiveIndex_pos n).ne' 0

theorem continuous_sourceInParameters (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => sourceInParameters n z.1 z.2) := by
  unfold sourceInParameters shear
  fun_prop

def pqBox : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) (2 * Real.pi)

def unitBox : Set (ℝ × ℝ) :=
  Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

def parameterBox : Set ((ℝ × ℝ) × (ℝ × ℝ)) := unitBox ×ˢ pqBox

theorem isCompact_pqBox : IsCompact pqBox := isCompact_Icc.prod isCompact_Icc

theorem isCompact_unitBox : IsCompact unitBox := isCompact_Icc.prod isCompact_Icc

theorem isCompact_parameterBox : IsCompact parameterBox :=
  isCompact_unitBox.prod isCompact_pqBox

theorem source_sq_inner_integral (n : ℕ) (p : ℝ) :
    ∫ q in Icc (0 : ℝ) (2 * Real.pi), sourceInParameters n p q ^ 2 =
      (2 * epsilon n / delta n)^2 * Real.cos (p / epsilon n)^2 * Real.pi := by
  simp_rw [sourceInParameters, mul_pow]
  rw [integral_const_mul, q_cos_sq]

theorem source_sq_pqBox (n : ℕ) :
    ∫ z in pqBox, sourceInParameters n z.1 z.2 ^ 2 =
      4 * Real.pi ^ 2 * (positiveIndex n : ℝ)^4 := by
  have hi : IntegrableOn (fun z : ℝ × ℝ => sourceInParameters n z.1 z.2 ^ 2)
      pqBox volume := ((continuous_sourceInParameters n).pow 2).continuousOn.integrableOn_compact isCompact_pqBox
  rw [Measure.volume_eq_prod, pqBox, MeasureTheory.setIntegral_prod _ hi]
  simp_rw [source_sq_inner_integral, mul_assoc _ _ Real.pi, mul_comm (Real.cos _ ^ 2) Real.pi,
    ← mul_assoc _ Real.pi (Real.cos _ ^ 2)]
  rw [integral_const_mul, p_cos_sq, source_amplitude]
  ring

theorem volume_unitBox : volume unitBox = 1 := by
  rw [unitBox, Measure.volume_eq_prod, Measure.prod_prod]
  simp only [Real.volume_Icc]
  norm_num

/-- Four-dimensional box integral, including both unit-length dummy coordinates. -/
theorem source_sq_parameterBox (n : ℕ) :
    ∫ z in parameterBox, sourceInParameters n z.2.1 z.2.2 ^ 2 =
      4 * Real.pi ^ 2 * (positiveIndex n : ℝ)^4 := by
  have hc : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => sourceInParameters n z.2.1 z.2.2 ^ 2) :=
    ((continuous_sourceInParameters n).pow 2).comp continuous_snd
  have hi : IntegrableOn (fun z : (ℝ × ℝ) × (ℝ × ℝ) => sourceInParameters n z.2.1 z.2.2 ^ 2)
      parameterBox volume := hc.continuousOn.integrableOn_compact isCompact_parameterBox
  rw [Measure.volume_eq_prod, parameterBox, MeasureTheory.setIntegral_prod _ hi]
  simp_rw [source_sq_pqBox]
  rw [setIntegral_const, measureReal_def, volume_unitBox]
  simp

end Burnett.Geometry.HarmonicShearL2

namespace Burnett.Geometry.HarmonicShearL2

open Set MeasureTheory Filter
open Burnett.Geometry.ConnectionDifference
open scoped Topology ENNReal Matrix

abbrev ParameterSpace := (ℝ × ℝ) × (ℝ × ℝ)

/-- The manuscript's fixed coordinate chart, with parameters ordered as \(t,x^2,p,q\). -/
def boxCoordinates : CoordinateSpace ≃ₜ ParameterSpace where
  toFun x := ((x 0, x 2), (x 0 - x 3, x 0 - x 1))
  invFun y := WithLp.toLp 2 ![y.1.1, y.1.1 - y.2.2, y.1.2, y.1.1 - y.2.1]
  left_inv x := by
    apply WithLp.ofLp_injective 2
    funext i
    fin_cases i <;> simp
  right_inv y := by
    rcases y with ⟨⟨t, x₂⟩, ⟨p, q⟩⟩
    simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (PiLp.continuous_apply 2 _ 0).prodMk (PiLp.continuous_apply 2 _ 2)
    · exact ((PiLp.continuous_apply 2 _ 0).sub (PiLp.continuous_apply 2 _ 3)).prodMk
        ((PiLp.continuous_apply 2 _ 0).sub (PiLp.continuous_apply 2 _ 1))
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

/-- Matrix before regrouping the four Euclidean coordinates into two pairs. -/
def boxMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 1, 0, 0, -1; 1, -1, 0, 0]

theorem det_boxMatrix : Matrix.det boxMatrix = 1 := by
  have hrow (j : Fin 3) : boxMatrix 0 j.succ = 0 := by
    fin_cases j <;> rfl
  have hdiag : boxMatrix 0 0 = 1 := rfl
  have hminor : boxMatrix.submatrix Fin.succ (0 : Fin 4).succAbove =
      !![0, 1, 0; 0, 0, -1; -1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hdiag, hminor, Matrix.det_fin_three]
  norm_num
  change (-1 : ℝ) * (-1) = 1
  norm_num

private def splitFour : (Fin 4 → ℝ) ≃ᵐ ParameterSpace :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => ℝ) (finSumFinEquiv (m := 2) (n := 2)).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).prodCongr
        (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

private theorem splitFour_volume : MeasurePreserving splitFour := by
  have h₁ := volume_measurePreserving_piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
    (finSumFinEquiv (m := 2) (n := 2)).symm
  have h₂ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  have hFin := volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  exact (hFin.prod hFin).comp (h₂.comp h₁)

private theorem splitFour_apply (x : Fin 4 → ℝ) : splitFour x = ((x 0, x 1), (x 2, x 3)) := by
  rfl

private theorem matrix_apply (x : Fin 4 → ℝ) :
    Matrix.toLin' boxMatrix x = ![x 0, x 2, x 0 - x 3, x 0 - x 1] := by
  funext i
  rw [Matrix.toLin'_apply, Matrix.mulVec]
  have hfin : (2 : Fin 3).succ = (3 : Fin 4) := by decide
  fin_cases i <;> norm_num [boxMatrix, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg, hfin]

theorem boxCoordinates_volume : MeasurePreserving boxCoordinates := by
  have h₁ : MeasurePreserving (Matrix.toLin' boxMatrix) :=
    ⟨(Matrix.toLin' boxMatrix).continuous_of_finiteDimensional.measurable, by
      rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (M := boxMatrix) (by rw [det_boxMatrix]; norm_num)]
      simp [det_boxMatrix]⟩
  have h₂ : MeasurePreserving (@WithLp.ofLp 2 (Fin 4 → ℝ)) := PiLp.volume_preserving_ofLp (Fin 4)
  have h := splitFour_volume.comp (h₁.comp h₂)
  convert h using 1
  funext x
  simp only [Function.comp_apply, splitFour_apply, matrix_apply]
  rfl

/-- A fixed compact parallelepiped, independent of the sequence index. -/
def fixedBox : Set CoordinateSpace := boxCoordinates ⁻¹' parameterBox

theorem fixedBox_eq_image : fixedBox = boxCoordinates.symm '' parameterBox := by
  ext x
  simp [fixedBox, Homeomorph.image_symm]

theorem isCompact_fixedBox : IsCompact fixedBox := by
  rw [fixedBox_eq_image]
  exact isCompact_parameterBox.image boxCoordinates.symm.continuous

def source (n : ℕ) (x : CoordinateSpace) : ℝ :=
  sourceInParameters n (x 0 - x 3) (x 0 - x 1)

theorem continuous_source (n : ℕ) : Continuous (source n) := by
  unfold source sourceInParameters shear
  fun_prop

theorem source_sq_fixedBox (n : ℕ) :
    ∫ x in fixedBox, source n x ^ 2 = 4 * Real.pi ^ 2 * (positiveIndex n : ℝ)^4 := by
  have h := boxCoordinates_volume.setIntegral_preimage_emb
    boxCoordinates.toMeasurableEquiv.measurableEmbedding
    (fun y : ParameterSpace => sourceInParameters n y.2.1 y.2.2 ^ 2) parameterBox
  exact h.trans (source_sq_parameterBox n)

theorem source_memLp_fixedBox (n : ℕ) :
    MemLp (source n) 2 ((volume : Measure CoordinateSpace).restrict fixedBox) := by
  haveI : IsFiniteMeasure ((volume : Measure CoordinateSpace).restrict fixedBox) :=
    isFiniteMeasure_restrict.mpr isCompact_fixedBox.measure_ne_top
  refine (memLp_const |2 * epsilon n / delta n|).mono'
    (continuous_source n).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  simp only [source, sourceInParameters, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (|2 * epsilon n / delta n| * 1) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _))
        (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem source_L2_fixedBox (n : ℕ) :
    eLpNorm (source n) 2 ((volume : Measure CoordinateSpace).restrict fixedBox) =
      ENNReal.ofReal (2 * Real.pi * (positiveIndex n : ℝ)^2) := by
  rw [(source_memLp_fixedBox n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [source_sq_fixedBox, ← one_div, ← Real.sqrt_eq_rpow,
    show 4 * Real.pi ^ 2 * (positiveIndex n : ℝ)^4 =
      (2 * Real.pi * (positiveIndex n : ℝ)^2)^2 by ring,
    Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi * (positiveIndex n : ℝ)^2)]

theorem source_L2_tendsto_top :
    Tendsto (fun n : ℕ => eLpNorm (source n) 2 ((volume : Measure CoordinateSpace).restrict fixedBox))
      atTop (𝓝 ⊤) := by
  simp_rw [source_L2_fixedBox]
  have hIndex : Tendsto (fun n : ℕ => (positiveIndex n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id)
  have hPow : Tendsto (fun n : ℕ => (positiveIndex n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hIndex
  exact ENNReal.tendsto_ofReal_atTop.comp (hPow.const_mul_atTop (by positivity : 0 < 2 * Real.pi))

/-- The same fixed set controls any tensor source with this \(21\)-component. -/
theorem tensor_source_L2_tendsto_top (F : ℕ → CoordinateSpace → Burnett.RicciSymbol.Tensor2)
    (h : ∀ n x, F n x 2 1 = source n x) :
    Tendsto (fun n : ℕ => eLpNorm (F n) 2 ((volume : Measure CoordinateSpace).restrict fixedBox))
      atTop (𝓝 ⊤) := by
  apply tendsto_nhds_top_mono' source_L2_tendsto_top
  intro n
  apply eLpNorm_mono
  intro x
  rw [← h n x]
  exact (norm_le_pi_norm (F n x 2) 1).trans (norm_le_pi_norm (F n x) 2)

end Burnett.Geometry.HarmonicShearL2
