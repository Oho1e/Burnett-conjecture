import Burnett.Analysis.PrincipalEnergy.Energy.CompactScalarMultiplier
import Burnett.Analysis.PrincipalEnergy.Energy.CompactFourierNorms

set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection Op)
open scoped BigOperators ComplexConjugate InnerProductSpace ContDiff NNReal

/-- A finite matrix of smooth functions acts on the same compact Schwartz domain. -/
def compactFiniteMultiplier {ι : Type*} [Fintype ι] (r : ι → ι → Space → ℂ)
    (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) :
    CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι :=
  ∑ j, {
    toFun := fun f =>
      ⟨fun i => smoothScalarSchwartzProduct (r i j) (hr i j) (f.val j) (f.property j),
        fun i => (f.property j).mul_left⟩
    map_add' := fun f g => by
      apply Subtype.ext
      funext i
      ext x
      change r i j x * (f.val j x+g.val j x) = r i j x*f.val j x+r i j x*g.val j x
      rw [mul_add]
    map_smul' := fun c f => by
      apply Subtype.ext
      funext i
      ext x
      change r i j x * (c*f.val j x) = c*(r i j x*f.val j x)
      ring }

theorem compactFiniteMultiplier_eqSchwartzSum {ι : Type*} [Fintype ι] (r : ι → ι → Space → ℂ)
    (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (f : CompactSchwartzComponents ι) (i : ι) :
    (compactFiniteMultiplier r hr f).val i =
      ∑ j, smoothScalarSchwartzProduct (r i j) (hr i j) (f.val j) (f.property j) := by
  change LinearMap.proj (R := ℂ) i ((compactSchwartzComponents ι).subtype (compactFiniteMultiplier r hr f)) = _
  simp only [compactFiniteMultiplier, LinearMap.sum_apply, map_sum]
  rfl

@[simp] theorem compactFiniteMultiplier_apply {ι : Type*} [Fintype ι] (r : ι → ι → Space → ℂ)
    (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (f : CompactSchwartzComponents ι) (i : ι) (x : Space) :
    (compactFiniteMultiplier r hr f).val i x = ∑ j, r i j x*f.val j x := by
  symm
  rw [compactFiniteMultiplier_eqSchwartzSum]
  change _ = SchwartzMap.delta ℂ ℂ x (∑ j, smoothScalarSchwartzProduct (r i j) (hr i j) (f.val j) (f.property j))
  simp only [map_sum, SchwartzMap.delta_apply]
  rfl

theorem compactFiniteMultiplier_leibniz {ι : Type*} [Fintype ι] (r : ι → ι → Space → ℂ)
    (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (b : Fin 4) :
    let D := compactMatrixCoordinatePartial (ι := ι) b
    let R := compactTransportOp (compactFiniteMultiplier r hr)
    let dR := compactTransportOp (compactFiniteMultiplier (fun i j => scalarCoordinateDerivative (r i j) b)
      (fun i j => scalarCoordinateDerivative_smooth (hr i j) b))
    D*R = R*D+dR := by
  intro D R dR
  apply LinearMap.ext
  intro u
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  dsimp only [D, R, dR, compactMatrixCoordinatePartial]
  simp only [Module.End.mul_apply, LinearMap.add_apply, compactTransportOp_apply, ← map_add]
  apply congrArg (compactMatrixTestEquiv ι)
  apply Subtype.ext
  funext i
  ext x
  change fderiv ℝ (fun y => (compactFiniteMultiplier r hr f).val i y) x (coordinateDirection b) =
    (compactFiniteMultiplier r hr (compactComponentDerivative b f)).val i x +
      (compactFiniteMultiplier (fun i j => scalarCoordinateDerivative (r i j) b)
        (fun i j => scalarCoordinateDerivative_smooth (hr i j) b) f).val i x
  simp only [compactFiniteMultiplier_apply]
  change fderiv ℝ (fun y => ∑ j, r i j y * f.val j y) x (coordinateDirection b) =
    (∑ j, r i j x * (fderiv ℝ (f.val j : Space → ℂ) x (coordinateDirection b))) +
      ∑ j, (fderiv ℝ (r i j) x (coordinateDirection b))*f.val j x
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y => r i j y * f.val j y)
    (fun j _ => ((hr i j).differentiable (by simp) x).mul (f.val j).differentiableAt),
    ContinuousLinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul ((hr i j).differentiable (by simp) x) (f.val j).differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem compactFiniteMultiplier_integrable_pair {ι : Type*} [Fintype ι]
    (r : ι → ι → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (f g : CompactSchwartzComponents ι)
    (i j : ι) : Integrable (fun x => conj (r i j x * f.val j x)*g.val i x) := by
  let v := smoothScalarSchwartzProduct (r i j) (hr i j) (f.val j) (f.property j)
  exact (((Complex.continuous_conj.comp v.continuous).mul (g.val i).continuous).integrable_of_hasCompactSupport
    (((f.property j).mul_left).comp_left (map_zero (starRingEnd ℂ))).mul_right)

theorem compactFiniteMultiplier_adjoints {ι : Type*} [Fintype ι]
    (r s : ι → ι → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (s i j)) (h : ∀ i j x, conj (r i j x) = s j i x)
    (u v : CompactMatrixTest ι) :
    ⟪compactTransportOp (compactFiniteMultiplier r hr) u, v⟫_ℂ =
      ⟪u, compactTransportOp (compactFiniteMultiplier s hs) v⟫_ℂ := by
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective u
  obtain ⟨g, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  simp only [compactTransportOp_apply, compactMatrixTestEquiv_inner, compactFiniteMultiplier_apply,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  have hL (i : ι) := integral_finset_sum Finset.univ
    (fun j _ => compactFiniteMultiplier_integrable_pair r hr f g i j)
  have hR (j i : ι) : Integrable (fun x => conj (f.val j x) * (s j i x * g.val i x)) := by
    let m := smoothScalarSchwartzProduct (s j i) (hs j i) (g.val i) (g.property i)
    exact (((Complex.continuous_conj.comp (f.val j).continuous).mul m.continuous).integrable_of_hasCompactSupport
      ((g.property i).mul_left).mul_left)
  calc
    (∑ i, ∫ x, ∑ j, conj (r i j x*f.val j x)*g.val i x) =
        ∑ i, ∑ j, ∫ x, conj (r i j x*f.val j x)*g.val i x := by
      exact Finset.sum_congr rfl fun i _ => hL i
    _ = ∑ j, ∑ i, ∫ x, conj (f.val j x) * (s j i x * g.val i x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      apply integral_congr_ae
      filter_upwards with x
      rw [map_mul, h i j x]
      ring
    _ = _ := by
      exact Finset.sum_congr rfl fun j _ =>
        (integral_finset_sum Finset.univ (fun i _ => hR j i)).symm

theorem compactFiniteMultiplier_norm_le {ι : Type*} [Fintype ι]
    (r : ι → ι → Space → ℂ) (hr : ∀ i j, ContDiff ℝ ∞ (r i j)) (A : ℝ) (hA : 0 ≤ A)
    (hSup : ∀ i j x, ‖r i j x‖ ≤ A) (v : CompactMatrixTest ι) :
    ‖compactTransportOp (compactFiniteMultiplier r hr) v‖ ≤ (Fintype.card ι : ℝ)^2*A*‖v‖ := by
  obtain ⟨f, rfl⟩ := (compactMatrixTestEquiv ι).surjective v
  let q (i j : ι) := smoothScalarSchwartzProduct (r i j) (hr i j) (f.val j) (f.property j)
  have hL (i j : ι) : (((q i j).memLp 2 volume).toLp (q i j)) = (q i j).toLp 2 volume := rfl
  have hAt (i j : ι) : ‖(q i j).toLp 2 volume‖ ≤ A*matrixSchwartzL2Norm f.val := by
    let f' : CompactSchwartzComponents Unit := ⟨fun _ => f.val j, fun _ => f.property j⟩
    have h := compactScalarMultiplier_norm_le (r i j) (hr i j) A hA (hSup i j) (compactMatrixTestEquiv Unit f')
    rw [compactTransportOp_apply, compactMatrixTestEquiv_norm, compactMatrixTestEquiv_norm] at h
    have h1 : matrixSchwartzL2Norm f'.val = ‖(f.val j).toLp 2 volume‖ := by
      rw [matrixSchwartzL2Norm, PiLp.norm_eq_of_L2, Fintype.sum_unique]
      exact Real.sqrt_sq (norm_nonneg _)
    have h2 : matrixSchwartzL2Norm (compactScalarMultiplier (r i j) (hr i j) f').val =
        ‖(q i j).toLp 2 volume‖ := by
      rw [matrixSchwartzL2Norm, PiLp.norm_eq_of_L2, Fintype.sum_unique]
      exact Real.sqrt_sq (norm_nonneg _)
    rw [h1, h2] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun k => (f.val k).toLp 2 volume)) j) hA)
  rw [compactTransportOp_apply, compactMatrixTestEquiv_norm, compactMatrixTestEquiv_norm]
  have h := matrixSchwartzL2Norm_le_of_entry_bounds (compactFiniteMultiplier r hr f).val
    (fun i j x => q i j x) (compactFiniteMultiplier_apply r hr f)
    (fun i j => (q i j).memLp 2 volume) (fun _ _ => A) (matrixSchwartzL2Norm f.val)
    (fun i j => by rw [hL]; exact hAt i j)
  have hCard : (∑ _i : ι, ∑ _j : ι, A) = (Fintype.card ι : ℝ)^2*A := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hCard] at h
  exact h

end Burnett.Analysis.CarlesonEmbedding
