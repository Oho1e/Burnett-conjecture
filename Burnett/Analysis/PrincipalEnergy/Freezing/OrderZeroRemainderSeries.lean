import Burnett.Analysis.PrincipalEnergy.Freezing.SymmetrizationOrderZero
import Burnett.Analysis.PrincipalEnergy.Freezing.ModeFourierMoment
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 2150000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators ContDiff ENNReal Burnett.A03

private theorem fourier_moment_nonneg (r : ℕ) (f : E → ℂ) : 0 ≤ patchFourierMoment r f :=
  integral_nonneg fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)

/-- Value and first weak derivatives of the actual symmetrization remainders
converge in the physical L³ space. Only the input's first-order L³ norms
enter the estimate. -/
theorem exists_summable_symmetrization_remainder_jets :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {I : Type} (f : I → Fin 2 → SchwartzMap E ℂ) (b : I → Fin 2 → E → ℝ)
        (D : I → Fin 2 → ℝ),
        (∀ k j, ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0}) →
        (∀ k j (t : ℝ), 0 < t → ∀ ξ, b k j (t • ξ) = t * b k j ξ) →
        (∀ k j, 0 ≤ D k j) →
        (∀ k j n, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (b k j) ξ‖ ≤ D k j) →
        let W (r : ℕ) (k : I) := ∑ j : Fin 2, D k j * patchFourierMoment r (f k j)
        Summable (W 1) → Summable (W 2) →
        ∀ u : SchwartzMap E ℂ,
          let p := ENNReal.ofReal 3
          let Y := (eLpNorm (u : E → ℂ) p volume).toReal
          let Yj (a : Index) := (eLpNorm (energyPartial a u : E → ℂ) p volume).toReal
          let R (k : I) (j : Fin 2) := separatedSkewLeftRemainder (f k j) (b k j) u
          let dR (a : Index) (k : I) (j : Fin 2) (x : E) :=
            fderiv ℝ (R k j) x (EuclideanSpace.single a 1)
          ∃ (value : I → Fin 2 → PatchLp3) (coordinate : Index → I → Fin 2 → PatchLp3),
            (∀ k j, (value k j : E → ℂ) =ᵐ[volume] R k j) ∧
            (∀ a k j, (coordinate a k j : E → ℂ) =ᵐ[volume] dR a k j) ∧
            let v (k : I) := ∑ j : Fin 2, value k j
            let d (a : Index) (k : I) := ∑ j : Fin 2, coordinate a k j
            let V := ∑' k, v k
            let T (a : Index) := ∑' k, d a k
            HasSum v V ∧ ‖V‖ ≤ K * Y * (∑' k, W 1 k) ∧
            ∀ a : Index, HasSum (d a) (T a) ∧ HasWeakCoordinateDerivative3 V (T a) a ∧
              ‖T a‖ ≤ K * Yj a * (∑' k, W 1 k) + K * tau * Y * (∑' k, W 2 k) := by
  classical
  obtain ⟨K, hK, est⟩ := exists_separated_skew_left_remainder_W13_bound
  refine ⟨K, hK, ?_⟩
  intro I f b D hb hom hD jet W weightOne weightTwo u p Y Yj R dR
  let S (k : I) (j : Fin 2) := est (b k j) (hb k j) (hom k j) (D k j) (hD k j) (jet k j) (f k j) u
  let hR (k : I) (j : Fin 2) : MemLp (R k j) p volume := (S k j).1
  let hdR (a : Index) (k : I) (j : Fin 2) : MemLp (dR a k j) p volume := ((S k j).2.2 a).1
  let value (k : I) (j : Fin 2) : PatchLp3 := (hR k j).toLp _
  let coordinate (a : Index) (k : I) (j : Fin 2) : PatchLp3 := (hdR a k j).toLp _
  refine ⟨value, coordinate, (fun k j => (hR k j).coeFn_toLp),
    (fun a k j => (hdR a k j).coeFn_toLp), ?_⟩
  intro v d V T
  have coef (g : SchwartzMap E ℂ) (k : I) (j : Fin 2) :
      0 ≤ K * D k j * patchFourierFirstMoment g :=
    mul_nonneg (mul_nonneg hK (hD k j)) (fourier_moment_nonneg _ _)
  have vEst (k : I) (j : Fin 2) : ‖value k j‖ ≤ K * D k j * patchFourierMoment 1 (f k j) * Y := by
    have fin : ENNReal.ofReal (K * D k j * patchFourierFirstMoment (f k j)) *
        eLpNorm (u : E → ℂ) p volume < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (u.memLp p volume).eLpNorm_lt_top
    simpa only [value, Lp.norm_toLp, Y, ENNReal.toReal_mul, ENNReal.toReal_ofReal (coef (f k j) k j)]
      using ENNReal.toReal_mono fin.ne (S k j).2.1
  have dEst (a : Index) (k : I) (j : Fin 2) : ‖coordinate a k j‖ ≤
      K * D k j * patchFourierMoment 1 (f k j) * Yj a +
        (K * tau) * D k j * patchFourierMoment 2 (f k j) * Y := by
    let A := K * D k j * patchFourierFirstMoment (f k j)
    let B := K * D k j * patchFourierFirstMoment (energyPartial a (f k j))
    let X := eLpNorm (energyPartial a u : E → ℂ) p volume
    let U := eLpNorm (u : E → ℂ) p volume
    have finA : ENNReal.ofReal A * X < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((energyPartial a u).memLp p volume).eLpNorm_lt_top
    have finB : ENNReal.ofReal B * U < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (u.memLp p volume).eLpNorm_lt_top
    have fin := (ENNReal.add_lt_top.mpr ⟨finA, finB⟩).ne
    have raw : eLpNorm (dR a k j) p volume ≤ ENNReal.ofReal A * X + ENNReal.ofReal B * U :=
      ((S k j).2.2 a).2
    have A0 : 0 ≤ A := coef (f k j) k j
    have B0 : 0 ≤ B := coef (energyPartial a (f k j)) k j
    have bound : ‖coordinate a k j‖ ≤ A * Yj a + B * Y := by
      simpa only [coordinate, Lp.norm_toLp, ENNReal.toReal_add finA.ne finB.ne,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal A0, ENNReal.toReal_ofReal B0, X, U, Y, Yj]
        using ENNReal.toReal_mono fin raw
    refine bound.trans ?_
    have mom := patch_fourier_moment_partial 1 a (f k j)
    calc
      _ ≤ A * Yj a + (K * D k j * (tau * patchFourierMoment 2 (f k j))) * Y := by
        dsimp only [B]
        gcongr
        exact mul_nonneg hK (hD k j)
      _ = _ := by dsimp only [A, patchFourierFirstMoment]; ring
  let Vm (k : I) := K * Y * W 1 k
  let Tm (a : Index) (k : I) := K * Yj a * W 1 k + K * tau * Y * W 2 k
  have vMajor (k : I) : ‖v k‖ ≤ Vm k := by
    change ‖∑ j : Fin 2, value k j‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => vEst k j).trans_eq ?_
    simp only [Vm, W, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have dMajor (a : Index) (k : I) : ‖d a k‖ ≤ Tm a k := by
    change ‖∑ j : Fin 2, coordinate a k j‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => dEst a k j).trans_eq ?_
    simp only [Tm, W, Finset.sum_add_distrib, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => by ring) (Finset.sum_congr rfl fun j _ => by ring)
  have sv : Summable Vm := weightOne.mul_left _
  have sd (a : Index) : Summable (Tm a) := (weightOne.mul_left _).add (weightTwo.mul_left _)
  have absV : Summable (fun k => ‖v k‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) vMajor sv
  have absT (a : Index) : Summable (fun k => ‖d a k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (dMajor a) (sd a)
  have sumV : HasSum v V := absV.of_norm.hasSum
  have sumT (a : Index) : HasSum (d a) (T a) := (absT a).of_norm.hasSum
  have w (a : Index) (k : I) : HasWeakCoordinateDerivative3 (v k) (d a k) a :=
    weak_coordinate_derivative_finset_sum Finset.univ (value k) (coordinate a k) a
      (fun j _ => separated_skew_left_remainder_weak_coordinate (f k j) (b k j) (hb k j) (hom k j)
        u a (hR k j) (hdR a k j))
  refine ⟨sumV, ?_, fun a => ⟨sumT a, weak_coordinate_derivative_hasSum v (d a) V (T a) a
    sumV (sumT a) (w a), ?_⟩⟩
  · exact (norm_tsum_le_tsum_norm absV).trans ((absV.tsum_le_tsum vMajor sv).trans_eq
      (tsum_mul_left))
  · refine (norm_tsum_le_tsum_norm (absT a)).trans (((absT a).tsum_le_tsum (dMajor a) (sd a)).trans_eq ?_)
    change (∑' k, (K * Yj a * W 1 k + K * tau * Y * W 2 k)) = _
    rw [(weightOne.mul_left (K * Yj a)).tsum_add (weightTwo.mul_left (K * tau * Y)),
      tsum_mul_left, tsum_mul_left]

end Burnett.A03
