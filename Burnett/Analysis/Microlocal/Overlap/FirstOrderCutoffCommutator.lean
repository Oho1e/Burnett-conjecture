import Burnett.Analysis.Microlocal.BesselLocalization

/-! The differential row commutator with the inner cutoff is a genuine
zeroth-order row. Its negative energy tends to zero on the localized inputs. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Burnett.Microlocal.BesselLocalization

open MeasureTheory Filter Burnett.Fourier Burnett.Analysis.HminusWeightedDual
open Burnett.X02.SobolevTestJet Burnett.Analysis.LocalHminusFourier
open scoped ContDiff Topology BigOperators

private theorem coeffMul_apply (a : D) (u : SchwartzMap Space ℂ) (x : Space) :
    coeffMul a u x = ((a : Space → ℝ) x : ℂ) * u x := rfl

private def cutoffProduct (a χ : D) : D :=
  ⟨fun x => (a : Space → ℝ) x * (χ : Space → ℝ) x,
    (test_smooth a).mul (test_smooth χ), (test_compactSupport a).mul_right⟩

private theorem coeffMul_comp (a χ : D) (u : SchwartzMap Space ℂ) :
    coeffMul a (coeffMul χ u) = coeffMul (cutoffProduct a χ) u := by
  ext x
  simp only [coeffMul_apply, cutoffProduct, Complex.ofReal_mul, mul_assoc]

private theorem coeffMul_comm (a χ : D) (u : SchwartzMap Space ℂ) :
    coeffMul a (coeffMul χ u) = coeffMul χ (coeffMul a u) := by
  ext x
  simp only [coeffMul_apply, mul_left_comm]

private def coeffMulAddHom (a : D) : SchwartzMap Space ℂ →+ SchwartzMap Space ℂ where
  toFun := coeffMul a
  map_zero' := SchwartzMap.ext fun x => by
    simp only [coeffMul_apply, SchwartzMap.zero_apply, mul_zero]
  map_add' u v := SchwartzMap.ext fun x => by
    simp only [coeffMul_apply, SchwartzMap.add_apply, mul_add]

variable {ι κ η : Type*} [Fintype ι] [Fintype η]

theorem firstOrderRow_cutoff_sub (a : ι → D) (v : ι → Space) (i : ι → κ)
    (b : η → D) (j : η → κ) (χ : D) (u : κ → SchwartzMap Space ℂ) :
    firstOrderRow a v i b j (fun k => coeffMul χ (u k)) -
      coeffMul χ (firstOrderRow a v i b j u) =
      ∑ h, coeffMul (a h) (coeffMul (coefficientPDeriv χ (v h)) (u (i h))) := by
  let p h := coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (u (i h)))
  let l h := coeffMul (b h) (u (j h))
  let e h := coeffMul (a h) (coeffMul (coefficientPDeriv χ (v h)) (u (i h)))
  let m := coeffMulAddHom χ
  have hP (h : ι) : coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (coeffMul χ (u (i h)))) =
      m (p h) + e h := by
    rw [pderiv_coeffMul]
    change coeffMulAddHom (a h) (_ + _) = _
    rw [map_add]
    change coeffMul (a h) (coeffMul χ _) + coeffMul (a h) (coeffMul (coefficientPDeriv χ (v h)) _) = _
    rw [coeffMul_comm (a h) χ]
    rfl
  have hL (h : η) : coeffMul (b h) (coeffMul χ (u (j h))) = m (l h) := coeffMul_comm _ _ _
  change ((∑ h, coeffMul (a h) (SchwartzMap.pderivCLM ℂ (v h) (coeffMul χ (u (i h))))) +
    ∑ h, coeffMul (b h) (coeffMul χ (u (j h)))) - m ((∑ h, p h) + ∑ h, l h) = ∑ h, e h
  simp only [hP, hL, map_add, map_sum, Finset.sum_add_distrib]
  abel

/-- Moving the inner cutoff through a first-order row has strongly zero
error after applying the actual inverse Bessel operator. -/
theorem bessel_firstOrderRow_cutoff_sub_tendsto_zero (a : ι → D) (v : ι → Space) (i : ι → κ)
    (b : η → D) (j : η → κ) (χ : D)
    (f : ℕ → κ → Space → ℝ) (hs : ∀ n k, ContDiff ℝ ∞ (f n k))
    (hf : ∀ n k, MemLp (f n k) 2 (volume : Measure Space))
    (θ : D) (hθ : ∀ n k x, f n k x ≠ 0 → (θ : Space → ℝ) x = 1)
    (B : ℝ) (hB : ∀ n k, ‖(hf n k).toLp (f n k)‖ ≤ B)
    (hw : ∀ k (ψ : D), Tendsto (fun n => ∫ x, f n k x * (ψ : Space → ℝ) x) atTop (𝓝 0)) :
    let u n k := sourceSchwartz (hs n k) θ (hθ n k)
    Tendsto (fun n => fourierMultiplier besselSymbol
      ((firstOrderRow a v i b j (fun k => coeffMul χ (u n k)) -
        coeffMul χ (firstOrderRow a v i b j (u n))).toLp 2 volume)) atTop (𝓝 0) := by
  intro u
  let L := (fourierMultiplier besselSymbol).comp (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space))
  let d h := cutoffProduct (a h) (coefficientPDeriv χ (v h))
  have hE (h : ι) : Tendsto (fun n => L (coeffMul (d h) (u n (i h)))) atTop (𝓝 0) := by
    simp only [L, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, coeffMul_toLp]
    exact vanishingFrequency_after_coefficient_tendsto_zero besselSymbol bessel_small_outside_ball
      (d h) (fun n => f n (i h)) (fun n => hs n (i h)) (fun n => hf n (i h))
      θ (fun n => hθ n (i h)) B (fun n => hB n (i h)) (hw (i h))
  change Tendsto (fun n => L (firstOrderRow a v i b j (fun k => coeffMul χ (u n k)) -
    coeffMul χ (firstOrderRow a v i b j (u n)))) atTop (𝓝 0)
  simp_rw [firstOrderRow_cutoff_sub, map_sum, coeffMul_comp]
  simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun h _ => hE h)

end Burnett.Microlocal.BesselLocalization
