import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicAmbientJetBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A06

open Metric MeasureTheory Set
open scoped BigOperators ContDiff

/-- The actual homogeneous extension of the harmonic restriction. -/
def sphereHarmonicRadialSymbol (d : ℕ) (H : sphereHarmonicSubmodule d) : RotationSpace → ℝ :=
  spherePolynomialValue H.val.val ∘ roundSphereRadialNormalize

theorem sphereHarmonicRadialSymbol_contDiffOn (d : ℕ) (H : sphereHarmonicSubmodule d) :
    ContDiffOn ℝ ∞ (sphereHarmonicRadialSymbol d H) {x : RotationSpace | x ≠ 0} := by
  intro x hx
  exact ((spherePolynomialValue_contDiff H.val.val).contDiffAt.comp x
    (roundSphereRadialNormalize_contDiffAt hx)).contDiffWithinAt

theorem sphereHarmonicRadialSymbol_smul (d : ℕ) (H : sphereHarmonicSubmodule d) (t : ℝ)
    (ht : 0 < t) (x : RotationSpace) :
    sphereHarmonicRadialSymbol d H (t • x) = sphereHarmonicRadialSymbol d H x := by
  by_cases hx : x = 0
  · simp [hx]
  · have h : roundSphereRadialNormalize (t • x) = roundSphereRadialNormalize x := by
      unfold roundSphereRadialNormalize
      rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul]
      congr 1
      field_simp [ht.ne', norm_ne_zero_iff.mpr hx]
    change spherePolynomialValue H.val.val (roundSphereRadialNormalize (t • x)) = _
    rw [h]
    rfl

private theorem radial_normalize_contDiffOn :
    ContDiffOn ℝ ∞ roundSphereRadialNormalize {x : RotationSpace | x ≠ 0} :=
  fun _ hx => (roundSphereRadialNormalize_contDiffAt hx).contDiffWithinAt

private theorem sphere_in_puncture :
    sphere (0 : RotationSpace) 1 ⊆ {x : RotationSpace | x ≠ 0} :=
  fun _ hx => ne_of_mem_sphere hx (by norm_num)

private theorem radial_normalize_fixed_jet_constants :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ n : ℕ, 1 ≤ n → n ≤ 6 →
      ∀ x ∈ sphere (0 : RotationSpace) 1, ‖iteratedFDeriv ℝ n roundSphereRadialNormalize x‖ ≤ D^n := by
  let U : Set RotationSpace := {x | x ≠ 0}
  have ho : IsOpen U := isOpen_ne
  have bh (n : Fin 7) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ sphere (0 : RotationSpace) 1,
      ‖iteratedFDeriv ℝ n.val roundSphereRadialNormalize x‖ ≤ M := by
    have h : ContinuousOn (iteratedFDeriv ℝ n.val roundSphereRadialNormalize) U := by
      have h' := radial_normalize_contDiffOn.continuousOn_iteratedFDerivWithin
        (m := n.val) (WithTop.coe_le_coe.mpr (le_top : (n.val : ℕ∞) ≤ ⊤)) ho.uniqueDiffOn
      exact h'.congr (fun _ hx => (iteratedFDerivWithin_of_isOpen n.val ho hx).symm)
    obtain ⟨M,hM⟩ := (isCompact_sphere (0 : RotationSpace) 1).exists_bound_of_continuousOn
      (h.mono sphere_in_puncture)
    exact ⟨max 0 M, le_max_left _ _, fun x hx => (hM x hx).trans (le_max_right _ _)⟩
  choose M hM hB using bh
  let D := 1 + ∑ i : Fin 7, M i
  have hm₀ : 0 ≤ ∑ i : Fin 7, M i := Finset.sum_nonneg (fun i _ => hM i)
  have hD : 1 ≤ D := le_add_of_nonneg_right hm₀
  refine ⟨D,hD,fun n hn hn₆ x hx => ?_⟩
  let i : Fin 7 := ⟨n,by omega⟩
  have hm := Finset.single_le_sum (f := M) (fun i _ => hM i) (Finset.mem_univ i)
  have hl : M i ≤ D := by dsimp [D]; linarith
  have hp : D ≤ D^n := by
    simpa only [pow_one] using (pow_le_pow_right₀ hD hn)
  exact (hB i x hx).trans (hl.trans hp)

/-- The exact order-zero symbol for a spherical harmonic has all ambient jets
required by the four-dimensional Mikhlin theorem, with a single degree factor. -/
theorem exists_sphereHarmonicRadialSymbol_mikhlin_jets :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (H : sphereHarmonicSubmodule d),
      ∀ n : ℕ, n ≤ 6 → ∀ x ∈ sphere (0 : RotationSpace) 1,
      ‖iteratedFDeriv ℝ n (sphereHarmonicRadialSymbol d H) x‖ ≤
        C * ((d : ℝ) + 1)^7 * ‖sphereHarmonicToLp d H‖ := by
  obtain ⟨A,B,hA,hB,hpoly⟩ := exists_sphereHarmonic_ambient_jet_bound
  obtain ⟨D,hD,hnorm⟩ := radial_normalize_fixed_jet_constants
  refine ⟨(720 : ℝ) * A * B^6 * D^6, by positivity, ?_⟩
  intro d H n hn x hx
  let U : Set RotationSpace := {x | x ≠ 0}
  have ho : IsOpen U := isOpen_ne
  have hxU : x ∈ U := sphere_in_puncture hx
  let f := spherePolynomialValue H.val.val
  let u : RoundSphere3 := ⟨roundSphereRadialNormalize x,
    mem_sphere_zero_iff_norm.mpr (roundSphereRadialNormalize_norm hxU)⟩
  let C := A * B^6 * ((d : ℝ) + 1)^7 * ‖sphereHarmonicToLp d H‖
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i f univ (roundSphereRadialNormalize x)‖ ≤ C := by
    rw [iteratedFDerivWithin_univ]
    have hBi := pow_le_pow_right₀ hB (hi.trans hn)
    have hd : 1 ≤ (d : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg d)
    have hdi := pow_le_pow_right₀ hd (show i+1 ≤ 7 by omega)
    exact (hpoly i d H u).trans (by
      dsimp [C]
      gcongr)
  have hD' (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i roundSphereRadialNormalize U x‖ ≤ D^i := by
    rw [iteratedFDerivWithin_of_isOpen i ho hxU]
    exact hnorm i hi (hin.trans hn) x hx
  have hmain := norm_iteratedFDerivWithin_comp_le
    ((spherePolynomialValue_contDiff H.val.val).contDiffOn (s := (univ : Set RotationSpace)))
    radial_normalize_contDiffOn (WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))
    uniqueDiffOn_univ ho.uniqueDiffOn (mapsTo_univ _ _) hxU hC hD'
  rw [iteratedFDerivWithin_of_isOpen n ho hxU] at hmain
  calc
    _ ≤ (n.factorial : ℝ) * C * D^n := hmain
    _ ≤ (720 : ℝ) * C * D^6 := by
      have hpow := pow_le_pow_right₀ hD hn
      have hfac : (n.factorial : ℝ) ≤ 720 := by
        exact_mod_cast (show n.factorial ≤ 720 from (Nat.factorial_le hn).trans (by decide))
      gcongr
    _ = _ := by dsimp [C]; ring

end Burnett.A06
