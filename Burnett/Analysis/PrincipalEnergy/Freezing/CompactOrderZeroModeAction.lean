import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderZeroModes
import Burnett.Analysis.PrincipalEnergy.Freezing.FourierOrderZeroModeBounds

set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform

/-- Series of the actual slanted actions of the fixed physical cube modes. -/
def compactBaseModeQuantization (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hS : tsupport ρ ⊆ ball (0 : E) P) (σ : ℝ) (a : E → E → ℝ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∑' i : (Index → ℤ) × Fin 2,
    separatedRadianQuantization σ (compactBaseRealMode P a i.1 i.2)
      (compactBaseSpatialMode P ρ hρ hS i.1 i.2) u x

/-- The complete real compact-base order-zero mode action has one fixed
value and first-jet constant, for all input fields and all slants. -/
theorem exists_compact_base_order_zero_mode_action_W13 (P R : ℝ) (hP : 0 < P) (hRP : R ≤ P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hS : tsupport ρ ⊆ ball (0 : E) P)
    (a : E → E → ℝ)
    (support : ∀ x ξ, x ∉ closedBall (0 : E) R → a x ξ = 0)
    (ha : CompactBaseFrequencyJets (fun x q => (a x q : ℂ)) univ)
    (M : ℝ) (M0 : 0 ≤ M) (hM : CompactBaseOrderZeroBudget a M) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ σ : ℝ, SchwartzOrderZeroJetBound (compactBaseModeQuantization P ρ hρ hS σ a) A A := by
  let I := (Index → ℤ) × Fin 2
  let f (i : I) := compactBaseSpatialMode P ρ hρ hS i.1 i.2
  let b (i : I) := compactBaseRealMode P a i.1 i.2
  let C := max 1 ((3 / spatialModeRate P)^8) * M
  let D (i : I) := C / spatialLatticeWeight i.1 ^ 8
  have C0 : 0 ≤ C := mul_nonneg (zero_le_one.trans (le_max_left _ _)) M0
  have D0 (i : I) : 0 ≤ D i := by
    apply div_nonneg C0 (pow_nonneg ?_ _)
    unfold spatialLatticeWeight
    positivity
  have B (i : I) : ContDiff ℝ ∞ (b i) ∧ MikhlinOrderZeroBudget (b i) (D i) :=
    compact_base_order_zero_real_mode_budget P R hP hRP a support ha M M0 hM i.1 i.2
  have U (i : I) (ξ : E) : ‖b i ξ‖ ≤ D i :=
    mikhlin_order_zero_budget_value_bound (b i) (B i).1 (D i) (B i).2 ξ
  have Sm (r : ℕ) (hr : r ≤ 2) : Summable (fun i : I => D i * patchFourierMoment r (f i)) := by
    obtain ⟨K, _, H⟩ := exists_summable_localized_mode_fourier_moments 8 r (by decide) hr P hP ρ hρ hS
    have hD (k : Index → ℤ) (j : Fin 2) :
        0 ≤ D (k,j) ∧ D (k,j) ≤ C * 1 / spatialLatticeWeight k ^ 8 :=
      ⟨D0 (k,j), by simp [D]⟩
    obtain ⟨Hsum, _⟩ := H 0 1 zero_lt_one C C0 (fun k j => D (k,j)) hD
    apply (summable_prod_of_nonneg (fun i : I => mul_nonneg (D0 i) (patch_moment_nonneg _ _))).mpr
    refine ⟨fun _ => hasSum_fintype _ |>.summable, ?_⟩
    simpa only [tsum_fintype, f, compactBaseSpatialMode] using Hsum
  obtain ⟨K, K0, old⟩ := exists_radian_mikhlin_order_zero_separated_W13
  let L := max 1 K
  have L1 : 1 ≤ L := le_max_left _ _
  have L0 : 0 ≤ L := zero_le_one.trans L1
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  let q0 (i : I) := D i * patchFourierMoment 0 (f i)
  let q1 (i : I) := D i * tau * patchFourierMoment 1 (f i)
  have q00 (i : I) : 0 ≤ q0 i := mul_nonneg (D0 i) (patch_moment_nonneg _ _)
  have q10 (i : I) : 0 ≤ q1 i := mul_nonneg (mul_nonneg (D0 i) τ0) (patch_moment_nonneg _ _)
  let w (i : I) := L * (q0 i + q1 i)
  have q₀s : Summable q0 := Sm 0 (by decide)
  have q₁s : Summable q1 := by
    have s := (Sm 1 (by decide)).mul_left tau
    convert s using 1
    funext i
    dsimp only [q1]
    ring
  have ws : Summable w := (q₀s.add q₁s).mul_left L
  have w0 (i : I) : 0 ≤ w i := mul_nonneg L0 (add_nonneg (q00 i) (q10 i))
  have q0w (i : I) : q0 i ≤ w i :=
    (le_add_of_nonneg_right (q10 i)).trans (le_mul_of_one_le_left (add_nonneg (q00 i) (q10 i)) L1)
  have q1w (i : I) : q1 i ≤ w i :=
    (le_add_of_nonneg_left (q00 i)).trans (le_mul_of_one_le_left (add_nonneg (q00 i) (q10 i)) L1)
  have k0w (i : I) : K * D i * patchFourierMoment 0 (f i) ≤ w i := by
    calc
      _ = K * q0 i := by dsimp only [q0]; ring
      _ ≤ L * (q0 i + q1 i) :=
        mul_le_mul (le_max_right _ _) (le_add_of_nonneg_right (q10 i)) (q00 i) L0
  have k1w (i : I) : K * D i * tau * patchFourierMoment 1 (f i) ≤ w i := by
    calc
      _ = K * q1 i := by dsimp only [q1]; ring
      _ ≤ L * (q0 i + q1 i) :=
        mul_le_mul (le_max_right _ _) (le_add_of_nonneg_left (q00 i)) (q10 i) L0
  refine ⟨ENNReal.ofReal (∑' i, w i), ENNReal.ofReal_lt_top, ?_⟩
  intro σ u
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (u : E → ℂ) p volume
  let X (j : Index) := eLpNorm (energyPartial j u : E → ℂ) p volume
  let G (i : I) := separatedRadianQuantization σ (b i) (f i) u
  let Z := patchFourierMoment 0 u
  let Zj (j : Index) := patchFourierMoment 0 (energyPartial j u)
  let J := Z + ∑ j : Index, Zj j
  have Z0 : 0 ≤ Z := patch_moment_nonneg _ _
  have Zj0 (j : Index) : 0 ≤ Zj j := patch_moment_nonneg _ _
  have Zle : Z ≤ J := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => Zj0 j)
  have Zjle (j : Index) : Zj j ≤ J :=
    (Finset.single_le_sum (fun k _ => Zj0 k) (Finset.mem_univ j)).trans (le_add_of_nonneg_left Z0)
  have J0 : 0 ≤ J := Z0.trans Zle
  have point (i : I) := bounded_separated_radian_action_pointwise σ (b i) (B i).1.continuous.measurable
    (D i) (D0 i) (U i) (f i) u
  have estimates (i : I) := old (b i) (B i).1 (D i) (D0 i) (B i).2 σ (f i) u
  have agr (i : I) (j : Index) (x : E) : ‖actualCoordinateJet (G i) j x‖ ≤ w i * J := by
    refine ((point i).2 j |>.2 x).trans ?_
    calc
      _ = q1 i * Z + q0 i * Zj j := by dsimp only [q0, q1, Z, Zj]; ring
      _ ≤ (q1 i + q0 i) * J := by
        rw [add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left Zle (q10 i)) (mul_le_mul_of_nonneg_left (Zjle j) (q00 i))
      _ ≤ _ := by
        rw [add_comm (q1 i)]
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (add_nonneg (q00 i) (q10 i)) L1) J0
  exact summed_order_zero_coordinate_L3 G (fun i => (estimates i).2.2.1) (fun i j => ((point i).2 j).1)
    w ws w0 J J0
    (fun i x => ((point i).1 x).trans (mul_le_mul (q0w i) Zle Z0 (w0 i))) agr
    Y (u.memLp p volume).eLpNorm_lt_top X (fun j => ((energyPartial j u).memLp p volume).eLpNorm_lt_top)
    (fun i => ⟨(estimates i).1, (estimates i).2.1.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (k0w i)) _)⟩)
    (fun i j => by
      have E := (estimates i).2.2.2 j
      refine ⟨E.1, E.2.trans ?_⟩
      rw [mul_add]
      exact add_le_add (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (k0w i)) _)
        (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (k1w i)) _))

end Burnett.A03
