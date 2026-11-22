import Burnett.Analysis.AngularCaps.CapAngularCube
import Burnett.Analysis.AngularCaps.CapAngularL2
import Burnett.Analysis.AngularCaps.CapMultiplierLp
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Burnett.Analysis.Fourier.SharpProjection

set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Burnett.Fourier Burnett.Analysis.ProjectiveNullCaps

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private def angularCubeConstant (A C q : ℝ) : ℝ :=
  24 * (A + C^q/(q-3))

private theorem angularCubeConstant_nonneg {A C q : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 3 < q) :
    0 ≤ angularCubeConstant A C q :=
  mul_nonneg (by norm_num) (add_nonneg hA (div_nonneg (Real.rpow_nonneg hC q) (sub_pos.mpr hq).le))

private theorem counting_scale_balance {N q : ℝ} (hN : 0 < N) (hq : 3 < q) :
    N * (N^(1/(q-2)))^(3-q) = N^(1/(q-2)) := by
  calc
    _ = N^(1 + (1/(q-2))*(3-q)) := by
      rw [Real.rpow_add hN,Real.rpow_one,Real.rpow_mul hN.le]
    _ = _ := by
      congr 1
      have hq₂ : q - 2 ≠ 0 := by linarith
      field_simp [hq₂]
      ring

private theorem angular_L3_of_compatible_endpoints {ι : Type*} [Fintype ι]
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 3 < q) {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (T : ι → ComplexLp 2 →L[ℂ] ComplexLp 2)
    (U : ι → ComplexLp (ENNReal.ofReal q) →L[ℂ] ComplexLp (ENNReal.ofReal q))
    (P : ι → ComplexLp (ENNReal.ofReal 3) →L[ℂ] ComplexLp (ENNReal.ofReal 3))
    (hTU : ∀ (i : ι) (f : Space → ℂ) (f₂ : MemLp f 2 volume) (fq : MemLp f (ENNReal.ofReal q) volume),
      (U i (fq.toLp f) : Space → ℂ) =ᵐ[volume] (T i (f₂.toLp f) : Space → ℂ))
    (hPT : ∀ (i : ι) (f : SchwartzMap Space ℂ),
      (P i (f.toLp (ENNReal.ofReal 3) volume) : Space → ℂ) =ᵐ[volume]
        (T i (f.toLp 2 volume) : Space → ℂ))
    (sqBound : ∀ f, (∑ i, ‖T i f‖^2) ≤ A * ‖f‖^2)
    (qBound : ∀ i f, ‖U i f‖ ≤ C * ‖f‖)
    (v : ComplexLp (ENNReal.ofReal 3)) :
    (∑ i, ‖P i v‖^3)^(1/3 : ℝ) ≤
      (angularCubeConstant A C q)^(1/3 : ℝ) * (Fintype.card ι : ℝ)^(1/(3*(q-2))) * ‖v‖ := by
  classical
  let N : ℝ := Fintype.card ι
  have hN₀ : 0 ≤ N := Nat.cast_nonneg _
  have hA₃ := angularCubeConstant_nonneg hA hC hq
  let k := N^(1/(q-2))
  have hk₀ : 0 ≤ k := Real.rpow_nonneg hN₀ _
  by_cases eN : N = 0
  · have card_zero : Fintype.card ι = 0 := by
      change (Fintype.card ι : ℝ) = 0 at eN
      exact_mod_cast eN
    letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp card_zero
    have rt : 0 < (1/3:ℝ) := by norm_num
    simp only [Finset.univ_eq_empty,Finset.sum_empty,Real.zero_rpow rt.ne']
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hA₃ _) (Real.rpow_nonneg hN₀ _)) (norm_nonneg _)
  have hN : 0 < N := lt_of_le_of_ne hN₀ (Ne.symm eN)
  have hk : 0 < k := Real.rpow_pos_of_pos hN _
  have den : 0 < q - 3 := sub_pos.mpr hq
  have q₀ : 0 < q := by linarith
  have hB : 0 ≤ C^q*N := mul_nonneg (Real.rpow_nonneg hC q) hN₀
  have summed_q (u : ComplexLp (ENNReal.ofReal q)) : (∑ i, ‖U i u‖^q) ≤ (C^q*N)*‖u‖^q := by
    calc
      _ ≤ ∑ _ : ι, (C*‖u‖)^q := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.rpow_le_rpow (norm_nonneg _) (qBound i u) q₀.le
      _ = _ := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Real.mul_rpow hC (norm_nonneg u)]
        change N*(C^q*‖u‖^q) = _
        ring
  have balance : N*k^(3-q) = k := counting_scale_balance hN hq
  have kq : 0 ≤ k^(3-q)/(q-3) := div_nonneg (Real.rpow_nonneg hk₀ _) den.le
  have coefficient :
      24 * (ENNReal.ofReal A * ENNReal.ofReal k +
        ENNReal.ofReal (C^q*N) * ENNReal.ofReal (k^(3-q)/(q-3))) =
        ENNReal.ofReal (angularCubeConstant A C q*k) := by
    rw [← ENNReal.ofReal_mul hA,← ENNReal.ofReal_mul hB,
      ← ENNReal.ofReal_add (mul_nonneg hA hk₀) (mul_nonneg hB kq)]
    have e : 24 = ENNReal.ofReal (24:ℝ) := by norm_num
    rw [e,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 24)]
    congr 1
    unfold angularCubeConstant
    calc
      _ = 24 * (A*k + C^q*(N*k^(3-q))/(q-3)) := by ring
      _ = _ := by rw [balance]; ring
  let sumCube (u : ComplexLp (ENNReal.ofReal 3)) := ∑ i, ‖P i u‖^3
  have sum_nonneg (u : ComplexLp (ENNReal.ofReal 3)) : 0 ≤ sumCube u :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg (P i u)) _)
  have sz : ENNReal.ofReal (3 : ℝ) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)
  have cube_norm (u : ComplexLp (ENNReal.ofReal 3)) :
      (∫⁻ x : Space, ‖u x‖ₑ^(3:ℕ)) = ENNReal.ofReal (‖u‖^3) := by
    have ep : (ENNReal.ofReal (3:ℝ)).toReal = 3 := by norm_num
    simpa only [ep,ENNReal.rpow_ofNat,Real.rpow_ofNat] using
      lp_moment_eq_norm_rpow sz ENNReal.ofReal_ne_top u
  have cube_bound : ∀ u : ComplexLp (ENNReal.ofReal 3),
      sumCube u ≤ angularCubeConstant A C q*k*‖u‖^3 := by
    intro u
    have dense := Burnett.A02.FrequencySplit.CMBilinearDual.schwartz_toLp_denseRange
      (V := Space) (ENNReal.ofReal (3 : ℝ)) ENNReal.ofReal_ne_top
    apply dense.induction_on
      (p := fun u => sumCube u ≤ angularCubeConstant A C q*k*‖u‖^3) u
    · apply isClosed_le
      · exact continuous_finset_sum _ (fun i _ => (P i).continuous.norm.pow 3)
      · exact continuous_const.mul (continuous_norm.pow 3)
    · intro f
      let u := f.toLp (ENNReal.ofReal (3:ℝ)) volume
      have h := cap_cube_moment_of_endpoints hq T U hTU hA hB sqBound summed_q f f.continuous.measurable
        (f.memLp 2 volume) (f.memLp (ENNReal.ofReal q) volume) hk
      have out (i : ι) :
          (∫⁻ x : Space, ‖T i (f.toLp 2 volume) x‖ₑ^(3:ℕ)) =
            ENNReal.ofReal (‖P i u‖^3) := by
        rw [← cube_norm]
        apply lintegral_congr_ae
        filter_upwards [(hPT i f).symm] with x hx
        rw [hx]
      have inCube : (∫⁻ x : Space, ‖f x‖ₑ^(3:ℕ)) = ENNReal.ofReal (‖u‖^3) := by
        rw [← cube_norm]
        apply lintegral_congr_ae
        filter_upwards [(f.coeFn_toLp (ENNReal.ofReal (3:ℝ)) volume).symm] with x hx
        rw [hx]
      change (∑ i, ∫⁻ x : Space, ‖T i (f.toLp 2 volume) x‖ₑ^(3:ℕ)) ≤ _ at h
      simp_rw [out,inCube,coefficient,← ENNReal.ofReal_mul (mul_nonneg hA₃ hk₀)] at h
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (norm_nonneg (P i u)) 3)] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hroot := Real.rpow_le_rpow (sum_nonneg v) (cube_bound v) (by norm_num : (0:ℝ) ≤ 1/3)
  have cube_root_norm : (‖v‖^3:ℝ)^(1/3 : ℝ) = ‖v‖ := by
    rw [← Real.rpow_natCast_mul (norm_nonneg v) 3]
    norm_num
  have scale_root : k^(1/3 : ℝ) = N^(1/(3*(q-2))) := by
    unfold k
    rw [← Real.rpow_mul hN₀]
    congr 1
    have hq₂ : q - 2 ≠ 0 := by linarith
    field_simp [hq₂]
  rw [Real.mul_rpow (mul_nonneg hA₃ hk₀) (pow_nonneg (norm_nonneg v) 3),
    Real.mul_rpow hA₃ hk₀,cube_root_norm,scale_root] at hroot
  exact hroot

private theorem angular_L3_for_symbols {ι : Type*} [Fintype ι] {b : ι → Space → ℝ}
    {q : ℝ} [Fact (1 ≤ ENNReal.ofReal q)] (hq : 3 < q) {A C C₃ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (P : ∀ i, CapLpRealization (ENNReal.ofReal 3) (b i) C₃)
    (Q : ∀ i, CapLpRealization (ENNReal.ofReal q) (b i) C)
    (sqBound : ∀ f : ComplexLp 2, (∑ i, ‖fourierMultiplier (Q i).symbol f‖^2) ≤ A*‖f‖^2)
    (v : ComplexLp (ENNReal.ofReal 3)) :
    (∑ i, ‖(P i).action v‖^3)^(1/3 : ℝ) ≤
      (angularCubeConstant A C q)^(1/3 : ℝ)*(Fintype.card ι : ℝ)^(1/(3*(q-2)))*‖v‖ := by
  apply angular_L3_of_compatible_endpoints hq hA hC (fun i => fourierMultiplier (Q i).symbol)
    (fun i => (Q i).action) (fun i => (P i).action) (fun i => (Q i).intersection_eq) _ sqBound
      (fun i => (Q i).norm_le) v
  intro i f
  have h := (P i).intersection_eq f (f.memLp 2 volume) (f.memLp (ENNReal.ofReal (3:ℝ)) volume)
  have same := fourierMultiplier_congr_ae (P i).symbol (Q i).symbol
    (Eventually.of_forall (fun ξ => ((P i).symbol_eq ξ).trans ((Q i).symbol_eq ξ).symm))
  rw [same] at h
  exact h

/-- For both actual cap families in the locked compact Lorentz family, the
physical L³ angular sequence has the original counting factor. -/
theorem exists_uniform_actual_capMultipliers_angular_L3 {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (hND : ∀ m ∈ K, Nondegenerate m)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ D c₀ δ₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∃ C : {q : ℝ // 3 < q} → ℝ, (∀ q, 0 ≤ C q) ∧
        ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∃ S : SmoothThinConeCaps m δ (c*κ*δ^2) inner outer enlarged D,
            ∃ (P : ∀ w : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
                  (capMultiplier S.centers m δ (c*κ*δ^2) inner outer w) C₃)
              (Pplus : ∀ w : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
                  (enlargedCapMultiplier m δ (c*κ*δ^2) outer enlarged w) C₃),
              ∀ (q : {q : ℝ // 3 < q}) (f : ComplexLp (ENNReal.ofReal 3)),
                (∑ w : ↑S.centers, ‖(P w).action f‖^3)^(1/3 : ℝ) ≤
                  C q*(S.centers.card : ℝ)^(1/(3*(q.val-2)))*‖f‖ ∧
                (∑ w : ↑S.centers, ‖(Pplus w).action f‖^3)^(1/3 : ℝ) ≤
                  C q*(S.centers.card : ℝ)^(1/(3*(q.val-2)))*‖f‖ := by
  classical
  obtain ⟨D,c₀,δ₀,hD,hc₀,hδ₀,hδOne,hCoefficients⟩ :=
    exists_uniform_actual_capMultiplier_Lp hK hFrame hND hIn hIO hOE
  refine ⟨D,c₀,δ₀,hD,hc₀,hδ₀,hδOne,?_⟩
  intro κ hκ hκSmall c hc hcSmall
  obtain ⟨Cₚ,hCₚ,hCaps⟩ := hCoefficients κ hκ hκSmall c hc hcSmall
  let p₃ : {p : ℝ // 1 < p} := ⟨3, by norm_num⟩
  let exponent (q : {q : ℝ // 3 < q}) : {p : ℝ // 1 < p} :=
    ⟨q.val,lt_trans (by norm_num : (1:ℝ) < 3) q.property⟩
  let A := (81:ℝ)^4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let C (q : {q : ℝ // 3 < q}) :=
    (angularCubeConstant A (Cₚ (exponent q)) q.val)^(1/3 : ℝ)
  have hC (q : {q : ℝ // 3 < q}) : 0 ≤ C q :=
    Real.rpow_nonneg (angularCubeConstant_nonneg hA (hCₚ (exponent q)) q.property) _
  refine ⟨Cₚ p₃,hCₚ p₃,C,hC,?_⟩
  intro m hm δ hδ hδSmall
  obtain ⟨S,hS⟩ := hCaps m hm δ hδ hδSmall
  let P (w : ↑S.centers) := Classical.choice (hS w w.property p₃).1
  let Pplus (w : ↑S.centers) := Classical.choice (hS w w.property p₃).2
  refine ⟨S,P,Pplus,?_⟩
  intro q f
  letI : Fact (1 ≤ ENNReal.ofReal q.val) :=
    ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (exponent q).property.le⟩
  let Q (w : ↑S.centers) := Classical.choice (hS w w.property (exponent q)).1
  let Qplus (w : ↑S.centers) := Classical.choice (hS w w.property (exponent q)).2
  have l2 (u : ComplexLp 2) :=
    actual_capMultipliers_angular_L2 S (fun w => (Q w).symbol) (fun w => (Qplus w).symbol)
      (fun w => (Q w).symbol_eq) (fun w => (Qplus w).symbol_eq) u
  have base (u : ComplexLp 2) : (∑ w : ↑S.centers, ‖fourierMultiplier (Q w).symbol u‖^2) ≤ A*‖u‖^2 :=
    (l2 u).1.trans (mul_le_mul_of_nonneg_right (by dsimp only [A]; norm_num) (sq_nonneg _))
  have hq := hCₚ (exponent q)
  have plain := angular_L3_for_symbols q.property hA hq P Q base f
  have wide := angular_L3_for_symbols q.property hA hq Pplus Qplus (fun u => (l2 u).2) f
  exact ⟨by simpa only [C,Fintype.card_coe] using plain,by simpa only [C,Fintype.card_coe] using wide⟩

end Burnett.Analysis.CapFourier
