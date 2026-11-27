import Burnett.Analysis.PrincipalEnergy.Freezing.SummedOrderZeroJets
import Burnett.Analysis.PrincipalEnergy.Freezing.CompactKernelOrderZero

set_option autoImplicit false
set_option maxHeartbeats 1900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal

theorem schwartz_order_zero_jet_bound_add
    (Q R : SchwartzMap E ℂ → E → ℂ) (A B C D : ℝ≥0∞)
    (hQ : SchwartzOrderZeroJetBound Q A B) (hR : SchwartzOrderZeroJetBound R C D) :
    SchwartzOrderZeroJetBound (fun u => Q u + R u) (A+C) (B+D) := by
  intro u
  let p := ENNReal.ofReal 3
  obtain ⟨Qu, aQ, dQ, jQ⟩ := hQ u
  obtain ⟨Ru, aR, dR, jR⟩ := hR u
  refine ⟨Qu.add Ru, ?_, dQ.add dR, ?_⟩
  · exact (eLpNorm_add_le Qu.1 Ru.1 (by norm_num [p])).trans
      ((add_le_add aQ aR).trans_eq (add_mul _ _ _).symm)
  intro j W
  have eq : W = actualCoordinateJet (Q u) j + actualCoordinateJet (R u) j := funext fun x => by
    change fderiv ℝ (Q u + R u) x (EuclideanSpace.single j 1) = _
    rw [fderiv_add (dQ x) (dR x), ContinuousLinearMap.add_apply]
    rfl
  rw [eq]
  have q := jQ j
  have r := jR j
  refine ⟨q.1.add r.1, (eLpNorm_add_le q.1.1 r.1.1 (by norm_num [p])).trans ?_⟩
  refine (add_le_add q.2 r.2).trans_eq ?_
  simp only [add_mul]
  ring

theorem schwartz_order_zero_jet_bound_const_mul
    (Q : SchwartzMap E ℂ → E → ℂ) (A B : ℝ≥0∞) (hQ : SchwartzOrderZeroJetBound Q A B)
    (c : ℂ) : SchwartzOrderZeroJetBound (fun u => c • Q u) (‖c‖ₑ*A) (‖c‖ₑ*B) := by
  intro u
  let p := ENNReal.ofReal 3
  obtain ⟨Qu,aQ,dQ,jQ⟩ := hQ u
  refine ⟨Qu.const_smul c, ?_, dQ.const_smul c, ?_⟩
  · refine eLpNorm_const_smul_le.trans ((mul_le_mul_left' aQ _).trans_eq ?_)
    exact (mul_assoc _ _ _).symm
  intro j W
  have eq : W = c • actualCoordinateJet (Q u) j := funext fun x => by
    change fderiv ℝ (c • Q u) x (EuclideanSpace.single j 1) = _
    rw [fderiv_const_smul (dQ x), ContinuousLinearMap.smul_apply]
    rfl
  rw [eq]
  have q := jQ j
  refine ⟨q.1.const_smul c, eLpNorm_const_smul_le.trans ((mul_le_mul_left' q.2 _).trans_eq ?_)⟩
  rw [mul_add, mul_assoc, mul_assoc]

theorem schwartz_order_zero_jet_bound_sub
    (Q R : SchwartzMap E ℂ → E → ℂ) (A B C D : ℝ≥0∞)
    (hQ : SchwartzOrderZeroJetBound Q A B) (hR : SchwartzOrderZeroJetBound R C D) :
    SchwartzOrderZeroJetBound (fun u => Q u - R u) (A+C) (B+D) := by
  have neg := schwartz_order_zero_jet_bound_const_mul R C D hR (-1)
  have eq : (fun u => (-1 : ℂ) • R u) = (fun u => -R u) := by
    funext u
    rw [neg_one_smul]
  rw [eq, enorm_neg, enorm_one, one_mul, one_mul] at neg
  simpa only [sub_eq_add_neg] using schwartz_order_zero_jet_bound_add Q (fun u => -R u) A B C D hQ neg

theorem schwartz_order_zero_jet_bound_mono
    (Q : SchwartzMap E ℂ → E → ℂ) (A B C D : ℝ≥0∞)
    (hQ : SchwartzOrderZeroJetBound Q A B) (hAC : A ≤ C) (hBD : B ≤ D) :
    SchwartzOrderZeroJetBound Q C D := by
  intro u
  obtain ⟨Qu,aQ,dQ,jQ⟩ := hQ u
  refine ⟨Qu,aQ.trans (mul_le_mul_right' hAC _),dQ,?_⟩
  intro j
  exact ⟨(jQ j).1, (jQ j).2.trans (add_le_add (mul_le_mul_right' hAC _) (mul_le_mul_right' hBD _))⟩

/-- The true compact kernel bounds enter the same actual-operator estimate
with zero cost for differentiating the input. -/
theorem exists_compact_kernel_order_zero_jet_bound (K : E → E → ℂ) (R : ℝ)
    (smooth : ContDiff ℝ 1 (Function.uncurry K))
    (support : ∀ x y, x ∉ Metric.closedBall (0 : E) R ∨ y ∉ Metric.closedBall (0 : E) R → K x y = 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ SchwartzOrderZeroJetBound (compactKernelAction K) C C := by
  obtain ⟨C,Cfin,est⟩ := exists_compact_kernel_action_W13 K smooth R support
  refine ⟨C,Cfin,?_⟩
  intro u
  obtain ⟨hu,hB,d,j⟩ := est u
  exact ⟨hu,hB,d,fun q => ⟨(j q).1, (j q).2.trans (le_add_of_nonneg_left bot_le)⟩⟩

/-- The two actual cutoff placements give uniform constants from uniform
cutoff and first-derivative sup bounds. -/
theorem schwartz_order_zero_jet_bound_sandwich (θ : SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (A B P T : ℝ≥0∞)
    (hQ : SchwartzOrderZeroJetBound Q A B)
    (val : eLpNorm (θ : E → ℂ) ⊤ volume ≤ P)
    (jet : ∀ j : Index, eLpNorm (energyPartial j θ : E → ℂ) ⊤ volume ≤ T) :
    SchwartzOrderZeroJetBound (sandwichedScalarTest θ Q) (P^2*A) (2*P*T*A + P^2*B) := by
  intro u
  obtain ⟨hu,hB,d,hJ⟩ := sandwiched_order_zero_action_W13 θ Q A B hQ u
  have pow : (eLpNorm (θ : E → ℂ) ⊤ volume)^2 ≤ P^2 := pow_le_pow_left' val _
  refine ⟨hu,hB.trans (mul_le_mul_right' (mul_le_mul_right' pow A) _),d,?_⟩
  intro j
  have h := hJ j
  refine ⟨h.1, h.2.trans ?_⟩
  gcongr
  exact jet j

end Burnett.A03
