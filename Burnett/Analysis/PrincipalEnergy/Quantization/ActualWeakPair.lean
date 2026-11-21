import Burnett.Analysis.PrincipalEnergy.Quantization.FormalCommutatorAdjoint
import Burnett.Analysis.PrincipalEnergy.Commutator.LargeBallWeakBound

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse Burnett.Analysis.SymmetricEnergy
open scoped ComplexConjugate InnerProductSpace

private theorem integral_pair_eq_inner {u v : E → ℂ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    (∫ x, conj (u x)*v x) = ⟪hu.toLp u,hv.toLp v⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp,hv.coeFn_toLp] with x hx hy
  simp [hx,hy,mul_comm]

private theorem action_pair_integrable {a : E → E → ℂ} (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (Function.uncurry a)) (u v : SchwartzMap E ℂ) :
    Integrable (fun x => conj (u x)*firstOrderAction a v x) :=
  (firstOrderAction_integrable_of_compactBase hBase hCont v).bdd_mul
    u.continuous.aestronglyMeasurable.star
    ⟨SchwartzMap.seminorm ℝ 0 0 u, fun x => by rw [Complex.norm_conj]; exact SchwartzMap.norm_le_seminorm ℝ u x⟩

theorem exists_actualCoefficientCommutator_weakPair_bound {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (hSym : FirstOrderFormalSymmetry a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r f g : SchwartzMap E ℂ) (z : ℂ), conj z = z →
      (∀ x, conj (r x) = r x) → ∀ Q : ℝ, 0 ≤ Q →
      ‖(scalarSchwartzProduct r f-z • f).toLp 2 volume‖ ≤ Q*‖f.toLp 2 volume‖ →
      ‖(scalarSchwartzProduct r g-z • g).toLp 2 volume‖ ≤ Q*‖g.toLp 2 volume‖ →
      ‖∫ x, conj (g x)*actualCoefficientCommutator a r f x‖ ≤
        K*Q*(coordinateH1 f*‖g.toLp 2 volume‖+‖f.toLp 2 volume‖*coordinateH1 g) := by
  obtain ⟨K,hK,hMap⟩ := exists_compactBase_firstOrderAction_h1_to_l2 hBase hCont
  refine ⟨K,hK,?_⟩
  intro r f g z hz hr Q hQ hf hg
  let cf := scalarSchwartzProduct r f-z • f
  let cg := scalarSchwartzProduct r g-z • g
  let B (u : SchwartzMap E ℂ) (x : E) := firstOrderAction a u x
  have hX (u : SchwartzMap E ℂ) (x : E) :
      r x*B u x-B (scalarSchwartzProduct r u) x =
        (r x-z)*B u x-B (scalarSchwartzProduct r u-z • u) x := by
    unfold B
    rw [firstOrderAction_sub_smul a ha x (scalarSchwartzProduct r u) u z]
    ring
  have hPoint (x : E) : conj (g x)*actualCoefficientCommutator a r f x =
      conj (cg x)*B f x-conj (g x)*B cf x := by
    change conj (g x)*(r x*B f x-B (scalarSchwartzProduct r f) x) = _
    rw [hX f x]
    simp only [cg,cf,SchwartzMap.sub_apply,SchwartzMap.smul_apply,scalarSchwartzProduct_apply,smul_eq_mul,
      map_sub,map_mul,hr,hz]
    ring
  have hEq : (∫ x, conj (g x)*actualCoefficientCommutator a r f x) =
      (∫ x, conj (cg x)*B f x) - (∫ x, conj (B g x)*cf x) := by
    simp_rw [hPoint]
    rw [integral_sub (action_pair_integrable hBase hCont cg f)
      (action_pair_integrable hBase hCont g cf)]
    change _ - (∫ x, conj (g x)*firstOrderAction a cf x) = _
    rw [hSym g cf]
  obtain ⟨hBf,hEf⟩ := hMap f
  obtain ⟨hBg,hEg⟩ := hMap g
  have hEnergy (u : SchwartzMap E ℂ) : 0 ≤ coordinateH1 u := Real.sqrt_nonneg _
  have hNorm (u : SchwartzMap E ℂ) (h : MemLp (B u) 2 volume)
      (hB : ‖h.toLp (B u)‖^2 ≤ K^2*schwartzH1Energy u) :
      ‖h.toLp (B u)‖ ≤ K*coordinateH1 u := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (hEnergy u))).mp
    rw [mul_pow,show coordinateH1 u ^ 2 = schwartzH1Energy u from
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
    exact hB
  rw [hEq,integral_pair_eq_inner (cg.memLp 2 volume) hBf,integral_pair_eq_inner hBg (cf.memLp 2 volume)]
  have hF : ‖⟪(cg.memLp 2 volume).toLp cg,hBf.toLp (B f)⟫_ℂ‖ ≤
      (Q*‖g.toLp 2 volume‖)*(K*coordinateH1 f) := by
    exact (norm_inner_le_norm _ _).trans (mul_le_mul hg (hNorm f hBf hEf) (norm_nonneg _) (by positivity))
  have hG : ‖⟪hBg.toLp (B g),(cf.memLp 2 volume).toLp cf⟫_ℂ‖ ≤
      (K*coordinateH1 g)*(Q*‖f.toLp 2 volume‖) := by
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (hNorm g hBg hEg) hf (norm_nonneg _) (mul_nonneg hK (hEnergy g)))
  exact (norm_sub_le _ _).trans ((add_le_add hF hG).trans_eq (by ring))

end Burnett.Analysis.FirstOrderDyadic
