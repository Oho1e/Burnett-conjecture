import Burnett.Analysis.PrincipalEnergy.Fourier.FrequencyWeights
import Burnett.Analysis.Sobolev.Pairing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The graph-dual bound for Fourier negative energy
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.SchwartzH1Density

open Filter MeasureTheory Set Metric
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet

def baseCutoff : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩

def cutoffRadius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem one_le_cutoffRadius (n : ℕ) : 1 ≤ cutoffRadius n := by
  unfold cutoffRadius
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

def cutoff (n : ℕ) (x : Space) : ℝ := baseCutoff ((cutoffRadius n)⁻¹ • x)

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  baseCutoff.contDiff.comp (contDiff_const.smul contDiff_id)

theorem cutoff_compactSupport (n : ℕ) : HasCompactSupport (cutoff n) :=
  baseCutoff.hasCompactSupport.comp_smul (inv_ne_zero (by linarith [one_le_cutoffRadius n]))

theorem cutoff_nonneg (n : ℕ) (x : Space) : 0 ≤ cutoff n x := baseCutoff.nonneg

theorem cutoff_le_one (n : ℕ) (x : Space) : cutoff n x ≤ 1 := baseCutoff.le_one

theorem cutoff_eventually_locally_one (x : Space) :
    ∀ᶠ n in atTop, cutoff n =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 < cutoffRadius n := by linarith [one_le_cutoffRadius n]
  have hb : (cutoffRadius n)⁻¹ • x ∈ ball (0 : Space) baseCutoff.rIn := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    change (cutoffRadius n)⁻¹ * ‖x‖ < 1
    rw [← div_eq_inv_mul, div_lt_one hr]
    exact hN.trans_le (hn'.trans (by linarith [one_le_cutoffRadius n, show cutoffRadius n = (n : ℝ) + 1 by rfl]))
  have hc : ContinuousAt (fun y : Space => (cutoffRadius n)⁻¹ • y) x :=
    (continuous_id.const_smul _).continuousAt
  exact hc.tendsto.eventually (baseCutoff.eventuallyEq_one_of_mem_ball hb)

theorem cutoff_eventually_value_and_derivative (x : Space) :
    ∀ᶠ n in atTop, cutoff n x = 1 ∧ fderiv ℝ (cutoff n) x = 0 := by
  filter_upwards [cutoff_eventually_locally_one x] with n hn
  exact ⟨hn.eq_of_nhds, hn.fderiv_eq.trans (by simp)⟩

theorem exists_baseCutoff_fderiv_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : Space, ‖fderiv ℝ (baseCutoff : Space → ℝ) x‖ ≤ C := by
  let f : Space → ℝ := baseCutoff
  have hc : Continuous (fun x => ‖fderiv ℝ f x‖) :=
    ((baseCutoff.contDiff (n := ⊤)).continuous_fderiv (by simp)).norm
  obtain ⟨B, hB⟩ := baseCutoff.hasCompactSupport.bddAbove_image hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x
  change ‖fderiv ℝ f x‖ ≤ max B 0
  by_cases hx : x ∈ tsupport f
  · exact (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
    exact le_max_right _ _

theorem cutoff_directional_formula (n : ℕ) (i : Fin 4) (x : Space) :
    directional i (cutoff n) x = (cutoffRadius n)⁻¹ *
      directional i (baseCutoff : Space → ℝ) ((cutoffRadius n)⁻¹ • x) := by
  let a : ℝ := (cutoffRadius n)⁻¹
  let L := a • ContinuousLinearMap.id ℝ Space
  have hL : HasFDerivAt (fun y : Space => a • y) L x := L.hasFDerivAt
  have hb : Differentiable ℝ (baseCutoff : Space → ℝ) :=
    (baseCutoff.contDiff (n := ⊤)).differentiable (by simp)
  have hd := (hb (a • x)).hasFDerivAt.comp x hL
  change HasFDerivAt (cutoff n) ((fderiv ℝ (baseCutoff : Space → ℝ) (a • x)).comp L) x at hd
  simp [directional, hd.fderiv, L, a, smul_eq_mul]

theorem exists_cutoff_directional_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n : ℕ) (i : Fin 4) (x : Space), ‖directional i (cutoff n) x‖ ≤ C := by
  obtain ⟨C, hC, hbase⟩ := exists_baseCutoff_fderiv_bound
  refine ⟨C, hC, ?_⟩
  intro n i x
  have hr : 0 < cutoffRadius n := by linarith [one_le_cutoffRadius n]
  have hInv : (cutoffRadius n)⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr (one_le_cutoffRadius n)
  rw [cutoff_directional_formula, norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ (cutoffRadius n)⁻¹ * C := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hr.le)
      unfold directional
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      simpa [EuclideanSpace.norm_single] using hbase ((cutoffRadius n)⁻¹ • x)
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right hInv hC
    _ = C := one_mul _

def compactSchwartzTest (u : SchwartzMap Space ℝ) (n : ℕ) : D :=
  ⟨fun x => cutoff n x * u x, (cutoff_smooth n).mul (u.smooth ⊤), (cutoff_compactSupport n).mul_right⟩

theorem compactSchwartzTest_directional (u : SchwartzMap Space ℝ) (n : ℕ) (i : Fin 4) (x : Space) :
    directional i (compactSchwartzTest u n) x =
      cutoff n x * directional i u x + directional i (cutoff n) x * u x := by
  unfold directional
  change fderiv ℝ (cutoff n * (u : Space → ℝ)) x _ = _
  rw [fderiv_mul ((cutoff_smooth n).differentiable (by simp) x) u.differentiableAt]
  simp [smul_eq_mul, mul_comm]

theorem compactSchwartzTest_eventually_value_and_directionals (u : SchwartzMap Space ℝ) (x : Space) :
    ∀ᶠ n in atTop, (compactSchwartzTest u n : Space → ℝ) x = u x ∧
      ∀ i : Fin 4, directional i (compactSchwartzTest u n) x = directional i u x := by
  filter_upwards [cutoff_eventually_value_and_derivative x] with n hn
  refine ⟨?_, fun i => ?_⟩
  · change cutoff n x * u x = u x
    rw [hn.1, one_mul]
  · rw [compactSchwartzTest_directional, hn.1, one_mul]
    have h : directional i (cutoff n) x = 0 := by simp only [directional, hn.2, ContinuousLinearMap.zero_apply]
    rw [h, zero_mul, add_zero]

end Burnett.F05.SchwartzH1Density

noncomputable section

namespace Burnett.F05.SchwartzH1Density

open Filter MeasureTheory Set Metric
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet

private theorem toLp_tendsto_of_eventuallyEq_and_bound
    (a : ℕ → Space → ℝ) (f B : Space → ℝ)
    (ha : ∀ n, MemLp (a n) 2 volume) (hf : MemLp f 2 volume) (hB : MemLp B 2 volume)
    (hbound : ∀ n x, ‖a n x - f x‖ ≤ ‖B x‖)
    (hpoint : ∀ x, ∀ᶠ n in atTop, a n x = f x) :
    Tendsto (fun n => (ha n).toLp (a n)) atTop (𝓝 (hf.toLp f)) := by
  have hI : Tendsto (fun n => ∫ x, (a n x - f x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_of_dominated_convergence (μ := (volume : Measure Space))
      (F := fun n x => (a n x - f x) ^ 2) (f := fun _ => (0 : ℝ)) (fun x => B x ^ 2)
      (fun n => ((ha n).sub hf).integrable_sq.aestronglyMeasurable) hB.integrable_sq
      ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      filter_upwards [] with x
      have h := pow_le_pow_left₀ (norm_nonneg _) (hbound n x) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a n x - f x))]
      simpa only [Real.norm_eq_abs, sq_abs] using h
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [hpoint x] with n hn
      simp [hn]
  have hdist (n : ℕ) : dist ((ha n).toLp (a n)) (hf.toLp f) ^ 2 = ∫ x, (a n x - f x) ^ 2 := by
    rw [dist_eq_norm, ← MemLp.toLp_sub, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((ha n).sub hf).coeFn_toLp] with x hx
    rw [hx]
    simp only [Pi.sub_apply, Burnett.X02.TestJetPairing.real_inner_eq_mul, pow_two]
  have hdistSq : Tendsto (fun n => dist ((ha n).toLp (a n)) (hf.toLp f) ^ 2) atTop (𝓝 0) :=
    hI.congr' (Eventually.of_forall fun n => (hdist n).symm)
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.sqrt_zero, Real.sqrt_sq dist_nonneg] using hdistSq.sqrt

def schwartzDirectional (u : SchwartzMap Space ℝ) (i : Fin 4) : SchwartzMap Space ℝ :=
  SchwartzMap.pderivCLM ℝ (EuclideanSpace.single i 1) u

theorem schwartzDirectional_apply (u : SchwartzMap Space ℝ) (i : Fin 4) (x : Space) :
    schwartzDirectional u i x = directional i u x := rfl

def schwartzValueLp (u : SchwartzMap Space ℝ) : ScalarL2 := u.toLp 2 volume

def schwartzDirectionalLp (u : SchwartzMap Space ℝ) (i : Fin 4) : ScalarL2 :=
  (schwartzDirectional u i).toLp 2 volume

private theorem norm_cutoff_sub_one_le (n : ℕ) (x : Space) : ‖cutoff n x - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (cutoff_le_one n x))]
  linarith [cutoff_nonneg n x]

theorem tendsto_compactSchwartzTest_valueLp (u : SchwartzMap Space ℝ) :
    Tendsto (fun n => valueLp (compactSchwartzTest u n)) atTop (𝓝 (schwartzValueLp u)) := by
  refine toLp_tendsto_of_eventuallyEq_and_bound
    (fun n => (compactSchwartzTest u n : Space → ℝ)) u (fun x => ‖u x‖)
    (fun n => test_memLp (compactSchwartzTest u n)) (u.memLp 2 volume) (u.memLp 2 volume).norm ?_ ?_
  · intro n x
    change ‖cutoff n x * u x - u x‖ ≤ ‖‖u x‖‖
    calc
      _ = ‖cutoff n x - 1‖ * ‖u x‖ := by rw [← norm_mul, sub_mul, one_mul]
      _ ≤ _ := by
        simpa only [show ‖‖u x‖‖ = ‖u x‖ by simp [Real.norm_eq_abs], one_mul] using
          mul_le_mul_of_nonneg_right (norm_cutoff_sub_one_le n x) (norm_nonneg (u x))
  · intro x
    exact (compactSchwartzTest_eventually_value_and_directionals u x).mono fun _ h => h.1

theorem tendsto_compactSchwartzTest_directionalLp (u : SchwartzMap Space ℝ) (i : Fin 4) :
    Tendsto (fun n => directionalLp i (compactSchwartzTest u n)) atTop (𝓝 (schwartzDirectionalLp u i)) := by
  obtain ⟨C, hC, hCbound⟩ := exists_cutoff_directional_bound
  let d := schwartzDirectional u i
  have hB : MemLp (fun x => ‖d x‖ + C * ‖u x‖) 2 volume :=
    ((d.memLp 2 volume).norm).add (((u.memLp 2 volume).norm).const_smul C)
  refine toLp_tendsto_of_eventuallyEq_and_bound
    (fun n => directional i (compactSchwartzTest u n)) d _
    (fun n => directional_memLp i (compactSchwartzTest u n)) (d.memLp 2 volume) hB ?_ ?_
  · intro n x
    change ‖directional i (compactSchwartzTest u n) x - directional i u x‖ ≤
      ‖‖directional i u x‖ + C * ‖u x‖‖
    have hnorm : ‖‖directional i u x‖ + C * ‖u x‖‖ = ‖directional i u x‖ + C * ‖u x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [compactSchwartzTest_directional, hnorm]
    calc
      _ = ‖(cutoff n x - 1) * directional i u x + directional i (cutoff n) x * u x‖ := by
        congr 1
        ring
      _ ≤ ‖(cutoff n x - 1) * directional i u x‖ + ‖directional i (cutoff n) x * u x‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [norm_mul, norm_mul]
        simpa only [one_mul] using
          add_le_add (mul_le_mul_of_nonneg_right (norm_cutoff_sub_one_le n x) (norm_nonneg (directional i u x)))
            (mul_le_mul_of_nonneg_right (hCbound n i x) (norm_nonneg _))
  · intro x
    exact (compactSchwartzTest_eventually_value_and_directionals u x).mono fun _ h => h.2 i

/-- The actual value and four actual directional derivatives of a real Schwartz test. -/
def schwartzJet (u : SchwartzMap Space ℝ) : JetSpace :=
  WithLp.toLp 2 (Fin.cases (schwartzValueLp u) (schwartzDirectionalLp u))

@[simp] theorem schwartzJet_value (u : SchwartzMap Space ℝ) :
    schwartzJet u 0 = schwartzValueLp u := rfl

@[simp] theorem schwartzJet_directional (u : SchwartzMap Space ℝ) (i : Fin 4) :
    schwartzJet u i.succ = schwartzDirectionalLp u i := rfl

theorem tendsto_compactSchwartzTest_jet (u : SchwartzMap Space ℝ) :
    Tendsto (fun n => J (compactSchwartzTest u n)) atTop (𝓝 (schwartzJet u)) := by
  let F (n : ℕ) : Fin 5 → ScalarL2 := fun j => J (compactSchwartzTest u n) j
  have hF : Tendsto F atTop (𝓝 (fun j => schwartzJet u j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact tendsto_compactSchwartzTest_valueLp u
    · exact tendsto_compactSchwartzTest_directionalLp u i
  exact ((PiLp.continuous_toLp 2 (fun _ : Fin 5 => ScalarL2)).tendsto _).comp hF

theorem schwartzJet_mem_graphClosure (u : SchwartzMap Space ℝ) : schwartzJet u ∈ graphClosure := by
  change schwartzJet u ∈ closure (LinearMap.range J : Set JetSpace)
  apply isClosed_closure.mem_of_tendsto (tendsto_compactSchwartzTest_jet u)
  exact Eventually.of_forall fun n => subset_closure ⟨compactSchwartzTest u n, rfl⟩

def schwartzGraphTest (u : SchwartzMap Space ℝ) : Burnett.X02.GraphDual.Graph J :=
  ⟨schwartzJet u, schwartzJet_mem_graphClosure u⟩

theorem norm_functional_schwartzGraphTest_le (F : Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ)
    (u : SchwartzMap Space ℝ) : ‖F (schwartzGraphTest u)‖ ≤ ‖F‖ * ‖schwartzJet u‖ :=
  F.le_opNorm (schwartzGraphTest u)

end Burnett.F05.SchwartzH1Density

noncomputable section

namespace Burnett.F05.SchwartzH1Density

open Filter MeasureTheory
open scoped ContDiff Topology
open Burnett.X02.SobolevTestJet Burnett.X02.TestJetPairing
open Burnett.X02.GraphDual

theorem coefficientFunctional_schwartzGraphTest
    (g : Space → ℝ) (V : Fin 4 → Space → ℝ) (hg : MemLp g 2 volume)
    (hV : ∀ i, MemLp (V i) 2 volume) (u : SchwartzMap Space ℝ) :
    coefficientFunctional J (coefficients (hg.toLp g) (fun i => (hV i).toLp (V i)))
        (schwartzGraphTest u) =
      (∫ x, g x * u x) - ∑ i : Fin 4, ∫ x, V i x * directional i u x := by
  change inner ℝ (coefficients (hg.toLp g) (fun i => (hV i).toLp (V i))) (schwartzJet u) = _
  rw [PiLp.inner_apply, Fin.sum_univ_succ]
  simp only [coefficients_zero, coefficients_succ, schwartzJet_value, schwartzJet_directional,
    inner_neg_left, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1
  · rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, u.coeFn_toLp 2 volume] with x hx hu
    change inner ℝ ((hg.toLp g) x) ((u.toLp 2 volume) x) = _
    rw [real_inner_eq_mul, hx, hu]
  · apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hV i).coeFn_toLp, (schwartzDirectional u i).coeFn_toLp 2 volume] with x hx hu
    change inner ℝ (((hV i).toLp (V i)) x) (((schwartzDirectional u i).toLp 2 volume) x) = _
    rw [real_inner_eq_mul, hx, hu, schwartzDirectional_apply]

theorem sourceFunctional_schwartzGraphTest (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : SchwartzMap Space ℝ) :
    Burnett.Analysis.HminusWeightedDual.sourceFunctional f hs hc (schwartzGraphTest u) = ∫ x, f x * u x := by
  have h := coefficientFunctional_schwartzGraphTest f (fun _ => (0 : Space → ℝ))
    (hs.continuous.memLp_of_hasCompactSupport hc) (fun _ => MemLp.zero) u
  simpa only [MemLp.toLp_zero, Pi.zero_apply, zero_mul, integral_zero,
    Finset.sum_const_zero, sub_zero, Burnett.Analysis.HminusWeightedDual.sourceFunctional] using h

theorem abs_integral_mul_schwartz_le_sourceFunctional (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : SchwartzMap Space ℝ) :
    |∫ x, f x * u x| ≤ ‖Burnett.Analysis.HminusWeightedDual.sourceFunctional f hs hc‖ * ‖schwartzJet u‖ := by
  rw [← sourceFunctional_schwartzGraphTest f hs hc u, ← Real.norm_eq_abs]
  exact norm_functional_schwartzGraphTest_le _ u

end Burnett.F05.SchwartzH1Density

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace Burnett.Microlocal.HminusReverse

open MeasureTheory Filter
open Burnett.X02.SobolevTestJet Burnett.F05.SchwartzH1Density
open Burnett.Analysis.HminusWeightedDual
open scoped ContDiff Topology

private def realPart (u : SchwartzMap Space ℂ) : SchwartzMap Space ℝ where
  toFun := Complex.reCLM ∘ u
  smooth' := Complex.reCLM.contDiff.comp (u.smooth ⊤)
  decay' k n := by
    obtain ⟨C, hC⟩ := u.decay' k n
    refine ⟨‖Complex.reCLM‖ * C, fun x => ?_⟩
    rw [Complex.reCLM.iteratedFDeriv_comp_left (u.smooth n).contDiffAt le_rfl]
    calc
      _ ≤ ‖x‖ ^ k * (‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ n u x‖) :=
        mul_le_mul_of_nonneg_left
          (Complex.reCLM.norm_compContinuousMultilinearMap_le _) (pow_nonneg (norm_nonneg _) _)
      _ = ‖Complex.reCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n u x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

private theorem realPart_apply (u : SchwartzMap Space ℂ) (x : Space) :
    realPart u x = (u x).re := rfl

private theorem directional_realPart (u : SchwartzMap Space ℂ) (j : Fin 4) (x : Space) :
    schwartzDirectional (realPart u) j x =
      (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u x).re := by
  unfold schwartzDirectional
  rw [SchwartzMap.pderivCLM_apply, SchwartzMap.pderivCLM_apply]
  change fderiv ℝ (Complex.reCLM ∘ u) x (EuclideanSpace.single j 1) = _
  have hu := ((u.smooth 1).differentiable (by norm_num) x).hasFDerivAt
  rw [(Complex.reCLM.hasFDerivAt.comp x hu).fderiv]
  rfl

private theorem realPart_toLp_norm_le (u : SchwartzMap Space ℂ) :
    ‖(realPart u).toLp 2 volume‖ ≤ ‖u.toLp 2 volume‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(realPart u).coeFn_toLp 2 volume, u.coeFn_toLp 2 volume] with x hr hu
  rw [hr, hu, realPart_apply, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

private theorem directional_realPart_toLp_norm_le (u : SchwartzMap Space ℂ) (j : Fin 4) :
    ‖schwartzDirectionalLp (realPart u) j‖ ≤
      ‖(SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u).toLp 2 volume‖ := by
  unfold schwartzDirectionalLp
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(schwartzDirectional (realPart u) j).coeFn_toLp 2 volume,
    (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u).coeFn_toLp 2 volume] with x hr hu
  rw [hr, hu, directional_realPart, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

private theorem realPart_jetNorm_le (u : SchwartzMap Space ℂ) :
    ‖schwartzJet (realPart u)‖ ≤ Real.sqrt (schwartzH1Energy u) := by
  have henergy : 0 ≤ schwartzH1Energy u := by unfold schwartzH1Energy; positivity
  apply (Real.le_sqrt (norm_nonneg _) henergy).mpr
  unfold schwartzH1Energy
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, schwartzJet_value]
  simp only [schwartzJet_directional]
  exact add_le_add
    (pow_le_pow_left₀ (norm_nonneg _) (realPart_toLp_norm_le u) 2)
    (Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (directional_realPart_toLp_norm_le u j) 2))

private theorem inner_complexSource_re (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (u : SchwartzMap Space ℂ) :
    (inner ℂ ((complexSource f hs hc).toLp 2 volume) (u.toLp 2 volume)).re =
      ∫ x, f x * realPart u x := by
  rw [L2.inner_def]
  let F := (complexSource f hs hc).toLp 2 volume
  let U := u.toLp 2 volume
  change RCLike.re (∫ x, inner ℂ (F x) (U x)) = _
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) F U)]
  change (∫ x, (inner ℂ (F x) (U x)).re) = _
  apply integral_congr_ae
  filter_upwards [(complexSource f hs hc).coeFn_toLp 2 volume, u.coeFn_toLp 2 volume] with x hf hu
  rw [show F x = (complexSource f hs hc) x from hf, show U x = u x from hu]
  change (inner ℂ (f x : ℂ) (u x)).re = _
  simp [RCLike.inner_apply, realPart_apply, mul_comm]

/-- The Fourier negative energy of the actual compact smooth source is
bounded by the squared operator norm on the existing real Sobolev graph. -/
theorem negativeEnergy_le_sourceFunctional_norm_sq (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    negativeEnergy (complexSource f hs hc) ≤ ‖sourceFunctional f hs hc‖ ^ 2 := by
  apply negativeEnergy_le_sq_of_schwartz_tests (complexSource f hs hc)
    ‖sourceFunctional f hs hc‖ (norm_nonneg (sourceFunctional f hs hc))
  intro u
  rw [inner_complexSource_re f hs hc u]
  exact (le_abs_self _).trans ((abs_integral_mul_schwartz_le_sourceFunctional f hs hc
    (realPart u)).trans (mul_le_mul_of_nonneg_left (realPart_jetNorm_le u)
      (norm_nonneg (sourceFunctional f hs hc))))

/-- Graph dual convergence of actual source functionals gives exactly the
Fourier negative-energy convergence consumed by the principal localization. -/
theorem negativeEnergy_tendsto_zero_of_sourceFunctional_tendsto_zero
    {f : ℕ → Space → ℝ} (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (h : Tendsto (fun n => sourceFunctional (f n) (hs n) (hc n)) atTop (𝓝 0)) :
    Tendsto (fun n => negativeEnergy (complexSource (f n) (hs n) (hc n))) atTop (𝓝 0) := by
  have hv : Tendsto (fun n => ‖sourceFunctional (f n) (hs n) (hc n)‖) atTop (𝓝 (0 : ℝ)) := by
    have hn : Continuous (fun F : Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ => ‖F‖) :=
      @continuous_norm (Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ) inferInstance
    simpa only [Function.comp_def, ContinuousLinearMap.opNorm_zero] using
      (hn.tendsto (0 : Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ)).comp h
  have hu : Tendsto (fun n => ‖sourceFunctional (f n) (hs n) (hc n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using hv.pow 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro n
    exact integral_nonneg (negativeDensity_nonneg _)
  · intro n
    exact negativeEnergy_le_sourceFunctional_norm_sq (f n) (hs n) (hc n)

end Burnett.Microlocal.HminusReverse
