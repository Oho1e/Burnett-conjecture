import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NoncommRing

/-!
# General Rosen plane waves

The positive screen square root and weak-star convergence of the symmetric screens.
-/

set_option autoImplicit false

noncomputable section

set_option autoImplicit false
noncomputable section

namespace Burnett.RosenScreen

open Matrix
open scoped BigOperators MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def screenInverseSqrt (γ : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  CFC.sqrt γ⁻¹

theorem screenInverseSqrt_eq_inv_sqrt (γ : Matrix ι ι ℝ) (hγ : γ.PosDef) :
    screenInverseSqrt γ = (CFC.sqrt γ)⁻¹ :=
  hγ.posSemidef.inv_sqrt.symm

theorem screenInverseSqrt_posDef (γ : Matrix ι ι ℝ) (hγ : γ.PosDef) :
    (screenInverseSqrt γ).PosDef :=
  hγ.inv.posDef_sqrt

theorem screenInverseSqrt_isSymm (γ : Matrix ι ι ℝ) (hγ : γ.PosDef) :
    (screenInverseSqrt γ).IsSymm := by
  have hh : (screenInverseSqrt γ)ᴴ = screenInverseSqrt γ :=
    (screenInverseSqrt_posDef γ hγ).1
  change (screenInverseSqrt γ)ᵀ = screenInverseSqrt γ
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh

theorem screenInverseSqrt_mul_self (γ : Matrix ι ι ℝ) (hγ : γ.PosDef) :
    screenInverseSqrt γ * screenInverseSqrt γ = γ⁻¹ :=
  CFC.sqrt_mul_sqrt_self _ hγ.inv.posSemidef.nonneg

def screenL (γ D : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  γ⁻¹ * ((1 / 2 : ℝ) • D)

def screenS (γ D : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  screenInverseSqrt γ * ((1 / 2 : ℝ) • D) * screenInverseSqrt γ

theorem screenL_eq_half_mul (γ D : Matrix ι ι ℝ) :
    screenL γ D = (1 / 2 : ℝ) • (γ⁻¹ * D) := by
  rw [screenL, Matrix.mul_smul]

theorem screenS_eq_half_mul (γ D : Matrix ι ι ℝ) :
    screenS γ D =
      (1 / 2 : ℝ) • (screenInverseSqrt γ * D * screenInverseSqrt γ) := by
  rw [screenS, Matrix.mul_smul, Matrix.smul_mul]

theorem screenS_isSymm (γ D : Matrix ι ι ℝ) (hγ : γ.PosDef) (hD : D.IsSymm) :
    (screenS γ D).IsSymm := by
  change (screenS γ D)ᵀ = screenS γ D
  simp only [screenS, Matrix.transpose_mul, Matrix.transpose_smul,
    (screenInverseSqrt_isSymm γ hγ).eq, hD.eq, Matrix.mul_assoc]

theorem trace_screenL_sq_eq_trace_screenS_sq (γ D : Matrix ι ι ℝ) (hγ : γ.PosDef) :
    Matrix.trace (screenL γ D ^ 2) = Matrix.trace (screenS γ D ^ 2) := by
  let R := screenInverseSqrt γ
  let A := (1 / 2 : ℝ) • D
  change Matrix.trace ((γ⁻¹ * A)^2) = Matrix.trace ((R * A * R)^2)
  have hR : R * R = γ⁻¹ := screenInverseSqrt_mul_self γ hγ
  rw [← hR]
  calc
    _ = Matrix.trace (R * (R * A * R * R * A)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((R * A * R * R * A) * R) := Matrix.trace_mul_comm _ _
    _ = _ := by
      congr 1
      noncomm_ring

theorem trace_screenL_sq_eq_sum_screenS_sq (γ D : Matrix ι ι ℝ)
    (hγ : γ.PosDef) (hD : D.IsSymm) :
    Matrix.trace (screenL γ D ^ 2) = ∑ i, ∑ j, screenS γ D i j ^ 2 := by
  rw [trace_screenL_sq_eq_trace_screenS_sq γ D hγ, pow_two]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(screenS_isSymm γ D hγ hD).apply i j, pow_two]

theorem trace_screenL_sq_nonneg (γ D : Matrix ι ι ℝ) (hγ : γ.PosDef) (hD : D.IsSymm) :
    0 ≤ Matrix.trace (screenL γ D ^ 2) := by
  rw [trace_screenL_sq_eq_sum_screenS_sq γ D hγ hD]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end Burnett.RosenScreen


noncomputable section

namespace Burnett.RosenScreen

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_screenL_eq_trace_screenS (γ D : Matrix ι ι ℝ) (hγ : γ.PosDef) :
    Matrix.trace (screenL γ D) = Matrix.trace (screenS γ D) := by
  let R := screenInverseSqrt γ
  let A := (1 / 2 : ℝ) • D
  change Matrix.trace (γ⁻¹ * A) = Matrix.trace (R * A * R)
  have hR : R * R = γ⁻¹ := screenInverseSqrt_mul_self γ hγ
  rw [← hR, Matrix.mul_assoc, Matrix.trace_mul_comm R (R * A)]

end Burnett.RosenScreen


noncomputable section

namespace Burnett.RosenScreen

open Matrix Set
open scoped BigOperators MatrixOrder ContDiff

abbrev Screen2 := Matrix (Fin 2) (Fin 2) ℝ

def screenDetSqrt2 (γ : Screen2) : ℝ := Real.sqrt γ.det

def screenTraceExpression2 (γ : Screen2) : ℝ :=
  γ.trace + 2 * screenDetSqrt2 γ

def screenRoot2Formula (γ : Screen2) : Screen2 :=
  (Real.sqrt (screenTraceExpression2 γ))⁻¹ • (γ + screenDetSqrt2 γ • (1 : Screen2))

def screenInverseSqrt2Formula (γ : Screen2) : Screen2 :=
  (Real.sqrt (screenTraceExpression2 γ))⁻¹ •
    ((1 : Screen2) + (screenDetSqrt2 γ)⁻¹ • γ.adjugate)

def screenInverseSqrt2Domain : Set Screen2 :=
  {γ | 0 < γ.det ∧ 0 < screenTraceExpression2 γ}

theorem screenInverseSqrt2Domain_of_posDef (γ : Screen2) (hγ : γ.PosDef) :
    γ ∈ screenInverseSqrt2Domain := by
  refine ⟨hγ.det_pos, ?_⟩
  exact add_pos_of_pos_of_nonneg hγ.trace_pos (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

private theorem screenRoot2Numerator_mul_self (γ : Screen2) (d : ℝ) (hd : d^2 = γ.det) :
    (γ + d • (1 : Screen2)) * (γ + d • (1 : Screen2)) =
      (γ.trace + 2 * d) • γ := by
  rw [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.trace_fin_two] <;>
    nlinarith only [hd]

theorem screenRoot2Formula_posDef (γ : Screen2) (hγ : γ.PosDef) :
    (screenRoot2Formula γ).PosDef := by
  have h := screenInverseSqrt2Domain_of_posDef γ hγ
  exact (hγ.add ((Matrix.PosDef.one : (1 : Screen2).PosDef).smul
    (Real.sqrt_pos.mpr h.1))).smul (inv_pos.mpr (Real.sqrt_pos.mpr h.2))

theorem screenRoot2Formula_mul_self (γ : Screen2) (hγ : γ.PosDef) :
    screenRoot2Formula γ * screenRoot2Formula γ = γ := by
  let c := Real.sqrt (screenTraceExpression2 γ)
  let d := screenDetSqrt2 γ
  let N := γ + d • (1 : Screen2)
  have hDomain := screenInverseSqrt2Domain_of_posDef γ hγ
  have hc : 0 < c := Real.sqrt_pos.mpr hDomain.2
  have hc2 : c^2 = screenTraceExpression2 γ := Real.sq_sqrt hDomain.2.le
  have hd2 : d^2 = γ.det := Real.sq_sqrt hDomain.1.le
  have hN : N * N = screenTraceExpression2 γ • γ := screenRoot2Numerator_mul_self γ d hd2
  change (c⁻¹ • N) * (c⁻¹ • N) = γ
  rw [Matrix.smul_mul, Matrix.mul_smul, hN, ← hc2, smul_smul, smul_smul]
  have hone : c⁻¹ * c⁻¹ * c^2 = 1 := by field_simp
  rw [hone, one_smul]

theorem screenRoot2Formula_eq_sqrt (γ : Screen2) (hγ : γ.PosDef) :
    screenRoot2Formula γ = CFC.sqrt γ :=
  (CFC.sqrt_unique (screenRoot2Formula_mul_self γ hγ)
    (screenRoot2Formula_posDef γ hγ).posSemidef.nonneg).symm

theorem screenInverseSqrt_eq_screenInverseSqrt2Formula (γ : Screen2) (hγ : γ.PosDef) :
    screenInverseSqrt γ = screenInverseSqrt2Formula γ := by
  let P := screenRoot2Formula γ
  let d := screenDetSqrt2 γ
  have hγunit := isUnit_iff_ne_zero.mpr (hγ.det_pos.ne')
  have hPInv : P⁻¹ = P * γ⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc, screenRoot2Formula_mul_self γ hγ, Matrix.mul_nonsing_inv _ hγunit]
  have hd : 0 < d := Real.sqrt_pos.mpr hγ.det_pos
  have hd2 : d^2 = γ.det := Real.sq_sqrt hγ.det_pos.le
  calc
    _ = P * γ⁻¹ := by
      rw [screenInverseSqrt_eq_inv_sqrt γ hγ, ← screenRoot2Formula_eq_sqrt γ hγ, hPInv]
    _ = _ := by
      change ((Real.sqrt (screenTraceExpression2 γ))⁻¹ • (γ + d • (1 : Screen2))) * γ⁻¹ =
        (Real.sqrt (screenTraceExpression2 γ))⁻¹ • ((1 : Screen2) + d⁻¹ • γ.adjugate)
      rw [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_nonsing_inv _ hγunit,
        Matrix.smul_mul, Matrix.one_mul, Matrix.inv_def, Ring.inverse_eq_inv, smul_smul]
      have he : d * (γ.det)⁻¹ = d⁻¹ := by rw [← hd2]; field_simp
      rw [he]

end Burnett.RosenScreen


noncomputable section

namespace Burnett.RosenScreen

open Matrix Set Filter
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

theorem isOpen_screenInverseSqrt2Domain : IsOpen screenInverseSqrt2Domain := by
  have hcoord (i j : Fin 2) : Continuous (fun A : Screen2 => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hdet : Continuous (fun A : Screen2 => A.det) := by
    simpa only [Matrix.det_fin_two] using ((hcoord 0 0).mul (hcoord 1 1)).sub
      ((hcoord 0 1).mul (hcoord 1 0))
  have htrace : Continuous (fun A : Screen2 => A.trace) := by
    simpa only [Matrix.trace_fin_two] using (hcoord 0 0).add (hcoord 1 1)
  have htraceExp : Continuous screenTraceExpression2 :=
    htrace.add (continuous_const.mul hdet.sqrt)
  exact (isOpen_lt continuous_const hdet).inter (isOpen_lt continuous_const htraceExp)

section Parameters

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem screenInverseSqrt2Formula_entry_contDiffOn (A : E → Screen2) (U : Set E)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hdom : MapsTo A U screenInverseSqrt2Domain) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => screenInverseSqrt2Formula (A x) i j) U := by
  have hdet : ContDiffOn ℝ ∞ (fun x => (A x).det) U := by
    simpa only [Matrix.det_fin_two] using ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))
  have htrace : ContDiffOn ℝ ∞ (fun x => (A x).trace) U := by
    simpa only [Matrix.trace_fin_two] using (hA 0 0).add (hA 1 1)
  have hd : ContDiffOn ℝ ∞ (fun x => screenDetSqrt2 (A x)) U :=
    hdet.sqrt (fun x hx => (hdom hx).1.ne')
  have hn : ContDiffOn ℝ ∞ (fun x => screenTraceExpression2 (A x)) U :=
    htrace.add (contDiffOn_const.mul hd)
  have hc : ContDiffOn ℝ ∞ (fun x => Real.sqrt (screenTraceExpression2 (A x))) U :=
    hn.sqrt (fun x hx => (hdom hx).2.ne')
  have hdinv := hd.inv (fun x hx => (Real.sqrt_pos.mpr (hdom hx).1).ne')
  have hcinv := hc.inv (fun x hx => (Real.sqrt_pos.mpr (hdom hx).2).ne')
  have hadj : ContDiffOn ℝ ∞ (fun x => (A x).adjugate i j) U := by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.adjugate_fin_two] <;>
      first | exact hA _ _ | exact (hA _ _).neg
  have hone : ContDiffOn ℝ ∞ (fun _ : E => (1 : Screen2) i j) U := contDiffOn_const
  simpa only [screenInverseSqrt2Formula, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    using hcinv.mul (hone.add (hdinv.mul hadj))

theorem screenInverseSqrt_entry_contDiffOn (A : E → Screen2) (U : Set E)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) U)
    (hpos : ∀ x ∈ U, (A x).PosDef) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => screenInverseSqrt (A x) i j) U := by
  refine (screenInverseSqrt2Formula_entry_contDiffOn A U hA ?_ i j).congr ?_
  · exact fun x hx => screenInverseSqrt2Domain_of_posDef (A x) (hpos x hx)
  · intro x hx
    rw [screenInverseSqrt_eq_screenInverseSqrt2Formula (A x) (hpos x hx)]

theorem screenS_entry_contDiffOn (γ D : E → Screen2) (U : Set E)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun x => γ x i j) U)
    (hD : ∀ i j, ContDiffOn ℝ ∞ (fun x => D x i j) U)
    (hpos : ∀ x ∈ U, (γ x).PosDef) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => screenS (γ x) (D x) i j) U := by
  have hR := screenInverseSqrt_entry_contDiffOn γ U hγ hpos
  simp only [screenS, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  apply ContDiffOn.sum
  intro k _
  exact (ContDiffOn.sum (fun l _ => (hR i l).mul (contDiffOn_const.mul (hD l k)))).mul (hR k j)

end Parameters

theorem screenInverseSqrt2Formula_contDiffOn_domain :
    ContDiffOn ℝ ∞ screenInverseSqrt2Formula screenInverseSqrt2Domain := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply screenInverseSqrt2Formula_entry_contDiffOn id screenInverseSqrt2Domain _ (fun _ hx => hx) i j
  intro a b
  exact ((contDiff_apply ℝ ℝ b).comp (contDiff_apply ℝ (Fin 2 → ℝ) a)).contDiffOn

theorem screenS_deriv_entry_contDiffOn (γ : ℝ → Screen2) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hpos : ∀ u ∈ U, (γ u).PosDef) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun u =>
      screenS (γ u) (fun a b => deriv (fun t => γ t a b) u) i j) U :=
  screenS_entry_contDiffOn γ _ U hγ (fun a b => (hγ a b).deriv_of_isOpen hU (by simp)) hpos i j

theorem screenDeriv2_isSymm (γ : ℝ → Screen2) (U : Set ℝ) (hU : IsOpen U)
    (hpos : ∀ u ∈ U, (γ u).PosDef) (u : ℝ) (hu : u ∈ U) :
    Matrix.IsSymm (fun i j => deriv (fun t => γ t i j) u : Screen2) := by
  apply Matrix.IsSymm.ext
  intro i j
  have he : (fun t => γ t j i) =ᶠ[𝓝 u] (fun t => γ t i j) := by
    filter_upwards [hU.mem_nhds hu] with t ht
    have hh : (γ t)ᴴ = γ t := (hpos t ht).isHermitian
    have hs : (γ t).IsSymm := by
      change (γ t)ᵀ = γ t
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
    exact hs.apply i j
  exact he.deriv_eq

end Burnett.RosenScreen

namespace Burnett.RosenScreen

open Filter Matrix Set
open scoped Matrix.Norms.Elementwise Topology

private theorem compactUniformComp {X E F : Type*} [TopologicalSpace X]
    [PseudoMetricSpace E] [ProperSpace E] [PseudoMetricSpace F]
    {K : Set X} (hK : IsCompact K) {V : Set E} (hV : IsOpen V)
    {G : E → F} (hG : ContinuousOn G V)
    {Aₙ : ℕ → X → E} {A : X → E} (hA : ContinuousOn A K) (hAV : MapsTo A K V)
    (h : TendstoUniformlyOn Aₙ A atTop K) :
    TendstoUniformlyOn (fun n x => G (Aₙ n x)) (fun x => G (A x)) atTop K := by
  have hImage : IsCompact (A '' K) := hK.image_of_continuousOn hA
  obtain ⟨δ, hδ, hsub⟩ := hImage.exists_cthickening_subset_open hV (image_subset_iff.mpr hAV)
  apply (hImage.cthickening.uniformContinuousOn_of_continuous (hG.mono hsub)).comp_tendstoUniformlyOn_eventually
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp h δ hδ] with n hn x hx
    apply Metric.thickening_subset_cthickening _ _
    apply Metric.ball_subset_thickening (mem_image_of_mem A hx) δ
    exact Metric.mem_ball.mpr ((dist_comm _ _).trans_lt (hn x hx))
  · exact fun x hx => Metric.self_subset_cthickening (A '' K) (mem_image_of_mem A hx)
  · exact h

theorem tendstoUniformlyOn_screen2_iff_entries {X : Type*} {K : Set X}
    {Aₙ : ℕ → X → Screen2} {A : X → Screen2} :
    TendstoUniformlyOn Aₙ A atTop K ↔ ∀ i j,
      TendstoUniformlyOn (fun n x => Aₙ n x i j) (fun x => A x i j) atTop K := by
  constructor
  · intro h i j
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with n hn x hx
    exact ((dist_le_pi_dist (A x i) (Aₙ n x i) j).trans
      (dist_le_pi_dist (A x) (Aₙ n x) i)).trans_lt (hn x hx)
  · intro h
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have half : 0 < ε / 2 := half_pos hε
    have hall : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin 2, ∀ x ∈ K,
        dist (A x i j) (Aₙ n x i j) < ε / 2 := by
      apply eventually_all.mpr
      intro i
      apply eventually_all.mpr
      intro j
      exact Metric.tendstoUniformlyOn_iff.mp (h i j) (ε / 2) half
    filter_upwards [hall] with n hn x hx
    exact ((dist_pi_le_iff half.le).mpr fun i =>
      (dist_pi_le_iff half.le).mpr fun j => (hn i j x hx).le).trans_lt (half_lt_self hε)

theorem screenInverseSqrt_tendstoUniformlyOn_of_compact {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {Aₙ : ℕ → X → Screen2} {A : X → Screen2}
    (hA : ContinuousOn A K) (hPos : ∀ x ∈ K, (A x).PosDef)
    (hPosₙ : ∀ n x, x ∈ K → (Aₙ n x).PosDef)
    (h : TendstoUniformlyOn Aₙ A atTop K) :
    TendstoUniformlyOn (fun n x => screenInverseSqrt (Aₙ n x))
      (fun x => screenInverseSqrt (A x)) atTop K := by
  have explicit := compactUniformComp hK isOpen_screenInverseSqrt2Domain
    screenInverseSqrt2Formula_contDiffOn_domain.continuousOn hA
    (fun x hx => screenInverseSqrt2Domain_of_posDef (A x) (hPos x hx)) h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp explicit ε hε] with n hn x hx
  rw [screenInverseSqrt_eq_screenInverseSqrt2Formula _ (hPos x hx),
    screenInverseSqrt_eq_screenInverseSqrt2Formula _ (hPosₙ n x hx)]
  exact hn x hx

end Burnett.RosenScreen

namespace Burnett.RosenScreen

open Filter MeasureTheory Set
open scoped Interval Topology

private theorem intervalIntegral_uniform_error {l r C : ℝ} (hlr : l ≤ r) (hC : 0 ≤ C)
    {fₙ gₙ : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : TendstoUniformlyOn fₙ f atTop (Icc l r))
    (hg : ∀ n u, u ∈ Icc l r → ‖gₙ n u‖ ≤ C) :
    Tendsto (fun n => ∫ u in l..r, (fₙ n u - f u) * gₙ n u) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hgap := sub_nonneg.mpr hlr
  have hd : 0 < C * (r - l) + 1 := by positivity
  let δ := ε / (C * (r - l) + 1)
  have hδ : 0 < δ := div_pos hε hd
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf δ hδ] with n hn
  rw [dist_zero_right]
  have hbound : ∀ u ∈ uIoc l r, ‖(fₙ n u - f u) * gₙ n u‖ ≤ δ * C := by
    intro u hu
    have hm : u ∈ Icc l r := by
      rw [uIoc_of_le hlr] at hu
      exact Ioc_subset_Icc_self hu
    have hdiff : ‖fₙ n u - f u‖ ≤ δ := by
      rw [← dist_eq_norm, dist_comm]
      exact (hn u hm).le
    rw [norm_mul]
    exact mul_le_mul hdiff (hg n u hm) (norm_nonneg _) hδ.le
  calc
    ‖∫ u in l..r, (fₙ n u - f u) * gₙ n u‖ ≤ (δ * C) * |r - l| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = δ * (C * (r - l)) := by rw [abs_of_nonneg hgap, mul_assoc]
    _ < δ * (C * (r - l) + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ _ hd.ne'

private theorem deriv_continuousOn_of_contDiffOn_one {f : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (deriv f) U :=
  (hf.deriv_of_isOpen (m := 0) hU (by simp)).continuousOn

private theorem intervalIntegral_mul_deriv_eq_of_contDiffOn_one {l r : ℝ} (hlr : l ≤ r)
    {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    {f w : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f U) (hw : ContDiffOn ℝ 1 w U) :
    (∫ u in l..r, w u * deriv f u) =
      w r * f r - w l * f l - ∫ u in l..r, deriv w u * f u := by
  have subset : uIcc l r ⊆ U := by simpa [uIcc_of_le hlr] using hJ
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
  · intro u hu
    exact ((hw.differentiableOn_one u (subset hu)).differentiableAt
      (hU.mem_nhds (subset hu))).hasDerivAt
  · intro u hu
    exact ((hf.differentiableOn_one u (subset hu)).differentiableAt
      (hU.mem_nhds (subset hu))).hasDerivAt
  · exact ((deriv_continuousOn_of_contDiffOn_one hU hw).mono subset).intervalIntegrable
  · exact ((deriv_continuousOn_of_contDiffOn_one hU hf).mono subset).intervalIntegrable

theorem tendsto_intervalIntegral_mul_deriv_of_uniform {l r : ℝ} (hlr : l ≤ r)
    {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    {fₙ : ℕ → ℝ → ℝ} {f w : ℝ → ℝ} (hfₙ : ∀ n, ContDiffOn ℝ 1 (fₙ n) U)
    (hf : ContDiffOn ℝ 1 f U) (hw : ContDiffOn ℝ 1 w U)
    (h : TendstoUniformlyOn fₙ f atTop (Icc l r)) :
    Tendsto (fun n => ∫ u in l..r, w u * deriv (fₙ n) u) atTop
      (𝓝 (∫ u in l..r, w u * deriv f u)) := by
  have hw' := (deriv_continuousOn_of_contDiffOn_one hU hw).mono hJ
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hw'.norm
  have htest : ∀ n : ℕ, ∀ u ∈ Icc l r, ‖deriv w u‖ ≤ max C 0 := fun _ u hu =>
    (hC (mem_image_of_mem _ hu)).trans (le_max_left C 0)
  have herr := intervalIntegral_uniform_error hlr (le_max_right C 0) h htest
  have hInt (n : ℕ) : IntervalIntegrable (fun u => deriv w u * fₙ n u) volume l r :=
    (hw'.mul ((hfₙ n).continuousOn.mono hJ)).intervalIntegrable_of_Icc hlr
  have hInt0 : IntervalIntegrable (fun u => deriv w u * f u) volume l r :=
    (hw'.mul (hf.continuousOn.mono hJ)).intervalIntegrable_of_Icc hlr
  have he (n : ℕ) :
      (∫ u in l..r, (fₙ n u - f u) * deriv w u) =
        (∫ u in l..r, deriv w u * fₙ n u) - ∫ u in l..r, deriv w u * f u := by
    rw [← intervalIntegral.integral_sub (hInt n) hInt0]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  simp only [he] at herr
  have hconv : Tendsto (fun n => ∫ u in l..r, deriv w u * fₙ n u) atTop
      (𝓝 (∫ u in l..r, deriv w u * f u)) := by
    simpa only [Pi.add_apply, sub_add_cancel, zero_add] using herr.add_const
      (∫ u in l..r, deriv w u * f u)
  have hR := (h.tendsto_at (right_mem_Icc.mpr hlr)).const_mul (w r)
  have hL := (h.tendsto_at (left_mem_Icc.mpr hlr)).const_mul (w l)
  simpa only [intervalIntegral_mul_deriv_eq_of_contDiffOn_one hlr hU hJ hf hw,
    intervalIntegral_mul_deriv_eq_of_contDiffOn_one hlr hU hJ (hfₙ _) hw] using
    (hR.sub hL).sub hconv

theorem rosen_intervalIntegral_eq_restrict_Icc {l r : ℝ} (hlr : l ≤ r) (f : ℝ → ℝ) :
    (∫ u in l..r, f u) = ∫ u, f u ∂(volume.restrict (Icc l r)) := by
  rw [intervalIntegral.integral_of_le hlr, integral_Icc_eq_integral_Ioc]

end Burnett.RosenScreen

namespace Burnett.RosenScreen

open Filter Matrix MeasureTheory Set
open scoped BigOperators ContDiff Interval Matrix.Norms.Elementwise Topology

private theorem compactUniformRealMul {K : Set ℝ} (hK : IsCompact K)
    {Fₙ Gₙ : ℕ → ℝ → ℝ} {F G : ℝ → ℝ} (hF : ContinuousOn F K) (hG : ContinuousOn G K)
    (huf : TendstoUniformlyOn Fₙ F atTop K) (hug : TendstoUniformlyOn Gₙ G atTop K) :
    TendstoUniformlyOn (fun n u => Fₙ n u * Gₙ n u) (fun u => F u * G u) atTop K := by
  have hp : TendstoUniformlyOn (fun n u => (Fₙ n u, Gₙ n u)) (fun u => (F u, G u)) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp huf ε hε,
      Metric.tendstoUniformlyOn_iff.mp hug ε hε] with n hnF hnG u hu
    exact max_lt (hnF u hu) (hnG u hu)
  exact compactUniformComp hK isOpen_univ
    (continuous_fst.mul continuous_snd).continuousOn (hF.prodMk hG) (fun _ _ => mem_univ _) hp

private theorem tendsto_intervalIntegral_mul_deriv_of_uniform_both {l r C : ℝ}
    (hlr : l ≤ r) (hC : 0 ≤ C) {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    {fₙ wₙ : ℕ → ℝ → ℝ} {f w : ℝ → ℝ} (hfₙ : ∀ n, ContDiffOn ℝ 1 (fₙ n) U)
    (hf : ContDiffOn ℝ 1 f U) (hwₙ : ∀ n, ContinuousOn (wₙ n) (Icc l r))
    (hw : ContDiffOn ℝ 1 w U) (hfLim : TendstoUniformlyOn fₙ f atTop (Icc l r))
    (hwLim : TendstoUniformlyOn wₙ w atTop (Icc l r))
    (hDb : ∀ n u, u ∈ Icc l r → ‖deriv (fₙ n) u‖ ≤ C) :
    Tendsto (fun n => ∫ u in l..r, wₙ n u * deriv (fₙ n) u) atTop
      (𝓝 (∫ u in l..r, w u * deriv f u)) := by
  have herr := intervalIntegral_uniform_error hlr hC hwLim hDb
  have hbase := tendsto_intervalIntegral_mul_deriv_of_uniform hlr hU hJ hfₙ hf hw hfLim
  have he (n : ℕ) :
      (∫ u in l..r, (wₙ n u - w u) * deriv (fₙ n) u) =
        (∫ u in l..r, wₙ n u * deriv (fₙ n) u) - ∫ u in l..r, w u * deriv (fₙ n) u := by
    have hD := (deriv_continuousOn_of_contDiffOn_one hU (hfₙ n)).mono hJ
    rw [← intervalIntegral.integral_sub (((hwₙ n).mul hD).intervalIntegrable_of_Icc hlr)
      (((hw.continuousOn.mono hJ).mul hD).intervalIntegrable_of_Icc hlr)]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  simp only [he] at herr
  simpa only [sub_add_cancel, zero_add] using herr.add hbase

private theorem screenS_mul_entry_eq_sum (γ D : Screen2) (w : ℝ) (i j : Fin 2) :
    w * screenS γ D i j = ∑ p : Fin 2 × Fin 2,
      (w / 2 * screenInverseSqrt γ i p.2 * screenInverseSqrt γ p.1 j) * D p.2 p.1 := by
  simp only [screenS, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem intervalIntegral_screenS_mul_entry_eq_sum {l r : ℝ} (hlr : l ≤ r)
    {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    (γ : ℝ → Screen2) (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hPos : ∀ u ∈ U, (γ u).PosDef) {w : ℝ → ℝ} (hw : ContDiffOn ℝ 1 w U) (i j : Fin 2) :
    (∫ u in l..r, w u * screenS (γ u) (fun a b => deriv (fun t => γ t a b) u) i j) =
      ∑ p : Fin 2 × Fin 2, ∫ u in l..r,
        (w u / 2 * screenInverseSqrt (γ u) i p.2 * screenInverseSqrt (γ u) p.1 j) *
          deriv (fun t => γ t p.2 p.1) u := by
  simp_rw [screenS_mul_entry_eq_sum]
  apply intervalIntegral.integral_finset_sum
  intro p _
  have hR₁ := (screenInverseSqrt_entry_contDiffOn γ U hγ hPos i p.2).continuousOn
  have hR₂ := (screenInverseSqrt_entry_contDiffOn γ U hγ hPos p.1 j).continuousOn
  have hD := deriv_continuousOn_of_contDiffOn_one hU ((hγ p.2 p.1).of_le (by simp))
  exact (((((hw.continuousOn.div_const 2).mul hR₁).mul hR₂).mul hD).mono hJ).intervalIntegrable_of_Icc hlr

theorem tendsto_intervalIntegral_screenS_deriv_mul_test {l r C : ℝ} (hlr : l ≤ r)
    {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    {γₙ : ℕ → ℝ → Screen2} {γ : ℝ → Screen2}
    (hγₙ : ∀ n i j, ContDiffOn ℝ ∞ (fun u => γₙ n u i j) U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hPosₙ : ∀ n u, u ∈ U → (γₙ n u).PosDef) (hPos : ∀ u ∈ U, (γ u).PosDef)
    (h : ∀ i j, TendstoUniformlyOn (fun n u => γₙ n u i j) (fun u => γ u i j) atTop (Icc l r))
    (hC : 0 ≤ C) (hD : ∀ n i j u, u ∈ Icc l r → ‖deriv (fun t => γₙ n t i j) u‖ ≤ C)
    {w : ℝ → ℝ} (hw : ContDiffOn ℝ 1 w U) (i j : Fin 2) :
    Tendsto (fun n => ∫ u in l..r,
      w u * screenS (γₙ n u) (fun a b => deriv (fun t => γₙ n t a b) u) i j) atTop
      (𝓝 (∫ u in l..r, w u * screenS (γ u) (fun a b => deriv (fun t => γ t a b) u) i j)) := by
  have hγC : ContinuousOn γ (Icc l r) := by
    apply continuousOn_pi.mpr
    intro a
    apply continuousOn_pi.mpr
    intro b
    exact (hγ a b).continuousOn.mono hJ
  have hInv := screenInverseSqrt_tendstoUniformlyOn_of_compact isCompact_Icc hγC
    (fun u hu => hPos u (hJ hu)) (fun n u hu => hPosₙ n u (hJ hu))
    (tendstoUniformlyOn_screen2_iff_entries.mpr h)
  have hInvEntry := tendstoUniformlyOn_screen2_iff_entries.mp hInv
  have hwConst : TendstoUniformlyOn (fun (_ : ℕ) u => w u / 2) (fun u => w u / 2)
      atTop (Icc l r) := Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
    Eventually.of_forall fun _ _ _ => by simpa using hε
  simp_rw [intervalIntegral_screenS_mul_entry_eq_sum hlr hU hJ _ (hγₙ _) (hPosₙ _) hw i j,
    intervalIntegral_screenS_mul_entry_eq_sum hlr hU hJ γ hγ hPos hw i j]
  apply tendsto_finset_sum
  intro p _
  let Rₙ (n : ℕ) (a b : Fin 2) (u : ℝ) := screenInverseSqrt (γₙ n u) a b
  let R (a b : Fin 2) (u : ℝ) := screenInverseSqrt (γ u) a b
  have hRₙ (n : ℕ) (a b : Fin 2) : ContinuousOn (Rₙ n a b) U :=
    (screenInverseSqrt_entry_contDiffOn (γₙ n) U (hγₙ n) (hPosₙ n) a b).continuousOn
  have hR (a b : Fin 2) : ContDiffOn ℝ 1 (R a b) U :=
    (screenInverseSqrt_entry_contDiffOn γ U hγ hPos a b).of_le (by simp)
  have hwR : TendstoUniformlyOn (fun n u => w u / 2 * Rₙ n i p.2 u)
      (fun u => w u / 2 * R i p.2 u) atTop (Icc l r) :=
    compactUniformRealMul isCompact_Icc ((hw.continuousOn.div_const 2).mono hJ)
      ((hR i p.2).continuousOn.mono hJ) hwConst (hInvEntry i p.2)
  apply tendsto_intervalIntegral_mul_deriv_of_uniform_both hlr hC hU hJ
    (fun n => (hγₙ n p.2 p.1).of_le (by simp)) ((hγ p.2 p.1).of_le (by simp))
    (fun n => ((((hw.continuousOn.div_const 2).mul (hRₙ n i p.2)).mul (hRₙ n p.1 j))).mono hJ)
    (((hw.div_const 2).mul (hR i p.2)).mul (hR p.1 j)) (h p.2 p.1) _ (fun n => hD n p.2 p.1)
  exact compactUniformRealMul isCompact_Icc
    (((hw.continuousOn.div_const 2).mul (hR i p.2).continuousOn).mono hJ)
    ((hR p.1 j).continuousOn.mono hJ) hwR (hInvEntry p.1 j)

theorem tendsto_restrict_Icc_screenS_deriv_mul_test {l r C : ℝ} (hlr : l ≤ r)
    {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    {γₙ : ℕ → ℝ → Screen2} {γ : ℝ → Screen2}
    (hγₙ : ∀ n i j, ContDiffOn ℝ ∞ (fun u => γₙ n u i j) U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hPosₙ : ∀ n u, u ∈ U → (γₙ n u).PosDef) (hPos : ∀ u ∈ U, (γ u).PosDef)
    (h : ∀ i j, TendstoUniformlyOn (fun n u => γₙ n u i j) (fun u => γ u i j) atTop (Icc l r))
    (hC : 0 ≤ C) (hD : ∀ n i j u, u ∈ Icc l r → ‖deriv (fun t => γₙ n t i j) u‖ ≤ C)
    {w : ℝ → ℝ} (hw : ContDiffOn ℝ 1 w U) (i j : Fin 2) :
    Tendsto (fun n => ∫ u,
      w u * screenS (γₙ n u) (fun a b => deriv (fun t => γₙ n t a b) u) i j
        ∂(volume.restrict (Icc l r))) atTop
      (𝓝 (∫ u, w u * screenS (γ u) (fun a b => deriv (fun t => γ t a b) u) i j
        ∂(volume.restrict (Icc l r)))) := by
  simpa only [rosen_intervalIntegral_eq_restrict_Icc hlr] using
    tendsto_intervalIntegral_screenS_deriv_mul_test hlr hU hJ hγₙ hγ hPosₙ hPos h hC hD hw i j

end Burnett.RosenScreen

namespace Burnett.RosenScreen

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

theorem exists_smooth_L1_approx_Icc {l r : ℝ} (hlr : l ≤ r) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc l r)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ IntegrableOn g (Icc l r) ∧
      (∫ u in Icc l r, ‖f u - g u‖) ≤ ε := by
  let J := Icc l r
  let μ : Measure ℝ := volume.restrict J
  let f₀ := J.indicator f
  have hf₀ : Integrable f₀ (volume : Measure ℝ) := hf.integrable_indicator measurableSet_Icc
  obtain ⟨g₀, hcompact, happ₀, hcontinuous, hg₀⟩ :=
    hf₀.exists_hasCompactSupport_integral_sub_le (half_pos hε)
  have happ : (∫ u, ‖f u - g₀ u‖ ∂μ) ≤ ε / 2 := by
    have heq : (fun u => ‖f u - g₀ u‖) =ᵐ[μ] (fun u => ‖f₀ u - g₀ u‖) := by
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with u hu
      simp only [f₀, indicator_of_mem hu]
    rw [integral_congr_ae heq]
    exact (setIntegral_le_integral (hf₀.sub hg₀).norm
      (Eventually.of_forall fun _ => norm_nonneg _)).trans happ₀
  let δ := (ε / 2) / (r - l + 1)
  have hgap : 0 ≤ r - l := sub_nonneg.mpr hlr
  have hden : 0 < r - l + 1 := by positivity
  have hδ : 0 < δ := div_pos (half_pos hε) hden
  obtain ⟨g, hsmooth, hclose⟩ :=
    (hcompact.uniformContinuous_of_continuous hcontinuous).exists_contDiff_dist_le hδ
  have hg : Integrable g μ := hsmooth.continuous.integrableOn_Icc
  have hg₀' : Integrable g₀ μ := hg₀.mono_measure Measure.restrict_le_self
  have hf' : Integrable f μ := hf
  have hmass : μ.real univ = r - l := by
    rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def]
    exact Real.volume_real_Icc_of_le hlr
  have herr : (∫ u, ‖g₀ u - g u‖ ∂μ) ≤ ε / 2 := by
    letI : IsFiniteMeasure μ := by dsimp [μ, J]; infer_instance
    have hpoint (u : ℝ) : ‖g₀ u - g u‖ ≤ δ := by
      rw [← dist_eq_norm, dist_comm]
      exact (hclose u).le
    calc
      (∫ u, ‖g₀ u - g u‖ ∂μ) ≤ ∫ _ : ℝ, δ ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const _) (Eventually.of_forall hpoint)
      _ = (r - l) * δ := by rw [integral_const, hmass, smul_eq_mul]
      _ ≤ (r - l + 1) * δ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
      _ = ε / 2 := by rw [mul_comm]; exact div_mul_cancel₀ _ hden.ne'
  refine ⟨g, hsmooth, hg, ?_⟩
  change (∫ u, ‖f u - g u‖ ∂μ) ≤ ε
  have hsum : (∫ u, ‖f u - g u‖ ∂μ) ≤
      (∫ u, ‖f u - g₀ u‖ ∂μ) + ∫ u, ‖g₀ u - g u‖ ∂μ := by
    have hfg₀ : Integrable (fun u => ‖f u - g₀ u‖) μ := (hf'.sub hg₀').norm
    have hg₀g : Integrable (fun u => ‖g₀ u - g u‖) μ := (hg₀'.sub hg).norm
    rw [← integral_add hfg₀ hg₀g]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      (hfg₀.add hg₀g)
      (Eventually.of_forall fun u => by
        simpa only [← dist_eq_norm] using dist_triangle (f u) (g₀ u) (g u))
  linarith

private theorem testIntegral_sub_le_of_bounded {μ : Measure ℝ} {f g q : ℝ → ℝ}
    {C : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hqm : AEStronglyMeasurable q μ) (hqb : ∀ᵐ u ∂μ, ‖q u‖ ≤ C) :
    dist (∫ u, f u * q u ∂μ) (∫ u, g u * q u ∂μ) ≤ C * ∫ u, ‖f u - g u‖ ∂μ := by
  have hfi : Integrable (fun u => f u * q u) μ := by
    simpa only [mul_comm] using hf.bdd_mul' hqm hqb
  have hgi : Integrable (fun u => g u * q u) μ := by
    simpa only [mul_comm] using hg.bdd_mul' hqm hqb
  rw [dist_eq_norm, ← integral_sub hfi hgi, ← integral_const_mul]
  apply norm_integral_le_of_norm_le ((hf.sub hg).norm.const_mul C)
  filter_upwards [hqb] with u hu
  rw [← sub_mul, norm_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)

theorem tendsto_Icc_pairings_all_L1_of_smooth {l r C : ℝ} (hlr : l ≤ r) (hC : 0 ≤ C)
    {qₙ : ℕ → ℝ → ℝ} {q : ℝ → ℝ}
    (hmₙ : ∀ n, AEStronglyMeasurable (qₙ n) (volume.restrict (Icc l r)))
    (hm : AEStronglyMeasurable q (volume.restrict (Icc l r)))
    (hBₙ : ∀ n, ∀ᵐ u ∂(volume.restrict (Icc l r)), ‖qₙ n u‖ ≤ C)
    (hB : ∀ᵐ u ∂(volume.restrict (Icc l r)), ‖q u‖ ≤ C)
    (hSmooth : ∀ w : ℝ → ℝ, ContDiff ℝ ∞ w →
      Tendsto (fun n => ∫ u in Icc l r, w u * qₙ n u) atTop (𝓝 (∫ u in Icc l r, w u * q u)))
    (w : ℝ → ℝ) (hw : IntegrableOn w (Icc l r)) :
    Tendsto (fun n => ∫ u in Icc l r, w u * qₙ n u) atTop (𝓝 (∫ u in Icc l r, w u * q u)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := (ε / 8) / (C + 1)
  have hden : 0 < C + 1 := by positivity
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hsmooth, hg, happ⟩ := exists_smooth_L1_approx_Icc hlr hw hδ
  have herror : C * (∫ u in Icc l r, ‖w u - g u‖) ≤ ε / 8 := by
    calc
      _ ≤ C * δ := mul_le_mul_of_nonneg_left happ hC
      _ ≤ (C + 1) * δ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hδ.le
      _ = ε / 8 := by rw [mul_comm]; exact div_mul_cancel₀ _ hden.ne'
  filter_upwards [Metric.tendsto_nhds.mp (hSmooth g hsmooth) (ε / 2) (half_pos hε)] with n hn
  have h₁ := (testIntegral_sub_le_of_bounded hw hg (hmₙ n) (hBₙ n)).trans herror
  have h₂ := (testIntegral_sub_le_of_bounded hw hg hm hB).trans herror
  calc
    _ ≤ dist (∫ u in Icc l r, w u * qₙ n u) (∫ u in Icc l r, g u * qₙ n u) +
        (dist (∫ u in Icc l r, g u * qₙ n u) (∫ u in Icc l r, g u * q u) +
          dist (∫ u in Icc l r, g u * q u) (∫ u in Icc l r, w u * q u)) :=
      (dist_triangle _ _ _).trans (add_le_add_left (dist_triangle _ _ _) _)
    _ < ε := by rw [dist_comm (∫ u in Icc l r, g u * q u)]; linarith

end Burnett.RosenScreen

namespace Burnett.RosenScreen

open Filter Matrix MeasureTheory Set
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Elementwise Topology

private theorem compact_uniform_sequence_bound {E : Type*} [NormedAddCommGroup E]
    {K : Set ℝ} (hK : IsCompact K) {Fₙ : ℕ → ℝ → E} {F : ℝ → E}
    (hFₙ : ∀ n, ContinuousOn (Fₙ n) K) (hF : ContinuousOn F K)
    (h : TendstoUniformlyOn Fₙ F atTop K) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ n u, u ∈ K → ‖Fₙ n u‖ ≤ B) ∧ ∀ u ∈ K, ‖F u‖ ≤ B := by
  obtain ⟨b, hb⟩ := hK.bddAbove_image hF.norm
  have hb' (u : ℝ) (hu : u ∈ K) : ‖F u‖ ≤ b := hb (mem_image_of_mem _ hu)
  have hEach (n : ℕ) : ∃ bₙ : ℝ, ∀ u ∈ K, ‖Fₙ n u‖ ≤ bₙ := by
    obtain ⟨bₙ, hbₙ⟩ := hK.bddAbove_image (hFₙ n).norm
    exact ⟨bₙ, fun u hu => hbₙ (mem_image_of_mem _ hu)⟩
  choose bₙ hbₙ using hEach
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp h 1 zero_lt_one)
  let B := max b 0 + 1 + ∑ n ∈ Finset.range N, max (bₙ n) 0
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, max (bₙ n) 0 :=
    Finset.sum_nonneg fun n _ => le_max_right _ _
  have hleft : max b 0 + 1 ≤ B := le_add_of_nonneg_right hsum
  have hright : (∑ n ∈ Finset.range N, max (bₙ n) 0) ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_left (by positivity)
  refine ⟨B, (by positivity), ?_, fun u hu => (hb' u hu).trans ?_⟩
  · intro n u hu
    by_cases hn : N ≤ n
    · have hdiff : ‖Fₙ n u - F u‖ ≤ 1 := by
        rw [← dist_eq_norm, dist_comm]
        exact (hN n hn u hu).le
      calc
        ‖Fₙ n u‖ = ‖Fₙ n u - F u + F u‖ := by rw [sub_add_cancel]
        _ ≤ ‖Fₙ n u - F u‖ + ‖F u‖ := norm_add_le _ _
        _ ≤ 1 + max b 0 := add_le_add hdiff ((hb' u hu).trans (le_max_left _ _))
        _ ≤ B := by simpa only [add_comm 1 (max b 0)] using hleft
    · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
      exact ((hbₙ n u hu).trans (le_max_left _ _)).trans
        ((Finset.single_le_sum (fun k (_ : k ∈ Finset.range N) => le_max_right (bₙ k) 0) hmem).trans hright)
  · exact (le_max_left _ _).trans ((le_add_of_nonneg_right zero_le_one).trans hleft)

private theorem screen2_entry_norm_le (A : Screen2) (i j : Fin 2) : ‖A i j‖ ≤ ‖A‖ := by
  simpa using (dist_le_pi_dist (A i) ((0 : Screen2) i) j).trans (dist_le_pi_dist A (0 : Screen2) i)

private theorem screen2_norm_le_of_entry_bound {A : Screen2} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A‖ ≤ B := by
  rw [← dist_zero_right]
  exact (dist_pi_le_iff hB).mpr fun i => (dist_pi_le_iff hB).mpr fun j => by simpa using h i j

private theorem screenS_norm_le_of_inverse_root_and_derivative {γ D : Screen2} {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hRoot : ‖screenInverseSqrt γ‖ ≤ B) (hD : ‖D‖ ≤ C) :
    ‖screenS γ D‖ ≤ 2 * B * B * C := by
  apply screen2_norm_le_of_entry_bound (by positivity)
  intro i j
  rw [← one_mul (screenS γ D i j), screenS_mul_entry_eq_sum]
  calc
    _ ≤ ∑ p : Fin 2 × Fin 2, ‖((1 : ℝ) / 2 * screenInverseSqrt γ i p.2 *
        screenInverseSqrt γ p.1 j) * D p.2 p.1‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Fin 2 × Fin 2, (1 / 2 : ℝ) * B * B * C := by
      apply Finset.sum_le_sum
      intro p _
      simp only [norm_mul, show ‖(1 : ℝ) / 2‖ = 1 / 2 by norm_num]
      gcongr
      · exact (screen2_entry_norm_le _ _ _).trans hRoot
      · exact (screen2_entry_norm_le _ _ _).trans hRoot
      · exact (screen2_entry_norm_le _ _ _).trans hD
    _ = 2 * B * B * C := by norm_num [Fintype.card_prod]; ring

theorem screenS_deriv_LInf_weakStar_Icc {l r C : ℝ} (hlr : l ≤ r)
    {U : Set ℝ} (hU : IsOpen U) (hJ : Icc l r ⊆ U)
    {γₙ : ℕ → ℝ → Screen2} {γ : ℝ → Screen2}
    (hγₙ : ∀ n i j, ContDiffOn ℝ ∞ (fun u => γₙ n u i j) U)
    (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun u => γ u i j) U)
    (hPosₙ : ∀ n u, u ∈ U → (γₙ n u).PosDef) (hPos : ∀ u ∈ U, (γ u).PosDef)
    (h : ∀ i j, TendstoUniformlyOn (fun n u => γₙ n u i j) (fun u => γ u i j) atTop (Icc l r))
    (hC : 0 ≤ C) (hD : ∀ n i j u, u ∈ Icc l r → ‖deriv (fun t => γₙ n t i j) u‖ ≤ C) :
    let μ : Measure ℝ := volume.restrict (Icc l r)
    let Sₙ := fun (n : ℕ) u => screenS (γₙ n u) (fun a b => deriv (fun t => γₙ n t a b) u)
    let S := fun u => screenS (γ u) (fun a b => deriv (fun t => γ t a b) u)
    ∃ M : ℝ, 0 ≤ M ∧ (∀ n, eLpNorm (Sₙ n) ∞ μ ≤ ENNReal.ofReal M) ∧
      eLpNorm S ∞ μ ≤ ENNReal.ofReal M ∧
      ∀ w : ℝ → ℝ, Integrable w μ → ∀ i j,
        (∀ n, Integrable (fun u => w u * Sₙ n u i j) μ) ∧
        Integrable (fun u => w u * S u i j) μ ∧
        Tendsto (fun n => ∫ u, w u * Sₙ n u i j ∂μ) atTop (𝓝 (∫ u, w u * S u i j ∂μ)) := by
  dsimp only
  let J := Icc l r
  let μ : Measure ℝ := volume.restrict J
  let Rₙ (n : ℕ) (u : ℝ) := screenInverseSqrt (γₙ n u)
  let R (u : ℝ) := screenInverseSqrt (γ u)
  let Dₙ (n : ℕ) (u : ℝ) : Screen2 := fun a b => deriv (fun t => γₙ n t a b) u
  let D (u : ℝ) : Screen2 := fun a b => deriv (fun t => γ t a b) u
  let Sₙ (n : ℕ) (u : ℝ) := screenS (γₙ n u) (Dₙ n u)
  let S (u : ℝ) := screenS (γ u) (D u)
  have hγC : ContinuousOn γ J := continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b =>
    (hγ a b).continuousOn.mono hJ
  have hRootC (A : ℝ → Screen2) (hA : ∀ a b, ContDiffOn ℝ ∞ (fun u => A u a b) U)
      (hP : ∀ u ∈ U, (A u).PosDef) : ContinuousOn (fun u => screenInverseSqrt (A u)) J :=
    continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b =>
      (screenInverseSqrt_entry_contDiffOn A U hA hP a b).continuousOn.mono hJ
  have hInv : TendstoUniformlyOn Rₙ R atTop J :=
    screenInverseSqrt_tendstoUniformlyOn_of_compact isCompact_Icc hγC
      (fun u hu => hPos u (hJ hu)) (fun n u hu => hPosₙ n u (hJ hu))
      (tendstoUniformlyOn_screen2_iff_entries.mpr h)
  obtain ⟨B, hB, hRn, hR⟩ := compact_uniform_sequence_bound isCompact_Icc
    (fun n => hRootC _ (hγₙ n) (hPosₙ n)) (hRootC _ hγ hPos) hInv
  have hDC : ContinuousOn D J := continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b =>
    (deriv_continuousOn_of_contDiffOn_one hU ((hγ a b).of_le (by simp))).mono hJ
  obtain ⟨b, hb⟩ := isCompact_Icc.bddAbove_image hDC.norm
  let C' := max C b
  have hC' : 0 ≤ C' := hC.trans (le_max_left _ _)
  let M := 2 * B * B * C'
  have hM : 0 ≤ M := by positivity
  have hSn (n : ℕ) (u : ℝ) (hu : u ∈ J) : ‖Sₙ n u‖ ≤ M :=
    screenS_norm_le_of_inverse_root_and_derivative hB hC' (hRn n u hu)
      (screen2_norm_le_of_entry_bound hC' fun i j => (hD n i j u hu).trans (le_max_left _ _))
  have hS (u : ℝ) (hu : u ∈ J) : ‖S u‖ ≤ M :=
    screenS_norm_le_of_inverse_root_and_derivative hB hC' (hR u hu)
      ((hb (mem_image_of_mem _ hu)).trans (le_max_right _ _))
  have hJae : ∀ᵐ u ∂μ, u ∈ J := ae_restrict_mem measurableSet_Icc
  have hNorm {F : ℝ → Screen2} (hF : ∀ u ∈ J, ‖F u‖ ≤ M) : eLpNorm F ∞ μ ≤ ENNReal.ofReal M := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (hJae.mono hF)
  refine ⟨M, hM, fun n => hNorm (hSn n), hNorm hS, ?_⟩
  intro w hw i j
  have hCₙ (n : ℕ) : ContinuousOn (fun u => Sₙ n u i j) J :=
    (screenS_deriv_entry_contDiffOn _ U hU (hγₙ n) (hPosₙ n) i j).continuousOn.mono hJ
  have hC₀ : ContinuousOn (fun u => S u i j) J :=
    (screenS_deriv_entry_contDiffOn _ U hU hγ hPos i j).continuousOn.mono hJ
  have hmₙ (n : ℕ) : AEStronglyMeasurable (fun u => Sₙ n u i j) μ :=
    (hCₙ n).aestronglyMeasurable measurableSet_Icc
  have hm₀ : AEStronglyMeasurable (fun u => S u i j) μ := hC₀.aestronglyMeasurable measurableSet_Icc
  have hbₙ (n : ℕ) : ∀ᵐ u ∂μ, ‖Sₙ n u i j‖ ≤ M :=
    hJae.mono fun u hu => (screen2_entry_norm_le _ _ _).trans (hSn n u hu)
  have hb₀ : ∀ᵐ u ∂μ, ‖S u i j‖ ≤ M :=
    hJae.mono fun u hu => (screen2_entry_norm_le _ _ _).trans (hS u hu)
  refine ⟨fun n => ?_, ?_, tendsto_Icc_pairings_all_L1_of_smooth hlr hM hmₙ hm₀ hbₙ hb₀ ?_ w hw⟩
  · simpa only [mul_comm] using hw.bdd_mul' (hmₙ n) (hbₙ n)
  · simpa only [mul_comm] using hw.bdd_mul' hm₀ hb₀
  · intro g hg
    have hg' : ContDiff ℝ 1 g := (contDiff_infty.mp hg) 1
    exact tendsto_restrict_Icc_screenS_deriv_mul_test hlr hU hJ hγₙ hγ hPosₙ hPos h hC hD
      hg'.contDiffOn i j

end Burnett.RosenScreen
