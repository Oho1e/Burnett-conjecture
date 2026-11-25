import Burnett.Analysis.FrozenTransport.ActualFarAngularProfile
import Burnett.Analysis.FrozenTransport.PatchCorrection.ParameterizedCyclicPhase
import Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Metric Matrix Burnett.C02 Burnett.V03 Burnett.V04 Burnett.V11
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

def jointFarProfile (G : E → Mat) (S : E → E → Matrix OrderedPair OrderedPair ℝ) (a : Joint → ℝ)
    (ϑ : ℝ → ℝ) (κ δ b : ℝ) (k j l : OrderedPair) (x : E × (Joint × E)) : ℂ :=
  farPhysicalCubicCorrection orderedMetricDirection (G x.1) (fun v => a (x.1, v)) ϑ κ δ b
    (fun y t => (S x.1 y.1 t k : ℂ)) (fun y t => (S x.1 y.2.2 t j : ℂ))
    (fun y t => (S x.1 (-farHighOutput y) t l : ℂ)) (x.2.2, x.2.1)

/-- The actual density coefficient is differentiated in the metric before
freezing. The resulting guarded far numerator is smooth also in the center. -/
theorem jointFarProfile_contDiffOn (U : Set E) (G : E → Mat) (Gdiff : ContDiffOn ℝ ∞ G U)
    (Gnd : ∀ x ∈ U, G x ∈ nonsingularMetricDomain)
    (mdiff : ∀ a b, ContDiffOn ℝ ∞ (fun x => inverseMatrix (G x) a b) U)
    (S : E → E → Matrix OrderedPair OrderedPair ℝ)
    (Sdiff : ∀ k j, ContDiffOn ℝ ∞ (fun x : Joint => S x.1 x.2 k j) (U ×ˢ {v : E | v ≠ 0}))
    (a : Joint → ℝ) (adiff : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) (δ b : ℝ) (k j l : OrderedPair) :
    ContDiffOn ℝ ∞ (jointFarProfile G S a ϑ κ δ b k j l) (U ×ˢ gaugePhaseWindow) := by
  let X := E × (Joint × E)
  let O := U ×ˢ gaugePhaseWindow
  let ctr (p : X) := p.1
  let w (p : X) := p.2.2
  let z (p : X) := p.2.1.1
  let q (p : X) := p.2.1.2
  let r (p : X) := -(q p + z p)
  let normVars (p : X) : FarProfilePoint := (w p, z p, q p)
  have dc : ContDiff ℝ ∞ ctr := contDiff_fst
  have dw : ContDiff ℝ ∞ w := contDiff_snd.comp contDiff_snd
  have dz : ContDiff ℝ ∞ z := (contDiff_fst.comp contDiff_fst).comp contDiff_snd
  have dq : ContDiff ℝ ∞ q := (contDiff_snd.comp contDiff_fst).comp contDiff_snd
  have dr : ContDiff ℝ ∞ r := (dq.add dz).neg
  have dvars : ContDiff ℝ ∞ normVars := dw.prodMk (dz.prodMk dq)
  have dG := Gdiff.comp dc.contDiffOn (show MapsTo ctr O U from fun _ h => h.1)
  have dm (i j : Fin 4) := (mdiff i j).comp dc.contDiffOn (show MapsTo ctr O U from fun _ h => h.1)
  have away (p : X) (hp : p ∈ O) : w p ≠ 0 ∧ q p ≠ 0 ∧ r p ≠ 0 := by
    have hw : (1 / 4 : ℝ) < ‖w p‖ := hp.2.1
    have hz : ‖z p‖ < 1 / 2 := hp.2.2.1
    have hq : (3 / 4 : ℝ) < ‖q p‖ := hp.2.2.2
    refine ⟨norm_pos_iff.mp (lt_trans (by norm_num) hw), norm_pos_iff.mp (lt_trans (by norm_num) hq), ?_⟩
    intro hr
    have hsum : q p + z p = 0 := neg_eq_zero.mp hr
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg] at hq
    linarith
  have vars (p : X) (hp : p ∈ O) : normVars p ∈ farProfileOpenDomain := by
    intro h
    change q p + z p = 0 at h
    exact (away p hp).2.2 (by change -(q p + z p) = 0; simp only [h, neg_zero])
  have weight := Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((farCutoffExtension_contDiffOn hϑ hκ δ).comp dvars.contDiffOn vars)
  have realCoord (f : X → E) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
      ContDiffOn ℝ ∞ (fun x => f x i) O :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hf).contDiffOn
  have pairingSmooth (f g : X → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
      ContDiffOn ℝ ∞ (fun x => pairing (inverseMatrix (G (ctr x))) (f x) (g x)) O := by
    unfold pairing rowValue
    exact ContDiffOn.sum fun j _ => (ContDiffOn.sum fun i _ => (dm i j).mul (realCoord f hf i)).mul (realCoord g hg j)
  have phase : ContDiffOn ℝ ∞ (fun x => normalizedFarPhase (inverseMatrix (G (ctr x))) (normVars x)) O := by
    change ContDiffOn ℝ ∞ (fun x => 2 * pairing (inverseMatrix (G (ctr x))) (w x) (q x) +
      inner ℝ (w x) (z x) * pairing (inverseMatrix (G (ctr x))) (w x) (w x)) O
    exact (contDiffOn_const.mul (pairingSmooth w q dw dq)).add
      ((dw.inner ℝ dz).contDiffOn.mul (pairingSmooth w w dw dw))
  have reciprocal := Complex.ofRealCLM.contDiff.comp_contDiffOn ((guardedFarReciprocal_contDiff (b * δ ^ 2)).comp_contDiffOn phase)
  have cyc := Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((parametric_cyclicLowNormalizedPhase a adiff).mono (show O ⊆ univ ×ˢ gaugePhaseWindow from fun _ h => ⟨mem_univ _, h.2⟩))
  let H (x : X) (t : OrderedPair) := (S (ctr x) (w x) t k : ℂ)
  let J (x : X) (t : OrderedPair) := (S (ctr x) (q x) t j : ℂ)
  let L (x : X) (t : OrderedPair) := (S (ctr x) (r x) t l : ℂ)
  have columns (f : X → E) (hf : ContDiff ℝ ∞ f) (hn : ∀ x ∈ O, f x ≠ 0) (s t : OrderedPair) :
      ContDiffOn ℝ ∞ (fun x => (S (ctr x) (f x) s t : ℂ)) O :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn ((Sdiff s t).comp (dc.prodMk hf).contDiffOn (fun x h => ⟨h.1, hn x h⟩))
  have hH (t : OrderedPair) : ContDiffOn ℝ ∞ (fun x => H x t) O := columns w dw (fun x h => (away x h).1) t k
  have hJ (t : OrderedPair) : ContDiffOn ℝ ∞ (fun x => J x t) O := columns q dq (fun x h => (away x h).2.1) t j
  have hL (t : OrderedPair) : ContDiffOn ℝ ∞ (fun x => L x t) O := columns r dr (fun x h => (away x h).2.2) t l
  have coef (s t : ActionSlot OrderedPair) (i : OrderedPair) : ContDiffOn ℝ ∞
      (fun x => (fderiv ℝ (metricActionCoefficient orderedMetricDirection s t) (G (ctr x)) (orderedMetricDirection i) : ℂ)) O := by
    have hDerivative : ContDiffOn ℝ ∞ (fderiv ℝ (metricActionCoefficient orderedMetricDirection s t)) nonsingularMetricDomain :=
      (contDiffOn_metricActionCoefficient orderedMetricDirection s t).fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (((hDerivative.comp dG (fun x h => Gnd (ctr x) h.1)).clm_apply contDiffOn_const))
  have cub (H J L : X → OrderedPair → ℂ) (q r : X → E)
      (hH : ∀ i, ContDiffOn ℝ ∞ (fun x => H x i) O)
      (hJ : ∀ i, ContDiffOn ℝ ∞ (fun x => J x i) O)
      (hL : ∀ i, ContDiffOn ℝ ∞ (fun x => L x i) O)
      (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r) :
      ContDiffOn ℝ ∞ (fun x => frozenDensityCubicTerm orderedMetricDirection (G (ctr x)) (H x) (q x) (J x) (r x) (L x)) O := by
    have coord (f : X → E) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
        ContDiffOn ℝ ∞ (fun x => (f x i : ℂ)) O := Complex.ofRealCLM.contDiff.comp_contDiffOn (realCoord f hf i)
    unfold frozenDensityCubicTerm densityCoefficientDirection
    exact ContDiffOn.sum fun s _ => ContDiffOn.sum fun t _ =>
      ((ContDiffOn.sum fun i _ => (coef s t i).mul (hH i)).mul ((coord q hq s.1).mul (hJ s.2))).mul
        ((coord r hr t.1).mul (hL t.2))
  have vertex := (((cub H J L q r hH hJ hL dq dr).add (cub J L H r z hJ hL hH dr dz)).add
    (cub L H J z q hL hH hJ dz dq)).neg
  exact weight.mul ((contDiffOn_const.mul ((contDiffOn_const.mul cyc).mul vertex)).mul reciprocal)

/-- A single bound on the actual far profile jets works at every frozen
center and across all tensor placements. -/
theorem exists_jointFarProfile_jets (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (G : E → Mat) (Gdiff : ContDiffOn ℝ ∞ G U) (Gnd : ∀ x ∈ U, G x ∈ nonsingularMetricDomain)
    (mdiff : ∀ a b, ContDiffOn ℝ ∞ (fun x => inverseMatrix (G x) a b) U)
    (S : E → E → Matrix OrderedPair OrderedPair ℝ)
    (Sdiff : ∀ k j, ContDiffOn ℝ ∞ (fun x : Joint => S x.1 x.2 k j) (U ×ˢ {v : E | v ≠ 0}))
    (a : Joint → ℝ) (adiff : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) (δ b : ℝ) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ k j l, GaugeProfileBound N M
      (fun y => jointFarProfile G S a ϑ κ δ b k j l (x, y)) := by
  classical
  let O := U ×ˢ gaugePhaseWindow
  have hsub : K ×ˢ gaugeAngularWindow ⊆ O := by
    intro p hp
    have hw := mem_sphere_zero_iff_norm.mp hp.2.2
    have hz := mem_closedBall_zero_iff.mp hp.2.1.1
    have hq := mem_sphere_zero_iff_norm.mp hp.2.1.2
    refine ⟨hKU hp.1, ?_, ?_, ?_⟩ <;> dsimp <;> linarith
  have bound (k j l : OrderedPair) := exists_uniform_frozen_angular_jets K hK
    (jointFarProfile G S a ϑ κ δ b k j l) O (hU.prod gaugePhaseWindow_open) hsub
    (jointFarProfile_contDiffOn U G Gdiff Gnd mdiff S Sdiff a adiff ϑ hϑ κ hκ δ b k j l) N
  choose M hM estimates using bound
  let total := ∑ k : OrderedPair, ∑ j : OrderedPair, ∑ l : OrderedPair, M k j l
  refine ⟨total, Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hM k j l, ?_⟩
  intro x hx k j l
  have hi : M k j l ≤ total := calc
    _ ≤ ∑ a : OrderedPair, M k j a := Finset.single_le_sum (fun a _ => hM k j a) (Finset.mem_univ l)
    _ ≤ ∑ b : OrderedPair, ∑ a : OrderedPair, M k b a :=
      Finset.single_le_sum (fun b _ => Finset.sum_nonneg fun a _ => hM k b a) (Finset.mem_univ j)
    _ ≤ total := Finset.single_le_sum (fun c _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun a _ => hM c b a)
      (Finset.mem_univ k)
  obtain ⟨W, openW, inc, smooth, jet⟩ := estimates k j l x hx
  exact ⟨W, openW, inc, smooth, fun n hn y hy => (jet n hn y hy).trans hi⟩

end Burnett.V10.OriginalGaugeCompatibility
