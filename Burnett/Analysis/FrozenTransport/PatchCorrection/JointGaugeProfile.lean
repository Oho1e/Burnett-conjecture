import Burnett.Analysis.FrozenTransport.PatchCorrection.UniformAngularJets
import Burnett.Analysis.FrozenTransport.PatchCorrection.ParameterizedCyclicPhase
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeScreenContraction

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 5500
noncomputable section
namespace Burnett.V11
open Set Metric Matrix Burnett.P01 Burnett.V08 Burnett.V06
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight)
open scoped ContDiff Matrix BigOperators

theorem exists_actualGauge_compact_jets (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (sub : K ⊆ U)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) (hκ : 0 < κ) (m : E → ScreenMatrix)
    (hm : ∀ i j, ContDiffOn ℝ ∞ (fun x => m x i j) U) (w : E → ℝ) (hw : ContDiffOn ℝ ∞ w U)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (S : E → GaugeScreen)
    (hs : ∀ i j, ContDiffOn ℝ ∞ (fun p : Joint => S p.1 p.2 i j) (U ×ˢ {t : E | t ≠ 0})) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ k I J, GaugeProfileBound N M
      (gaugeTriadAngularProfile θ κ (m x) (w x) (fun y => a (x,y)) (gaugeFrozenContraction (m x)) (S x) k I J) := by
  classical
  let O := U ×ˢ gaugePhaseWindow
  have oo : IsOpen O := hU.prod gaugePhaseWindow_open
  have subQ : K ×ˢ gaugeAngularWindow ⊆ O := by
    intro p hp
    have lo := mem_sphere_zero_iff_norm.mp hp.2.2
    have hi := mem_sphere_zero_iff_norm.mp hp.2.1.2
    have r := mem_closedBall_zero_iff.mp hp.2.1.1
    refine ⟨sub hp.1,?_,?_,?_⟩ <;> dsimp <;> linarith
  let X := E × (Joint × E)
  let c (p : E × (Joint × E)) := p.1
  let d (p : E × (Joint × E)) := p.2.2
  let r (p : E × (Joint × E)) := p.2.1.1
  let h (p : E × (Joint × E)) := p.2.1.2
  have dc : ContDiff ℝ ∞ c := contDiff_fst
  have dd : ContDiff ℝ ∞ d := contDiff_snd.comp contDiff_snd
  have dr : ContDiff ℝ ∞ r := (contDiff_fst.comp contDiff_fst).comp contDiff_snd
  have dh : ContDiff ℝ ∞ h := (contDiff_snd.comp contDiff_fst).comp contDiff_snd
  have hc (i j : Fin 4) := (hm i j).comp dc.contDiffOn (show MapsTo c O U from fun x hx => hx.1)
  have contr (i j : TensorSlot) : ContDiffOn ℝ ∞ (fun p => gaugeFrozenContraction (m (c p)) i j) O :=
    (((hc i.1 j.1).mul (hc i.2 j.2)).sub (((hc i.1 i.2).mul (hc j.1 j.2)).div_const 2)).div_const 4
  have pos (p : X) (hp : p ∈ O) : 0 < ‖h p‖ := lt_trans (by norm_num : (0:ℝ)<3/4) hp.2.2.2
  have inp (i j : TensorSlot) := (hs i j).comp (dc.prodMk dh).contDiffOn
    (show MapsTo (fun x => (c x,h x)) O _ from fun x hx => ⟨hx.1,norm_pos_iff.mp (pos x hx)⟩)
  have out (i j : TensorSlot) := (hs i j).comp (dc.prodMk (dr.add dh)).contDiffOn
    (show MapsTo (fun x => (c x,r x+h x)) O _ from by
      intro p hp; refine ⟨hp.1,?_⟩; intro eq
      have hv : h p = -(r p) := eq_neg_of_add_eq_zero_right eq
      have a : ‖r p‖ < 1/2 := hp.2.2.1
      have b : 3/4 < ‖h p‖ := hp.2.2.2
      rw [hv,norm_neg] at b; linarith)
  have mask : ContDiffOn ℝ ∞ (fun p => (lowSlotWeight θ κ (r p) (h p) (-(r p+h p)) : ℂ)) O := by
    simp only [lowSlotWeight, norm_neg]
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn (hθ.comp_contDiffOn ?_)
    exact (dr.norm_sq ℝ).contDiffOn.div (contDiff_const.mul ((dh.norm_sq ℝ).add ((dr.add dh).norm_sq ℝ))).contDiffOn
      (fun x hx => (mul_pos (pow_pos hκ _) (add_pos_of_pos_of_nonneg (pow_pos (pos x hx) _) (sq_nonneg _))).ne')
  have phase := (parametric_cyclicLowNormalizedPhase a ha).mono (show O ⊆ univ ×ˢ gaugePhaseWindow from fun p hp => ⟨mem_univ _,hp.2⟩)
  have factor := Complex.ofRealCLM.contDiff.comp_contDiffOn (((hw.comp dc.contDiffOn (fun _ hx => hx.1)).div_const 3).mul phase)
  let F (k I J : TensorSlot) (p : E × (Joint × E)) := gaugeTriadAngularProfile θ κ (m p.1) (w p.1)
    (fun y => a (p.1,y)) (gaugeFrozenContraction (m p.1)) (S p.1) k I J p.2
  have smooth (k I J : TensorSlot) : ContDiffOn ℝ ∞ (F k I J) O := by
    have mat : ContDiffOn ℝ ∞ (fun p => lowGaugeHighMatrix (gaugeFrozenContraction (m (c p))) (S (c p)) (r p) (h p) I J) O := by
      simp only [lowGaugeHighMatrix,Matrix.mul_apply,Matrix.transpose_apply]
      exact ContDiffOn.sum fun u _ => (ContDiffOn.sum fun v _ => (out v I).mul (contr v u)).mul (inp u J)
    have coord (i : Fin 4) := Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp (dh.add (dr.add dh)))
    have diff : ContDiffOn ℝ ∞ (fun p => lowGaugeNormalizedHighDifference (m (c p)) (gaugeEntryBasis k) (d p) (r p) (h p)) O := by
      simp only [lowGaugeNormalizedHighDifference,lowGaugeHighDifference]
      exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ((Complex.ofRealCLM.contDiff.comp_contDiffOn (hc i j)).mul
        ((normalizedGaugePotential_contDiff (gaugeEntryBasis k) j).comp dd).contDiffOn).mul (coord i).contDiffOn
    exact mask.mul ((factor.mul diff).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn mat))
  choose A hA bounds using fun k I J => exists_uniform_frozen_angular_jets K hK (F k I J) O oo subQ (smooth k I J) N
  let B := ∑ k : TensorSlot, ∑ I : TensorSlot, ∑ J : TensorSlot, A k I J
  refine ⟨B,Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun J _ => hA k I J,?_⟩
  intro x hx k I J
  have le : A k I J ≤ B := calc
    _ ≤ ∑ j : TensorSlot, A k I j := Finset.single_le_sum (fun j _ => hA k I j) (Finset.mem_univ J)
    _ ≤ ∑ i : TensorSlot, ∑ j : TensorSlot, A k i j := Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hA k i j) (Finset.mem_univ I)
    _ ≤ B := Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA k i j) (Finset.mem_univ k)
  obtain ⟨V,vOpen,vSub,vSmooth,jet⟩ := bounds k I J x hx
  exact ⟨V,vOpen,vSub,vSmooth,fun n hn y hy => (jet n hn y hy).trans le⟩

end Burnett.V11
