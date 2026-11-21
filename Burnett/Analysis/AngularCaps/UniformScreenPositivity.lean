import Burnett.Analysis.AngularCaps.UniformNullCompanion
import Burnett.Algebra.MinkowskiNull

set_option autoImplicit false
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Set Finset Metric
open scoped BigOperators
open Burnett.RicciSymbol

def screenOrthogonal (m : Form) (w n x : Vec) : Prop :=
  pairing m w x = 0 ∧ pairing m n x = 0

private theorem quadratic_eq_symbolNorm (m : Form) (x : Vec) :
    quadratic m x = symbolNorm m (fun i => x i) := by
  simp only [quadratic,pairing,rowValue,symbolNorm,Finset.sum_mul]
  exact Finset.sum_comm

private def inLorentzFrame {m : Form} (f : TensorFrame.LorentzFrame m) (x : Vec) : Covector :=
  TensorFrame.covector f.components (fun i => x i)

private theorem quadratic_lorentz_coordinates {m : Form} (f : TensorFrame.LorentzFrame m) (x : Vec) :
    quadratic m x = -(inLorentzFrame f x 0)^2 + (inLorentzFrame f x 1)^2 +
      (inLorentzFrame f x 2)^2 + (inLorentzFrame f x 3)^2 := by
  conv_lhs => rw [quadratic_eq_symbolNorm,← f.inverseMetric_eq,TensorFrame.symbolNorm_transform]
  exact MinkowskiNull.symbolNorm_eq_coordinates _

private theorem temporal_sub_smul {m : Form} (f : TensorFrame.LorentzFrame m) (z t : Vec) (a : ℝ) :
    inLorentzFrame f (z-a • t) 0 = inLorentzFrame f z 0-a*inLorentzFrame f t 0 := by
  simp only [inLorentzFrame,TensorFrame.covector,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The screen of this Lorentz signature is positive. The pair has both
quadratic values zero and mixed value `-1/2`, so its sum is timelike. -/
theorem screen_quadratic_pos {m : Form} (f : TensorFrame.LorentzFrame m) {w n z : Vec}
    (hw : w ∈ unitNull m) (hn : complementaryNullAxis m w n)
    (hzScreen : screenOrthogonal m w n z) (hz : z ≠ 0) :
    0 < quadratic m z := by
  have hSym := lorentzFrame_symm f
  let t := w+n
  have hQt : quadratic m t = -1 := by
    simp only [t,quadratic_add hSym,hw.2,hn.1,hn.2]
    norm_num
  have hTZ : pairing m z t = 0 := by
    rw [pairing_symm hSym z t]
    simp only [t,pairing_add_left,hzScreen.1,hzScreen.2,add_zero]
  have ht0 : inLorentzFrame f t 0 ≠ 0 := by
    intro h
    have ht := quadratic_lorentz_coordinates f t
    rw [hQt,h] at ht
    nlinarith only [ht,sq_nonneg (inLorentzFrame f t 1),sq_nonneg (inLorentzFrame f t 2),
      sq_nonneg (inLorentzFrame f t 3)]
  let a := inLorentzFrame f z 0/inLorentzFrame f t 0
  let u := z-a • t
  have hu0 : inLorentzFrame f u 0 = 0 := by
    change inLorentzFrame f (z-a • t) 0 = 0
    rw [temporal_sub_smul]
    dsimp only [a]
    rw [div_mul_cancel₀ _ ht0,sub_self]
  have hUQ0 : 0 ≤ quadratic m u := by
    rw [quadratic_lorentz_coordinates f,hu0]
    positivity
  have hUQ : quadratic m u = quadratic m z-a^2 := by
    simp only [u,quadratic_sub hSym,quadratic_smul,pairing_smul_right,hQt,hTZ]
    ring
  have hZQ : 0 ≤ quadratic m z := by linarith only [hUQ,hUQ0,sq_nonneg a]
  by_contra! hNot
  have hZero : quadratic m z = 0 := hNot.antisymm hZQ
  have hw0 : w ≠ 0 := by
    intro h
    have hW : ‖w‖ = 1 := hw.1
    simp [h] at hW
  obtain ⟨s,hs⟩ := lorentzFrame_nullLinesUnique f w z hw0 hw.2 hZero hzScreen.1
  have hNS : pairing m n w = -1/2 := (pairing_symm hSym n w).trans hn.2
  have hZ := hzScreen.2
  rw [hs,pairing_smul_right,hNS] at hZ
  have hs0 : s = 0 := by linarith only [hZ]
  exact hz (by simp [hs,hs0])

private abbrev ScreenData := Form × Vec × Vec × Vec

private def positiveScreenConfigurations (K : Set Form) (L : ℝ) : Set ScreenData :=
  (K ×ˢ (sphere (0 : Vec) 1 ×ˢ (closedBall (0 : Vec) L ×ˢ sphere (0 : Vec) 1))) ∩
      ({z | quadratic z.1 z.2.1 = 0}
        ∩ ({z | quadratic z.1 z.2.2.1 = 0}
        ∩ ({z | pairing z.1 z.2.1 z.2.2.1 = -1/2}
        ∩ ({z | pairing z.1 z.2.1 z.2.2.2 = 0}
        ∩ {z | pairing z.1 z.2.2.1 z.2.2.2 = 0}))))

private theorem positiveScreenConfigurations_compact {K : Set Form} (hK : IsCompact K) (L : ℝ) :
    IsCompact (positiveScreenConfigurations K L) := by
  have hm : Continuous (fun x : ScreenData => x.1) := continuous_fst
  have hw : Continuous (fun x : ScreenData => x.2.1) := continuous_snd.fst
  have hn : Continuous (fun x : ScreenData => x.2.2.1) := continuous_snd.snd.fst
  have hz : Continuous (fun x : ScreenData => x.2.2.2) := continuous_snd.snd.snd
  exact (hK.prod ((isCompact_sphere _ _).prod ((isCompact_closedBall _ _).prod (isCompact_sphere _ _)))).inter_right
    ((isClosed_eq (continuous_pairing_family hm hw hw) continuous_const).inter
      ((isClosed_eq (continuous_pairing_family hm hn hn) continuous_const).inter
      ((isClosed_eq (continuous_pairing_family hm hw hn) continuous_const).inter
      ((isClosed_eq (continuous_pairing_family hm hw hz) continuous_const).inter
      (isClosed_eq (continuous_pairing_family hm hn hz) continuous_const)))))

/-- Positivity on the unit screen has a common strict lower bound over all
true centers and every complementary null axis with the fixed norm bound.
No continuous choice of either axis is required. -/
theorem exists_uniform_unitScreen_quadratic_lower {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (TensorFrame.LorentzFrame m)) (L : ℝ) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ m ∈ K, ∀ w ∈ unitNull m, ∀ n : Vec,
      complementaryNullAxis m w n → ‖n‖ ≤ L → ∀ x : Vec,
      ‖x‖ = 1 → screenOrthogonal m w n x → ℓ ≤ quadratic m x := by
  let S := positiveScreenConfigurations K L
  have hMem (m : Form) (hm : m ∈ K) (w : Vec) (hw : w ∈ unitNull m) (n : Vec)
      (hn : complementaryNullAxis m w n) (hN : ‖n‖ ≤ L) (x : Vec) (hx : ‖x‖ = 1)
      (hScreen : screenOrthogonal m w n x) : (m,w,n,x) ∈ S :=
    ⟨⟨hm,by simpa only [mem_sphere,dist_zero_right] using hw.1,
         by simpa only [mem_closedBall,dist_zero_right] using hN,
         by simpa only [mem_sphere,dist_zero_right] using hx⟩,
      hw.2,hn.1,hn.2,hScreen.1,hScreen.2⟩
  by_cases hS : S.Nonempty
  · have hCont : Continuous (fun z : ScreenData => quadratic z.1 z.2.2.2) :=
      continuous_pairing_family continuous_fst continuous_snd.snd.snd continuous_snd.snd.snd
    obtain ⟨z,hz,hMin⟩ := (positiveScreenConfigurations_compact hK L).exists_isMinOn hS hCont.continuousOn
    have hW : z.2.1 ∈ unitNull z.1 :=
      ⟨by simpa only [mem_sphere,dist_zero_right] using hz.1.2.1,hz.2.1⟩
    have hN : complementaryNullAxis z.1 z.2.1 z.2.2.1 := ⟨hz.2.2.1,hz.2.2.2.1⟩
    have hScreen : screenOrthogonal z.1 z.2.1 z.2.2.1 z.2.2.2 :=
      ⟨hz.2.2.2.2.1,hz.2.2.2.2.2⟩
    have hNorm : ‖z.2.2.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz.1.2.2.2
    have hNZ : z.2.2.2 ≠ 0 := by intro he; simp [he] at hNorm
    have hPos : 0 < quadratic z.1 z.2.2.2 :=
      (hFrame z.1 hz.1.1).elim (fun f => screen_quadratic_pos f hW hN hScreen hNZ)
    exact ⟨quadratic z.1 z.2.2.2,hPos,fun m hm w hw n hn hN x hx hScreen =>
      (isMinOn_iff.mp hMin) _ (hMem m hm w hw n hn hN x hx hScreen)⟩
  · refine ⟨1,zero_lt_one,?_⟩
    intro m hm w hw n hn hN x hx hScreen
    exact (hS ⟨(m,w,n,x),hMem m hm w hw n hn hN x hx hScreen⟩).elim

end Burnett.Analysis.ProjectiveNullCaps
