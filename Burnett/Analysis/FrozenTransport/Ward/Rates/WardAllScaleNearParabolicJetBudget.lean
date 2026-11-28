import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicSmooth
import Burnett.Analysis.AllScaleTransfer.FixedAnnularCutoff

set_option autoImplicit false
set_option maxRecDepth 6400
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set
open Burnett.A02.FrequencySplit (Joint)
open Burnett.A05.BoxFourier
open scoped ContDiff

open private wardParabolicTestSegment wardParabolicTestSegment_smooth from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearParabolicSmooth

theorem wardParabolicTestDomain_open (ρ : ℝ) : IsOpen (wardParabolicTestDomain ρ) := by
  let T := Icc (0 : ℝ) 1
  letI : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  let F (p : WardParabolicTestPoint × T) := ‖wardParabolicTestSegment p.1 p.2‖
  have hc : Continuous F :=
    (wardParabolicTestSegment_smooth.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).norm
  have hClosed : IsClosed (Prod.fst '' {p : WardParabolicTestPoint × T | F p ≤ ρ}) :=
    isClosedMap_fst_of_compactSpace _ (isClosed_le hc continuous_const)
  have hEq : (wardParabolicTestDomain ρ)ᶜ =
      Prod.fst '' {p : WardParabolicTestPoint × T | F p ≤ ρ} := by
    ext p
    constructor
    · intro hp
      have hn : ¬∀ t ∈ Icc (0 : ℝ) 1, ρ < ‖wardParabolicTestSegment p t‖ := hp
      push_neg at hn
      obtain ⟨t, ht, h⟩ := hn
      exact ⟨(p,⟨t,ht⟩), h, rfl⟩
    · rintro ⟨⟨p',t⟩, ht, rfl⟩ hp
      exact (not_lt_of_ge ht) (hp t t.2)
  rw [← hEq] at hClosed
  exact isClosed_compl_iff.mp hClosed

/-- The normalized test coefficient has a single joint derivative bound
on any compact separated family of physical near interpolation charts. -/
theorem exists_wardParabolicTest_jetBound (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (ρ : ℝ) (hρ : 0 < ρ)
    (K : Set WardParabolicTestPoint) (hK : IsCompact K) (hSub : K ⊆ wardParabolicTestDomain ρ)
    (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n ≤ N, ∀ p ∈ K,
      ‖iteratedFDeriv ℝ n (wardJointParabolicTestRemainder a) p‖ ≤ D :=
  exists_compact_contDiffOn_jet_bound hK (wardParabolicTestDomain_open ρ)
    hSub (wardJointParabolicTestRemainder_contDiffOn a ha ρ hρ) N

end Burnett.C02
