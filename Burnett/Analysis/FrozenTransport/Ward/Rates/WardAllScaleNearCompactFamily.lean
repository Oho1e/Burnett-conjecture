import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFixedCapProfile
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileExtension
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfileAxes
import Burnett.Analysis.AngularCaps.ParabolicBaseTemplate

set_option autoImplicit false
set_option maxRecDepth 8600
set_option maxHeartbeats 12000000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.RicciSymbol Burnett.Analysis.ProjectiveNullCaps
open Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

open private wardNearProfileArgument_contDiff from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearFixedCapProfile
open private boundedCapNeighbors_compact fixed_baseCapProfileDomain from Burnett.Analysis.AngularCaps.ParabolicBaseTemplate

def wardNearParameterCompact (N : ℕ) (K : Set E) (B M : ℝ) : Set (WardNearProfileParameters N) :=
  (K ×ˢ boundedNullCoordinateMaps B ×ˢ Icc (0 : ℝ) 1) ×ˢ boundedCapNeighbors N M (1/2)

def wardNearProfileCompact (N : ℕ) (K : Set E) (B M R ρMax s₀ : ℝ) :
    Set (WardNearProfileInput N) :=
  (wardNearParameterCompact N K B M ×ˢ
    (closedBall (0 : NullFrequencyCoordinates) R ×ˢ closedBall (0 : NullFrequencyCoordinates) R ×ˢ Icc 0 ρMax)) ∩
      {x | ∀ j : Fin 3, s₀ ≤ |(wardNearProfileArguments x j).1|}

theorem wardNearParameterCompact_isCompact (N : ℕ) {K : Set E} (hK : IsCompact K) (B M : ℝ) :
    IsCompact (wardNearParameterCompact N K B M) :=
  (hK.prod ((boundedNullCoordinateMaps_compact B).prod isCompact_Icc)).prod
    (boundedCapNeighbors_compact N M (1/2))

theorem wardNearProfileCompact_isCompact (N : ℕ) {K : Set E} (hK : IsCompact K) (B M R ρMax s₀ : ℝ) :
    IsCompact (wardNearProfileCompact N K B M R ρMax s₀) := by
  have hQ : IsCompact (closedBall (0 : NullFrequencyCoordinates) R ×ˢ
      closedBall (0 : NullFrequencyCoordinates) R ×ˢ Icc 0 ρMax) :=
    (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hClosed : IsClosed {x : WardNearProfileInput N | ∀ j : Fin 3, s₀ ≤ |(wardNearProfileArguments x j).1|} := by
    rw [show {x : WardNearProfileInput N | ∀ j : Fin 3, s₀ ≤ |(wardNearProfileArguments x j).1|} =
      ⋂ j : Fin 3, {x | s₀ ≤ |(wardNearProfileArguments x j).1|} by ext x; simp]
    exact isClosed_iInter fun j => isClosed_le continuous_const
      (wardNearProfileArgument_contDiff (N := N) j).fst.continuous.abs
  exact ((wardNearParameterCompact_isCompact N hK B M).prod hQ).inter_right hClosed

theorem wardNearProfileCompact_subset_domain (N : ℕ) {K V : Set E} (hKV : K ⊆ V)
    (B M R ρMax s₀ tube b : ℝ) (hB : 0 ≤ B) (hs₀ : 0 < s₀) (ht : tube ≠ 0)
    (hb : B*b < s₀) (slot : Fin 3) :
    wardNearProfileCompact N K B M R ρMax s₀ ⊆ wardParabolicNearProfileDomain N V tube b slot := by
  intro x hx
  let F := x.1.1.2.1
  let δ := x.1.1.2.2
  let c := x.1.1.1
  have hF : F ∈ boundedNullCoordinateMaps B := hx.1.1.1.2.1
  have hv : x.1.2 ∈ boundedCapNeighbors N M (1/2) := hx.1.1.2
  have hc : c ∈ V := hKV hx.1.1.1.1
  have hax (j : Fin 3) : s₀ ≤ |(wardNearProfileArguments x j).1| := hx.2 j
  have hz (j : Fin 3) : (wardNearProfileArguments x j).1 ≠ 0 :=
    abs_pos.mp (hs₀.trans_le (hax j))
  have hn (j : Fin 3) : F (parabolicDilation δ (wardNearProfileArguments x j)) ≠ 0 := by
    intro he
    have h := hF.2 (parabolicDilation δ (wardNearProfileArguments x j))
    rw [he,norm_zero,mul_zero,norm_le_zero_iff] at h
    exact parabolicDilation_ne_zero_of_s (hz j) h
  have hCap : wardNearProfileCapPoint tube slot x ∈ baseCapProfileDomain N :=
    fixed_baseCapProfileDomain hF ht (hax slot) hs₀ hv (by norm_num : (0:ℝ) < 1/2)
  refine ⟨⟨⟨hc,hn 0⟩,⟨hc,hn 1⟩,⟨hc,hn 2⟩⟩,hCap,?_⟩
  intro j
  exact ⟨hz j,wardParabolicTestDomain_of_axis hB hF.2 c δ (wardNearProfileArguments x j) (hb.trans_le (hax j))⟩

/-- Joint compact extensions for the actual local near expressions, with
all cap widths in the same compact family. This construction leaves room
for the three signed endpoint charts and the finite comparable shifts. -/
theorem exists_wardParabolicNearCompactProfile {N : ℕ} (K V : Set E)
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (G : E → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ x ∈ V, Matrix.det (G x) ≠ 0)
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (M : WardParabolicTestPoint → ℝ) (hM : ContDiff ℝ ∞ M)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (κ tube thinIn thinOut capIn capOut B Rv R ρMax s₀ b : ℝ)
    (hκ : κ ≠ 0) (hTube : tube ≠ 0) (hB : 0 ≤ B) (hs₀ : 0 < s₀) (hb : B*b < s₀)
    (comparable : Bool) (s : Fin 3) (j : WardNearEntries) :
    let T := wardNearProfileCompact N K B Rv R ρMax s₀
    let U := wardParabolicNearProfileDomain N V tube b s
    let f := wardParabolicNearProfile G W M ϑ κ tube thinIn thinOut capIn capOut comparable s j
    ∃ F : WardNearProfileInput N → ℂ,
      ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      ∀ (x : WardNearProfileInput N) (g : ℂ), (g ≠ 0 → x ∈ T) → (x ∈ U → f x = g) → F x = g := by
  intro T U f
  have hT : IsCompact T := wardNearProfileCompact_isCompact N hK B Rv R ρMax s₀
  have hU : IsOpen U := wardParabolicNearProfileDomain_open hV N tube b s
  have hTU : T ⊆ U := wardNearProfileCompact_subset_domain N hKV B Rv R ρMax s₀ tube b hB hs₀ hTube hb s
  have hf : ContDiffOn ℝ ∞ f U := wardParabolicNearProfile_contDiffOn V G hG hND W hW M hM ϑ hϑ
    κ tube thinIn thinOut capIn capOut b hκ hTube comparable s j
  obtain ⟨χ,_,_,hSupp,hχ,hSmooth,hCompact⟩ := exists_wardCompactProfile_extension hU hT hTU f hf
  refine ⟨fun x => (χ x : ℂ)*f x,hSmooth,hCompact,?_⟩
  intro x g hg hLocal
  change (χ x : ℂ)*f x = g
  by_cases hn : g = 0
  · by_cases hx : x ∈ U
    · rw [hLocal hx,hn,mul_zero]
    · have hχ₀ : χ x = 0 := by
        by_contra he
        exact hx (hSupp (subset_tsupport _ he))
      rw [hχ₀,Complex.ofReal_zero,zero_mul,hn]
  · have hx := hg hn
    rw [hχ x hx,Complex.ofReal_one,one_mul,hLocal (hTU hx)]

end Burnett.C02
