import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearLowProfileBinding
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearComparableProfileBinding
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearA05Consumer

set_option autoImplicit false
set_option maxRecDepth 10200
set_option maxHeartbeats 18000000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory
open Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol Burnett.A05 Burnett.A05.BoxFourier
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.Analysis.CapFourier
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

/-- The original signed endpoint and shifted comparable witnesses can
both be chosen with one jet budget before the thin width is chosen. -/
theorem exists_wardActualNearA05Profiles_uniform (K V : Set E) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (G : E → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ c ∈ V, Matrix.det (G c) ≠ 0)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ c ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ c (t : ℝ), 0 < t → ∀ ξ, a (c,t • ξ) = t*a (c,ξ))
    (wi wo : ℝ) (hm : ∀ c ∈ K, WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (hWide : ∀ c (hc : c ∈ K) ξ k j, W c ξ k j =
      (wideScreenAngular wi wo (inverseMatrix (G c)) (hm c hc)).matrix ξ k j)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube κ ti thinOut ci co ce R b : ℝ)
    (hB : 0 < B) (hTube : 0 < tube) (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (hti : 0 ≤ ti) (hThin : ti < thinOut) (hCo : 0 ≤ co) (hCe : co < ce) (hR : R < 1) (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c (hc : c ∈ K) δ (hδ : δ ∈ Ioc (0 : ℝ) 1), 4*B*(5*δ) ≤ 1 →
      ∀ (D : ℝ) (S : SmoothThinConeCaps (inverseMatrix (G c)) δ (tube*δ^2) ci co ce D)
        (chart : ∀ γ : ↑S.centers, NullCapChart (inverseMatrix (G c)) γ),
      (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) →
      (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) →
      let hη : 0 < tube*δ^2 := mul_pos hTube (pow_pos hδ.1 _)
      let sym := wardNearGradientSymbol (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo (hm c hc) hη ti thinOut
      (∀ (j : WardNearEntries) (y : Joint), sym j y ≠ 0 →
        ∀ γ : ↑S.centers, capMultiplier S.centers (inverseMatrix (G c)) δ (tube*δ^2) ci co γ y.1 ≠ 0 →
          enlargedCapMultiplier (inverseMatrix (G c)) δ (tube*δ^2) co ce γ y.1 = 1 ∧
          enlargedCapMultiplier (inverseMatrix (G c)) δ (tube*δ^2) co ce γ y.2 = 1 ∧
          enlargedCapMultiplier (inverseMatrix (G c)) δ (tube*δ^2) co ce γ (-(y.1+y.2)) = 1) →
      WardNearA05Profiles hδ.1.ne' S chart ϑ κ R b A N sym := by
  classical
  obtain ⟨α,hα,_,hAxis⟩ := exists_enlarged_cap_support_axial_margin B tube co ce hB hTube hCo hCe
  let L := α/B
  let U := B*(‖frequencyCoordinates.toContinuousLinearMap‖+1)
  have hL : 0 < L := div_pos hα hB
  have hU : 0 < U := by dsimp [U]; positivity
  let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let T : ℝ := 2+(∑ k ∈ I, 2*(2 : ℝ)^k)
  have hT : 1 ≤ T := by
    have h : 0 ≤ ∑ k ∈ I, 2*(2 : ℝ)^k := Finset.sum_nonneg (fun _ _ => by positivity)
    dsimp only [T]
    linarith only [h]
  let Rbig := ‖frequencyCoordinates.toContinuousLinearMap‖*T
  have hRbig : ‖frequencyCoordinates.toContinuousLinearMap‖ ≤ Rbig :=
    le_mul_of_one_le_right (norm_nonneg _) hT
  let ρMax := max 1 (b*U/L)
  let s₀ := min (min α (α*(L/(2*U)))) (min (α/2) (α*(κ*L/(4*U))))
  have hs₀ : 0 < s₀ := lt_min (lt_min hα (by positivity))
    (lt_min (half_pos hα) (by positivity))
  have hs₀α : s₀ ≤ α := (min_le_left _ _).trans (min_le_left _ _)
  have hs₀L : s₀ ≤ α*(L/(2*U)) := (min_le_left _ _).trans (min_le_right _ _)
  have hs₀C : s₀ ≤ min (α/2) (α*(κ*L/(4*U))) := min_le_right _ _
  let d₀ := s₀/(2*(B+1))
  have hd₀ : 0 < d₀ := div_pos hs₀ (by positivity)
  have hD₀ : B*d₀ < s₀ := by
    dsimp only [d₀]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(B+1))).mpr
    nlinarith only [mul_pos hB hs₀,hs₀]
  obtain ⟨M,hM,hMExact⟩ := exists_wardJointParabolicTestRemainder_extension a ha d₀ hd₀
  let Ncap : ℕ := 33^4
  let Rv := max 1 (max B (max (16*B^2) ((16*B)^2*B)))
  let P := wardNearParameterCompact Ncap K B Rv
  have hP : IsCompact P := wardNearParameterCompact_isCompact Ncap hK B Rv
  choose Flo hLo hLoSupp hLoExact using (fun k : Fin 3 × WardNearEntries =>
    exists_wardParabolicNearCompactProfile (N := Ncap) K V hK hV hKV G hG hND W hW M hM ϑ hϑ
      κ tube ti thinOut ci co B Rv Rbig ρMax s₀ d₀ hκ.ne' hTube.ne' hB.le hs₀ hD₀ false
      (wardNearRotateCap k.1) (wardNearRotateEntries k.1 k.2))
  choose Fco hCoSmooth hCoSupp hCoExact using (fun j : WardNearEntries =>
    exists_wardParabolicNearCompactProfile (N := Ncap) K V hK hV hKV G hG hND W hW M hM ϑ hϑ
      κ tube ti thinOut ci co B Rv Rbig ρMax s₀ d₀ hκ.ne' hTube.ne' hB.le hs₀ hD₀ true 0 j)
  choose Alo Blo hAlo hLoJets using (fun k : Fin 3 × WardNearEntries =>
    exists_wardNearEndpointProfile_jets (Flo k) (hLo k) (hLoSupp k) hP R b L hR hL)
  choose Aco hAco hCoJets using (fun j : WardNearEntries =>
    exists_wardNearComparableBox_jets (Fco j) (hCoSmooth j) hP I)
  let A := (∑ k, Alo k)+(∑ j, Aco j)
  have hAs₁ : 0 ≤ ∑ k, Alo k := Finset.sum_nonneg (fun k _ => hAlo k)
  have hAs₂ : 0 ≤ ∑ j, Aco j := Finset.sum_nonneg (fun j _ => hAco j)
  have leA₁ (k : Fin 3 × WardNearEntries) : Alo k ≤ A :=
    (Finset.single_le_sum (fun j _ => hAlo j) (Finset.mem_univ k)).trans (le_add_of_nonneg_right hAs₂)
  have leA₂ (j : WardNearEntries) : Aco j ≤ A :=
    (Finset.single_le_sum (fun j' _ => hAco j') (Finset.mem_univ j)).trans (le_add_of_nonneg_left hAs₁)
  refine ⟨A,add_nonneg hAs₁ hAs₂,?_⟩
  intro c hc δ hδ hSmall D S chart hF hI hη sym hSupport γ j aCap Kcap μ bases low comparable I'
  let F := chart γ
  have hw : ‖(γ : E)‖ = 1 := (S.centers_null γ.property).1
  have hSmall' : 4*B*(4*δ) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (by linarith only [hδ.1] : 4*δ ≤ 5*δ) (by positivity)).trans hSmall
  obtain ⟨vCap,hvCap,hEncoded⟩ := exists_wardBaseCapProfile_exact F S.centers S.centers_null B tube ci co δ
    hB (hI γ) hw hδ.1 hSmall' S.centers_separated
  let p₀ : WardNearProfileParameters Ncap := ((c,F.toFrequency.toContinuousLinearMap,δ),vCap)
  have hParam : p₀ ∈ P := ⟨⟨hc,chart_mem_boundedNullCoordinateMaps F (hF γ) (hI γ),hδ.1.le,hδ.2⟩,hvCap⟩
  have hAx (x : E) (hx : aCap x ∈ Kcap) : α*‖x‖ ≤ |x 0| :=
    hAxis (inverseMatrix (G c)) γ F hw (hI γ) δ hδ.1 hSmall x hx
  have hLower (x : E) (hx : α*‖x‖ ≤ |(frequencyCoordinates x).1|) : L*‖x‖ ≤ ‖aCap x‖ :=
    capFrequencyEquiv_lower_on_axial_cone F hδ.1.ne' hB (hI γ) hx
  have hUpper (x : E) : ‖aCap x‖ ≤ U*‖x‖ := by
    have hb := (aCap.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (capFrequencyEquiv_opNorm_le F hδ.1 hδ.2 hB.le (hF γ)) (norm_nonneg x))
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hB.le) (norm_nonneg x))
  let Lo (k : Fin 3) := wardNearEndpointProfile (Flo (k,j)) L p₀
  let B₀ := ∑ k : Fin 3, max (Blo (k,j)) 0
  have hB₀ (k : Fin 3) : Blo (k,j) ≤ B₀ := by
    have hSum : max (Blo (k,j)) 0 ≤ ∑ i : Fin 3, max (Blo (i,j)) 0 :=
      Finset.single_le_sum (fun i _ => le_max_right (Blo (i,j)) (0 : ℝ)) (Finset.mem_univ k)
    exact (le_max_left _ _).trans hSum
  refine ⟨⟨Lo,B₀,?_,?_,?_,?_,?_⟩,⟨wardNearComparableBoxProfile (Fco j) p₀,?_,?_,?_⟩⟩
  · exact fun k => (hLoJets (k,j) p₀ hParam).1
  · exact fun k p => ((hLoJets (k,j) p₀ hParam).2.1 p).trans (hB₀ k)
  · exact fun k s => (hLoJets (k,j) p₀ hParam).2.2.1 s
  · exact fun k s n hn z hz => ((hLoJets (k,j) p₀ hParam).2.2.2 s n hn z hz).trans (leA₁ (k,j))
  · intro k p hp hq hr hr'
    exact wardNearLowProfileBinding K V G c (hND c (hKV hc)) a ha (hOdd c) (hHom c) W M hM d₀ hMExact
      ϑ hCut κ hκ hκsmall tube δ ti thinOut ci co ce D wi wo hδ.1.ne' hη (hm c hc) (hWide c hc) S γ F vCap
      B Rv Rbig ρMax s₀ L α L U b hParam hEncoded hL le_rfl hα.le hU hRbig (le_max_right _ _) hs₀α hs₀L
      j k (Flo (k,j)) (hLoExact (k,j)) hAx hUpper hLower p hp hq hr hr'
  · exact (hCoJets j p₀ hParam).1
  · exact fun k hk n hn z hz => ((hCoJets j p₀ hParam).2 k hk n hn z hz).trans (leA₂ j)
  · intro k hk ζ υ hζ hυ
    have hζN := (endpointHighProfile_properties.2.2 ζ hζ).2.le
    have hυN := (endpointHighProfile_properties.2.2 υ hυ).2.le
    have hZpow : 0 ≤ (2:ℝ)^k := by positivity
    have hc₁ : 2*(2:ℝ)^k ≤ T := by
      have hNonneg : ∀ i ∈ I, 0 ≤ 2*(2:ℝ)^i := fun _ _ => by positivity
      have e := Finset.single_le_sum hNonneg hk
      dsimp only [T]
      linarith only [e]
    have hc₂ : 2 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
    have hζB : ‖frequencyCoordinates ((2:ℝ)^k • ζ)‖ ≤ Rbig := by
      apply (frequencyCoordinates.toContinuousLinearMap.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [norm_smul,Real.norm_of_nonneg hZpow]
      exact ((mul_le_mul_of_nonneg_left hζN hZpow).trans_eq (mul_comm _ _)).trans hc₁
    have hυB : ‖frequencyCoordinates υ‖ ≤ Rbig :=
      (frequencyCoordinates.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hυN.trans hc₂) (norm_nonneg _))
    have hAx' (x : E) (hx : x ∈ Kcap) :
        α*‖aCap.symm x‖ ≤ |(frequencyCoordinates (aCap.symm x)).1| := by
      rw [frequencyCoordinates_axis]
      apply hAx
      rwa [aCap.apply_symm_apply]
    exact wardNearComparableProfileBinding K V G c (hND c (hKV hc)) a ha (hOdd c) (hHom c)
      W M hM d₀ hMExact ϑ hCut hFlat κ hκ hκsmall tube δ ti thinOut ci co ce D wi wo hδ.1.ne' hη hti hThin
      (hm c hc) (hWide c hc) S γ F vCap B Rv Rbig ρMax s₀ α L U hParam hEncoded
      (le_max_left _ _) hα hL hU hs₀C j (Fco j) k ζ υ hυ hζB hυB (hCoExact j) hAx' hUpper hLower
      (fun y hy hp => hSupport j y hy γ hp)

end Burnett.C02
