import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearProfilesUniform
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearSymbolBound
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleNearSymbolMeasurable
import Burnett.Analysis.AngularCaps.ActualFieldCapAngularL3
import Burnett.Analysis.AngularCaps.UniformNullCapCharts
import Burnett.Geometry.InverseField

set_option autoImplicit false
set_option maxRecDepth 10500
set_option maxHeartbeats 20000000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps hiding Index
open Burnett.Analysis.CapFourier Burnett.A05
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.Geometry.InverseField (continuousOn_matrixInverse)
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- The original C02 pure physical near term has the A05 decay on a
compact frozen metric family with one fixed wide screen. The constants
and cone-prefactor range are chosen before the thin angular scale. -/
theorem exists_wardActualNearField_uniform (K V : Set E) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (G : E → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ c ∈ V, Matrix.det (G c) ≠ 0)
    (hFrame : ∀ c ∈ K, Nonempty (TensorFrame.LorentzFrame (inverseMatrix (G c))))
    (hGeoND : ∀ c ∈ K, Nondegenerate (inverseMatrix (G c)))
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ c ξ, a (c,-ξ) = -a (c,ξ))
    (hHom : ∀ c (t : ℝ), 0 < t → ∀ ξ, a (c,t • ξ) = t*a (c,ξ))
    (wi wo : ℝ) (hm : ∀ c ∈ K, WideScreenFrequencySmooth wi wo (inverseMatrix (G c)))
    (W : E → E → OrderedPair → OrderedPair → ℝ)
    (hW : ∀ k j, ContDiffOn ℝ ∞ (fun p : Joint => W p.1 p.2 k j) (V ×ˢ {u : E | u ≠ 0}))
    (hWide : ∀ c (hc : c ∈ K) ξ k j, W c ξ k j =
      (wideScreenAngular wi wo (inverseMatrix (G c)) (hm c hc)).matrix ξ k j)
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ ti thinOut q : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hti : 0 ≤ ti) (hThin : ti < thinOut) (hq : 3 < q) :
    ∃ c₀ δ₀ : ℝ, 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (cScale : ℝ) (hcScale : 0 < cScale), cScale ≤ c₀ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ c (hc : c ∈ K) δ (hδ : δ ∈ Ioc (0 : ℝ) δ₀) (z : ProjectionSchwartzMatrix),
        let η := cScale*κ*δ^2
        let hη : 0 < η := mul_pos (mul_pos hcScale hκ) (pow_pos hδ.1 _)
        let H := wardActualThinSpectrum (inverseMatrix (G c)) wi wo (hm c hc) hη ti thinOut z
        Integrable (fun p => (wardPurePhysicalNearWeight ϑ κ δ p : ℂ) *
          wardCyclicCubicWeight (G c) (fun ξ => a (c,ξ)) H H H p) ∧
        ‖wardActualNearCubicForm (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo (hm c hc) hη ti thinOut z‖ ≤
          C*δ^(2*(q-3)/(q-2))*‖schwartzFieldLp3 (wardNearGradient z)‖^3 := by
  classical
  let g (c : E) := inverseMatrix (G c)
  let Kmet := g '' K
  have hg : ContinuousOn g K := continuousOn_matrixInverse G K (hG.continuousOn.mono hKV)
    (fun x hx => hND x (hKV hx))
  have hKmet : IsCompact Kmet := hK.image_of_continuousOn hg
  have hFrame' : ∀ m ∈ Kmet, Nonempty (TensorFrame.LorentzFrame m) := by
    rintro m ⟨x,hx,rfl⟩
    exact hFrame x hx
  have hND' : ∀ m ∈ Kmet, Nondegenerate m := by
    rintro m ⟨x,hx,rfl⟩
    exact hGeoND x hx
  let ci := thinOut
  let co := thinOut+1
  let ce := thinOut+2
  have hto : 0 ≤ thinOut := hti.trans hThin.le
  have hci : 0 ≤ ci := hto
  have hico : ci < co := by dsimp [ci,co]; linarith
  have hco : 0 ≤ co := hci.trans hico.le
  have hce : co < ce := by dsimp [co,ce]; linarith
  obtain ⟨B,hB,hCharts⟩ := exists_uniform_nullCapCharts hKmet hFrame' hND'
  obtain ⟨cEdge,hcEdge,hEdges⟩ := exists_wardPurePhysicalNearWeight_all_edges hKmet hFrame' thinOut hto
  obtain ⟨D,cAng,δAng,hD,hcAng,hδAng,hδAng₁,hAngular⟩ :=
    exists_uniform_actual_capMultipliers_field_angular_L3 WardNearSlot hKmet hFrame' hND' hci hico hce
  let c₀ := min cEdge cAng
  let δ₀ := min δAng (1/(20*B))
  have hδ₀ : 0 < δ₀ := lt_min hδAng (one_div_pos.mpr (by positivity))
  have hδ₀₁ : δ₀ ≤ 1 := (min_le_left _ _).trans hδAng₁
  refine ⟨c₀,δ₀,lt_min hcEdge hcAng,hδ₀,hδ₀₁,?_⟩
  intro cScale hcScale hc₀
  let tube := cScale*κ
  have hTube : 0 < tube := mul_pos hcScale hκ
  obtain ⟨C₃,hC₃,Cang,hCang,hAng⟩ :=
    hAngular κ hκ hκsmall cScale hcScale (hc₀.trans (min_le_right _ _))
  let χ := descendingProfile κ (7*κ/4)
  have hχGap : κ < 7*κ/4 := by linarith only [hκ]
  have hχRange : ∀ t ≥ 0, ‖χ t‖ ≤ 1 := by
    intro t _
    have h := descendingProfile_range κ (7*κ/4) t
    rw [Real.norm_of_nonneg h.1]
    exact h.2
  obtain ⟨R,N,Cκ,hR,hR1,hCκ,applyNear⟩ :=
    exists_wardActualNearFieldBound_of_A05Profiles ϑ hϑ.continuous.measurable hRange hCut hFlat
      B tube co ce κ κ 1 hB hTube hco hce hκ hκsmall hκ (by linarith only [hκsmall])
      χ (descendingProfile_contDiff _ _) hχRange
      (fun t _ hx => descendingProfile_eq_one hχGap hx)
      (fun t hx => descendingProfile_eq_zero hχGap hx)
  obtain ⟨A,hA,profiles⟩ := exists_wardActualNearA05Profiles_uniform K V hK hV hKV G hG hND a ha hOdd hHom
    wi wo hm W hW hWide ϑ hϑ hCut hFlat B tube κ ti thinOut ci co ce R 1 hB hTube hκ hκsmall hti hThin hco hce hR1 N
  let C := Cang ⟨q,hq⟩
  have hC : 0 ≤ C := hCang _
  let Cnear := ((Cκ*(Fintype.card WardNearEntries : ℝ))*((Fintype.card WardNearSlot : ℝ)*C)^3*
    D^(1/(q-2)))*A
  have hCnear : 0 ≤ Cnear := by dsimp [Cnear]; positivity
  refine ⟨Cnear,hCnear,?_⟩
  intro c hc δ hδ z η hη H
  have hδAng' : δ ≤ δAng := hδ.2.trans (min_le_left _ _)
  have hδ' : δ ∈ Ioc (0:ℝ) 1 := ⟨hδ.1,hδ.2.trans hδ₀₁⟩
  have hSmall : 4*B*(5*δ) ≤ 1 := by
    have hb : δ ≤ 1/(20*B) := hδ.2.trans (min_le_right _ _)
    have e := (le_div_iff₀ (show 0 < 20*B by positivity)).mp hb
    nlinarith only [e]
  have hMet : g c ∈ Kmet := mem_image_of_mem g hc
  obtain ⟨S,P,Pplus,angular⟩ := hAng (g c) hMet δ hδ.1 hδAng'
  choose chart hF hI using (fun γ : ↑S.centers => hCharts (g c) hMet γ (S.centers_null γ.property))
  let sym := wardNearGradientSymbol (G c) (fun ξ => a (c,ξ)) ϑ κ δ wi wo (hm c hc) hη ti thinOut
  have ha' : ContDiffOn ℝ ∞ (fun ξ => a (c,ξ)) {ξ : E | ξ ≠ 0} :=
    ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)
  have hMeas (j : WardNearEntries) : Measurable (sym j) :=
    wardNearGradientSymbol_measurable (G c) (hND c (hKV hc)) (fun ξ => a (c,ξ)) ha' ϑ hϑ.continuous.measurable
      κ δ wi wo (hm c hc) hη ti thinOut j
  obtain ⟨Hmax,_,hMag⟩ := exists_wardNearGradientSymbol_bound (G c) (hND c (hKV hc)) (fun ξ => a (c,ξ))
    ha' (hOdd c) (hHom c) ϑ hRange κ δ wi wo (hm c hc) hη ti thinOut hti hThin
  have hHomSym (j : WardNearEntries) (t : ℝ) (ht : 0 < t) (p : Joint) :
      sym j (t • p) = sym j p :=
    wardNearGradientSymbol_homogeneous (G c) (hND c (hKV hc)) (fun ξ => a (c,ξ)) (hHom c)
      ϑ κ δ wi wo (hm c hc) hη ti thinOut j t ht p
  have hSupp (j : WardNearEntries) (x : Joint) (hx : sym j x ≠ 0) :
      |quadratic (g c) x.1| ≤ ci*(tube*δ^2)*‖x.1‖^2 ∧
      ∀ γ : ↑S.centers, capMultiplier S.centers (g c) δ (tube*δ^2) ci co γ x.1 ≠ 0 →
        enlargedCapMultiplier (g c) δ (tube*δ^2) co ce γ x.1 = 1 ∧
        enlargedCapMultiplier (g c) δ (tube*δ^2) co ce γ x.2 = 1 ∧
        enlargedCapMultiplier (g c) δ (tube*δ^2) co ce γ (-(x.1+x.2)) = 1 := by
    obtain ⟨hp,hq,hr,hNear,hP,hQ,hR⟩ := wardNearGradientSymbol_support (G c) (hND c (hKV hc))
      (fun ξ => a (c,ξ)) ϑ κ δ wi wo (hm c hc) hη ti thinOut hti hThin j x hx
    have e := hEdges (g c) hMet hCut hFlat hκ hκsmall hδ.1 hcScale (hc₀.trans (min_le_left _ _))
      x hp hq hr hP hQ hR hNear
    refine ⟨hP,?_⟩
    intro γ hCap
    exact (wardNear_capPlateaux S hη le_rfl hico.le γ hp hq hr hP hQ hR e.1 e.2.2 hCap).2
  have hProfiles : WardNearA05Profiles hδ.1.ne' S chart ϑ κ R 1 A N sym :=
    profiles c hc δ hδ' hSmall D S chart hF hI (fun j x hx => (hSupp j x hx).2)
  have hInt (j : WardNearEntries) := integrable_radianTrilinearWeight_of_bounded (sym j)
    (hMeas j).aestronglyMeasurable Hmax (hMag j)
    (wardNearGradient z j.1) (wardNearGradient z j.2.1) (wardNearGradient z j.2.2)
  have hActual := wardActualNearCubicForm_eq_gradientSum (G c) (hND c (hKV hc)) (fun ξ => a (c,ξ))
    ϑ κ δ wi wo (hm c hc) hη ti thinOut z hInt
  refine ⟨hActual.1,?_⟩
  exact applyNear (G c) (hND c (hKV hc)) (fun ξ => a (c,ξ)) wi wo (hm c hc)
    δ hδ' ti thinOut ci D C₃ S Pplus chart hF hI q A C Hmax hq hSmall hD hA hC
    (fun v => (angular ⟨q,hq⟩ v).2) hMeas hMag hHomSym (fun j p hp _ _ _ => hSupp j p hp) hProfiles z

end Burnett.C02
