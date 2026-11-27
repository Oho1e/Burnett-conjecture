import Burnett.Analysis.AngularCaps.ActualFieldCapAngularL3
import Burnett.Analysis.AngularCaps.UniformNullCapCharts

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C02

open Set MeasureTheory
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

/-- Actual enlarged caps, uniformly bounded signed null charts, and
the per-cap scalar angular bound on the same compact metric family. -/
theorem exists_analyticNear_uniform_capInputs
    {K : Set Form} (hK : IsCompact K) (hFrame : ∀ metric ∈ K, Nonempty (LorentzFrame metric))
    (hND : ∀ metric ∈ K, Nondegenerate metric)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ B D c₀ δ₀ : ℝ, 0 < B ∧ 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ (C₃ : ℝ) (C : {q : ℝ // 3 < q} → ℝ), 0 ≤ C₃ ∧ (∀ q, 0 ≤ C q) ∧
        ∀ metric ∈ K, ∀ δ ∈ Ioc (0 : ℝ) δ₀,
          δ ∈ Ioc (0 : ℝ) 1 ∧ 4*B*(5*δ) ≤ 1 ∧
          ∃ (S : SmoothThinConeCaps metric δ (c*κ*δ^2) inner outer enlarged D)
            (Pplus : ∀ γ : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
              (enlargedCapMultiplier metric δ (c*κ*δ^2) outer enlarged γ) C₃)
            (chart : ∀ γ : ↑S.centers, NullCapChart metric γ),
            (∀ γ, ‖(chart γ).toFrequency.toContinuousLinearMap‖ ≤ B) ∧
            (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) ∧
            ∀ (q : {q : ℝ // 3 < q}) (f : FieldLp Unit (ENNReal.ofReal 3)),
              (∑ γ : ↑S.centers, ‖(Pplus γ).fieldAction f‖^3)^(1/3 : ℝ) ≤
                C q * (S.centers.card : ℝ)^(1/(3*(q.val-2))) * ‖f‖ := by
  obtain ⟨B,hB,hCharts⟩ := exists_uniform_nullCapCharts hK hFrame hND
  obtain ⟨D,c₀,δAng,hD,hc₀,hδAng,hδAng₁,hAngular⟩ :=
    exists_uniform_actual_capMultipliers_field_angular_L3 Unit hK hFrame hND hIn hIO hOE
  have hB₀ : 0 < 20*B := by positivity
  let δ₀ := min δAng (1/(20*B))
  have hδ₀₁ : δ₀ ≤ 1 := (min_le_left _ _).trans hδAng₁
  refine ⟨B,D,c₀,δ₀,hB,hD,hc₀,lt_min hδAng (one_div_pos.mpr hB₀),hδ₀₁,?_⟩
  intro κ hκ hκsmall c hc hc₀'
  obtain ⟨C₃,hC₃,C,hC,hCaps⟩ := hAngular κ hκ hκsmall c hc hc₀'
  refine ⟨C₃,C,hC₃,hC,?_⟩
  intro metric hMetric δ hδ
  have hSmall : 4*B*(5*δ) ≤ 1 := by
    have hδB : δ ≤ 1/(20*B) := hδ.2.trans (min_le_right _ _)
    have e := (le_div_iff₀ hB₀).mp hδB
    nlinarith only [e]
  obtain ⟨S,_,Pplus,angular⟩ := hCaps metric hMetric δ hδ.1 (hδ.2.trans (min_le_left _ _))
  choose chart hForward hInverse using
    (fun γ : ↑S.centers => hCharts metric hMetric γ (S.centers_null γ.property))
  refine ⟨⟨hδ.1,hδ.2.trans hδ₀₁⟩,hSmall,S,Pplus,chart,hForward,hInverse,?_⟩
  intro q f
  simpa using (angular q f).2

end Burnett.C02
