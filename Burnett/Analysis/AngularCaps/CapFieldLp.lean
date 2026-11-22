import Burnett.Analysis.AngularCaps.FieldLpLift

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Filter
open scoped ENNReal
open Burnett.Fourier Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit (radianAction)

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The field Fourier multiplier on L², obtained by applying the same
Plancherel multiplier to every component. -/
def fieldFourierMultiplier (symbol : BoundedSymbol Space) :
    FieldLp ι 2 →L[ℂ] FieldLp ι 2 :=
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  liftScalarLp (fourierMultiplier symbol)

def CapLpRealization.fieldAction {b : Space → ℝ} {C : ℝ} (R : CapLpRealization p b C) :
    FieldLp ι p →L[ℂ] FieldLp ι p :=
  liftScalarLp R.action

theorem CapLpRealization.fieldAction_norm_le {b : Space → ℝ} {C : ℝ}
    (R : CapLpRealization p b C) (hC : 0 ≤ C) (f : FieldLp ι p) :
    ‖R.fieldAction f‖ ≤ ((Fintype.card ι : ℝ) * C) * ‖f‖ :=
  liftScalarLp_norm_le R.action hC R.norm_le f

theorem CapLpRealization.fieldAction_intersection_eq {b : Space → ℝ} {C : ℝ}
    (R : CapLpRealization p b C) (f : Space → EuclideanSpace ℂ ι)
    (h₂ : MemLp f 2 volume) (hp : MemLp f p volume) :
    (R.fieldAction (hp.toLp f) : Space → EuclideanSpace ℂ ι) =ᵐ[volume]
      (fieldFourierMultiplier R.symbol (h₂.toLp f) : Space → EuclideanSpace ℂ ι) := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h (i : ι) : ∀ᵐ x ∂(volume : Measure Space),
      R.action (fieldCoordinateLp i (hp.toLp f)) x =
        fourierMultiplier R.symbol (fieldCoordinateLp i (h₂.toLp f)) x := by
    rw [fieldCoordinateLp_toLp i, fieldCoordinateLp_toLp i]
    exact R.intersection_eq (fun x => f x i) _ _
  change (liftScalarLp R.action (hp.toLp f) : Space → EuclideanSpace ℂ ι) =ᵐ[volume]
    (liftScalarLp (fourierMultiplier R.symbol) (h₂.toLp f) : Space → EuclideanSpace ℂ ι)
  filter_upwards [liftScalarLp_ae R.action (hp.toLp f),
    liftScalarLp_ae (fourierMultiplier R.symbol) (h₂.toLp f), ae_all_iff.2 h] with x ha hb hc
  rw [ha, hb]
  ext i
  exact hc i

/-- The array of the manuscript's Schwartz coordinate fields uses the same
radian Fourier action in each component and the Euclidean fiber metric. -/
theorem CapLpRealization.fieldAction_schwartz_eq {b : Space → ℝ} {C : ℝ}
    (R : CapLpRealization p b C) (u : ι → SchwartzMap Space ℂ) :
    let f : Space → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 (fun i => u i x)
    let hf := fieldArray_memLp (fun i x => u i x) (fun i => (u i).memLp p volume)
    (R.fieldAction (hf.toLp f) : Space → EuclideanSpace ℂ ι) =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun i => radianAction b (u i) x) := by
  dsimp only
  let f : Space → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 (fun i => u i x)
  let hf : MemLp f p volume := fieldArray_memLp (fun i x => u i x) (fun i => (u i).memLp p volume)
  change (liftScalarLp R.action (hf.toLp f) : Space → EuclideanSpace ℂ ι) =ᵐ[volume]
    fun x => WithLp.toLp 2 (fun i => radianAction b (u i) x)
  have hcoord (i : ι) : fieldCoordinateLp i (hf.toLp f) = (u i).toLp p volume :=
    fieldCoordinateLp_toLp i hf
  filter_upwards [liftScalarLp_ae R.action (hf.toLp f),
    ae_all_iff.2 fun i => R.schwartz_eq (u i)] with x hx hg
  rw [hx]
  ext i
  change R.action (fieldCoordinateLp i (hf.toLp f)) x = radianAction b (u i) x
  rw [hcoord i]
  exact hg i

/-- Both actual caps from the same family act on the full Euclidean field,
with a common fixed dimension factor multiplying the scalar bound. -/
theorem exists_uniform_actual_capMultiplier_fieldLp (ι : Type*) [Fintype ι]
    {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (Burnett.RicciSymbol.TensorFrame.LorentzFrame m))
    (hND : ∀ m ∈ K, Nondegenerate m)
    {inner outer enlarged : ℝ} (hIn : 0 ≤ inner) (hIO : inner < outer) (hOE : outer < enlarged) :
    ∃ D c₀ δ₀ : ℝ, 0 < D ∧ 0 < c₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ κ : ℝ, 0 < κ → κ < 1/16 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ C : {p : ℝ // 1 < p} → ℝ, (∀ p, 0 ≤ C p) ∧
        ∀ m ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          ∃ S : SmoothThinConeCaps m δ (c*κ*δ^2) inner outer enlarged D,
            ∀ w ∈ S.centers, ∀ p : {p : ℝ // 1 < p},
              let P := ENNReal.ofReal p.val
              letI : Fact (1 ≤ P) :=
                ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal p.property.le⟩
              ∃ (R : CapLpRealization P
                  (capMultiplier S.centers m δ (c*κ*δ^2) inner outer w) (C p))
                (Rplus : CapLpRealization P
                  (enlargedCapMultiplier m δ (c*κ*δ^2) outer enlarged w) (C p)),
                ∀ f : FieldLp ι P,
                  ‖R.fieldAction f‖ ≤ ((Fintype.card ι : ℝ) * C p) * ‖f‖ ∧
                  ‖Rplus.fieldAction f‖ ≤ ((Fintype.card ι : ℝ) * C p) * ‖f‖ := by
  obtain ⟨D, c₀, δ₀, hD, hc₀, hδ₀, hδone, hFamily⟩ :=
    exists_uniform_actual_capMultiplier_Lp hK hFrame hND hIn hIO hOE
  refine ⟨D, c₀, δ₀, hD, hc₀, hδ₀, hδone, ?_⟩
  intro κ hκ hκsmall c hc hcsmall
  obtain ⟨C, hC, hBound⟩ := hFamily κ hκ hκsmall c hc hcsmall
  refine ⟨C, hC, ?_⟩
  intro m hm δ hδ hδsmall
  obtain ⟨S, hS⟩ := hBound m hm δ hδ hδsmall
  refine ⟨S, ?_⟩
  intro w hw p
  letI : Fact (1 ≤ ENNReal.ofReal p.val) :=
    ⟨by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal p.property.le⟩
  obtain ⟨⟨R⟩, ⟨Rplus⟩⟩ := hS w hw p
  exact ⟨R, Rplus, fun f => ⟨R.fieldAction_norm_le (hC p) f, Rplus.fieldAction_norm_le (hC p) f⟩⟩

end Burnett.Analysis.CapFourier
