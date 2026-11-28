import Burnett.Analysis.TransportWard.Weyl.ActualWeylPrincipalPairDifference
import Burnett.Analysis.TransportWard.Weyl.LowerWeylPairLimit

set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxRecDepth 3500

noncomputable section

namespace Burnett.V03.Palatini

open Filter Function MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.CarlesonEmbedding (firstOrderAction_finset_sum)
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.Microlocal.HminusReverse (schwartzH1Energy)
open scoped BigOperators ContDiff Topology ComplexConjugate

local notation "J" => Fin 4 × Fin 4
local notation "D" => frozenSchwartzCoordinatePartial

private def lowerZeroTerm (c : SchwartzMap E ℂ) (w : SchwartzMap E ℂ) :=
  scalarSchwartzProduct c w

private def lowerFirstTerm (c : SchwartzMap E ℂ) (k : Fin 4) (w : SchwartzMap E ℂ) :=
  scalarSchwartzProduct c (D k w)

private theorem integrable_schwartz_test (u v : SchwartzMap E ℂ) :
    Integrable (fun x => conj (v x) * u x) volume := by
  let C := SchwartzMap.seminorm ℝ 0 0 u
  have hu (x : E) : ‖u x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u 0 x
  refine (v.integrable.norm.mul_const C).mono'
    ((Complex.continuous_conj.comp v.continuous).mul u.continuous).aestronglyMeasurable ?_
  exact .of_forall fun x => by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hu x) (norm_nonneg _)

/-- The actual finite Euler differential expression on the Schwartz domain,
with its principal part in the coefficient matrix used by the Weyl theorem. -/
def eulerWeylDifferentialField {ι : Type*} [Fintype ι]
    (c₀ : ι → ι → SchwartzMap E ℂ) (c₁ : ι → ι → Fin 4 → SchwartzMap E ℂ)
    (c₂ : ι → ι → J → SchwartzMap E ℂ) (u : ι → SchwartzMap E ℂ) (i : ι) :
    SchwartzMap E ℂ :=
  ((∑ j, lowerZeroTerm (c₀ i j) (u j)) +
    (∑ j, ∑ k, lowerFirstTerm (c₁ i j k) k (u j))) +
    variableDensityPrincipalSchwartzField c₂ u i

/-- Exact integrated splitting of a Schwartz-domain commutator of the
finite full differential field with the same scalar left operator. -/
theorem integral_eulerWeylDifferentialComm_split {ι : Type*} [Fintype ι]
    {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u x, B u x = firstOrderAction a u x)
    (c₀ : ι → ι → SchwartzMap E ℂ) (c₁ : ι → ι → Fin 4 → SchwartzMap E ℂ)
    (c₂ : ι → ι → J → SchwartzMap E ℂ) (u v : ι → SchwartzMap E ℂ) :
    let L := eulerWeylDifferentialField c₀ c₁ c₂
    (∫ x, ∑ i, conj (v i x) * (Complex.I * (L (fun j => B (u j)) i x - B (L u i) x))) =
      (∑ i, ∫ x, conj (v i x) * variableDensityWeylCommutator c₂ a u i x) +
      ∑ i, ∑ j, (
        (∫ x, conj (v i x) * (Complex.I * (c₀ i j x * firstOrderAction a (u j) x -
          firstOrderAction a (scalarSchwartzProduct (c₀ i j) (u j)) x))) +
        ∑ k : Fin 4, ∫ x, conj (v i x) * (Complex.I *
          (c₁ i j k x * physicalCoordinatePartial k (firstOrderAction a (u j)) x -
            firstOrderAction a (scalarSchwartzProduct (c₁ i j k) (D k (u j))) x))) := by
  intro L
  let F (j : ι) := B (u j)
  let C₀ (i j : ι) := Complex.I • (lowerZeroTerm (c₀ i j) (F j) - B (lowerZeroTerm (c₀ i j) (u j)))
  let C₁ (i j : ι) (k : Fin 4) := Complex.I •
    (lowerFirstTerm (c₁ i j k) k (F j) - B (lowerFirstTerm (c₁ i j k) k (u j)))
  let C₂ (i : ι) := Complex.I •
    (variableDensityPrincipalSchwartzField c₂ F i - B (variableDensityPrincipalSchwartzField c₂ u i))
  have hF (j : ι) : (F j : E → ℂ) = firstOrderAction a (u j) := funext (hB (u j))
  have h₀ (i j : ι) (x : E) : C₀ i j x = Complex.I *
      (c₀ i j x * firstOrderAction a (u j) x - firstOrderAction a (scalarSchwartzProduct (c₀ i j) (u j)) x) := by
    simp only [C₀,lowerZeroTerm,SchwartzMap.smul_apply,SchwartzMap.sub_apply,
      scalarSchwartzProduct_apply,hB,smul_eq_mul,F]
  have h₁ (i j : ι) (k : Fin 4) (x : E) : C₁ i j k x = Complex.I *
      (c₁ i j k x * physicalCoordinatePartial k (firstOrderAction a (u j)) x -
        firstOrderAction a (scalarSchwartzProduct (c₁ i j k) (D k (u j))) x) := by
    have hDeriv : D k (F j) x = physicalCoordinatePartial k (firstOrderAction a (u j)) x := by
      rw [frozenSchwartzCoordinatePartial,SchwartzMap.pderivCLM_apply,hF,physicalCoordinatePartial]
    simp only [C₁,lowerFirstTerm,SchwartzMap.smul_apply,SchwartzMap.sub_apply,
      scalarSchwartzProduct_apply,hDeriv,hB,smul_eq_mul]
  have h₂ (i : ι) (x : E) : C₂ i x = variableDensityWeylCommutator c₂ a u i x := by
    simp only [C₂,SchwartzMap.smul_apply,SchwartzMap.sub_apply,hB,smul_eq_mul,
      variableDensityWeylCommutator,variableDensityPrincipalSchwartzField_apply,hF]
  have hBA (f g : SchwartzMap E ℂ) (x : E) : B (f + g) x = B f x + B g x := by
    simpa only [hB,neg_one_smul,neg_one_mul,sub_neg_eq_add] using firstOrderAction_sub_smul a ha x f g (-1)
  have hBSj (f : ι → SchwartzMap E ℂ) (x : E) :
      B (∑ j, f j : SchwartzMap E ℂ) x = ∑ j, B (f j) x := by
    simpa only [hB] using firstOrderAction_finset_sum ha Finset.univ f x
  have hBSk (f : Fin 4 → SchwartzMap E ℂ) (x : E) :
      B (∑ k, f k : SchwartzMap E ℂ) x = ∑ k, B (f k) x := by
    simpa only [hB] using firstOrderAction_finset_sum ha Finset.univ f x
  have hExpr (i : ι) (x : E) : Complex.I * (L F i x - B (L u i) x) =
      C₂ i x + ∑ j, (C₀ i j x + ∑ k, C₁ i j k x) := by
    change Complex.I * (SchwartzMap.delta ℂ ℂ x (L F i) - B (L u i) x) = _
    simp only [L,eulerWeylDifferentialField,map_add,map_sum,SchwartzMap.delta_apply,hBA,hBSj,hBSk,
      C₂,C₀,C₁,SchwartzMap.smul_apply,SchwartzMap.sub_apply,smul_eq_mul,mul_sub,
      mul_add,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    ring
  let T₂ (i : ι) (x : E) := conj (v i x) * C₂ i x
  let T₀ (i j : ι) (x : E) := conj (v i x) * C₀ i j x
  let T₁ (i j : ι) (k : Fin 4) (x : E) := conj (v i x) * C₁ i j k x
  have hInt₂ (i : ι) : Integrable (T₂ i) volume := integrable_schwartz_test (C₂ i) (v i)
  have hInt₀ (i j : ι) : Integrable (T₀ i j) volume := integrable_schwartz_test (C₀ i j) (v i)
  have hInt₁ (i j : ι) (k : Fin 4) : Integrable (T₁ i j k) volume := integrable_schwartz_test (C₁ i j k) (v i)
  let T (i j : ι) (x : E) := T₀ i j x + ∑ k, T₁ i j k x
  have hIntL (i j : ι) : Integrable (T i j) volume :=
    (hInt₀ i j).add (integrable_finset_sum Finset.univ (fun k _ => hInt₁ i j k))
  let P (i : ι) (x : E) := T₂ i x + ∑ j, T i j x
  have hIntP (i : ι) : Integrable (P i) volume :=
    (hInt₂ i).add (integrable_finset_sum Finset.univ (fun j _ => hIntL i j))
  change (∫ x, ∑ i, conj (v i x) * (Complex.I * (L F i x - B (L u i) x))) = _
  have hPoint (x : E) : (∑ i, conj (v i x) * (Complex.I * (L F i x - B (L u i) x))) = ∑ i, P i x := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hExpr]
    simp only [P,T,T₂,T₀,T₁,mul_add,Finset.mul_sum]
  simp only [hPoint,← h₂,← h₀,← h₁]
  calc
    (∫ x, ∑ i, P i x) = ∑ i, ∫ x, P i x :=
      integral_finset_sum Finset.univ (fun i _ => hIntP i)
    _ = ∑ i, ((∫ x, T₂ i x) + ∑ j, ∫ x, T i j x) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (integral_add (hInt₂ i) (integrable_finset_sum Finset.univ (fun j _ => hIntL i j))).trans
        (congrArg (fun z => (∫ x, T₂ i x) + z) (integral_finset_sum Finset.univ (fun j _ => hIntL i j)))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_add (hInt₀ i j) (integrable_finset_sum Finset.univ (fun k _ => hInt₁ i j k))).trans
        (congrArg (fun z => (∫ x, T₀ i j x) + z) (integral_finset_sum Finset.univ (fun k _ => hInt₁ i j k)))

/-- Once the exact canonical Poisson pairing limit is known, the genuine
full Euler Weyl commutator has that limit on the same sequence. -/
theorem tendsto_eulerWeylDifferentialComm_of_canonicalPair {ι : Type*} [Fintype ι]
    (S : ι → Mat) (G : E → Mat)
    (c₀ : ι → ι → SchwartzMap E ℂ) (c₁ : ι → ι → Fin 4 → SchwartzMap E ℂ)
    (c₂ : ι → ι → J → SchwartzMap E ℂ)
    (θ : E → ℝ) (β : E → E → ℝ) (R : ℝ) (hθ : HasCompactSupport θ)
    (hs : ContDiff ℝ ∞ (uncurry β))
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ (fun x ξ => (β x ξ : ℂ))))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol (fun x ξ => (β x ξ : ℂ))))
    (hC : ∀ y ∈ tsupport θ, ∀ (i j : ι) (d : J),
      DifferentiableAt ℝ (fun z => metricActionCoefficient S (d.1,i) (d.2,j) (G z)) y)
    (hc : ∀ y ∈ tsupport θ, ∀ (i j : ι) (d : J), (fun z => c₂ i j d z) =ᶠ[𝓝 y]
      fun z => (metricActionCoefficient S (d.1,i) (d.2,j) (G z) : ℂ))
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u x, B u x = firstOrderAction (windowedWeylLeftSymbol θ (fun x ξ => (β x ξ : ℂ)) R h) u x)
    (u v : ℕ → ι → SchwartzMap E ℂ)
    (hU : ∀ j, ∃ M : ℝ, ∀ n, Real.sqrt (schwartzH1Energy (u n j)) ≤ M)
    (hV : ∀ i, Tendsto (fun n => ‖(v n i).toLp 2 volume‖) atTop (𝓝 0))
    (z : ℂ)
    (hLim : let P (i j : ι) (x ξ : E) :=
      (canonicalBracket (fun y ζ => frozenDensityPrincipalPhase S (G y) ζ i j)
        (fun y ζ => β y (WithLp.toLp 2 ζ)) x (physicalRadianCovector ξ) : ℂ)
      ; Tendsto (fun n => ∑ i, ∑ j, ∫ x, conj (v n i x) * firstOrderAction (P i j) (u n j) x) atTop (𝓝 z)) :
    let L := eulerWeylDifferentialField c₀ c₁ c₂
    Tendsto (fun n => ∫ x, ∑ i, conj (v n i x) *
      (Complex.I * (L (fun j => B (u n j)) i x - B (L (u n) i) x))) atTop (𝓝 z) := by
  intro L
  let β' (x ξ : E) : ℂ := β x ξ
  let a := windowedWeylLeftSymbol θ β' R h
  have hPlateau' (x ξ : E) (hx : β' x ξ ≠ 0) : θ x = 1 :=
    hPlateau x ξ (fun hz => hx (by simp only [β',hz,Complex.ofReal_zero]))
  have ha := windowedWeyl_leftSymbol_scaled_order_one θ β' R h hAmp hPlateau' hβ
  have hOff (x : E) (hx : x ∉ tsupport θ) (ξ : E) : a x ξ = 0 :=
    windowedWeylLeftSymbol_eq_zero_of_output θ β' R h x ξ (image_eq_zero_of_notMem_tsupport hx)
  have hLower := tendsto_lowerEulerWeylComm_pair_zero ha hθ hOff c₀ c₁ u v hU hV
  have hDiff := tendsto_actual_variableDensityWeyl_pair_sub_canonical_zero S G c₂ θ β R hθ hs
    h hAmp hPlateau hβ hC hc u v hU hV
  have hMain := (hDiff.add hLim).congr (fun n => sub_add_cancel _ _)
  have hAll := hMain.add hLower
  simp only [zero_add,add_zero] at hAll
  exact hAll.congr (fun n => (integral_eulerWeylDifferentialComm_split ha.firstBaseFrequency.frequency
    B hB c₀ c₁ c₂ (u n) (v n)).symm)

end Burnett.V03.Palatini
