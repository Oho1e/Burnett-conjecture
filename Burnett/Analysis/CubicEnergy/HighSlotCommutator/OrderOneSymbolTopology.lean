import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneJetRange
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable

set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 600000
set_option maxSynthPendingDepth 8

noncomputable section

namespace Burnett.A06

open Set
open Burnett.A02.FrequencySplit (Joint)
open scoped ContDiff Uniformity NNReal

private abbrev WeightedJetAt (n : ℕ) :=
  BoundedContinuousFunction Joint (Joint[×n]→L[ℝ] ℂ)

local instance : Module ℝ WeightedOrderOneJetSpace := Pi.module ℕ WeightedJetAt ℝ

/-- The actual order-one symbols with their weighted-derivative topology. -/
def OrderOneSymbolFrechet : Type := OrderOneSymbol ℂ

instance : AddCommGroup OrderOneSymbolFrechet :=
  inferInstanceAs (AddCommGroup (OrderOneSymbol ℂ))

instance : Module ℝ OrderOneSymbolFrechet :=
  inferInstanceAs (Module ℝ (OrderOneSymbol ℂ))

def orderOneSymbolFrechetEquiv : OrderOneSymbol ℂ ≃ₗ[ℝ] OrderOneSymbolFrechet :=
  LinearEquiv.refl ℝ (OrderOneSymbol ℂ)

private def frechetJets : OrderOneSymbolFrechet →ₗ[ℝ] WeightedOrderOneJetSpace :=
  orderOneWeightedJets.comp orderOneSymbolFrechetEquiv.symm.toLinearMap

instance : UniformSpace OrderOneSymbolFrechet :=
  UniformSpace.comap frechetJets inferInstance

private theorem isUniformInducing_frechetJets : IsUniformInducing frechetJets := ⟨rfl⟩

instance : CompleteSpace OrderOneSymbolFrechet := by
  apply isUniformInducing_frechetJets.completeSpace
  change IsComplete (range orderOneWeightedJets)
  exact isClosed_range_orderOneWeightedJets.isComplete

theorem orderOneSymbolFrechet_baire : BaireSpace OrderOneSymbolFrechet := by
  letI : Filter.IsCountablyGenerated (𝓤 WeightedOrderOneJetSpace) := by
    change Filter.IsCountablyGenerated (𝓤 (∀ n : ℕ, WeightedJetAt n))
    infer_instance
  letI : Filter.IsCountablyGenerated (𝓤 OrderOneSymbolFrechet) := by
    change Filter.IsCountablyGenerated
      (Filter.comap (Prod.map frechetJets frechetJets) (𝓤 WeightedOrderOneJetSpace))
    infer_instance
  exact BaireSpace.of_pseudoEMetricSpace_completeSpace

private abbrev JetIndex := (_ : ℕ) × Fin 1

private def productJetSeminorm : SeminormFamily ℝ WeightedOrderOneJetSpace JetIndex :=
  SeminormFamily.sigma fun n : ℕ =>
    SeminormFamily.comp (fun _ : Fin 1 => normSeminorm ℝ (WeightedJetAt n))
      (LinearMap.proj n : WeightedOrderOneJetSpace →ₗ[ℝ] WeightedJetAt n)

private def frechetJetSeminorm : SeminormFamily ℝ OrderOneSymbolFrechet JetIndex :=
  SeminormFamily.comp (𝕜 := ℝ) (E := OrderOneSymbolFrechet) (σ₁₂ := RingHom.id ℝ)
    productJetSeminorm frechetJets

private theorem seminorms_orderOneSymbolFrechet : WithSeminorms frechetJetSeminorm := by
  have hProd : WithSeminorms productJetSeminorm :=
    withSeminorms_pi (fun n : ℕ => norm_withSeminorms ℝ (WeightedJetAt n))
  exact isUniformInducing_frechetJets.isInducing.withSeminorms hProd

private theorem frechetJetSeminorm_eval (i : JetIndex) (b : OrderOneSymbol ℂ) :
    frechetJetSeminorm i (orderOneSymbolFrechetEquiv b) = orderOneWeightedSeminorm ℂ i.1 b :=
  norm_orderOneWeightedJets_apply b i.1

/-- A linear map controlled by the zeroth weighted seminorm is continuous
on the actual symbol space. -/
theorem continuous_orderOneSymbolFrechet_of_orderZero {Y : Type*}
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : OrderOneSymbolFrechet →ₗ[ℝ] Y) (C : ℝ≥0)
    (hT : ∀ b : OrderOneSymbol ℂ,
      ‖T (orderOneSymbolFrechetEquiv b)‖ ≤ C * orderOneWeightedSeminorm ℂ 0 b) :
    Continuous T := by
  classical
  apply Seminorm.cont_withSeminorms_normedSpace (τ₁₂ := RingHom.id ℝ) Y seminorms_orderOneSymbolFrechet T
  refine ⟨{⟨0,0⟩}, C, ?_⟩
  intro u
  obtain ⟨b, rfl⟩ := orderOneSymbolFrechetEquiv.surjective u
  simpa only [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton,
    Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, frechetJetSeminorm_eval] using hT b

/-- For the actual Fréchet symbol space, a pointwise bounded family of
continuous linear maps has one finite derivative threshold in the exact
order-one symbol seminorm. -/
theorem exists_finite_orderOneSymbol_bound {ι Y : Type*}
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : ι → OrderOneSymbolFrechet →L[ℝ] Y)
    (hT : ∀ u : OrderOneSymbolFrechet, ∃ B : ℝ, ∀ i : ι, ‖T i u‖ ≤ B) :
    ∃ (K : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (b : OrderOneSymbol ℂ) (i : ι),
        ‖T i (orderOneSymbolFrechetEquiv b)‖ ≤ C * realOrderOneSymbolSeminorm ℂ K b := by
  classical
  letI : BaireSpace OrderOneSymbolFrechet := orderOneSymbolFrechet_baire
  letI : IsTopologicalAddGroup OrderOneSymbolFrechet := seminorms_orderOneSymbolFrechet.topologicalAddGroup
  letI : ContinuousSMul ℝ OrderOneSymbolFrechet := seminorms_orderOneSymbolFrechet.continuousSMul
  let q (i : ι) : Seminorm ℝ OrderOneSymbolFrechet :=
    (normSeminorm ℝ Y).comp (𝕜 := ℝ) (E := OrderOneSymbolFrechet) (σ₁₂ := RingHom.id ℝ) (T i).toLinearMap
  have B : BddAbove (range q) := by
    rw [Seminorm.bddAbove_range_iff]
    intro u
    obtain ⟨D,hD⟩ := hT u
    refine ⟨D,?_⟩
    rintro _ ⟨i,rfl⟩
    exact hD i
  let Q := ⨆ i, q i
  have hQ : Continuous Q := by
    rw [show (Q : OrderOneSymbolFrechet → ℝ) = ⨆ i, (q i : OrderOneSymbolFrechet → ℝ)
      from Seminorm.coe_iSup_eq B]
    exact Seminorm.continuous_iSup q (fun i => continuous_norm.comp (T i).continuous) B
  obtain ⟨J,C,_,hC⟩ := Seminorm.bound_of_continuous seminorms_orderOneSymbolFrechet Q hQ
  let K : ℕ := J.sup (fun i => i.1)
  refine ⟨K,C,C.coe_nonneg,?_⟩
  intro b i
  let u := orderOneSymbolFrechetEquiv b
  have hJ : (J.sup frechetJetSeminorm) u ≤ orderOneSymbolSeminorm ℂ K b := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro j hj
    have nK : j.1 ≤ K := Finset.le_sup (f := fun i : JetIndex => i.1) hj
    change frechetJetSeminorm j (orderOneSymbolFrechetEquiv b) ≤ _
    rw [frechetJetSeminorm_eval j b]
    exact Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (Nat.lt_succ_of_le nK))
  have first : q i ≤ Q := le_ciSup B i
  calc
    ‖T i u‖ = q i u := rfl
    _ ≤ Q u := first u
    _ ≤ (C : ℝ) * (J.sup frechetJetSeminorm) u := hC u
    _ ≤ (C : ℝ) * realOrderOneSymbolSeminorm ℂ K b := mul_le_mul_of_nonneg_left hJ C.coe_nonneg

end Burnett.A06
