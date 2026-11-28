import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleOrderedVertex

set_option autoImplicit false
set_option maxRecDepth 5900
set_option maxHeartbeats 5100000

noncomputable section

namespace Burnett.C02

open Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol Burnett.V03 Burnett.V04
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)

private theorem wardOrderedPrincipalLeg_eq_densityTerm (G : Mat) (hG : Matrix.det G ≠ 0)
    (H : ComplexTensor2) (q r : E) (J L : ComplexTensor2) :
    wardOrderedPrincipalLeg G H (fun i => q i) (fun i => r i) J L =
      frozenDensityCubicTerm frozenActionOrderedBasis G (fun k => H k.1 k.2)
        q (fun k => J k.1 k.2) r (fun k => L k.1 k.2) := by
  have hND : G ∈ nonsingularMetricDomain := hG
  have sumEntry (F : WardActionEntry → ℂ) :
      (∑ k, F k) = ∑ s : ActionSlot OrderedPair, ∑ t : ActionSlot OrderedPair, ∑ i : OrderedPair, F (i,s,t) := by
    have he : (∑ k, F k) = ∑ i : OrderedPair, ∑ s : ActionSlot OrderedPair, ∑ t : ActionSlot OrderedPair, F (i,s,t) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ => Fintype.sum_prod_type _
    rw [he, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  unfold wardOrderedPrincipalLeg frozenDensityCubicTerm
  rw [sumEntry]
  simp only [frozenDensityCubicDirection_eq_frozenActionCubicLinear G hND, Finset.sum_mul,
    wardActionEntryCoefficient]

/-- The real-Lorentz-frame Ward vertex and the original V04 physical
far numerator use the very same complex density vertex. -/
theorem wardComplexPrincipalVertex_eq_physicalDensityVertex (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : E) (H : ComplexTensor2) (q : E) (J : ComplexTensor2) (r : E) (L : ComplexTensor2) :
    complexPrincipalVertex G (fun d => p d) H (fun d => q d) J (fun d => r d) L =
      frozenDensityCubicVertex frozenActionOrderedBasis G p (fun k => H k.1 k.2) q (fun k => J k.1 k.2)
        r (fun k => L k.1 k.2) := by
  rw [wardComplexPrincipalVertex_eq_ordered G hG, wardOrderedPrincipalLeg_eq_densityTerm G hG H q r J L,
    wardOrderedPrincipalLeg_eq_densityTerm G hG J p r H L, wardOrderedPrincipalLeg_eq_densityTerm G hG L p q H J]
  unfold frozenDensityCubicVertex
  rw [frozenDensityCubicTerm_swap frozenActionOrderedBasis G (fun k : OrderedPair => J k.1 k.2)
    p (fun k => H k.1 k.2) r (fun k => L k.1 k.2)]

end Burnett.C02
