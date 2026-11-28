import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleOrderedVertex
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 6300000

noncomputable section

namespace Burnett.C02

open Set Burnett.V03 Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Matrix.Norms.Elementwise

/-- The same exact complex principal vertex is jointly smooth in a
smooth invertible metric and smooth ordered frequency amplitudes. -/
theorem wardComplexPrincipalVertex_contDiffOn {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] (V : Set X)
    (G : X → Mat) (hG : ContDiffOn ℝ ∞ G V) (hND : ∀ x ∈ V, Matrix.det (G x) ≠ 0)
    (p q r : X → E) (hp : ContDiffOn ℝ ∞ p V) (hq : ContDiffOn ℝ ∞ q V) (hr : ContDiffOn ℝ ∞ r V)
    (H J L : X → ComplexTensor2)
    (hH : ∀ k : OrderedPair, ContDiffOn ℝ ∞ (fun x => H x k.1 k.2) V)
    (hJ : ∀ k : OrderedPair, ContDiffOn ℝ ∞ (fun x => J x k.1 k.2) V)
    (hL : ∀ k : OrderedPair, ContDiffOn ℝ ∞ (fun x => L x k.1 k.2) V) :
    ContDiffOn ℝ ∞ (fun x => complexPrincipalVertex (G x) (fun i => p x i) (H x)
      (fun i => q x i) (J x) (fun i => r x i) (L x)) V := by
  have hMap : MapsTo G V nonsingularMetricDomain := hND
  have coef (k : WardActionEntry) : ContDiffOn ℝ ∞ (fun x => (wardActionEntryCoefficient (G x) k : ℂ)) V := by
    let c := metricActionCoefficient frozenActionOrderedBasis k.2.1 k.2.2
    have hD : ContDiffOn ℝ ∞ (fderiv ℝ c) nonsingularMetricDomain :=
      (contDiffOn_metricActionCoefficient frozenActionOrderedBasis k.2.1 k.2.2).fderiv_of_isOpen
        isOpen_nonsingularMetricDomain (by simp)
    apply (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((hD.comp hG hMap).clm_apply (contDiffOn_const (c := frozenActionOrderedBasis k.1)))).congr
    intro x hx
    change (wardActionEntryCoefficient (G x) k : ℂ) =
      (fderiv ℝ c (G x) (frozenActionOrderedBasis k.1) : ℂ)
    exact congrArg Complex.ofReal (frozenActionCubicLinear_eq_metricActionCoefficient_fderiv (G x)
      (hMap hx) k.2.1.1 k.2.2.1 k.2.1.2 k.2.2.2 k.1)
  have leg (p' q' : X → E) (hp' : ContDiffOn ℝ ∞ p' V) (hq' : ContDiffOn ℝ ∞ q' V)
      (A B C : X → ComplexTensor2)
      (hA : ∀ k : OrderedPair, ContDiffOn ℝ ∞ (fun x => A x k.1 k.2) V)
      (hB : ∀ k : OrderedPair, ContDiffOn ℝ ∞ (fun x => B x k.1 k.2) V)
      (hC : ∀ k : OrderedPair, ContDiffOn ℝ ∞ (fun x => C x k.1 k.2) V) :
      ContDiffOn ℝ ∞ (fun x => wardOrderedPrincipalLeg (G x) (A x)
        (fun i => p' x i) (fun i => q' x i) (B x) (C x)) V := by
    have coord (f : X → E) (hf : ContDiffOn ℝ ∞ f V) (j : Index) :
        ContDiffOn ℝ ∞ (fun x => (f x j : ℂ)) V :=
      (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff).comp_contDiffOn hf
    unfold wardOrderedPrincipalLeg
    exact ContDiffOn.sum fun k _ => (((coef k).mul (hA k.1)).mul
      ((coord p' hp' k.2.1.1).mul (hB k.2.1.2))).mul ((coord q' hq' k.2.2.1).mul (hC k.2.2.2))
  have hTotal := (((leg q r hq hr H J L hH hJ hL).add
    (leg p r hp hr J H L hJ hH hL)).add (leg p q hp hq L H J hL hH hJ)).neg
  exact hTotal.congr fun x hx => wardComplexPrincipalVertex_eq_ordered (G x) (hND x hx) _ _ _ _ _ _

end Burnett.C02
