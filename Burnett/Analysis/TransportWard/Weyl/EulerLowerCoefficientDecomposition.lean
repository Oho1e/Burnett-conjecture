import Burnett.Analysis.TransportWard.Weyl.LinearizedEulerPrincipal

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1800

noncomputable section

namespace Burnett.V03.Palatini

open Function Set Burnett.Analysis.TransportWardSymbol
open scoped ContDiff Topology Matrix.Norms.Elementwise BigOperators

open private hasDerivAt_comp_fieldSegment from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

abbrev EulerBackgroundJet (ι : Type*) := Mat × (ActionSlot ι → ℝ) × (Fin 4 → ActionSlot ι → ℝ)

def eulerBackgroundJetDomain (ι : Type*) : Set (EulerBackgroundJet ι) :=
  Prod.fst ⁻¹' nonsingularMetricDomain

theorem isOpen_eulerBackgroundJetDomain (ι : Type*) : IsOpen (eulerBackgroundJetDomain ι) :=
  isOpen_nonsingularMetricDomain.preimage continuous_fst

def eulerAtBackgroundJet {ι : Type*} [Fintype ι] (S : ι → Mat) (i : ι)
    (p : EulerBackgroundJet ι) : ℝ := metricEulerAtJet S p.1 p.2.1 p.2.2 i

theorem contDiffOn_eulerAtBackgroundJet {ι : Type*} [Fintype ι] (S : ι → Mat) (i : ι) :
    ContDiffOn ℝ ∞ (eulerAtBackgroundJet S i) (eulerBackgroundJetDomain ι) := by
  have hp (s : ActionSlot ι) : ContDiff ℝ ∞ (fun p : EulerBackgroundJet ι => p.2.1 s) :=
    (contDiff_apply ℝ ℝ s).comp (contDiff_fst.comp contDiff_snd)
  have hq (a : Fin 4) (s : ActionSlot ι) : ContDiff ℝ ∞ (fun p : EulerBackgroundJet ι => p.2.2 a s) :=
    (contDiff_apply ℝ ℝ s).comp ((contDiff_apply ℝ (ActionSlot ι → ℝ) a).comp (contDiff_snd.comp contDiff_snd))
  have hDom : MapsTo (Prod.fst : EulerBackgroundJet ι → Mat) (eulerBackgroundJetDomain ι) nonsingularMetricDomain :=
    fun _ h => h
  exact (ContDiffOn.sum fun s _ => ContDiffOn.sum fun t _ =>
    ((((contDiffOn_metricEulerLowerCoefficient S i s t).comp contDiff_fst.contDiffOn hDom).mul
      (hp s).contDiffOn).mul (hp t).contDiffOn)).sub
    (ContDiffOn.sum fun a _ => ContDiffOn.sum fun t _ =>
      ((contDiffOn_metricActionCoefficient S (a,i) t).comp contDiff_fst.contDiffOn hDom).mul (hq a t).contDiffOn)

/-- The Euler density derivative in a value direction with the two
spatial jets held fixed. -/
def actualEulerZeroOrderCoefficient {ι : Type*} [Fintype ι] (S : ι → Mat) (i j : ι)
    (p : EulerBackgroundJet ι) : ℝ := fderiv ℝ (eulerAtBackgroundJet S i) p (S j,0,0)

/-- The Euler density derivative in one actual first-jet direction,
with the value and second jet held fixed. -/
def actualEulerFirstOrderCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Mat) (i : ι) (s : ActionSlot ι) (p : EulerBackgroundJet ι) : ℝ :=
  fderiv ℝ (eulerAtBackgroundJet S i) p (0,Pi.single s 1,0)

theorem contDiffOn_actualEulerZeroOrderCoefficient {ι : Type*} [Fintype ι]
    (S : ι → Mat) (i j : ι) :
    ContDiffOn ℝ ∞ (actualEulerZeroOrderCoefficient S i j) (eulerBackgroundJetDomain ι) :=
  ((contDiffOn_eulerAtBackgroundJet S i).fderiv_of_isOpen (isOpen_eulerBackgroundJetDomain ι) (by simp)).clm_apply
    contDiffOn_const

theorem contDiffOn_actualEulerFirstOrderCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Mat) (i : ι) (s : ActionSlot ι) :
    ContDiffOn ℝ ∞ (actualEulerFirstOrderCoefficient S i s) (eulerBackgroundJetDomain ι) :=
  ((contDiffOn_eulerAtBackgroundJet S i).fderiv_of_isOpen (isOpen_eulerBackgroundJetDomain ι) (by simp)).clm_apply
    contDiffOn_const

/-- The lower part of the previously proved actual affine Hessian
is precisely a zeroth- and first-order linear differential expression in
the normalized field components, with smooth background coefficients. -/
theorem metricEulerJetLowerLinearization_eq_coefficients {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Mat) (G : Mat) (z : ι → ℝ) (p dp : ActionSlot ι → ℝ)
    (q : Fin 4 → ActionSlot ι → ℝ) (i : ι) (hG : G.det ≠ 0) :
    metricEulerJetLowerLinearization S G (assembleMetricComponents S z) p dp q i =
      (∑ j, z j * actualEulerZeroOrderCoefficient S i j (G,p,q)) +
      ∑ s, dp s * actualEulerFirstOrderCoefficient S i s (G,p,q) := by
  let v : EulerBackgroundJet ι := (assembleMetricComponents S z,dp,0)
  let F := eulerAtBackgroundJet S i
  let A := fderiv ℝ F (G,p,q)
  have hIn : fieldSegment (G,p,q) v 0 ∈ eulerBackgroundJetDomain ι := by
    simpa only [fieldSegment,zero_smul,add_zero] using (show (G,p,q) ∈ eulerBackgroundJetDomain ι from hG)
  have hPath (t : ℝ) : F (fieldSegment (G,p,q) v t) =
      metricEulerAtJet S (fieldSegment G (assembleMetricComponents S z) t) (fieldSegment p dp t) q i := by
    unfold F eulerAtBackgroundJet
    change metricEulerAtJet S (G+t • assembleMetricComponents S z) (p+t • dp) (q+t • 0) i = _
    simp only [smul_zero,add_zero,fieldSegment]
  have hDer := (hasDerivAt_comp_fieldSegment F (isOpen_eulerBackgroundJetDomain ι)
    (contDiffOn_eulerAtBackgroundJet S i) (G,p,q) v 0 hIn).deriv
  have hEq : metricEulerJetLowerLinearization S G (assembleMetricComponents S z) p dp q i = A v := by
    unfold metricEulerJetLowerLinearization
    simp_rw [← hPath]
    simpa only [fieldSegment,zero_smul,add_zero,A] using hDer
  let L₀ : Mat →L[ℝ] EulerBackgroundJet ι := ContinuousLinearMap.inl ℝ _ _
  let L₁ : (ActionSlot ι → ℝ) →L[ℝ] EulerBackgroundJet ι :=
    (ContinuousLinearMap.inr ℝ _ _).comp (ContinuousLinearMap.inl ℝ _ _)
  let basis (s : ActionSlot ι) : ActionSlot ι → ℝ := Pi.single s 1
  have hdp : dp = ∑ s : ActionSlot ι, dp s • basis s := by
    funext s
    simp [basis,Finset.sum_apply,Pi.single_apply,smul_eq_mul,mul_ite]
  have hv : v = L₀ (assembleMetricComponents S z) + L₁ dp := by
    exact Prod.ext (by simp [v,L₀,L₁]) (Prod.ext (by simp [v,L₀,L₁]) (by simp [v,L₀,L₁]))
  rw [hEq,hv,map_add,assembleMetricComponents_apply]
  calc
    _ = (∑ j, z j • A (L₀ (S j))) + ∑ s, dp s • A (L₁ (basis s)) := by
      congr 1
      · simp only [map_sum,map_smul]
      · conv_lhs => rw [hdp]
        simp only [map_sum,map_smul]
    _ = _ := rfl

end Burnett.V03.Palatini
