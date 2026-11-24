import Burnett.Analysis.Microlocal.CompactChartInput
import Burnett.Geometry.CurvatureDifference

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.RawCovariance

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open scoped BigOperators

open Burnett.Microlocal.CurlDensity (JetSlot)

def jetEntries (J : FirstJet) (i : JetSlot) : ℝ :=
  J i.1 i.2.1 i.2.2

def jetBasis (i : JetSlot) : FirstJet :=
  fun a b c => if i = (a, b, c) then 1 else 0

theorem jet_eq_basis_sum (J : FirstJet) :
    J = ∑ i, jetEntries J i • jetBasis i := by
  classical
  funext a b c
  simp [jetEntries, jetBasis, Finset.sum_apply, Pi.smul_apply, mul_ite]

/-- The Christoffel expression is linear in the actual three-index jet. -/
def christoffelJet (G : Tensor2) (a b c : Index) : FirstJet →ₗ[ℝ] ℝ where
  toFun J := christoffel G J a b c
  map_add' J K := by
    unfold christoffel
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    simp only [koszul, Pi.add_apply]
    ring
  map_smul' r J := by
    simp only [RingHom.id_apply, smul_eq_mul, christoffel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [koszul, Pi.smul_apply, smul_eq_mul]
    ring

theorem christoffel_eq_jet_sum (G : Tensor2) (J : FirstJet) (a b c : Index) :
    christoffel G J a b c = ∑ i, jetEntries J i * christoffel G (jetBasis i) a b c := by
  let L := christoffelJet G a b c
  calc
    christoffel G J a b c = L J := rfl
    _ = L (∑ i, jetEntries J i • jetBasis i) := congrArg L (jet_eq_basis_sum J)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, L, christoffelJet, LinearMap.coe_mk,
             AddHom.coe_mk]

/-- Two raw jets in the ordered product with the sign of the weak Ricci limit. -/
def rawJetCross (G : Tensor2) (J K : FirstJet) (b c : Index) : ℝ :=
  ∑ a, ∑ e,
    (christoffel G J a c e * christoffel G K e b a -
      christoffel G J a a e * christoffel G K e b c)

theorem rawJetCross_diag (G : Tensor2) (J : FirstJet) (b c : Index) :
    rawJetCross G J J b c = -quadraticDifference (christoffel G J) b c := by
  simp only [rawJetCross, quadraticDifference, ← Finset.sum_neg_distrib, neg_sub]

def rawJetProductCoefficient (G : Tensor2) (b c : Index) (i j : JetSlot) : ℝ :=
  rawJetCross G (jetBasis i) (jetBasis j) b c

private theorem product_eq_jet_sum (G : Tensor2) (J K : FirstJet)
    (a b c p q r : Index) :
    christoffel G J a b c * christoffel G K p q r =
      ∑ i, ∑ j, (christoffel G (jetBasis i) a b c * christoffel G (jetBasis j) p q r) *
        (jetEntries J i * jetEntries K j) := by
  rw [christoffel_eq_jet_sum G J, christoffel_eq_jet_sum G K]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rawJetCross_eq_jet_sum (G : Tensor2) (J K : FirstJet) (b c : Index) :
    rawJetCross G J K b c = ∑ i, ∑ j, rawJetProductCoefficient G b c i j *
      (jetEntries J i * jetEntries K j) := by
  unfold rawJetCross rawJetProductCoefficient
  simp only [rawJetCross, Finset.sum_mul]
  simp only [product_eq_jet_sum G J K]
  simp only [← Finset.sum_sub_distrib]
  let f (a e : Index) (i j : JetSlot) :=
    (christoffel G (jetBasis i) a c e * christoffel G (jetBasis j) e b a) *
      (jetEntries J i * jetEntries K j) -
    (christoffel G (jetBasis i) a a e * christoffel G (jetBasis j) e b c) *
      (jetEntries J i * jetEntries K j)
  change (∑ a, ∑ e, ∑ i, ∑ j, f a e i j) = _
  calc
    (∑ a, ∑ e, ∑ i, ∑ j, f a e i j) = ∑ a, ∑ i, ∑ e, ∑ j, f a e i j := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ e, ∑ j, f a e i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ e, f a e i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ e, f a e i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by simp only [f, sub_mul]

def rankOneJet (ξ : Covector) (h : Tensor2) : FirstJet :=
  fun a b c => ξ a * h b c

theorem christoffel_rankOneJet (G : Tensor2) (ξ : Covector) (h : Tensor2) (a b c : Index) :
    christoffel G (rankOneJet ξ h) a b c = connectionSymbol G ξ h a b c := by
  unfold christoffel koszul rankOneJet connectionSymbol raiseSecond raiseCovector
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

end Burnett.Microlocal.RawCovariance
