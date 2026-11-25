import Burnett.Analysis.TransportPatches.WideJointWindow
import Burnett.Analysis.TransportPatches.CompactFrequencyJets

/-! The two actual wide error symbols have one sphere-jet bound on the window. -/
set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set Metric Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.V06
open Burnett.A02.FrequencySplit (E)
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Analysis.ProjectiveNullCaps (quadratic pairing rowValue)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ContDiff Manifold Matrix

open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols

local notation "Punctured" => ({0}ᶜ : Set E)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

private theorem joint_phase_smooth (B : Field (M := M)) (c : AtlasChart M) (V : Set E)
    (hV : V ⊆ c.chart.target) (hB : IsSmooth B) (hn : IsNondegenerate B) :
    ContDiffOn ℝ ∞ (fun p : E × E => normalizedFrozenPhase (chartInverseMetric B c p.1) p.2)
      (V ×ˢ Punctured) := by
  let U := V ×ˢ Punctured
  have hG : ContDiffOn ℝ ∞ (fun p : E × E => chartInverseMetric B c p.1) U :=
    (chartInverseMetric_smooth B hB hn c).comp contDiff_fst.contDiffOn (fun _ hp => hV hp.1)
  have hCoord (i : Index) : ContDiffOn ℝ ∞ (fun p : E × E => p.2 i) U :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).contDiffOn
  have hNorm : ContDiffOn ℝ ∞ (fun p : E × E => ‖p.2‖ ^ 2) U :=
    ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffOn
  change ContDiffOn ℝ ∞ (fun p : E × E => quadratic (chartInverseMetric B c p.1) p.2 / ‖p.2‖ ^ 2) U
  apply ContDiffOn.div _ hNorm (fun _ hp => pow_ne_zero 2 (norm_ne_zero_iff.mpr hp.2))
  unfold quadratic pairing rowValue
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.mul _ (hCoord j)
  apply ContDiffOn.sum
  intro i _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hG i) j).mul (hCoord i)

theorem actualWideWindow_sphereJets (B : Field (M := M)) (c : AtlasChart M) (K V : Set E)
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hVU : V ⊆ c.chart.target)
    (hB : IsSmooth B) (hN : IsNondegenerate B) (inner outer : ℝ)
    (hJoint : HasJointWideScreen B c inner outer V)
    (hf : ∀ x ∈ K, WideScreenFrequencySmooth inner outer (chartInverseMetric B c x)) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ (x : E) (hx : x ∈ K), ∀ k i : OrderedPair, ∀ n : ℕ, n ≤ 6 →
      ∀ ξ ∈ sphere (0 : E) 1,
        let m := chartInverseMetric B c x
        let hm := hf x hx
        ‖iteratedFDeriv ℝ n (fun η : E => (frozenScreenErrorAngular inner outer m hm).matrix η k i) ξ‖ ≤ J ∧
        ‖iteratedFDeriv ℝ n (fun η : E => (frozenPhaseErrorAngular inner outer m hm).matrix η k i) ξ‖ ≤ J := by
  let S (k i : OrderedPair) (p : E × E) :=
    globalAngularScreenSymbol inner outer (chartInverseMetric B c p.1) (orderedBasis i) (fun j => p.2 j) k.1 k.2
  let F₁ (k i : OrderedPair) (p : E × E) := (1 : Matrix OrderedPair OrderedPair ℝ) k i - S k i p
  let F₂ (k i : OrderedPair) (p : E × E) := normalizedFrozenPhase (chartInverseMetric B c p.1) p.2 * S k i p
  have hS (k i : OrderedPair) : ContDiffOn ℝ ∞ (S k i) (V ×ˢ Punctured) := hJoint (orderedBasis i) k.1 k.2
  have hF₁ (k i : OrderedPair) : ContDiffOn ℝ ∞ (F₁ k i) (V ×ˢ Punctured) := contDiffOn_const.sub (hS k i)
  have hF₂ (k i : OrderedPair) : ContDiffOn ℝ ∞ (F₂ k i) (V ×ˢ Punctured) :=
    (joint_phase_smooth B c V hVU hB hN).mul (hS k i)
  choose J₁ hJ₁ hB₁ using fun k i => compactChartFamily_uniform_frequency_jets K V hK hV hKV (F₁ k i) (hF₁ k i)
  choose J₂ hJ₂ hB₂ using fun k i => compactChartFamily_uniform_frequency_jets K V hK hV hKV (F₂ k i) (hF₂ k i)
  let J := ∑ k : OrderedPair, ∑ i : OrderedPair, (J₁ k i + J₂ k i)
  have hJ (k i : OrderedPair) : 0 ≤ J₁ k i + J₂ k i := add_nonneg (hJ₁ k i) (hJ₂ k i)
  refine ⟨J, Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ => hJ k i)), ?_⟩
  intro x hx k i n hn ξ hξ m hm
  have hDom : J₁ k i + J₂ k i ≤ J :=
    (Finset.single_le_sum (fun j _ => hJ k j) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hJ a b)) (Finset.mem_univ k))
  exact ⟨(hB₁ k i x hx n hn ξ hξ).trans ((le_add_of_nonneg_right (hJ₂ k i)).trans hDom),
    (hB₂ k i x hx n hn ξ hξ).trans ((le_add_of_nonneg_left (hJ₁ k i)).trans hDom)⟩

end Burnett.C02
