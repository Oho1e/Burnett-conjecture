import Burnett.Analysis.TransportWard.Weyl.WindowedWeylSchwartzAction
import Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Burnett.V03

open Function Set MeasureTheory Burnett.A03
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.CarlesonEmbedding
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction FrequencyOrderOne)
open Burnett.Analysis.SymmetricEnergy (Op)
open scoped BigOperators ComplexConjugate ContDiff InnerProductSpace

open private actualFirstOrderAction_add actualFirstOrderAction_smul from
  Burnett.Analysis.PrincipalEnergy.Energy.CompactActualFourier

private def compactScalarWeylAction {ι : Type*}
    (a : E → E → ℂ) (ha : FrequencyOrderOne a)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u x, B u x = firstOrderAction a u x)
    (hBc : ∀ u, HasCompactSupport (B u : E → ℂ)) :
    CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι where
  toFun f := ⟨fun i => B (f.val i), fun i => hBc (f.val i)⟩
  map_add' f g := by
    apply Subtype.ext
    funext i
    ext x
    change B (f.val i + g.val i) x = B (f.val i) x + B (g.val i) x
    simp only [hB, actualFirstOrderAction_add ha]
  map_smul' c f := by
    apply Subtype.ext
    funext i
    ext x
    change B (c • f.val i) x = c * B (f.val i) x
    simp only [hB, actualFirstOrderAction_smul ha]

/-- The actual double-cutoff Weyl test acts on the compact matrix domain.
The same action gives the real cubic test after multiplication by `-I`. -/
theorem exists_windowedWeylCompactMatrixTest {ι : Type*} [Fintype ι]
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β))
    (hReal : ∀ x ξ, conj (β x ξ) = β x ξ)
    (hOdd : ∀ x ξ, β x (-ξ) = -β x ξ) :
    ∃ A : CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι,
      (∀ f i x, (A f).val i x = firstOrderAction (windowedWeylLeftSymbol θ β R h) (f.val i) x) ∧
      (∀ f i, tsupport ((A f).val i : E → ℂ) ⊆ tsupport θ) ∧
      (compactTransportOp A).IsSymmetric ∧
      ∀ f : CompactSchwartzComponents ι, (∀ i x, conj (f.val i x) = f.val i x) →
        ∀ i x, conj (((-Complex.I) • A f).val i x) = ((-Complex.I) • A f).val i x := by
  obtain ⟨B,hB,hBs,hSym⟩ := exists_windowedWeylSchwartz_selfAdjoint
    θ β R h hAmp hPlateau hθ hθc hβ hReal
  let a := windowedWeylLeftSymbol θ β R h
  have ha := (windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ).firstBaseFrequency.frequency
  have hBc (u : SchwartzMap E ℂ) : HasCompactSupport (B u : E → ℂ) :=
    hθc.of_isClosed_subset (isClosed_tsupport _) (hBs u)
  let A : CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι :=
    compactScalarWeylAction a ha B hB hBc
  have hA (f : CompactSchwartzComponents ι) (i : ι) : (A f).val i = B (f.val i) := rfl
  refine ⟨A, fun f i x => hB (f.val i) x, fun f i => hBs (f.val i), ?_, ?_⟩
  · intro u v
    obtain ⟨f,rfl⟩ := (compactMatrixTestEquiv ι).surjective u
    obtain ⟨g,rfl⟩ := (compactMatrixTestEquiv ι).surjective v
    simp only [compactTransportOp_apply, compactMatrixTestEquiv_inner, hA]
    exact Finset.sum_congr rfl fun i _ => (hSym (g.val i) (f.val i)).symm
  · intro f hf i x
    have hβc (y : E) : Continuous (normalizedWeylSymbol β y) :=
      hβ.smooth.continuous.comp (continuous_const.prodMk continuous_id)
    have hAnti := windowedWeyl_leftAction_anticommutes θ β R h hβc hReal hOdd
      (f.val i) (f.val i) (fun y => (hf i y).symm) x
    rw [← hB] at hAnti
    change conj ((-Complex.I) * B (f.val i) x) = (-Complex.I) * B (f.val i) x
    rw [map_mul, map_neg, Complex.conj_I, hAnti]
    ring

/-- Converting the actual Weyl test to the real cubic test fixes the sign
under Lean's conjugate-first inner product. -/
theorem compactMatrixTest_minusI_pair_re {ι : Type*} [Fintype ι]
    (A : CompactSchwartzComponents ι →ₗ[ℂ] CompactSchwartzComponents ι)
    (f g : CompactSchwartzComponents ι) :
    (⟪compactMatrixTestEquiv ι ((-Complex.I) • A f), compactMatrixTestEquiv ι g⟫_ℂ).re =
      -(⟪(compactTransportOp A) (compactMatrixTestEquiv ι f), compactMatrixTestEquiv ι g⟫_ℂ).im := by
  simp only [compactTransportOp_apply, map_smul, inner_smul_left, map_neg, Complex.conj_I,
    neg_neg, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]

end Burnett.V03
