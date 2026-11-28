import Burnett.Analysis.TransportWard.Weyl.CubicPartitionIntegralSmallness
import Burnett.Analysis.TransportWard.Weyl.PrincipalVariationCutoffCommutatorLimit

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.C01

open Filter MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped BigOperators ContDiff ENNReal Topology

private theorem integrable_schwartz_principal_variation {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z w : J → SchwartzMap E ℂ) :
    Integrable (principalVariationDensity (fun a b i j k => C a b i j k) z (fun i => w i)) := by
  let u (i : J) : E → ℂ := z i
  let v (i : J) : E → ℂ := w i
  have hu (i : J) : BoundedCoordinateJet (u i) := schwartz_bounded_coordinate_jet (z i)
  have hv (i : J) : BoundedCoordinateJet (v i) := schwartz_bounded_coordinate_jet (w i)
  rw [← principal_cubic_linear_density_eq_variation (fun a b i j k => C a b i j k) z v]
  exact ((principal_cubic_mixed_integrable C v u u hv hu hu).add
    (principal_cubic_mixed_integrable C u v u hu hv hu)).add
    (principal_cubic_mixed_integrable C u u v hu hu hv)

private theorem principal_variation_zero_off_test_support {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) (x : E) (h : ∀ i, x ∉ tsupport (w i)) :
    principalVariationDensity C z w x = 0 := by
  have hv (i : J) : w i x = 0 := image_eq_zero_of_notMem_tsupport (h i)
  have hd (i : J) : fderiv ℝ (w i) x = 0 := fderiv_of_notMem_tsupport ℝ (h i)
  simp only [principalVariationDensity, hv, hd, ContinuousLinearMap.zero_apply, mul_zero,
    zero_mul, add_zero, Finset.sum_const_zero]

/-- A finite cubic partition preserves the limiting principal integral when the
test is reapplied to each localized field. Both the differentiated cutoff
remainder and the actual cutoff commutators tend to zero. -/
theorem tendsto_principalVariation_retested_cubic_partition_error_zero
    {J L : Type} [Fintype J] (s : Finset L) (χ : L → SchwartzMap E ℂ)
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (A : ℝ≥0∞) (hA : A < ⊤) (hC : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ A)
    (T : SchwartzMap E ℂ → E → ℂ) (hT : ∀ u, Differentiable ℝ (T u))
    (z w : ℕ → J → SchwartzMap E ℂ)
    (hTest : ∀ n i, (w n i : E → ℂ) = T (z n i))
    (hzR : ∀ n i x, Complex.ofReal (z n i x).re = z n i x)
    (hwR : ∀ n i x, Complex.ofReal (w n i x).re = w n i x)
    (K : Set E) (hK : IsCompact K) (hwK : ∀ n i, tsupport (w n i : E → ℂ) ⊆ K)
    (hcube : ∀ x ∈ K, (fun y => ∑ l ∈ s, χ l y ^ 3) =ᶠ[𝓝 x] fun _ : E => (1 : ℂ))
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρOne : ∀ x ∈ K, ρ x = 1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (hSmall : ∀ n i x, ‖z n i x‖ ≤ ε n) (M : ℝ) (hM : 0 ≤ M)
    (hZ : ∀ n i, ‖(z n i).toLp 2 volume‖ ≤ M) (hW : ∀ n i, ‖(w n i).toLp 2 volume‖ ≤ M)
    (hComm : ∀ l ∈ s, ∃ D : ℝ≥0∞, D < ⊤ ∧ SchwartzOrderZeroJetBound
      (fun u x => T (energyProduct (χ l) u) x - χ l x * T u x) D D)
    (hL3 : ∀ l ∈ s, ∃ (e : ℕ → ℝ) (V : ℝ≥0∞), (∀ n, 0 ≤ e n) ∧
      Tendsto e atTop (𝓝 0) ∧ V < ⊤ ∧
      (∀ n i, eLpNorm (z n i : E → ℂ) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (e n)) ∧
      (∀ n i, eLpNorm (energyProduct (χ l) (z n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal (e n)) ∧
      (∀ n a i, eLpNorm (energyPartial a (z n i) : E → ℂ) (ENNReal.ofReal 3) volume ≤ V) ∧
      (∀ n a i, eLpNorm (energyPartial a (energyProduct (χ l) (z n i)) : E → ℂ)
        (ENNReal.ofReal 3) volume ≤ V)) :
    Tendsto (fun n =>
      (∑ l ∈ s, ∫ x, (principalVariationDensity (fun a b i j k => C a b i j k)
        (fun i => energyProduct (χ l) (z n i)) (fun i => T (energyProduct (χ l) (z n i))) x).re) -
      ∫ x in K, (principalVariationDensity (fun a b i j k => C a b i j k) (z n) (fun i => w n i) x).re)
      atTop (𝓝 0) := by
  classical
  let c (a b : Index) (i j k : J) : E → ℂ := C a b i j k
  let u (n : ℕ) (l : L) (i : J) := energyProduct (χ l) (z n i)
  let v (n : ℕ) (l : L) (i : J) := energyProduct (χ l) (w n i)
  let Q (l : L) (f : SchwartzMap E ℂ) (x : E) := T (energyProduct (χ l) f) x - χ l x * T f x
  let F (n : ℕ) (l : L) := principalVariationDensity c (u n l) (fun i => T (u n l i))
  let G (n : ℕ) (l : L) := principalVariationDensity c (u n l) (fun i => v n l i)
  let H (n : ℕ) (l : L) := principalVariationDensity c (u n l) (fun i => Q l (z n i))
  let P (n : ℕ) := principalVariationDensity c (z n) (fun i => w n i)
  have hPartition := tendsto_principalVariation_cubic_partition_error_zero s χ c
    (fun a b i j k => (C a b i j k).smooth') z w hzR hwR K hK hwK hcube ρ hρ hρc hρOne
    ε hε hLim hSmall M hM hZ hW
  change Tendsto (fun n => ∫ x in K, ((∑ l ∈ s, G n l x) - P n x).re) atTop (𝓝 0) at hPartition
  have hError (l : L) (hl : l ∈ s) :
      (∀ n, Integrable (H n l)) ∧ Tendsto (fun n => ∫ x, H n l x) atTop (𝓝 0) := by
    obtain ⟨D, hD, hQ⟩ := hComm l hl
    obtain ⟨e, N, he, ht, hN, hz, hu, hdz, hdu⟩ := hL3 l hl
    exact tendsto_principalVariation_cutoff_commutator_zero C A hA hC z (fun n => u n l)
      (Q l) D hD hQ e he ht N hN hz hu hdz hdu
  have hRe (l : L) (hl : l ∈ s) : Tendsto (fun n => ∫ x, (H n l x).re) atTop (𝓝 0) := by
    have ht := (Complex.continuous_re.tendsto (0 : ℂ)).comp (hError l hl).2
    refine (by simpa only [Function.comp_apply, Complex.zero_re] using ht :
      Tendsto (fun n => (∫ x, H n l x).re) atTop (𝓝 0)).congr fun n => ?_
    exact (integral_re ((hError l hl).1 n)).symm
  have hCommSum : Tendsto (fun n => ∑ l ∈ s, ∫ x, (H n l x).re) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum s hRe
  have hSplit (n : ℕ) (l : L) (x : E) : F n l x = G n l x + H n l x := by
    have h₁ := principalCubicVariation_cutoff_commutator C (z n) T hT (χ l) x
    have h₂ := principalCubicVariation_cutoff_product c (z n) (fun i => T (z n i))
      (fun i => hT (z n i)) (χ l) x
    dsimp only at h₁
    have hw : (fun i y => χ l y * T (z n i) y) = fun i y => v n l i y := by
      funext i y
      rw [← hTest n i]
      rfl
    change F n l x = _ + H n l x at h₁
    change principalVariationDensity c (u n l) _ x = _ at h₂
    rw [hw] at h₂
    rw [h₁, ← h₂]
  have hG (n : ℕ) (l : L) : Integrable (G n l) :=
    integrable_schwartz_principal_variation C (u n l) (v n l)
  have hP (n : ℕ) : Integrable (P n) := integrable_schwartz_principal_variation C (z n) (w n)
  have hGRe (n : ℕ) (l : L) : Integrable (fun x => (G n l x).re) := (hG n l).re
  have hPRe (n : ℕ) : Integrable (fun x => (P n x).re) := (hP n).re
  have hOutside (n : ℕ) (l : L) (x : E) (hx : x ∉ K) : G n l x = 0 := by
    apply principal_variation_zero_off_test_support
    intro i hi
    apply hx (hwK n i ?_)
    exact tsupport_mul_subset_right hi
  have hPart (n : ℕ) :
      (∫ x in K, ((∑ l ∈ s, G n l x) - P n x).re) =
      (∑ l ∈ s, ∫ x, (G n l x).re) - ∫ x in K, (P n x).re := by
    simp only [Complex.sub_re, Complex.re_sum]
    rw [integral_sub (integrable_finset_sum s (fun l _ => (hGRe n l).integrableOn))
      (hPRe n).integrableOn, integral_finset_sum s (fun l _ => (hGRe n l).integrableOn)]
    congr 1
    exact Finset.sum_congr rfl fun l _ => setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp only [hOutside n l x hx, Complex.zero_re])
  have hPatch (n : ℕ) (l : L) (hl : l ∈ s) :
      (∫ x, (F n l x).re) = (∫ x, (G n l x).re) + ∫ x, (H n l x).re := by
    have equality : (fun x => (F n l x).re) = fun x => (G n l x).re + (H n l x).re := by
      funext x
      rw [hSplit, Complex.add_re]
    have hHRe : Integrable (fun x => (H n l x).re) := ((hError l hl).1 n).re
    rw [equality, integral_add (hGRe n l) hHRe]
  have hLimit := hPartition.add hCommSum
  simp only [add_zero] at hLimit
  refine hLimit.congr fun n => ?_
  change _ = (∑ l ∈ s, ∫ x, (F n l x).re) - ∫ x in K, (P n x).re
  rw [hPart n, Finset.sum_congr rfl (hPatch n), Finset.sum_add_distrib]
  ring

end Burnett.C01
