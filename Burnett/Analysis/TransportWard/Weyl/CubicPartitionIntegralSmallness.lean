import Burnett.Analysis.PrincipalEnergy.Freezing.CubicPartitionWeylSupport
import Burnett.Analysis.TransportWard.Weyl.CubicBackgroundCompactLimits

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.C01

open Filter MeasureTheory Set Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped BigOperators ContDiff Topology

/-- The terms with two cutoff derivatives vanish for the actual real
Schwartz fields. The undifferentiated Weyl test needs only a uniform
(L^2) bound and its fixed compact support. -/
theorem tendsto_principalVariation_cubic_partition_error_zero {J L : Type} [Fintype J]
    (s : Finset L) (χ : L → SchwartzMap E ℂ)
    (C : Index → Index → J → J → J → E → ℂ)
    (hC : ∀ a b i j k, ContDiff ℝ ∞ (C a b i j k))
    (z w : ℕ → J → SchwartzMap E ℂ)
    (hzR : ∀ n i x, Complex.ofReal (z n i x).re = z n i x)
    (hwR : ∀ n i x, Complex.ofReal (w n i x).re = w n i x)
    (K : Set E) (hK : IsCompact K)
    (hwK : ∀ n i, tsupport (w n i : E → ℂ) ⊆ K)
    (hcube : ∀ x ∈ K, (fun y => ∑ l ∈ s, χ l y ^ 3) =ᶠ[𝓝 x] fun _ : E => (1 : ℂ))
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρOne : ∀ x ∈ K, ρ x = 1)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hLim : Tendsto ε atTop (𝓝 0))
    (hSmall : ∀ n i x, ‖z n i x‖ ≤ ε n) (M : ℝ) (hM : 0 ≤ M)
    (hZ : ∀ n i, ‖(z n i).toLp 2 volume‖ ≤ M)
    (hW : ∀ n i, ‖(w n i).toLp 2 volume‖ ≤ M) :
    Tendsto (fun n => ∫ x in K,
      ((∑ l ∈ s, principalVariationDensity C (fun i => energyProduct (χ l) (z n i))
          (fun i y => χ l y * w n i y) x) -
        principalVariationDensity C (z n) (fun i y => w n i y) x).re) atTop (𝓝 0) := by
  classical
  let T := Index × Index × J × J × J
  let D (q : T) (x : E) :=
    C q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 x *
      (∑ l ∈ s, χ l x * energyPartial q.1 (χ l) x * energyPartial q.2.1 (χ l) x)
  have hD (q : T) : ContDiff ℝ ∞ (D q) := by
    apply (hC _ _ _ _ _).mul
    exact ContDiff.sum (s := s) fun l _ =>
      ((χ l).smooth'.mul (energyPartial q.1 (χ l)).smooth').mul
        (energyPartial q.2.1 (χ l)).smooth'
  let F (q : T) (i j k : J) (n : ℕ) (x : E) :=
    (D q x).re * (z n i x).re * (z n j x).re * (w n k x).re
  have hFi (q : T) (i j k : J) (n : ℕ) : IntegrableOn (F q i j k n) K := by
    have h₀ := Complex.continuous_re.comp (hD q).continuous
    have h₁ := Complex.continuous_re.comp (z n i).continuous
    have h₂ := Complex.continuous_re.comp (z n j).continuous
    have h₃ := Complex.continuous_re.comp (w n k).continuous
    exact (((h₀.mul h₁).mul h₂).mul h₃).continuousOn.integrableOn_compact hK
  have hFt (q : T) (i j k : J) :
      Tendsto (fun n => ∫ x in K, F q i j k n x) atTop (𝓝 0) :=
    Burnett.V03.Palatini.tendsto_compact_cubicBackground_valuePair_zero
      (U := univ) isOpen_univ hK (fun x => (D q x).re) ρ
      (Complex.reCLM.contDiff.comp (hD q)).contDiffOn hρ (subset_univ _) hρc hρOne
      (fun n => z n i) (fun n => z n j) (fun n => w n k)
      (fun n => hzR n i) (fun n => hzR n j) (fun n => hwK n k)
      ε hε hLim (fun n => hSmall n i) M hM (fun n => hZ n j) (fun n => hW n k)
  let G (q : T) (n : ℕ) :=
    F q q.2.2.2.1 q.2.2.2.2 q.2.2.1 n +
      F q q.2.2.1 q.2.2.2.2 q.2.2.2.1 n +
      F q q.2.2.1 q.2.2.2.1 q.2.2.2.2 n
  have hGi (q : T) (n : ℕ) : IntegrableOn (G q n) K :=
    (((hFi q _ _ _ n).add (hFi q _ _ _ n)).add (hFi q _ _ _ n))
  have hGt (q : T) : Tendsto (fun n => ∫ x in K, G q n x) atTop (𝓝 0) := by
    have h := ((hFt q q.2.2.2.1 q.2.2.2.2 q.2.2.1).add
      (hFt q q.2.2.1 q.2.2.2.2 q.2.2.2.1)).add (hFt q q.2.2.1 q.2.2.2.1 q.2.2.2.2)
    simp only [add_zero] at h
    refine h.congr' (Eventually.of_forall fun n => ?_)
    have hA := hFi q q.2.2.2.1 q.2.2.2.2 q.2.2.1 n
    have hB := hFi q q.2.2.1 q.2.2.2.2 q.2.2.2.1 n
    have hC₁ := hFi q q.2.2.1 q.2.2.2.1 q.2.2.2.2 n
    exact ((integral_add (hA.add hB) hC₁).trans
      (congrArg (fun v : ℝ => v + ∫ x in K, F q q.2.2.1 q.2.2.2.1 q.2.2.2.2 n x)
        (integral_add hA hB))).symm
  have hSum : Tendsto (fun n => ∑ q : T, ∫ x in K, G q n x) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum (Finset.univ : Finset T) (fun q _ => hGt q)
  have hProd (d a b c : ℂ) (ha : Complex.ofReal a.re = a) (hb : Complex.ofReal b.re = b)
      (hc : Complex.ofReal c.re = c) : (d * (a * b * c)).re = d.re * a.re * b.re * c.re := by
    rw [← ha, ← hb, ← hc]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero]
    ring
  refine hSum.congr' (Eventually.of_forall fun n => ?_)
  rw [← integral_finset_sum Finset.univ (fun q _ => hGi q n)]
  apply integral_congr_ae
  filter_upwards with x
  rw [principalVariation_cubic_partition_of_output_support s χ C (z n) (fun i => w n i)
    (fun i => (w n i).differentiable) K (hwK n) hcube x, add_sub_cancel_left]
  simp only [T, Fintype.sum_prod_type, G, Pi.add_apply, F, D, Complex.re_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  simp only [mul_add, Complex.add_re]
  rw [hProd _ _ _ _ (hwR _ _ _) (hzR _ _ _) (hzR _ _ _),
    hProd _ _ _ _ (hzR _ _ _) (hwR _ _ _) (hzR _ _ _),
    hProd _ _ _ _ (hzR _ _ _) (hzR _ _ _) (hwR _ _ _)]
  ring

end Burnett.C01
