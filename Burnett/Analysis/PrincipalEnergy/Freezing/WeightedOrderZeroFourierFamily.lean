import Burnett.Analysis.PrincipalEnergy.Freezing.CompactWeylOrderOneLimit
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedTestOrderZeroAlgebra

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped FourierTransform ENNReal ContDiff

private def orderZeroBaseMoments (f : SchwartzMap E ℂ) : ℝ :=
  patchFourierMoment 0 f + patchFourierMoment 1 f

private def orderZeroBaseFirstJetMoments (f : SchwartzMap E ℂ) : ℝ :=
  tau * (patchFourierMoment 1 f + patchFourierMoment 2 f)

private theorem base_moments_nonneg (f : SchwartzMap E ℂ) : 0 ≤ orderZeroBaseMoments f :=
  add_nonneg (patch_moment_nonneg _ _) (patch_moment_nonneg _ _)

private theorem base_jet_moments_nonneg (f : SchwartzMap E ℂ) : 0 ≤ orderZeroBaseFirstJetMoments f :=
  mul_nonneg (by unfold tau; positivity) (add_nonneg (patch_moment_nonneg _ _) (patch_moment_nonneg _ _))

private theorem base_moments_partial (f : SchwartzMap E ℂ) (j : Index) :
    orderZeroBaseMoments (energyPartial j f) ≤ orderZeroBaseFirstJetMoments f := by
  unfold orderZeroBaseMoments orderZeroBaseFirstJetMoments
  rw [mul_add]
  exact add_le_add (patch_fourier_moment_partial 0 j f) (patch_fourier_moment_partial 1 j f)

private theorem weighted_base_moment_integral (f : SchwartzMap E ℂ) (A : ℝ) :
    Integrable (fun η : E => (A*(1+‖η‖))*‖(SchwartzMap.fourierTransformCLM ℂ f) η‖) volume ∧
      (∫ η : E, (A*(1+‖η‖))*‖(SchwartzMap.fourierTransformCLM ℂ f) η‖) = A * orderZeroBaseMoments f := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have eq (η : E) : (A*(1+‖η‖))*‖F η‖ = A * (‖F η‖ + ‖η‖^1 * ‖F η‖) := by
    rw [pow_one]
    ring
  change Integrable (fun η => (A*(1+‖η‖))*‖F η‖) volume ∧ (∫ η, (A*(1+‖η‖))*‖F η‖) = _
  simp_rw [eq]
  refine ⟨(F.integrable.norm.add (F.integrable_pow_mul volume 1)).const_mul A,?_⟩
  rw [integral_const_mul, integral_add F.integrable.norm (F.integrable_pow_mul volume 1)]
  simp only [orderZeroBaseMoments, patchFourierMoment, pow_zero, one_mul, F, SchwartzMap.fourierTransformCLM_apply]

/-- A frequency shift difference whose operator and pointwise bounds grow
at most linearly in the base Fourier variable retains the displayed input
jet and consumes at most two moments of the fixed coefficient. -/
theorem weighted_radian_order_zero_jet_and_pointwise (m : E × E → ℝ)
    (mM : Measurable m) (D : ℝ) (D0 : 0 ≤ D)
    (point : ∀ η ξ, ‖m (η,ξ)‖ ≤ D * (1+‖η‖))
    (sectionBound : ∀ (η : E) (u : SchwartzMap E ℂ),
      MemLp (radianAction (fun ξ => m (η,ξ)) u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (radianAction (fun ξ => m (η,ξ)) u) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal (D*(1+‖η‖)) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume)
    (f : SchwartzMap E ℂ) :
    SchwartzOrderZeroJetBound (radianFourierAverage m f)
      (ENNReal.ofReal (D * orderZeroBaseMoments f))
      (ENNReal.ofReal (D * orderZeroBaseFirstJetMoments f)) ∧
      ∀ u : SchwartzMap E ℂ,
        (∀ x, ‖radianFourierAverage m f u x‖ ≤ D * orderZeroBaseMoments f * patchFourierMoment 0 u) ∧
          ∀ j : Index, let d := actualCoordinateJet (radianFourierAverage m f u) j
            Continuous d ∧ ∀ x, ‖d x‖ ≤ D * orderZeroBaseFirstJetMoments f * patchFourierMoment 0 u +
              D * orderZeroBaseMoments f * patchFourierMoment 0 (energyPartial j u) := by
  let A (η : E) := D*(1+‖η‖)
  have A0 (η : E) : 0 ≤ A η := mul_nonneg D0 (by positivity)
  have mg : RadianAverageGrowth m := ⟨D,D0,fun η ξ =>
    (point η _).trans (le_mul_of_one_le_right (A0 η) (le_add_of_nonneg_right (norm_nonneg _)))⟩
  have diff (g v : SchwartzMap E ℂ) : Differentiable ℝ (radianFourierAverage m g v) :=
    fun x => (radian_fourier_average_coordinate m mM mg g v 0 x).1
  have lip (g v : SchwartzMap E ℂ) :=
    radian_fourier_average_L3_bound m mM mg g v A A0 point
      (weighted_base_moment_integral g D).1 _ (v.memLp (ENNReal.ofReal 3) volume).eLpNorm_lt_top
      (fun η => sectionBound η v)
  have L (g v : SchwartzMap E ℂ) :
      MemLp (radianFourierAverage m g v) (ENNReal.ofReal 3) volume ∧
        eLpNorm (radianFourierAverage m g v) (ENNReal.ofReal 3) volume ≤
          ENNReal.ofReal (D*orderZeroBaseMoments g) * eLpNorm (v : E → ℂ) (ENNReal.ofReal 3) volume := by
    have e := lip g v
    rw [show (∫ η, A η * ‖𝓕 (g : E → ℂ) η‖) = D * orderZeroBaseMoments g
      from (weighted_base_moment_integral g D).2] at e
    exact e
  have Jet (u : SchwartzMap E ℂ) (j : Index) :
      actualCoordinateJet (radianFourierAverage m f u) j =
        radianFourierAverage m (energyPartial j f) u + radianFourierAverage m f (energyPartial j u) :=
    funext fun x => (radian_fourier_average_coordinate m mM mg f u j x).2
  refine ⟨?_,?_⟩
  · intro u
    refine ⟨(L f u).1,(L f u).2,diff f u,?_⟩
    intro j d
    have e : d = _ := Jet u j
    rw [e]
    have h1 := L (energyPartial j f) u
    have h2 := L f (energyPartial j u)
    refine ⟨h1.1.add h2.1,(eLpNorm_add_le h1.1.1 h2.1.1 (by norm_num)).trans ?_⟩
    rw [add_comm]
    exact add_le_add h2.2 (h1.2.trans (mul_le_mul_right'
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (base_moments_partial f j) D0)) _))
  have pt (g v : SchwartzMap E ℂ) (x : E) :
      ‖radianFourierAverage m g v x‖ ≤ D * orderZeroBaseMoments g * patchFourierMoment 0 v := by
    rw [radian_fourier_average_eq_integral m mM mg]
    let G := SchwartzMap.fourierTransformCLM ℂ g
    let V := SchwartzMap.fourierTransformCLM ℂ v
    let Q := patchFourierMoment 0 v
    have q0 : 0 ≤ Q := patch_moment_nonneg _ _
    have eq : D*orderZeroBaseMoments g*Q = ∫ η : E, (A η * ‖G η‖)*Q := by
      rw [integral_mul_const, show (∫ η : E, A η * ‖G η‖) = D*orderZeroBaseMoments g
        from (weighted_base_moment_integral g D).2]
    rw [eq]
    apply norm_integral_le_of_norm_le ((weighted_base_moment_integral g D).1.mul_const Q)
    filter_upwards with η
    simp only [norm_mul, patch_fourier_phase_norm, one_mul]
    change ‖G η‖ * ‖radianAction (fun ξ => m (η,ξ)) v x‖ ≤ _
    have h := norm_radian_action_le_of_symbol_bound (fun ξ => m (η,ξ)) (A η) (point η) v x
    have q : (∫ ξ : E, ‖𝓕 (v : E → ℂ) ξ‖) = Q := by simp [Q, patchFourierMoment]
    rw [q] at h
    exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)
  intro u
  refine ⟨pt f u,?_⟩
  intro j d
  have e : d = _ := Jet u j
  rw [e]
  refine ⟨(diff _ _).continuous.add (diff _ _).continuous,?_⟩
  intro x
  refine (norm_add_le _ _).trans (add_le_add ((pt _ _ x).trans ?_) (pt _ _ x))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (base_moments_partial f j) D0) (patch_moment_nonneg _ _)

/-- Exact order-zero Fourier averages can be summed with one finite jet
bound when the three genuine coefficient moments are summable. -/
theorem exists_weighted_radian_order_zero_mode_sum_W13 {ι : Type} [Countable ι]
    (f : ι → SchwartzMap E ℂ) (m : ι → E × E → ℝ)
    (mM : ∀ i, Measurable (m i)) (D : ι → ℝ) (D0 : ∀ i, 0 ≤ D i)
    (point : ∀ i η ξ, ‖m i (η,ξ)‖ ≤ D i * (1+‖η‖))
    (sectionBound : ∀ i (η : E) (u : SchwartzMap E ℂ),
      MemLp (radianAction (fun ξ => m i (η,ξ)) u) (ENNReal.ofReal 3) volume ∧
      eLpNorm (radianAction (fun ξ => m i (η,ξ)) u) (ENNReal.ofReal 3) volume ≤
        ENNReal.ofReal (D i*(1+‖η‖)) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume)
    (mass : ∀ r : ℕ, r ≤ 2 → Summable (fun i => D i * patchFourierMoment r (f i))) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      SchwartzOrderZeroJetBound (fun u x => ∑' i, radianFourierAverage (m i) (f i) u x) A A := by
  let q0 (i : ι) := D i * orderZeroBaseMoments (f i)
  let q1 (i : ι) := D i * orderZeroBaseFirstJetMoments (f i)
  have q00 (i : ι) : 0 ≤ q0 i := mul_nonneg (D0 i) (base_moments_nonneg _)
  have q10 (i : ι) : 0 ≤ q1 i := mul_nonneg (D0 i) (base_jet_moments_nonneg _)
  have s0 : Summable q0 := by
    have h := (mass 0 (by decide)).add (mass 1 (by decide))
    simpa only [q0, orderZeroBaseMoments, mul_add, Pi.add_apply] using h
  have s1 : Summable q1 := by
    have h := ((mass 1 (by decide)).add (mass 2 (by decide))).mul_left tau
    convert h using 1
    funext i
    dsimp only [q1, orderZeroBaseFirstJetMoments, Pi.add_apply]
    ring
  let w (i : ι) := q0 i + q1 i
  have ws : Summable w := s0.add s1
  have w0 (i : ι) : 0 ≤ w i := add_nonneg (q00 i) (q10 i)
  refine ⟨ENNReal.ofReal (∑' i, w i),ENNReal.ofReal_lt_top,?_⟩
  intro u
  let G (i : ι) := radianFourierAverage (m i) (f i) u
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (u : E → ℂ) p volume
  let X (j : Index) := eLpNorm (energyPartial j u : E → ℂ) p volume
  let Z := patchFourierMoment 0 u
  let Zj (j : Index) := patchFourierMoment 0 (energyPartial j u)
  let M := Z + ∑ j : Index, Zj j
  have Z0 : 0 ≤ Z := patch_moment_nonneg _ _
  have Zj0 (j : Index) : 0 ≤ Zj j := patch_moment_nonneg _ _
  have hZ : Z ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => Zj0 j)
  have hJ (j : Index) : Zj j ≤ M :=
    (Finset.single_le_sum (fun k _ => Zj0 k) (Finset.mem_univ j)).trans (le_add_of_nonneg_left Z0)
  have M0 : 0 ≤ M := Z0.trans hZ
  have H (i : ι) := weighted_radian_order_zero_jet_and_pointwise (m i) (mM i) (D i) (D0 i)
    (point i) (sectionBound i) (f i)
  have V (i : ι) := (schwartz_order_zero_jet_bound_mono _ _ _ _ _ (H i).1
    (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (q10 i)))
    (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (q00 i)))) u
  have v (i : ι) (x : E) : ‖G i x‖ ≤ w i*M :=
    (((H i).2 u).1 x).trans (mul_le_mul (le_add_of_nonneg_right (q10 i)) hZ Z0 (w0 i))
  have cd (i : ι) (j : Index) (x : E) : ‖actualCoordinateJet (G i) j x‖ ≤ w i*M := by
    refine (((H i).2 u).2 j |>.2 x).trans ?_
    change q1 i*Z + q0 i*Zj j ≤ _
    exact (add_le_add (mul_le_mul_of_nonneg_left hZ (q10 i))
      (mul_le_mul_of_nonneg_left (hJ j) (q00 i))).trans_eq (by dsimp only [w]; ring)
  exact summed_order_zero_coordinate_L3 G (fun i => (V i).2.2.1)
    (fun i j => (((H i).2 u).2 j).1) w ws w0 M M0 v cd
    Y (u.memLp p volume).eLpNorm_lt_top X (fun j => ((energyPartial j u).memLp p volume).eLpNorm_lt_top)
    (fun i => ⟨(V i).1,(V i).2.1⟩)
    (fun i j => by simpa only [mul_add] using (V i).2.2.2 j)


end Burnett.A03
