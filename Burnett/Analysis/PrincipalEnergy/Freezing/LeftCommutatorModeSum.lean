import Burnett.Analysis.PrincipalEnergy.Freezing.RadianPrincipalCommutator

set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform Topology

theorem actual_coordinate_jet_schwartz_mul (f : SchwartzMap E ℂ) (W : E → ℂ)
    (dW : Differentiable ℝ W) (j : Index) :
    actualCoordinateJet (fun x => f x * W x) j =
      (fun x => energyPartial j f x * W x + f x * actualCoordinateJet W j x) := by
  funext x
  change fderiv ℝ ((f : E → ℂ) * W) x (EuclideanSpace.single j 1) = _
  rw [fderiv_mul (f.differentiable x) (dW x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    actualCoordinateJet, energyPartial, SchwartzMap.pderivCLM_apply]
  ring

/-- Multiplication of the output by a fixed Schwartz coefficient uses
one ordinary Leibniz rule and the actual sup norms of that coefficient. -/
theorem schwartz_order_zero_jet_bound_output_product (f : SchwartzMap E ℂ)
    (Q : SchwartzMap E ℂ → E → ℂ) (A B P T : ℝ≥0∞)
    (hQ : SchwartzOrderZeroJetBound Q A B)
    (val : eLpNorm (f : E → ℂ) ⊤ volume ≤ P)
    (jet : ∀ j : Index, eLpNorm (energyPartial j f : E → ℂ) ⊤ volume ≤ T) :
    SchwartzOrderZeroJetBound (fun u x => f x * Q u x) (P*A) (T*A+P*B) := by
  intro u
  let p := ENNReal.ofReal 3
  let W := Q u
  let Y := eLpNorm (u : E → ℂ) p volume
  obtain ⟨hV,vBound,hDiff,hGrad⟩ := hQ u
  have mix (s : SchwartzMap E ℂ) (v : E → ℂ) (hv : MemLp v p volume) :
      MemLp (fun x => s x * v x) p volume ∧
        eLpNorm (fun x => s x * v x) p volume ≤ eLpNorm (s : E → ℂ) ⊤ volume * eLpNorm v p volume :=
    ⟨hv.mul' (s.memLp ⊤ volume),
      eLpNorm_smul_le_mul_eLpNorm (φ := (s : E → ℂ)) (f := v) (p := ⊤) (q := p) (r := p)
        hv.1 s.continuous.aestronglyMeasurable⟩
  have base := mix f W hV
  refine ⟨base.1, base.2.trans ((mul_le_mul val vBound bot_le bot_le).trans_eq (mul_assoc _ _ _).symm),
    f.differentiable.mul hDiff,?_⟩
  intro j d
  have dj : d = (fun x => energyPartial j f x * W x + f x * actualCoordinateJet W j x) :=
    actual_coordinate_jet_schwartz_mul f W hDiff j
  rw [dj]
  let X := eLpNorm (energyPartial j u : E → ℂ) p volume
  have left := mix (energyPartial j f) W hV
  have right := mix f (actualCoordinateJet W j) (hGrad j).1
  refine ⟨left.1.add right.1,(eLpNorm_add_le left.1.1 right.1.1 (by norm_num [p])).trans ?_⟩
  calc
    _ ≤ T*(A*Y) + P*(A*X + B*Y) :=
      add_le_add (left.2.trans (mul_le_mul (jet j) vBound bot_le bot_le))
        (right.2.trans (mul_le_mul val (hGrad j).2 bot_le bot_le))
    _ = _ := by change _ = (P*A)*X + (T*A+P*B)*Y; ring

/-- The actual mode commutators form a W¹,³ action as soon as the first
coefficient seminorms and the common Fourier budgets have finite sums. -/
theorem exists_separated_left_commutator_mode_sum_W13 {ι : Type} [Countable ι]
    (f : ι → SchwartzMap E ℂ) (b : ι → E → ℝ)
    (bSmooth : ∀ i, ContDiffOn ℝ ∞ (b i) {ξ | ξ ≠ 0})
    (hom : ∀ i (t : ℝ), 0 < t → ∀ ξ, b i (t • ξ) = t * b i ξ)
    (D U V : ι → ℝ) (D0 : ∀ i, 0 ≤ D i) (U0 : ∀ i, 0 ≤ U i) (V0 : ∀ i, 0 ≤ V i)
    (bJets : ∀ i, ∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (b i) ξ‖ ≤ D i)
    (fBound : ∀ i x, ‖f i x‖ ≤ U i)
    (fJets : ∀ i (j : Index) (x : E), ‖energyPartial j (f i) x‖ ≤ V i)
    (S : Summable (fun i => D i * (U i + V i)))
    (F₁ F₂ : ℝ) (F₁0 : 0 ≤ F₁) (F₂0 : 0 ≤ F₂) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ θ : SchwartzMap E ℂ, patchFourierMoment 1 θ ≤ F₁ → patchFourierMoment 2 θ ≤ F₂ →
        SchwartzOrderZeroJetBound (fun u x => ∑' i, f i x * radianCommutator (b i) θ u x) A A := by
  obtain ⟨K,K0,estimates⟩ := exists_radian_commutator_order_zero_W13
  have τ0 : 0 ≤ tau := by unfold tau; positivity
  let L := max 1 (max K tau)
  have L1 : 1 ≤ L := le_max_left _ _
  have L0 : 0 ≤ L := zero_le_one.trans L1
  have KL : K ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have TL : tau ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  let P := F₁ + tau * F₂
  have P0 : 0 ≤ P := add_nonneg F₁0 (mul_nonneg τ0 F₂0)
  let w (i : ι) := L * (D i * (U i + V i)) * P
  have hw : Summable w := (S.mul_left L).mul_right P
  have w0 (i : ι) : 0 ≤ w i := mul_nonneg (mul_nonneg L0 (mul_nonneg (D0 i) (add_nonneg (U0 i) (V0 i)))) P0
  refine ⟨ENNReal.ofReal (∑' i, w i), ENNReal.ofReal_lt_top, ?_⟩
  intro θ θ1 θ2 u
  let C (i : ι) := radianCommutator (b i) θ u
  let G (i : ι) (x : E) := f i x * C i x
  let p := ENNReal.ofReal 3
  let Y := eLpNorm (u : E → ℂ) p volume
  let X (j : Index) := eLpNorm (energyPartial j u : E → ℂ) p volume
  let M := patchFourierMoment 0 u + ∑ j : Index, patchFourierMoment 0 (energyPartial j u)
  have M0 : 0 ≤ M := add_nonneg (patch_moment_nonneg _ _) (Finset.sum_nonneg fun _ _ => patch_moment_nonneg _ _)
  have uM : patchFourierMoment 0 u ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => patch_moment_nonneg _ _)
  have gM (j : Index) : patchFourierMoment 0 (energyPartial j u) ≤ M :=
    (Finset.single_le_sum (fun k _ => patch_moment_nonneg 0 (energyPartial k u))
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left (patch_moment_nonneg _ _))
  have cp (i : ι) (s v : SchwartzMap E ℂ) := radian_commutator_pointwise_and_coordinate
    (b i) (bSmooth i) (hom i) (D i) (D0 i) (bJets i 1 (by decide)) s v
  have hP₁ : patchFourierMoment 1 θ ≤ P := θ1.trans (le_add_of_nonneg_right (mul_nonneg τ0 F₂0))
  have hP₂ (j : Index) : patchFourierMoment 1 (energyPartial j θ) ≤ tau * F₂ :=
    (patch_fourier_moment_partial 1 j θ).trans (mul_le_mul_of_nonneg_left θ2 τ0)
  have firstP : F₁ ≤ P := le_add_of_nonneg_right (mul_nonneg τ0 F₂0)
  have product (i : ι) (k q r : ℝ) (kL : k ≤ L) (q0 : 0 ≤ q) (qr : q ≤ r) :
      k * D i * q ≤ L * D i * r :=
    mul_le_mul (mul_le_mul_of_nonneg_right kL (D0 i)) qr q0 (mul_nonneg L0 (D0 i))
  have point (i : ι) (s v : SchwartzMap E ℂ) (x : E) (q : ℝ) (q0 : 0 ≤ q)
      (qs : patchFourierMoment 1 s ≤ q) (vM : patchFourierMoment 0 v ≤ M) :
      ‖radianCommutator (b i) s v x‖ ≤ (tau * D i * q) * M :=
    ((cp i s v).1 x).trans (mul_le_mul (mul_le_mul_of_nonneg_left qs (mul_nonneg τ0 (D0 i)))
      vM (patch_moment_nonneg _ _) (mul_nonneg (mul_nonneg τ0 (D0 i)) q0))
  have cv (i : ι) (x : E) :
      ‖C i x‖ ≤ (tau * D i * F₁) * M := point i θ u x F₁ F₁0 θ1 uM
  have dv (i : ι) (j : Index) (x : E) :
      ‖actualCoordinateJet (C i) j x‖ ≤ (tau * D i * P) * M := by
    rw [(cp i θ u).2.2 j |>.2, Pi.add_apply]
    calc
      _ ≤ ‖radianCommutator (b i) (energyPartial j θ) u x‖ + ‖radianCommutator (b i) θ (energyPartial j u) x‖ :=
        norm_add_le _ _
      _ ≤ (tau * D i * (tau * F₂))*M + (tau * D i * F₁)*M :=
        add_le_add (point i (energyPartial j θ) u x (tau*F₂) (mul_nonneg τ0 F₂0) (hP₂ j) uM)
          (point i θ (energyPartial j u) x F₁ F₁0 θ1 (gM j))
      _ = _ := by dsimp only [P]; ring
  have gd (i : ι) : Differentiable ℝ (G i) := (f i).differentiable.mul (cp i θ u).2.1
  have gc (i : ι) (j : Index) : Continuous (actualCoordinateJet (G i) j) := by
    rw [actual_coordinate_jet_schwartz_mul (f i) (C i) (cp i θ u).2.1]
    exact ((energyPartial j (f i)).continuous.mul (cp i θ u).2.1.continuous).add
      ((f i).continuous.mul ((cp i θ u).2.2 j).1)
  have bounds (i : ι) (x : E) : ‖G i x‖ ≤ w i * M := by
    change ‖f i x * C i x‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ U i * ((tau * D i * F₁) * M) := mul_le_mul (fBound i x) (cv i x) (norm_nonneg _) (U0 i)
      _ ≤ (U i + V i) * ((L * D i * P) * M) :=
        mul_le_mul (le_add_of_nonneg_right (V0 i))
          (mul_le_mul_of_nonneg_right (product i tau F₁ P TL F₁0 firstP) M0)
          (mul_nonneg (mul_nonneg (mul_nonneg τ0 (D0 i)) F₁0) M0) (add_nonneg (U0 i) (V0 i))
      _ = _ := by dsimp only [w]; ring
  have jbound (i : ι) (j : Index) (x : E) : ‖actualCoordinateJet (G i) j x‖ ≤ w i * M := by
    rw [actual_coordinate_jet_schwartz_mul (f i) (C i) (cp i θ u).2.1]
    calc
      _ ≤ V i * ((tau * D i * F₁)*M) + U i * ((tau * D i * P)*M) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (fJets i j x) (cv i x) (norm_nonneg _) (V0 i))
          (mul_le_mul (fBound i x) (dv i j x) (norm_nonneg _) (U0 i))
      _ ≤ V i * ((L * D i * P)*M) + U i * ((L * D i * P)*M) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (product i tau F₁ P TL F₁0 firstP) M0) (V0 i))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (product i tau P P TL P0 le_rfl) M0) (U0 i))
      _ = _ := by dsimp only [w]; ring
  have el (i : ι) :=
    schwartz_order_zero_jet_bound_output_product (f i) (radianCommutator (b i) θ) _ _
      (ENNReal.ofReal (U i)) (ENNReal.ofReal (V i)) (estimates (b i) (bSmooth i) (hom i) (D i) (D0 i) (bJets i) θ)
      (by rw [eLpNorm_exponent_top]; exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (fBound i)))
      (fun j => by rw [eLpNorm_exponent_top]; exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall (fJets i j)))
  have coeff0 (i : ι) : ENNReal.ofReal (U i) * ENNReal.ofReal (K*D i*patchFourierMoment 1 θ) ≤ ENNReal.ofReal (w i) := by
    rw [← ENNReal.ofReal_mul (U0 i)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (U i + V i) * (L * D i * P) :=
        mul_le_mul (le_add_of_nonneg_right (V0 i))
          (product i K _ P KL (patch_moment_nonneg _ _) hP₁)
          (mul_nonneg (mul_nonneg K0 (D0 i)) (patch_moment_nonneg _ _))
          (add_nonneg (U0 i) (V0 i))
      _ = _ := by dsimp only [w]; ring
  have coeff1 (i : ι) : ENNReal.ofReal (V i) * ENNReal.ofReal (K*D i*patchFourierMoment 1 θ) +
      ENNReal.ofReal (U i) * ENNReal.ofReal (K*D i*tau*patchFourierMoment 2 θ) ≤ ENNReal.ofReal (w i) := by
    rw [← ENNReal.ofReal_mul (V0 i), ← ENNReal.ofReal_mul (U0 i), ← ENNReal.ofReal_add
      (mul_nonneg (V0 i) (mul_nonneg (mul_nonneg K0 (D0 i)) (patch_moment_nonneg _ _)))
      (mul_nonneg (U0 i) (mul_nonneg (mul_nonneg (mul_nonneg K0 (D0 i)) τ0) (patch_moment_nonneg _ _)))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ V i * (L*D i*P) + U i * (L*D i*P) := by
        have m : tau * patchFourierMoment 2 θ ≤ P :=
          (mul_le_mul_of_nonneg_left θ2 τ0).trans (le_add_of_nonneg_left F₁0)
        rw [mul_assoc (K * D i) tau]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (product i K _ P KL (patch_moment_nonneg _ _) hP₁) (V0 i))
          (mul_le_mul_of_nonneg_left (product i K _ P KL (mul_nonneg τ0 (patch_moment_nonneg _ _)) m) (U0 i))
      _ = _ := by dsimp only [w]; ring
  exact summed_order_zero_coordinate_L3 G gd gc w hw w0 M M0 bounds jbound
    Y (u.memLp p volume).eLpNorm_lt_top X (fun j => ((energyPartial j u).memLp p volume).eLpNorm_lt_top)
    (fun i => ⟨(el i u).1,(el i u).2.1.trans (mul_le_mul_right' (coeff0 i) _)⟩)
    (fun i j => by
      have h := (el i u).2.2.2 j
      refine ⟨h.1,h.2.trans ?_⟩
      rw [mul_add]
      exact add_le_add (mul_le_mul_right' (coeff0 i) _) (mul_le_mul_right' (coeff1 i) _))

end Burnett.A03
