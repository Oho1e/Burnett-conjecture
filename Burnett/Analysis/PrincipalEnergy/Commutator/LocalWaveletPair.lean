import Burnett.Analysis.PrincipalEnergy.Commutator.ScaledWeakPair

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped ComplexConjugate NNReal

/-- Applying the actual ball weak bound to the local oscillation of the
coarser wavelet uses one derivative and gains a full scale ratio. -/
theorem localOscillationRamp_wavelet_weak_bound
    (χ θ η : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ))
    (hχs : tsupport (χ : Space → ℂ) ⊆ Metric.closedBall 0 2) (hχv : ∀ z, ‖χ z‖≤1)
    (D : ℝ) (hD : 0≤D) (hχd : ∀ z, ‖fderiv ℝ (χ : Space → ℂ) z‖≤D)
    (hθ : ∀ z, 1<‖z‖ → θ z=0) (hη : ∀ z, 1<‖z‖ → η z=0) :
    ∃ M : ℝ, 0≤M ∧ ∀ (R : SchwartzMap Space ℂ → SchwartzMap Space ℂ → ℂ)
      (_hLin : ∀ f u g : SchwartzMap Space ℂ, ∀ c : ℂ, R (f-c • u) g=R f g-c*R u g)
      (_hSkew : ∀ f g, R g f= -conj (R f g)) {W : ℝ}
      (_hWeak : ∀ (x : Space) (ρ : ℝ), 0<ρ → ∀ (f g : SchwartzMap Space ℂ),
        tsupport (f : Space → ℂ) ⊆ Metric.closedBall x ρ →
        tsupport (g : Space → ℂ) ⊆ Metric.closedBall x ρ →
        (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
        (∀ (j : Fin 4) z, ‖fderiv ℝ (⇑f) z (coordinateDirection j)‖≤ρ⁻¹) →
        (∀ (j : Fin 4) z, ‖fderiv ℝ (⇑g) z (coordinateDirection j)‖≤ρ⁻¹) →
        ‖R f g‖≤W*ρ^4)
      (s t : ℝ) (hs : 0<s) (ht : 0<t) (x y : Space),
        let f := centeredWavelet θ hθ t ht y
        let g := centeredWavelet η hη s hs x
        ‖R (localOscillationRamp f χ hχ x hs) g‖≤W*M*s*(t^5)⁻¹ := by
  let P := SchwartzMap.seminorm ℝ 0 1 θ
  let Q := SchwartzMap.seminorm ℝ 0 0 η
  let V := SchwartzMap.seminorm ℝ 0 1 η
  have hP : 0≤P := apply_nonneg _ _
  have hQ : 0≤Q := apply_nonneg _ _
  have hV : 0≤V := apply_nonneg _ _
  let A₀ := 4*(1+2*D)*(1+P)
  let B₀ := 4*(1+Q+V)
  have hA₀ : 0<A₀ := by dsimp only [A₀]; positivity
  have hB₀ : 0<B₀ := by dsimp only [B₀]; positivity
  refine ⟨256*A₀*B₀,by positivity,?_⟩
  intro R hLin hSkew W hWeak s t hs ht x y f g
  let u := localOscillationRamp f χ hχ x hs
  let A := A₀*s*(t^5)⁻¹
  let B := B₀*(s^4)⁻¹
  have hA : 0<A := by dsimp only [A]; positivity
  have hB : 0<B := by dsimp only [B]; positivity
  let J : NNReal := ⟨(t^5)⁻¹*P,mul_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _)) hP⟩
  have hLip : LipschitzWith J f := centeredWavelet_lipschitz θ hθ t ht y
  obtain ⟨hUs,_,hUd⟩ := localOscillationRamp_bounds f χ J hLip _
    D hD (centeredWavelet_norm_le θ hθ t ht y) hχ hχs hχv hχd x hs
  have hSupport : tsupport (g : Space → ℂ) ⊆ Metric.closedBall x (4*s) :=
    (centeredWavelet_support η hη s hs x).trans (Metric.closedBall_subset_closedBall (by linarith))
  have hALip : (4*s)*(J:ℝ)≤A := by
    have hAP : 4*P≤A₀ := by
      calc
        _ ≤ 4*(1+P) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hD]) (by positivity)
    calc
      _ = (4*P)*s*(t^5)⁻¹ := by simp only [J,NNReal.coe_mk]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAP hs.le) (by positivity)
  have hUv (z : Space) : ‖u z‖≤A := by
    by_cases hz : z ∈ Metric.closedBall x (4*s)
    · have hZ := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at hZ
      have hDiff : ‖f z-f x‖≤(J:ℝ)*‖z-x‖ := by
        simpa only [dist_eq_norm] using hLip.dist_le_mul z x
      dsimp only [u]
      rw [localOscillationRamp_apply,norm_mul]
      calc
        _ ≤ ‖f z-f x‖ := mul_le_of_le_one_left (norm_nonneg _) (hχv _)
        _ ≤ (J:ℝ)*‖z-x‖ := hDiff
        _ ≤ (4*s)*(J:ℝ) := by
          rw [mul_comm (4*s)]
          exact mul_le_mul_of_nonneg_left hZ J.coe_nonneg
        _ ≤ _ := hALip
    · have hZero : u z=0 := by
        by_contra hn
        exact hz (hUs (subset_closure hn))
      rw [hZero,norm_zero]
      exact hA.le
  have hGv (z : Space) : ‖g z‖≤B := by
    refine (centeredWavelet_norm_le η hη s hs x z).trans ?_
    dsimp only [B]
    rw [mul_comm B₀]
    exact mul_le_mul_of_nonneg_left (by dsimp only [B₀]; linarith only [hQ,hV]) (by positivity)
  have hCoord (L : Space →L[ℝ] ℂ) (j : Fin 4) : ‖L (coordinateDirection j)‖≤‖L‖ := by
    have h := L.le_opNorm (coordinateDirection j)
    simpa only [coordinateDirection,EuclideanSpace.norm_single,norm_one,mul_one] using h
  have hUder (j : Fin 4) (z : Space) : ‖fderiv ℝ (⇑u) z (coordinateDirection j)‖≤(4*s)⁻¹*A := by
    have hAP : (1+2*D)*P≤A₀/4 := by
      rw [show A₀/4=(1+2*D)*(1+P) by dsimp only [A₀]; ring]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc
      _ ≤ ‖fderiv ℝ (⇑u) z‖ := hCoord _ _
      _ ≤ (1+2*D)*(J:ℝ) := hUd z
      _ = ((1+2*D)*P)*(t^5)⁻¹ := by simp only [J,NNReal.coe_mk]; ring
      _ ≤ (A₀/4)*(t^5)⁻¹ := mul_le_mul_of_nonneg_right hAP (by positivity)
      _ = _ := by dsimp only [A]; field_simp [hs.ne',ht.ne']
  have hGder (j : Fin 4) (z : Space) : ‖fderiv ℝ (⇑g) z (coordinateDirection j)‖≤(4*s)⁻¹*B := by
    calc
      _ ≤ ‖fderiv ℝ (⇑g) z‖ := hCoord _ _
      _ ≤ (s^5)⁻¹*V := centeredWavelet_fderiv_bound η hη s hs x z
      _ ≤ (s^5)⁻¹*(B₀/4) := mul_le_mul_of_nonneg_left
        (by dsimp only [B₀]; linarith only [hQ,hV]) (by positivity)
      _ = _ := by dsimp only [B]; field_simp [hs.ne']
  calc
    _ ≤ W*(4*s)^4*A*B := weakPair_amplitude_bound R hLin hSkew hWeak x (4*s) (by positivity)
      u g hUs hSupport A B hA hB hUv hGv hUder hGder
    _ = _ := by dsimp only [A,B]; field_simp [hs.ne',ht.ne']; ring

end Burnett.Analysis.CarlesonEmbedding
