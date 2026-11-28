import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

/-! Smoothness of the actual first and second Euler variations. -/

set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 5500000
set_option synthInstance.maxSize 4200

noncomputable section

namespace Burnett.V03.Palatini

open Set Filter Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference
open scoped ContDiff BigOperators Topology Matrix.Norms.Elementwise

open private contDiffOn_coordinateMetricFirstJet coordinateMetricFirstJet_line
  coordinateMetricSecondJet_line from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

local notation "E" => CoordinateSpace

private theorem contDiffOn_coordinateMetricSecondJet
    {ι : Type*} [Fintype ι] {U : Set E} (hU : IsOpen U) (g : E → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) (a : Index) (t : ActionSlot ι) :
    ContDiffOn ℝ ∞ (fun y => coordinateMetricSecondJet g y a t) U :=
  ((contDiffOn_coordinateMetricFirstJet hU g hg t).fderiv_of_isOpen hU (by simp)).clm_apply
    contDiffOn_const

private theorem contDiffOn_two_time_partials
    {U : Set E} {W : Set (ℝ × E)} (hW : IsOpen W)
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ ∞ F W)
    (hZero : MapsTo (fun y : E => ((0 : ℝ),y)) U W) :
    ContDiffOn ℝ ∞ (fun y => deriv (fun t => F (t,y)) 0) U ∧
      ContDiffOn ℝ ∞ (fun y => deriv (deriv (fun t => F (t,y))) 0) U := by
  let D (f : ℝ × E → ℝ) (p : ℝ × E) := fderiv ℝ f p (1,0)
  let Z (x : E) : ℝ × E := (0,x)
  have hD (f : ℝ × E → ℝ) (hf : ContDiffOn ℝ ∞ f W) : ContDiffOn ℝ ∞ (D f) W :=
    (hf.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const
  have eq (f : ℝ × E → ℝ) (hf : ContDiffOn ℝ ∞ f W) (p : ℝ × E) (hp : p ∈ W) :
      deriv (fun t => f (t,p.2)) p.1 = D f p := by
    have hd := ((hf.contDiffAt (hW.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have ht : HasDerivAt (fun t : ℝ => (t,p.2)) (1,0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hd.comp_hasDerivAt p.1 ht).deriv
  have hz : ContDiff ℝ ∞ Z := contDiff_const.prodMk contDiff_id
  constructor
  · refine ((hD F hF).comp hz.contDiffOn hZero).congr ?_
    intro y hy
    exact eq F hF (Z y) (hZero hy)
  · refine ((hD (D F) (hD F hF)).comp hz.contDiffOn hZero).congr ?_
    intro y hy
    have near : ∀ᶠ t in 𝓝 (0 : ℝ), (t,y) ∈ W := by
      have hc : Continuous (fun t : ℝ => (t,y)) := continuous_id.prodMk continuous_const
      exact (hc.continuousAt (x := 0)) (hW.mem_nhds (hZero hy))
    have hNear : (fun t => deriv (fun s => F (s,y)) t) =ᶠ[𝓝 (0 : ℝ)] fun t => D F (t,y) :=
      near.mono fun t ht => eq F hF (t,y) ht
    exact hNear.deriv_eq.trans (eq (D F) (hD F hF) (Z y) (hZero hy))

/-- The first and second time derivatives along the same actual affine
Euler path are smooth in space wherever the background is nonsingular. -/
theorem coordinateDensityEuler_affine_variations_contDiffOn
    {ι : Type*} [Fintype ι] (S : ι → Burnett.Analysis.TransportWardSymbol.Mat)
    {U : Set E} (hU : IsOpen U) (g h : E → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (hND : ∀ y ∈ U, Matrix.det (assembleMetricComponents S (g y)) ≠ 0) :
    let f (u : ℝ) (y : E) (i : ι) := coordinateDensityEuler S (fun z => g z + u • h z) y i
    ContDiffOn ℝ ∞ (fun y i => deriv (fun u => f u y i) 0) U ∧
      ContDiffOn ℝ ∞ (fun y i => deriv (deriv (fun u => f u y i)) 0) U := by
  intro f
  let V : Set (ℝ × E) := univ ×ˢ U
  let G (p : ℝ × E) := fieldSegment (assembleMetricComponents S (g p.2))
    (assembleMetricComponents S (h p.2)) p.1
  let J (p : ℝ × E) := fieldSegment (coordinateMetricFirstJet g p.2) (coordinateMetricFirstJet h p.2) p.1
  let K (p : ℝ × E) := fieldSegment (coordinateMetricSecondJet g p.2) (coordinateMetricSecondJet h p.2) p.1
  have hSnd : MapsTo Prod.snd V U := fun _ p => p.2
  have hG : ContDiffOn ℝ ∞ G V := by
    exact (((assembleMetricComponents S).contDiff.comp_contDiffOn hg).comp contDiff_snd.contDiffOn hSnd).add
      (contDiff_fst.contDiffOn.smul
        (((assembleMetricComponents S).contDiff.comp_contDiffOn hh).comp contDiff_snd.contDiffOn hSnd))
  have hJ (t : ActionSlot ι) : ContDiffOn ℝ ∞ (fun p => J p t) V :=
    ((contDiffOn_coordinateMetricFirstJet hU g hg t).comp contDiff_snd.contDiffOn hSnd).add
      (contDiff_fst.contDiffOn.mul
        ((contDiffOn_coordinateMetricFirstJet hU h hh t).comp contDiff_snd.contDiffOn hSnd))
  have hK (a : Index) (t : ActionSlot ι) : ContDiffOn ℝ ∞ (fun p => K p a t) V :=
    ((contDiffOn_coordinateMetricSecondJet hU g hg a t).comp contDiff_snd.contDiffOn hSnd).add
      (contDiff_fst.contDiffOn.mul
        ((contDiffOn_coordinateMetricSecondJet hU h hh a t).comp contDiff_snd.contDiffOn hSnd))
  let W := V ∩ G ⁻¹' nonsingularMetricDomain
  have hW : IsOpen W := hG.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU)
    isOpen_nonsingularMetricDomain
  have hZero : MapsTo (fun y : E => ((0 : ℝ),y)) U W := by
    intro y hy
    refine ⟨⟨mem_univ _,hy⟩, ?_⟩
    change Matrix.det (assembleMetricComponents S (g y) + (0 : ℝ) • assembleMetricComponents S (h y)) ≠ 0
    simpa only [zero_smul, add_zero] using hND y hy
  have hActual (i : ι) : ContDiffOn ℝ ∞ (fun p : ℝ × E => f p.1 p.2 i) W := by
    have hG' : MapsTo G W nonsingularMetricDomain := fun _ p => p.2
    have base : ContDiffOn ℝ ∞ G W := hG.mono inter_subset_left
    have summand₀ (s t : ActionSlot ι) : ContDiffOn ℝ ∞
        (fun p => metricEulerLowerCoefficient S i s t (G p) * J p s * J p t) W :=
      (((contDiffOn_metricEulerLowerCoefficient S i s t).comp base hG').mul
        ((hJ s).mono inter_subset_left)).mul ((hJ t).mono inter_subset_left)
    have summand₁ (a : Index) (t : ActionSlot ι) : ContDiffOn ℝ ∞
        (fun p => metricActionCoefficient S (a,i) t (G p) * K p a t) W :=
      ((contDiffOn_metricActionCoefficient S (a,i) t).comp base hG').mul ((hK a t).mono inter_subset_left)
    have poly : ContDiffOn ℝ ∞ (fun p => metricEulerAtJet S (G p) (J p) (K p) i) W :=
      (ContDiffOn.sum fun s _ => ContDiffOn.sum fun t _ => summand₀ s t).sub
        (ContDiffOn.sum fun a _ => ContDiffOn.sum fun t _ => summand₁ a t)
    apply poly.congr
    intro p hp
    have hy : p.2 ∈ U := hp.1.2
    have hm : assembleMetricComponents S (g p.2 + p.1 • h p.2) = G p := by
      simp only [G, fieldSegment, map_add, map_smul]
    have hd : Matrix.det (assembleMetricComponents S (g p.2 + p.1 • h p.2)) ≠ 0 := by
      rw [hm]
      exact hp.2
    have hFirst := coordinateMetricFirstJet_line g h p.2 p.1
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hh.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
    have hSecond := coordinateMetricSecondJet_line hU g h hg hh p.2 hy p.1
    dsimp only [f]
    rw [coordinateDensityEuler_eq_metricEulerAtJet S hU (fun y => g y + p.1 • h y)
      (hg.add (hh.const_smul p.1)) p.2 hy hd, hm, hFirst, hSecond]
  constructor
  · exact contDiffOn_pi.mpr fun i => (contDiffOn_two_time_partials hW (hActual i) hZero).1
  · exact contDiffOn_pi.mpr fun i => (contDiffOn_two_time_partials hW (hActual i) hZero).2

end Burnett.V03.Palatini
