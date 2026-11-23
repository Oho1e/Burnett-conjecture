import Burnett.Analysis.Microlocal.Overlap.HalfDensityScalarPairing
import Burnett.Analysis.Microlocal.Overlap.TransportedHalfDensitySchwartz

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open scoped ComplexConjugate ContDiff InnerProduct Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem transportedHalfDensity_recover (c d : M) (S : Set E)
    (hSU : S ⊆ (chartTransition c d).source) (f : E → ℂ) {x : E} (hx : x ∈ S) :
    overlapJacobianWeight c d x • transportedHalfDensity c d S f (overlapTransition c d x) = f x := by
  rw [overlapTransition_eq c d (hSU hx)]
  have hImg : chartTransition c d x ∈ chartTransition c d '' S := mem_image_of_mem _ hx
  rw [transportedHalfDensity, indicator_of_mem hImg, overlapTransition_reverse_apply c d (hSU hx),
    smul_smul, overlapJacobianWeight_inverse_mul c d (hSU hx), one_smul]

/-- Half-density transport preserves the actual L² inner product on the
overlap-supported Schwartz inputs. -/
theorem transportedHalfDensitySchwartz_inner_toLp (c d : M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (chartTransition c d).source) (f g : SchwartzMap E ℂ)
    (hf : tsupport (f : E → ℂ) ⊆ S) (hg : tsupport (g : E → ℂ) ⊆ S) :
    inner ℂ ((transportedHalfDensitySchwartz c d S hS hSU f hf).toLp 2 volume)
      ((transportedHalfDensitySchwartz c d S hS hSU g hg).toLp 2 volume) =
      inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  let F := transportedHalfDensitySchwartz c d S hS hSU f hf
  let G := transportedHalfDensitySchwartz c d S hS hSU g hg
  have hPair (u v : SchwartzMap E ℂ) : inner ℂ (u.toLp 2 volume) (v.toLp 2 volume) =
      ∫ y, conj (u y) * v y := by
    rw [L2.inner_def]
    exact integral_congr_ae (by
      filter_upwards [u.coeFn_toLp 2 volume, v.coeFn_toLp 2 volume] with x hx hy
      simp only [RCLike.inner_apply', hx, hy])
  change inner ℂ (F.toLp 2 volume) (G.toLp 2 volume) = _
  rw [hPair, hPair]
  have h := integral_transportHalfDensity_pairing c d S hS hSU
    f (fun _ => 1) (transportedHalfDensity c d S g)
  simp only [one_mul] at h
  change (∫ y, conj (transportedHalfDensity c d S f y) * transportedHalfDensity c d S g y) = _
  rw [h]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ S
  · rw [indicator_of_mem hx, transportedHalfDensity_recover c d S hSU g hx]
  · have hz : f x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := (f : E → ℂ)) (fun h => hx (hf h))
    simp only [hz, map_zero, zero_mul]

theorem transportedHalfDensitySchwartz_norm_toLp (c d : M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (chartTransition c d).source) (f : SchwartzMap E ℂ)
    (hf : tsupport (f : E → ℂ) ⊆ S) :
    ‖(transportedHalfDensitySchwartz c d S hS hSU f hf).toLp 2 volume‖ =
      ‖f.toLp 2 volume‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), transportedHalfDensitySchwartz_inner_toLp]

end Burnett.Microlocal.Overlap
