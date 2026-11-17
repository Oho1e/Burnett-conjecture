import Burnett.Geometry.GlobalCovariantDerivative
import Burnett.Geometry.ChartDifferential

/-!
# Algebraic laws of the actual global covariant derivative

The operator is the actual preferred-chart construction in
GlobalCovariantDerivative. All identities below are for values in the
same genuine tangent fiber. Forward tangent coordinates preserve addition
and scalar multiplication only on the chart target; differentiation uses
open-target eventual equality rather than a false global chart extension law.

The first slot is additive and linear over arbitrary scalar functions, and
the second slot is additive at points where the two total-space sections are
differentiable. Constant scalar linearity is valid without a regularity
assumption under mathlib's total fderiv convention over a field. The function
Leibniz law assumes actual point differentiability of the scalar and section,
and its extra term uses the genuine manifold mfderiv on the actual V(m).

These are raw operator laws for any fiberwise bilinear field B; smoothness,
symmetry and nondegeneracy of B are not needed for these algebraic identities.
The operator's intrinsic chart independence and smooth-output interpretation
remain the separately proved geometric results in GlobalCovariantDerivative.
-/

noncomputable section
namespace Burnett.Geometry.GlobalConnectionLaws
open Bundle Set
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ChartVectorField
open Burnett.Geometry.ChartConnectionNaturality Burnett.Geometry.BackgroundConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

def SectionDifferentiableAt (W : ChartVectorField.Field (M := M)) (m : M) : Prop :=
  MDifferentiableAt Model (Model.prod Model)
    (fun p => TotalSpace.mk' CoordinateSpace p (W p)) m

theorem sectionDifferentiableAt_of_isSmooth (W : ChartVectorField.Field (M := M))
    (hW : ChartVectorField.IsSmooth W) (m : M) : SectionDifferentiableAt W m := by
  apply hW.mdifferentiableAt
  change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

theorem coordinateVector_add (U V : ChartVectorField.Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (fun p => U p + V p) c y = coordinateVector U c y + coordinateVector V c y := by
  rw [ChartDifferential.coordinateVector_eq_mfderiv_chart (fun p => U p + V p) c hy,
    ChartDifferential.coordinateVector_eq_mfderiv_chart U c hy,
    ChartDifferential.coordinateVector_eq_mfderiv_chart V c hy]
  exact map_add _ _ _

theorem coordinateVector_fun_smul (f : M → ℝ) (W : ChartVectorField.Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (fun p => f p • W p) c y =
      f ((chartAt CoordinateSpace c).symm y) • coordinateVector W c y := by
  rw [ChartDifferential.coordinateVector_eq_mfderiv_chart (fun p => f p • W p) c hy,
    ChartDifferential.coordinateVector_eq_mfderiv_chart W c hy]
  exact map_smul _ _ _

theorem differentiableAt_coordinateVector (W : ChartVectorField.Field (M := M))
    (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source)
    (hW : SectionDifferentiableAt W m) :
    DifferentiableAt ℝ (coordinateVector W c) (chartAt CoordinateSpace c m) := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  have hframe : MDifferentiableAt Model Model (frameVector W c) m :=
    (e.mdifferentiableAt_section_iff Model W hm).mp hW
  have hi := (mdifferentiable_chart (I := Model) c).mdifferentiableAt_symm
    ((chartAt CoordinateSpace c).mapsTo hm)
  exact (hframe.comp_of_eq (chartAt CoordinateSpace c m) hi
    ((chartAt CoordinateSpace c).left_inv hm)).differentiableAt

theorem derivative_add_left (B : ManifoldBilinear.Field (M := M))
    (U V W : ChartVectorField.Field (M := M)) (m : M) :
    GlobalCovariantDerivative.derivative B (fun p => U p + V p) W m =
      GlobalCovariantDerivative.derivative B U W m + GlobalCovariantDerivative.derivative B V W m := by
  have hy := (chartAt CoordinateSpace m).mapsTo (mem_chart_source CoordinateSpace m)
  unfold GlobalCovariantDerivative.derivative chartDerivative coordinateDerivative
    CoordinateCovariantDerivative.derivative
  rw [coordinateVector_add U V m hy]
  simp only [map_add, CoordinateCovariantDerivative.connectionTerm_add_left]
  abel

theorem derivative_smul_left (B : ManifoldBilinear.Field (M := M))
    (f : M → ℝ) (V W : ChartVectorField.Field (M := M)) (m : M) :
    GlobalCovariantDerivative.derivative B (fun p => f p • V p) W m =
      f m • GlobalCovariantDerivative.derivative B V W m := by
  have hm := mem_chart_source CoordinateSpace m
  have hy := (chartAt CoordinateSpace m).mapsTo hm
  unfold GlobalCovariantDerivative.derivative chartDerivative coordinateDerivative
    CoordinateCovariantDerivative.derivative
  rw [coordinateVector_fun_smul f V m hy, (chartAt CoordinateSpace m).left_inv hm]
  simp only [map_smul, CoordinateCovariantDerivative.connectionTerm_smul_left, map_add, smul_add]

theorem derivative_add_right (B : ManifoldBilinear.Field (M := M))
    (V W Z : ChartVectorField.Field (M := M)) (m : M)
    (hW : SectionDifferentiableAt W m) (hZ : SectionDifferentiableAt Z m) :
    GlobalCovariantDerivative.derivative B V (fun p => W p + Z p) m =
      GlobalCovariantDerivative.derivative B V W m + GlobalCovariantDerivative.derivative B V Z m := by
  have hm := mem_chart_source CoordinateSpace m
  have hy := (chartAt CoordinateSpace m).mapsTo hm
  have hWc := differentiableAt_coordinateVector W m m hm hW
  have hZc := differentiableAt_coordinateVector Z m m hm hZ
  have heq : coordinateVector (fun p => W p + Z p) m =ᶠ[𝓝 (chartAt CoordinateSpace m m)]
      (fun y => coordinateVector W m y + coordinateVector Z m y) := by
    filter_upwards [(chartAt CoordinateSpace m).open_target.mem_nhds hy] with y hyt
    exact coordinateVector_add W Z m hyt
  unfold GlobalCovariantDerivative.derivative chartDerivative coordinateDerivative
    CoordinateCovariantDerivative.derivative
  rw [heq.fderiv_eq, fderiv_fun_add hWc hZc, coordinateVector_add W Z m hy]
  simp only [ContinuousLinearMap.add_apply, CoordinateCovariantDerivative.connectionTerm_add_right, map_add]
  abel

theorem derivative_const_smul_right (B : ManifoldBilinear.Field (M := M))
    (r : ℝ) (V W : ChartVectorField.Field (M := M)) (m : M) :
    GlobalCovariantDerivative.derivative B V (fun p => r • W p) m =
      r • GlobalCovariantDerivative.derivative B V W m := by
  have hm := mem_chart_source CoordinateSpace m
  have hy := (chartAt CoordinateSpace m).mapsTo hm
  have heq : coordinateVector (fun p => r • W p) m =ᶠ[𝓝 (chartAt CoordinateSpace m m)]
      (r • coordinateVector W m) := by
    filter_upwards [(chartAt CoordinateSpace m).open_target.mem_nhds hy] with y hyt
    exact coordinateVector_fun_smul (fun _ => r) W m hyt
  unfold GlobalCovariantDerivative.derivative chartDerivative coordinateDerivative
    CoordinateCovariantDerivative.derivative
  rw [heq.fderiv_eq, fderiv_const_smul_of_field]
  rw [coordinateVector_fun_smul (fun _ => r) W m hy]
  simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply,
    CoordinateCovariantDerivative.connectionTerm_smul_right, map_smul, map_add, smul_add]

theorem derivative_smul_right (B : ManifoldBilinear.Field (M := M))
    (f : M → ℝ) (V W : ChartVectorField.Field (M := M)) (m : M)
    (hf : MDifferentiableAt Model 𝓘(ℝ, ℝ) f m) (hW : SectionDifferentiableAt W m) :
    GlobalCovariantDerivative.derivative B V (fun p => f p • W p) m =
      f m • GlobalCovariantDerivative.derivative B V W m +
        (mfderiv Model 𝓘(ℝ, ℝ) f m (V m)) • W m := by
  let e := chartAt CoordinateSpace m
  let y₀ := e m
  let Γ := computedConnection (ManifoldMetricTransition.coordinateBilinear B m)
  let Vc := coordinateVector V m
  let Wc := coordinateVector W m
  let F : CoordinateSpace → ℝ := f ∘ e.symm
  have hm : m ∈ e.source := mem_chart_source CoordinateSpace m
  have hy : y₀ ∈ e.target := e.mapsTo hm
  have hi := (mdifferentiable_chart (I := Model) m).mdifferentiableAt_symm hy
  have hfco : DifferentiableAt ℝ F y₀ :=
    (hf.comp_of_eq y₀ hi (e.left_inv hm)).differentiableAt
  have hWco : DifferentiableAt ℝ Wc y₀ := differentiableAt_coordinateVector W m m hm hW
  have heq : coordinateVector (fun p => f p • W p) m =ᶠ[𝓝 y₀] (F • Wc) := by
    filter_upwards [e.open_target.mem_nhds hy] with y hyt
    exact coordinateVector_fun_smul f W m hyt
  have hactual : CoordinateCovariantDerivative.derivative Γ Vc
      (coordinateVector (fun p => f p • W p) m) y₀ =
      CoordinateCovariantDerivative.derivative Γ Vc (F • Wc) y₀ := by
    unfold CoordinateCovariantDerivative.derivative
    rw [heq.fderiv_eq, coordinateVector_fun_smul f W m hy]
    rfl
  have hLeib := CoordinateCovariantDerivative.derivative_smul_right Γ F Vc Wc y₀ hfco hWco
  have hscalar : fderiv ℝ F y₀ (Vc y₀) = mfderiv Model 𝓘(ℝ, ℝ) f m (V m) := by
    dsimp only [F, Vc, y₀, e]
    rw [coordinateVector_at_chart V m m hm]
    exact (ChartDifferential.scalar_mfderiv_eq_chart f V m m hm hf).symm
  have hvalue : F y₀ = f m := by
    dsimp only [F, y₀, Function.comp_apply]
    rw [e.left_inv hm]
  have hreconstruct : tangentFrame m m (Wc y₀) = W m := by
    dsimp only [Wc, y₀, e]
    rw [coordinateVector_at_chart W m m hm, tangentFrame_frameVector W m m hm]
  change tangentFrame m m (CoordinateCovariantDerivative.derivative Γ Vc
      (coordinateVector (fun p => f p • W p) m) y₀) =
    f m • tangentFrame m m (CoordinateCovariantDerivative.derivative Γ Vc Wc y₀) +
      (mfderiv Model 𝓘(ℝ, ℝ) f m (V m)) • W m
  rw [hactual, hLeib, map_add, map_smul, map_smul, hvalue, hscalar, hreconstruct]

end Burnett.Geometry.GlobalConnectionLaws
