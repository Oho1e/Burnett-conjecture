import Burnett.Geometry.ConnectionDifference
import Burnett.Geometry.InversePerturbation

/-!
# Quantitative error in the genuine connection difference

All norms are component sup norms on the existing finite function types.
The regularity hypotheses for the metric theorem concern only the chosen
point and its symmetry neighborhood. Uniform background inverse and jet
bounds are explicit consumer inputs, not consequences of admissibility
asserted in this file.
-/

noncomputable section

namespace Burnett.Geometry.ConnectionError

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.InversePerturbation
open scoped BigOperators Topology
open Filter

theorem abs_firstJet_entry_le_norm (J : FirstJet) (i j k : Index) : |J i j k| ≤ ‖J‖ := by
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (J i j) k).trans
      ((norm_le_pi_norm (J i) j).trans (norm_le_pi_norm J i))

theorem norm_connection_le_of_entries (A : Connection) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i j k, |A i j k| ≤ C) : ‖A‖ ≤ C := by
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro k
  simpa only [Real.norm_eq_abs] using h i j k

theorem abs_koszul_le (J : FirstJet) (b c d : Index) :
    |koszul J b c d| ≤ (3/2 : ℝ) * ‖J‖ := by
  have h1 := abs_le.mp (abs_firstJet_entry_le_norm J b c d)
  have h2 := abs_le.mp (abs_firstJet_entry_le_norm J c b d)
  have h3 := abs_le.mp (abs_firstJet_entry_le_norm J d b c)
  apply abs_le.mpr
  constructor <;> unfold koszul <;> linarith

/-- Four summed indices and the three half-weighted Koszul terms give 6. -/
theorem norm_christoffel_le (G : Tensor2) (J : FirstJet) :
    ‖christoffel G J‖ ≤ 6 * ‖G‖ * ‖J‖ := by
  apply norm_connection_le_of_entries _ (by positivity)
  intro a b c
  have hs := norm_sum_le Finset.univ (fun d : Index => G a d * koszul J b c d)
  simp only [Real.norm_eq_abs, abs_mul] at hs
  calc
    |christoffel G J a b c| ≤ ∑ d, |G a d| * |koszul J b c d| := hs
    _ ≤ ∑ _ : Index, ‖G‖ * ((3/2 : ℝ) * ‖J‖) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul (abs_entry_le_norm G a d) (abs_koszul_le J b c d)
        (abs_nonneg _) (norm_nonneg _)
    _ = 6 * ‖G‖ * ‖J‖ := by simp; ring

theorem christoffel_sub_inverse_slot (G₁ G₀ : Tensor2) (J : FirstJet) :
    christoffel G₁ J - christoffel G₀ J = christoffel (G₁ - G₀) J := by
  funext a b c
  simp [christoffel, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

def metricConnectionError
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate) : Connection :=
  (metricConnection g₁ x hn₁ - metricConnection g₀ x hn₀) -
    christoffel (metricInverse (g₀ x) hn₀) (perturbationCovariantJet g₀ g₁ x hn₀)

/-- The error is derived from the actual connection-difference theorem and
inverse-slot linearity, rather than introduced as a small remainder field. -/
theorem metricConnectionError_eq
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate)
    (hs₀ : ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm) (hs₁ : ∀ᶠ y in 𝓝 x, (g₁ y).IsSymm)
    (hd₀ : DifferentiableComponentsAt (metricComponents g₀) x)
    (hd₁ : DifferentiableComponentsAt (metricComponents g₁) x) :
    metricConnectionError g₀ g₁ x hn₀ hn₁ =
      christoffel (metricInverse (g₁ x) hn₁ - metricInverse (g₀ x) hn₀)
        (perturbationCovariantJet g₀ g₁ x hn₀) := by
  have hc : metricConnection g₁ x hn₁ - metricConnection g₀ x hn₀ =
      christoffel (metricInverse (g₁ x) hn₁) (perturbationCovariantJet g₀ g₁ x hn₀) := by
    funext a b c
    exact metricConnection_difference g₀ g₁ x hn₀ hn₁ hs₀ hs₁ hd₀ hd₁ a b c
  unfold metricConnectionError
  rw [hc, christoffel_sub_inverse_slot]

theorem norm_metricConnectionError_le
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate)
    (hs₀ : ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm) (hs₁ : ∀ᶠ y in 𝓝 x, (g₁ y).IsSymm)
    (hd₀ : DifferentiableComponentsAt (metricComponents g₀) x)
    (hd₁ : DifferentiableComponentsAt (metricComponents g₁) x) :
    ‖metricConnectionError g₀ g₁ x hn₀ hn₁‖ ≤
      6 * ‖metricInverse (g₁ x) hn₁ - metricInverse (g₀ x) hn₀‖ *
        ‖perturbationCovariantJet g₀ g₁ x hn₀‖ := by
  rw [metricConnectionError_eq g₀ g₁ x hn₀ hn₁ hs₀ hs₁ hd₀ hd₁]
  exact norm_christoffel_le _ _

theorem norm_metricConnectionError_le_of_small
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (hn₀ : (g₀ x).Nondegenerate) (hn₁ : (g₁ x).Nondegenerate)
    (hs₀ : ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm) (hs₁ : ∀ᶠ y in 𝓝 x, (g₁ y).IsSymm)
    (hd₀ : DifferentiableComponentsAt (metricComponents g₀) x)
    (hd₁ : DifferentiableComponentsAt (metricComponents g₁) x)
    (hsmall : 16 * ‖metricComponents g₁ x - metricComponents g₀ x‖ *
      ‖metricInverse (g₀ x) hn₀‖ ≤ 1/2) :
    ‖metricConnectionError g₀ g₁ x hn₀ hn₁‖ ≤
      192 * ‖metricInverse (g₀ x) hn₀‖^2 * ‖metricComponents g₁ x - metricComponents g₀ x‖ *
        ‖perturbationCovariantJet g₀ g₁ x hn₀‖ := by
  have hi := (fiber_inverse_estimates (g₀ x) (g₁ x) hn₀ hn₁
    hs₀.self_of_nhds hs₁.self_of_nhds coordinateBasis hsmall).2
  calc
    _ ≤ 6 * ‖metricInverse (g₁ x) hn₁ - metricInverse (g₀ x) hn₀‖ *
        ‖perturbationCovariantJet g₀ g₁ x hn₀‖ :=
      norm_metricConnectionError_le g₀ g₁ x hn₀ hn₁ hs₀ hs₁ hd₀ hd₁
    _ ≤ 6 * (32 * ‖metricInverse (g₀ x) hn₀‖^2 *
        ‖metricComponents g₁ x - metricComponents g₀ x‖) *
        ‖perturbationCovariantJet g₀ g₁ x hn₀‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (by norm_num)) (norm_nonneg _)
    _ = _ := by ring

/-- The error estimate on one specified set; no inverse/jet bound is
required outside that set. The metric difference remains pointwise in
the conclusion, so this estimate can consume its actual uniform limit. -/
theorem norm_metricConnectionError_le_on
    (K : Set CoordinateSpace)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs₁ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₁ y).IsSymm)
    (hd₀ : ∀ x ∈ K, DifferentiableComponentsAt (metricComponents g₀) x)
    (hd₁ : ∀ x ∈ K, DifferentiableComponentsAt (metricComponents g₁) x)
    {B H : ℝ}
    (hbase : ∀ x (hx : x ∈ K), ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ B)
    (hjet : ∀ x (hx : x ∈ K), ‖perturbationCovariantJet g₀ g₁ x (hn₀ x hx)‖ ≤ H)
    (hsmall : ∀ x (hx : x ∈ K), 16 * ‖metricComponents g₁ x - metricComponents g₀ x‖ *
      ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ 1/2) :
    ∀ x (hx : x ∈ K), ‖metricConnectionError g₀ g₁ x (hn₀ x hx) (hn₁ x hx)‖ ≤
      (192 * B^2 * H) * ‖metricComponents g₁ x - metricComponents g₀ x‖ := by
  intro x hx
  have hb := norm_metricConnectionError_le_of_small g₀ g₁ x (hn₀ x hx) (hn₁ x hx)
    (hs₀ x hx) (hs₁ x hx) (hd₀ x hx) (hd₁ x hx) (hsmall x hx)
  calc
    _ ≤ 192 * ‖metricInverse (g₀ x) (hn₀ x hx)‖^2 *
        ‖metricComponents g₁ x - metricComponents g₀ x‖ *
        ‖perturbationCovariantJet g₀ g₁ x (hn₀ x hx)‖ := hb
    _ ≤ 192 * B^2 * ‖metricComponents g₁ x - metricComponents g₀ x‖ * H := by
      gcongr
      · exact hbase x hx
      · exact hjet x hx
    _ = _ := by ring

/-- A local error represented by a total function only for the purpose of
`TendstoUniformlyOn`. The zero values outside K carry no geometric claim. -/
def metricConnectionErrorOn (K : Set CoordinateSpace)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate) :
    CoordinateSpace → Connection := by
  classical
  exact fun x => if hx : x ∈ K then
    metricConnectionError g₀ g₁ x (hn₀ x hx) (hn₁ x hx) else 0

@[simp] theorem metricConnectionErrorOn_of_mem (K : Set CoordinateSpace)
    (g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate) (hn₁ : ∀ x ∈ K, (g₁ x).Nondegenerate)
    {x : CoordinateSpace} (hx : x ∈ K) :
    metricConnectionErrorOn K g₀ g₁ hn₀ hn₁ x =
      metricConnectionError g₀ g₁ x (hn₀ x hx) (hn₁ x hx) := by
  classical
  exact dif_pos hx

theorem tendstoUniformlyOn_zero_of_eventually_norm_le_dist
    {X A Z : Type*} [NormedAddCommGroup A] [PseudoMetricSpace Z]
    {K : Set X} {F : ℕ → X → A} {G : ℕ → X → Z} {g : X → Z}
    (hG : TendstoUniformlyOn G g atTop K) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, ∀ x ∈ K, ‖F n x‖ ≤ C * dist (G n x) (g x)) :
    TendstoUniformlyOn F (fun _ => 0) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (C + 1)
  have hden : 0 < C + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδmul : δ * (C + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hsmall : C * δ < ε := by nlinarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hG δ hδ, hbound] with n hn hb
  intro x hx
  have hd : dist (G n x) (g x) < δ := by simpa only [dist_comm] using hn x hx
  have he : ‖F n x‖ < ε :=
    (hb x hx).trans_lt ((mul_le_mul_of_nonneg_left hd.le hC).trans_lt hsmall)
  simpa only [dist_zero_left] using he

/-- Actual uniform convergence of the constructed connection error on K.
Eventual smallness is a consumer input from the separate inverse-sequence
bridge; the derivative-array bound is also explicit. No convergence of E
is an assumption, and no regularity outside the stated local hypotheses is
required. -/
theorem metricConnectionError_tendstoUniformlyOn
    (K : Set CoordinateSpace)
    (g₀ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (g : ℕ → CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (hn₀ : ∀ x ∈ K, (g₀ x).Nondegenerate)
    (hn : ∀ n x, x ∈ K → (g n x).Nondegenerate)
    (hs₀ : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, (g₀ y).IsSymm)
    (hs : ∀ n x, x ∈ K → ∀ᶠ y in 𝓝 x, (g n y).IsSymm)
    (hd₀ : ∀ x ∈ K, DifferentiableComponentsAt (metricComponents g₀) x)
    (hd : ∀ n x, x ∈ K → DifferentiableComponentsAt (metricComponents (g n)) x)
    {B H : ℝ} (hH : 0 ≤ H)
    (hbase : ∀ x (hx : x ∈ K), ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ B)
    (hjet : ∀ᶠ n in atTop, ∀ x (hx : x ∈ K),
      ‖perturbationCovariantJet g₀ (g n) x (hn₀ x hx)‖ ≤ H)
    (hsmall : ∀ᶠ n in atTop, ∀ x (hx : x ∈ K),
      16 * ‖metricComponents (g n) x - metricComponents g₀ x‖ *
        ‖metricInverse (g₀ x) (hn₀ x hx)‖ ≤ 1/2)
    (hconv : TendstoUniformlyOn (fun n => metricComponents (g n)) (metricComponents g₀) atTop K) :
    TendstoUniformlyOn (fun n => metricConnectionErrorOn K g₀ (g n) hn₀ (hn n))
      (fun _ => 0) atTop K := by
  apply tendstoUniformlyOn_zero_of_eventually_norm_le_dist hconv
    (C := 192 * B^2 * H) (by positivity)
  filter_upwards [hjet, hsmall] with n hJn hsn
  intro x hx
  rw [metricConnectionErrorOn_of_mem _ _ _ _ _ hx, dist_eq_norm]
  exact norm_metricConnectionError_le_on K g₀ (g n) hn₀ (hn n) hs₀ (hs n) hd₀ (hd n)
    hbase hJn hsn x hx

end Burnett.Geometry.ConnectionError
