import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowPairing
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointSchwartzSlots

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ContDiff FourierTransform

def highOffset (i : ℕ) : ℝ := 2^i/4

def windowBlock (A : Joint → ℂ) (s : ℝ) (f g h a b c : SchwartzMap E ℂ) (u v w : ℝ) : ℂ :=
  testedBlock A s (windowTest a f (u*s)) (windowTest b g (v*s)) (windowTest c h (w*s))

private def densityAt (A : Joint → ℂ) (s : ℝ) (f g h a b c : SchwartzMap E ℂ)
    (u v w : ℝ) (p : Joint) : ℂ :=
  triDensity A s (windowTest a f (u*s)) (windowTest b g (v*s)) (windowTest c h (w*s)) p

private theorem expand_three (I : Finset ℕ) (u v w : ℕ → ℂ) (x y z D : ℂ) :
    D*((∑ i ∈ I,u i)*(∑ j ∈ I,v j)*z + x*(∑ i ∈ I,v i)*(∑ j ∈ I,w j) +
       (∑ i ∈ I,u i)*y*(∑ j ∈ I,w j)) =
    ∑ i ∈ I, ∑ j ∈ I, (D*(u i*v j*z) + D*(x*v i*w j) + D*(u i*y*w j)) := by
  have scalar (P Q : ℕ → ℂ) (c : ℂ) :
      (∑ i ∈ I,P i)*(∑ j ∈ I,Q j)*c = ∑ i ∈ I,∑ j ∈ I,P i*Q j*c := by
    rw [sum_mul_sum]; simp only [sum_mul]
  calc
    _ = ((∑ i ∈ I,u i)*(∑ j ∈ I,v j)*(D*z)) +
        ((∑ i ∈ I,v i)*(∑ j ∈ I,w j)*(D*x)) + ((∑ i ∈ I,u i)*(∑ j ∈ I,w j)*(D*y)) := by ring
    _ = _ := by
      simp only [scalar,sum_add_distrib]
      apply congrArg₂ (·+·)
      · apply congrArg₂ (·+·) <;>
          apply sum_congr rfl <;> intro i _ <;> apply sum_congr rfl <;> intro j _ <;> ring
      · apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring

/-- One fixed pair of windows works at every scale, for every joint symbol
and every triple of actual Schwartz inputs. -/
theorem testedBlock_slot_expansion :
    ∃ a d : SchwartzMap E ℂ, HasCompactSupport (a : E → ℂ) ∧
      (∀ z, a z ≠ 0 → 1/2 < ‖z‖ ∧ ‖z‖ < 2) ∧
      ∀ (m : Joint → ℝ), ContDiffOn ℝ ∞ m {p | p ≠ 0} → ∀ (s : ℝ) (f g h : SchwartzMap E ℂ),
      testedBlock (symbolBlock m) s f g h = ∑ i ∈ range 7,∑ j ∈ range 7,
        (windowBlock (symbolBlock m) s f g h a a d (highOffset i) (highOffset j) (1/4) +
         windowBlock (symbolBlock m) s f g h d a a 32 (highOffset i) (highOffset j) +
         windowBlock (symbolBlock m) s f g h a d a (highOffset i) 32 (highOffset j)) := by
  obtain ⟨a,d,ac,cut,_ae,_de,slots⟩ := symbolBlock_schwartz_slots
  refine ⟨a,d,ac,cut,?_⟩
  intro m hm s f g h
  obtain ⟨hc,hs⟩ := symbolBlock_regular m hm
  let A := symbolBlock m
  let R := densityAt A s f g h
  have hi (u v w : SchwartzMap E ℂ) (r t l : ℝ) : Integrable (R u v w r t l) :=
    integrable_triDensity A hc hs s _ _ _
  let term := fun i j p => R a a d (highOffset i) (highOffset j) (1/4) p +
      R d a a 32 (highOffset i) (highOffset j) p + R a d a (highOffset i) 32 (highOffset j) p
  have it (i j : ℕ) : Integrable (term i j) := ((hi ..).add (hi ..)).add (hi ..)
  have pt (p : Joint) : triDensity A s f g h p = ∑ i ∈ range 7,∑ j ∈ range 7,term i j p := by
    let u := fun i (z : E) => a ((highOffset i*s) • z)
    let W := fun z : E => d (((1/4:ℝ)*s) • z)
    let L := fun z : E => d ((32*s) • z)
    let Z := -(p.1+p.2)
    have part := slots m s p.1 p.2
    dsimp only at part
    have ar (k : ℕ) : (2:ℝ)^k*(s/4) = highOffset k*s := by unfold highOffset; ring
    simp only [ar] at part
    simp only [show s/4=(1/4:ℝ)*s by ring] at part
    let D := triDensity A s f g h p
    let mult := (∑ i ∈ range 7,u i p.1)*(∑ j ∈ range 7,u j p.2)*W Z +
      L p.1*(∑ i ∈ range 7,u i p.2)*(∑ j ∈ range 7,u j Z) +
      (∑ i ∈ range 7,u i p.1)*L p.2*(∑ j ∈ range 7,u j Z)
    have split : A (s • p) = A (s • p)*mult := part
    have act : D = D*mult := by
      unfold D triDensity
      conv_lhs => rw [split]
      ring
    exact act.trans (by
      simpa only [term,R,densityAt,windowed_density] using
        expand_three (range 7) (fun i => u i p.1) (fun j => u j p.2) (fun j => u j Z)
          (L p.1) (L p.2) (W Z) D)
  rw [testedBlock_density (symbolBlock m) hc hs]
  change (∫ p, triDensity A s f g h p) = _
  simp_rw [pt]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => it i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _ => it i j)]
  apply sum_congr rfl
  intro j _
  unfold term
  have h1 := hi a a d (highOffset i) (highOffset j) (1/4)
  have h2 := hi d a a 32 (highOffset i) (highOffset j)
  have h3 := hi a d a (highOffset i) 32 (highOffset j)
  have h12 : Integrable (fun p => R a a d (highOffset i) (highOffset j) (1/4) p +
      R d a a 32 (highOffset i) (highOffset j) p) := h1.add h2
  rw [integral_add h12 h3,integral_add h1 h2]
  simp only [windowBlock,testedBlock_density _ hc hs]
  rfl

end Burnett.A02.FrequencySplit
