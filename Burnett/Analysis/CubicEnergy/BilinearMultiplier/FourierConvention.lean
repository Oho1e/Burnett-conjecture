import Burnett.Analysis.CubicEnergy.FourierPairing

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open scoped FourierTransform

/-- Whole-space action through the inverse Fourier transform. -/
def orderOneAction (b : E → ℝ) (v : SchwartzMap E ℂ) : E → ℂ :=
  𝓕⁻ (fun ξ => (b ξ : ℂ) * 𝓕 (v : E → ℂ) ξ)

/-- Joint Fourier weight for the bilinear physical pairing. -/
def bilinearFourierWeight (a : Joint → ℝ) (f v w : SchwartzMap E ℂ) (p : Joint) : ℂ :=
  (a p : ℂ)*𝓕 (f : E → ℂ) p.1*𝓕 (v : E → ℂ) p.2*𝓕 (w : E → ℂ) (-(p.1+p.2))

end Burnett.A02.FrequencySplit
