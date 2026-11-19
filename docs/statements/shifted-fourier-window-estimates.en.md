# Shifted Fourier window estimates in four dimensions

[简体中文](shifted-fourier-window-estimates.zh-CN.md)

Lines 626–685 use the bilinear Coifman–Meyer estimate. The formalization estimates a product of two annular factors and a low-frequency factor. The following declarations give the convolution formula and bound for the low-frequency factor on four-dimensional Schwartz inputs.

- `shifted_window_physical` identifies the Fourier multiplier with symbol $e^{2πi\langle sξ,q\rangle}a(sξ)$, for $s>0$, with convolution by $s^{-4}(\mathcal F^{-1} a)((x-y)/s+q)$.
- `maximalShiftedWindow_Lp` bounds the $L^p$ seminorm of the pointwise supremum of the absolute multipliers over all real $s>0$. For each real $p>1$ and each shift $q$, its bound is the input seminorm times the window constant, $(1+\lVert q\rVert)^5$, and the strong centered maximal bound. The supremum is measurable by `maximalShiftedWindow_measurable`.

The finite-exponent annular square estimates and joint multiplier argument supply the other factors needed for the commutator. Author confirmation of the correspondence remains pending. [Source bindings](shifted-fourier-window-estimates-source-bindings.json)
