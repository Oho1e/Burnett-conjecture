# Failure of a background L² source estimate

[中文](harmonic-shear.zh-CN.md) · [Statement T13](main.en.md#t13)

The main declaration `Burnett.HarmonicShear.Bounds.harmonic_coordinate_source_counterexample` proves Proposition A.1 (`prop:shear`, lines 3121–3123, proof at 3124–3169). Lean's zero-based index `n` represents the paper's positive index $n+1$.

The two inverse shear maps are global smooth diffeomorphisms. Their actual pulled-back Minkowski metrics have Minkowski signature, full intrinsic Riemann curvature zero and vacuum Ricci tensor. The same fields satisfy the exact contracted Christoffel equations $H(g_n)=H(m)=0$, physical local uniform convergence to Minkowski and a uniform local $L^\infty$ bound for the actual auxiliary covariant derivative. The auxiliary metric is Euclidean.

One fixed compact parallelepiped comes from the determinant-one coordinates $(t,x^2,p,q)$. The square integral of the actual $(\Box_m h_n)_{21}$ component is $4\pi^2(n+1)^4$. The full source has finite Euclidean tensor $L^2$ norm for every index, and these norms tend to infinity on the same compact set with respect to the Minkowski geometric volume.

The integrated proof snapshot passed 38 actual type and transitive-axiom checks under trust policy A. Its receipt SHA256 is `bfb6aff7101fd8e719d2f804f23e44a82a57a88c76594ac91457ffa6fa7cb518`. The independent capstone review checked the manuscript correspondence and reproduced the native log byte for byte. Its replay receipt SHA256 is `4f6e792cf1b49b3819fb952c3864bb34d51dc4f1b8d8a3719e0c6e825fbea416`. The candidate uses the intrinsic curvature bridge from X07. The independent review testimony receipt SHA256 is `9baf8197f2e932835368a9b5ea515a4b14dbda2613b6b22209ccf7d4047463d6`. The ordinary module and project checks verify the registered repository sources separately. Author confirmation is pending.
