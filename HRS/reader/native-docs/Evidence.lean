import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal
#doc (Manual) "Evidence and selected direct proof calls" =>
%%%
tag := "evidence"
%%%

The statements and proofs in the reading chapters are linked to their Lean declarations. This page records the scope of the formal checks and the principal dependencies.

# What has been checked

The supplied Lean package compiles. The ten proved declarations displayed in the two reading chapters were also checked for their axioms: each uses only `propext`, `Classical.choice` and `Quot.sound`. This is a check of those ten declarations. The original statements with admitted proofs (`sorry`) are identified separately, together with the proved declarations and their type checks.

The English statements and proof explanations have a separate, scoped correspondence review. The source links below identify the formal results on which they depend.

# Assumptions that matter

## Gaussian comparison

Fix $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d/2`, a finite family $`\phi_a\in C_c^\infty(\mathbb R^{\mathsf d})`, a center $`x_0`, and $`0<b_{\min}\le b_{\max}`. The constants are uniform in $`N\ge2`, $`\beta,\ell>0`, $`b\in[b_{\min},b_{\max}]` and nonnegative observation times, provided $`\beta\ell^{\mathsf d-\mathsf s}\in[b_{\min},b_{\max}]`.

The initial positions have product Haar law and are independent of the Brownian motion. A collision-free strong solution on every finite horizon is assumed, with the specified Brownian filtration, adaptedness and progressive measurability. The conclusion is the six-term bound in smooth distance for the finite observation vector, together with nonnegativity of the corrected energy off collisions.

[Comparison statement and proof](source/HRS/Sections/ScrnFinal.lean), lines 21–108.

## Shrinking scales and the stationary window

For $`\ell=N^{-\kappa}` with $`0<\kappa<\kappa_{\max}`, the first five error terms vanish for every $`C_0\ge0`. The temperature error vanishes under the additional assumption $`\beta_N\ell_N^{\mathsf d-\mathsf s}\to b>0`. The upper bound satisfies $`\kappa_{\max}>0`, with $`\kappa_{\max}(2,0)=1/6` and $`\kappa_{\max}(3,1)=1/21`.

The stationary limit uses $`N=n+2` and nonnegative waiting times $`u_n\to\infty`. For fixed tests and nonnegative lag times, the observation vector converges in smooth distance to the centered Gaussian with the stationary covariance.

For fixed $`b,t>0`, the low-frequency multiplier has limits $`1`, $`e^{-2\mathsf{c}_{\mathsf d,\mathsf s}t}` and $`0` in the cases $`\mathsf d-\mathsf s<2`, $`\mathsf d-\mathsf s=2` and $`\mathsf d-\mathsf s>2`, respectively.

[Scale and multiplier results](source/HRS/Sections/Sec6.lean), lines 146–430.
[Stationary statement and proof](source/HRS/Sections/ScrnFinal.lean), lines 110–169.

## The torus specialization

The sharp torus estimate permits signed densities of mass one. Its application assumes $`\mathsf d\ge3`, $`0\le\mathsf s<\mathsf d-2`, a probability density $`0\le\rho\le\Lambda` with $`\Lambda\ge1`, and a collision-free configuration with $`N\ge2`. The Lipschitz and fractional-derivative bounds are nonnegative. A periodic embedding supplies the regularity required by the sharp theorem; the density-dependent correction is then bounded by the correction used in the fluctuation estimate.

[Application specialization](source/HRS/Commutator/Torus/Bridge.lean), lines 76–168.

The all-regime estimate holds for $`\mathsf d\ge1` and $`0\le\mathsf s<\mathsf d`, with the same density and configuration assumptions and the transport hypothesis `HasTransportBound`. It gives absolute integrability off the diagonal and the commutator bound. The proof divides at $`\mathsf s=\mathsf d-2`.

The proved declaration is `HRS.Commutator.commutator_estimate_of_packets`. The source checks its type against `HRS.commutator_estimate`, whose original proof is admitted.

[All-regime statement, proof and type check](source/HRS/Energy/Commutator/Assembly.lean), lines 35–96.

# Seven selected proof calls

The following seven direct calls connect the commutator and Gaussian-comparison arguments. The linked proofs give their other dependencies.

* `HRS.screening_comparison_proof` calls `HRS.Main.A8P.a8p_commSpec` to obtain the commutator constants and specification. [Source](source/HRS/Sections/ScrnFinal.lean), line 52.
* `HRS.screening_comparison_proof` calls `HRS.scrn_instance` for scales at most one. The larger-scale case is handled separately. [Source](source/HRS/Sections/ScrnFinal.lean), line 53.
* `HRS.screening_stationary_limit_proof` calls `HRS.screening_error_tendsto` for the five error terms, with the particle count shifted by two. Temperature mismatch is handled separately. [Source](source/HRS/Sections/ScrnFinal.lean), line 150.
* `HRS.screening_stationary_limit_proof` calls `HRS.scrn_stat_gauss_tendsto` to pass from the transient Gaussian to the stationary Gaussian for fixed tests and lags. [Source](source/HRS/Sections/ScrnFinal.lean), line 155.
* `HRS.Commutator.TorusNote.commutator_estimate_sub_of_torus` calls `HRS.Commutator.TorusNote.torus_subcoulomb_commutator`, specializing the sharp result to a probability density. [Source](source/HRS/Commutator/Torus/Bridge.lean), line 83.
* `HRS.Commutator.TorusNote.commutator_estimate_sub_of_torus` calls `HRS.Commutator.TorusNote.embedding_T` to supply the sharper theorem’s fractional transport bound from the application’s higher-derivative bound. [Source](source/HRS/Commutator/Torus/Bridge.lean), line 84.
* `HRS.Commutator.commutator_estimate_of_packets` calls `HRS.Commutator.TorusNote.commutator_estimate_sub_of_torus` in its sub-Coulomb branch. The remaining branch is separate. [Source](source/HRS/Energy/Commutator/Assembly.lean), line 51.
