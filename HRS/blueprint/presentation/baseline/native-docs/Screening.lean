import HRS.Sections.ScrnFinal
import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Mesoscopic observations and screening" =>

%%%
tag := "screening"
%%%

[Home](reader-anchor:home) / [Section index](reader-anchor:broad) / Main §6

We compare finitely many mesoscopic observations of the periodic Riesz diffusion with Gaussian vectors, uniformly in the observation times. The error determines admissible shrinking scales and yields a stationary limit after a diverging rescaled waiting time.

Throughout, the particle system is assumed to satisfy the strong-solution and filtration hypotheses below.

Proposition 6.1 is developed through the comparison estimate, the admissible scale range and the stationary limit. The low-frequency behavior gives the accompanying remark.

[Objects](reader-anchor:d1) · [Comparison](reader-anchor:d2) · [Scales](reader-anchor:d3) · [Stationary window](reader-anchor:d4) · [Low frequency](reader-anchor:d5) · [Paper-to-Lean map](reader-anchor:inventory)

# Objects and hypotheses
%%%
tag := "d1"
%%%

Fix an integer $`\mathsf{d}\ge 2`, $`0\le \mathsf{s}<\mathsf{d}/2`, and $`q=\mathsf{d}-\mathsf{s}`. Fix a finite number $`p` of real, smooth, compactly supported tests $`\phi_a` on Euclidean $`\mathsf{d}`-space, and a center $`x_0`. For $`\ell>0` the periodized test is

$$`\phi_\ell(x)=\ell^{-\mathsf{d}/2}\sum_{z\in\mathbb Z^{\mathsf{d}}}\phi\!\left(\ell^{-1}(\operatorname{rep}(x)-x_0+z)\right).`

[(6.1)](reader-anchor:eq-6-1)

The observation is $`Z_{N,\ell}^t(\phi)=\sqrt N(\mu_N^t-\mathrm dx)(\phi_\ell)`, with normalized Haar measure $`\mathrm dx`. Observations are taken at physical times $`\ell^{2-q}t_a`, $`t_a\ge0`.

Let $`N\ge2` and $`\beta>0`. Assume a collision-free strong solution of the periodic Riesz particle system with zero external potential on every finite time interval, started from product Haar law. The driving Brownian motions are jointly independent of the initial positions. Require a Brownian filtration relative to which the solution is adapted and progressively measurable. The local stochastic hypotheses below specify the lift, time-integrable drift, initial condition, measurable time slices and almost-sure continuity.

For $`r=2\pi\lVert\xi\rVert` and $`b>0` the defining multipliers are

$$`a_b(\xi)=b^{-1}r^2+\mathsf{c}_{\mathsf{d},\mathsf{s}}r^{2-q},\qquad  S_b(\xi)=\frac{r^q}{r^q+b\,\mathsf{c}_{\mathsf{d},\mathsf{s}}}.`

[(6.2)](reader-anchor:eq-6-2)

For $`t\ge u\ge 0` the covariance entry is the real part of

$$`\int \widehat\phi(\xi)\,\overline{\widehat\psi(\xi)}\,e^{-(t-u)a_b(\xi)}  \cdot\bigl[S_b(\xi)+(1-S_b(\xi))e^{-2u a_b(\xi)}\bigr]\,\mathrm{d}\xi .`

[(6.3)](reader-anchor:eq-6-3)

The matrix $`\Sigma_b(t,\phi)` is obtained by placing the later time first in (6.3). Its stationary counterpart $`\Sigma_b^{\mathrm{stat}}(t,\phi)` omits the transient term.

# Uniform Gaussian comparison
%%%
tag := "d2"
%%%

Fix $`0<b_{\min}\le b_{\max}`. There exist $`C_0,C\ge 0`, chosen *before* $`N`, $`\beta`, $`\ell`, $`b`, the stochastic system and observation times, such that the following holds whenever $`\beta\ell^q` and $`b` lie in $`[b_{\min},b_{\max}]`. Write

$$`o_N=C_0 N^{-q/\mathsf{d}}+\mathbf{1}_{\{\mathsf{s}=0\}}\frac{\log N}{2\mathsf{d}N}.`

[(6.4)](reader-anchor:eq-6-4)

The same $`C_0` gives nonnegativity of the corrected Riesz energy for every off-collision $`N`-particle configuration. The smooth distance of order 3 between the observation law and the centered Gaussian with `mesoCovMatrix` is at most $`C` times

$$`N^{-1/2}\,\ell^{-\mathsf{d}/2}+\sqrt N\,o_N\,\ell^{-\mathsf{d}/2-\max(q,2)}+N^{-1/\mathsf{d}}\,\ell^{-\mathsf{d}-3+\min(q,2)}+\sqrt{o_N}\,\ell^{-(\mathsf{d}+q)/2-2+\min(q,2)}+\ell+|\beta\ell^q-b|.`

[(6.5)](reader-anchor:eq-6-5)

Here smooth distance means the supremum of expectation differences over $`C^3` functions whose *sum* of the supremum norms of derivatives of orders 0 through 3 is at most one; boundedness of those derivatives is explicit.

*Lean proof.* [`HRS.screening_comparison_proof`](reader-anchor:decl-HRS.screening_comparison_proof) proves the comparison. The source checks that its type matches `HRS.screening_comparison`, the earlier declaration in `Sec6.lean` whose proof is admitted with `sorry`. Archived verification records cover the `_proof` theorem and this type check in nanoda and Lean’s default kernel.

*Proof.* For $`\ell\le1`, combine the commutator estimate with the small-scale probabilistic and Gaussian comparisons. The same commutator constants give nonnegativity of the corrected energy. Enlarge the comparison constant to at least $`2`. For $`\ell>1`, use $`d_3\le2` and the $`\ell` term in the error. The small-scale argument transports the test functions and combines the two comparison errors.

[Read the commutator theorem behind this step →](reader-anchor:commutator)

# Admissible shrinking scales
%%%
tag := "d3"
%%%

Define

$$`\kappa_{\max}=\min\Biggl\{\frac{1}{\mathsf{d}},\;\frac{q/\mathsf{d}-1/2}{\mathsf{d}/2+\max(q,2)},\;\frac{1}{\mathsf{d}(\mathsf{d}+3-\min(q,2))},\;\frac{q}{2\mathsf{d}\big((\mathsf{d}+q)/2+2-\min(q,2)\big)}\Biggr\}.`

[(6.6)](reader-anchor:eq-6-6)

The exponent $`\kappa_{\max}` is positive, with $`\kappa_{\max}(2,0)=1/6` and $`\kappa_{\max}(3,1)=1/21`. For every $`C_0\ge0` and $`0<\kappa<\kappa_{\max}`, the first five terms of (6.5) tend to zero at $`\ell=N^{-\kappa}`. The temperature condition $`\beta_N\ell_N^q\to b` controls the last term.

The proof turns the strict $`\kappa` inequalities into negative powers of $`N`. When $`\mathsf{s}=0`, the logarithmic factor is dominated by the negative power of the particle number. The first restriction in (6.6) gives growth of $`N\ell^{\mathsf{d}}`; the others control the error terms.

# Stationary limit
%%%
tag := "d4"
%%%

Fix $`0<\kappa<\kappa_{\max}`. Take $`N=n+2`, $`\ell_n=(n+2)^{-\kappa}`, positive $`\beta_n` with $`\beta_n\ell_n^q\to b>0`, and a sequence of supplied stochastic systems satisfying the hypotheses above. For any nonnegative $`u_n\to\infty` and fixed nonnegative lags $`t_a`, the smooth distance of order 3 between observations at physical times $`\ell_n^{2-q}(u_n+t_a)` and the centered Gaussian with `mesoStatCovMatrix d s b t φ` tends to zero.

For all sufficiently large particle counts, the scaled temperature lies in $`[b/2,2b]`. Apply the comparison estimate and the vanishing-error result. The covariance entries of the comparison Gaussian converge to the stationary entries; the Gaussian comparison bound therefore gives convergence in smooth distance. The triangle inequality completes the proof for the fixed tests and lag times.

The proved declaration is `HRS.screening_stationary_limit_proof`. Its type is checked against the original `HRS.screening_stationary_limit`, whose proof is admitted with `sorry`.

# Low-frequency behavior

For fixed $`b,t>0`, as $`\xi` approaches zero through nonzero frequencies,

$$`S_b(\xi)+(1-S_b(\xi))e^{-2t a_b(\xi)}\longrightarrow\begin{cases}1 & q<2,\\ e^{-2\mathsf{c}_{\mathsf{d},\mathsf{s}}t}& q=2,\\ 0 & q>2 .\end{cases}`

[(6.7)](reader-anchor:eq-6-7)

In all three regimes $`S_b(\xi)\to 0`. Thus the stationary multiplier vanishes at low frequency, but the finite-time multiplier need not. This calculation concerns the Gaussian multiplier in the $`N`-particle comparison. The proof uses the positive radial variable $`r\to 0`: $`a_b` tends to 0, $`\mathsf{c}_{\mathsf{d},\mathsf{s}}`, or $`+\infty` according to the three regimes, then combines exponential and spectral limits.

[Compare with the broad index →](reader-anchor:broad) · [Back to overview](reader-anchor:home)

# Definitions and theorems

## Normalization and conventions
%%%
tag := "screening-notation"
number := false
%%%

Write $`\mathsf{c}_{\mathsf{d},\mathsf{s}}` for the Riesz normalization

$$`\mathsf{c}_{\mathsf{d},\mathsf{s}}=\begin{cases}2^{\mathsf{d}-1}\pi^{\mathsf{d}/2}\Gamma(\mathsf{d}/2),&\mathsf{s}=0,\\ 2^{\mathsf{d}-\mathsf{s}}\pi^{\mathsf{d}/2}\Gamma((\mathsf{d}-\mathsf{s})/2)/\Gamma(\mathsf{s}/2),&\mathsf{s}\ne0.\end{cases}`

For the definitions, $`\mathsf{d}\in\mathbb N` and the displayed real parameters are unrestricted. Scalar operations have their total real meanings: zero inverse is zero, and real powers use the total real-power convention. A sum or Bochner integral is assigned zero when it is nonsummable or nonintegrable, respectively.

## `HRS.mesoRate`
%%%
tag := "decl-HRS.mesoRate"
%%%

:::definition "screening-provider-1" (lean := "HRS.mesoRate")
Let $`\mathsf{d}\in\mathbb N`, $`\mathsf{s},b\in\mathbb R`, and $`q=\mathsf{d}-\mathsf{s}`. For $`\xi\in\mathbb R^{\mathsf{d}}`, set $`r=2\pi|\xi|`.

$$`a_b(\xi)=b^{-1}r^2+\mathsf{c}_{\mathsf{d},\mathsf{s}}r^{2-q}.`

Here $`\mathsf{c}_{\mathsf{d},\mathsf{s}}` is the [Riesz normalization](reader-anchor:screening-notation).
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.mesoRate`

`Sec6.lean`, lines 46–47.

```
def mesoRate (d : ℕ) (s b : ℝ) (ξ : Euc d) : ℝ :=
  b⁻¹ * (2 * Real.pi * ‖ξ‖) ^ 2 + rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (2 - ((d : ℝ) - s))
```

## `HRS.mesoSpectral`
%%%
tag := "decl-HRS.mesoSpectral"
%%%

:::definition "screening-provider-2" (lean := "HRS.mesoSpectral")
Let $`\mathsf{d}\in\mathbb N`, $`\mathsf{s},b\in\mathbb R`, and $`q=\mathsf{d}-\mathsf{s}`. For $`\xi\in\mathbb R^{\mathsf{d}}`, set $`r=2\pi|\xi|`.

$$`S_b(\xi)=\frac{r^q}{r^q+b\mathsf{c}_{\mathsf{d},\mathsf{s}}}.`

Here $`\mathsf{c}_{\mathsf{d},\mathsf{s}}` is the [Riesz normalization](reader-anchor:screening-notation).
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.mesoSpectral`

`Sec6.lean`, lines 50–52.

```
def mesoSpectral (d : ℕ) (s b : ℝ) (ξ : Euc d) : ℝ :=
  (2 * Real.pi * ‖ξ‖) ^ ((d : ℝ) - s) /
    ((2 * Real.pi * ‖ξ‖) ^ ((d : ℝ) - s) + b * rieszConst d s)
```

## `HRS.mesoCovIntegral`
%%%
tag := "decl-HRS.mesoCovIntegral"
%%%

:::definition "screening-provider-3" (lean := "HRS.mesoCovIntegral")
Let $`\mathsf{d}\in\mathbb N`, $`\mathsf{s},b\in\mathbb R`. For $`t,u\in\mathbb R` and $`\phi,\psi:\mathbb R^{\mathsf{d}}\to\mathbb R`, define

$$`I_b(t,u;\phi,\psi)=\operatorname{Re}\int_{\mathbb R^{\mathsf{d}}}\widehat\phi(\xi)\overline{\widehat\psi(\xi)}e^{-(t-u)a_b(\xi)}\bigl[S_b(\xi)+(1-S_b(\xi))e^{-2u a_b(\xi)}\bigr]\,\mathrm d\xi.`

We use $`\widehat\phi(\xi)=\int_{\mathbb R^{\mathsf{d}}}\phi(x)e^{-2\pi i x\cdot\xi}\,\mathrm dx`. The multipliers are [$`a_b`](reader-anchor:decl-HRS.mesoRate) and [$`S_b`](reader-anchor:decl-HRS.mesoSpectral).
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.mesoCovIntegral`

`Sec6.lean`, lines 56–60.

```
def mesoCovIntegral (d : ℕ) (s b t u : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  (∫ ξ : Euc d, 𝓕 (fun x => (φ x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (ψ x : ℂ)) ξ) *
    (((Real.exp (-(t - u) * mesoRate d s b ξ) *
      (mesoSpectral d s b ξ + (1 - mesoSpectral d s b ξ) *
        Real.exp (-2 * u * mesoRate d s b ξ)) : ℝ) : ℂ))).re
```

## `HRS.mesoCovMatrix`
%%%
tag := "decl-HRS.mesoCovMatrix"
%%%

:::definition "screening-provider-4" (lean := "HRS.mesoCovMatrix")
Let $`\mathsf{d}\in\mathbb N`, $`\mathsf{s},b\in\mathbb R`. Let $`p\in\mathbb N`, $`t\in\mathbb R^p`, and $`\phi_a:\mathbb R^{\mathsf{d}}\to\mathbb R` for $`1\le a\le p`. Define

$$`\Sigma_b(t,\phi)_{ac}=\begin{cases}I_b(t_a,t_c;\phi_a,\phi_c),&t_c\le t_a,\\I_b(t_c,t_a;\phi_c,\phi_a),&t_a<t_c.\end{cases}`

Here [$`I_b`](reader-anchor:decl-HRS.mesoCovIntegral) is the two-time covariance integral.
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.mesoCovMatrix`

`Sec6.lean`, lines 64–68.

```
def mesoCovMatrix (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a c =>
    if t c ≤ t a then mesoCovIntegral d s b (t a) (t c) (φ a) (φ c)
    else mesoCovIntegral d s b (t c) (t a) (φ c) (φ a)
```

## `HRS.mesoStatCovMatrix`
%%%
tag := "decl-HRS.mesoStatCovMatrix"
%%%

:::definition "screening-provider-5" (lean := "HRS.mesoStatCovMatrix")
Let $`\mathsf{d}\in\mathbb N`, $`\mathsf{s},b\in\mathbb R`. Let $`p\in\mathbb N`, $`t\in\mathbb R^p`, and $`\phi_a:\mathbb R^{\mathsf{d}}\to\mathbb R` for $`1\le a\le p`. Set

$$`\Sigma_b^{\mathrm{stat}}(t,\phi)_{ac}=\begin{cases}J_b(t_a-t_c;\phi_a,\phi_c),&t_c\le t_a,\\J_b(t_c-t_a;\phi_c,\phi_a),&t_a<t_c.\end{cases}`

We use $`\widehat\phi(\xi)=\int_{\mathbb R^{\mathsf{d}}}\phi(x)e^{-2\pi i x\cdot\xi}\,\mathrm dx`. With [$`a_b`](reader-anchor:decl-HRS.mesoRate) and [$`S_b`](reader-anchor:decl-HRS.mesoSpectral),

$$`J_b(v;\phi,\psi)=\operatorname{Re}\int_{\mathbb R^{\mathsf{d}}}\widehat\phi(\xi)\overline{\widehat\psi(\xi)}e^{-v a_b(\xi)}S_b(\xi)\,\mathrm d\xi.`
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.mesoStatCovMatrix`

`Sec6.lean`, lines 73–81.

```
def mesoStatCovMatrix (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun a c =>
    if t c ≤ t a then
      (∫ ξ : Euc d, 𝓕 (fun x => (φ a x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (φ c x : ℂ)) ξ) *
        (((Real.exp (-(t a - t c) * mesoRate d s b ξ) * mesoSpectral d s b ξ : ℝ) : ℂ))).re
    else
      (∫ ξ : Euc d, 𝓕 (fun x => (φ c x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (φ a x : ℂ)) ξ) *
        (((Real.exp (-(t c - t a) * mesoRate d s b ξ) * mesoSpectral d s b ξ : ℝ) : ℂ))).re
```

## `HRS.mesoTest`
%%%
tag := "decl-HRS.mesoTest"
%%%

:::definition "screening-provider-6" (lean := "HRS.mesoTest")
Let $`\mathsf{d}\in\mathbb N`, $`\ell\in\mathbb R`, $`x_0\in\mathbb R^{\mathsf{d}}`, and $`\phi:\mathbb R^{\mathsf{d}}\to\mathbb R`. For $`x\in\mathbb T^{\mathsf{d}}`, define

$$`\phi_\ell(x)=\ell^{-\mathsf{d}/2}\sum_{z\in\mathbb Z^{\mathsf{d}}}\phi\!\left(\frac{\operatorname{rep}(x)-x_0+z}{\ell}\right).`

Here $`\mathbb T^{\mathsf{d}}=\mathbb R^{\mathsf{d}}/\mathbb Z^{\mathsf{d}}`, and $`\operatorname{rep}(x)` is the fixed representative of $`x`.
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.mesoTest`

`Sec6.lean`, lines 85–87.

```
def mesoTest (d : ℕ) (ℓ : ℝ) (x₀ : Euc d) (φ : Euc d → ℝ) : Torus d → ℝ :=
  fun x => ℓ ^ (-(d : ℝ) / 2) *
    ∑' z : Lattice d, φ (ℓ⁻¹ • (Torus.rep x - x₀ + Lattice.toEuc z))
```

## `HRS.kappaMax`
%%%
tag := "decl-HRS.kappaMax"
%%%

:::definition "screening-provider-7" (lean := "HRS.kappaMax")
For $`\mathsf{d}\in\mathbb N` and $`\mathsf{s}\in\mathbb R`, set $`q=\mathsf{d}-\mathsf{s}` and define

$$`\kappa_{\max}(\mathsf{d},\mathsf{s})=\min\left\{\frac1{\mathsf{d}},\frac{q/\mathsf{d}-1/2}{\mathsf{d}/2+\max(q,2)},\frac1{\mathsf{d}(\mathsf{d}+3-\min(q,2))},\frac{q}{2\mathsf{d}((\mathsf{d}+q)/2+2-\min(q,2))}\right\}.`
:::

*Verification:* Definition; displayed source is the defining expression.

`HRS.kappaMax`

`Sec6.lean`, lines 91–95.

```
def kappaMax (d : ℕ) (s : ℝ) : ℝ :=
  min (min (1 / (d : ℝ))
      ((((d : ℝ) - s) / d - 1 / 2) / ((d : ℝ) / 2 + max ((d : ℝ) - s) 2)))
    (min (1 / ((d : ℝ) * ((d : ℝ) + 3 - min ((d : ℝ) - s) 2)))
      (((d : ℝ) - s) / (2 * d * (((d : ℝ) + ((d : ℝ) - s)) / 2 + 2 - min ((d : ℝ) - s) 2))))
```

## `HRS.screening_comparison_proof`
%%%
tag := "decl-HRS.screening_comparison_proof"
%%%

:::theorem "screening-provider-8" (lean := "HRS.screening_comparison_proof")
Let $`\mathsf{d}\ge2`, $`0\le\mathsf{s}<\mathsf{d}/2`, and $`q=\mathsf{d}-\mathsf{s}`. Fix $`p\in\mathbb N`, real tests $`\phi_1,\ldots,\phi_p\in C_c^\infty(\mathbb R^{\mathsf{d}})`, $`x_0\in\mathbb R^{\mathsf{d}}`, and $`0<b_-\le b_+`. There exist $`C_0,C\ge0`, depending only on these fixed data, such that for every $`N\ge2` and every collision-free configuration $`X_N`,

$$`\mathsf{F}_N^{\mathsf{g}}(X_N,\mathrm dx)+o_N(C_0)\ge0.`

For every $`N\ge2`, $`\beta,\ell>0` and $`b\in[b_-,b_+]` with $`\beta\ell^q\in[b_-,b_+]`, every particle system satisfying the stochastic hypotheses below, and every $`t_1,\ldots,t_p\ge0`,

$$`d_3\!\left(\operatorname{Law}\bigl((Z_{N,\ell}^{\ell^{2-q}t_a}(\phi_a))_{a=1}^p\bigr),\mathcal N(0,\Sigma_b(t,\phi))\right)\le C\left[E_N(C_0,\ell)+|\beta\ell^q-b|\right].`

With normalized Haar measure $`\mathrm dx` and [$`\phi_\ell`](reader-anchor:decl-HRS.mesoTest), set

$$`Z_{N,\ell}^{t}(\phi)=\sqrt N\left[\frac1N\sum_{i=1}^N\phi_\ell(X_i(t))-\int_{\mathbb T^{\mathsf{d}}}\phi_\ell(x)\,\mathrm dx\right].`

For probability laws $`P,Q` on $`\mathbb R^p`,

$$`d_3(P,Q)=\sup_{\|F\|_{C_b^3}\le1}\left|\int F\,\mathrm dP-\int F\,\mathrm dQ\right|,\qquad\|F\|_{C_b^3}=\sum_{j=0}^3\sup_z\|D^jF(z)\|.`

The supremum runs over $`C^3` functions with bounded derivatives through order three; derivative norms are operator norms.

The covariance is [$`\Sigma_b`](reader-anchor:decl-HRS.mesoCovMatrix).

For a real constant $`C_0` and a natural number $`N`, write

$$`o_N(C_0)=C_0N^{-q/\mathsf{d}}+\mathbf1_{\{\mathsf{s}=0\}}\frac{\log N}{2\mathsf{d} N}.`

Define the five-term error

$$`E_N(C_0,\ell)=N^{-1/2}\ell^{-\mathsf{d}/2}+\sqrt N\,o_N(C_0)\ell^{-\mathsf{d}/2-\max(q,2)}+N^{-1/\mathsf{d}}\ell^{-\mathsf{d}-3+\min(q,2)}+\sqrt{o_N(C_0)}\ell^{-(\mathsf{d}+q)/2-2+\min(q,2)}+\ell.`

For a configuration $`x=(x_i)_{i=1}^N`, define the modulated energy relative to Haar measure by

$$`\mathsf{F}_N^{\mathsf{g}}(x,\mathrm dx)=\frac1{2N^2}\sum_{i\ne j}\mathsf{g}(x_i-x_j)-\frac1N\sum_i\int \mathsf{g}(x_i-y)\,\mathrm dy+\frac12\iint \mathsf{g}(x-y)\,\mathrm dx\,\mathrm dy.`

*Stochastic hypotheses.*

On a probability space $`(\Omega,P)`, the initial configuration has product Haar law. The $`N\mathsf{d}` real coordinates of $`W` are independent standard Brownian motions, jointly independent of the initial configuration. The torus-valued process $`X` has measurable time slices, almost surely continuous paths, and the prescribed initial condition.

For each $`T\ge0`, there is a lift $`Y` of $`X` to $`(\mathbb R^{\mathsf{d}})^N` such that, almost surely, its drift is integrable and

$$`Y_i(t)=Y_i(0)-\frac1N\int_0^t\sum_{j\ne i}\nabla\mathsf{g}(X_i(v)-X_j(v))\,\mathrm dv+\sqrt{2/\beta}\,[W_i(t)-W_i(0)]\qquad(0\le t\le T).`

The particles are almost surely distinct throughout each $`[0,T]`. There is a Brownian filtration carrying a version of $`W` equal in all coordinates and times almost surely, relative to which $`X` is adapted and progressively measurable; for real times use $`X_{\max(t,0)}`. The kernel $`\mathsf{g}` is the periodic Riesz kernel and the external potential is zero.
:::

*Verification:* Proof-bearing declaration, with an exact-type check against the frozen `screening_comparison` statement. Historical Comparator acceptance applies to the provider and its type tie.

Uniform comparison

`HRS.screening_comparison_proof`

`HRS/Sections/ScrnFinal.lean`, line 21.

*Evidence:* Historical Comparator acceptance via exact-type tie; frozen `HRS.screening_comparison` itself contains sorry.

Exact theorem declaration · lines 21–50

```
theorem screening_comparison_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (bm bp : ℝ) (hbm : 0 < bm) (hbmp : bm ≤ bp) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 ≤ C ∧
      (∀ N : ℕ, 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (volume : Measure (Torus d)) + oN d s C₀ N) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (βN : ℝ) (hβN : 0 < βN) (ℓ b : ℝ), 0 < ℓ →
        βN * ℓ ^ ((d : ℝ) - s) ∈ Set.Icc bm bp → b ∈ Set.Icc bm bp →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsVectorBrownian P W →
          ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P →
          P.map X₀ = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))) →
          (∀ T' : ℝ, 0 ≤ T' →
            IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) βN hβN) T' X₀ W X) →
          (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
            (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
          ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
            smoothDist 3
                (law P fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
                    (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤
              C * ((N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) +
                Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
                (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
                Real.sqrt (oN d s C₀ N) *
                  ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
                ℓ + |βN * ℓ ^ ((d : ℝ) - s) - b|) := by
```

Exact-type check against the frozen statement · line 108

`example := (@screening_comparison_proof : type_of% @screening_comparison)`

## `HRS.kappaMax_pos_and_values`
%%%
tag := "decl-HRS.kappaMax_pos_and_values"
%%%

:::theorem "screening-provider-9" (lean := "HRS.kappaMax_pos_and_values")
Let $`\mathsf{d}\ge2`, $`0\le\mathsf{s}<\mathsf{d}/2`, and $`q=\mathsf{d}-\mathsf{s}`. Then

$$`\kappa_{\max}(\mathsf{d},\mathsf{s})>0,\qquad\kappa_{\max}(2,0)=\frac16,\qquad\kappa_{\max}(3,1)=\frac1{21}.`

The exponent [$`\kappa_{\max}`](reader-anchor:decl-HRS.kappaMax) is the minimum defined above.
:::

*Verification:* Proof-bearing declaration; historical Comparator acceptance is recorded separately from this statement.

Admissible shrinking scales

`HRS.kappaMax_pos_and_values`

`HRS/Sections/Sec6.lean`, line 146.

*Evidence:* Historical Comparator acceptance; local proof reviewed.

Exact theorem declaration · lines 146–148

```
theorem kappaMax_pos_and_values :
    (∀ (d : ℕ) (s : ℝ), 2 ≤ d → 0 ≤ s → s < (d : ℝ) / 2 → 0 < kappaMax d s) ∧
      kappaMax 2 0 = 1 / 6 ∧ kappaMax 3 1 = 1 / 21 := by
```

## `HRS.screening_error_tendsto`
%%%
tag := "decl-HRS.screening_error_tendsto"
%%%

:::theorem "screening-provider-10" (lean := "HRS.screening_error_tendsto")
Let $`\mathsf{d}\ge2`, $`0\le\mathsf{s}<\mathsf{d}/2`, and $`q=\mathsf{d}-\mathsf{s}`. For every $`C_0\ge0` and $`0<\kappa<\kappa_{\max}(\mathsf{d},\mathsf{s})`,

$$`E_N(C_0,N^{-\kappa})\longrightarrow0\qquad(N\to\infty).`

Use [$`\kappa_{\max}`](reader-anchor:decl-HRS.kappaMax) and the following error terms.

For a real constant $`C_0` and a natural number $`N`, write

$$`o_N(C_0)=C_0N^{-q/\mathsf{d}}+\mathbf1_{\{\mathsf{s}=0\}}\frac{\log N}{2\mathsf{d} N}.`

Define the five-term error

$$`E_N(C_0,\ell)=N^{-1/2}\ell^{-\mathsf{d}/2}+\sqrt N\,o_N(C_0)\ell^{-\mathsf{d}/2-\max(q,2)}+N^{-1/\mathsf{d}}\ell^{-\mathsf{d}-3+\min(q,2)}+\sqrt{o_N(C_0)}\ell^{-(\mathsf{d}+q)/2-2+\min(q,2)}+\ell.`
:::

*Verification:* Proof-bearing declaration; historical Comparator acceptance is recorded separately from this statement.

Error tends to zero

`HRS.screening_error_tendsto`

`HRS/Sections/Sec6.lean`, line 174.

*Evidence:* Historical Comparator acceptance; local proof assembly reviewed.

Exact theorem declaration · lines 174–182

```
theorem screening_error_tendsto (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (κ : ℝ) (hκ : 0 < κ) (hκm : κ < kappaMax d s) :
    Tendsto (fun N : ℕ =>
      (N : ℝ) ^ (-(1 : ℝ) / 2) * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) / 2) +
        Real.sqrt N * oN d s C₀ N * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
        (N : ℝ) ^ (-(1 : ℝ) / d) * ((N : ℝ) ^ (-κ)) ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
        Real.sqrt (oN d s C₀ N) *
          ((N : ℝ) ^ (-κ)) ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
        (N : ℝ) ^ (-κ)) atTop (𝓝 0) := by
```

## `HRS.screening_stationary_limit_proof`
%%%
tag := "decl-HRS.screening_stationary_limit_proof"
%%%

:::theorem "screening-provider-11" (lean := "HRS.screening_stationary_limit_proof")
Let $`\mathsf{d}\ge2`, $`0\le\mathsf{s}<\mathsf{d}/2`, and $`q=\mathsf{d}-\mathsf{s}`. Fix $`p\in\mathbb N`, real tests $`\phi_1,\ldots,\phi_p\in C_c^\infty(\mathbb R^{\mathsf{d}})`, $`x_0\in\mathbb R^{\mathsf{d}}`, $`b>0`, and $`0<\kappa<\kappa_{\max}(\mathsf{d},\mathsf{s})`. Set $`N_n=n+2` and $`\ell_n=(n+2)^{-\kappa}`. Suppose $`\beta_n>0` and $`\beta_n\ell_n^q\to b`. For each $`n\in\mathbb N`, let $`X_n` satisfy the stochastic hypotheses below with $`N=N_n` and $`\beta=\beta_n`, on a probability space $`(\Omega_n,P_n)`.

For every sequence $`u_n\ge0` with $`u_n\to\infty` and every fixed $`t_1,\ldots,t_p\ge0`,

$$`d_3\!\left(\operatorname{Law}_{P_n}\bigl((Z_{N_n,\ell_n}^{\ell_n^{2-q}(u_n+t_a)}(\phi_a))_{a=1}^p\bigr),\mathcal N(0,\Sigma_b^{\mathrm{stat}}(t,\phi))\right)\longrightarrow0.`

With normalized Haar measure $`\mathrm dx` and [$`\phi_\ell`](reader-anchor:decl-HRS.mesoTest), set

$$`Z_{N,\ell}^{t}(\phi)=\sqrt N\left[\frac1N\sum_{i=1}^N\phi_\ell(X_i(t))-\int_{\mathbb T^{\mathsf{d}}}\phi_\ell(x)\,\mathrm dx\right].`

For probability laws $`P,Q` on $`\mathbb R^p`,

$$`d_3(P,Q)=\sup_{\|F\|_{C_b^3}\le1}\left|\int F\,\mathrm dP-\int F\,\mathrm dQ\right|,\qquad\|F\|_{C_b^3}=\sum_{j=0}^3\sup_z\|D^jF(z)\|.`

The supremum runs over $`C^3` functions with bounded derivatives through order three; derivative norms are operator norms.

Use [$`\Sigma_b^{\mathrm{stat}}`](reader-anchor:decl-HRS.mesoStatCovMatrix) and [$`\kappa_{\max}`](reader-anchor:decl-HRS.kappaMax).

*Stochastic hypotheses.*

On a probability space $`(\Omega,P)`, the initial configuration has product Haar law. The $`N\mathsf{d}` real coordinates of $`W` are independent standard Brownian motions, jointly independent of the initial configuration. The torus-valued process $`X` has measurable time slices, almost surely continuous paths, and the prescribed initial condition.

For each $`T\ge0`, there is a lift $`Y` of $`X` to $`(\mathbb R^{\mathsf{d}})^N` such that, almost surely, its drift is integrable and

$$`Y_i(t)=Y_i(0)-\frac1N\int_0^t\sum_{j\ne i}\nabla\mathsf{g}(X_i(v)-X_j(v))\,\mathrm dv+\sqrt{2/\beta}\,[W_i(t)-W_i(0)]\qquad(0\le t\le T).`

The particles are almost surely distinct throughout each $`[0,T]`. There is a Brownian filtration carrying a version of $`W` equal in all coordinates and times almost surely, relative to which $`X` is adapted and progressively measurable; for real times use $`X_{\max(t,0)}`. The kernel $`\mathsf{g}` is the periodic Riesz kernel and the external potential is zero.
:::

*Verification:* Proof-bearing declaration, with an exact-type check against the frozen `screening_stationary_limit` statement. Historical Comparator acceptance applies to the provider and its type tie.

Stationary waiting window

`HRS.screening_stationary_limit_proof`

`HRS/Sections/ScrnFinal.lean`, line 110.

*Evidence:* Historical Comparator acceptance via exact-type tie; frozen `HRS.screening_stationary_limit` itself contains sorry.

Exact theorem declaration · lines 110–135

```
theorem screening_stationary_limit_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (κ : ℝ) (hκ : 0 < κ) (hκm : κ < kappaMax d s) (b : ℝ) (hb : 0 < b) (βN : ℕ → ℝ)
    (hβN : ∀ n, 0 < βN n)
    (hbN : Tendsto (fun n : ℕ => βN n * (((n + 2 : ℕ) : ℝ) ^ (-κ)) ^ ((d : ℝ) - s)) atTop (𝓝 b))
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (X₀ : ∀ n, Ω n → Config d (n + 2))
    (W : ∀ n, ℝ≥0 → Ω n → (Fin (n + 2) → Euc d)) (X : ∀ n, ℝ≥0 → Ω n → Config d (n + 2))
    (hW : ∀ n, IsVectorBrownian (P n) (W n))
    (hI : ∀ n, ProbabilityTheory.IndepFun (X₀ n) (fun ω => fun t : ℝ≥0 => W n t ω) (P n))
    (hX₀ : ∀ n, (P n).map (X₀ n) = Measure.pi (fun _ : Fin (n + 2) => (volume : Measure (Torus d))))
    (hsol : ∀ n, ∀ T' : ℝ, 0 ≤ T' →
      IsStrongSolution (P n) (PDE.mfData d s hs0 hsd (fun _ => 0) (βN n) (hβN n)) T' (X₀ n) (W n)
        (X n))
    (hfilt : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω n)))
      (W' : ℝ≥0 → Ω n → (Fin (n + 2) × Fin d) → ℝ), IsFilteredSolution (P n) ℱ W' (W n) (X n))
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) (t : Fin p → ℝ)
    (ht : ∀ a, 0 ≤ t a) :
    Tendsto (fun n : ℕ => smoothDist 3
      (law (P n) fun ω => (WithLp.toLp 2 fun a =>
        linCoord (volume : Measure (Torus d))
          (mesoTest d (((n + 2 : ℕ) : ℝ) ^ (-κ)) x₀ (φ a))
          (X n ((((n + 2 : ℕ) : ℝ) ^ (-κ)) ^ (2 - ((d : ℝ) - s)) * (u n + t a)).toNNReal ω) :
            EuclideanSpace ℝ (Fin p)))
      (ProbabilityTheory.multivariateGaussian 0 (mesoStatCovMatrix d s b t φ))) atTop (𝓝 0) := by
```

Exact-type check against the frozen statement · line 169

`example := (@screening_stationary_limit_proof : type_of% @screening_stationary_limit)`

## `HRS.meso_low_frequency`
%%%
tag := "decl-HRS.meso_low_frequency"
%%%

:::theorem "screening-provider-12" (lean := "HRS.meso_low_frequency")
Let $`\mathsf{d}\ge2`, $`0\le\mathsf{s}<\mathsf{d}/2`, and $`q=\mathsf{d}-\mathsf{s}`. Let $`b,t>0`. As $`\xi\to0` through $`\xi\ne0`,

$$`S_b(\xi)\longrightarrow0,\qquad S_b(\xi)+(1-S_b(\xi))e^{-2t a_b(\xi)}\longrightarrow\begin{cases}1,&q<2,\\e^{-2\mathsf{c}_{\mathsf{d},\mathsf{s}}t},&q=2,\\0,&q>2.\end{cases}`

Use [$`a_b`](reader-anchor:decl-HRS.mesoRate) and [$`S_b`](reader-anchor:decl-HRS.mesoSpectral). Here $`\mathsf{c}_{\mathsf{d},\mathsf{s}}` is the [Riesz normalization](reader-anchor:screening-notation).
:::

*Verification:* Proof-bearing declaration; historical Comparator acceptance is recorded separately from this statement.

Formation at low frequency

`HRS.meso_low_frequency`

`HRS/Sections/Sec6.lean`, line 299.

*Evidence:* Historical Comparator acceptance; local proof reviewed.

Exact theorem declaration · lines 299–308

```
theorem meso_low_frequency (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (b : ℝ)
    (hb : 0 < b) (t : ℝ) (ht : 0 < t) :
    (((d : ℝ) - s < 2 → Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0) (𝓝 1)) ∧
      ((d : ℝ) - s = 2 → Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0)
          (𝓝 (Real.exp (-2 * rieszConst d s * t)))) ∧
      (2 < (d : ℝ) - s → Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ +
        (1 - mesoSpectral d s b ξ) * Real.exp (-2 * t * mesoRate d s b ξ)) (𝓝[≠] 0) (𝓝 0))) ∧
    Tendsto (fun ξ : Euc d => mesoSpectral d s b ξ) (𝓝[≠] 0) (𝓝 0) := by
```

# Paper-to-Lean map
%%%
tag := "inventory"
%%%

The map covers every local paper label. Statement and proof review covers the results identified above. The intermediate energy, Fourier, semigroup and martingale estimates are included as navigation references. The Gaussian white-noise representation, quantitative decay rates and full stochastic-comparison derivation remain outside this correspondence review.

All 23 navigation items: section, proposition, remark and 20 equations

- *Section* · `sec:screening`

Section navigation: one proposition, one unlabelled remark and 20 labeled equations. Reviewed statements and proof steps are identified individually.

- *Equation* · `O:eq:screen-particles`

Stochastic hypotheses in provider; no existence claim.

`HRS.IsStrongSolution` `HRS.IsFilteredSolution` 

- *Equation* · `O:eq:meso-test`

Periodized test and fluctuation coordinate definitions.

[`HRS.mesoTest`](reader-anchor:decl-HRS.mesoTest) `HRS.linCoord` 

- *Equation* · `O:eq:meso-scales`

Scaling and convergence hypotheses used in the stationary limit.

[`HRS.screening_stationary_limit_proof`](reader-anchor:decl-`HRS.screening_stationary_limit_proof`) 

- *Equation* · `O:eq:meso-o`

Error correction and corrected-energy nonnegativity in provider conclusion.

`HRS.oN` [`HRS.screening_comparison_proof`](reader-anchor:decl-`HRS.screening_comparison_proof`) 

- *Equation* · `O:eq:meso-comm`

Provider imports commutator specification; exact displayed-paper inequality not independently audited here.

`HRS.Main.A8P.a8p_commSpec` 

- *Equation* · `O:eq:meso-coer`

Paper proof-navigation estimate. Exact declaration-level correspondence remains outside this review.

- *Equation* · `O:eq:meso-vnorm`

Paper norm definition used in presentation. Exact definition-level bridge outside this review.

- *Equation* · `O:eq:meso-multipliers`

Definitions shown above.

[`HRS.mesoRate`](reader-anchor:decl-HRS.mesoRate) [`HRS.mesoSpectral`](reader-anchor:decl-HRS.mesoSpectral) 

- *Equation* · `O:eq:meso-limit-cov`

Covariance definitions shown above; white-noise realization outside the correspondence review.

[`HRS.mesoCovMatrix`](reader-anchor:decl-HRS.mesoCovMatrix) [`HRS.mesoStatCovMatrix`](reader-anchor:decl-HRS.mesoStatCovMatrix) 

- *Equation* · `O:eq:screening-bound`

Full finite-dimensional error bound; solution and filtration assumptions retained.

[`HRS.screening_comparison_proof`](reader-anchor:decl-`HRS.screening_comparison_proof`) 

- *Equation* · `O:eq:kappa-range`

Exact range, positivity, two special values, and five-term convergence.

[`HRS.kappaMax`](reader-anchor:decl-HRS.kappaMax) [`HRS.kappaMax_pos_and_values`](reader-anchor:decl-`HRS.kappaMax_pos_and_values`) [`HRS.screening_error_tendsto`](reader-anchor:decl-`HRS.screening_error_tendsto`) 

- *Equation* · `O:eq:uniform-energy-meso`

Paper proof-navigation estimate; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-lambda`

Paper semigroup multiplier; exact declaration bridge not independently audited.

- *Equation* · `O:eq:meso-gap`

Paper proof-navigation estimate; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-Fourier-norms`

Paper proof-navigation estimates; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-v-bound`

Paper proof-navigation estimate; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-rem`

Paper proof-navigation remainder estimate; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-product-Lip`

Paper proof-navigation estimate; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-product-H`

Paper proof-navigation estimate; no independent exact local proof correspondence claimed.

- *Equation* · `O:eq:meso-bracket-error`

Paper proof-navigation estimate; final comparison assembly inspected, exact local bridge not independently audited.

- *Proposition* · `O:prop:screening`

One proposition split into four Lean results; two frozen statements have separate exact-type proof providers.

[`HRS.screening_comparison_proof`](reader-anchor:decl-`HRS.screening_comparison_proof`) [`HRS.kappaMax_pos_and_values`](reader-anchor:decl-`HRS.kappaMax_pos_and_values`) [`HRS.screening_error_tendsto`](reader-anchor:decl-`HRS.screening_error_tendsto`) [`HRS.screening_stationary_limit_proof`](reader-anchor:decl-`HRS.screening_stationary_limit_proof`) 

- *Unlabelled remark* · `M:@remark:L7716`

Low-frequency trichotomy and stationary spectral limit; Lean proof reviewed.

[`HRS.meso_low_frequency`](reader-anchor:decl-`HRS.meso_low_frequency`) 

Selected proof calls

Four selected direct calls in the proof source. Each arrow points *from a helper to the proof that uses it*.

## Four selected calls

- `HRS.Main.A8P.a8p_commSpec` is used by `HRS.screening_comparison_proof` (`ScrnFinal.lean`, line 52).

- `HRS.scrn_instance` is used by `HRS.screening_comparison_proof` (`ScrnFinal.lean`, line 53).

- `HRS.screening_error_tendsto` is used by `HRS.screening_stationary_limit_proof` (`ScrnFinal.lean`, line 150).

- `HRS.scrn_stat_gauss_tendsto` is used by `HRS.screening_stationary_limit_proof` (`ScrnFinal.lean`, line 155).

## Sources and verification

*Lean snapshot:* `48a9b5c1f9c99f70f59dd17a1b0cfe6f1b516c21`, Lean v4.34.1. The section’s statements and local proof routes are taken from `Sec6.lean` and `ScrnFinal.lean`. Source excerpts refer to this snapshot.

*Paper locator:* main manuscript, §6, lines 7556–7720. The manuscript supplies the organization and comparison labels; Lean supplies the formal statements and proofs.

*Correspondence review.* Five result descriptions, seven displayed formulas and selected local proof routes were checked against Lean, with no unresolved discrepancy in that scope. The 20 equation labels were matched to the paper. Imported proofs were not reviewed in full.

*Formal verification evidence.* Recorded nanoda and Lean kernel checks cover six definition roots, five theorem/provider checks and two exact-type ties. These checks are distinct from the package build and were not rerun for this exposition.

*Index coverage.* The section index records the paper’s labels and their links to the selected Lean declarations.

[Compare with the broad index →](reader-anchor:broad) · [Back to overview](reader-anchor:home)
