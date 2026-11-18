import HRS.Whole.Window
import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Relaxation on moving windows" =>

%%%
tag := "s11-moving-windows"
%%%

Start a gas at preparation parameter $`\gamma` and observe it on $`[u,u+T]`. How large must $`u` be before the stationary Gaussian law and its first correction describe the fluctuations to order $`o(N^{-1/2})`? Proposition S11.1 gives separate rates for the covariance and cubic tensor. Corollary S11.2 compares them with the error at finite $`N`.

# Setting and notation

Fix $`\mathsf d\ge 2`, $`0\le\mathsf s<\mathsf d/2`, $`a,\beta,T>0` and $`\gamma\ge 0`, with $`\gamma>0` when $`\mathsf s>0`. The confining potential is $`V(x)=a|x|^2/2`. Let $`\mu=\rho_\beta\,\mathrm dx` be a thermal equilibrium with Poincaré constant $`\lambda>0`, and put $`\kappa=\lambda/\beta`. The observation space is $`\mathcal X_T=C([0,T];B_{24\mathsf d+240})`, where $`B_m` is the dual of the oscillator space $`\Sigma^m`.

For $`\theta\in\{\gamma,\beta\}`, take a linear Gaussian evolution about $`\rho_\beta` on every finite time interval, with diffusivity $`\beta^{-1}` and initial susceptibility covariance at $`(\theta,\mu)`. Write $`Z_{\theta,u}(t)=Z_\theta^{u+t}` for $`0\le t\le T` and $`Z_*=Z_{\beta,0}` for the stationary window. The two Gaussian laws may be realized on different probability spaces.

The frozen theorem declarations contain admissions. Separate companion proofs have matching types; see the proof supplement.

# Proposition S11.1 · Covariance and cubic-tensor relaxation

%%%
tag := "s11-tensor-relaxation"
%%%

:::theorem "s11-tensor-relaxation-declaration" (lean := "HRS.Whole.r2_tensor_relaxation")
There are constants $`c>0` and $`C` depending only on $`\mathsf d,\mathsf s,a,\beta,\gamma,T,\lambda` such that, for every $`u\ge0` and every continuous bilinear form $`M` on $`\mathcal X_T` of norm at most one,
$$`\big|\mathbb E M(Z_{\gamma,u},Z_{\gamma,u})-\mathbb E M(Z_*,Z_*)\big|\le C e^{-2\kappa u}.`

Let $`\mathcal K_{\gamma,u}` and $`\mathcal K_*` be any cubic path tensors satisfying the observation formula below for the preparations $`(\gamma,u)` and $`(\beta,0)`, respectively. In the projective tensor norm,
$$`\|\mathcal K_{\gamma,u}-\mathcal K_*\|_\pi\le C e^{-cu}.`

The covariance rate is explicit. The cubic estimate requires only some positive $`c`.
:::

Companion proof (exact type checked): `HRS.Fp81.V01.fp81v01_tensor_relaxation`.

```
theorem fp81v01_tensor_relaxation : type_of% @HRS.Whole.r2_tensor_relaxation :=
  HRS.MS.S111K4.k4_tensor_relaxation_of_V01 fp81v01_K4V01All
```

# Corollary S11.2 · The stationary first correction

%%%
tag := "s11-two-parameter-edgeworth"
%%%

:::theorem "s11-two-parameter-edgeworth-declaration" (lean := "HRS.Whole.r2_two_parameter_edgeworth")
Take a particle realization of the quadratic gradient dynamics with initial law $`Q_{N,\gamma}(\mu)`, the modulated Gibbs law at preparation $`\gamma`. On the window $`[u,u+T]`, write $`\zeta_{N,u}` for the path of the empirical measure centered at its own expectation and multiplied by $`\sqrt N`. Fix cubic tensors $`\mathcal K_{\gamma,u}` for all $`u\ge0` and $`\mathcal K_*` for the stationary window, as in Proposition S11.1. Write $`A(W,K;\Phi)` for the expected cubic pairing defined below.

For $`N\ge2`, suppose $`\varepsilon_N` bounds the moving-window error uniformly over $`u\ge0` and the unit ball of $`C_b^5(\mathcal X_T)`:
$$`\left|\sqrt N\bigl(\mathbb E\Phi(\zeta_{N,u})-\mathbb E\Phi(Z_{\gamma,u})\bigr)-\tfrac16 A(Z_{\gamma,u},\mathcal K_{\gamma,u};\Phi)\right|\le\varepsilon_N.`

Define the stationary remainder by
$$`R_{N,u}(\Phi)=\mathbb E\Phi(\zeta_{N,u})-\mathbb E\Phi(Z_*)-\tfrac{1}{6\sqrt N} A(Z_*,\mathcal K_*;\Phi).`
There are constants $`c>0` and $`C`, depending only on the parameters in Proposition S11.1, for which
$$`\sup_{\|\Phi\|_{C_b^5}\le1}|R_{N,u}(\Phi)|\le\frac{\varepsilon_N}{\sqrt N}+C e^{-2\kappa u}+\frac{C}{\sqrt N} e^{-cu}.`

For a sequence of such realizations, assume $`\varepsilon_N\to0`. If $`u_N\ge0` and $`\sqrt N e^{-2\kappa u_N}\to0`, then $`\sup_{\|\Phi\|_{C_b^5}\le1}|R_{N,u_N}(\Phi)|=o(N^{-1/2})`. In particular this holds if, for some $`\delta>0` and all $`N\ge2`,
$$`u_N\ge\left(\frac{1}{4\kappa}+\delta\right)\log N.`
:::

Companion proof (exact type checked): `HRS.Fp81.V01.fp81v01_two_parameter_edgeworth`.

```
theorem fp81v01_two_parameter_edgeworth :
    type_of% @HRS.Whole.r2_two_parameter_edgeworth := by
  intro d hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
  exact HRS.MS.S111T.s111t_two_param_of_producers hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam
    (fp81v01_physical_V01 hd s a β γ T lam hs0 hs ha hβ hγ hT hlam)
    (fp81v01_physical_V01 hd s a β β T lam hs0 hs ha hβ hβ.le hT hlam)
    (HRS.MS.S111K4.k4_v02_contract hd s hs0 hs a β ha hβ T)
```

# The observation space

%%%
tag := "s11-window-space"
%%%

:::definition "s11-window-space-declaration" (lean := "HRS.Whole.R2X")
A window is a continuous path $`w:[0,T]\to B_m` with the uniform norm, where $`m=24\mathsf d+240`. At $`t\in[0,T]`, the field $`w(t)` acts on oscillator tests in $`\Sigma^m`.
:::

# The Poincaré constant

%%%
tag := "s11-poincare-constant"
%%%

:::definition "s11-poincare-constant-declaration" (lean := "HRS.Whole.IsR2Poincare")
The measure $`\mu` satisfies the Poincaré inequality with constant $`\lambda` if every real $`C^1` function $`f\in L^2(\mu)` with bounded gradient satisfies
$$`\lambda\,\operatorname{Var}_\mu(f)\le\int |\nabla f|^2\,\mathrm d\mu.`
The proposition and corollary take $`\lambda>0`.
:::

# The particle dynamics

%%%
tag := "s11-particle-realization"
%%%

:::definition "s11-particle-realization-declaration" (lean := "HRS.Whole.IsR2Realization")
The driving noise is a vector Brownian motion independent of the initial configuration. The particle paths give a strong solution on every finite time interval. There is a filtration under which a Brownian motion $`W'` has coordinates $`W'_{i,j}=W_i^j` almost surely for every time and index. The particle paths are adapted and progressively measurable for this same filtration. Corollary S11.2 prescribes the initial law separately.
:::

# The cubic path tensor

%%%
tag := "s11-cubic-tensor"
%%%

:::definition "s11-cubic-tensor-declaration" (lean := "HRS.Whole.IsR2PathCubic")
For preparation $`\theta` and shift $`u`, the cubic path tensor is specified by the three-observation formula of Theorem S2.1(iii) at the constant trajectory $`\rho^r=\rho_\beta`. It is a symmetric element of $`\mathcal X_T^{\widehat\otimes_\pi3}`. Choose three times $`\tau_i\in[0,T]`, smooth oscillator tests $`\phi_i\in\Sigma^{24\mathsf d+240}`, and put $`t_i=u+\tau_i`. For each such choice there must exist cross-covariance densities $`\chi_i^r` for all $`0\le r\le u+T`. They satisfy $`\chi_i^r/\rho_\beta\in L^2(\mu)` and, for every oscillator test $`\psi`,
$$`\int\psi\,\chi_i^r\,\mathrm dx=\operatorname{Cov}(Z_\theta^r(\psi),Z_\theta^{t_i}(\phi_i)),`
with integrable product. For every such family of densities, the tensor evaluated on the trilinear form $`M(w_1,w_2,w_3)=\prod_i w_i(\tau_i)(\phi_i)` must equal the three terms of that formula at the physical times $`t_i`. All its spatial and time integrals must exist as specified there.
:::

# The expected cubic pairing

%%%
tag := "s11-expected-cubic-pairing"
%%%

:::definition "s11-expected-cubic-pairing-declaration" (lean := "HRS.Whole.r2CubicExpect")
For a random path $`W`, a projective cubic tensor $`K` and a test $`\Phi` on $`\mathcal X_T`, set
$$`A(W,K;\Phi)=\mathbb E\,\langle K,D^3\Phi(W)\rangle.`
Here $`D^3\Phi(w)` is the third Fréchet derivative, a continuous trilinear form on $`\mathcal X_T`.
:::

