import HRS.Whole.Headline
import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Whole-space fluctuations" =>

%%%
tag := "whole-space-headlines"
%%%

For $`C_b^j` we use $`\|f\|_{C_b^j}=\sum_{i=0}^j\sup_x\|D^i f(x)\|`, including the function itself. Let $`h_\alpha` be the normalized Hermite functions and $`\lambda_\alpha=2|\alpha|+\mathsf d+1`. The oscillator space $`\Sigma^m` consists of the $`L^2(\mathbb R^{\mathsf d})` functions for which $`\|f\|_{\Sigma^m}^2=\sum_\alpha\lambda_\alpha^m|\langle f,h_\alpha\rangle|^2` is finite. Its continuous dual is $`B_m`. Oscillator tests are smooth functions in $`\Sigma^m`.

A whole-space mean-field solution consists of probability densities $`\mu^t=\rho^t\,dx` with finite second moment at each time. For every $`C_b^2` test $`f` and each time $`t` in the interval, its weak equation is
$$`\langle\mu^t-\mu^0,f\rangle=\int_0^t\!\left[\langle\mu^r,\nu\Delta f-\nabla V\cdot\nabla f\rangle+\tfrac12\iint_{x\ne y}(\nabla f(x)-\nabla f(y))\cdot M\nabla\mathsf g(x-y)\,\mathrm d\mu^r(x)\,\mathrm d\mu^r(y)\right]\,\mathrm dr.`
Here $`\nu` is the diffusivity and $`M` the interaction matrix; for the quadratic gradient dynamics of Theorem S2.1 they are $`\beta^{-1}` and $`-I`.

# Theorem S2.1(i) · Equilibrium paths with exact centering

%%%
tag := "headline-whole-space-stationary"
%%%

:::theorem "headline-whole-space-stationary-provider" (lean := "HRS.Whole.whole_space_stationary")
Let $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d` and $`a,\beta,T>0`. For quadratic confinement $`V(x)=a|x|^2/2` there are constants $`C_0,C`, uniform in the thermal equilibrium $`\mu_\beta=\rho_\beta\,dx` and in $`N\ge2`, with the following properties. For every configuration of distinct particles,
$$`\mathsf F_N^{\mathsf g}(X_N,\mu_\beta)+o_N\ge0.`
Here $`\mathsf g(x)=|x|^{-\mathsf s}` for $`\mathsf s>0` and $`\mathsf g(x)=-\log|x|` for $`\mathsf s=0`, off the diagonal. The equilibrium minimizes the mean-field free energy and satisfies the normalized thermal equation.

Suppose the canonical Gibbs law is invariant under the particle dynamics at this $`N`. Start a strong solution from that law, independently of its vector Brownian motion. Let $`Z_\beta` be any linear Gaussian evolution at $`\rho_\beta`, with noise parameter $`\beta^{-1}` and initial susceptibility covariance at $`(\beta,\mu_\beta)`. Set $`\zeta_N^t=\sqrt N(\mu_N^t-\mathbb E\mu_N^t)`. On $`\mathcal X_T=C([0,T];B_{24\mathsf d+240})` the two window paths are almost everywhere measurable and their laws satisfy
$$`d_2(\zeta_N,Z_\beta)\le C\bigl(\sqrt{\delta_N}+w_N\bigr),\qquad W_1(\zeta_N,Z_\beta)\le\bigl[C(\delta_N^{3/20}+\sqrt{w_N})\bigr]_+.`
:::

## Notation and hypotheses

Here $`d_2` tests the unit ball of $`C_b^2(\mathcal X_T)`, and $`W_1` uses the supremum path norm. Set $`o_N=C_0N^{\mathsf s/\mathsf d-1}+\mathbf1_{\{\mathsf s=0\}}\log N/(2\mathsf d N)` and $`w_N=(N^{-1/\mathsf d}+\sqrt{o_N})^{4/(\mathsf d+4)}`. The rate $`\delta_N` is $`N^{-1}` below $`\mathsf d/2`, $`N^{-1}\log(eN)` at $`\mathsf d/2`, and $`N^{1-\mathsf d/\mathsf s}` above it. The positive part $`[\cdot]_+` is the embedding of a real upper bound in the extended nonnegative reals.

Exact Lean source: `HRS.Whole.whole_space_stationary`.

```
theorem whole_space_stationary (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) :
    ∃ C₀ C : ℝ, (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal ρβ) + oN d s C₀ N) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
      GibbsInvariant d s a β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
        law P X₀ = canonicalGibbs (rieszKernel d s) (confinement a) N β →
        IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
        IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T
          (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) β) Z →
        AEMeasurable (zetaPathW (wholeSpaceIndex d) T 0 P X) P ∧
        AEMeasurable (processWindow (wholeSpaceIndex d) T 0 Z) P' ∧
        smoothDist 2 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
            (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
          C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ∧
        wassersteinE 1 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
            (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
          ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N))) :=
  @HRS.MS.S21.whole_space_stationary_proof d hd s hs0 hsd a β ha hβ T hT
```

# Theorem S2.1(ii) · Prepared nonequilibrium paths

%%%
tag := "headline-whole-space-prepared"
%%%

:::theorem "headline-whole-space-prepared-provider" (lean := "HRS.Whole.whole_space_prepared")
Let $`\mathsf d\ge2`, $`0\le\mathsf s<2\mathsf d/3`, $`a,\beta,T>0` and $`\beta_0\ge0`. Fix $`c_1,C_1\in\mathbb R`. There exist $`\varepsilon_*>0` and $`C_0,C` for the following class. Take a thermal equilibrium $`\mu_\beta=\rho_\beta\,dx` for $`V(x)=a|x|^2/2`. Set $`\rho^0=(1+\varepsilon\psi)\rho_\beta`, with $`0\ne\psi\in C_c^\infty`, $`\int\psi\,d\mu_\beta=0` and
$$`\|\varepsilon\psi\|_{C_b^{100\mathsf d+1001}}+\|\varepsilon\sqrt{\rho_\beta}\,\psi\|_{\Sigma^{102\mathsf d+1020}}\le\varepsilon_*.`
Take a resulting global mean-field solution $`\mu^t=\rho^t dx` in the specified decay class: $`c_1>0`, $`C_1^{-1}\rho_\beta\le\rho^t\le C_1\rho_\beta`, and the weighted perturbation and velocity bounds below hold. For every $`N\ge2`, $`t\ge0` and collision-free $`X_N`,
$$`\mathsf F_N^{\mathsf g}(X_N,\mu^t)+o_N\ge0.`

Suppose relative entropy with respect to the canonical Gibbs law contracts under the particle dynamics at this $`N`. Start the particles at time zero from the modulated Gibbs law of $`(\beta_0,\mu^0)` independently of their Brownian motion, and take a strong solution on every finite interval. Let $`Z` be a linear Gaussian evolution on every finite interval along $`\rho^t`, with noise parameter $`\beta^{-1}` and initial susceptibility covariance at $`(\beta_0,\mu^0)`. With $`\eta_N^t=\sqrt N(\mu_N^t-\mu^t)`, both window paths are almost everywhere measurable. Uniformly in the window start $`h\ge0`, the laws on $`\mathcal X_T=C([0,T];B_{24\mathsf d+240})` satisfy
$$`d_2(\eta_N^{h+\cdot},Z^{h+\cdot})\le C\bigl(\sqrt N\,\delta_N+w_N+i_N\bigr),`
$$`W_1(\eta_N^{h+\cdot},Z^{h+\cdot})\le\bigl[C\bigl(\sqrt N\,\delta_N+\sqrt{w_N}+j_N\bigr)\bigr]_+.`
Use $`o_N,\delta_N,w_N,d_2` as in part (i). For independent preparation ($`\beta_0=0`), $`i_N=j_N=N^{-1/(4\mathsf d+6)}`. For $`\beta_0>0`, $`i_N=\sqrt{\delta_N}` and $`j_N=\delta_N^{3/20}`.
:::

## Notation and hypotheses

In the decay hypothesis, $`v^t=(\rho^t-\rho_\beta)/\sqrt{\rho_\beta}` is continuous in $`t\ge0` with values in $`\Sigma^{102\mathsf d+1020}`, with norm at most $`C_1\varepsilon_*e^{-c_1t}`. Each $`\rho^t` is continuous in space, and the sum of the $`C_b^{100\mathsf d+1000}` norms of $`\nabla\log(\rho^t/\rho_\beta)` and $`\beta^{-1}\nabla\log\rho^t+ax+\nabla\mathsf g*\rho^t` has the same bound. Existence of such a solution is a separate result.

Exact Lean source: `HRS.Whole.whole_space_prepared`.

```
theorem whole_space_prepared(hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (T : ℝ) (hT : 0 < T)
    (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ C : ℝ,
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal (ρ t)) + oN d s C₀ N) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N →
        GibbsEntropyContraction d s a β N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
          (X : ℝ≥0 → Ω → EucConfig d N),
          IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
          law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
          (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
          (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
            (wholeSpaceIndex d) β⁻¹ T'
            (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
        ∀ a₀ : ℝ, 0 ≤ a₀ →
          AEMeasurable (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ) P ∧
          AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
          smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
              (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
            C * (Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N) ∧
          wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
              (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N +
              Real.sqrt (localizationRate d s C₀ N) + jN d s β₀ N)) :=
  @HRS.MS.S104e.s104e_final_whole_space_prepared d hd s hs0 hs a β ha hβ β₀ hβ₀ T hT c₁ C₁
```

# Theorem S2.1(iii) · First correction on moving windows

%%%
tag := "headline-whole-space-edgeworth"
%%%

:::theorem "headline-whole-space-edgeworth-provider" (lean := "HRS.Whole.whole_space_edgeworth")
Assume $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d/2`, $`a,\beta,T>0` and $`\beta_0\ge0`, with $`\beta_0>0` when $`\mathsf s>0`. Fix $`c_1,C_1\in\mathbb R`. There exists $`\varepsilon_*>0` such that the following holds for every thermal equilibrium $`\rho_\beta`, admissible perturbation $`(\varepsilon,\psi)` and resulting mean-field solution $`\rho^t` in the smallness and decay classes of part (ii). Set $`\mathcal X_T=C([0,T];B_{24\mathsf d+240})`. There are symmetric projective cubic tensors $`\kappa_h` with $`\sup_{h\ge0}\|\kappa_h\|_\pi<\infty`, and $`e_N\to0`. The tensors and errors may depend on the mean-field data.

For $`N\ge2`, start from the modulated Gibbs law of $`(\beta_0,\mu^0)` independently of the driving Brownian motion. Take any strong particle solution and linear Gaussian evolution $`Z` on every finite interval, the latter along $`\rho^t` with noise parameter $`\beta^{-1}` and initial susceptibility covariance at $`(\beta_0,\mu^0)`. Center at the actual expected empirical measure: $`\zeta_N^t=\sqrt N(\mu_N^t-\mathbb E\mu_N^t)`. Both window maps are almost everywhere measurable. For $`h\ge0` and $`\|\Phi\|_{C_b^5(\mathcal X_T)}\le1`,
$$`\left|\sqrt N\bigl(\mathbb E\Phi(\zeta_N^{h+\cdot})-\mathbb E\Phi(Z^{h+\cdot})\bigr)-\tfrac16\mathbb E\langle\kappa_h,D^3\Phi(Z^{h+\cdot})\rangle\right|\le e_N.`
:::

## Tensor on three observations

The tensor is specified on products of three observations. Take $`\tau_i\in[0,T]`, $`t_i=h+\tau_i`, and smooth oscillator tests $`\phi_i\in\Sigma^{24\mathsf d+240}`. There exist densities $`\chi_i^r` for every $`0\le r\le h+T` such that $`\chi_i^r/\rho^r\in L^2(\mu^r)` and
$$`\int\varphi\chi_i^r\,dx=\operatorname{Cov}(Z^r(\varphi),Z^{t_i}(\phi_i))`
for all such tests $`\varphi`, with integrable product. Here the covariance denotes that of the linearized Gaussian evolution with the stated initial covariance; it is defined from the coefficients before choosing a realization. Set $`f_i^r=U(r,t_i)\phi_i` and let $`R_i` be the susceptibility response to $`f_i^0` at $`(\beta_0,\mu^0)`. For *every* such family $`\chi` and every bounded trilinear form $`M` on $`\mathcal X_T` with $`M(w_1,w_2,w_3)=\prod_i w_i(\tau_i)(\phi_i)`, its pairing with $`\kappa_h` is the sum of these three terms (cyclic indices):
$$`\int R_1R_2R_3\,d\mu^0,`
$$`-\sum_i\int_0^{t_i}\iint h_{\nabla f_i^r}(x,y)\chi_{i+1}^r(x)\chi_{i+2}^r(y)\,dx\,dy\,dr,`
$$`\frac2\beta\sum_i\int_0^{\min(t_i,t_{i+1})}\int\nabla f_i^r\cdot\nabla f_{i+1}^r\,\chi_{i+2}^r\,dx\,dr.`
Here $`h_v(x,y)=(v(x)-v(y))\cdot\nabla\mathsf g(x-y)`. The first product is integrable; the spatial integrands in the other two terms are integrable at every indicated time, and their spatial integrals are integrable in time.

Exact Lean source: `HRS.Whole.whole_space_edgeworth`.

```
theorem whole_space_edgeworth (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀s : 0 < s → 0 < β₀)
    (T : ℝ) (hT : 0 < T) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∃ (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ),
          (∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖κ a₀‖ ≤ Kb) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
            (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
            (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) (M.domDomCongr σ) =
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M) ∧
          Tendsto εN atTop (𝓝 0) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
            (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
            (∃ χ : Fin 3 → ℝ → Euc d → ℝ,
              ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
                MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
                ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                  Integrable (fun x => ψ' x * χ i r x) ∧
                  ∫ x, ψ' x * χ i r x = linearGaussianCov
                    ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                    (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                    ψ' (φ i)) ∧
            ∀ χ : Fin 3 → ℝ → Euc d → ℝ,
            (∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
              MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
              ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                Integrable (fun x => ψ' x * χ i r x) ∧
                ∫ x, ψ' x * χ i r x = linearGaussianCov
                  ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                  (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                  ψ' (φ i)) →
            ∀ M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ,
              (∀ w : Fin 3 → OscPath d (wholeSpaceIndex d) T,
                M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) →
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M =
                cubicFormula (quadraticGradientDyn d s a β) ρ β β₀ (withDensityReal (ρ 0))
                  (fun i => a₀ + τ i) φ χ ∧
              CubicFormulaIntegrable (quadraticGradientDyn d s a β) ρ β₀ (withDensityReal (ρ 0))
                (fun i => a₀ + τ i) φ χ) ∧
          ∀ N : ℕ, 2 ≤ N →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
            (X : ℝ≥0 → Ω → EucConfig d N),
            IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
            law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
            (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
            (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
              (wholeSpaceIndex d) β⁻¹ T'
              (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
          ∀ a₀ : ℝ, 0 ≤ a₀ →
            AEMeasurable (zetaPathW (wholeSpaceIndex d) T a₀ P X) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
            ∀ Φ : OscPath d (wholeSpaceIndex d) T → ℝ,
              Φ ∈ CbUnitBall (OscPath d (wholeSpaceIndex d) T) 5 →
              |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T a₀ P X ζ) ∂P -
                  ∫ ζ', Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ') ∂P') -
                (1 / 6) * ∫ ζ', (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
                  (iteratedFDeriv ℝ 3 Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ')) ∂P'| ≤
                εN N :=
  @HRS.Fp81.S21.fp81s21_whole_space_edgeworth d hd s hs0 hs a β ha hβ β₀ hβ₀ hβ₀s T hT c₁ C₁
```

# Corollary S3.2 · preparation bounds · Entropy bounds for two preparations

%%%
tag := "headline-euclidean-preparations-bounds"
%%%

:::theorem "headline-euclidean-preparations-bounds-provider" (lean := "HRS.Whole.euclidean_preparations_bounds")
Let $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d`, $`M,L\in\mathbb R`, and $`b,b_0>0`. There is $`C\in\mathbb R`, depending only on $`\mathsf d,\mathsf s,M,L,b,b_0`, with the following property. Let $`\rho` be a measurable probability density with $`0\le\rho(x)\le M` for every $`x`. If $`\mathsf s=0`, assume $`\log(2+|x|)\in L^1(\mu)` and $`\int\log(2+|x|)\,\mathrm d\mu\le L`.
For every $`N\ge2`,
$$`H(\mu^{\otimes N}\mid\mathbb Q_{N,b}(\mu))+H(\mathbb Q_{N,b_0}(\mu)\mid\mathbb Q_{N,b}(\mu))\le [CN\delta_N]_+.`
In particular both relative entropies are finite.
:::

## Notation

Set $`\mu=\rho\,\mathrm dx`, $`\mu_N=N^{-1}\sum_{i=1}^N\delta_{x_i}`, and
$$`\mathsf g(x)=\begin{cases}-\log|x|,&\mathsf s=0,\\ |x|^{-\mathsf s},&\mathsf s>0,\end{cases}\qquad
\delta_N=\begin{cases}N^{-1},&\mathsf s<\mathsf d/2,\\N^{-1}\log(eN),&\mathsf s=\mathsf d/2,\\N^{1-\mathsf d/\mathsf s},&\mathsf s>\mathsf d/2.\end{cases}`
The particle diagonal is omitted. For a symmetric pair kernel $`h`, set
$$`D_\mu(h)(X_N)=\frac1{N^2}\sum_{i\ne j}h(x_i,x_j)-\frac2N\sum_i\int h(x_i,y)\,\mathrm d\mu(y)+\iint h(x,y)\,\mathrm d\mu(y)\,\mathrm d\mu(x).`
Write $`h_v(x,y)=(v(x)-v(y))\cdot\nabla\mathsf g(x-y)` and $`h_f=h_{\nabla f}`.

The modulated energy and Gibbs law are
$$`\mathsf F_N(X_N,\mu)=\tfrac12D_\mu\bigl((x,y)\mapsto\mathsf g(x-y)\bigr)(X_N),\qquad
\mathrm d\mathbb Q_{N,b}(\mu)=K_{N,b}(\mu)^{-1}e^{-bN\mathsf F_N(X_N,\mu)}\,\mathrm d\mu^{\otimes N},`
where $`K_{N,b}(\mu)=\int e^{-bN\mathsf F_N(X_N,\mu)}\,\mathrm d\mu^{\otimes N}`. Relative entropy $`H` takes values in $`[0,\infty]`; $`[u]_+=\max\{u,0\}`.

Exact Lean source: `HRS.Whole.euclidean_preparations_bounds`.

```
theorem euclidean_preparations_bounds (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M L b b₀ : ℝ)
    (hb : 0 < b) (hb₀ : 0 < b₀) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
        relEntropy (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) +
          relEntropy (modulatedGibbs (rieszKernel d s) N b₀ (withDensityReal ρ))
            (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * N * deltaN d s N) :=
  @HRS.MS.Wr.euclidean_preparations_bounds_proof d s hd hs0 hsd M L b b₀ hb hb₀
```

# Corollary S3.2 · stationary transfer · Stationary-reference transfer

%%%
tag := "headline-euclidean-preparations-stationary"
%%%

:::theorem "headline-euclidean-preparations-stationary-provider" (lean := "HRS.Whole.euclidean_preparations_stationary")
Let $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d`, $`M,L\in\mathbb R`, and $`b,b_0>0`. There is $`C\in\mathbb R`, depending only on $`\mathsf d,\mathsf s,M,L,b,b_0`, with the following property. Let $`\rho` be a measurable probability density with $`0\le\rho(x)\le M` for every $`x`. If $`\mathsf s=0`, assume $`\log(2+|x|)\in L^1(\mu)` and $`\int\log(2+|x|)\,\mathrm d\mu\le L`.
Suppose $`V:\mathbb R^{\mathsf d}\to\mathbb R` satisfies the thermal equation
$$`\rho(x)=\frac{\exp[-b(V(x)+(\mathsf g*\mu)(x))]}{\int\exp[-b(V(y)+(\mathsf g*\mu)(y))]\,\mathrm dy}.`
Fix $`N\ge2` and assume $`\mathbb Q_{N,b}(\mu)` is invariant in the following sense: on every probability space, every particle process with viscosity $`\nu=b^{-1}`, initial law $`\mathbb Q_{N,b}(\mu)` and initial configuration independent of its driving Brownian motion has that same law at every time in its finite horizon.

Every such particle process whose initial configuration is independent of the Brownian motion and whose initial law is either $`\mu^{\otimes N}` or $`\mathbb Q_{N,b_0}(\mu)` satisfies, for every $`0\le t\le T`, with $`f_N^t=\operatorname{Law}(X^t)`,
$$`H(f_N^t\mid\mathbb Q_{N,b}(\mu))+H(f_N^t\mid\mu^{\otimes N})\le[CN\delta_N]_+.`
For every measurable $`a` and real $`A` with $`|a(x)|\le A` everywhere, and every globally $`\Lambda`-Lipschitz vector field $`v`, $`\Lambda\ge0`,
$$`\mathbb E|\mu_N^t(a)-\mu(a)|\le CA\sqrt{\delta_N},\qquad
\mathbb E|D_\mu(h_v)(X^t)|\le C\Lambda\delta_N.`
Both random variables in these last two estimates are integrable. The same $`C` works for every admissible $`\rho,V,N,T`, realization, time and test function.
:::

## Notation and dynamics

Set $`\mu=\rho\,\mathrm dx`, $`\mu_N=N^{-1}\sum_{i=1}^N\delta_{x_i}`, and
$$`\mathsf g(x)=\begin{cases}-\log|x|,&\mathsf s=0,\\ |x|^{-\mathsf s},&\mathsf s>0,\end{cases}\qquad
\delta_N=\begin{cases}N^{-1},&\mathsf s<\mathsf d/2,\\N^{-1}\log(eN),&\mathsf s=\mathsf d/2,\\N^{1-\mathsf d/\mathsf s},&\mathsf s>\mathsf d/2.\end{cases}`
The particle diagonal is omitted. For a symmetric pair kernel $`h`, set
$$`D_\mu(h)(X_N)=\frac1{N^2}\sum_{i\ne j}h(x_i,x_j)-\frac2N\sum_i\int h(x_i,y)\,\mathrm d\mu(y)+\iint h(x,y)\,\mathrm d\mu(y)\,\mathrm d\mu(x).`
Write $`h_v(x,y)=(v(x)-v(y))\cdot\nabla\mathsf g(x-y)` and $`h_f=h_{\nabla f}`.

The modulated energy and Gibbs law are
$$`\mathsf F_N(X_N,\mu)=\tfrac12D_\mu\bigl((x,y)\mapsto\mathsf g(x-y)\bigr)(X_N),\qquad
\mathrm d\mathbb Q_{N,b}(\mu)=K_{N,b}(\mu)^{-1}e^{-bN\mathsf F_N(X_N,\mu)}\,\mathrm d\mu^{\otimes N},`
where $`K_{N,b}(\mu)=\int e^{-bN\mathsf F_N(X_N,\mu)}\,\mathrm d\mu^{\otimes N}`. Relative entropy $`H` takes values in $`[0,\infty]`; $`[u]_+=\max\{u,0\}`.

The particle process has continuous paths, measurable time marginals and no collisions almost surely throughout $`[0,T]`, and satisfies, with absolutely integrable drift,
$$`X_i^t=X_i^0-\int_0^t\left(\frac1N\sum_{j\ne i}\nabla\mathsf g(X_i^r-X_j^r)+\nabla V(X_i^r)\right)\,\mathrm dr+\sqrt{2\nu}\,(W_i^t-W_i^0).`
Here $`W` is a standard vector Brownian motion on the underlying probability space.

Exact Lean source: `HRS.Whole.euclidean_preparations_stationary`.

```
theorem euclidean_preparations_stationary (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (M L b b₀ : ℝ) (hb : 0 < b) (hb₀ : 0 < b₀) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) → ∀ V : Euc d → ℝ,
      IsThermalDensity (rieszKernel d s) V b ρ → ∀ N : ℕ, 2 ≤ N →
      (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (T : ℝ) (X₀' : Ω' → EucConfig d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d))
          (X' : ℝ≥0 → Ω' → EucConfig d N), IsVectorBrownian P' W' →
          IndepFun X₀' (fun ζ t => W' t ζ) P' →
          law P' X₀' = modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ) →
          IsWholeStrongSolution P' (⟨s, -1, V, b⁻¹⟩ : WholeDyn d) T X₀' W' X' →
          ∀ t : ℝ≥0, (t : ℝ) ≤ T →
            law P' (X' t) = modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
        (law P X₀ = Measure.pi (fun _ : Fin N => withDensityReal ρ) ∨
          law P X₀ = modulatedGibbs (rieszKernel d s) N b₀ (withDensityReal ρ)) →
        IsWholeStrongSolution P (⟨s, -1, V, b⁻¹⟩ : WholeDyn d) T X₀ W X →
        ∀ t : ℝ≥0, (t : ℝ) ≤ T →
          (relEntropy (law P (X t)) (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) +
            relEntropy (law P (X t)) (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
              ENNReal.ofReal (C * N * deltaN d s N)) ∧
          (∀ (a : Euc d → ℝ) (A : ℝ), Measurable a → (∀ x, |a x| ≤ A) →
            Integrable (fun ζ => |pair (empirical (X t ζ)) a - pair (withDensityReal ρ) a|) P ∧
            ∫ ζ, |pair (empirical (X t ζ)) a - pair (withDensityReal ρ) a| ∂P ≤
              C * A * Real.sqrt (deltaN d s N)) ∧
          (∀ (v : Euc d → Euc d) (Λ : ℝ≥0), LipschitzWith Λ v →
            Integrable (fun ζ => |commN d s v (X t ζ) (withDensityReal ρ)|) P ∧
            ∫ ζ, |commN d s v (X t ζ) (withDensityReal ρ)| ∂P ≤ C * Λ * deltaN d s N) :=
  @HRS.MS.PrepStat.euclidean_preparations_stationary_proof d s hd hs0 hsd M L b b₀ hb hb₀
```

# Proposition S5.3 · field remainder · The field remainder

%%%
tag := "headline-field-remainder"
%%%

:::theorem "headline-field-remainder-provider" (lean := "HRS.Whole.field_remainder")
Let $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d`, $`k\in\mathbb N`, $`k>\mathsf d/2+6`, $`J=2k+2\mathsf d+20`, and $`m>J+3\mathsf d+4`. Fix $`T\ge0`, $`\nu>0`, a real $`\mathsf d\times\mathsf d` matrix $`Q`, a nonnegative Schwartz probability density $`\rho`, and $`C_A\in\mathbb R`. Set $`V(x)=\tfrac12x\cdot Qx`. There is $`C_T\in\mathbb R`, depending only on these fixed data, such that the following holds for every $`N\ge2` and every particle process on a probability space with this potential and viscosity.
Assume, for every $`r\in[0,T]` and $`f\in C_b^2(\mathbb R^{\mathsf d})`, that $`|D_\mu(h_f)(X^r)|` is integrable and
$$`\mathbb E|D_\mu(h_f)(X^r)|\le C_A\delta_N\|D^2f\|_\infty.`
Then almost surely, simultaneously for every $`\alpha\in\mathbb N^{\mathsf d}` and $`t\in[0,T]`, the function $`r\mapsto B_\alpha(t,r)` is integrable on $`[0,t]`, and
$$`\mathbb E\sup_{0\le t\le T}\left\|\left(-\frac{\sqrt N}{2}\int_0^t B_\alpha(t,r)\,\mathrm dr\right)_\alpha\right\|_{\ell^2}\le[C_T\sqrt N\delta_N]_+.`
:::

## Notation and dynamics

Set $`\mu=\rho\,\mathrm dx`, $`\mu_N=N^{-1}\sum_{i=1}^N\delta_{x_i}`, and
$$`\mathsf g(x)=\begin{cases}-\log|x|,&\mathsf s=0,\\ |x|^{-\mathsf s},&\mathsf s>0,\end{cases}\qquad
\delta_N=\begin{cases}N^{-1},&\mathsf s<\mathsf d/2,\\N^{-1}\log(eN),&\mathsf s=\mathsf d/2,\\N^{1-\mathsf d/\mathsf s},&\mathsf s>\mathsf d/2.\end{cases}`
The particle diagonal is omitted. For a symmetric pair kernel $`h`, set
$$`D_\mu(h)(X_N)=\frac1{N^2}\sum_{i\ne j}h(x_i,x_j)-\frac2N\sum_i\int h(x_i,y)\,\mathrm d\mu(y)+\iint h(x,y)\,\mathrm d\mu(y)\,\mathrm d\mu(x).`
Write $`h_v(x,y)=(v(x)-v(y))\cdot\nabla\mathsf g(x-y)` and $`h_f=h_{\nabla f}`.

Set $`\lambda_\alpha=2|\alpha|+\mathsf d+1` and $`\phi_\alpha=\lambda_\alpha^{-m/2}h_\alpha`, $`\alpha\in\mathbb N^{\mathsf d}`, where $`h_\alpha(x)=\prod_i h_{\alpha_i}(x_i)` and
$$`h_n(x)=(n!\sqrt\pi)^{-1/2}\operatorname{He}_n(\sqrt2x)e^{-x^2/2}`
with the probabilists' Hermite polynomials $`\operatorname{He}_n`. For each terminal datum $`\phi`, $`U^{r,t}\phi` denotes a fixed classical solution at time $`r` of
$$`-\partial_r u=\mathcal Lu,\qquad u(t)=\phi,\qquad
\mathcal Lu=\nu\Delta u-(\nabla\mathsf g*\rho+\nabla V)\cdot\nabla u+\sum_{j=1}^{\mathsf d}\partial_j\mathsf g*(\rho\,\partial_j u).`
For a scalar density $`q`, the force convolution means
$$`\nabla\mathsf g*q(x)=\int\nabla\mathsf g(x-y)\left(\mathbf1_{|x-y|\le1/4}(q(y)-q(x))+\mathbf1_{|x-y|>1/4}q(y)\right)\,\mathrm dy.`
The classical solution class has continuous spatial derivatives through order two, uniformly bounded on $`[0,t]\times\mathbb R^{\mathsf d}`; the generator is continuous there and grows at most linearly in $`x`, uniformly in time. The backward equation holds for $`0<r<t`. If this class is empty, set $`U^{r,t}\phi=0`.

Write
$$`B_\alpha(t,r)=D_\mu(h_{U^{r,t}\phi_\alpha})(X^r),\qquad
\|(z_\alpha)_\alpha\|_{\ell^2}=\left(\sum_\alpha|z_\alpha|^2\right)^{1/2}\in[0,\infty].`
Here $`C_b^2` consists of twice continuously differentiable functions with the function and both derivatives bounded, and $`\|D^2f\|_\infty` is the supremum of the operator norm. Nonnegative expectations and variances in $`[0,\infty]` use the extended nonnegative integral; $`[u]_+=\max\{u,0\}`.

The particle process has continuous paths, measurable time marginals and no collisions almost surely throughout $`[0,T]`, and satisfies, with absolutely integrable drift,
$$`X_i^t=X_i^0-\int_0^t\left(\frac1N\sum_{j\ne i}\nabla\mathsf g(X_i^r-X_j^r)+\nabla V(X_i^r)\right)\,\mathrm dr+\sqrt{2\nu}\,(W_i^t-W_i^0).`
Here $`W` is a standard vector Brownian motion on the underlying probability space.

Exact Lean source: `HRS.Whole.field_remainder`.

```
theorem field_remainder (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : IsSchwartzDensity ρ) (CA : ℝ) :
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N), IsVectorBrownian P W →
      IsWholeStrongSolution P (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) T X₀ W X →
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
        Integrable (fun ζ => |centeredPairFunctional (commutatorKernel d s (fun x => gradient f x))
            (X (Real.toNNReal r) ζ) (withDensityReal ρ)|) P ∧
        ∫ ζ, |centeredPairFunctional (commutatorKernel d s (fun x => gradient f x))
            (X (Real.toNNReal r) ζ) (withDensityReal ρ)| ∂P ≤
          CA * deltaN d s N * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) →
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntegrableOn (fun r => commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
          s m (withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
              s m (withDensityReal ρ) X α t r ζ)) ∂P ≤
        ENNReal.ofReal (CT * Real.sqrt N * deltaN d s N) :=
  @HRS.MS.S53.field_remainder_proof d hd s hs0 hsd k hk m hm T ν hT hν Q ρ hρ CA
```

# Proposition S5.3 · centered field remainder · The centered field remainder

%%%
tag := "headline-field-remainder-centered"
%%%

:::theorem "headline-field-remainder-centered-provider" (lean := "HRS.Whole.field_remainder_centered")
Let $`\mathsf d\ge2`, $`0\le\mathsf s<\mathsf d`, $`k\in\mathbb N`, $`k>\mathsf d/2+6`, $`J=2k+2\mathsf d+20`, and $`m>J+3\mathsf d+4`. Fix $`T\ge0`, $`\nu>0`, a real $`\mathsf d\times\mathsf d` matrix $`Q`, a nonnegative Schwartz probability density $`\rho`, and $`C_A\in\mathbb R`. Set $`V(x)=\tfrac12x\cdot Qx`. There is $`C_T\in\mathbb R`, depending only on these fixed data, such that the following holds for every $`N\ge2` and every particle process on a probability space with this potential and viscosity.
Assume the time marginals are stationary, $`\operatorname{Law}(X^r)=\operatorname{Law}(X^0)` for every $`r\in[0,T]`, and for every $`f\in C_b^2(\mathbb R^{\mathsf d})`,
$$`N\operatorname{Var}\bigl(D_\mu(h_f)(X^0)\bigr)\le[C_A\delta_N\|D^2f\|_\infty^2]_+.`
Then almost surely, simultaneously for every $`\alpha\in\mathbb N^{\mathsf d}` and $`t\in[0,T]`, $`r\mapsto B_\alpha(t,r)` is integrable on $`[0,t]`, and
$$`\left(\mathbb E\left(\left[\sup_{0\le t\le T}\left\|\left(-\frac{\sqrt N}{2}\int_0^t\bigl(B_\alpha(t,r)-\mathbb E B_\alpha(t,r)\bigr)\,\mathrm dr\right)_\alpha\right\|_{\ell^2}\right]^2\right)\right)^{1/2}\le[C_T\sqrt{\delta_N}]_+.`
:::

## Notation and dynamics

Set $`\mu=\rho\,\mathrm dx`, $`\mu_N=N^{-1}\sum_{i=1}^N\delta_{x_i}`, and
$$`\mathsf g(x)=\begin{cases}-\log|x|,&\mathsf s=0,\\ |x|^{-\mathsf s},&\mathsf s>0,\end{cases}\qquad
\delta_N=\begin{cases}N^{-1},&\mathsf s<\mathsf d/2,\\N^{-1}\log(eN),&\mathsf s=\mathsf d/2,\\N^{1-\mathsf d/\mathsf s},&\mathsf s>\mathsf d/2.\end{cases}`
The particle diagonal is omitted. For a symmetric pair kernel $`h`, set
$$`D_\mu(h)(X_N)=\frac1{N^2}\sum_{i\ne j}h(x_i,x_j)-\frac2N\sum_i\int h(x_i,y)\,\mathrm d\mu(y)+\iint h(x,y)\,\mathrm d\mu(y)\,\mathrm d\mu(x).`
Write $`h_v(x,y)=(v(x)-v(y))\cdot\nabla\mathsf g(x-y)` and $`h_f=h_{\nabla f}`.

Set $`\lambda_\alpha=2|\alpha|+\mathsf d+1` and $`\phi_\alpha=\lambda_\alpha^{-m/2}h_\alpha`, $`\alpha\in\mathbb N^{\mathsf d}`, where $`h_\alpha(x)=\prod_i h_{\alpha_i}(x_i)` and
$$`h_n(x)=(n!\sqrt\pi)^{-1/2}\operatorname{He}_n(\sqrt2x)e^{-x^2/2}`
with the probabilists' Hermite polynomials $`\operatorname{He}_n`. For each terminal datum $`\phi`, $`U^{r,t}\phi` denotes a fixed classical solution at time $`r` of
$$`-\partial_r u=\mathcal Lu,\qquad u(t)=\phi,\qquad
\mathcal Lu=\nu\Delta u-(\nabla\mathsf g*\rho+\nabla V)\cdot\nabla u+\sum_{j=1}^{\mathsf d}\partial_j\mathsf g*(\rho\,\partial_j u).`
For a scalar density $`q`, the force convolution means
$$`\nabla\mathsf g*q(x)=\int\nabla\mathsf g(x-y)\left(\mathbf1_{|x-y|\le1/4}(q(y)-q(x))+\mathbf1_{|x-y|>1/4}q(y)\right)\,\mathrm dy.`
The classical solution class has continuous spatial derivatives through order two, uniformly bounded on $`[0,t]\times\mathbb R^{\mathsf d}`; the generator is continuous there and grows at most linearly in $`x`, uniformly in time. The backward equation holds for $`0<r<t`. If this class is empty, set $`U^{r,t}\phi=0`.

Write
$$`B_\alpha(t,r)=D_\mu(h_{U^{r,t}\phi_\alpha})(X^r),\qquad
\|(z_\alpha)_\alpha\|_{\ell^2}=\left(\sum_\alpha|z_\alpha|^2\right)^{1/2}\in[0,\infty].`
Here $`C_b^2` consists of twice continuously differentiable functions with the function and both derivatives bounded, and $`\|D^2f\|_\infty` is the supremum of the operator norm. Nonnegative expectations and variances in $`[0,\infty]` use the extended nonnegative integral; $`[u]_+=\max\{u,0\}`.

The particle process has continuous paths, measurable time marginals and no collisions almost surely throughout $`[0,T]`, and satisfies, with absolutely integrable drift,
$$`X_i^t=X_i^0-\int_0^t\left(\frac1N\sum_{j\ne i}\nabla\mathsf g(X_i^r-X_j^r)+\nabla V(X_i^r)\right)\,\mathrm dr+\sqrt{2\nu}\,(W_i^t-W_i^0).`
Here $`W` is a standard vector Brownian motion on the underlying probability space.

Exact Lean source: `HRS.Whole.field_remainder_centered`.

```
theorem field_remainder_centered (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : IsSchwartzDensity ρ) (CA : ℝ) :
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N), IsVectorBrownian P W →
      IsWholeStrongSolution P (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) T X₀ W X →
      (∀ t ∈ Set.Icc (0 : ℝ) T, law P (X (Real.toNNReal t)) = law P (X 0)) →
      (∀ f : Euc d → ℝ, MemCb 2 f →
        N * evariance (fun ζ => centeredPairFunctional
            (commutatorKernel d s (fun x => gradient f x)) (X 0 ζ) (withDensityReal ρ)) P ≤
          ENNReal.ofReal (CA * deltaN d s N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2)) →
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntegrableOn (fun r => commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
          s m (withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
      (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            (commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
                s m (withDensityReal ρ) X α t r ζ -
              ∫ ζ', commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
                s m (withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (CT * Real.sqrt (deltaN d s N)) :=
  @HRS.MS.S53.field_remainder_centered_proof d hd s hs0 hsd k hk m hm T ν hT hν Q ρ hρ CA
```

# Theorem S5.6 · Path comparison at varying temperature

%%%
tag := "headline-general-paths"
%%%

:::theorem "headline-general-paths-provider" (lean := "HRS.Whole.general_paths")
Fix a valid set of whole-space bounds in dimension $`\mathsf d\ge2`, with $`0\le\mathsf s<\mathsf d`, time $`T>0` and symmetric confinement matrix $`Q`. There is a threshold for the completion constant $`C_0`. For each $`C_0` at least this threshold, keeping all other bounds fixed, there is $`C>0` uniform over the associated mean-field setups and $`N\ge2`.

Let $`\rho_N^t` solve the mean-field equation with $`V(x)=x^\top Qx/2+c\cdot x`, interaction matrix $`M` and diffusivity $`\nu_N\in[0,\nu_*]`. Write $`\mu_N^t` for the empirical measure of a strong particle solution on $`[0,T]`. Assume there is a filtration for which the coordinate driving process is Brownian and the particles are adapted and progressively measurable. Couple the initial configuration and a random initial functional $`\eta_0` independently of the Brownian motion. Suppose the expected empirical and mean-field second moments are bounded by $`[M_2]_+` on $`[0,T]`. Assume the oscillator adjoint identity and feature condition stated below.

For the initial scale $`\kappa_N>0`, set $`\sigma_N=\min(\kappa_N,\sqrt{N/\nu_N})` when $`\nu_N>0`, and $`\sigma_N=\kappa_N` when $`\nu_N=0`. Set $`a_N=\sigma_N/\kappa_N`, $`q_N=\sigma_N^2\nu_N/N`. Compare $`\Xi_N^t=\sigma_N(\mu_N^t-\rho_N^t\,dx)` with any linear fluctuation solution $`Y_N` on the same probability space with initial field $`a_N\eta_0`, coefficients along $`\rho_N` and noise parameter $`q_N`. The paths in $`C([0,T];B_m)` are almost everywhere measurable. Their laws satisfy
$$`[d_2(\Xi_N,Y_N)]_+\le C\bigl(a_N\epsilon_{N,1}+\sigma_N E_{N,1}+[q_N w_N]_+\bigr),`
$$`W_1(\Xi_N,Y_N)\le C\bigl(a_N\epsilon_{N,1}+\sigma_N E_{N,1}+\sqrt{q_N w_N}\bigr),`
$$`W_2(\Xi_N,Y_N)\le C\bigl(a_N\epsilon_{N,2}+\sigma_N E_{N,2}+\sqrt{q_N w_N}\bigr).`
Here $`E_{N,p}=\sup_{0\le t\le T}\|\mathsf F_N^{\mathsf g}(X_N^t,\rho_N^t\,dx)+o_N\|_{L^p}`, and $`\epsilon_{N,p}` is the $`L^p` norm of the supremum in $`t` of the $`\ell^2` norm of the initial field error $`\kappa_N(\mu_N^0-\rho_N^0\,dx)-\eta_0` evaluated on the adjoint-propagated oscillator basis. Set
$$`w_N=\inf_{R\ge1}\left\{R^{\mathsf d/2}(N^{-1/\mathsf d}+\sqrt{E_{N,1}^{\mathrm r}})+(1+M_2)R^{-2}\right\}.`
The bounds use extended nonnegative reals. $`E_{N,1}^{\mathrm r}` is the real value of $`E_{N,1}` when finite and $`0` at infinity; the square root is the nonnegative square root of the positive part.
:::

## Notation and hypotheses

Fix a smooth compactly supported cutoff $`\theta` equal to one on $`[-2,2]^{\mathsf d}`, and fix $`M,Q,c,k,m,\nu_*,\Lambda,K,L`. Assume $`k\in\mathbb N`, $`k>\mathsf d/2+8`, $`J=4k+4\mathsf d+40`, $`m>J+3\mathsf d+4` and $`L>3\mathsf d+3k+2\mathsf s+30`. Assume $`0\le\nu_N\le\nu_*` and that $`\rho_N^t` has continuous derivatives through order $`k+6+\lceil\mathsf d/2\rceil` with weighted suprema at weight $`\langle x\rangle^L` bounded by $`[\Lambda]_+`. The completed energy is nonnegative off collisions on $`[0,T]`. If $`\mathsf s\ge\mathsf d-1`, assume $`|c_{\mathsf d,\mathsf s}^{-1}(\nabla\mathsf g*\rho_N^t)(x)|\le\Lambda` for every $`N,t,x` in this range, where $`c_{\mathsf d,\mathsf s}=2^{\mathsf d-\mathsf s}\pi^{\mathsf d/2}\Gamma((\mathsf d-\mathsf s)/2)/\Gamma(\mathsf s/2)`.

For each $`N`, assume either $`\mathsf s\le\mathsf d-2` or, when $`\mathsf s>\mathsf d-2`, at least one of the following: $`M+M^\top=0`; $`\mathsf s\le\mathsf d-1` and $`M+M^\top\preceq0`; $`\nu_N>0`; or $`M=-\lambda I+A` with $`\lambda\ge0` and $`A^\top=-A`.

Set $`j=k+1`, $`\ell=j+1+\lceil\mathsf d/2\rceil` and $`\|f\|_{H^\ell_{\rm ul}}=\sup_{z\in\mathbb Z^{\mathsf d}}\|\theta(\cdot-z)f\|_{H^\ell}`. For every $`0\le r\le t\le T` and every $`C^\ell` terminal datum $`f` with finite uniformly local norm, assume a classical adjoint solution exists and $`\|U(r,t)f\|_{C_b^j}\le K\|f\|_{H^\ell_{\rm ul}}`. The coefficients have diffusivity $`\nu_N`, density $`\rho_N` and drift $`M(\nabla\mathsf g*\rho_N)-\nabla V`.

For each Hermite test $`\phi_\alpha=\lambda_\alpha^{-m/2}h_\alpha`, each coordinate derivative $`D`, point $`x` and $`0\le r\le t\le T`, assume
$$`DU(r,t)\phi_\alpha(x)-D\phi_\alpha(x)=\int_r^t DU(r,u)(\mathcal L_u\phi_\alpha)(x)\,\mathrm du,`
with integrable right-hand side; $`\mathcal L_u` is the linearized generator at time $`u`. The sequence $`(D\phi_\alpha(x))_\alpha` belongs to $`\ell^2`. The sequence $`z_u=(DU(r,u)(\mathcal L_u\phi_\alpha)(x))_\alpha` belongs to $`\ell^2` for each $`r<u\le T`, and $`u\mapsto\mathbf1_{\{u>r\}}z_u` belongs to $`L^2([0,T];\ell^2)`.

Exact Lean source: `HRS.Whole.general_paths`.

```
theorem general_paths (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ S : WholeSetup b, ∀ (N : ℕ), 2 ≤ N →
      OscAdjointInput (S.coeff N) b.m b.T → ∀ (M₂ : ℝ)
      {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)), IsVectorBrownian P W →
      ∀ X : ℝ≥0 → Ω → EucConfig d N, IsWholeStrongSolution P (S.dyn N) b.T X₀ W X →
      (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
        IsWholeFilteredSolution P ℱ W' W X) →
      ∀ η₀ : Ω → (Euc d → ℝ) → ℝ,
      IndepFun (fun ζ => (X₀ ζ, η₀ ζ)) (fun ζ t => W t ζ) P →
      (∀ t ∈ Set.Icc (0 : ℝ) b.T,
        ∫⁻ ζ, ENNReal.ofReal (pair (empirical (X (Real.toNNReal t) ζ)) (fun x => ‖x‖ ^ 2)) ∂P ≤
          ENNReal.ofReal M₂ ∧
        ENNReal.ofReal (pair (withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
          ENNReal.ofReal M₂) →
      ∀ Y : ℝ → Ω → OscDual d b.m,
      IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y →
      AEMeasurable (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)) P ∧
      AEMeasurable (processWindow b.m b.T 0 Y) P ∧
      ENNReal.ofReal (smoothDist 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (S.q N * generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ∧
      wassersteinE 1 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (Real.sqrt (S.q N * generalLocalizationRate d
            (S.energyMomentE N 1 P X).toReal M₂ N))) ∧
      wassersteinE 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 2 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 2 P X +
          ENNReal.ofReal (Real.sqrt (S.q N * generalLocalizationRate d
            (S.energyMomentE N 1 P X).toReal M₂ N))) :=
  @HRS.MS.GenPath.general_paths_proof d b₀ hb
```
