import HRS.Commutator.Torus.Assembly
import HRS.Commutator.Torus.Bridge
import HRS.Commutator.Whole.Assembly
import HRS.Energy.Commutator.Assembly
import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "The sharp sub-Coulomb commutator" =>

%%%
tag := "commutator"
%%%

For $`0\le\mathsf{s}<\mathsf{d}-2`, the sharp commutator estimate combines the transport regularity $`|\nabla|^{(\mathsf{d}-\mathsf{s})/2}v\in L^{2\mathsf{d}/(\mathsf{d}-\mathsf{s}-2)}` with the correction $`\|\rho\|_\infty^{\mathsf{s}/\mathsf{d}}N^{\mathsf{s}/\mathsf{d}-1}`. The whole-space and periodic theorems allow real signed densities of mass one. The periodic specialization gives the sub-Coulomb commutator estimate in HRS.

# Whole-space argument

At unit scale, for bounded compactly supported densities, split the force into high and low frequencies, then split the transport in the low-frequency term. This gives three contributions: high-frequency force, low-frequency force with low-frequency transport, and low-frequency force with high-frequency transport. The last is a particle sum minus a background integral; estimate these separately and add the three bounds.

# Rescaling and density approximation

Rescaling gives the arbitrary-scale estimate. A common density approximation preserves mass and gives convergence of the density norms, energies and commutators. Passing to the limit removes the temporary boundedness and support assumptions. Finally, take $`p=\infty` and $`\eta=\lambda=(N\|\rho\|_\infty)^{-1/\mathsf{d}}`. The two error terms agree:

$$`\frac{\lambda^{-\mathsf{s}}}{N}=\|\rho\|_\infty\lambda^{\mathsf{d}-\mathsf{s}}=\|\rho\|_\infty^{\mathsf{s}/\mathsf{d}}N^{\mathsf{s}/\mathsf{d}-1}.`

The logarithmic renormalization remains $`-\log\lambda/(2N)` when $`\mathsf{s}=0`.

# Relation to the earlier sharp-error estimate

The sub-Coulomb note of 13 October 2026, Introduction and Theorem 1.1, compares this bound with the earlier estimate of Hess-Childs, Rosenzweig and Serfaty, which required

$$`\bigl\||\nabla|^{\mathsf{a}/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{a}-2)}},\qquad \mathsf{d}<\mathsf{a}<\mathsf{d}+2.`

The note obtains $`\mathsf{a}=\mathsf{d}-\mathsf{s}` with the same $`N^{\mathsf{s}/\mathsf{d}-1}` error.

# Periodic estimates

The periodic sharp theorem has the same density-dependent bound. Its kernel has singular part $`|x|^{-\mathsf{s}}` for $`\mathsf{s}>0`, whereas the whole-space kernel is $`\mathsf{s}^{-1}|x|^{-\mathsf{s}}`; both have logarithmic singularity $`-\log|x|` at $`\mathsf{s}=0`.

# The HRS application

For the HRS application, specialize to $`0\le\rho\le\Lambda`, $`\Lambda\ge1` and $`N\ge2`. The periodic embedding bounds the sharp transport seminorm by the higher-derivative seminorm in the application:

$$`\bigl\||\nabla|^{(\mathsf{d}-\mathsf{s})/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-\mathsf{s}-2)}}\le C_{\mathsf{d},\mathsf{s}}\bigl\||\nabla|^{(\mathsf{d}+1)/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-1)}}.`

Bounding $`\|\rho\|_\infty` by $`\Lambda` gives $`\mathsf{o}_N(\Lambda)`. Combining this specialization with the Lipschitz estimate for $`\mathsf{d}-2\le\mathsf{s}<\mathsf{d}` yields the all-regime result.

# Lean declarations and evidence

## Verification status

The whole-space and periodic sharp estimates have Lean proof terms. No separate Comparator verification record for either standalone sharp estimate is identified here.

The all-regime estimate `commutator_estimate_of_packets` and its identification with `HRS.commutator_estimate` have archived acceptance logs from nanoda and Lean’s default kernel. The recorded checks cover these two declarations.

The §6 argument uses `HRS.commutator_coercivity_common_proof`, which applies the all-regime estimate. The proof is supplied by the `_proof` declaration; the older `HRS.commutator_coercivity_common` declaration is separate.

## Scope of the exposition

The source links below contain the declarations and the analytic lemmas used in these proofs.

## Whole space · sharp-scale theorem
%%%
tag := "comm-lean-HRS.Commutator.Whole.subcoulomb_commutator"
%%%

:::theorem "comm-provider-1" (lean := "HRS.Commutator.Whole.subcoulomb_commutator")
Let $`\mathsf{d}\ge3` be an integer and $`0\le\mathsf{s}<\mathsf{d}-2`.

There are $`C,C_0>0`, depending only on $`\mathsf{d},\mathsf{s}`. Let $`\rho\in L^1(\mathbb R^{\mathsf{d}})\cap L^\infty(\mathbb R^{\mathsf{d}})` be real with $`\int\rho\,\mathrm{d}x=1`. Let $`N\ge1` be an integer and let $`X_N\in(\mathbb R^{\mathsf{d}})^N` be pairwise distinct.

When $`\mathsf{s}=0`, assume $`\iint \lvert\log\lvert x-y\rvert\rvert\,|\rho(x)\rho(y)|\,\mathrm{d}x\,\mathrm{d}y<\infty`.

For $`K\in\mathbb R`, let $`v:\mathbb R^{\mathsf{d}}\to\mathbb R^{\mathsf{d}}` be Lipschitz with

$$`\|\nabla v\|_\infty+\bigl\||\nabla|^{(\mathsf{d}-\mathsf{s})/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-\mathsf{s}-2)}}\le K.`

For $`\lambda=(N\|\rho\|_\infty)^{-1/\mathsf{d}}`,

$$`|\mathsf{A}_1[X_N,\rho,v]|\le CK\left(\mathsf{F}_N(X_N,\rho)-\mathbf1_{\{\mathsf{s}=0\}}\frac{\log\lambda}{2N}+C_0\|\rho\|_\infty\lambda^{\mathsf{d}-\mathsf{s}}\right).`

The quantity in parentheses is nonnegative. The mixed and background integrals defining $`\mathsf{F}_N` and $`\mathsf{A}_1` converge absolutely.

The whole-space kernel is $`\mathsf{g}(x)=\mathsf{s}^{-1}|x|^{-\mathsf{s}}` for $`\mathsf{s}>0` and $`\mathsf{g}(x)=-\log|x|` for $`\mathsf{s}=0`.

Set $`\nu=N^{-1}\sum_{i=1}^N\delta_{x_i}-\rho\,\mathrm{d}x`. The energy and first transport commutator are

$$`\mathsf{F}_N(X_N,\rho)=\frac12\iint_{x\ne y}\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y),\qquad
\mathsf{A}_1[X_N,\rho,v]=\iint_{x\ne y}(v(x)-v(y))\cdot\nabla\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y).`

The integrals expand into the particle sum with $`i=j` omitted, the mixed terms and the background term. All vector norms are Euclidean.

In the transport bound, $`\|\nabla v\|_\infty` denotes the Lipschitz seminorm. The componentwise distributional derivative $`|\nabla|^a v` has multiplier $`(2\pi|\xi|)^a` for the Fourier convention $`e^{-2\pi i x\cdot\xi}`. Each fractional-derivative norm is the norm of a representative satisfying the distributional identity with absolutely convergent pairings against every complex Schwartz test function.
:::

*Verification:* Lean proof term available.

Source: [`HRS/Commutator/Whole/Assembly.lean`](source/HRS/Commutator/Whole/Assembly.lean).

Declaration type, as written:

```
theorem subcoulomb_commutator (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ ∀ ρ : Euc d → ℝ, Integrable ρ → MemLp ρ ⊤ volume →
      ∫ x, ρ x = 1 → (s = 0 → LogIntegrable ρ) →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
        EnergyIntegrable s X ρ ∧ CommIntegrable s X ρ v ∧
        0 ≤ modEnergy s X ρ - (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
              C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s) ∧
        |commA s X ρ v| ≤ C * K *
          (modEnergy s X ρ - (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
            C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s))
```

Inspected Lean proof body:

```
by
  obtain ⟨C, hC, S⟩ := subcoulomb_commutator_scale hd hs0 hsd
  obtain ⟨Cp, hCp, S'⟩ := S ⊤ (by simp)
  refine ⟨C, 2 * Cp, hC, by positivity, fun ρ h1 hinf hmass hlog v K hv N X hN hX => ?_⟩
  have hM := normE_top_pos ρ h1 hinf hmass
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNM : 0 < (N : ℝ) * normE ⊤ ρ := mul_pos hNpos hM
  have hlam : 0 < lamN d N ρ := Real.rpow_pos_of_pos hNM _
  have hlamd : lamN d N ρ ^ (d : ℝ) = ((N : ℝ) * normE ⊤ ρ)⁻¹ := by
    unfold lamN
    rw [← Real.rpow_mul hNM.le, show (-(1 : ℝ) / d) * d = -1 by field_simp, Real.rpow_neg_one]
  have hkey : lamN d N ρ ^ (-s) / (N : ℝ) = normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, hlamd]
    field_simp
  obtain ⟨hE, hCI, hQ, hA⟩ := S' ρ h1 hinf hmass hlog v K hv N X hN hX (lamN d N ρ) hlam
  have hQe : scaleQ s Cp ⊤ (lamN d N ρ) X ρ =
      modEnergy s X ρ - (if s = 0 then Real.log (lamN d N ρ) / (2 * (N : ℝ)) else 0) +
        2 * Cp * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s) := by
    unfold scaleQ
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, mul_one]
    rw [hkey]
    ring
  rw [hQe] at hQ hA
  exact ⟨hE, hCI, hQ, hA⟩
```

## Whole space · arbitrary-scale theorem
%%%
tag := "comm-lean-HRS.Commutator.Whole.subcoulomb_commutator_scale"
%%%

:::theorem "comm-provider-2" (lean := "HRS.Commutator.Whole.subcoulomb_commutator_scale")
Let $`\mathsf{d}\ge3` be an integer and $`0\le\mathsf{s}<\mathsf{d}-2`.

There is $`C=C(\mathsf{d},\mathsf{s})>0` such that, for each $`\mathsf{d}/(\mathsf{d}-\mathsf{s})<p\le\infty`, there is $`C_p=C_p(\mathsf{d},\mathsf{s},p)>0`. Let $`\rho\in L^1(\mathbb R^{\mathsf{d}})\cap L^p(\mathbb R^{\mathsf{d}})` be real with $`\int\rho\,\mathrm{d}x=1`, let $`N\ge1` be an integer and let $`X_N\in(\mathbb R^{\mathsf{d}})^N` be pairwise distinct.

When $`\mathsf{s}=0`, assume $`\iint \lvert\log\lvert x-y\rvert\rvert\,|\rho(x)\rho(y)|\,\mathrm{d}x\,\mathrm{d}y<\infty`.

For $`K\in\mathbb R`, let $`v:\mathbb R^{\mathsf{d}}\to\mathbb R^{\mathsf{d}}` be Lipschitz with

$$`\|\nabla v\|_\infty+\bigl\||\nabla|^{(\mathsf{d}-\mathsf{s})/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-\mathsf{s}-2)}}\le K.`

For every $`\eta>0`,

$$`|\mathsf{A}_1[X_N,\rho,v]|\le CK\left(\mathsf{F}_N(X_N,\rho)-\mathbf1_{\{\mathsf{s}=0\}}\frac{\log\eta}{2N}+C_p\left(\frac{\eta^{-\mathsf{s}}}{N}+\|\rho\|_p\eta^{\mathsf{d}(1-1/p)-\mathsf{s}}\right)\right).`

The quantity in parentheses is nonnegative, and the mixed and background integrals defining $`\mathsf{F}_N` and $`\mathsf{A}_1` converge absolutely. Here $`1/p=0` for $`p=\infty`; $`C` is uniform in $`p`, and both constants are independent of $`\rho,v,K,N,X_N,\eta`.

The whole-space kernel is $`\mathsf{g}(x)=\mathsf{s}^{-1}|x|^{-\mathsf{s}}` for $`\mathsf{s}>0` and $`\mathsf{g}(x)=-\log|x|` for $`\mathsf{s}=0`.

Set $`\nu=N^{-1}\sum_{i=1}^N\delta_{x_i}-\rho\,\mathrm{d}x`. The energy and first transport commutator are

$$`\mathsf{F}_N(X_N,\rho)=\frac12\iint_{x\ne y}\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y),\qquad
\mathsf{A}_1[X_N,\rho,v]=\iint_{x\ne y}(v(x)-v(y))\cdot\nabla\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y).`

The integrals expand into the particle sum with $`i=j` omitted, the mixed terms and the background term. All vector norms are Euclidean.

In the transport bound, $`\|\nabla v\|_\infty` denotes the Lipschitz seminorm. The componentwise distributional derivative $`|\nabla|^a v` has multiplier $`(2\pi|\xi|)^a` for the Fourier convention $`e^{-2\pi i x\cdot\xi}`. Each fractional-derivative norm is the norm of a representative satisfying the distributional identity with absolutely convergent pairings against every complex Schwartz test function.
:::

*Verification:* Lean proof term available.

Source: [`HRS/Commutator/Whole/Assembly.lean`](source/HRS/Commutator/Whole/Assembly.lean).

Declaration type, as written:

```
theorem subcoulomb_commutator_scale (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp : ℝ, 0 < Cp ∧ ∀ ρ : Euc d → ℝ, Integrable ρ → MemLp ρ p volume → ∫ x, ρ x = 1 →
      (s = 0 → LogIntegrable ρ) →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X → ∀ η : ℝ, 0 < η →
        EnergyIntegrable s X ρ ∧ CommIntegrable s X ρ v ∧
        0 ≤ scaleQ s Cp p η X ρ ∧ |commA s X ρ v| ≤ C * K * scaleQ s Cp p η X ρ
```

Inspected Lean proof body:

```
by
  obtain ⟨C, hC, S⟩ := scale_estimate hd hs0 hsd
  refine ⟨C, hC, fun p hp => ?_⟩
  obtain ⟨Cp, hCp, S'⟩ := S p hp
  refine ⟨Cp, hCp, fun ρ h1 hpρ hmass hlog v K hv N X hN hX η hη => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, LipschitzWith L v := by
    obtain ⟨L, F, -, hL, -, -⟩ := hv
    exact ⟨L, hL⟩
  obtain ⟨hE, hCI⟩ := integrable_of_Lp hd hs0 hsd p hp ρ h1 hpρ hlog v L hL X
  obtain ⟨ρm, hbdd, hnorm, hlim⟩ := density_approx hd hs0 hsd p hp ρ h1 hpρ hmass hlog
  obtain ⟨hF, hA⟩ := hlim N X v L hL
  have hm := fun m => S' (ρm m) (hbdd m) N X hN hX v K hv η hη
  have hQ : Tendsto (fun m => scaleQ s Cp p η X (ρm m)) atTop (𝓝 (scaleQ s Cp p η X ρ)) := by
    unfold scaleQ
    exact (hF.sub tendsto_const_nhds).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.add (hnorm.mul tendsto_const_nhds)))
  refine ⟨hE, hCI, ge_of_tendsto hQ (Eventually.of_forall fun m => (hm m).1), ?_⟩
  exact le_of_tendsto_of_tendsto hA.abs (tendsto_const_nhds.mul hQ)
    (Eventually.of_forall fun m => (hm m).2)
```

## Torus · sharp-scale theorem
%%%
tag := "comm-lean-HRS.Commutator.TorusNote.torus_subcoulomb_commutator"
%%%

:::theorem "comm-provider-3" (lean := "HRS.Commutator.TorusNote.torus_subcoulomb_commutator")
Let $`\mathsf{d}\ge3` be an integer and $`0\le\mathsf{s}<\mathsf{d}-2`.

There are $`C,C_0>0`, depending only on $`\mathsf{d},\mathsf{s}`. Let $`\rho\in L^1(\mathbb T^{\mathsf{d}})\cap L^\infty(\mathbb T^{\mathsf{d}})` be real with $`\int\rho\,\mathrm{d}x=1`. Let $`N\ge1` be an integer and let $`X_N\in(\mathbb T^{\mathsf{d}})^N` be pairwise distinct.

For $`K\in\mathbb R`, let $`v:\mathbb T^{\mathsf{d}}\to\mathbb R^{\mathsf{d}}` be Lipschitz with

$$`\|\nabla v\|_\infty+\bigl\||\nabla|^{(\mathsf{d}-\mathsf{s})/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-\mathsf{s}-2)}}\le K.`

For $`\lambda=(N\|\rho\|_\infty)^{-1/\mathsf{d}}`,

$$`|\mathsf{A}_1[X_N,\rho,v]|\le CK\left(\mathsf{F}_N(X_N,\rho)-\mathbf1_{\{\mathsf{s}=0\}}\frac{\log\lambda}{2N}+C_0\|\rho\|_\infty\lambda^{\mathsf{d}-\mathsf{s}}\right).`

The quantity in parentheses is nonnegative. The mixed and background integrals defining $`\mathsf{F}_N` and $`\mathsf{A}_1` converge absolutely.

The torus is $`\mathbb T^{\mathsf{d}}=(\mathbb R/\mathbb Z)^{\mathsf{d}}`, with unit-volume Haar measure. The mean-zero periodic kernel has coefficients

$$`\widehat{\mathsf{g}}(0)=0,\qquad \widehat{\mathsf{g}}(k)=\mathsf{c}_{\mathsf{d},\mathsf{s}}(2\pi|k|)^{\mathsf{s}-\mathsf{d}}\quad(k\ne0),`

where

$$`\mathsf{c}_{\mathsf{d},\mathsf{s}}=\begin{cases}2^{\mathsf{d}-\mathsf{s}}\pi^{\mathsf{d}/2}\Gamma((\mathsf{d}-\mathsf{s})/2)/\Gamma(\mathsf{s}/2),&\mathsf{s}>0,\\2^{\mathsf{d}-1}\pi^{\mathsf{d}/2}\Gamma(\mathsf{d}/2),&\mathsf{s}=0.\end{cases}`

The kernel and its gradient are the heat-regularized limits. Their singular normalization is $`|x|^{-\mathsf{s}}` for $`\mathsf{s}>0` and $`-\log|x|` for $`\mathsf{s}=0`.

Set $`\nu=N^{-1}\sum_{i=1}^N\delta_{x_i}-\rho\,\mathrm{d}x`. The energy and first transport commutator are

$$`\mathsf{F}_N(X_N,\rho)=\frac12\iint_{x\ne y}\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y),\qquad
\mathsf{A}_1[X_N,\rho,v]=\iint_{x\ne y}(v(x)-v(y))\cdot\nabla\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y).`

The integrals expand into the particle sum with $`i=j` omitted, the mixed terms and the background term. All vector norms are Euclidean.

In the transport bound, $`\|\nabla v\|_\infty` is the Lipschitz seminorm for the quotient Euclidean distance. Each fractional-derivative norm is the norm of a representative $`w=|\nabla|^a v` satisfying

$$`\widehat w_j(k)=(2\pi|k|)^a\widehat v_j(k)\quad(j=1,\ldots,\mathsf{d},\ k\in\mathbb Z^{\mathsf{d}}),`

with Fourier convention $`e^{-2\pi i k\cdot x}`, including $`k=0`.
:::

*Verification:* Lean proof term available; used in the verified all-regime estimate.

Source: [`HRS/Commutator/Torus/Assembly.lean`](source/HRS/Commutator/Torus/Assembly.lean).

Declaration type, as written:

```
theorem torus_subcoulomb_commutator (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 < C₀ ∧ ∀ ρ : Torus d → ℝ, Integrable ρ → MemLp ρ ⊤ volume →
      ∫ x, ρ x = 1 → ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
        EnergyIntegrableT s X ρ ∧ CommIntegrableT s X ρ v ∧
        0 ≤ modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
              C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ∧
        |commAT s X ρ v| ≤ C * K *
          (modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
            C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s))
```

Inspected Lean proof body:

```
by
  obtain ⟨C, hC, S⟩ := subcoulomb_commutator_scale_T hd hs0 hsd
  obtain ⟨Cp, hCp, S'⟩ := S ⊤ (by simp)
  refine ⟨C, 2 * Cp, hC, by positivity, fun ρ h1 hinf hmass v K hv N X hN hX => ?_⟩
  have hM1 := normT_top_ge_one ρ h1 hinf hmass
  have hM : 0 < normT ⊤ ρ := lt_of_lt_of_le one_pos hM1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNM : 0 < (N : ℝ) * normT ⊤ ρ := mul_pos hNpos hM
  have hlam : 0 < lamT d N ρ := Real.rpow_pos_of_pos hNM _
  have hNM1 : 1 ≤ (N : ℝ) * normT ⊤ ρ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlam1 : lamT d N ρ ≤ 1 := by
    unfold lamT
    exact Real.rpow_le_one_of_one_le_of_nonpos hNM1 (by
      have : (0 : ℝ) < d := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have : (0 : ℝ) ≤ 1 / d := by positivity
      rw [neg_div]; linarith)
  have hlamd : lamT d N ρ ^ (d : ℝ) = ((N : ℝ) * normT ⊤ ρ)⁻¹ := by
    unfold lamT
    rw [← Real.rpow_mul hNM.le, show (-(1 : ℝ) / d) * d = -1 by field_simp, Real.rpow_neg_one]
  have hkey : lamT d N ρ ^ (-s) / (N : ℝ) = normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, hlamd]
    field_simp
  obtain ⟨hE, hCI, hQ, hA⟩ := S' ρ h1 hinf hmass v K hv N X hN hX (lamT d N ρ) hlam hlam1
  have hQe : scaleQT s Cp ⊤ (lamT d N ρ) X ρ =
      modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
        2 * Cp * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) := by
    unfold scaleQT
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, sub_zero, mul_one]
    rw [hkey]
    ring
  rw [hQe] at hQ hA
  exact ⟨hE, hCI, hQ, hA⟩
```

## Torus · application specialization
%%%
tag := "comm-lean-HRS.Commutator.TorusNote.commutator_estimate_sub_of_torus"
%%%

:::theorem "comm-provider-4" (lean := "HRS.Commutator.TorusNote.commutator_estimate_sub_of_torus")
Let $`\mathsf{d}\ge3` be an integer and $`0\le\mathsf{s}<\mathsf{d}-2`.

There are $`C_0\ge0` and $`C>0`, depending only on $`\mathsf{d},\mathsf{s}`.

Let $`\Lambda\ge1` and let $`N\ge2` be an integer. Let $`\rho` be a measurable real density on $`\mathbb T^{\mathsf{d}}` with $`0\le\rho(x)\le\Lambda` for every $`x` and $`\int\rho\,\mathrm{d}x=1`. Let $`X_N\in(\mathbb T^{\mathsf{d}})^N` be pairwise distinct.

Let $`v:\mathbb T^{\mathsf{d}}\to\mathbb R^{\mathsf{d}}` be Lipschitz, and let $`L,F\ge0` satisfy

$$`\|\nabla v\|_\infty\le L,\qquad \bigl\||\nabla|^{(\mathsf{d}+1)/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-1)}}\le F.`

Set

$$`\mathsf{o}_N(\Lambda)=\mathbf1_{\{\mathsf{s}=0\}}\frac{\log(N\Lambda)}{2\mathsf{d}N}+C_0\Lambda^{\mathsf{s}/\mathsf{d}}N^{\mathsf{s}/\mathsf{d}-1}.`

Then

$$`|\mathsf{A}_1[X_N,\rho,v]|\le C(L+F)\bigl(\mathsf{F}_N(X_N,\rho)+\mathsf{o}_N(\Lambda)\bigr).`

The torus is $`\mathbb T^{\mathsf{d}}=(\mathbb R/\mathbb Z)^{\mathsf{d}}`, with unit-volume Haar measure. The mean-zero periodic kernel has coefficients

$$`\widehat{\mathsf{g}}(0)=0,\qquad \widehat{\mathsf{g}}(k)=\mathsf{c}_{\mathsf{d},\mathsf{s}}(2\pi|k|)^{\mathsf{s}-\mathsf{d}}\quad(k\ne0),`

where

$$`\mathsf{c}_{\mathsf{d},\mathsf{s}}=\begin{cases}2^{\mathsf{d}-\mathsf{s}}\pi^{\mathsf{d}/2}\Gamma((\mathsf{d}-\mathsf{s})/2)/\Gamma(\mathsf{s}/2),&\mathsf{s}>0,\\2^{\mathsf{d}-1}\pi^{\mathsf{d}/2}\Gamma(\mathsf{d}/2),&\mathsf{s}=0.\end{cases}`

The kernel and its gradient are the heat-regularized limits. Their singular normalization is $`|x|^{-\mathsf{s}}` for $`\mathsf{s}>0` and $`-\log|x|` for $`\mathsf{s}=0`.

Set $`\nu=N^{-1}\sum_{i=1}^N\delta_{x_i}-\rho\,\mathrm{d}x`. The energy and first transport commutator are

$$`\mathsf{F}_N(X_N,\rho)=\frac12\iint_{x\ne y}\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y),\qquad
\mathsf{A}_1[X_N,\rho,v]=\iint_{x\ne y}(v(x)-v(y))\cdot\nabla\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y).`

The integrals expand into the particle sum with $`i=j` omitted, the mixed terms and the background term. All vector norms are Euclidean.

In the transport bound, $`\|\nabla v\|_\infty` is the Lipschitz seminorm for the quotient Euclidean distance. Each fractional-derivative norm is the norm of a representative $`w=|\nabla|^a v` satisfying

$$`\widehat w_j(k)=(2\pi|k|)^a\widehat v_j(k)\quad(j=1,\ldots,\mathsf{d},\ k\in\mathbb Z^{\mathsf{d}}),`

with Fourier convention $`e^{-2\pi i k\cdot x}`, including $`k=0`.
:::

*Verification:* Lean proof term available.

Source: [`HRS/Commutator/Torus/Bridge.lean`](source/HRS/Commutator/Torus/Bridge.lean).

Declaration type, as written:

```
theorem commutator_estimate_sub_of_torus (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L F : ℝ) (v : Torus d → Euc d), 0 ≤ L → 0 ≤ F → IsLipschitzVF L v → HasFracBound d v F →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)
```

Inspected Lean proof body:

```
by
  obtain ⟨C, C₀, hC, hC₀, H⟩ := torus_subcoulomb_commutator hd hs0 hs
  obtain ⟨Ce, hCe, E⟩ := embedding_T hd hs0 hs
  refine ⟨C₀, C * max 1 Ce, hC₀.le, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hΛρ X hX L F v hL hF hLip hfrac
  have h1 : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hinf : MemLp ρ ⊤ volume :=
    memLp_top_of_bound h1.aestronglyMeasurable |Λ| (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact le_trans (hΛρ x) (le_abs_self Λ))
  obtain ⟨w, hw, hwn⟩ := E v F hF hfrac
  have hv' : TorusSubTransport d s v (L + Ce * F) :=
    ⟨L, Ce * F, hL, by positivity, hLip, ⟨w, hw, hwn⟩, le_refl _⟩
  obtain ⟨-, -, hQ, hA⟩ := H ρ h1 hinf hρ.integral_one v _ hv' N X (by omega) hX
  rw [commQuantity_eq_T ρ hρ X v, rieszEnergy_eq_T ρ hρ X]
  have hM1 := normT_top_ge_one ρ h1 hinf hρ.integral_one
  have hM : 0 < normT ⊤ ρ := lt_of_lt_of_le one_pos hM1
  have hMΛ := normT_top_le ρ hρ Λ hΛρ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hNM : 0 < (N : ℝ) * normT ⊤ ρ := mul_pos hNpos hM
  have hlam : 0 < lamT d N ρ := Real.rpow_pos_of_pos hNM _
  have hlamd : lamT d N ρ ^ (d : ℝ) = ((N : ℝ) * normT ⊤ ρ)⁻¹ := by
    unfold lamT
    rw [← Real.rpow_mul hNM.le, show (-(1 : ℝ) / d) * d = -1 by field_simp, Real.rpow_neg_one]
  have hlams : lamT d N ρ ^ (-s) = ((N : ℝ) * normT ⊤ ρ) ^ (s / d) := by
    unfold lamT
    rw [← Real.rpow_mul hNM.le]
    congr 1
    field_simp
  have hMl : normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
    rw [sub_eq_add_neg, Real.rpow_add hlam, hlamd, hlams, Real.mul_rpow hNpos.le hM.le]
    have e : normT ⊤ ρ * (((N : ℝ) * normT ⊤ ρ)⁻¹ * ((N : ℝ) ^ (s / d) * normT ⊤ ρ ^ (s / d))) =
        (N : ℝ) ^ (s / d - 1) * normT ⊤ ρ ^ (s / d) := by
      rw [Real.rpow_sub_one hNpos.ne']
      field_simp
    rw [e, mul_comm]
    gcongr
  have hlogterm : (if s = 0 then -(Real.log (lamT d N ρ) / (2 * (N : ℝ))) else 0) ≤
      (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) := by
    split_ifs with h0
    · have h2 : Real.log (lamT d N ρ) = (-(1 : ℝ) / d) * Real.log ((N : ℝ) * normT ⊤ ρ) := by
        unfold lamT; rw [Real.log_rpow hNM]
      rw [h2]
      have h3 : Real.log ((N : ℝ) * normT ⊤ ρ) ≤ Real.log ((N : ℝ) * Λ) :=
        Real.log_le_log hNM (mul_le_mul_of_nonneg_left hMΛ hNpos.le)
      have : -((-(1 : ℝ) / d * Real.log ((N : ℝ) * normT ⊤ ρ)) / (2 * (N : ℝ))) =
          Real.log ((N : ℝ) * normT ⊤ ρ) / (2 * d * N) := by field_simp
      rw [this]
      gcongr
    · exact le_rfl
  have hQle : modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
        C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ≤
      modEnergyT s X ρ + oNΛ d s C₀ Λ N := by
    unfold oNΛ
    have h5 : C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s) ≤ C₀ * Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
      calc C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)
          = C₀ * (normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)) := by ring
        _ ≤ C₀ * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by gcongr
        _ = _ := by ring
    have h7 : -(if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) ≤
        (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) := by
      split_ifs at hlogterm ⊢ with h0
      · simpa [neg_div] using hlogterm
      · simp
    linarith
  have hL1 : 0 ≤ L + Ce * F := by positivity
  calc |commAT s X ρ v| ≤ C * (L + Ce * F) *
        (modEnergyT s X ρ - (if s = 0 then Real.log (lamT d N ρ) / (2 * (N : ℝ)) else 0) +
          C₀ * normT ⊤ ρ * lamT d N ρ ^ ((d : ℝ) - s)) := hA
    _ ≤ C * (L + Ce * F) * (modEnergyT s X ρ + oNΛ d s C₀ Λ N) := by
        have : 0 ≤ C * (L + Ce * F) := by positivity
        exact mul_le_mul_of_nonneg_left hQle this
    _ ≤ C * max 1 Ce * (L + F) * (modEnergyT s X ρ + oNΛ d s C₀ Λ N) := by
        have hY : 0 ≤ modEnergyT s X ρ + oNΛ d s C₀ Λ N := le_trans hQ hQle
        have hineq : C * (L + Ce * F) ≤ C * max 1 Ce * (L + F) := by
          have : L + Ce * F ≤ max 1 Ce * (L + F) := by
            have h1' : 1 ≤ max 1 Ce := le_max_left _ _
            have h2' : Ce ≤ max 1 Ce := le_max_right _ _
            nlinarith [mul_nonneg hL (sub_nonneg.2 h1'), mul_nonneg hF (sub_nonneg.2 h2')]
          calc C * (L + Ce * F) ≤ C * (max 1 Ce * (L + F)) := mul_le_mul_of_nonneg_left this hC.le
            _ = _ := by ring
        exact mul_le_mul_of_nonneg_right hineq hY
```

## Main Proposition 3.32 · all-regime estimate
%%%
tag := "comm-lean-HRS.Commutator.commutator_estimate_of_packets"
%%%

:::theorem "comm-provider-5" (lean := "HRS.Commutator.commutator_estimate_of_packets")
Let $`\mathsf{d}\ge1` be an integer and $`0\le\mathsf{s}<\mathsf{d}`. There are $`C_0\ge0` and $`C>0`, depending only on $`\mathsf{d},\mathsf{s}`.

Let $`\Lambda\ge1` and let $`N\ge2` be an integer. Let $`\rho` be a measurable real density on $`\mathbb T^{\mathsf{d}}` with $`0\le\rho(x)\le\Lambda` for every $`x` and $`\int\rho\,\mathrm{d}x=1`. Let $`X_N\in(\mathbb T^{\mathsf{d}})^N` be pairwise distinct.

For $`K\in\mathbb R`, let $`v:\mathbb T^{\mathsf{d}}\to\mathbb R^{\mathsf{d}}` be Lipschitz and satisfy $`\|v\|_*\le K`, where

$$`\|v\|_*=\begin{cases}\|\nabla v\|_\infty+\bigl\||\nabla|^{(\mathsf{d}+1)/2}v\bigr\|_{L^{2\mathsf{d}/(\mathsf{d}-1)}},&\mathsf{s}<\mathsf{d}-2,\\\|\nabla v\|_\infty,&\mathsf{d}-2\le\mathsf{s}<\mathsf{d}.\end{cases}`

Set

$$`\mathsf{o}_N(\Lambda)=\mathbf1_{\{\mathsf{s}=0\}}\frac{\log(N\Lambda)}{2\mathsf{d}N}+C_0\Lambda^{\mathsf{s}/\mathsf{d}}N^{\mathsf{s}/\mathsf{d}-1}.`

Then the mixed and background commutator integrals converge absolutely, and

$$`|\mathsf{A}_1[X_N,\rho,v]|\le CK\bigl(\mathsf{F}_N(X_N,\rho)+\mathsf{o}_N(\Lambda)\bigr).`

The torus is $`\mathbb T^{\mathsf{d}}=(\mathbb R/\mathbb Z)^{\mathsf{d}}`, with unit-volume Haar measure. The mean-zero periodic kernel has coefficients

$$`\widehat{\mathsf{g}}(0)=0,\qquad \widehat{\mathsf{g}}(k)=\mathsf{c}_{\mathsf{d},\mathsf{s}}(2\pi|k|)^{\mathsf{s}-\mathsf{d}}\quad(k\ne0),`

where

$$`\mathsf{c}_{\mathsf{d},\mathsf{s}}=\begin{cases}2^{\mathsf{d}-\mathsf{s}}\pi^{\mathsf{d}/2}\Gamma((\mathsf{d}-\mathsf{s})/2)/\Gamma(\mathsf{s}/2),&\mathsf{s}>0,\\2^{\mathsf{d}-1}\pi^{\mathsf{d}/2}\Gamma(\mathsf{d}/2),&\mathsf{s}=0.\end{cases}`

The kernel and its gradient are the heat-regularized limits. Their singular normalization is $`|x|^{-\mathsf{s}}` for $`\mathsf{s}>0` and $`-\log|x|` for $`\mathsf{s}=0`.

Set $`\nu=N^{-1}\sum_{i=1}^N\delta_{x_i}-\rho\,\mathrm{d}x`. The energy and first transport commutator are

$$`\mathsf{F}_N(X_N,\rho)=\frac12\iint_{x\ne y}\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y),\qquad
\mathsf{A}_1[X_N,\rho,v]=\iint_{x\ne y}(v(x)-v(y))\cdot\nabla\mathsf{g}(x-y)\,\mathrm{d}\nu(x)\mathrm{d}\nu(y).`

The integrals expand into the particle sum with $`i=j` omitted, the mixed terms and the background term. All vector norms are Euclidean.

In the transport bound, $`\|\nabla v\|_\infty` is the Lipschitz seminorm for the quotient Euclidean distance. Each fractional-derivative norm is the norm of a representative $`w=|\nabla|^a v` satisfying

$$`\widehat w_j(k)=(2\pi|k|)^a\widehat v_j(k)\quad(j=1,\ldots,\mathsf{d},\ k\in\mathbb Z^{\mathsf{d}}),`

with Fourier convention $`e^{-2\pi i k\cdot x}`, including $`k=0`.
:::

*Verification:* Archived Comparator acceptance for this declaration.

Source: [`HRS/Energy/Commutator/Assembly.lean`](source/HRS/Energy/Commutator/Assembly.lean).

Declaration type, as written:

```
theorem commutator_estimate_of_packets (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
        OffDiagIntegrable (commKernel (periodicRieszGrad d s) v) X (withDensityReal ρ) ∧
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)
```

Inspected Lean proof body:

```
by
  obtain ⟨Cn, hCn, hnn⟩ := energy_add_oN_nonneg hd hs0 hsd
  by_cases hsub : s < (d : ℝ) - 2
  · -- fractional regime
    have hd3 : 3 ≤ d := by
      have h2 : (2 : ℝ) < d := by linarith
      have : 2 < d := by exact_mod_cast h2
      omega
    obtain ⟨C₀', C', hC₀', hC', hreg⟩ := TorusNote.commutator_estimate_sub_of_torus hd3 hs0 hsub
    refine ⟨max C₀' Cn, C', le_max_of_le_left hC₀', hC', ?_⟩
    intro Λ hΛ N hN ρ hρ hρΛ X hX v K hK
    obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := hK
    rw [if_pos hsub] at hLK
    have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
    refine ⟨offDiagIntegrable_of_lipschitz hd hs0 hsd hρ hρΛ X hL hlip, ?_⟩
    have hmain := hreg Λ hΛ N hN ρ hρ hρΛ X hX L F v hL hF hlip (hfrac hsub)
    have hY0 : 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N :=
      le_trans (hnn Λ hΛ N hN ρ hρ hρΛ X hX)
        (by have := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_right C₀' Cn); linarith)
    have hmono := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_left C₀' Cn)
    have hCLF : 0 ≤ C' * (L + F) := by positivity
    calc |commQuantity d s v X (withDensityReal ρ)|
        ≤ C' * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀' Λ N) := hmain
      _ ≤ C' * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) :=
          mul_le_mul_of_nonneg_left (by linarith) hCLF
      _ ≤ C' * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) := by
          have : C' * (L + F) ≤ C' * K := mul_le_mul_of_nonneg_left hLK hC'.le
          exact mul_le_mul_of_nonneg_right this hY0
  · -- Lipschitz-only regime
    push_neg at hsub
    obtain ⟨C₀', C', hC₀', hC', hreg⟩ := commutator_estimate_super hd hs0 hsub hsd
    refine ⟨max C₀' Cn, C', le_max_of_le_left hC₀', hC', ?_⟩
    intro Λ hΛ N hN ρ hρ hρΛ X hX v K hK
    obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := hK
    rw [if_neg (not_lt.mpr hsub)] at hLK
    have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
    refine ⟨offDiagIntegrable_of_lipschitz hd hs0 hsd hρ hρΛ X hL hlip, ?_⟩
    have hmain := hreg Λ hΛ N hN ρ hρ hρΛ X hX L v hL hlip
    have hY0 : 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N :=
      le_trans (hnn Λ hΛ N hN ρ hρ hρΛ X hX)
        (by have := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_right C₀' Cn); linarith)
    have hmono := oNΛ_mono (d := d) (s := s) (N := N) hΛ0 (le_max_left C₀' Cn)
    have hCL : 0 ≤ C' * L := by positivity
    have hLK' : L ≤ K := by linarith
    calc |commQuantity d s v X (withDensityReal ρ)|
        ≤ C' * L * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀' Λ N) := hmain
      _ ≤ C' * L * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) :=
          mul_le_mul_of_nonneg_left (by linarith) hCL
      _ ≤ C' * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max C₀' Cn) Λ N) := by
          have : C' * L ≤ C' * K := mul_le_mul_of_nonneg_left hLK' hC'.le
          exact mul_le_mul_of_nonneg_right this hY0
```

Exact-type tie:

```
-- Exact-statement tie with the frozen `HRS.commutator_estimate` (Prop 3.32, `Coercivity.lean`).
example := (@commutator_estimate_of_packets : type_of% @HRS.commutator_estimate)
```
