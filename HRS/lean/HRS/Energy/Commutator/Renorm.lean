import HRS.Energy.Commutator.Stress
import HRS.Energy.Commutator.AbsConv
import HRS.Energy.Commutator.RenormFinal
import HRS.Energy.Commutator.RenormStjFinal
import HRS.Energy.Commutator.RenormStj0Final

/-!
# Route S, packet S4: renormalisation of the commutator (Serfaty smearing, slice by slice)

Source: `[RS] §3.2` (self-contained first-order proof, `Term1 + Term2 + Term3`),
`[CdCRS] Prop. 5.8` (torus sketch); here with the resolvent slices of `Slice.lean` instead of the
Caffarelli-Silvestre extension.

**Statement proved by this packet** (`super_core_*`): for `d - 2 ≤ s < d`, `L`-Lipschitz `v`,
```
|Comm_N(v)| ≤ C L ( F_N + logPart + N⁻² ∑_i selfExcess(r_i) + K a_N^Λ ),   r_i = smearRadius,
```
with `C > 0, K ≥ 0` depending only on `d, s`.  The constant `K` in front of `a_N^Λ` is essential: the bracket
without it can be negative (`F_N` is only `≥ -logPart - C₀ a_N^Λ`; e.g. `d=1, s=0.9, Λ=1, ρ≡1, N=10,
X_i = i/10`: `F_N = -6.548`, `S = 5.16`, `a = 0.794`, bracket `-0.59`), so a hard-coded coefficient `1` would be false.
```
```

**Internal lemma list for the worker** (each is a short, independent lemma; `η_i ∈ [r_i/2, r_i]`,
all objects are those of `Smear.lean`/`Stress.lean`; `c, β` as in `Slice.lean`):
* (S4.1) *Desymmetrisation* (`[RS] (3.33)`): for `l > 0`,
  `Comm^{(l)}_N = (2/N) ∑_i ∫ v(x_i)·∇h^{i,l} dδ_{x_i} - 2 ∫ v·∇h^l dμ` with
  `h^l = N⁻¹∑ G_l(·-x_i) - G_l*μ`, `h^{i,l} = h^l - N⁻¹ G_l(· - x_i)`; from the oddness of `∇G_l`
  and the finite sums (`offDiagPairing` unfolded); no integrability issue (`|k_l| ≲ L G_l`).
* (S4.2) *Term3 = 0* (exactness): `∫ ∇G_l(· - x_j) d(δ_{x_i} - σ^{(i)}) = 0` for `j ≠ i` by S2.2
  (`G_l * σ = G_l` outside the ball, and `∇` of it), and `∫ ∇u_{l,η_i}(·-x_i) dσ_i = 0` by the
  evenness of `σ_i` and the radial symmetry of `u`.  For the Coulomb slice the same with the
  constant `η²/2d`, which disappears under `∇`.
* (S4.3) *Term1* (`[RS] (3.44)`): `Term1^{(l)} = quadForm(k_l)(ν_l, μ)` for the charge
  `ν_l = chargeMeasure (smearT d l) η X`, so `|Term1^{(l)}| ≤ C L E_l(ν_l,μ)` by `stress_rough`.
* (S4.4) *Energy identity integrated in `l`*: from `energy_identity_slice`, the Stieltjes
  representation (`stieltjes_kernel`, `yukawa_stieltjes`) and Tonelli,
  `c ∫ l^{-β} E_l dl ≤ 2 F_N + N⁻²∑ g(η_i) + C Λ λ^{d-s}` (the mass-defect terms
  `(N⁻²∑ w_i - N⁻¹)/l ≤ 0` and `m_l²/l` are nonpositive/`O(η^{d-s})`, see the plan §4.3).  Coulomb
  slice: `energy_identity_coulomb`, error `O(η²)`.
* (S4.5) *Term2* (`[RS] (3.46)-(3.49)`): `|v(x_i) - v(x)| ≤ L η_i` on `supp σ_i ⊂ B_{η_i}`, `|∇u|`
  bounded by `|Γ_l'(η_i)|`, and `∫ l^{-β} |Γ_l'(η)| dl ≈ η^{-s-1}`; the self and `μ` pieces give
  `L (N⁻² ∑ η_i^{-s} + Λ N⁻¹ ∑ η_i^{d-s})`; the piece with the field `∇h^{i,l}` of the *other*
  charges on the sphere is averaged over `η_i ∈ [r_i/2, r_i]` (polar coordinates) and estimated by
  Cauchy-Schwarz against the local energy `∫_{B(x_i,r_i)} (l|h^i|² + |∇h^i|²) ≤ E_l` (disjoint balls,
  `[RS] (3.51)-(3.52)`).  The integral in `l` is done last, with `∫ l^{-β}|Γ_l'|² dl ≈ η^{-s-d}`.
* (S4.6) assembly of S4.1-S4.5 for each of the two cases.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d N : ℕ} {s : ℝ}

/-- **S4, super-Coulomb case `d - 2 < s < d`** (Stieltjes mixture of slices `l > 0`). -/
theorem super_core_stieltjes (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy d s X (withDensityReal ρ) + logPart d s Λ N +
            (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d s Λ N (smearRadius Λ X i) + K * aNΛ d s Λ N) := by
  rcases hs0.lt_or_eq with hpos | hzero
  · exact Stj.super_core_stj_pos hd hpos hs hsd
  · subst hzero
    have hd1 : d = 1 := by
      have h1 : (d : ℝ) < 2 := by linarith
      have h2 : d < 2 := by exact_mod_cast h1
      omega
    subst hd1
    exact Stj.super_core_stj_zero

/-- **S4, Coulomb case `s = d - 2`, `d ≥ 2`** (the single slice `l = 0`; `d = 2` is the logarithm). -/
theorem super_core_coulomb (hd : 2 ≤ d) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity d ((d : ℝ) - 2) v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy d ((d : ℝ) - 2) X (withDensityReal ρ) + logPart d ((d : ℝ) - 2) Λ N +
            (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (smearRadius Λ X i) +
            K * aNΛ d ((d : ℝ) - 2) Λ N) := by
  exact Renorm.super_core_coulomb_aux hd

/-- **S4 (both cases).**  Proved from the two cases above. -/
theorem super_core (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 ≤ s) (hsd : s < d) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy d s X (withDensityReal ρ) + logPart d s Λ N +
            (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d s Λ N (smearRadius Λ X i) + K * aNΛ d s Λ N) := by
  rcases hs.lt_or_eq with hlt | heq
  · exact super_core_stieltjes hd hs0 hlt hsd
  · subst heq
    have hd2 : 2 ≤ d := by
      by_contra h
      have : d = 1 := by omega
      subst this
      norm_num at hs0
    exact super_core_coulomb hd2

end HRS.Commutator
