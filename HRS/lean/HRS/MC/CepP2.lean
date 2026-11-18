import HRS.MC.CepP2Aux8

/-!
# Packet CEPP2: parabolic Weyl lemma for measures with smooth drift (`cep_P2_parabolic_weyl`)

PLAN (no kernel theory; Fourier transform of compactly supported measures + integer-order bootstrap).
Notation: `X = ℝ × ℝⁿ`, `T(O)` = smooth compactly supported `g` with `tsupport g ⊆ O`, `ℓ_ζ(p) = τ t + ⟪ξ, x⟫`,
`C_g(ζ) = ∫ g cos ℓ_ζ dρ`, `S_g(ζ) = ∫ g sin ℓ_ζ dρ`, `N_g = C_g² + S_g²`, `w(ζ) = 1 + |τ| + ‖ξ‖²`.
1. Aux1 (~350 l.)  test class `T(O)`, closure under derivatives, products with `b_k`; second directional derivative of a
   product, derivatives of `cos ∘ ℓ_ζ`, `sin ∘ ℓ_ζ`; integrability of `T(O)` against `ρ`.
2. Aux2 (~400 l.)  Fourier side: `C_g, S_g` bounded (by `∫|g| dρ`) and continuous in `ζ`; the two real identities from `heq`
   applied to `χ cos ℓ_ζ`, `χ sin ℓ_ζ` (χ ∈ T(O)):
     a C_χ + τ S_χ = C_{g0} − ξ·S_{G1},   τ C_χ − a S_χ = −S_{g0} − ξ·C_{G1}       (a = invβ‖ξ‖²),
   with `g0 = ∂_tχ + invβ Δχ + Dχ(0,b)`, `G1_k = 2 invβ ∂_kχ + χ b_k`, all in T(O).
3. Aux3 (~300 l.)  bootstrap: `S(s) := ∀ g ∈ T(O), w^s N_g integrable` for integers `s`.  Base `s = −2(n+2)`
   (`N_g ≤ (∫|g|dρ)²`, `∫ w^{−2(n+2)} < ∞`).  Step: pointwise `w² N_χ ≤ 2 N_χ + c (N_{g0} + w Σ N_{G1_k})`
   (from the identities, Cauchy–Schwarz, `a² + τ² ≥ c' w²`-type bound), so `S(s−1) ⇒ S(s)`.  Hence `S(s)` for all `s`.
4. Aux4 (~400 l.)  all moments `∫ ‖ζ‖^m |F_g| < ∞` for `g ∈ T(O)`; Fourier inversion on `X` for smooth compactly
   supported `φ`, transported from `WithLp 2 X` (`WithLp.volume_preserving_toLp`, Mathlib `Continuous.fourierInv_fourier_eq`).
5. Aux5 (~500 l.)  finite measure `ν` on `X` with all moments of `F_ν` integrable: `∫ φ dν = ∫ φ h` for smooth compactly
   supported `φ`, `h` smooth (`VectorFourier.contDiff_fourierIntegral`); if `ν(Kᶜ) = 0`: `h = 0` off `K`, `h ≥ 0`, and
   `ν = h • vol` (`Measure.ext_of_charFunDual` with cutoff `=1` on `K`).
6. Aux6/CepP2 (~400 l.)  local density near `p₀ ∈ O` (bump `χ` with `χ = 1` near `p₀`, `ν = ρ.withDensity χ`), gluing of local
   smooth densities (a.e. equal continuous functions on overlaps are equal; countable cover; `restrict_iUnion_congr`).
Tie file `CepP2Tie.lean`.  Total estimate ~2500 lines (the plan's 6000 assumed Sobolev-space theory).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepP2

/-- **P2 (parabolic Weyl lemma for measures)**, statement copied verbatim from
`HRS.MC.Cepa.cep_P2_parabolic_weyl`. -/
theorem cep_P2_parabolic_weyl_proof {n : ℕ} {O : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    {b : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b O) {invβ : ℝ} (hβ : 0 < invβ)
    {ρ : Measure (ℝ × EuclideanSpace ℝ (Fin n))} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    (heq : ∀ Φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ →
        HasCompactSupport Φ → tsupport Φ ⊆ O →
        ∫ p, (fderiv ℝ Φ p (1, 0)
              + invβ * ∑ k : Fin n, fderiv ℝ (fderiv ℝ Φ) p (0, EuclideanSpace.single k 1) (0, EuclideanSpace.single k 1)
              + fderiv ℝ Φ p (0, b p)) ∂ρ = 0) :
    ∃ f : ℝ × EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O ∧ (∀ p ∈ O, 0 ≤ f p) ∧
      ρ.restrict O = ((volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))).restrict O).withDensity
        (fun p => ENNReal.ofReal (f p)) :=
  weyl_XS hO hb hρ (fun Φ h1 h2 h3 => heq Φ h1 h2 h3) hβ

end HRS.MC.CepP2
