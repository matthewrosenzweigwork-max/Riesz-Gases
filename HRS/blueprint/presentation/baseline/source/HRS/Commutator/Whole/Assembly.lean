import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.Energy
import HRS.Commutator.Whole.Unit
import HRS.Commutator.Whole.ScaleAux2
import HRS.Commutator.Whole.ApproxAux
import HRS.Commutator.Whole.ApproxAux3

/-!
# Sub-Coulomb commutator on `ℝ^d`: scaling, approximation, Proposition 1.2 and Theorem 1.1

Source `[N]`: Section 5.2 (scaling, L730-766), Section 5.3 (approximation of `μ`, L768-801),
Proposition 1.2 `thm:scale` (L138-148), Theorem 1.1 `thm:main` (L100-119).  Packets `CMX-SCALE`,
`CMX-APPROX`, `CMX-FIN`.

*Proved here from the statements of the lemma layer* (no `sorry` in their own proofs):
`scale_estimate` (Proposition 1.2 for bounded compactly supported `μ`, from `Unit.unit_estimate`,
`Energy.energy_control` and the scaling identities), `subcoulomb_commutator_scale` (Proposition 1.2,
from `scale_estimate`, `integrable_of_Lp` and `density_approx`) and `subcoulomb_commutator`
(Theorem 1.1, from Proposition 1.2 with `p = ∞`, `η = λ`).  The only `sorry`'d statements used are the
elementary scaling identities, the density approximation and the integrability lemma, and (through
`unit_estimate`) the lemma layer of `Unit.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-! ### Section 5.2: restoring the length scale -/

/-- `μ̃ = η^d μ(η·)` is again a bounded compactly supported density of mass one. -/
theorem scaleDens_bdd (η : ℝ) (hη : 0 < η) (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) :
    BddCptDensity (scaleDens η ρ) := by
  exact cmxSA_scaleDens_bdd η hη ρ hρ

/-- `(5.normscaling)` second identity (`[N] L740`): `‖μ̃‖_{L^p} = η^{d(1-1/p)}‖μ‖_{L^p}`
(`p = ∞`: `η^d`; unconditional, both sides are `0` when `μ ∉ L^p`). -/
theorem normE_scaleDens (η : ℝ) (hη : 0 < η) (p : ℝ≥0∞) (ρ : Euc d → ℝ) :
    normE p (scaleDens η ρ) = η ^ ((d : ℝ) * (1 - (p⁻¹).toReal)) * normE p ρ := by
  exact cmxSA_normE_scaleDens η hη p ρ

/-- `(5.normscaling)` first identity (`[N] L739`, L742: "follows from `α - 1 - d/p₁ = 0`"):
`C(ṽ) = C(v)`; here `C(v) ≤ K ⇒ C(ṽ) ≤ K` (the Lipschitz constant and `‖|∇|^α ṽ‖_{L^{p₁}}` are
scale invariant). -/
theorem subTransport_scale (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (v : Euc d → Euc d) (K : ℝ) (hv : SubTransport d s v K) : SubTransport d s (scaleVec η v) K := by
  exact cmxSA_subTransport_scale hd hs0 hsd η hη v K hv

/-- `X̃ = X/η` is pairwise distinct if `X` is. -/
theorem scaleConf_injective {N : ℕ} (η : ℝ) (hη : 0 < η) (X : Fin N → Euc d)
    (hX : Function.Injective X) : Function.Injective (scaleConf η X) := by
  intro i j h
  apply hX
  have hη' : η⁻¹ ≠ 0 := inv_ne_zero hη.ne'
  exact smul_right_injective (Euc d) hη' h

/-- `(5.riesz-scaling)`, `(5.logscaling)` (`[N] L744-759`): `F_N(X̃, μ̃) = η^s F_N(X, μ)` for `s > 0`
and `F_N(X̃, μ̃) = F_N(X, μ) - log η/(2N)` for `s = 0` (`g(z/η) = g(z) + log η`, and
`∫_{△ᶜ} dν^{⊗2} = -1/N`, `(5.massoffdiag)`); the two cases read uniformly
`η^s F_N - 1_{s=0} log η/(2N)`.  Needs the absolute convergence of the integrals (automatic for
bounded compactly supported `μ`). -/
theorem modEnergy_scale (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d)
    (hX : Function.Injective X) :
    modEnergy s (scaleConf η X) (scaleDens η ρ) =
      η ^ s * modEnergy s X ρ - (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) := by
  exact cmxSA_modEnergy_scale hd hs0 hsd η hη ρ hρ hN X hX

/-- `(5.riesz-scaling)` second identity and `[N] L750`: `𝖠₁[X̃, μ̃, ṽ] = η^s 𝖠₁[X, μ, v]`
(for `s = 0` the commutator is unchanged; `∇g(z/η) = η^{s+1}∇g(z)`). -/
theorem commA_scale (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (ρ : Euc d → ℝ) (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Euc d)
    (hX : Function.Injective X) (v : Euc d → Euc d) (L : ℝ≥0) (hv : LipschitzWith L v) :
    commA s (scaleConf η X) (scaleDens η ρ) (scaleVec η v) = η ^ s * commA s X ρ v := by
  exact cmxSA_commA_scale s η hη ρ X v

/-- The right-hand side bracket of `(1.scale)` (`[N] L144-145`):
`Q = F_N - 1_{s=0} log η/(2N) + C_p(η^{-s}/N + ‖μ‖_{L^p} η^{d(1-1/p)-s})`. -/
def scaleQ (s Cp : ℝ) (p : ℝ≥0∞) (η : ℝ) {N : ℕ} (X : Fin N → Euc d) (ρ : Euc d → ℝ) : ℝ :=
  modEnergy s X ρ - (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) +
    Cp * (η ^ (-s) / (N : ℝ) + normE p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))

/-- Proposition 1.2 for bounded compactly supported `μ` (`[N] L761`: "Apply `(5.unitestimate)` to the
rescaled data and multiply by `η^{-s}` … yields `(1.scale)` for bounded compactly supported `μ`.  The
nonnegativity assertion follows at the same time from `(2.Ecoercive)` for the rescaled data").
Proved from `unit_estimate`, `energy_control` and the scaling identities. -/
theorem scale_estimate (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp : ℝ, 0 < Cp ∧ ∀ ρ : Euc d → ℝ, BddCptDensity ρ →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ η : ℝ, 0 < η →
        0 ≤ scaleQ s Cp p η X ρ ∧ |commA s X ρ v| ≤ C * K * scaleQ s Cp p η X ρ := by
  obtain ⟨C, hC, U⟩ := unit_estimate hd hs0 hsd
  refine ⟨C, hC, fun p hp => ?_⟩
  have hd0 : (0 : ℝ) < (d : ℝ) - s := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1p : 1 ≤ p := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) / (d - s) := by
      rw [le_div_iff₀ hd0]; linarith
    exact le_trans (by simpa using ENNReal.ofReal_le_ofReal h1) hp.le
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hq
  have hpq : p⁻¹ + q⁻¹ = 1 := by
    have : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 h1p
    rw [hq, inv_inv, add_tsub_cancel_of_le this]
  obtain ⟨Cp0, hCp0, Uc⟩ := U p q hp hpq
  obtain ⟨Cb, hCb, E⟩ := energy_control hd hs0 hsd
  obtain ⟨Cp1, hCp1, Ec⟩ := E p q hp hpq
  refine ⟨max Cp0 Cp1, lt_max_of_lt_left hCp0, fun ρ hρ N X hN hX v K hv η hη => ?_⟩
  have hρt := scaleDens_bdd η hη ρ hρ
  have hXt := scaleConf_injective η hη X hX
  have hvt := subTransport_scale hd hs0 hsd η hη v K hv
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0, LipschitzWith L v := by
    obtain ⟨L, F, -, hL, -, -⟩ := hv
    exact ⟨L, hL⟩
  have u := Uc (max Cp0 Cp1) (le_max_left _ _) (scaleDens η ρ) hρt N (scaleConf η X) hN hXt
    (scaleVec η v) K hvt
  have c := (Ec (max Cp0 Cp1) (le_max_right _ _) (scaleDens η ρ) hρt N (scaleConf η X) hN hXt).1
  have hηs : 0 < η ^ s := Real.rpow_pos_of_pos hη s
  -- the rescaled energy is `η^s * Q`
  have key : unitE s (max Cp0 Cp1) p (scaleConf η X) (scaleDens η ρ) =
      η ^ s * scaleQ s (max Cp0 Cp1) p η X ρ := by
    unfold unitE scaleQ
    rw [modEnergy_scale hd hs0 hsd η hη ρ hρ hN X hX, normE_scaleDens η hη p ρ]
    have e1 : η ^ s * (η ^ (-s) / (N : ℝ)) = 1 / (N : ℝ) := by
      rw [← mul_div_assoc, ← Real.rpow_add hη]; simp
    have e2 : η ^ s * (normE p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) =
        η ^ ((d : ℝ) * (1 - (p⁻¹).toReal)) * normE p ρ := by
      have := Real.rpow_add hη s ((d : ℝ) * (1 - (p⁻¹).toReal) - s)
      rw [show s + ((d : ℝ) * (1 - (p⁻¹).toReal) - s) = (d : ℝ) * (1 - (p⁻¹).toReal) by ring] at this
      rw [mul_left_comm, ← this]; ring
    have e3 : η ^ s * (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) =
        (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) := by
      split_ifs with h0
      · rw [h0]; simp
      · simp
    linear_combination e3 - (max Cp0 Cp1) * e1 - (max Cp0 Cp1) * e2
  rw [commA_scale hd hs0 hsd η hη ρ hρ hN X hX v L hL, key] at u
  have hM : 0 ≤ normE p (scaleDens η ρ) := ENNReal.toReal_nonneg
  have hMq : 0 ≤ normE q (fTrunc s 1 : Euc d → ℝ) := ENNReal.toReal_nonneg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hunit : 0 ≤ unitE s (max Cp0 Cp1) p (scaleConf η X) (scaleDens η ρ) := by
    refine le_trans ?_ c
    positivity
  rw [key] at hunit
  have hQ : 0 ≤ scaleQ s (max Cp0 Cp1) p η X ρ := (mul_nonneg_iff_of_pos_left hηs).1 hunit
  refine ⟨hQ, ?_⟩
  rw [abs_mul, abs_of_pos hηs] at u
  have : η ^ s * |commA s X ρ v| ≤ η ^ s * (C * K * scaleQ s (max Cp0 Cp1) p η X ρ) := by
    calc η ^ s * |commA s X ρ v| ≤ C * K * (η ^ s * scaleQ s (max Cp0 Cp1) p η X ρ) := u
      _ = η ^ s * (C * K * scaleQ s (max Cp0 Cp1) p η X ρ) := by ring
  exact le_of_mul_le_mul_left this hηs

/-! ### Section 5.3: removing the boundedness and support restrictions -/

/-- `(5.singular-integrability)`, `(5.comm-integrability)`, `(5.logmoment)` (`[N] L782-799`): for
`μ ∈ L¹ ∩ L^p`, `p > d/(d-s)` (and `(1.loghyp)` when `s = 0`), `v` Lipschitz and any configuration, the
integrals defining `F_N` and `𝖠₁` converge absolutely (`sup_x ∫_{|x-y|<1}|x-y|^{-s}|μ| ≤
‖|·|^{-s}1_B‖_{L^{p'}}‖μ‖_{L^p}`; `|(v(x)-v(y))·∇g(x-y)| ≤ ‖∇v‖_∞|x-y|^{-s}`; for `s = 0`,
`(1.loghyp)` implies `∫ log(2+|x|)|μ| < ∞`).  This is the sense of "ensures that the energy and
commutator are well-defined" (`[N] L154`). -/
theorem integrable_of_Lp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (h1 : Integrable ρ)
    (hpρ : MemLp ρ p volume) (hlog : s = 0 → LogIntegrable ρ) (v : Euc d → Euc d) (L : ℝ≥0)
    (hv : LipschitzWith L v) {N : ℕ} (X : Fin N → Euc d) :
    EnergyIntegrable s X ρ ∧ CommIntegrable s X ρ v := by
  exact cmxSA_integrable_of_Lp hd hs0 hsd p hp ρ h1 hpρ hlog v L hv X

/-- The approximation `(5.density-approximation)`, `(5.approximation-limits)` (`[N] L770-801`):
`μ̃_m = μ 1_{|x|≤m, |μ|≤m}`, `c_m = ∫ μ̃_m → 1`, `μ_m = μ̃_m/c_m` (for `m` large; the sequence is
defined for all `m` by any bounded compactly supported mass-one density, e.g. a fixed one, for the
finitely many small `m`); `μ_m` is a bounded compactly supported real density of mass one with
`|μ_m| ≤ 2|μ|`, `‖μ_m‖_{L^p} → ‖μ‖_{L^p}`, and for every configuration and Lipschitz `v`
`F_N(X_N, μ_m) → F_N(X_N, μ)`, `𝖠₁[X_N, μ_m, v] → 𝖠₁[X_N, μ, v]` (dominated convergence; `s > 0`:
`(5.singular-integrability)`; `s = 0`: `(5.logmoment)`).  The sequence depends only on `μ`. -/
theorem density_approx (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (h1 : Integrable ρ)
    (hpρ : MemLp ρ p volume) (hmass : ∫ x, ρ x = 1) (hlog : s = 0 → LogIntegrable ρ) :
    ∃ ρm : ℕ → Euc d → ℝ, (∀ m, BddCptDensity (ρm m)) ∧
      Tendsto (fun m => normE p (ρm m)) atTop (𝓝 (normE p ρ)) ∧
      ∀ (N : ℕ) (X : Fin N → Euc d) (v : Euc d → Euc d) (L : ℝ≥0), LipschitzWith L v →
        Tendsto (fun m => modEnergy s X (ρm m)) atTop (𝓝 (modEnergy s X ρ)) ∧
        Tendsto (fun m => commA s X (ρm m) v) atTop (𝓝 (commA s X ρ v)) := by
  exact cmxSA_density_approx hd hs0 hsd p hp ρ h1 hpρ hmass hlog

/-! ### Proposition 1.2 and Theorem 1.1 -/

/-- Proposition 1.2 `thm:scale` (`[N] L138-148`): let `d ≥ 3`, `0 ≤ s < d-2`, `d/(d-s) < p ≤ ∞`;
`μ ∈ L¹ ∩ L^p` real of mass one (and `(1.loghyp)` if `s = 0`); `v` Lipschitz with
`|∇|^{(d-s)/2} v ∈ L^{2d/(d-s-2)}` (`SubTransport d s v K`: `C(v) ≤ K`).  For every `η > 0` and
every pairwise distinct `X_N`,
`|𝖠₁[X_N, μ, v]| ≤ C(‖∇v‖_∞ + ‖|∇|^{(d-s)/2}v‖_{L^{2d/(d-s-2)}})
  (F_N - (log η)/(2N) 1_{s=0} + C_p(η^{-s}/N + ‖μ‖_{L^p} η^{d(1-1/p)-s}))`,
with `C` depending only on `d, s` (chosen before `p`) and `C_p` only on `d, s, p` (chosen before `μ,
v, X_N, η`); the bracket (`scaleQ`) is nonnegative.  The conclusion also asserts the absolute
convergence of the integrals defining `F_N` and `𝖠₁` (`[N] L154`, `integrable_of_Lp`).  The norm
`C(v)` is represented by an upper bound `K` as in `HRS.Whole.whole_commutator_sub_sharp`
(`‖∇v‖_∞ ≤ L` for a Lipschitz constant `L`, `‖|∇|^α v‖_{L^{p₁}} ≤ F`, `L + F ≤ K`).
Technical hypotheses: `1 ≤ N` (the TeX has `N ∈ ℕ`).  Proved from `scale_estimate`,
`integrable_of_Lp`, `density_approx` (`[N] L801`). -/
theorem subcoulomb_commutator_scale (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp : ℝ, 0 < Cp ∧ ∀ ρ : Euc d → ℝ, Integrable ρ → MemLp ρ p volume → ∫ x, ρ x = 1 →
      (s = 0 → LogIntegrable ρ) →
      ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (N : ℕ) (X : Fin N → Euc d), 1 ≤ N → Function.Injective X → ∀ η : ℝ, 0 < η →
        EnergyIntegrable s X ρ ∧ CommIntegrable s X ρ v ∧
        0 ≤ scaleQ s Cp p η X ρ ∧ |commA s X ρ v| ≤ C * K * scaleQ s Cp p η X ρ := by
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

/-- `‖μ‖_{L^∞} > 0` for a mass-one density in `L^∞`. -/
theorem normE_top_pos (ρ : Euc d → ℝ) (h1 : Integrable ρ) (hinf : MemLp ρ ⊤ volume)
    (hmass : ∫ x, ρ x = 1) : 0 < normE ⊤ ρ := by
  have hfin : eLpNorm ρ ⊤ volume ≠ ⊤ := hinf.eLpNorm_lt_top.ne
  have hne : eLpNorm ρ ⊤ volume ≠ 0 := by
    intro h0
    have hz : ρ =ᵐ[volume] 0 := (eLpNorm_eq_zero_iff (by simp)).1 h0
    have : ∫ x, ρ x = 0 := by
      rw [integral_congr_ae hz]; simp
    rw [hmass] at this
    exact one_ne_zero this
  exact ENNReal.toReal_pos hne hfin

/-- Theorem 1.1 `thm:main` (`[N] L100-119`): let `d ≥ 3`, `0 ≤ s < d-2`.  There are constants
`C, C₀ > 0` depending only on `d, s` such that: for every real `μ ∈ L¹ ∩ L^∞` with `∫ μ = 1` (and
`(1.loghyp)` if `s = 0`), every Lipschitz `v` with `|∇|^{(d-s)/2} v ∈ L^{2d/(d-s-2)}`
(`C(v) ≤ K`), `λ = (N‖μ‖_{L^∞})^{-1/d}` and every pairwise distinct `X_N`,
`|𝖠₁[X_N, μ, v]| ≤ C(‖∇v‖_∞ + ‖|∇|^{(d-s)/2}v‖_{L^{2d/(d-s-2)}})
  (F_N(X_N, μ) - (log λ)/(2N) 1_{s=0} + C₀‖μ‖_{L^∞} λ^{d-s})`,
and the second bracket is nonnegative.  The conclusion also asserts the absolute convergence of the
integrals defining `F_N` and `𝖠₁` (so that no Bochner integral is a junk value).
Technical hypotheses: `1 ≤ N`.  Proved from Proposition 1.2 with `p = ∞`, `η = λ`
(`[N] L150`, L761-766): `λ^{-s}/N = ‖μ‖_{L^∞}λ^{d-s}` and `C₀ = 2C_∞`. -/
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
            C₀ * normE ⊤ ρ * lamN d N ρ ^ ((d : ℝ) - s)) := by
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

end HRS.Commutator.Whole
