import HRS.ME.NfUPU7
import HRS.ME.NfUPU8B
import HRS.ME.NfUPU9B

/-!
# Packet PU10b (uniform `energy_all`, `partt_all`)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule for uniform statements in
`docs/MAIN_E_NF_PLAN.md`):

* `energy_all_unif` of `HRS.PairMom.energy_all` (`HRS/Equilibrium/PairMomentsEnergy.lean`, `EnergyAll`).
* `partt_all_unif` of `HRS.PairMom.partt_all` (`HRS/Equilibrium/PairMomentsTT.lean`, `TripleAll`).

Fixed data: `d, s` (with `hd`, `hcrit`), `βm βp c₀ Λ₀` with `0 < βm`, `βm ≤ βp`, `0 < c₀`, `1 ≤ Λ₀`.
The constant is chosen after this data and before `β ∈ Set.Icc βm βp` and `ρ` (`RhoU d βm βp c₀ Λ₀ β ρ`).
The setting constants and the sequence `K' : ℕ → ℝ` come from `exists_setting_unif` (`NfUPU7`); the
reference-level constants come from `energy_ref_large_unif`, `energy_ref_crude_unif` (`NfUPU8B`) resp.
`partt_ref_large_unif`, `level2_crude_unif` (`NfUPU9B`, `NfUPU9`). Only the potentials `Vf` depend on `(β, ρ)`.

Changes against the originals:
* `hρs : SmoothPosDensity ρ` and `hβ : 0 < β` are replaced by `RhoU` (its fields `rho`, `hβpos`).
* `exists_setting hd hcrit β hβ ρ hρs` is replaced by `exists_setting_unif`; the sequence `K'` is fixed
  before `(β, ρ)` (in the original it was chosen by `choose` from the per-`(β, ρ)` bound).
* The per-`(β, ρ)` data `Vf` and its properties are obtained from the setting after `intro β hβI ρ U`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.PoleVar HRS.PairMom HRS.PairCorrAux HRS.PoleCavityAux
  HRS.ME.PmU

variable {d : ℕ}

/-- Uniform `energy_all` (`HRS.PairMom.energy_all`): the constant `max (KQ Cl) Csum` is chosen before
`β ∈ Icc βm βp` and `ρ`; `RhoU` replaces `(β > 0, SmoothPosDensity ρ)`. -/
theorem energy_all_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), (∀ x y, ψ x y = ψ y x) →
      IsCanonicalPair (withDensityReal ρ) ψ →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d) →
      (∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
        K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))) → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 / N) := by
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, K', hc, hCq, -, hKQ, hδC, hC1, hCu, -,
    hK'pos, hset⟩ := exists_setting_unif hd hcrit hβm hββ hc₀ hΛ
  obtain ⟨Cl, hCl0, hCl⟩ := energy_ref_large_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c Mmax M'max γmax Cq
    Cu hCu δC C1 hδC hC1
  obtain ⟨Cc, hCc0, hCc⟩ := energy_ref_crude_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c Mmax M'max γmax Cq
    Cu hCu
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * Cc * (N₁ : ℝ) with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cl) Csum, le_trans (by positivity) (le_max_left _ _),
    fun β hβI ρ U K ψ hsymm hcan hsm hgrad N hN => ?_⟩
  obtain ⟨Vf, hVu, hbd, hprob, hcrude, hlarge, -⟩ := hset β hβI ρ U
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI := hprob n
  have hNp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  by_cases hbig : N₁ ≤ n + 1
  · obtain ⟨hle, hκ, hRD⟩ := hlarge n hbig
    have h1 := hCl β hβI ρ U (Vf n) (hbd n) (hVu n) n (by omega) hκ hRD K ψ hsymm hcan hsm hgrad
    calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂(ENNReal.ofReal KQ •
          pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
          lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal KQ * ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal KQ * ENNReal.ofReal (Cl * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (KQ * (Cl * K ^ 2 / ((n + 1 : ℕ) : ℝ))) := (ENNReal.ofReal_mul hKQ.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc, ← mul_assoc]
          refine div_le_div_of_nonneg_right ?_ hNp.le
          nlinarith [mul_le_mul_of_nonneg_right (le_max_left (KQ * Cl) Csum) (sq_nonneg K)]
  · push Not at hbig
    have hNlt : n + 1 < N₁ := hbig
    have hle := hcrude n
    have h1 := hCc β hβI ρ U (Vf n) (hbd n) n (by omega) K ψ hsymm hcan hsm hgrad
    calc ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂(ENNReal.ofReal (K' n) •
          pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
          lintegral_mono' hle le_rfl
      _ = ENNReal.ofReal (K' n) * ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
          ∂(pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (K' n) * ENNReal.ofReal (Cc * K ^ 2) := mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (K' n * (Cc * K ^ 2)) := (ENNReal.ofReal_mul (hK'pos n).le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hKn := hK'pos n
          have hterm : K' n * Cc * (N₁ : ℝ) ≤ Csum := by
            rw [hCsum]
            exact Finset.single_le_sum (f := fun n => K' n * Cc * (N₁ : ℝ))
              (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
          have hNN1 : ((n + 1 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
          rw [le_div_iff₀ hNp]
          have h3 : 0 ≤ K' n * Cc * K ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right (hterm.trans (le_max_right (KQ * Cl) Csum)) (sq_nonneg K),
            mul_le_mul_of_nonneg_left hNN1 h3]

/-- Uniform `partt_all` (`HRS.PairMom.partt_all`): the constant `max (KQ Cl) Csum` is chosen before
`β ∈ Icc βm βp` and `ρ`; `RhoU` replaces `(β > 0, SmoothPosDensity ρ)`. -/
theorem partt_all_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 → IsCanonicalTriple (withDensityReal ρ) g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) → ∀ N : ℕ, 2 ≤ N →
        evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * K ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2) := by
  obtain ⟨c, Cq, Mmax, M'max, γmax, N₁, KQ, δC, C1, Cu, C2, K', hc, hCq, -, hKQ, hδC, hC1, hCu, hC2,
    hK'pos, hset⟩ := exists_setting_unif hd hcrit hβm hββ hc₀ hΛ
  obtain ⟨Cl, hCl0, hCl⟩ := partt_ref_large_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq
    hCq Cu hCu δC hδC C2 hC2
  obtain ⟨Cc, hCc0, hCc⟩ := level2_crude_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ c hc Mmax M'max γmax Cq hCq
  set Csum : ℝ := ∑ n ∈ Finset.range N₁, K' n * Cc * (N₁ : ℝ) ^ 3 with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun n _ => by have := hK'pos n; positivity
  refine ⟨max (KQ * Cl) Csum, le_trans (by positivity) (le_max_left _ _),
    fun β hβI ρ U K g3 hgm hsym hcan hg3 N hN => ?_⟩
  have hβ : 0 < β := U.hβpos
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal U.rho.density
  obtain ⟨Vf, hVu, hbd, hprob, hcrude, hlarge, hlarge2⟩ := hset β hβI ρ U
  by_cases hN2 : N = 2
  · subst hN2
    have : (fun X : Config d 2 => ((2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X) = 0 := by
      funext X
      simp [tripleSum_two]
    rw [this, evariance_zero]
    exact bot_le
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hF : Measurable (fun X : Config d (m + 2) => ((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X) :=
    measurable_const.mul (measurable_tripleSum hgm)
  have hP : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (m + 2) β (withDensityReal ρ)) :=
    hprob (m + 1)
  have hNp : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hL1 := logEN_pos' (N := m + 2) (by omega)
  by_cases hbig : N₁ ≤ m + 2
  · obtain ⟨hle, hκ, hRD⟩ := hlarge (m + 1) hbig
    have hRD2 := hlarge2 m hbig
    refine (evar_transfer_large hle hF).trans ?_
    have h1 := hCl β hβI ρ U (Vf (m + 1)) (hbd (m + 1)) (hVu (m + 1)) m hm1 hκ C1 hRD hRD2 K g3 hgm hsym
      hcan hg3
    refine (mul_le_mul' le_rfl h1).trans ?_
    rw [← ENNReal.ofReal_mul hKQ.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have : KQ * (Cl * K ^ 2 * logEN (m + 2) ^ 2 / ((m + 2 : ℕ) : ℝ) ^ 2) ≤
        max (KQ * Cl) Csum * K ^ 2 * logEN (m + 2) ^ 2 / ((m + 2 : ℕ) : ℝ) ^ 2 := by
      rw [← mul_div_assoc, ← mul_assoc, ← mul_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have : 0 ≤ K ^ 2 * logEN (m + 2) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left (KQ * Cl) Csum) this]
    exact this
  · push Not at hbig
    have hNlt : m + 2 < N₁ := hbig
    have hle := hcrude (m + 1)
    have h2 := hCc β hβI ρ U (Vf (m + 1)) (hbd (m + 1)) m hm1 K g3 hgm hg3
    have hcr := crude_tripleSum (Vf (m + 1)) hβ.le (m := m) hgm
      (((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) h2 hle
    refine hcr.trans ?_
    have hc2 : (((m + 2 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / ((m + 2 : ℕ) : ℝ) ^ 5 := by
      rw [rpow_sq_neg (m + 2) (by omega)]
      have : (2 * (5 / 2 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_natCast]
    have hKn := hK'pos (m + 1)
    rw [hc2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hKn.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hterm : K' (m + 1) * Cc * (N₁ : ℝ) ^ 3 ≤ Csum := by
      rw [hCsum]
      exact Finset.single_le_sum (f := fun n => K' n * Cc * (N₁ : ℝ) ^ 3)
        (fun n _ => by have := hK'pos n; positivity) (Finset.mem_range.2 (by omega))
    have hNN1 : ((m + 2 : ℕ) : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hNlt.le
    set Nr : ℝ := ((m + 2 : ℕ) : ℝ) with hNr
    have e : K' (m + 1) * (1 / Nr ^ 5 * (Nr ^ 2 * (Cc * K ^ 2 * Nr ^ 4 * logEN (m + 2) ^ 2)))
        = (K' (m + 1) * Cc * K ^ 2 * logEN (m + 2) ^ 2) * Nr := by
      field_simp
    rw [e]
    have h3 : (K' (m + 1) * Cc * K ^ 2 * logEN (m + 2) ^ 2) * Nr ≤
        (K' (m + 1) * Cc * (N₁ : ℝ) ^ 3) * K ^ 2 * logEN (m + 2) ^ 2 / Nr ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h4 : Nr * Nr ^ 2 ≤ (N₁ : ℝ) ^ 3 := by
        have : Nr ^ 3 ≤ (N₁ : ℝ) ^ 3 := pow_le_pow_left₀ hNp.le hNN1 3
        nlinarith [this]
      have h5 : 0 ≤ K' (m + 1) * Cc * K ^ 2 * logEN (m + 2) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    refine h3.trans ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ K ^ 2 * logEN (m + 2) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (hterm.trans (le_max_right (KQ * Cl) Csum)) this]

end HRS.ME.NfU

end
