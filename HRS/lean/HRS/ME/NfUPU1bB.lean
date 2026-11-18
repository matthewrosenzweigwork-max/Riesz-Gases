import HRS.Equilibrium.PairMomentsPairs
import HRS.Equilibrium.PairMomentsM2
import HRS.ME.NfUPU1b

/-!
# Packet PU1b, part B (uniform pair-variance and two-pin mean envelopes)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (rule for uniform statements in
`docs/MAIN_E_NF_PLAN.md`, conventions as in `NfUPU1b.lean`):

* `pairVar_noLog_unif` of `HRS.PairMom.pairVar_noLog` (PairMomentsPairs l.485). The constant
  `16 Vc + 32 Cm²` with `Vc = exp (M'max + βp max(γmax,0) + Mmax) BB` and `Cm = δC BA + C1 BC` is chosen
  after `βm, βp, Λ₀` and the envelope data `Env, BA, BB, BC` (uniform in `ρ` via `hEnv`). The row bounds
  `rowData_noLog` are used at the given `(β, ρ)`; their prefactor `exp (M'max + β max(γmax,0) + Mmax)` is
  bounded by its value at `βp`.
* `mean2_large_unif` of `HRS.PairMom.mean2_large` (PairMomentsM2 l.60). The density constant `Λ` of
  `exists_density_bound` is replaced by the fixed `Λ₀` (`ρ ≤ Λ₀` from `RhoU.hup`); the other constants
  (`lintegral_mu_tEnv`, `lintegral_mu_tEnv_cap`) are already uniform in `ρ`.

The `β`-range is the hypothesis `β ∈ Set.Icc βm βp` in both; the density is `RhoU d βm βp c₀ Λ₀ β ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.PoleVar HRS.PairMom HRS.PairCorrAux HRS.PoleCavityAux
  HRS.KernelAux HRS.KernelAux2 HRS.ME.PmU

variable {d : ℕ}

/-- Uniform `pairVar_noLog`: the constant `16 Vc + 32 Cm²` depends on `d, s, βm, βp, Λ₀` and the
envelope data `BA, BB, BC` (uniform envelope bound `hEnv`), not on `β ∈ Icc βm βp` or `ρ`. -/
theorem pairVar_noLog_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c Mmax M'max γmax Cq : ℝ) (Cu : ℝ) (hCu : 0 ≤ Cu)
    (δC C1 : ℝ) (hδC : 0 ≤ δC) (hC1 : 0 ≤ C1)
    {Env : Torus d → Torus d → ℝ} (hEm : ∀ x, Measurable (Env x)) (BA BB BC : ℝ)
    (hBA : 0 ≤ BA) (hBB : 0 ≤ BB) (hBC : 0 ≤ BC)
    (hEnv : ∀ ρ : Torus d → ℝ, (∀ x, ρ x ≤ Λ₀) →
      EnvBounds (d := d) s Cu (withDensityReal ρ) Env BA BB BC) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)), PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      RefDens V β n (δC * deltaN d s (n + 1)) C1 →
      ∀ (K : ℝ) (v : Torus d → Torus d → ℝ), Measurable (Function.uncurry v) → (∀ x y, v x y = v y x) →
      IsCanonicalPair (withDensityReal ρ) v → (∀ x y, x ≠ y → |v x y| ≤ K * Env x y) →
        evariance (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered v X)
            (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  set Vc : ℝ := Real.exp (M'max + βp * max γmax 0 + Mmax) * BB with hVc
  set Cm : ℝ := δC * BA + C1 * BC with hCm
  have hVc0 : 0 ≤ Vc := by
    rw [hVc]; have := Real.exp_pos (M'max + βp * max γmax 0 + Mmax); positivity
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  refine ⟨16 * Vc + 32 * Cm ^ 2, by positivity,
    fun β hβI ρ hU V hV hVu n hn hκ hRD K v hm hsym hcan hv => ?_⟩
  have hβ : 0 < β := hU.hβpos
  have hβle : β ≤ βp := hU.hβle
  have hρ : SmoothPosDensity ρ := hU.rho
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hE0le : Real.exp (M'max + β * max γmax 0 + Mmax) ≤
      Real.exp (M'max + βp * max γmax 0 + Mmax) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβle (le_max_right γmax 0)
    linarith
  obtain ⟨hV1, hM1⟩ := rowData_noLog hd β hβ ρ hρ c Mmax M'max γmax Cq Cu hCu δC C1 hδC hC1 hcrit V hV
    hVu hn hRD hEm hBA hBB hBC (hEnv ρ hU.hup) K hm hcan hv
  have hV1' : ∀ x : Torus d, ∫⁻ y, ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (K ^ 2 * Vc) := by
    intro x
    refine (hV1 x).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hVc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE0le hBB) (sq_nonneg K)
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hL2 := logEN_sq_le (N := N) hN1
  have hL0 : 0 ≤ logEN N := by linarith [logEN_pos' (N := N) hN1]
  have hVar := pairVar_bound V hβ.le hκ hm hsym (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
    (𝒱 := ENNReal.ofReal (K ^ 2 * Vc)) (𝓜 := |K| * Cm * logEN N) hV1' hM1
  refine hVar.trans ?_
  have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 3 := by
    rw [rpow_sq_neg N (by omega)]
    have : (2 * (3 / 2 : ℝ)) = ((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [hc2]
  have hconv : ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 3)) * (((n + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * Vc) + ENNReal.ofReal ((|K| * Cm * logEN N) ^ 2)))
      = ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 3) * ((N : ℝ) * (2 * n * (K ^ 2 * Vc) +
        (|K| * Cm * logEN N) ^ 2))) := by
    rw [show (((n + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal (N : ℝ) by rw [ENNReal.ofReal_natCast]]
    have h1 : (0 : ℝ) ≤ 2 * n := by positivity
    rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  exact real_psi (N : ℝ) (n : ℝ) Vc K (logEN N) (|K| * Cm * logEN N) Cm (by exact_mod_cast hN1)
    (Nat.cast_nonneg n) hnR hVc0 hL2 hCm0 (by positivity) le_rfl

/-- Uniform `mean2_large`: the constant `Λ₀ (δC (2B + 5C_tp) + C2 Cp max(Cb, 1+Cu))` depends on
`d, s, c, βm, βp, c₀, Λ₀` and the data `Cu, C2, δC`, not on `β ∈ Icc βm βp` or `ρ`. -/
theorem mean2_large_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp c₀ Λ₀ : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hΛ : 1 ≤ Λ₀) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) (Cu : ℝ) (hCu : 0 ≤ Cu) (δC : ℝ) (hδC : 0 ≤ δC)
    (C2 : ℝ) (hC2 : 0 ≤ C2) :
    ∃ Cμ : ℝ, 0 ≤ Cμ ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ (V : WeakPotential (withDensityReal ρ)), PotBound (d := d) s c Mmax M'max γmax Cq V →
      (∀ x y : Torus d, x ≠ y → V.q x y ≤ Cu * wEnv s x y) → ∀ m : ℕ, 1 ≤ m → ∀ C1 : ℝ,
      RefDens V β (m + 1) (δC * deltaN d s (m + 2)) C1 → RefDens2 V β m C2 →
      ∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsCanonicalTriple (withDensityReal ρ) g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      ∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          (|K| * Cμ) * (wEnv s x u * (logEN (m + 2) + ellEnv x u)) := by
  obtain ⟨B, Ctp, hB0, hCt0, hT⟩ := lintegral_mu_tEnv (s := s) hd hcrit
  obtain ⟨Cp, hCp0, hCpF⟩ := lintegral_mu_tEnv_cap (s := s) hd hcrit
  have hΛ0 : 0 ≤ Λ₀ := by linarith
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  set Cb : ℝ := (1 + Cu) * (1 + |Real.log (1 + Cu)|) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨Λ₀ * (δC * (2 * B + 5 * Ctp) + C2 * Cp * max Cb (1 + Cu)), by positivity, ?_⟩
  intro β hβI ρ hU V hV hVu m hm1 C1 RD1 RD2 K g3 hgm hcan hg3 x u hxu
  have hβ : 0 < β := hU.hβpos
  have hρ : SmoothPosDensity ρ := hU.rho
  have hΛρ : ∀ x, ρ x ≤ Λ₀ := hU.hup
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hN2 : 2 ≤ m + 2 := by omega
  have hNp : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
  set Nr : ℝ := ((m + 1 + 1 : ℕ) : ℝ) with hNr
  have hNm : (m : ℝ) ≤ Nr := by simp only [hNr]; push_cast; linarith
  have hlam0 : 0 ≤ β / Nr := by positivity
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  set δ : ℝ := δC * deltaN d s (m + 2) with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg hδC (by rw [deltaN_crit hcrit]; have := logEN_pos' (N := m + 2) (by omega); positivity)
  set lam : ℝ := (1 + Cu) / Nr with hlamdef
  have hlam : 0 < lam := by positivity
  set W : ℝ := |K| * (δ * (Λ₀ * (2 * B * wEnv s x u + Ctp * ellEnv x u))) +
    |K| * C2 * (Λ₀ * (Cp * lam * wEnv s x u * (1 + |Real.log lam| + ellEnv x u))) with hW
  have hw1 := PairCorrAux.one_le_wEnv s x u
  have hℓ1 := one_le_ellEnv x u
  have hW0 : 0 ≤ W := by positivity
  have hmt : Measurable fun z : Torus d => ENNReal.ofReal (tEnv s x u z) := by
    have h1 := PairCorrAux.measurable_wEnv s x
    have h2 := PairCorrAux.measurable_wEnv s u
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tEnv
    exact (measurable_const.mul h1).add (measurable_const.mul h2) |>.add (h1.mul h2)
  have hmc : Measurable fun z : Torus d =>
      ENNReal.ofReal (tEnv s x u z * min 1 (lam * (1 + wEnv s x z + wEnv s u z))) := by
    have h1 := PairCorrAux.measurable_wEnv s x
    have h2 := PairCorrAux.measurable_wEnv s u
    refine ENNReal.measurable_ofReal.comp ?_
    unfold tEnv
    exact (((measurable_const.mul h1).add (measurable_const.mul h2)).add (h1.mul h2)).mul
      (measurable_const.min (measurable_const.mul ((measurable_const.add h1).add h2)))
  have hae : ∀ᵐ z ∂(withDensityReal ρ), z ≠ x ∧ z ≠ u :=
    (HRS.External.PoleVar.ae_ne_pt hatom x).and (HRS.External.PoleVar.ae_ne_pt hatom u)
  have hWint : ∫⁻ z, ENNReal.ofReal (|g3 x u z| * (δ + C2 * min 1 ((1 / Nr) * (1 + V.q z x + V.q z u))))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal W := by
    have hpt : ∀ᵐ z ∂(withDensityReal ρ), ENNReal.ofReal (|g3 x u z| * (δ + C2 * min 1 ((1 / Nr) *
        (1 + V.q z x + V.q z u)))) ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (tEnv s x u z) +
          ENNReal.ofReal (|K| * C2) * ENNReal.ofReal (tEnv s x u z *
            min 1 (lam * (1 + wEnv s x z + wEnv s u z))) := by
      filter_upwards [hae] with z hz
      have hzx : x ≠ z := Ne.symm hz.1
      have hzu : u ≠ z := Ne.symm hz.2
      have hf : |g3 x u z| ≤ |K| * tEnv s x u z :=
        (hg3 x u z hxu hzx hzu).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (tEnv_nonneg s x u z))
      have hq1 : V.q z x ≤ Cu * wEnv s x z := by
        have := hVu z x hz.1
        rwa [PairCorrAux.wEnv_symm s z x] at this
      have hq2 : V.q z u ≤ Cu * wEnv s u z := by
        have := hVu z u hz.2
        rwa [PairCorrAux.wEnv_symm s z u] at this
      have hwxz := PairCorrAux.one_le_wEnv s x z
      have hwuz := PairCorrAux.one_le_wEnv s u z
      have hmn : min 1 ((1 / Nr) * (1 + V.q z x + V.q z u)) ≤ min 1 (lam * (1 + wEnv s x z + wEnv s u z)) := by
        refine min_le_min le_rfl ?_
        have h1 : 1 + V.q z x + V.q z u ≤ (1 + Cu) * (1 + wEnv s x z + wEnv s u z) := by nlinarith
        calc (1 / Nr) * (1 + V.q z x + V.q z u) ≤ (1 / Nr) * ((1 + Cu) * (1 + wEnv s x z + wEnv s u z)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = lam * (1 + wEnv s x z + wEnv s u z) := by rw [hlamdef]; ring
      have hq0 := V.q_nonneg z x
      have hq0' := V.q_nonneg z u
      have ht0 := tEnv_nonneg s x u z
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmn0 : 0 ≤ min 1 ((1 / Nr) * (1 + V.q z x + V.q z u)) := le_min zero_le_one (by positivity)
      calc |g3 x u z| * (δ + C2 * min 1 ((1 / Nr) * (1 + V.q z x + V.q z u)))
          ≤ (|K| * tEnv s x u z) * (δ + C2 * min 1 (lam * (1 + wEnv s x z + wEnv s u z))) := by
            refine mul_le_mul hf ?_ (by positivity) (by positivity)
            have := mul_le_mul_of_nonneg_left hmn hC2
            linarith
        _ = _ := by ring
    calc _ ≤ ∫⁻ z, (ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (tEnv s x u z) +
          ENNReal.ofReal (|K| * C2) * ENNReal.ofReal (tEnv s x u z *
            min 1 (lam * (1 + wEnv s x z + wEnv s u z)))) ∂(withDensityReal ρ) := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (|K| * δ) * ∫⁻ z, ENNReal.ofReal (tEnv s x u z) ∂(withDensityReal ρ) +
          ENNReal.ofReal (|K| * C2) * ∫⁻ z, ENNReal.ofReal (tEnv s x u z *
            min 1 (lam * (1 + wEnv s x z + wEnv s u z))) ∂(withDensityReal ρ) := by
          rw [lintegral_add_left (hmt.const_mul _), lintegral_const_mul _ hmt, lintegral_const_mul _ hmc]
      _ ≤ ENNReal.ofReal (|K| * δ) * ENNReal.ofReal (Λ₀ * (2 * B * wEnv s x u + Ctp * ellEnv x u)) +
          ENNReal.ofReal (|K| * C2) * ENNReal.ofReal (Λ₀ * (Cp * lam * wEnv s x u *
            (1 + |Real.log lam| + ellEnv x u))) := by
          gcongr
          · exact hT hΛρ hΛ0 x u hxu
          · exact hCpF hΛρ hΛ0 lam hlam x u hxu
      _ = ENNReal.ofReal W := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; rw [hW]; ring
  have hfπ : ∀ k : Fin m, Integrable (g3 x u) ((pinnedLaw V (β / Nr) m
      (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k)) :=
    fun k => g3_marg_integrable hd hcrit hρ hV hβ.le (by omega) (by omega : m + 2 ≤ m + 1 + 1) K hgm hg3 hxu k
  have hmain := mean_two_pins_le hβ.le RD1 RD2 (f := g3 x u) x u (hcan x u hxu).1 (hcan x u hxu).2 hfπ hW0 hWint
  refine hmain.trans ?_
  have hL1 := logEN_pos' (N := m + 2) (by omega)
  have hNd : ((m + 2 : ℕ) : ℝ) * deltaN d s (m + 2) = logEN (m + 2) := N_mul_deltaN hcrit (by omega)
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmδ : (m : ℝ) * δ ≤ δC * logEN (m + 2) := by
    have hd0 : 0 ≤ deltaN d s (m + 2) := by rw [deltaN_crit hcrit]; positivity
    calc (m : ℝ) * δ = δC * ((m : ℝ) * deltaN d s (m + 2)) := by rw [hδ]; ring
      _ ≤ δC * (((m + 2 : ℕ) : ℝ) * deltaN d s (m + 2)) := by
          gcongr
      _ = δC * logEN (m + 2) := by rw [hNd]
  have hml : (m : ℝ) * (lam * (1 + |Real.log lam|)) ≤ Cb * logEN (m + 2) := by
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have h := lam_log_bound (N := Nr) (n := (m : ℝ)) (Cu := Cu) (by linarith) hmR hNm hCu
    rw [← hlamdef] at h
    have hLeq : logEN (m + 2) = 1 + Real.log ((m + 2 : ℕ) : ℝ) := PairCorrAux.logEN_eq (m + 2) (by omega)
    have : Real.log Nr = Real.log ((m + 2 : ℕ) : ℝ) := rfl
    rw [hLeq, hCb, ← this]
    linarith
  have hmlam : (m : ℝ) * lam ≤ 1 + Cu := by
    rw [hlamdef, ← mul_div_assoc, div_le_iff₀ hNp]
    nlinarith
  have hℓ5 := ellEnv_le_wEnv hxu hs1
  have hfin := real_mean2 (k := |K|) (Λ := Λ₀) (B := B) (Ctp := Ctp) (C2 := C2) (Cp := Cp) (δC := δC)
    (Cb := Cb) (Cu := Cu) (w := wEnv s x u) (ℓ := ellEnv x u) (L := logEN (m + 2)) (m := m) (δ := δ)
    (lam := lam) (abs_nonneg K) hΛ0 hB0 hCt0 hC2 hCp0 hδC hCb0 hCu hmR hδ0 hlam.le hmδ hml hmlam hw1 hℓ5 hℓ1 hL1
  rw [hW]
  exact hfin

end HRS.ME.NfU
