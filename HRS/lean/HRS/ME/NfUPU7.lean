import HRS.ME.NfUPU6
import HRS.ME.NfUPU3b
import HRS.ME.NfUPU7a
import HRS.Equilibrium.PairMomentsSetting

/-!
# Packet PU7 (uniform `exists_setting`)

`exists_setting_unif` is `HRS.PairMom.exists_setting` (`HRS/Equilibrium/PairMomentsSetting.lean:232`) in the
uniform form of `docs/MAIN_E_NF_PLAN.md`: every constant and threshold is chosen before `β ∈ [βm, βp]` and
before `ρ` (`RhoU d βm βp c₀ Λ₀ β ρ`); only the potentials `Vf` depend on `(β, ρ)`.

Changes against the original (same proof order):
* split parameters: `exists_split_params_unif` at `Λ₀' = max Λ₀ 1` and `γ₀ = min γ₁ γ₂`, with `γ₁` from
  `pin_comparison_proof_unif` and `γ₂` from `reference_marginal_linf_ev_unifG` (`NfUPU7a`, the variant of
  `reference_marginal_linf_ev_unif` with the row constant before the kernel `q`).
* `N₀` from `eventually_hsmall_unif`, `N₂` from `riesz_Q_le_smul_RN_eventually_unif`, `K` from
  `riesz_Q_le_smul_RN_crude_unif` (`K' n = K (n + 1)`), `CR, N₃` from `reference_marginal_density_L2_unif`,
  `Nthr` from `reference_marginal_density_uniform_unif` (`choose!`, with `max _ 1` for `0 < N`), and
  `Ns = max (max N₀ N₃) 3`, `N₁ = max (max Ns N₂) 4`.
* `Mmax = βp * γ + K0`, `K0 = max 1 (4 * βp * gL 0)`, `KQ = exp (4 * βp * gL 0)`; `β ≤ βp` enters through
  `4 * β * gL 0 ≤ 4 * βp * gL 0` and `β * γ ≤ βp * γ`.
* the `gL` bounds come from the Gram representation (`abs_gL_le_of_gram`), not from a density.
* `hκ : ∀ β ∈ Icc βm βp, KappaSmall β (max Λ₀ 1 * c)` replaces the pointwise smallness of the original.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.External HRS.Quad HRS.External.HeatSplit HRS.External.RefMarg HRS.External.PoleVar
  HRS.External.Glue HRS.External.Calib HRS.PairMom HRS.PinAux HRS.ME.PmU

variable {d : ℕ}

/-- Uniform version of `HRS.PairMom.exists_setting` (`HRS/Equilibrium/PairMomentsSetting.lean:232`). -/
theorem exists_setting_unif (hd : 2 ≤ d) {s : ℝ} (hcrit : s = (d : ℝ) / 2) {βm βp c₀ Λ₀ : ℝ}
    (hβm : 0 < βm) (hββ : βm ≤ βp) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ₀) :
    ∃ (c Cq Mmax M'max γmax : ℝ) (N₁ : ℕ) (KQ δC C1 Cu C2 : ℝ) (K' : ℕ → ℝ),
      (∀ z, 0 ≤ periodicRiesz d s z + c) ∧ 0 ≤ Cq ∧ 2 ≤ N₁ ∧ 0 < KQ ∧ 0 ≤ δC ∧ 0 ≤ C1 ∧ 0 ≤ Cu ∧
      0 ≤ C2 ∧ (∀ n, 0 < K' n) ∧
      ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, RhoU d βm βp c₀ Λ₀ β ρ →
      ∃ Vf : ℕ → WeakPotential (withDensityReal ρ),
        (∀ n (x y : Torus d), x ≠ y → (Vf n).q x y ≤ Cu * wEnv s x y) ∧
        (∀ n, PotBound (d := d) s c Mmax M'max γmax Cq (Vf n)) ∧
        (∀ n, IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))) ∧
        (∀ n, modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
          ENNReal.ofReal (K' n) • pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ∧
        (∀ n, N₁ ≤ n + 1 →
          modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
            ENNReal.ofReal KQ • pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) ∧
          weakKappa (Vf n) β ≤ 1 / 2 ∧
          RefDens (Vf n) β n (δC * deltaN d s (n + 1)) C1) ∧
        (∀ m : ℕ, N₁ ≤ m + 2 → RefDens2 (Vf (m + 1)) β m C2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hs : s ≠ 0 := by rw [hcrit]; linarith
  have hΛ0 : 0 ≤ Λ₀ := by linarith
  have hΛ1 : 1 ≤ max Λ₀ 1 := le_max_right _ _
  -- constants chosen before the split (and hence before `β`, `ρ`)
  obtain ⟨γ₁, hγ₁, hpin⟩ := pin_comparison_proof_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ0
  obtain ⟨γ₂, hγ₂, hlinfG⟩ :=
    reference_marginal_linf_ev_unifG hd hcrit (c₀ := c₀) (Λ₀ := Λ₀) hβm hββ hΛ0
  obtain ⟨τ, L, M, Ψ, hτ, hτ1, hΨ, hκ, hΛc⟩ :=
    exists_split_params_unif hd hs0 hsd hβm hββ (Λ₀ := Λ₀) (lt_min hγ₁ hγ₂)
  obtain ⟨hqm, hq0, hqe, hdec, Cq0, hqenv⟩ := weakSplit_pin_hyp hd hs0 hsd hs hτ hτ1 L
  set q := (weakSplit d s τ L).q with hqdef
  set gL := (weakSplit d s τ L).gL with hgLdef
  set c0 := (weakSplit d s τ L).c with hc0def
  obtain ⟨-, -, hsplit, -, -, -, -, -, -, hc0nn, -, -, hgLc, -, -, -, -⟩ :=
    weakSplit_spec hd hs0 hsd hτ hτ1 L
  have hgL0 : 0 ≤ gL 0 := gL_zero_nonneg_of_gram hΨ
  have hgLabs : ∀ z, |gL z| ≤ gL 0 := abs_gL_le_of_gram hΨ
  have hgLm : Measurable gL := hgLc.measurable
  set c : ℝ := gL 0 + c0 + |periodicRiesz d s 0| with hcdef
  have hc : ∀ z, 0 ≤ periodicRiesz d s z + c := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have := neg_abs_le (periodicRiesz d s 0)
      have := abs_nonneg (periodicRiesz d s 0)
      linarith
    · rw [hsplit z hz]
      have h1 := hgLabs z
      have h2 := neg_abs_le (gL z)
      have h3 := hq0 z
      have h4 := abs_nonneg (periodicRiesz d s 0)
      linarith
  set Cq : ℝ := max 0 (gL 0 + c) with hCqdef
  have hCq0 : 0 ≤ Cq := le_max_left _ _
  have hqlow : ∀ z : Torus d, z ≠ 0 → gPlus d s c z - Cq ≤ q z := by
    intro z hz
    unfold gPlus
    rw [hsplit z hz]
    have h1 := le_abs_self (gL z)
    have h2 := hgLabs z
    have h3 : gL 0 + c ≤ Cq := le_max_right _ _
    linarith
  set γ : ℝ := max Λ₀ 1 * c0 with hγdef
  have hγ0 : 0 ≤ γ := mul_nonneg (le_trans zero_le_one hΛ1) hc0nn
  set K0 : ℝ := max 1 (4 * βp * gL 0) with hK0def
  have hK01 : 1 ≤ K0 := le_max_left _ _
  have hqup : ∀ x y : Torus d, x ≠ y → q (x - y) ≤ |Cq0| * wEnv s x y := by
    intro x y hxy
    have h1 := hqenv (x - y) (sub_ne_zero.2 hxy)
    have hr := PairCorrAux.rTrunc_pos hxy
    have hd0 : Torus.eucDist (x - y) 0 = Torus.eucDist x y := (eucDist_sub x y).symm
    rw [hd0] at h1
    have h2 : Torus.eucDist x y ^ (-s) ≤ rTrunc x y ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hr (PairCorrAux.rTrunc_le_dist x y) (by linarith)
    have h3 : 0 ≤ 1 + Torus.eucDist x y ^ (-s) :=
      add_nonneg zero_le_one (Real.rpow_nonneg (PairCorrAux.eucDist_nonneg' x y) _)
    unfold wEnv
    calc q (x - y) ≤ Cq0 * (1 + Torus.eucDist x y ^ (-s)) := h1
      _ ≤ |Cq0| * (1 + Torus.eucDist x y ^ (-s)) := mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |Cq0| * (1 + rTrunc x y ^ (-s)) := by gcongr
  -- uniform density constants
  obtain ⟨N₀, hN₀⟩ := eventually_hsmall_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ
  obtain ⟨N₂, hN₂⟩ := riesz_Q_le_smul_RN_eventually_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ Ψ hΨ hκ
  obtain ⟨K, hK, hKcrude⟩ :=
    riesz_Q_le_smul_RN_crude_unif hd hs0 hsd hτ hτ1 L (Λ := max Λ₀ 1) Ψ hΨ hβm hββ
  obtain ⟨CR, N₃, hR2⟩ :=
    reference_marginal_density_L2_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ hκ Ψ hΨ
  have hunif := reference_marginal_density_uniform_unif hd hs0 hsd hτ hτ1 L hΛ1 hβm hββ hκ Ψ hΨ
  choose! Nthr₀ hNthr using hunif
  obtain ⟨Cpin, hCpin⟩ := hpin q Cq0 hqm hq0 hqe hdec hqenv 1 1
  obtain ⟨Cac, hCac⟩ := hpin q Cq0 hqm hq0 hqe hdec hqenv 0 0
  obtain ⟨Cpin2, hCpin2⟩ := hpin q Cq0 hqm hq0 hqe hdec hqenv 2 2
  set Ns : ℕ := max (max N₀ N₃) 3 with hNs
  have hNs3 : 3 ≤ Ns := le_max_right _ _
  have hN₀Ns : N₀ ≤ Ns := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₃Ns : N₃ ≤ Ns := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨Clinf, hClinf⟩ := hlinfG q Cq0 hqm hq0 hqe hdec hqenv gL (gL 0) hgLm hgLabs Ns (by omega) CR
    (fun ε => max (Nthr₀ ε) 1)
  set N₁ : ℕ := max (max Ns N₂) 4 with hN₁
  have hN₁Ns : Ns ≤ N₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₁N₂ : N₂ ≤ N₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN₁3 : 4 ≤ N₁ := le_max_right _ _
  refine ⟨c, Cq, βp * γ + K0, 0, γ, N₁, Real.exp (4 * βp * gL 0), max Clinf 0, max Cpin 0, |Cq0|,
    max Cpin2 0, fun n => K (n + 1), hc, hCq0, by omega, Real.exp_pos _, le_max_right _ _,
    le_max_right _ _, abs_nonneg _, le_max_right _ _, fun n => hK (n + 1), ?_⟩
  intro β hβI ρ U
  -- per `(β, ρ)` data
  have hβ : 0 < β := U.hβpos
  have hβle : β ≤ βp := U.hβle
  have hρ : IsProbDensity ρ := U.rho.density
  have hΛρ : ∀ y, ρ y ≤ max Λ₀ 1 := fun y => (U.hup y).trans (le_max_left _ _)
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hRH : Calib.RefHyp (withDensityReal ρ) q gL Ψ γ :=
    Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ
  have hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (min γ₁ γ₂) := by
    intro x
    have h1 := hRH.q_row x
    rw [← ofReal_integral_eq_lintegral_ofReal (hRH.q_int x) (Filter.Eventually.of_forall fun y => hq0 _)]
    exact ENNReal.ofReal_le_ofReal (h1.trans hΛc)
  have hrow1 : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₁ :=
    fun x => (hrow x).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hrow2 : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₂ :=
    fun x => (hrow x).trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have h4 : 4 * β * gL 0 ≤ 4 * βp * gL 0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβle (by norm_num)) hgL0
  have hβγ : β * γ ≤ βp * γ := mul_le_mul_of_nonneg_right hβle hγ0
  have hfieldm : ∀ N : ℕ, Measurable (fun x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)) := fun N => measurable_const.inner hRH.measurable_Xi
  have ht0 : ∀ N : ℕ, 0 < N → ∀ x, |inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun N hN x => (abs_tN_inner_le hRH hβ hN x).trans (h4.trans (le_max_right _ _))
  have ht1 : ∀ N : ℕ, N₀ ≤ N → ∀ x, |inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun N hN x => by
    have := hN₀ β hβI ρ hρ hΛρ N hN x
    rwa [← Calib.inner_eq_sum] at this
  have hWRM : ∀ N : ℕ, 0 < N → weakRefMarginal q (fun x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)) (withDensityReal ρ) β N =
      firstMarginal (Calib.RN q (withDensityReal ρ) Ψ β N) :=
    fun N hN => weakRefMarginal_eq hRH hβ.le (ht0 N hN)
  classical
  let Vf : ℕ → WeakPotential (withDensityReal ρ) := fun n =>
    if h : N₀ ≤ n + 1 then weakPotK hRH hβ.le (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (ht1 (n + 1) h)
    else weakPotK hRH hβ.le (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (ht0 (n + 1) (Nat.succ_pos n))
  have hVq : ∀ n x y, (Vf n).q x y = q (x - y) := by
    intro n x y; simp only [Vf]; split_ifs <;> rfl
  have hVφ : ∀ n, (Vf n).φ = fun x => β * convMeasure q (withDensityReal ρ) x +
      inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (Calib.Xi (withDensityReal ρ) Ψ x) := by
    intro n; simp only [Vf]; split_ifs <;> rfl
  have hVRN : ∀ n, Calib.RN q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    intro n; simp only [Vf]; split_ifs
    · exact RN_eq_pinnedLaw hRH hβ.le _
    · exact RN_eq_pinnedLaw hRH hβ.le _
  have hVbound : ∀ n, PotBound (d := d) s c (βp * γ + K0) 0 γ Cq (Vf n) := by
    intro n
    refine ⟨?_, ?_, ?_, fun x y hxy => ?_⟩
    · simp only [Vf]; split_ifs <;> simp [weakPotK] <;> linarith
    · simp only [Vf]; split_ifs <;> simp [weakPotK]
    · simp only [Vf]; split_ifs <;> simp [weakPotK, hγdef]
    · rw [hVq]; exact hqlow (x - y) (sub_ne_zero.2 hxy)
  have hQprob : ∀ n, IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) :=
    fun n => riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ hΛρ Ψ hΨ hβ (Nat.succ_pos n)
  have hKc : ∀ n, modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ) ≤
      ENNReal.ofReal (K (n + 1)) • pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    intro n
    rw [← hVRN n]
    exact hKcrude β hβI ρ hρ hΛρ (n + 1) (Nat.succ_pos n)
  have hπall : ∀ n : ℕ, (pinnedLaw (Vf n) (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
      (fun Y => Y 0) = weakRefMarginal q (fun x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β (n + 1))
        (Calib.Xi (withDensityReal ρ) Ψ x)) (withDensityReal ρ) β (n + 1) := by
    intro n
    rw [hWRM (n + 1) (Nat.succ_pos n), ← hVRN n]
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rfl
  -- the linf step, its hypotheses for `(β, ρ, hN)`
  have hclin := hClinf β hβI ρ U hrow2
    (fun N x => inner ℝ (Calib.tN q (withDensityReal ρ) Ψ β N) (Calib.Xi (withDensityReal ρ) Ψ x))
    (fun N hN => ⟨hfieldm N, ht1 N (le_trans hN₀Ns hN)⟩)
    (fun N hN => (hCac β hβI ρ U hrow1 N (by omega) _ (hfieldm N) (ht1 N (le_trans hN₀Ns hN))
      (Fin.elim0 : Fin 0 → Torus d) ⟨0, by omega⟩).2.1)
    (fun N hN => by
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      exact calib_form hRH hβ (ht1 (n + 1) (le_trans hN₀Ns hN)))
    (fun N hN => by
      rw [hWRM N (by omega)]
      exact (hR2 β hβI ρ hρ hΛρ N (le_trans hN₃Ns hN)).2)
    (fun ε hε N hN => by
      rw [hWRM N (le_trans (le_max_right _ _) hN)]
      exact (hNthr ε hε β hβI ρ hρ hΛρ N (le_trans (le_max_left _ _) hN)).2)
  refine ⟨Vf, fun n x y hxy => by rw [hVq]; exact hqup x y hxy, hVbound, hQprob, hKc, ?_, ?_⟩
  · intro n hn
    have hNs' : Ns ≤ n + 1 := le_trans hN₁Ns hn
    have hN0 : N₀ ≤ n + 1 := le_trans hN₀Ns hNs'
    have hdif : Vf n = weakPotK hRH hβ.le (Calib.tN q (withDensityReal ρ) Ψ β (n + 1)) (ht1 (n + 1) hN0) := by
      simp only [Vf]; rw [dif_pos hN0]
    have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
    have hπ := hπall n
    have hδ : 0 ≤ deltaN d s (n + 1) := PinAux.deltaN_nonneg hcrit (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [← hVRN n]
      exact gibbs_le_smul_mono (hN₂ β hβI ρ hρ hΛρ (n + 1) (le_trans hN₁N₂ hn)) (Real.exp_le_exp.2 h4)
    · rw [hdif]; exact weakKappa_weakPotK_le hRH hβ.le (ht1 (n + 1) hN0) (hκ β hβI)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hπ]
        exact (hCac β hβI ρ U hrow1 (n + 1) (by omega) _ (hfieldm (n + 1)) (ht1 (n + 1) hN0)
          (Fin.elim0 : Fin 0 → Torus d) ⟨0, by omega⟩).2.1
      · rw [hπ]
        filter_upwards [hclin (n + 1) hNs'] with y hy
        refine hy.trans ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
      · intro x k
        have := (hCpin β hβI ρ U hrow1 (n + 1) (by omega) _ (hfieldm (n + 1)) (ht1 (n + 1) hN0)
          (fun _ : Fin 1 => x) k).1
        rw [← pinnedReference_one_pin (Vf n) q _ (hVq n) (hVφ n) n hlam x]
        exact this
      · intro x k
        have h1 := (hCpin β hβI ρ U hrow1 (n + 1) (by omega) _ (hfieldm (n + 1)) (ht1 (n + 1) hN0)
          (fun _ : Fin 1 => x) k).2.2
        rw [← pinnedReference_one_pin (Vf n) q _ (hVq n) (hVφ n) n hlam x, hπ]
        filter_upwards [h1] with z hz
        refine hz.trans ?_
        have e : ∑ k : Fin 1, q (z - (fun _ : Fin 1 => x) k) = (Vf n).q z x := by
          rw [hVq]; simp
        rw [e]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (le_min zero_le_one (by have := (Vf n).q_nonneg z x; positivity))
  · intro m hm
    have hn : N₁ ≤ m + 1 + 1 := hm
    have hNs' : Ns ≤ m + 1 + 1 := le_trans hN₁Ns hn
    have hN0 : N₀ ≤ m + 1 + 1 := le_trans hN₀Ns hNs'
    have hlam : 0 ≤ β / ((m + 1 + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
    have hπ := hπall (m + 1)
    refine ⟨?_, ?_⟩
    · intro x y k
      have := (hCpin2 β hβI ρ U hrow1 (m + 2) (by omega) _ (hfieldm (m + 2)) (ht1 (m + 2) hN0)
        (![x, y] : Fin 2 → Torus d) k).1
      rw [← pinnedReference_two_pins (Vf (m + 1)) q _ (hVq (m + 1)) (hVφ (m + 1)) m hlam x y]
      exact this
    · intro x y k
      have h1 := (hCpin2 β hβI ρ U hrow1 (m + 2) (by omega) _ (hfieldm (m + 2)) (ht1 (m + 2) hN0)
        (![x, y] : Fin 2 → Torus d) k).2.2
      rw [← pinnedReference_two_pins (Vf (m + 1)) q _ (hVq (m + 1)) (hVφ (m + 1)) m hlam x y, hπ]
      filter_upwards [h1] with z hz
      refine hz.trans ?_
      have e : ∑ k : Fin 2, q (z - (![x, y] : Fin 2 → Torus d) k) =
          (Vf (m + 1)).q z x + (Vf (m + 1)).q z y := by
        rw [hVq, hVq]; simp [Fin.sum_univ_two]
      rw [e]
      have hq1 := (Vf (m + 1)).q_nonneg z x
      have hq2 := (Vf (m + 1)).q_nonneg z y
      have : (1 : ℝ) + ((Vf (m + 1)).q z x + (Vf (m + 1)).q z y) =
          1 + (Vf (m + 1)).q z x + (Vf (m + 1)).q z y := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min zero_le_one (by positivity))

end HRS.ME.NfU

end
