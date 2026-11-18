import HRS.ME.NfUPU5a

/-!
# Packet PU5b (uniform-in-`β` version of `core_unif`)

`core_unif_unif` is `HRS.External.RefMarg.core_unif` (`HRS/Equilibrium/ReferenceMarginal.lean:3131`)
with `β` quantified over `[βm, βp]` after the `∃`: `hκ`, `hsmall`, `hTV0` are restated uniformly in
`β ∈ [βm, βp]` (single `N₃`, single `ε₀`), and the conclusion is `∀ ε > 0, ∃ N₁, ∀ β ∈ [βm, βp], …`.
Changes against the original proof: the truncation level `K`, `τ = ε'/(βp K)`, `εh`, the thresholds
`N₂`, `Nh`, `ND` (from `cavD_torus_unif`) and `N₃` are chosen before `β`; the `β`-dependent constants
`Cν`, `κ₀` are bounded by `Cνu = exp((βp γ+1)+0+βp γ)` and `κu = 4 Cνu (βp γ)`; `β K τ ≤ ε'` and
`β · 2 Cν Λ Tf K ≤ ε'` replace the equalities that used `τ = ε'/(β K)`.
It uses `cavD_torus_unif` (`NfUPU5a.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.NfU

open HRS HRS.External HRS.External.Calib HeatSplit HRS.External.RefMarg

variable {d M : ℕ}

set_option maxHeartbeats 1600000 in
/-- Uniform-in-`β` version of `core_unif` (`HRS/Equilibrium/ReferenceMarginal.lean:3131`). -/
theorem core_unif_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    {βm βp : ℝ} (hβm : 0 < βm) (hββ : βm ≤ βp)
    {q gL : Torus d → ℝ} {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {c : ℝ} (hc0 : 0 ≤ c)
    (hRef : ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      RefHyp (withDensityReal ρ) q gL Ψ (Λ * c))
    (hqm : Measurable q) (hq0 : ∀ z, 0 ≤ q z) (hqe : ∀ z, q (-z) = q z)
    (hqc : ∫⁻ z, ENNReal.ofReal (q z) ≤ ENNReal.ofReal c)
    {K0 : ℝ} (hK0 : 0 < K0)
    (hw : ∀ r : ℝ, 0 < r → (volume : Measure (Torus d)) {z : Torus d | r < q z} ≤
      ENNReal.ofReal (K0 * r ^ (-(pOf d s))))
    (hκ : ∀ β ∈ Set.Icc βm βp, KappaSmall β (Λ * c))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, N₀ ≤ N → ∀ x : Torus d,
        |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ ε)
    {ε₀ : ℕ → ℝ} (hε₀ : Tendsto ε₀ atTop (𝓝 0)) {N₃ : ℕ}
    (hTV0 : ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ n : ℕ, N₃ ≤ n + 1 → 1 ≤ n →
      HRS.External.Entropy.tvDist ((R0 q (withDensityReal ρ) β (n + 1)).map
        (fun X => X ⟨0, Nat.succ_pos n⟩)) (withDensityReal ρ) ≤ ε₀ (n + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ N₁ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, N₁ ≤ N →
      firstMarginal (RN q (withDensityReal ρ) Ψ β N) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ), |((firstMarginal (RN q (withDensityReal ρ) Ψ β N)).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ ε := by
  intro ε hε
  set γ : ℝ := Λ * c with hγ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hγ0 : 0 ≤ γ := mul_nonneg hΛ0 hc0
  have hβp0 : 0 < βp := lt_of_lt_of_le hβm hββ
  set Cνu : ℝ := Real.exp ((βp * γ + 1) + 0 + βp * γ) with hCνu
  have hCνu1 : 1 ≤ Cνu := Real.one_le_exp (by positivity)
  have hCνu0 : 0 ≤ Cνu := by linarith
  have hp := one_lt_pOf hd hs0 hsd
  set p : ℝ := pOf d s with hpdef
  have hpp : 0 < p - 1 := by linarith
  obtain ⟨CD, ND, hCD0, hD⟩ := cavD_torus_unif hd hs0 hsd hΛ1 hqm hq0 hqe hc0 hqc hK0 hw hβm hββ hCνu1
  set κu : ℝ := 4 * Cνu * (βp * γ) with hκu
  have hκu0 : 0 ≤ κu := by positivity
  -- the constants
  set Es : ℝ := Real.log (1 + ε) / 2 with hEs
  have hEs0 : 0 < Es := by
    have : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    positivity
  set ε' : ℝ := Es / 5 with hε'
  have hε'0 : 0 < ε' := by positivity
  set Tf : ℝ → ℝ := fun K => K0 * K ^ (1 - p) * (p / (p - 1)) with hTf
  have hTf0 : ∀ K, 0 < K → 0 ≤ Tf K := fun K hK => by
    have := Real.rpow_pos_of_pos hK (1 - p); simp only [hTf]; positivity
  -- the truncation level `K` (chosen with `β` replaced by `βp`, `Cν` by `Cνu`)
  have hKex : ∃ K : ℝ, 1 ≤ K ∧ 2 * (βp * (Cνu * (Λ * Tf K))) ≤ ε' := by
    have hlim : Tendsto (fun K : ℝ => K ^ (-(p - 1))) atTop (𝓝 0) := tendsto_rpow_neg_atTop hpp
    have hlim2 : Tendsto (fun K : ℝ => 2 * (βp * (Cνu * (Λ * (K0 * K ^ (-(p - 1)) * (p / (p - 1))))))) atTop
        (𝓝 0) := by
      have := ((hlim.const_mul K0).mul_const (p / (p - 1))).const_mul (Λ)
      have := (this.const_mul Cνu).const_mul βp
      have := this.const_mul 2
      simpa using this
    obtain ⟨K, hK⟩ := (eventually_ge_atTop (1 : ℝ)).and (hlim2.eventually (gt_mem_nhds hε'0)) |>.exists
    refine ⟨K, hK.1, ?_⟩
    have e : Tf K = K0 * K ^ (-(p - 1)) * (p / (p - 1)) := by
      simp only [hTf]; congr 2; ring_nf
    rw [e]; exact hK.2.le
  obtain ⟨K, hK1, hKT⟩ := hKex
  have hKpos : 0 < K := by linarith
  have hTfK0 : 0 ≤ Tf K := hTf0 K hKpos
  set τ : ℝ := ε' / (βp * K) with hτ
  have hτ0 : 0 < τ := by positivity
  set εh : ℝ := min 1 (min ε' (τ / (12 * Cνu))) with hεh
  have hεh0 : 0 < εh := by
    refine lt_min one_pos (lt_min hε'0 ?_)
    positivity
  have hεh1 : εh ≤ 1 := min_le_left _ _
  have hεh2 : εh ≤ ε' := (min_le_right _ _).trans (min_le_left _ _)
  have hεh3 : 4 * Cνu * εh ≤ τ / 3 := by
    have : εh ≤ τ / (12 * Cνu) := (min_le_right _ _).trans (min_le_right _ _)
    have h12 : 0 < 12 * Cνu := by positivity
    calc 4 * Cνu * εh ≤ 4 * Cνu * (τ / (12 * Cνu)) := by gcongr
      _ = τ / 3 := by field_simp; ring
  obtain ⟨Nh, hNh⟩ := hsmall εh hεh0
  -- the large-`N` conditions (independent of `β`)
  have hb : ∀ᶠ N : ℕ in atTop, κu / (N : ℝ) ≤ τ / 3 := by
    have : Tendsto (fun N : ℕ => κu / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat κu
    exact this.eventually (ge_mem_nhds (by positivity))
  have hc' : ∀ᶠ N : ℕ in atTop, ε₀ N ≤ τ / 3 := hε₀.eventually (ge_mem_nhds (by positivity))
  have hd' : ∀ᶠ N : ℕ in atTop, βp * (Cνu * (Λ * c)) / (N : ℝ) ≤ ε' := by
    have : Tendsto (fun N : ℕ => βp * (Cνu * (Λ * c)) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    exact this.eventually (ge_mem_nhds hε'0)
  have he : ∀ᶠ N : ℕ in atTop, CD * deltaN d s N ≤ ε' := by
    have := (tendsto_deltaN hd hs0 hsd).const_mul CD
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hε'0)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hb.and (hc'.and (hd'.and he)))
  refine ⟨max (max (max Nh ND) (max N₂ 2)) N₃, fun β hβI ρ hρ hΛρ N hN0' => ?_⟩
  have hN : max (max Nh ND) (max N₂ 2) ≤ N := le_trans (le_max_left _ _) hN0'
  have hN3 : N₃ ≤ N := le_trans (le_max_right _ _) hN0'
  have hNh' : Nh ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hND' : ND ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hNb, hNc, hNd, hNe⟩ := hN₂ N hN₂'
  have hεhN := hNh β hβI ρ hρ hΛρ N hNh'
  have ht : ∀ x, |inner ℝ (tN q (withDensityReal ρ) Ψ β N) (Xi (withDensityReal ρ) Ψ x)| ≤ 1 :=
    fun x => (hεhN x).trans hεh1
  -- the `β`-dependent constants, bounded by their values at `βp`
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hβpβ : β ≤ βp := hβI.2
  have hκβ : KappaSmall β γ := hκ β hβI
  set Cν : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hCν
  have hCν1 : 1 ≤ Cν := Real.one_le_exp (by positivity)
  have hCν0 : 0 ≤ Cν := by linarith
  have hCν_le : Cν ≤ Cνu := by
    rw [hCν, hCνu]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβpβ hγ0
    linarith
  set κ₀ : ℝ := 4 * Cν * (β * γ) with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by positivity
  have hκ_le : κ₀ ≤ κu := by
    rw [hκ₀, hκu]
    gcongr
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  haveI := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have h := hRef ρ hρ hΛρ
  set V := weakPotK h hβ.le (tN q μ Ψ β (n + 1)) ht with hV
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := theta V lam n with hθdef
  have hθ0 : ∀ x, 0 < θ x := theta_pos V hlam0 n
  have hθm : Measurable θ := measurable_theta V hlam0 n
  have hVq : ∀ x y, V.q x y = q (x - y) := fun _ _ => rfl
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cν := le_of_eq rfl
  have hVCu : Real.exp (V.M + V.M' + β * V.γ) ≤ Cνu := by
    show Real.exp ((β * γ + 1) + 0 + β * γ) ≤ Cνu
    rw [hCνu]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hβpβ hγ0
    linarith
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le h hβ.le ht hκβ
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  set ν := cavMarg V lam n with hν
  haveI hνp : IsProbabilityMeasure ν := by
    haveI := isProb_pinnedLaw V hlam0 n (fun e : Empty => e.elim)
    have : IsProbabilityMeasure (cavMarg V lam n) := by unfold cavMarg; infer_instance
    exact this
  have hπle : firstMarginal (RN q μ Ψ β (n + 1)) ≤ ENNReal.ofReal Cν • μ :=
    firstMarginal_RN_leK h hβ hN0 ht
  have hπeq := firstMarginal_RN_eq h hβ ht (n := n)
  rw [← hV] at hπeq
  have hνle : ν ≤ ENNReal.ofReal Cν • μ := by
    have := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simp) (fun e : Empty => e.elim) 0
    exact this
  -- the total-variation distance of `μ` and `ν`
  haveI : IsProbabilityMeasure (R0 q μ β (n + 1)) := h.isProb_R0 hβ.le (n + 1)
  have hεh3' : 4 * Cν * εh ≤ τ / 3 := le_trans (by gcongr) hεh3
  have hκn : κ₀ / ((n + 1 : ℕ) : ℝ) ≤ τ / 3 := le_trans (by gcongr) hNb
  have hTVμν : HRS.External.Entropy.tvDist μ ν ≤ τ := by
    refine tvDist_le_of_forall μ ν fun A hA => ?_
    have h1 := hTV0 β hβI ρ hρ hΛρ n hN3 hn
    have h1' := HRS.External.Entropy.abs_le_tvDist ((R0 q μ β (n + 1)).map
      (fun X => X ⟨0, Nat.succ_pos n⟩)) μ hA
    have h2 := tv_RN_R0 h hβ ht hκV hεhN hA
    have h3 := event_pi_nu h hβ ht hκV hA
    have hκeq : weakKappa V β = κ₀ := rfl
    rw [hκeq] at h3
    have hεn : ε₀ (n + 1) ≤ τ / 3 := hNc
    have hA1 : |((R0 q μ β (n + 1)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A - μ.real A| ≤ τ / 3 :=
      h1'.trans (h1.trans hεn)
    have hA2 : |(firstMarginal (RN q μ Ψ β (n + 1))).real A -
        ((R0 q μ β (n + 1)).map (fun X => X ⟨0, Nat.succ_pos n⟩)).real A| ≤ τ / 3 :=
      h2.trans hεh3'
    have hA3 : |(firstMarginal (RN q μ Ψ β (n + 1))).real A - ν.real A| ≤ τ / 3 := h3.trans hκn
    rw [abs_le] at hA1 hA2 hA3 ⊢
    constructor <;> linarith [hA1.1, hA1.2, hA2.1, hA2.2, hA3.1, hA3.2]
  haveI : IsFiniteMeasure (firstMarginal (RN q μ Ψ β (n + 1))) :=
    ⟨lt_of_le_of_lt (hπle Set.univ) (by simp [Measure.smul_apply])⟩
  have hπ_ac := PoleCavityAux.rnDeriv_le_of_le_withDensity μ (firstMarginal (RN q μ Ψ β (n + 1)))
    (fun _ => ENNReal.ofReal Cν) (by rw [withDensity_const]; exact hπle)
  refine ⟨hπ_ac.1, ?_⟩
  have hrn : (firstMarginal (RN q μ Ψ β (n + 1))).rnDeriv μ =ᵐ[μ] fun y => ENNReal.ofReal (θ y) := by
    rw [hπeq]; exact Measure.rnDeriv_withDensity μ (ENNReal.measurable_ofReal.comp hθm)
  -- the pointwise bound of `φ + log u`
  have hμle : μ ≤ ENNReal.ofReal Cν • μ := by
    intro A
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hCν1)
  have hT : ∫⁻ z, ENNReal.ofReal (q z - K) ≤ ENNReal.ofReal (Tf K) :=
    lintegral_tail_le hqm hq0 hKpos hp hK0 hw
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set a0 : Empty → Torus d := fun e => e.elim with ha0
  set Dfun : Torus d → ℝ := fun x => Real.log (cavU V lam n a0 x) + lam * n * ∫ y, V.q y x ∂ν with hDfun
  set Qν : Torus d → ℝ := fun x => ∫ y, q (x - y) ∂ν with hQν
  have hVqx : ∀ x, (∫ y, V.q y x ∂ν) = Qν x := fun x => by
    simp only [hQν]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show q (y - x) = q (x - y)
    rw [← hqe (x - y), neg_sub]
  set gfun : Torus d → ℝ := fun x => V.φ x + Real.log (cavU V lam n a0 x) with hgfun
  have hQb : ∀ x, 0 ≤ Qν x ∧ Qν x ≤ Cν * (Λ * c) := fun x =>
    ⟨integral_nonneg fun y => hq0 _, integral_kernel_le hΛρ hΛ0 hνle hCν0 hqm hq0 hc0 hqc x⟩
  have hn1 : lam * n = β - lam := by
    have : lam * ((n : ℝ) + 1) = β := by rw [hlam]; push_cast; field_simp
    linarith
  have hDb : ∀ x, 0 ≤ Dfun x ∧ Dfun x ≤ CD * deltaN d s (n + 1) := fun x =>
    hD β hβI ρ hρ hΛρ V hVq hVCu hκV (n + 1) n (by omega) (Nat.le_succ n) x
  have hgb : ∀ x, |gfun x| ≤ Es := by
    intro x
    have hdiff := conv_diff_le hΛρ hΛ0 hqm hq0 (P := μ) (Q := ν) hCν0 hμle hνle hc0 hqc hKpos.le
      (hTf0 K hKpos) hT x
    have hd1 : |convMeasure q μ x - Qν x| ≤ K * τ + 2 * (Cν * (Λ * Tf K)) := by
      refine hdiff.trans ?_
      have : K * HRS.External.Entropy.tvDist μ ν ≤ K * τ := mul_le_mul_of_nonneg_left hTVμν hKpos.le
      linarith
    have e : gfun x = β * (convMeasure q μ x - Qν x) + lam * Qν x +
        inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) + Dfun x := by
      have e1 : V.φ x = β * convMeasure q μ x + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) := rfl
      have e2 : Real.log (cavU V lam n a0 x) = Dfun x - lam * n * Qν x := by
        simp only [hDfun]; rw [hVqx x]; ring
      simp only [hgfun]
      rw [e1, e2, hn1]
      ring
    -- `β K τ ≤ ε'`, since `τ = ε'/(βp K)` and `β ≤ βp`
    have hβKτ : β * K * τ ≤ ε' := by
      have e' : β * K * τ = (β / βp) * ε' := by
        rw [hτ]; field_simp
      have h1' : β / βp ≤ 1 := (div_le_one hβp0).2 hβpβ
      rw [e']
      calc β / βp * ε' ≤ 1 * ε' := mul_le_mul_of_nonneg_right h1' hε'0.le
        _ = ε' := one_mul _
    have hβ2 : β * (2 * (Cν * (Λ * Tf K))) ≤ ε' := by
      calc β * (2 * (Cν * (Λ * Tf K))) ≤ βp * (2 * (Cνu * (Λ * Tf K))) := by gcongr
        _ = 2 * (βp * (Cνu * (Λ * Tf K))) := by ring
        _ ≤ ε' := hKT
    have h1 : |β * (convMeasure q μ x - Qν x)| ≤ ε' + ε' := by
      rw [abs_mul, abs_of_pos hβ]
      calc β * |convMeasure q μ x - Qν x| ≤ β * (K * τ + 2 * (Cν * (Λ * Tf K))) :=
            mul_le_mul_of_nonneg_left hd1 hβ.le
        _ = β * K * τ + β * (2 * (Cν * (Λ * Tf K))) := by ring
        _ ≤ ε' + ε' := add_le_add hβKτ hβ2
    have h2 : |lam * Qν x| ≤ ε' := by
      rw [abs_of_nonneg (mul_nonneg hlam0 (hQb x).1)]
      calc lam * Qν x ≤ lam * (Cν * (Λ * c)) := mul_le_mul_of_nonneg_left (hQb x).2 hlam0
        _ = β * (Cν * (Λ * c)) / ((n + 1 : ℕ) : ℝ) := by rw [hlam]; ring
        _ ≤ βp * (Cνu * (Λ * c)) / ((n + 1 : ℕ) : ℝ) := by gcongr
        _ ≤ ε' := hNd
    have h3 : |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ ε' := (hεhN x).trans hεh2
    have h4 : |Dfun x| ≤ ε' := by
      rw [abs_of_nonneg (hDb x).1]; exact (hDb x).2.trans hNe
    rw [e]
    have := abs_add_le (β * (convMeasure q μ x - Qν x) + lam * Qν x + inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)) (Dfun x)
    have := abs_add_le (β * (convMeasure q μ x - Qν x) + lam * Qν x) (inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x))
    have := abs_add_le (β * (convMeasure q μ x - Qν x)) (lam * Qν x)
    have hEs5 : Es = 5 * ε' := by rw [hε']; ring
    linarith
  -- normalisation: `Z = ∫ exp(gfun)`
  have hZeq : ∫ x, cavTheta V lam n a0 x ∂μ = ∫ x, Real.exp (gfun x) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Real.exp (pinField V lam a0 x) * cavU V lam n a0 x = Real.exp (V.φ x + Real.log (cavU V lam n a0 x))
    rw [Real.exp_add, Real.exp_log (cavU_pos V hlam0 a0 n x), pinField_empty]
  have hZi : Integrable (fun x => Real.exp (gfun x)) μ := by
    rw [← funext fun x => show cavTheta V lam n a0 x = Real.exp (gfun x) from by
      show Real.exp (pinField V lam a0 x) * cavU V lam n a0 x = Real.exp (V.φ x + Real.log (cavU V lam n a0 x))
      rw [Real.exp_add, Real.exp_log (cavU_pos V hlam0 a0 n x), pinField_empty]]
    exact integrable_cavTheta V hlam0 a0 n
  have hZhi : ∫ x, Real.exp (gfun x) ∂μ ≤ Real.exp Es := by
    calc ∫ x, Real.exp (gfun x) ∂μ ≤ ∫ _x, Real.exp Es ∂μ :=
          integral_mono hZi (integrable_const _) fun x => Real.exp_le_exp.2 ((abs_le.1 (hgb x)).2)
      _ = Real.exp Es := by simp
  have hZlo : Real.exp (-Es) ≤ ∫ x, Real.exp (gfun x) ∂μ := by
    calc Real.exp (-Es) = ∫ _x, Real.exp (-Es) ∂μ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hZi fun x => Real.exp_le_exp.2 ((abs_le.1 (hgb x)).1)
  have hlogZ : |Real.log (∫ x, cavTheta V lam n a0 x ∂μ)| ≤ Es := by
    rw [hZeq]
    have hZpos : 0 < ∫ x, Real.exp (gfun x) ∂μ := lt_of_lt_of_le (Real.exp_pos _) hZlo
    rw [abs_le]
    constructor
    · calc -Es = Real.log (Real.exp (-Es)) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) hZlo
    · calc Real.log (∫ x, Real.exp (gfun x) ∂μ) ≤ Real.log (Real.exp Es) := Real.log_le_log hZpos hZhi
        _ = Es := Real.log_exp _
  have hlogθ : ∀ x, |Real.log (θ x)| ≤ 2 * Es := by
    intro x
    have := log_theta_eq V hlam0 n x
    have e : Real.log (θ x) = gfun x - Real.log (∫ x', cavTheta V lam n a0 x' ∂μ) := by
      rw [this]
    rw [e]
    have h1 := hgb x
    calc |gfun x - Real.log (∫ x', cavTheta V lam n a0 x' ∂μ)| ≤
        |gfun x| + |Real.log (∫ x', cavTheta V lam n a0 x' ∂μ)| := abs_sub _ _
      _ ≤ 2 * Es := by linarith
  have hε2 : Real.exp (2 * Es) - 1 = ε := by
    rw [hEs, show 2 * (Real.log (1 + ε) / 2) = Real.log (1 + ε) by ring, Real.exp_log (by linarith)]
    ring
  filter_upwards [hrn] with y h1
  rw [h1, ENNReal.toReal_ofReal (hθ0 y).le]
  have := abs_sub_one_le_of_abs_log_le (hθ0 y) (hlogθ y)
  rw [hε2] at this
  exact this

end HRS.ME.NfU

end
