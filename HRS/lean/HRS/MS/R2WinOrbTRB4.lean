import HRS.MS.R2WinOrbTRB3

/-!
# S10.3 packet [B], part 4: the x-weighted pointwise bounds for the nonlocal time-dependent adjoint solutions

Prefix `s103b_`, namespace `HRS.MS.R2WinOrbNL`.

**Theorem `s103b_weighted_decay` ([B], standalone).**  Let `ρ` be a family of densities with `ρ_τ ∈ U2Dec (N+1) L Ah` on `[0,T]`
(`L > d+N+s+3`; this is what `s103n_rho_u2dec` provides for the trajectory of the small class), let `f` be a classical adjoint solution on `[0,t]`,
`t ≤ T`, of the coefficient `(quadraticGradientDyn d s a β).coeff ρ` with terminal datum `φ`, and suppose

* `φ ∈ C^N` has `‖D^iφ(y)‖ ≤ Aφ (1+‖y‖)⁻¹` for `1 ≤ i ≤ N` (decaying derivatives; no assumption on `φ` itself);
* every slice `f_τ`, `τ ∈ [0,t]`, is `C^{N+2}` with `‖D^i f_τ‖ ≤ G` for `1 ≤ i ≤ N+2` (the uniform `C_b^k` gradient bounds of S6.7, `S103nGrad`);

then `(1+‖x‖) ‖D^i f_r(x)‖ ≤ K (Aφ + Ah G)` for all `r ∈ [0,t]`, `1 ≤ i ≤ N`, `x`, with `K = K(d,s,a,β,N,L,T)` independent of `ρ, t, φ, f`.

Route: Duhamel `f_r = P_{t-r}φ + ∫_r^t P_{τ-r} q_τ dτ` for the Mehler semigroup `P` of the Ornstein-Uhlenbeck part `β⁻¹Δ - a x·∇`, where the
whole nonlocal part `q_τ` of the generator (a linear expression in `∇f_τ` and the force of `ρ_τ`) is a SOURCE with jets decaying like `(1+‖x‖)⁻¹`
(`s103b_q_sy`); the iterated differences commute with the flow up to the factor `e^{-aτ}` which gives `e^{-ikτ}(1+e^{-aτ}‖x‖)⁻¹ ≤ (1+‖x‖)⁻¹`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul

variable {d : ℕ}

theorem s103b_dpF_bound {k : ℕ} {g : Euc d → ℝ} {Ng : ℝ} (hN : 0 ≤ Ng) (hg : ContDiff ℝ k g)
    (hb : ∀ i, i ≤ k → (1 ≤ i ∨ k = 0) → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Ng * (1 + ‖y‖)⁻¹)
    (m : Fin k → Euc d) (hm : ∑ l, ‖m l‖ ≤ 1 / 8) (y : Euc d) :
    |s8f_dpF k m g y| ≤ Ng * (5 / 4) ^ k * (∏ l, ‖m l‖) * (1 + ‖y‖)⁻¹ := by
  rw [← s8f_dp_ofFn]
  have hlen : (List.ofFn m).reverse.length = k := by simp
  have hs : (((List.ofFn m).reverse).map (fun e => ‖e‖)).sum ≤ 1 / 8 := by
    rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
    exact hm
  have := s103b_dp_bound k g hN hg hb (List.ofFn m).reverse hlen hs y
  rw [List.map_reverse, List.prod_reverse, List.map_ofFn, List.prod_ofFn] at this
  rwa [Real.norm_eq_abs] at this

/-- The weighted bound of the Mehler average of a difference. -/
theorem s103b_P_dp_wt {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 ≤ τ) {k : ℕ} (hk : 1 ≤ k)
    {g : Euc d → ℝ} {Ng : ℝ} (hN : 0 ≤ Ng) (hg : ContDiff ℝ k g)
    (hb : ∀ i, i ≤ k → 1 ≤ i → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Ng * (1 + ‖y‖)⁻¹)
    {h : ℝ} (hh : 0 < h) (hkh : (k : ℝ) * h ≤ 1 / 8) (e : Fin k → Euc d) (he : ∀ l, ‖e l‖ = h) (x : Euc d) :
    |s83_P a ν τ (s8f_dpF k (fun l => s83_mc a τ • e l) g) x| ≤
      (5 / 4) ^ k * mom d 1 (Real.sqrt (ν / a)) * Ng * h ^ k * (1 + ‖x‖)⁻¹ := by
  set c := s83_mc a τ with hc
  have hc0 : 0 < c := s83_mc_pos a τ
  have hc1 : c ≤ 1 := s83_mc_le_one ha.le hτ
  have hn : ∀ l, ‖c • e l‖ = c * h := fun l => by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0, he]
  have hsum : ∑ l, ‖c • e l‖ ≤ 1 / 8 := by
    simp only [hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (k : ℝ) * (c * h) ≤ (k : ℝ) * h := mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg k)
    linarith
  have hprod : ∏ l, ‖c • e l‖ = (c * h) ^ k := by
    simp only [hn, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  set Gd := s8f_dpF k (fun l => c • e l) g with hGd
  have hbd : ∀ y, |Gd y| ≤ (Ng * (5 / 4) ^ k * (c * h) ^ k) * (1 + ‖y‖)⁻¹ := by
    intro y
    have := s103b_dpF_bound hN hg (fun i hi h1 y => hb i hi (h1.resolve_right (by omega)) y)
      (fun l => c • e l) hsum y
    rwa [hprod] at this
  have hP := s103b_G_wt (c := c) (σ := s83_ms a ν τ) (σ₀ := Real.sqrt (ν / a)) hbd hc0
    (s83_abs_ms_le ha hν.le hτ) x
  have hpow : c ^ k * (1 + c * ‖x‖)⁻¹ ≤ (1 + ‖x‖)⁻¹ := by
    have h1 : c ^ k ≤ c := pow_le_of_le_one hc0.le hc1 (by omega)
    have hp1 : 0 < 1 + c * ‖x‖ := by positivity
    have hp2 : 0 < 1 + ‖x‖ := by positivity
    calc c ^ k * (1 + c * ‖x‖)⁻¹ ≤ c * (1 + c * ‖x‖)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hp1.le)
      _ ≤ (1 + ‖x‖)⁻¹ := by
          rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hp1 hp2]
          nlinarith [norm_nonneg x]
  show |s83_G c (s83_ms a ν τ) Gd x| ≤ _
  refine hP.trans ?_
  have hm1 : 0 ≤ mom d 1 (Real.sqrt (ν / a)) := s83_mom_nonneg _ _ (Real.sqrt_nonneg _)
  have hpw : (c * h) ^ k = c ^ k * h ^ k := mul_pow c h k
  calc Ng * (5 / 4) ^ k * (c * h) ^ k * mom d 1 (Real.sqrt (ν / a)) * (1 + c * ‖x‖)⁻¹
      = (5 / 4) ^ k * mom d 1 (Real.sqrt (ν / a)) * Ng * h ^ k * (c ^ k * (1 + c * ‖x‖)⁻¹) := by
        rw [hpw]; ring
    _ ≤ (5 / 4) ^ k * mom d 1 (Real.sqrt (ν / a)) * Ng * h ^ k * (1 + ‖x‖)⁻¹ :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

theorem s103b_weighted_decay {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (N : ℕ) {L : ℝ} (hL : (d : ℝ) + N + s + 3 < L) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ → Euc d → ℝ) (Ah : ℝ), 0 ≤ Ah → (∀ τ ∈ Set.Icc (0 : ℝ) T, U2Dec (N + 1) L Ah (ρ τ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (Aφ G : ℝ),
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) t φ f →
        ContDiff ℝ (N : WithTop ℕ∞) φ →
        (∀ i, 1 ≤ i → i ≤ N → ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Aφ * (1 + ‖y‖)⁻¹) →
        (∀ τ ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((N + 2 : ℕ) : WithTop ℕ∞) (f τ) ∧
          ∀ i, 1 ≤ i → i ≤ N + 2 → ∀ y, ‖iteratedFDeriv ℝ i (f τ) y‖ ≤ G) →
        ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ i, 1 ≤ i → i ≤ N → ∀ x : Euc d,
          ‖iteratedFDeriv ℝ i (f r) x‖ ≤ K * (Aφ + Ah * G) * (1 + ‖x‖)⁻¹ := by
  obtain ⟨Cq, hCq0, hCq⟩ := s103b_q_sy hd hs0 hsd N hL
  set m₁ : ℝ := mom d 1 (Real.sqrt (β⁻¹ / a)) with hm₁
  have hm₁0 : 0 ≤ m₁ := s83_mom_nonneg _ _ (Real.sqrt_nonneg _)
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  refine ⟨(max 1 (d : ℝ)) ^ N * (5 / 4) ^ N * m₁ * (1 + T) * (1 + Cq), by positivity, ?_⟩
  intro ρ Ah hAh hU t ht φ f Aφ G hf hφc hφb hfb r hr i hi1 hiN x
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc : ∀ τ ∈ Set.Icc (0 : ℝ) t, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ => ⟨hτ.1, hτ.2.trans htT⟩
  -- basic nonnegativity
  have hAφ : 0 ≤ Aφ := by
    have := hφb 1 le_rfl (by omega) 0
    simpa using (norm_nonneg _).trans this
  have hG : 0 ≤ G := by
    have := (hfb r hr).2 1 le_rfl (by omega) 0
    exact (norm_nonneg _).trans this
  -- the source `q_τ`
  set q : ℝ → Euc d → ℝ := fun τ => s103bQ d s (ρ τ) (f τ) with hq
  have hqSy : ∀ τ ∈ Set.Icc (0 : ℝ) t, Sy N (Cq * Ah * G) (q τ) := fun τ hτ =>
    hCq Ah (ρ τ) hAh (hU τ (hIcc τ hτ)) G (f τ) (hfb τ hτ).1 (hfb τ hτ).2
  obtain ⟨hmild, hint⟩ := s103b_mild s a β ha hβ ρ ht0 hf
  -- continuity and boundedness of the data
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  have htI : t ∈ Set.Icc (0 : ℝ) t := ⟨ht0, le_rfl⟩
  have hφcont : Continuous φ := by
    have := (hf.c2 t htI).continuous
    rwa [hf.terminal] at this
  have hφbd : ∀ y, |φ y| ≤ B0 := fun y => by
    have := hB0 t htI y
    rw [hf.terminal, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this
  have hqcont : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (q τ) := fun τ hτ =>
    (hqSy τ hτ).1.continuous
  have hqbd : ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ y, |q τ y| ≤ Cq * Ah * G := by
    intro τ hτ y
    have := (hqSy τ hτ).2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have hw : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
    have hA0 : 0 ≤ Cq * Ah * G := by positivity
    calc |q τ y| ≤ Cq * Ah * G * (1 + ‖y‖)⁻¹ := this
      _ ≤ Cq * Ah * G * 1 := mul_le_mul_of_nonneg_left hw hA0
      _ = _ := mul_one _
  -- the partial derivative bound
  have hfr : f r = fun y => s83_P a β⁻¹ (t - r) φ y +
      ∫ τ in r..t, s83_P a β⁻¹ (τ - r) (q τ) y := funext (hmild r hr)
  have hfrC : ContDiff ℝ (i : WithTop ℕ∞) (f r) :=
    (hfb r hr).1.of_le (by exact_mod_cast (by omega : i ≤ N + 2))
  have hpart : ∀ idx : Fin i → Fin d, |HRS.Whole.partialDeriv idx (f r) x| ≤
      (5 / 4) ^ i * m₁ * (Aφ + T * (Cq * Ah * G)) * (1 + ‖x‖)⁻¹ := by
    intro idx
    refine s8f_partial_le_of_dp hfrC idx x (h0 := 1 / (8 * ((i : ℝ) + 1))) (by positivity) ?_
    intro h hh hh0
    set m : Fin i → Euc d := fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d) with hm
    have hmn : ∀ l, ‖m l‖ = h := fun l => by simp [hm, norm_smul, abs_of_pos hh]
    have hkh : (i : ℝ) * h ≤ 1 / 8 := by
      have hi0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have : h ≤ 1 / (8 * ((i : ℝ) + 1)) := hh0
      calc (i : ℝ) * h ≤ ((i : ℝ) + 1) * (1 / (8 * ((i : ℝ) + 1))) :=
            mul_le_mul (by linarith) this hh.le hi0.le
        _ = 1 / 8 := by field_simp
    -- split the Duhamel representation
    have hsplit : s8f_dpF i m (f r) x = s8f_dpF i m (s83_P a β⁻¹ (t - r) φ) x +
        s8f_dpF i m (fun y => ∫ τ in r..t, s83_P a β⁻¹ (τ - r) (q τ) y) x := by
      rw [hfr]
      exact s103b_dpF_add i m _ _ x
    have hint' := (s103b_dpF_integral (r := r) (t := t)
      (F := fun τ y => s83_P a β⁻¹ (τ - r) (q τ) y) (fun y => hint r hr y) i m).2 x
    -- the datum term
    have hφi : ContDiff ℝ (i : WithTop ℕ∞) φ := hφc.of_le (by exact_mod_cast hiN)
    have hdat : |s8f_dpF i m (s83_P a β⁻¹ (t - r) φ) x| ≤
        (5 / 4) ^ i * m₁ * Aφ * h ^ i * (1 + ‖x‖)⁻¹ := by
      rw [s103b_P_dpF a β⁻¹ (t - r) hφcont hφbd i m x]
      exact s103b_P_dp_wt ha hν (sub_nonneg.2 hr.2) hi1 hAφ hφi
        (fun i' hi' h1 y => hφb i' h1 (hi'.trans hiN) y) hh hkh m hmn x
    -- the source term
    have hsrc : ‖∫ τ in r..t, s8f_dpF i m (fun y => s83_P a β⁻¹ (τ - r) (q τ) y) x‖ ≤
        ((5 / 4) ^ i * m₁ * (Cq * Ah * G) * h ^ i * (1 + ‖x‖)⁻¹) * |t - r| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ => ?_
      have hτ' : τ ∈ Set.Icc r t := by
        rw [Set.uIoc_of_le hr.2] at hτ
        exact ⟨hτ.1.le, hτ.2⟩
      have hτ0 : τ ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.trans hτ'.1, hτ'.2⟩
      show ‖s8f_dpF i m (s83_P a β⁻¹ (τ - r) (q τ)) x‖ ≤ _
      rw [s103b_P_dpF a β⁻¹ (τ - r) (hqcont τ hτ0) (hqbd τ hτ0) i m x, Real.norm_eq_abs]
      refine s103b_P_dp_wt ha hν (sub_nonneg.2 hτ'.1) hi1 (by positivity)
        ((hqSy τ hτ0).1.of_le (by exact_mod_cast hiN))
        (fun i' hi' h1 y => (hqSy τ hτ0).2 i' (hi'.trans hiN) y) hh hkh m hmn x
    have hw0 : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
    have hh0' : 0 ≤ h ^ i := by positivity
    have hA54 : 0 ≤ (5 / 4 : ℝ) ^ i := by positivity
    have habs : |t - r| ≤ T := by
      rw [abs_of_nonneg (sub_nonneg.2 hr.2)]; linarith [hr.1]
    have hpre : 0 ≤ (5 / 4) ^ i * m₁ * (Cq * Ah * G) * h ^ i * (1 + ‖x‖)⁻¹ := by positivity
    rw [hsplit, hint']
    refine (abs_add_le _ _).trans ?_
    rw [← Real.norm_eq_abs (∫ τ in r..t, s8f_dpF i m (fun y => s83_P a β⁻¹ (τ - r) (q τ) y) x)]
    calc _ ≤ (5 / 4) ^ i * m₁ * Aφ * h ^ i * (1 + ‖x‖)⁻¹ +
          ((5 / 4) ^ i * m₁ * (Cq * Ah * G) * h ^ i * (1 + ‖x‖)⁻¹) * |t - r| := add_le_add hdat hsrc
      _ ≤ (5 / 4) ^ i * m₁ * Aφ * h ^ i * (1 + ‖x‖)⁻¹ +
          ((5 / 4) ^ i * m₁ * (Cq * Ah * G) * h ^ i * (1 + ‖x‖)⁻¹) * T := by
          gcongr
      _ = ((5 / 4) ^ i * m₁ * (Aφ + T * (Cq * Ah * G)) * (1 + ‖x‖)⁻¹) * h ^ i := by ring
  -- from the partial derivatives to the full norm
  have hBnn : 0 ≤ (5 / 4 : ℝ) ^ i * m₁ * (Aφ + T * (Cq * Ah * G)) * (1 + ‖x‖)⁻¹ := by
    have : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
    positivity
  have hnorm := s83_norm_iter_le_card hBnn i (f r) x hpart
  refine hnorm.trans ?_
  have hd1 : (1 : ℝ) ≤ max 1 (d : ℝ) := le_max_left _ _
  have hdi : (d : ℝ) ^ i ≤ (max 1 (d : ℝ)) ^ N :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) i).trans
      (pow_le_pow_right₀ hd1 hiN)
  have h54 : (5 / 4 : ℝ) ^ i ≤ (5 / 4) ^ N := pow_le_pow_right₀ (by norm_num) hiN
  have hw0 : 0 ≤ (1 + ‖x‖)⁻¹ := inv_nonneg.2 (by linarith [norm_nonneg x])
  have hAG : Aφ + T * (Cq * Ah * G) ≤ (1 + T) * (1 + Cq) * (Aφ + Ah * G) := by
    have h1 : 0 ≤ Ah * G := mul_nonneg hAh hG
    nlinarith [mul_nonneg hT hCq0, mul_nonneg (mul_nonneg hT hCq0) h1, mul_nonneg hT h1,
      mul_nonneg hCq0 h1, mul_nonneg hT hAφ, mul_nonneg hCq0 hAφ, mul_nonneg (mul_nonneg hT hCq0) hAφ]
  have hdm : 0 ≤ (d : ℝ) ^ i := by positivity
  calc (d : ℝ) ^ i * ((5 / 4) ^ i * m₁ * (Aφ + T * (Cq * Ah * G)) * (1 + ‖x‖)⁻¹)
      ≤ (max 1 (d : ℝ)) ^ N * ((5 / 4) ^ N * m₁ * ((1 + T) * (1 + Cq) * (Aφ + Ah * G)) * (1 + ‖x‖)⁻¹) := by
        gcongr
    _ = _ := by ring

end HRS.MS.R2WinOrbNL

end
