import HRS.MC.S7PIDVMain
import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet I: proof of `HRS.MC.Sec7.PIDPlan.s7_PID_incr` (statement copied verbatim)

Route (docstring D1b of `S7PIDPlan.lean`):

* `s7_PID_V_holder` is taken from `HRS.MC.Sec7.S7PIDV.s7_PID_V_holder_proof` (`S7PIDVMain.lean`).
* The uniform bound `‖V^{t,u}F‖_{E_m} ≤ Am ‖F‖_{E_m}` comes from `pie_Vbound_of_finBd` with the finite-section
  bound `S7PIDV_finBd_unif` at the integer level `k+2 < m ≤ k+3` (`S7PIDV_hyp`).
* For the mode `e = modeVec m k`: `‖e‖_{E_m} ≤ ‖e‖_{E_{m-1}} = ⟨k⟩^{-(m-1)}`, hence `‖e‖² ≤ Q := ⟨k⟩^{-2(m-1)}`.
* The integrand of the first bound is `≤ A + D·1_{(s,t]}` on `(c,c']` with `A = B² L² (t-s) Q` (from the Hölder bound on
  `u ≤ s`) and `D = B² Am² Q` (on `u ∈ (s,t]`, where the kernel is `V^{t,u} e`), and it vanishes for `u > t`.
  Integrating gives `A (c'-c) + D (t-s) ≤ (L² T + Am²) B² Q (t-s)` since `c'-c ≤ T`.
* Junk values are avoided: `integral_mono_of_nonneg` needs no integrability or measurability of the integrand, only
  nonnegativity a.e. and an integrable majorant.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDI

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

/-- the coordinate sequence of a mode is finitely supported, hence in `ℓ²` -/
lemma S7PIDI_memℓp_mode (σ : ℝ) (k : NonzeroLattice d) :
    Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-σ) * (if j = k then (1 : ℝ) else 0)) 2 := by
  rw [Torus.memℓp_two_iff]
  refine summable_of_ne_finset_zero (s := {k}) fun j hj => ?_
  have hjk : j ≠ k := by simpa using hj
  simp [hjk]

/-- the unweighted Fourier coefficients of the mode vector `modeVec m k` are the indicator of `k` -/
lemma S7PIDI_fc_mode (m : ℝ) (k j : NonzeroLattice d) :
    NegSobolev.fourierCoeff (modeVec m k) j = if j = k then 1 else 0 := by
  unfold modeVec
  unfold NegSobolev.fourierCoeff
  rw [NegSobolev.coord_ofSeq_of_mem (fun j : NonzeroLattice d => if j = k then (1 : ℝ) else 0)
    (S7PIDI_memℓp_mode m k) j]
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos j.1)]
  simp

/-- the `ℓ²`-membership hypothesis of `s7_PID_V_holder` for the mode `e_k` -/
lemma S7PIDI_memℓp_fc (m : ℝ) (k : NonzeroLattice d) :
    Memℓp (fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-(m - 1)) *
      NegSobolev.fourierCoeff (modeVec m k) j) 2 := by
  simp only [S7PIDI_fc_mode]
  exact S7PIDI_memℓp_mode (m - 1) k

/-- the `E_σ`-norm of the element of `E_σ` with coefficients `δ_k` is `⟨k⟩^{-σ}` -/
lemma S7PIDI_norm_mode (σ : ℝ) (k : NonzeroLattice d) :
    ‖(NegSobolev.ofSeq σ (fun j : NonzeroLattice d => if j = k then (1 : ℝ) else 0) : NegSobolev d σ)‖ =
      Lattice.jp k.1 ^ (-σ) := by
  obtain ⟨-, hn⟩ := S7PIDV.S7PIDV_norm_ofSeq_sq (σ := σ)
    (fun j : NonzeroLattice d => if j = k then (1 : ℝ) else 0) (S7PIDI_memℓp_mode σ k)
  have h2 : ‖(NegSobolev.ofSeq σ (fun j : NonzeroLattice d => if j = k then (1 : ℝ) else 0) :
      NegSobolev d σ)‖ ^ 2 = (Lattice.jp k.1 ^ (-σ)) ^ 2 := by
    rw [hn, tsum_eq_single k]
    · simp
    · intro j hj
      simp [hj]
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (Torus.jp_pos k.1).le _) two_ne_zero).1 h2

/-- the `E_m`-norm of the mode vector `e_k` -/
lemma S7PIDI_norm_modeVec (m : ℝ) (k : NonzeroLattice d) :
    ‖modeVec m k‖ = Lattice.jp k.1 ^ (-m) := by
  unfold modeVec
  exact S7PIDI_norm_mode m k

/-- the `E_{m-1}`-norm of the mode vector `e_k` -/
lemma S7PIDI_sobAt_mode (m : ℝ) (k : NonzeroLattice d) :
    sobAt (m - 1) (modeVec m k) = Lattice.jp k.1 ^ (-(m - 1)) := by
  unfold sobAt
  simp only [S7PIDI_fc_mode]
  exact S7PIDI_norm_mode (m - 1) k

/-- `(⟨k⟩^{-σ})² = ⟨k⟩^{-2σ}` -/
lemma S7PIDI_rpow_sq (x : ℝ) (hx : 0 ≤ x) (σ : ℝ) :
    (x ^ (-σ)) ^ 2 = x ^ (-(2 * σ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- the causal kernel at `u ≤ t` -/
lemma S7PIDI_cv_of_le (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m t u : ℝ) (e : NegSobolev d m) (h : u ≤ t) :
    causalVec D ρ m t u e = Vprop D ρ m t u e := by
  unfold causalVec
  rw [if_pos h]

/-- the causal kernel at `u > t` -/
lemma S7PIDI_cv_of_not_le (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m t u : ℝ) (e : NegSobolev d m) (h : ¬ u ≤ t) :
    causalVec D ρ m t u e = 0 := by
  unfold causalVec
  rw [if_neg h]

/-- **D1b (increments of the causal kernel on `I = (c,c']`)**. -/
theorem s7_PID_incr_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (p : ℝ → ℝ) (B : ℝ), Measurable p → (∀ u, |p u| ≤ B) →
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ k : NonzeroLattice d, ∀ s t : ℝ, c ≤ s → s ≤ t → t ≤ c' →
        (∫ u in Set.Ioc c c', ‖p u • causalVec R.D R.ρ m t u (modeVec m k) -
            p u • causalVec R.D R.ρ m s u (modeVec m k)‖ ^ 2) ≤
          K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (t - s) ∧
        (∫ u in Set.Ioc c c', ‖p u • causalVec R.D R.ρ m t u (modeVec m k)‖ ^ 2) ≤
          K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (c' - c) := by
  obtain ⟨k0, hk1, hk2, hk3, -, H⟩ := S7PIDV.S7PIDV_hyp R m hm T hT
  obtain ⟨Am, hAm1, hAmb⟩ := S7PIDV.S7PIDV_finBd_unif H m (k0 + 2) (by omega) (by omega)
    (by push_cast; exact hk2) (by push_cast; linarith)
  have hAm0 : 0 ≤ Am := by linarith
  obtain ⟨L, C, hL, hC, hV⟩ := S7PIDV.s7_PID_V_holder_proof R m hm T hT
  refine ⟨L ^ 2 * T + Am ^ 2, by positivity, fun p B _hp hpB c c' hc hcc' hc'T k s t hcs hst htc' => ?_⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hpB 0)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Lattice.jp k.1 ^ (-(2 * (m - 1))) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  rw [← hQdef]
  have htT : t ≤ T := htc'.trans hc'T
  have hsT : s ≤ T := hst.trans htT
  -- the mode vector: norms and the E_{m-1}-norm
  have hsob : sobAt (m - 1) (modeVec m k) ^ 2 = Q := by
    rw [S7PIDI_sobAt_mode, hQdef, S7PIDI_rpow_sq _ (Torus.jp_pos k.1).le]
  have hnorm_le : ‖modeVec m k‖ ≤ sobAt (m - 1) (modeVec m k) := by
    rw [S7PIDI_norm_modeVec, S7PIDI_sobAt_mode]
    exact Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k.1) (by linarith)
  have hne2 : ‖modeVec m k‖ ^ 2 ≤ Q :=
    calc ‖modeVec m k‖ ^ 2 ≤ sobAt (m - 1) (modeVec m k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
      _ = Q := hsob
  -- the uniform bound of `V^{t,u}` on `E_m` and the Hölder bound of the difference
  have hVb : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ T →
      ‖Vprop R.D R.ρ m t' u (modeVec m k)‖ ≤ Am * ‖modeVec m k‖ := fun u t' hu hut htT' =>
    HRS.MC.Sec7.PIE.pie_Vbound_of_finBd R.D R.ρ m t' u hAm0 (hAmb u t' hu hut htT') (modeVec m k)
  have hVd : ∀ u s' t' : ℝ, 0 ≤ u → u ≤ s' → s' ≤ t' → t' ≤ T →
      ‖Vprop R.D R.ρ m t' u (modeVec m k) - Vprop R.D R.ρ m s' u (modeVec m k)‖ ≤
        L * (t' - s') ^ (1 / 2 : ℝ) * sobAt (m - 1) (modeVec m k) := fun u s' t' hu hus hst' htT' =>
    (hV u s' t' hu hus hst' htT' (modeVec m k) (S7PIDI_memℓp_fc m k)).1
  have hsmul : ∀ (x : NegSobolev d m) (q : ℝ), ‖q • x‖ = |q| * ‖x‖ := fun x q => by
    rw [norm_smul, Real.norm_eq_abs]
  -- the constants of the two integrals
  have hD0 : 0 ≤ B ^ 2 * Am ^ 2 * Q := mul_nonneg (mul_nonneg (sq_nonneg B) (sq_nonneg Am)) hQ0
  have hA0 : 0 ≤ B ^ 2 * (L ^ 2 * (t - s)) * Q :=
    mul_nonneg (mul_nonneg (sq_nonneg B) (mul_nonneg (sq_nonneg L) (by linarith))) hQ0
  -- pointwise bound of the kernel `p u • V^{t,u} e` on `u ∈ (c,c']`, `u ≤ t`
  have hDb : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ T →
      ‖p u • Vprop R.D R.ρ m t' u (modeVec m k)‖ ^ 2 ≤ B ^ 2 * Am ^ 2 * Q := by
    intro u t' hu hut htT'
    rw [hsmul]
    have h1 : |p u| * ‖Vprop R.D R.ρ m t' u (modeVec m k)‖ ≤ B * (Am * ‖modeVec m k‖) :=
      mul_le_mul (hpB u) (hVb u t' hu hut htT') (norm_nonneg _) hB0
    calc (|p u| * ‖Vprop R.D R.ρ m t' u (modeVec m k)‖) ^ 2 ≤ (B * (Am * ‖modeVec m k‖)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) h1 2
      _ = B ^ 2 * Am ^ 2 * ‖modeVec m k‖ ^ 2 := by ring
      _ ≤ B ^ 2 * Am ^ 2 * Q := mul_le_mul_of_nonneg_left hne2 (by positivity)
  -- second conclusion: pointwise bound on `Ioc c c'`
  have hD2 : ∀ u ∈ Set.Ioc c c',
      ‖p u • causalVec R.D R.ρ m t u (modeVec m k)‖ ^ 2 ≤ B ^ 2 * Am ^ 2 * Q := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hc hu.1.le
    by_cases hut : u ≤ t
    · rw [S7PIDI_cv_of_le R.D R.ρ m t u (modeVec m k) hut]
      exact hDb u t hu0 hut htT
    · rw [S7PIDI_cv_of_not_le R.D R.ρ m t u (modeVec m k) hut, smul_zero, norm_zero]
      simpa using hD0
  -- first conclusion: pointwise bound by a constant plus an indicator of `(s,t]`
  have hpt1 : ∀ u ∈ Set.Ioc c c',
      ‖p u • causalVec R.D R.ρ m t u (modeVec m k) - p u • causalVec R.D R.ρ m s u (modeVec m k)‖ ^ 2 ≤
        B ^ 2 * (L ^ 2 * (t - s)) * Q + (Set.Ioc s t).indicator (fun _ => B ^ 2 * Am ^ 2 * Q) u := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hc hu.1.le
    by_cases hus : u ≤ s
    · have hut : u ≤ t := hus.trans hst
      rw [S7PIDI_cv_of_le R.D R.ρ m t u (modeVec m k) hut,
        S7PIDI_cv_of_le R.D R.ρ m s u (modeVec m k) hus, ← smul_sub, hsmul]
      have hind : u ∉ Set.Ioc s t := fun h => absurd hus (not_le.2 h.1)
      rw [Set.indicator_of_notMem hind, add_zero]
      have hY := hVd u s t hu0 hus hst htT
      have h1 : |p u| * ‖Vprop R.D R.ρ m t u (modeVec m k) - Vprop R.D R.ρ m s u (modeVec m k)‖ ≤
          B * (L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) (modeVec m k)) :=
        mul_le_mul (hpB u) hY (norm_nonneg _) hB0
      have hr2 : ((t - s) ^ (1 / 2 : ℝ)) ^ 2 = t - s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
      calc (|p u| * ‖Vprop R.D R.ρ m t u (modeVec m k) - Vprop R.D R.ρ m s u (modeVec m k)‖) ^ 2
          ≤ (B * (L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) (modeVec m k))) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) h1 2
        _ = B ^ 2 * L ^ 2 * ((t - s) ^ (1 / 2 : ℝ)) ^ 2 * sobAt (m - 1) (modeVec m k) ^ 2 := by ring
        _ = B ^ 2 * (L ^ 2 * (t - s)) * Q := by rw [hr2, hsob]; ring
    · have hsu : s < u := lt_of_not_ge hus
      rw [S7PIDI_cv_of_not_le R.D R.ρ m s u (modeVec m k) hus, smul_zero, sub_zero]
      by_cases hut : u ≤ t
      · rw [S7PIDI_cv_of_le R.D R.ρ m t u (modeVec m k) hut,
          Set.indicator_of_mem (show u ∈ Set.Ioc s t from ⟨hsu, hut⟩)]
        have := hDb u t hu0 hut htT
        linarith
      · rw [S7PIDI_cv_of_not_le R.D R.ρ m t u (modeVec m k) hut, smul_zero, norm_zero,
          Set.indicator_of_notMem (show u ∉ Set.Ioc s t from fun h => hut h.2), add_zero]
        calc (0 : ℝ) ^ 2 = 0 := by norm_num
          _ ≤ B ^ 2 * (L ^ 2 * (t - s)) * Q := hA0
  -- the integrals of the majorant on `Ioc c c'`
  have hlen : volume.real (Set.Ioc c c') = c' - c := Real.volume_real_Ioc_of_le hcc'
  have hi1 : Integrable (fun _ : ℝ => B ^ 2 * (L ^ 2 * (t - s)) * Q) (volume.restrict (Set.Ioc c c')) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hi2 : Integrable ((Set.Ioc s t).indicator (fun _ : ℝ => B ^ 2 * Am ^ 2 * Q))
      (volume.restrict (Set.Ioc c c')) :=
    (integrableOn_const (C := B ^ 2 * Am ^ 2 * Q) measure_Ioc_lt_top.ne).indicator measurableSet_Ioc
  have hind : (volume.restrict (Set.Ioc c c')).real (Set.Ioc s t) = t - s := by
    simp only [measureReal_def]
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 (Set.Ioc_subset_Ioc hcs htc'),
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have hcalc1 : ∫ u in Set.Ioc c c', (B ^ 2 * (L ^ 2 * (t - s)) * Q +
      (Set.Ioc s t).indicator (fun _ => B ^ 2 * Am ^ 2 * Q) u) =
      B ^ 2 * (L ^ 2 * (t - s)) * Q * (c' - c) + B ^ 2 * Am ^ 2 * Q * (t - s) := by
    rw [integral_add hi1 hi2, setIntegral_const, integral_indicator_const _ measurableSet_Ioc, hind,
      hlen, smul_eq_mul, smul_eq_mul]
    ring
  have hconst : ∫ _ in Set.Ioc c c', B ^ 2 * Am ^ 2 * Q = (c' - c) * (B ^ 2 * Am ^ 2 * Q) := by
    rw [setIntegral_const, hlen, smul_eq_mul, mul_comm]
  -- first conclusion
  have hint1 : ∫ u in Set.Ioc c c', ‖p u • causalVec R.D R.ρ m t u (modeVec m k) -
      p u • causalVec R.D R.ρ m s u (modeVec m k)‖ ^ 2 ≤
      ∫ u in Set.Ioc c c', (B ^ 2 * (L ^ 2 * (t - s)) * Q +
        (Set.Ioc s t).indicator (fun _ => B ^ 2 * Am ^ 2 * Q) u) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) (hi1.add hi2)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hpt1 u hu))
  -- second conclusion
  have hint2 : ∫ u in Set.Ioc c c', ‖p u • causalVec R.D R.ρ m t u (modeVec m k)‖ ^ 2 ≤
      ∫ _ in Set.Ioc c c', B ^ 2 * Am ^ 2 * Q :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
      (integrableOn_const (C := B ^ 2 * Am ^ 2 * Q) measure_Ioc_lt_top.ne)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hD2 u hu))
  have hK0 : (0 : ℝ) ≤ L ^ 2 * T + Am ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · refine le_trans hint1 (le_trans (le_of_eq hcalc1) ?_)
    have h3 : 0 ≤ B ^ 2 * (L ^ 2 * (t - s)) * Q * (T - (c' - c)) :=
      mul_nonneg hA0 (by linarith)
    nlinarith [h3]
  · refine le_trans hint2 (le_trans (le_of_eq hconst) ?_)
    have h4 : 0 ≤ L ^ 2 * T * B ^ 2 * Q * (c' - c) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg L) hT.le) (sq_nonneg B)) hQ0)
        (by linarith)
    nlinarith [h4]

end HRS.MC.Sec7.S7PIDI

end
