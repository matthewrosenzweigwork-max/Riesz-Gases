import HRS.MS.WadAux59

/-!
# S8.3, packet S8D-2, part 6: far-field bound of classical solutions at time `0`

`s8d_tail_classical`: for every `ε > 0` there is `R` such that every frozen classical adjoint solution `w` on
`[0,1]` with terminal datum `|φ| ≤ Φ⟨x⟩^M` satisfies `|w_0(x)| ≤ Φ (e^{-aM} + ε) ⟨x⟩^M` for `‖x‖ ≥ R`
(Mehler tail `s83_P_tail_bound` for the free part, `s8d_B_decay` and the Gronwall bounds `s8d_apriori_adm` for the
Duhamel remainder).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s8d_tail_classical (hd : 2 ≤ d) {a β M : ℝ} {ρβ : Euc d → ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ {Φ : ℝ} {φ : Euc d → ℝ} {w : ℝ → Euc d → ℝ},
      IsClassicalAdjointW (critCoeff d a β ρβ) 1 φ w → Wt M Φ φ →
      ∀ x : Euc d, R ≤ ‖x‖ → |w 0 x| ≤ Φ * (Real.exp (-a * M) + ε) * jbracket x ^ M := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hg := s84_thermal_gaussReg hd ha hβ hρ
  have hM := hMpos.le
  obtain ⟨lam, K, hlam, hK0, hK⟩ := s8d_apriori_adm hd ha hν one_pos hM hg
  set K₀ : ℝ := 2 ^ M * mom d M (Real.sqrt (β⁻¹ / a)) with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  set E : ℝ := 8 * Real.exp lam * K with hE
  have hE0 : 0 ≤ E := by positivity
  set ε' : ℝ := ε / (4 * (E * K₀ + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hEε : E * K₀ * ε' ≤ ε / 4 := by
    rw [hε', ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hE0 hK₀0]
  obtain ⟨Cε, hCε0, hCε⟩ := s8d_B_decay hd hg hM hε'0
  obtain ⟨R₁, hR₁⟩ := s83_P_tail_bound (d := d) (E := ℝ) hM ha hν.le (t := 1) zero_le_one
    (ε := ε / 2) (by positivity)
  set N : ℝ := 4 * E * Cε / ε with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨max R₁ (N ^ (1 / M)), ?_⟩
  intro Φ φ w hw hφ x hx
  have hxR₁ : R₁ ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hxN : N ^ (1 / M) ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hΦ0 : 0 ≤ Φ := hφ.nonneg
  have hjx : N ≤ jbracket x ^ M := by
    have h1 : N = (N ^ (1 / M)) ^ M := by
      rw [← Real.rpow_mul hN0, one_div, inv_mul_cancel₀ hMpos.ne', Real.rpow_one]
    calc N = (N ^ (1 / M)) ^ M := h1
      _ ≤ ‖x‖ ^ M := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hxN hM
      _ ≤ jbracket x ^ M := Real.rpow_le_rpow (norm_nonneg _) (s83_norm_le_jb x) hM
  have hjpos : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have sol := s84_sol_of_classical a β ha hβ ρβ one_pos hw hφ
  have hadm := hK one_pos le_rfl sol
  have hφc : Continuous φ := by
    have := (hw.c2 1 h1I).continuous
    rwa [hw.terminal] at this
  -- free part
  have hfree : ‖s83_P a β⁻¹ 1 φ x‖ ≤ Φ * (Real.exp (-a * M * 1) + ε / 2) * jbracket x ^ M :=
    hR₁ x hxR₁ φ Φ hφc hφ
  -- Duhamel part
  have hmild := sol.mild 0 h0I x
  rw [hw.terminal, sub_zero] at hmild
  set Θ : ℝ := K * Φ with hΘ
  have hΘ0 : 0 ≤ Θ := mul_nonneg hK0 hΦ0
  set Q : ℝ := ε' * K₀ * jbracket x ^ M + Cε with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set g : ℝ → ℝ := fun s => (2 * Θ * Real.exp lam * Q) * (1 - s) ^ (-(3 / 4 : ℝ)) with hgdef
  have hgi : IntervalIntegrable g volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - 0) (r := -(3 / 4 : ℝ))
      (by norm_num)).comp_sub_left 1
    have h2 : IntervalIntegrable (fun s : ℝ => (1 - s) ^ (-(3 / 4 : ℝ))) volume 0 1 := by
      simpa using this.symm
    exact h2.const_mul _
  have hsrc : ‖∫ s in (0 : ℝ)..1, s83_P a β⁻¹ (s - 0) (fun y => s84_Bop ρβ (w s) y) x‖ ≤
      ∫ s in (0 : ℝ)..1, g s := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hgi
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem (volume : Measure ℝ)] with s hs1 hs
    have hs' : s ∈ Set.Ico (0 : ℝ) 1 := ⟨hs.1.le, lt_of_le_of_ne hs.2 hs1⟩
    have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hw0 := s84_wt_nonneg lam 1 s hs.2
    obtain ⟨h1, h2⟩ := hadm s hs'
    have hV : 0 ≤ Θ * s84_wt lam 1 s := mul_nonneg hΘ0 hw0
    have hB := hCε (h := w s) (V := Θ * s84_wt lam 1 s) (H := Θ * s84_wt lam 1 s) hV hV h1 h2
    have hqc := s84_sol_qcont sol hsI
    have hP := s8d_P_abs_le (g := fun y => s84_Bop ρβ (w s) y) (M := M)
      (α := (Θ * s84_wt lam 1 s + Θ * s84_wt lam 1 s) * ε') (γ := (Θ * s84_wt lam 1 s + Θ * s84_wt lam 1 s) * Cε)
      hM (by positivity) (by positivity) (fun y => by
        refine (hB y).trans (le_of_eq ?_); ring) ha hν.le (sub_nonneg.2 hs.1.le) x
    rw [Real.norm_eq_abs]
    refine hP.trans ?_
    have hexp : Real.exp (lam * (1 - s)) ≤ Real.exp lam := by
      apply Real.exp_le_exp.2
      nlinarith [hs.1, hlam]
    have hts : 0 ≤ (1 - s) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith [hs.2]) _
    have hwle : s84_wt lam 1 s ≤ Real.exp lam * (1 - s) ^ (-(3 / 4 : ℝ)) := by
      unfold s84_wt
      exact mul_le_mul_of_nonneg_right hexp hts
    have e1 : (Θ * s84_wt lam 1 s + Θ * s84_wt lam 1 s) * ε' * K₀ * jbracket x ^ M +
        (Θ * s84_wt lam 1 s + Θ * s84_wt lam 1 s) * Cε =
        (2 * Θ * s84_wt lam 1 s) * Q := by rw [hQ]; ring
    have e2 : (Θ * s84_wt lam 1 s + Θ * s84_wt lam 1 s) * ε' * (2 ^ M * mom d M (Real.sqrt (β⁻¹ / a))) *
        jbracket x ^ M + (Θ * s84_wt lam 1 s + Θ * s84_wt lam 1 s) * Cε =
        (2 * Θ * s84_wt lam 1 s) * Q := by rw [hQ, hK₀]; ring
    rw [e2]
    calc (2 * Θ * s84_wt lam 1 s) * Q ≤ (2 * Θ * (Real.exp lam * (1 - s) ^ (-(3 / 4 : ℝ)))) * Q := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwle (by positivity)) hQ0
      _ = g s := by rw [hgdef]; ring
  have hgint : ∫ s in (0 : ℝ)..1, g s = (2 * Θ * Real.exp lam * Q) * 4 := by
    rw [hgdef, intervalIntegral.integral_const_mul]
    congr 1
    have := s84_int_t_sub (r := 0) (t := 1) zero_le_one
    simpa using this
  -- assemble
  have hdu : |∫ s in (0 : ℝ)..1, s83_P a β⁻¹ (s - 0) (fun y => s84_Bop ρβ (w s) y) x| ≤
      E * Φ * Q := by
    rw [← Real.norm_eq_abs]
    refine hsrc.trans ?_
    rw [hgint, hE, hΘ]
    apply le_of_eq; ring
  have hexp1 : Real.exp (-a * M * 1) = Real.exp (-a * M) := by rw [mul_one]
  rw [hmild]
  refine (abs_add_le _ _).trans ?_
  rw [← Real.norm_eq_abs (s83_P a β⁻¹ 1 φ x)]
  have hc1 : E * Φ * Cε ≤ ε / 4 * (Φ * jbracket x ^ M) := by
    have : E * Cε ≤ ε / 4 * jbracket x ^ M := by
      have h2 : N * (ε / 4) ≤ jbracket x ^ M * (ε / 4) := mul_le_mul_of_nonneg_right hjx (by positivity)
      have h3 : N * (ε / 4) = E * Cε := by rw [hN]; field_simp
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hΦ0]
  have hc2 : E * Φ * (ε' * K₀ * jbracket x ^ M) ≤ ε / 4 * (Φ * jbracket x ^ M) := by
    have := mul_le_mul_of_nonneg_right hEε (mul_nonneg hΦ0 hjpos.le)
    nlinarith
  calc _ ≤ Φ * (Real.exp (-a * M * 1) + ε / 2) * jbracket x ^ M + E * Φ * Q :=
        add_le_add hfree hdu
    _ ≤ _ := by
        have hsplit : E * Φ * Q = E * Φ * (ε' * K₀ * jbracket x ^ M) + E * Φ * Cε := by
          rw [hQ]; ring
        rw [hexp1, hsplit]
        linarith [hc1, hc2]

end HRS.MS.Wad
