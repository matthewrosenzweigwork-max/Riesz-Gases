import HRS.MS.WadAux43

/-!
# S8.3, packet D8 (Route A), part 3: properties of the extension

`s85_approx_dist` (rate of convergence), `s85_Ulim_memCM` (`U_t f ∈ C_M`), `s85_Ulim_at_zero` (`U_0 = id`),
`s85_Ulim_wsup` (the frozen `bdd` clause), `s85_Ulim_classical` (the frozen `classical` clause).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_approx_dist {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {f : Euc d → ℝ} {φ : ℕ → Euc d → ℝ} (hφ : S85Approx M f φ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ (n : ℕ) (x : Euc d),
      |s85_Ucc a β ρβ t (φ n) x - s85_Ulim a β ρβ M t f x| ≤ K * (C / ((n : ℝ) + 1)) * jbracket x ^ M := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨K, hK0, hK⟩ := s85_Ucc_bound hd ha hβ hT hM hρ
  have hφ' := hφ
  obtain ⟨hcc, C, hC0, hC⟩ := hφ'
  refine ⟨K, C, hK0, hC0, fun n x => ?_⟩
  have sp := s85_Ulim_spec H ht0 htT hφ x
  have hb : ∀ m : ℕ, |s85_Ucc a β ρβ t (φ n) x - s85_Ucc a β ρβ t (φ m) x| ≤
      K * (C / ((n : ℝ) + 1) + C * (1 / ((m : ℝ) + 1))) * jbracket x ^ M := fun m => by
    have := hK ht0 htT (hcc n) (hcc m) (s85_wt_trans (hC n) (s85_wt_symm (hC m))) x
    simpa only [mul_one_div] using this
  have e := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim : Tendsto (fun m : ℕ => K * (C / ((n : ℝ) + 1) + C * (1 / ((m : ℝ) + 1))) * jbracket x ^ M)
      atTop (𝓝 (K * (C / ((n : ℝ) + 1) + C * 0) * jbracket x ^ M)) :=
    ((tendsto_const_nhds.add (e.const_mul C)).const_mul K).mul_const _
  have := le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub sp).abs) hlim hb
  simpa using this

theorem s85_Ulim_memCM {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {f : Euc d → ℝ} (hf : MemCM M f) :
    MemCM M (s85_Ulim a β ρβ M t f) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  obtain ⟨K, C, hK0, hC0, hdist⟩ := s85_approx_dist H ht0 htT hφ
  have hgn : ∀ n, MemCM M (s85_Ucc a β ρβ t (φ n)) := fun n => by
    obtain ⟨hc, C', hw⟩ := s85_Ucc_props hd ha hβ hT (M' := M / 2) (by positivity) hρ ht0 htT (hφ.1 n)
    exact s85_cm_of_wt (by linarith) hc hw
  refine s85_memCM_of_approx hM (g := fun n => s85_Ucc a β ρβ t (φ n))
    (e := fun n : ℕ => K * (C / ((n : ℝ) + 1))) ?_ hgn (fun n x => ?_)
  · have e : (fun n : ℕ => K * (C / ((n : ℝ) + 1))) = fun n : ℕ => (K * C) * (1 / ((n : ℝ) + 1)) := by
      funext n; ring
    rw [e]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K * C)
  · show ‖s85_Ucc a β ρβ t (φ n) x - s85_Ulim a β ρβ M t f x‖ ≤ K * (C / ((n : ℝ) + 1)) * jbracket x ^ M
    rw [Real.norm_eq_abs]
    exact hdist n x

theorem s85_Ucc_zero (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {φ : Euc d → ℝ} (hφ : S85Cc φ) (x : Euc d) :
    s85_Ucc a β ρβ 0 φ x = φ x := by
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ (le_refl 0) hφ
  rw [s85_Ucc_eq hd ha hβ hρ le_rfl hw]
  unfold s85_V
  rw [hw.terminal]
  unfold HRS.Whole.pair
  ring

theorem s85_Ulim_at_zero {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {f : Euc d → ℝ}
    (hf : MemCM M f) (x : Euc d) : s85_Ulim a β ρβ M 0 f x = f x := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  have sp := s85_Ulim_spec H le_rfl hT.le hφ x
  have h1 : ∀ n, s85_Ucc a β ρβ 0 (φ n) x = φ n x := fun n => s85_Ucc_zero hd ha hβ hρ (hφ.1 n) x
  obtain ⟨hcc, C, hC0, hC⟩ := hφ
  have hlim0 : Tendsto (fun n : ℕ => C * jbracket x ^ M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (C * jbracket x ^ M)
  have h0 : Tendsto (fun n : ℕ => φ n x - f x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hlim0
    have := hC n x
    rw [Real.norm_eq_abs]
    calc _ ≤ C / ((n : ℝ) + 1) * jbracket x ^ M := by simpa [Real.norm_eq_abs] using this
      _ = C * jbracket x ^ M * (1 / ((n : ℝ) + 1)) := by ring
  have hlim : Tendsto (fun n : ℕ => φ n x) atTop (𝓝 (f x)) := by
    simpa using h0.add_const (f x)
  exact tendsto_nhds_unique (sp.congr h1) hlim

theorem s85_Ulim_wsup {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t : ℝ}, 0 ≤ t → t ≤ T → ∀ {f : Euc d → ℝ}, MemCM M f →
      weightedSupE 0 (-M) (s85_Ulim a β ρβ M t f) ≤ ENNReal.ofReal K * weightedSupE 0 (-M) f := by
  obtain ⟨K, hK0, hK⟩ := s85_Ulim_bound H
  refine ⟨K, hK0, fun {t} ht0 htT {f} hf => ?_⟩
  have hfin : weightedSupE 0 (-M) f ≠ ⊤ := s83_wsup0_ne_top hf
  have hwt := s83_wt_of_memCM hf
  have hS0 : 0 ≤ (weightedSupE 0 (-M) f).toReal := ENNReal.toReal_nonneg
  have hz : MemCM M (fun _ : Euc d => (0 : ℝ)) := by
    refine ⟨continuous_const, ?_⟩
    simpa using tendsto_const_nhds (x := (0 : ℝ)) (f := cocompact (Euc d))
  have hb : Wt M (K * (weightedSupE 0 (-M) f).toReal) (s85_Ulim a β ρβ M t f) := fun x => by
    have := hK ht0 htT hf hz (Φ := (weightedSupE 0 (-M) f).toReal) (fun y => by
      show ‖f y - 0‖ ≤ _
      rw [sub_zero]; exact hwt y) x
    rw [s85_Ulim_zero_fun H ht0 htT, sub_zero] at this
    rwa [Real.norm_eq_abs]
  calc weightedSupE 0 (-M) (s85_Ulim a β ρβ M t f)
      ≤ ENNReal.ofReal (K * (weightedSupE 0 (-M) f).toReal) :=
        (s83_wsup0_le_iff (mul_nonneg hK0 hS0) _).2 hb
    _ = ENNReal.ofReal K * ENNReal.ofReal (weightedSupE 0 (-M) f).toReal := ENNReal.ofReal_mul hK0
    _ = ENNReal.ofReal K * weightedSupE 0 (-M) f := by rw [ENNReal.ofReal_toReal hfin]

theorem s85_Ulim_classical {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {φ : Euc d → ℝ} (hφ : S85Cc φ) :
    ∃ f : ℝ → Euc d → ℝ, IsAdjointSolutionG
      (projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ)) t φ f ∧
      s85_Ulim a β ρβ M t φ = f 0 := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ ht0 hφ
  refine ⟨_, s85_proj_solution hd ha hβ hρ hw, ?_⟩
  funext x
  rw [s85_Ulim_cc H ht0 htT hφ, s85_Ucc_eq hd ha hβ hρ ht0 hw]
  unfold s85_V
  ring

end HRS.MS.Wad
