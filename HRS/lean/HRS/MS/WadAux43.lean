import HRS.MS.WadAux42

/-!
# S8.3, packet D8 (Route A), part 2: the extension of `U_t` from `C_c^∞` to `C_M`

`s85_Ulim a β ρβ M t f x = lim_n U_t φ_n (x)` for any approximating sequence `φ_n → f` in `C_M`
(`S85Approx`).  `s85_Ulim_spec`: independence of the sequence; `s85_Ulim_bound`: Lipschitz in the weighted
sup norm; `s85_Ulim_cc`, `s85_Ulim_lin`, `s85_Ulim_memCM`, `s85_Ulim_zero`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Standing hypotheses of the extension. -/
def S85Hyp (d : ℕ) (a β T M : ℝ) (ρβ : Euc d → ℝ) : Prop :=
  2 ≤ d ∧ 0 < a ∧ 0 < β ∧ 0 < T ∧ 0 ≤ M ∧ IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ

open Classical in
/-- The extension of `U_t`: limit of `U_t φ_n` along an approximating sequence (`0` if none exists). -/
def s85_Ulim (a β : ℝ) (ρβ : Euc d → ℝ) (M t : ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  if h : ∃ φ : ℕ → Euc d → ℝ, S85Approx M f φ then
    limUnder atTop (fun n => s85_Ucc a β ρβ t (h.choose n) x)
  else 0

theorem s85_wt_trans {M C₁ C₂ : ℝ} {f g h : Euc d → ℝ} (h1 : Wt M C₁ (fun y => f y - g y))
    (h2 : Wt M C₂ (fun y => g y - h y)) : Wt M (C₁ + C₂) (fun y => f y - h y) := fun y => by
  have a1 := h1 y
  have a2 := h2 y
  show ‖f y - h y‖ ≤ (C₁ + C₂) * jbracket y ^ M
  have e : f y - h y = (f y - g y) + (g y - h y) := by ring
  rw [e]
  calc ‖(f y - g y) + (g y - h y)‖ ≤ ‖f y - g y‖ + ‖g y - h y‖ := norm_add_le _ _
    _ ≤ C₁ * jbracket y ^ M + C₂ * jbracket y ^ M := add_le_add a1 a2
    _ = (C₁ + C₂) * jbracket y ^ M := by ring

theorem s85_wt_symm {M C : ℝ} {f g : Euc d → ℝ} (h : Wt M C (fun y => f y - g y)) :
    Wt M C (fun y => g y - f y) := fun y => by
  show ‖g y - f y‖ ≤ C * jbracket y ^ M
  rw [norm_sub_rev]
  exact h y

theorem s85_wt_comb {M C₁ C₂ c : ℝ} {f f' g g' : Euc d → ℝ} (h1 : Wt M C₁ (fun y => f y - f' y))
    (h2 : Wt M C₂ (fun y => g y - g' y)) :
    Wt M (|c| * C₁ + C₂) (fun y => (c * f y + g y) - (c * f' y + g' y)) := fun y => by
  show ‖(c * f y + g y) - (c * f' y + g' y)‖ ≤ (|c| * C₁ + C₂) * jbracket y ^ M
  have a1 := h1 y
  have a2 := h2 y
  have e : (c * f y + g y) - (c * f' y + g' y) = c * (f y - f' y) + (g y - g' y) := by ring
  rw [e]
  calc ‖c * (f y - f' y) + (g y - g' y)‖ ≤ ‖c * (f y - f' y)‖ + ‖g y - g' y‖ := norm_add_le _ _
    _ ≤ |c| * (C₁ * jbracket y ^ M) + C₂ * jbracket y ^ M := by
        refine add_le_add ?_ a2
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left a1 (abs_nonneg c)
    _ = (|c| * C₁ + C₂) * jbracket y ^ M := by ring

theorem s85_approx_cauchy {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {f : Euc d → ℝ} {φ : ℕ → Euc d → ℝ} (hφ : S85Approx M f φ)
    (x : Euc d) : ∃ L, Tendsto (fun n => s85_Ucc a β ρβ t (φ n) x) atTop (𝓝 L) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := H
  obtain ⟨K, hK0, hK⟩ := s85_Ucc_bound hd ha hβ hT hM hρ
  obtain ⟨hcc, C, hC0, hC⟩ := hφ
  have hJ0 : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0
    (fun N : ℕ => 2 * K * C * jbracket x ^ M * (1 / ((N : ℝ) + 1))) ?_ ?_)
  · intro n m N hn hm
    rw [Real.dist_eq]
    have h1 := hK ht0 htT (hcc n) (hcc m) (s85_wt_trans (hC n) (s85_wt_symm (hC m))) x
    have hn' : C / ((n : ℝ) + 1) ≤ C / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hC0 (by positivity)
        (by have : (N : ℝ) ≤ n := by exact_mod_cast hn
            linarith)
    have hm' : C / ((m : ℝ) + 1) ≤ C / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hC0 (by positivity)
        (by have : (N : ℝ) ≤ m := by exact_mod_cast hm
            linarith)
    calc _ ≤ K * (C / ((n : ℝ) + 1) + C / ((m : ℝ) + 1)) * jbracket x ^ M := h1
      _ ≤ K * (C / ((N : ℝ) + 1) + C / ((N : ℝ) + 1)) * jbracket x ^ M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hn' hm') hK0) hJ0
      _ = 2 * K * C * jbracket x ^ M * (1 / ((N : ℝ) + 1)) := by ring
  · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (2 * K * C * jbracket x ^ M)
    simpa using this

theorem s85_approx_unique {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {f : Euc d → ℝ} {φ ψ : ℕ → Euc d → ℝ} (hφ : S85Approx M f φ)
    (hψ : S85Approx M f ψ) (x : Euc d) {L L' : ℝ}
    (hL : Tendsto (fun n => s85_Ucc a β ρβ t (φ n) x) atTop (𝓝 L))
    (hL' : Tendsto (fun n => s85_Ucc a β ρβ t (ψ n) x) atTop (𝓝 L')) : L = L' := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := H
  obtain ⟨K, hK0, hK⟩ := s85_Ucc_bound hd ha hβ hT hM hρ
  obtain ⟨hcc, C, hC0, hC⟩ := hφ
  obtain ⟨hcc', C', hC0', hC'⟩ := hψ
  have hlim0 : Tendsto (fun n : ℕ => K * (C + C') * jbracket x ^ M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K * (C + C') * jbracket x ^ M)
  have h0 : Tendsto (fun n => s85_Ucc a β ρβ t (φ n) x - s85_Ucc a β ρβ t (ψ n) x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hlim0
    rw [Real.norm_eq_abs]
    have h1 := hK ht0 htT (hcc n) (hcc' n) (s85_wt_trans (hC n) (s85_wt_symm (hC' n))) x
    calc _ ≤ K * (C / ((n : ℝ) + 1) + C' / ((n : ℝ) + 1)) * jbracket x ^ M := h1
      _ = K * (C + C') * jbracket x ^ M * (1 / ((n : ℝ) + 1)) := by ring
  have := tendsto_nhds_unique (hL.sub hL') h0
  linarith

theorem s85_Ulim_spec {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {f : Euc d → ℝ} {φ : ℕ → Euc d → ℝ} (hφ : S85Approx M f φ)
    (x : Euc d) :
    Tendsto (fun n => s85_Ucc a β ρβ t (φ n) x) atTop (𝓝 (s85_Ulim a β ρβ M t f x)) := by
  classical
  have h : ∃ φ : ℕ → Euc d → ℝ, S85Approx M f φ := ⟨φ, hφ⟩
  have hch := h.choose_spec
  obtain ⟨L₀, hL₀⟩ := s85_approx_cauchy H ht0 htT hch x
  obtain ⟨L, hL⟩ := s85_approx_cauchy H ht0 htT hφ x
  have hEq : L₀ = L := s85_approx_unique H ht0 htT hch hφ x hL₀ hL
  have : s85_Ulim a β ρβ M t f x = L₀ := by
    unfold s85_Ulim
    rw [dif_pos h]
    exact hL₀.limUnder_eq
  rw [this, hEq]
  exact hL

/-- **Lipschitz estimate for the extension.** -/
theorem s85_Ulim_bound {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {f g : Euc d → ℝ}, 0 ≤ t → t ≤ T → MemCM M f → MemCM M g →
      Wt M Φ (fun y => f y - g y) → ∀ x : Euc d,
        |s85_Ulim a β ρβ M t f x - s85_Ulim a β ρβ M t g x| ≤ K * Φ * jbracket x ^ M := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨K, hK0, hK⟩ := s85_Ucc_bound hd ha hβ hT hM hρ
  refine ⟨K, hK0, fun {t Φ f g} ht0 htT hf hg hΦ x => ?_⟩
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  obtain ⟨ψ, hψ⟩ := s85_exists_approx hM hg
  have sφ := s85_Ulim_spec H ht0 htT hφ x
  have sψ := s85_Ulim_spec H ht0 htT hψ x
  obtain ⟨hcφ, C₁, hC₁0, hC₁⟩ := hφ
  obtain ⟨hcψ, C₂, hC₂0, hC₂⟩ := hψ
  have hb : ∀ n : ℕ, |s85_Ucc a β ρβ t (φ n) x - s85_Ucc a β ρβ t (ψ n) x| ≤
      K * (C₁ * (1 / ((n : ℝ) + 1)) + (Φ + C₂ * (1 / ((n : ℝ) + 1)))) * jbracket x ^ M := fun n => by
    have := hK ht0 htT (hcφ n) (hcψ n)
      (s85_wt_trans (hC₁ n) (s85_wt_trans hΦ (s85_wt_symm (hC₂ n)))) x
    simpa only [mul_one_div] using this
  have hlim : Tendsto (fun n : ℕ => K * (C₁ * (1 / ((n : ℝ) + 1)) + (Φ + C₂ * (1 / ((n : ℝ) + 1)))) *
      jbracket x ^ M) atTop (𝓝 (K * (C₁ * 0 + (Φ + C₂ * 0)) * jbracket x ^ M)) := by
    have e := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact (((e.const_mul C₁).add (tendsto_const_nhds.add (e.const_mul C₂))).const_mul K).mul_const _
  have := le_of_tendsto_of_tendsto' ((sφ.sub sψ).abs) hlim hb
  simpa using this

theorem s85_Ulim_cc {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {φ : Euc d → ℝ} (hφ : S85Cc φ) (x : Euc d) :
    s85_Ulim a β ρβ M t φ x = s85_Ucc a β ρβ t φ x := by
  have hA : S85Approx M φ (fun _ => φ) :=
    ⟨fun _ => hφ, 0, le_rfl, fun n y => by
      show ‖φ y - φ y‖ ≤ 0 / ((n : ℝ) + 1) * jbracket y ^ M
      simp⟩
  have := s85_Ulim_spec H ht0 htT hA x
  exact tendsto_nhds_unique this tendsto_const_nhds

theorem s85_Ulim_lin {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {f g : Euc d → ℝ} (hf : MemCM M f) (hg : MemCM M g) (c : ℝ) (x : Euc d) :
    s85_Ulim a β ρβ M t (fun y => c * f y + g y) x =
      c * s85_Ulim a β ρβ M t f x + s85_Ulim a β ρβ M t g x := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  obtain ⟨ψ, hψ⟩ := s85_exists_approx hM hg
  have sφ := s85_Ulim_spec H ht0 htT hφ x
  have sψ := s85_Ulim_spec H ht0 htT hψ x
  obtain ⟨hcφ, C₁, hC₁0, hC₁⟩ := hφ
  obtain ⟨hcψ, C₂, hC₂0, hC₂⟩ := hψ
  have hχ : S85Approx M (fun y => c * f y + g y) (fun n y => c * φ n y + ψ n y) := by
    refine ⟨fun n => s85_Cc_lin (hcφ n) (hcψ n), |c| * C₁ + C₂, by positivity, fun n => ?_⟩
    have := s85_wt_comb (c := c) (hC₁ n) (hC₂ n)
    have e : (|c| * C₁ + C₂) / ((n : ℝ) + 1) = |c| * (C₁ / ((n : ℝ) + 1)) + C₂ / ((n : ℝ) + 1) := by
      ring
    rw [e]
    exact this
  have sχ := s85_Ulim_spec H ht0 htT hχ x
  have hlin : Tendsto (fun n => s85_Ucc a β ρβ t (fun y => c * φ n y + ψ n y) x) atTop
      (𝓝 (c * s85_Ulim a β ρβ M t f x + s85_Ulim a β ρβ M t g x)) := by
    refine ((sφ.const_mul c).add sψ).congr fun n => ?_
    exact (s85_Ucc_lin hd ha hβ hρ ht0 (hcφ n) (hcψ n) x).symm
  exact tendsto_nhds_unique sχ hlin

theorem s85_Ulim_zero_fun {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) (x : Euc d) : s85_Ulim a β ρβ M t (fun _ => 0) x = 0 := by
  have hz : MemCM M (fun _ : Euc d => (0 : ℝ)) := by
    refine ⟨continuous_const, ?_⟩
    simpa using tendsto_const_nhds (x := (0 : ℝ)) (f := cocompact (Euc d))
  have := s85_Ulim_lin H ht0 htT hz hz 1 x
  have e : (fun y : Euc d => (1 : ℝ) * (fun _ : Euc d => (0 : ℝ)) y + (fun _ : Euc d => (0 : ℝ)) y) =
      fun _ => 0 := by funext y; simp
  rw [e] at this
  linarith

/-- Generic: weighted uniform limits of `C_M` functions are in `C_M`. -/
theorem s85_memCM_of_approx {M : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} {g : ℕ → Euc d → ℝ} {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hg : ∀ n, MemCM M (g n))
    (hw : ∀ n, Wt M (e n) (fun y => g n y - f y)) : MemCM M f := by
  have he0 : ∀ n, 0 ≤ e n := fun n => (hw n).nonneg
  refine ⟨?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x₀
    apply continuousAt_of_locally_uniform_approx_of_continuousAt
    intro u hu
    obtain ⟨δ, hδ, hδu⟩ := Metric.mem_uniformity_dist.1 hu
    set Λ : ℝ := (3 * jbracket x₀) ^ M with hΛ
    have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg (by have := s83_jb_pos x₀; positivity) _
    have hev := he.eventually (gt_mem_nhds (show (0 : ℝ) < δ / (Λ + 1) by positivity))
    obtain ⟨n, hn⟩ := hev.exists
    refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ one_pos, g n, (hg n).1.continuousAt,
      fun y hy => hδu ?_⟩
    rw [Real.dist_eq]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hjy : jbracket y ^ M ≤ Λ :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_three hy) hM
    have h1 := hw n y
    rw [Real.norm_eq_abs] at h1
    have h2 : |f y - g n y| = |g n y - f y| := abs_sub_comm _ _
    rw [h2]
    have h3 : e n * Λ < δ := by
      have := (lt_div_iff₀ (show (0 : ℝ) < Λ + 1 by positivity)).1 hn
      nlinarith [he0 n]
    calc |g n y - f y| ≤ e n * jbracket y ^ M := h1
      _ ≤ e n * Λ := mul_le_mul_of_nonneg_left hjy (he0 n)
      _ < δ := h3
  · refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists
    have hgn := Metric.tendsto_nhds.1 (hg n).2 (ε / 2) (by positivity)
    filter_upwards [hgn] with x hx
    rw [Real.dist_eq, sub_zero] at hx ⊢
    have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    have h1 := hw n x
    rw [Real.norm_eq_abs] at h1
    have e1 : f x / jbracket x ^ M = g n x / jbracket x ^ M - (g n x - f x) / jbracket x ^ M := by
      rw [← sub_div]; congr 1; ring
    have h4 : |(g n x - f x) / jbracket x ^ M| ≤ e n := by
      rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
      exact h1
    rw [e1]
    calc |g n x / jbracket x ^ M - (g n x - f x) / jbracket x ^ M|
        ≤ |g n x / jbracket x ^ M| + |(g n x - f x) / jbracket x ^ M| := abs_sub _ _
      _ < ε := by linarith

end HRS.MS.Wad
