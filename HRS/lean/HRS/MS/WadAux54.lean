import HRS.MS.WadAux53

/-!
# S8.3, packet S8D-1, part 4: positive-time `C^{1,1/2}` smoothing of the weighted semigroup

`s8d_smoothing`: for `0 < t ≤ T`, `f ∈ C_M` with `|f| ≤ Φ⟨x⟩^M`, the extension `U_t f = s85_Ulim … t f` lies in
`C_M^1` (`MemCMj M 1`), with `‖D U_t f(y)‖ ≤ K Φ t^{-3/4} ⟨y⟩^M` and the weighted `1/2`-Hölder bound for `D U_t f`
(`K` independent of `t, Φ, f`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_decay_of_wt {M M' B : ℝ} (hM : M' < M) {E : Type*} [NormedAddCommGroup E] {h : Euc d → E}
    (hw : ∀ x, ‖h x‖ ≤ B * jbracket x ^ M') :
    Tendsto (fun x => ‖h x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0) := by
  have hexp : Tendsto (fun x : Euc d => jbracket x ^ (-(M - M'))) (cocompact (Euc d)) (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.2 hM)).comp s85_tendsto_jb
  have h1 : Tendsto (fun x : Euc d => B * jbracket x ^ (-(M - M'))) (cocompact (Euc d)) (𝓝 0) := by
    simpa using hexp.const_mul B
  refine squeeze_zero (fun x => ?_) (fun x => ?_) h1
  · exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (s83_jb_pos x).le _)
  · have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    rw [div_le_iff₀ hp]
    have e : jbracket x ^ (-(M - M')) * jbracket x ^ M = jbracket x ^ M' := by
      rw [← Real.rpow_add (s83_jb_pos x)]; congr 1; ring
    calc ‖h x‖ ≤ B * jbracket x ^ M' := hw x
      _ = B * jbracket x ^ (-(M - M')) * jbracket x ^ M := by rw [mul_assoc, e]

theorem s8d_smoothing {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {f : Euc d → ℝ}, 0 < t → t ≤ T → MemCM M f → Wt M Φ f →
      MemCMj M 1 (s85_Ulim a β ρβ M t f) ∧
      (∀ y, ‖fderiv ℝ (s85_Ulim a β ρβ M t f) y‖ ≤ K * Φ * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M) ∧
      ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ (s85_Ulim a β ρβ M t f) x' - fderiv ℝ (s85_Ulim a β ρβ M t f) x‖ ≤
          K * Φ * t ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨K1, hK1, hK1c⟩ := s8d_adm_classical hd ha hβ hT hM hρ
  obtain ⟨K2, hK2, hK2c⟩ := s8d_adm_classical_sub hd ha hβ hT hM hρ
  obtain ⟨K3, hK3, hK3c⟩ := s8d_adm_classical hd ha hβ hT (M := M / 2) (by positivity) hρ
  refine ⟨K1, hK1, ?_⟩
  intro t Φ f ht htT hf hΦ
  have ht0 : 0 ≤ t := ht.le
  have hΦ0 : 0 ≤ Φ := hΦ.nonneg
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  have hφ' := hφ
  obtain ⟨hcc, C, hC0, hC⟩ := hφ'
  choose w hw using fun n => s85_exists_cl hd ha hβ hρ ht0 (hcc n)
  set e : ℕ → ℝ := fun n => C / ((n : ℝ) + 1) with he_def
  have he0 : ∀ n, 0 ≤ e n := fun n => by positivity
  have hea : Antitone e := fun n m hnm =>
    div_le_div_of_nonneg_left hC0 (by positivity) (by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith)
  have he : Tendsto e atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa [e, div_eq_mul_inv] using this
  set p : ℝ := t ^ (-(3 / 4 : ℝ)) with hp_def
  have hp0 : 0 ≤ p := Real.rpow_nonneg ht0 _
  set u : ℕ → Euc d → ℝ := fun n => s85_Ucc a β ρβ t (φ n) with hu_def
  have hu : ∀ n, ContDiff ℝ 1 (u n) := fun n => (s8d_Ucc_C1 hd ha hβ hρ ht0 (hw n)).1
  have hfd : ∀ n y, fderiv ℝ (u n) y = fderiv ℝ (w n 0) y := fun n y =>
    (s8d_Ucc_C1 hd ha hβ hρ ht0 (hw n)).2 y
  have hφn : ∀ n, Wt M (Φ + e n) (φ n) := fun n y => by
    have h1 := hC n y
    have h2 := hΦ y
    have h3 : ‖φ n y‖ ≤ ‖φ n y - f y‖ + ‖f y‖ := by
      have := norm_add_le (φ n y - f y) (f y)
      simpa using this
    have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    nlinarith
  have hdiff : ∀ n m, Wt M (e n + e m) (fun y => φ n y - φ m y) := fun n m =>
    s85_wt_trans (hC n) (s85_wt_symm (hC m))
  have hcau : ∀ n m y, ‖fderiv ℝ (u n) y - fderiv ℝ (u m) y‖ ≤ (e n + e m) * (K2 * p) * jbracket y ^ M :=
    fun n m y => by
      have := (hK2c ht htT (hw n) (hw m) (hφn n) (hφn m) (hdiff n m)).1 y
      rw [hfd, hfd]
      refine this.trans (le_of_eq ?_)
      ring
  have hpt : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (s85_Ulim a β ρβ M t f x)) := fun x =>
    s85_Ulim_spec H ht0 htT hφ x
  obtain ⟨g, hgc, hgd, hglim, hgb⟩ := s8d_limit_C1 hM (mul_nonneg hK2 hp0) he0 hea he hu hpt hcau
  have hfdU : ∀ y, fderiv ℝ (s85_Ulim a β ρβ M t f) y = g y := fun y => (hgd y).fderiv
  -- bounds on `g`
  have hsingle : ∀ n y, ‖fderiv ℝ (u n) y‖ ≤ K1 * (Φ + e n) * p * jbracket y ^ M := fun n y => by
    rw [hfd]
    exact (hK1c ht htT (hw n) (hφn n)).1 y
  have hholder : ∀ n x x', ‖x' - x‖ ≤ 1 / 4 → ‖fderiv ℝ (u n) x' - fderiv ℝ (u n) x‖ ≤
      K1 * (Φ + e n) * p * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := fun n x x' hx => by
    rw [hfd, hfd]
    exact (hK1c ht htT (hw n) (hφn n)).2 x x' hx
  have hlimK : ∀ (A : ℝ), Tendsto (fun n => K1 * (Φ + e n) * p * A) atTop (𝓝 (K1 * Φ * p * A)) := by
    intro A
    have := (((he.const_add Φ).const_mul K1).mul_const p).mul_const A
    simpa using this
  have hbound : ∀ y, ‖g y‖ ≤ K1 * Φ * p * jbracket y ^ M := fun y =>
    le_of_tendsto_of_tendsto' (hglim y).norm (hlimK _) (fun n => hsingle n y)
  have hhold : ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
      ‖g x' - g x‖ ≤ K1 * Φ * p * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := fun x x' hx => by
    have := le_of_tendsto_of_tendsto' ((hglim x').sub (hglim x)).norm
      (hlimK (‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M)) (fun n => by
        have := hholder n x x' hx
        calc _ ≤ _ := this
          _ = _ := by ring)
    calc ‖g x' - g x‖ ≤ K1 * Φ * p * (‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) := this
      _ = _ := by ring
  -- decay of the gradient
  have hdecay_n : ∀ n, Tendsto (fun y => ‖fderiv ℝ (u n) y‖ / jbracket y ^ M) (cocompact (Euc d)) (𝓝 0) :=
    fun n => by
      obtain ⟨Bφ, hBφ⟩ := (hcc n).1.continuous.bounded_above_of_compact_support (hcc n).2
      have hJ : ∀ x : Euc d, 1 ≤ jbracket x ^ (M / 2) := fun x =>
        Real.one_le_rpow (s83_one_le_jb x) (by positivity)
      have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0)
      have hwt : Wt (M / 2) Bφ (φ n) := fun x => (hBφ x).trans (le_mul_of_one_le_right hBφ0 (hJ x))
      refine s8d_decay_of_wt (M' := M / 2) (B := K3 * Bφ * p) (by linarith) (fun y => ?_)
      rw [hfd]
      exact (hK3c ht htT (hw n) hwt).1 y |>.trans (le_of_eq (by ring))
  have hDdec : Tendsto (fun y => ‖g y‖ / jbracket y ^ M) (cocompact (Euc d)) (𝓝 0) := by
    refine s8d_decay_of_approx (g := fun n y => ‖fderiv ℝ (u n) y‖) (h := fun y => ‖g y‖)
      (c := K2 * p) he0 he hdecay_n (fun n x => ?_) (mul_nonneg hK2 hp0)
    have := hgb n x
    calc |‖g x‖ - ‖fderiv ℝ (u n) x‖| ≤ ‖g x - fderiv ℝ (u n) x‖ := abs_norm_sub_norm_le _ _
      _ ≤ _ := this
  have hU1 : ContDiff ℝ 1 (s85_Ulim a β ρβ M t f) := contDiff_one_iff_hasFDerivAt.2 ⟨g, hgc, hgd⟩
  refine ⟨s8d_memCMj1 hU1 (s85_Ulim_memCM H hMpos ht0 htT hf) ?_, fun y => ?_, fun x x' hx => ?_⟩
  · simpa only [hfdU] using hDdec
  · rw [hfdU]; exact hbound y
  · rw [hfdU, hfdU]; exact hhold x x' hx

end HRS.MS.Wad
