import HRS.MS.WadAux68

/-!
# S8.3, packet S8D-2, part 15: geometric decay of `U_n P` on `C_M` (clause (2a), integer times)

`s8d_Ulim_shift`: `U_t (g - c) = U_t g - c` (`U_t 1 = 1`).
`s8d_decay_iter`: there are `κ < 1` and `C` such that for every `n : ℕ`, `y ∈ C_M` with `|y| ≤ Φ⟨x⟩^M`:
`|U_n y - μ(y)| ≤ C κ^n Φ ⟨x⟩^M`.  Induction on `n`: the Lasota-Yorke inequality `s8d_LY` for `z_n = U_n y - μ(y)`
(`S z_n = z_{n+1}` by the semigroup law, `U_1 1 = 1`, mean preservation) with the `L²(μ)` decay `s8d_L2_decay`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_Ulim_shift {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {g : Euc d → ℝ} (hg : MemCM M g) (c : ℝ) (x : Euc d) :
    s85_Ulim a β ρβ M t (fun y => g y - c) x = s85_Ulim a β ρβ M t g x - c := by
  have e : (fun y => g y - c) = fun y => (-c) * (fun _ : Euc d => (1 : ℝ)) y + g y := by
    funext y; simp only; ring
  rw [e, s85_Ulim_lin H ht0 htT (s8d_memCM_const hMpos 1) hg (-c) x, s8d_Ulim_one H hMpos ht0 htT x]
  ring

theorem s8d_memCM_sub_const {M : ℝ} (hM : 0 < M) {g : Euc d → ℝ} (hg : MemCM M g) (c : ℝ) :
    MemCM M (fun y => g y - c) :=
  s85_memCM_sub hg (s8d_memCM_const hM c)

theorem s8d_integral_sub_const {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {g : Euc d → ℝ} (hg : Integrable g μ)
    (c : ℝ) : ∫ x, (g x - c) ∂μ = ∫ x, g x ∂μ - c := by
  rw [integral_sub hg (integrable_const c), integral_const]
  simp

theorem s8d_integrable_of_memCM {ρ : Euc d → ℝ} (hP : HRS.Whole.IsProbDensity ρ) (hg : s84_GaussReg ρ) {M : ℝ}
    (hM : 0 ≤ M) {g : Euc d → ℝ} (hg' : MemCM M g) : Integrable g (HRS.Whole.withDensityReal ρ) := by
  have hw := s83_wt_of_memCM hg'
  refine ((s85_jb_integrable hP hg hM).const_mul (weightedSupE 0 (-M) g).toReal).mono'
    hg'.1.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  exact hw x

theorem s8d_sq_integral_le {ρ : Euc d → ℝ} (hP : HRS.Whole.IsProbDensity ρ) (hg : s84_GaussReg ρ) {M : ℝ}
    (hM : 0 ≤ M) {y : Euc d → ℝ} {Φ : ℝ} (hyc : Continuous y) (hΦ : Wt M Φ y) :
    ∫ x, y x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      Φ ^ 2 * ∫ x, (jbracket x ^ M) ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have hj2 := s8d_jb_sq_integrable hP hg hM
  have hb : ∀ x, y x ^ 2 ≤ Φ ^ 2 * (jbracket x ^ M) ^ 2 := fun x => by
    have h1 := hΦ x
    rw [Real.norm_eq_abs] at h1
    calc y x ^ 2 = |y x| ^ 2 := (sq_abs _).symm
      _ ≤ (Φ * jbracket x ^ M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = _ := by ring
  have hi : Integrable (fun x => y x ^ 2) (HRS.Whole.withDensityReal ρ) :=
    (hj2.const_mul (Φ ^ 2)).mono' ((hyc.pow 2).aestronglyMeasurable) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb x)
  calc ∫ x, y x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ ∫ x, Φ ^ 2 * (jbracket x ^ M) ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
        integral_mono hi (hj2.const_mul _) hb
    _ = _ := integral_const_mul _ _

theorem s8d_decay_iter (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) :
    ∃ κ Cc : ℝ, 0 < κ ∧ κ < 1 ∧ 0 ≤ Cc ∧ ∀ (n : ℕ) {y : Euc d → ℝ} {Φ : ℝ}, MemCM M y → Wt M Φ y →
      Wt M (Cc * κ ^ n * Φ) (fun x => s85_Ulim a β ρβ M (n : ℝ) y x -
        ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)) := by
  have hM := hMpos.le
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have HH : ∀ T : ℝ, 0 < T → S85Hyp d a β T M ρβ := fun T hT => ⟨hd, ha, hβ, hT, hM, hρ⟩
  obtain ⟨lam, C0, hlam, hC0, hL2⟩ := s8d_L2_decay (M := M) hd ha hβ hρ
  obtain ⟨θ', C', hθ'0, hθ'1, hC'0, hLY⟩ := s8d_LY hd ha hβ hρ hMpos
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  have hj2 := s8d_jb_sq_integrable hP hg hM
  set mM : ℝ := ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) with hmM
  have hmM0 : 0 ≤ mM := integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  set m2 : ℝ := ∫ z, (jbracket z ^ M) ^ 2 ∂(HRS.Whole.withDensityReal ρβ) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun z => sq_nonneg _
  set q : ℝ := Real.exp (-lam) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; linarith
  set κ : ℝ := (1 + max θ' q) / 2 with hκ
  have hκ1 : κ < 1 := by
    have : max θ' q < 1 := max_lt hθ'1 hq1
    rw [hκ]; linarith
  have hκθ : θ' < κ := by
    have : θ' ≤ max θ' q := le_max_left _ _
    have h2 : max θ' q < 1 := max_lt hθ'1 hq1
    rw [hκ]; linarith
  have hκq : q ≤ κ := by
    have : q ≤ max θ' q := le_max_right _ _
    have h2 : max θ' q < 1 := max_lt hθ'1 hq1
    rw [hκ]; linarith
  have hκ0 : 0 < κ := lt_of_lt_of_le hq0 hκq
  set Cc : ℝ := max (1 + mM) (C' * C0 * Real.sqrt m2 / (κ - θ')) with hCc
  have hCc0 : 0 ≤ Cc := le_max_of_le_left (by linarith)
  have hCcb : C' * C0 * Real.sqrt m2 ≤ Cc * (κ - θ') := by
    have h1 : C' * C0 * Real.sqrt m2 / (κ - θ') ≤ Cc := le_max_right _ _
    rwa [div_le_iff₀ (sub_pos.2 hκθ)] at h1
  refine ⟨κ, Cc, hκ0, hκ1, hCc0, fun n => ?_⟩
  induction n with
  | zero =>
    intro y Φ hy hΦ x
    have hΦ0 := hΦ.nonneg
    have h0 := (s85_exists_semigroup hd ha hβ hρ hMpos).zero y hy
    have e : s85_Ulim a β ρβ M ((0 : ℕ) : ℝ) y = y := by simpa using h0
    rw [e]
    have hc : |∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤ Φ * mM := by
      have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := y)
        (bd := fun z => Φ * jbracket z ^ M) (hjint.const_mul Φ) (fun z => by
          have := hΦ z; rwa [Real.norm_eq_abs] at this)
      rwa [integral_const_mul] at this
    have hjx := Real.one_le_rpow (s83_one_le_jb x) hM
    rw [Real.norm_eq_abs]
    have h1 := hΦ x
    rw [Real.norm_eq_abs] at h1
    have h2 : |y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤ |y x| + |∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| :=
      abs_sub _ _
    have hCc1 : 1 + mM ≤ Cc := le_max_left _ _
    simp only [pow_zero, mul_one]
    nlinarith [mul_nonneg hΦ0 hmM0, mul_le_mul_of_nonneg_right hCc1 (mul_nonneg hΦ0 (Real.rpow_nonneg (s83_jb_pos x).le M))]
  | succ n ih =>
    intro y Φ hy hΦ x
    have hΦ0 := hΦ.nonneg
    have ih' := ih hy hΦ
    have Hn : S85Hyp d a β ((n : ℝ) + 1) M ρβ := HH _ (by positivity)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hUn : MemCM M (s85_Ulim a β ρβ M (n : ℝ) y) :=
      s85_Ulim_memCM Hn hMpos hn0 (by linarith) hy
    have hzn : MemCM M (fun x => s85_Ulim a β ρβ M (n : ℝ) y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)) :=
      s8d_memCM_sub_const hMpos hUn _
    have hmean : ∫ x, (s85_Ulim a β ρβ M (n : ℝ) y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ))
        ∂(HRS.Whole.withDensityReal ρβ) = 0 := by
      rw [s8d_integral_sub_const (s8d_integrable_of_memCM hP hg hM hUn), s8d_mean_U Hn hn0 (by linarith) hy]
      ring
    have hid : ∀ x, s85_Ulim a β ρβ M 1 (fun x => s85_Ulim a β ρβ M (n : ℝ) y x -
        ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)) x -
        ∫ x, (s85_Ulim a β ρβ M (n : ℝ) y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ))
          ∂(HRS.Whole.withDensityReal ρβ) =
        s85_Ulim a β ρβ M ((n + 1 : ℕ) : ℝ) y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ) := fun x => by
      rw [hmean, sub_zero, s8d_Ulim_shift Hn hMpos zero_le_one (by linarith) hUn]
      have := s85_semigroup Hn hMpos (t := 1) (s := (n : ℝ)) zero_le_one hn0 (by linarith) hy x
      rw [← this]
      congr 3
      push_cast; ring
    have hLYn := hLY hzn ih' x
    simp only [hid] at hLYn
    -- the L² term
    have hL2n := hL2 (T := (n : ℝ) + 1) (t := ((n + 1 : ℕ) : ℝ)) (f := y) Hn (Nat.cast_nonneg _)
      (by push_cast; exact le_rfl) hy
    have hexp : Real.exp (-lam * ((n + 1 : ℕ) : ℝ)) = q ^ (n + 1) := by
      rw [hq, ← Real.exp_nat_mul]; congr 1; ring
    rw [hexp] at hL2n
    have hy2 := s8d_sq_integral_le hP hg hM hy.1 hΦ
    have hNh : Real.sqrt (∫ z, (s85_Ulim a β ρβ M ((n + 1 : ℕ) : ℝ) y z -
        ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) ≤
        C0 * q ^ (n + 1) * (Φ * Real.sqrt m2) := by
      refine (Real.sqrt_le_sqrt (hL2n.trans (mul_le_mul_of_nonneg_left hy2 (sq_nonneg _)))).trans ?_
      have : (C0 * q ^ (n + 1)) ^ 2 * (Φ ^ 2 * m2) = (C0 * q ^ (n + 1) * (Φ * Real.sqrt m2)) ^ 2 := by
        have hs := Real.sq_sqrt hm20
        calc (C0 * q ^ (n + 1)) ^ 2 * (Φ ^ 2 * m2) = (C0 * q ^ (n + 1)) ^ 2 * (Φ ^ 2 * Real.sqrt m2 ^ 2) := by
              rw [hs]
          _ = _ := by ring
      rw [this, Real.sqrt_sq]
      exact mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hq0.le _)) (mul_nonneg hΦ0 (Real.sqrt_nonneg _))
    have hqκ : q ^ (n + 1) ≤ κ ^ n :=
      (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_succ n)).trans (pow_le_pow_left₀ hq0.le hκq n)
    have hκn : 0 ≤ κ ^ n := pow_nonneg hκ0.le n
    have hA : 0 ≤ Cc * κ ^ n * Φ := mul_nonneg (mul_nonneg hCc0 hκn) hΦ0
    have hjx : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le M
    have hC0' : 0 ≤ C0 := by linarith
    have key : θ' * (Cc * κ ^ n * Φ) + C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M ((n + 1 : ℕ) : ℝ) y z -
        ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) ≤
        Cc * κ ^ (n + 1) * Φ := by
      have h1 := mul_le_mul_of_nonneg_left hNh hC'0
      have h2 : C' * (C0 * q ^ (n + 1) * (Φ * Real.sqrt m2)) ≤ (C' * C0 * Real.sqrt m2) * (κ ^ n * Φ) := by
        have : C' * (C0 * q ^ (n + 1) * (Φ * Real.sqrt m2)) = (C' * C0 * Real.sqrt m2) * (q ^ (n + 1) * Φ) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqκ hΦ0)
          (mul_nonneg (mul_nonneg hC'0 hC0') (Real.sqrt_nonneg _))
      have h3 : (C' * C0 * Real.sqrt m2) * (κ ^ n * Φ) ≤ Cc * (κ - θ') * (κ ^ n * Φ) :=
        mul_le_mul_of_nonneg_right hCcb (mul_nonneg hκn hΦ0)
      have : Cc * κ ^ (n + 1) * Φ = θ' * (Cc * κ ^ n * Φ) + Cc * (κ - θ') * (κ ^ n * Φ) := by ring
      rw [this]
      linarith
    rw [Real.norm_eq_abs]
    refine hLYn.trans ?_
    have := mul_le_mul_of_nonneg_right key hjx
    exact this

end HRS.MS.Wad
