import HRS.MS.WadAux27

/-!
# S8.3, packet D5^7 (Route A): closing the Gronwall argument

* `s84_adm_closed`: `S84Adm` is closed under decreasing limits of `Θ`.
* `s84_adm_start`: a classical solution (bounded `Dw, D²w`) is admissible for some `Θ₀`.
* `s84_adm_fix`: if `Θ ↦ A + Θ/2` improves admissibility and some `Θ₀` is admissible, then `2A` is.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_adm_closed {lam t M : ℝ} {w : ℝ → Euc d → ℝ} {Θ : ℝ}
    (h : ∀ η : ℝ, 0 < η → S84Adm lam t M w (Θ + η)) : S84Adm lam t M w Θ := by
  intro s hs
  have hw := s84_wt_nonneg lam t s hs.2.le
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    set c : ℝ := s84_wt lam t s * jbracket y ^ M with hc
    have hc0 : 0 ≤ c := mul_nonneg hw (Real.rpow_nonneg (s83_jb_pos _).le _)
    have := (h (ε / (c + 1)) (by positivity) s hs).1 y
    refine this.trans ?_
    have e : (Θ + ε / (c + 1)) * s84_wt lam t s * jbracket y ^ M = Θ * s84_wt lam t s * jbracket y ^ M +
        ε * (c / (c + 1)) := by rw [hc]; field_simp
    rw [e]
    have : c / (c + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    set c : ℝ := s84_wt lam t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M with hc
    have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg hw (Real.rpow_nonneg (norm_nonneg _) _))
      (Real.rpow_nonneg (s83_jb_pos _).le _)
    have := (h (ε / (c + 1)) (by positivity) s hs).2 x x' hx
    refine this.trans ?_
    have e : (Θ + ε / (c + 1)) * s84_wt lam t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M =
        Θ * s84_wt lam t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M + ε * (c / (c + 1)) := by
      rw [hc]; field_simp
    rw [e]
    have : c / (c + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith

theorem s84_norm_le_sqrt {z : Euc d} (hz : ‖z‖ ≤ 1 / 4) : ‖z‖ ≤ ‖z‖ ^ (1 / 2 : ℝ) / 2 := by
  have h0 := norm_nonneg z
  have hsq : ‖z‖ ^ (1 / 2 : ℝ) = Real.sqrt ‖z‖ := (Real.sqrt_eq_rpow ‖z‖).symm
  rw [hsq]
  have h1 := Real.sq_sqrt h0
  have h2 : Real.sqrt ‖z‖ ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hz
  nlinarith [Real.sqrt_nonneg ‖z‖]

/-- A classical solution (bounded first and second derivatives) is admissible for some `Θ₀`. -/
theorem s84_adm_start {ρ : Euc d → ℝ} {a ν t M Φ T lam : ℝ} {w : ℝ → Euc d → ℝ}
    (sol : S84Sol ρ a ν t M Φ w) (hM : 0 ≤ M) (ht : 0 < t) (htT : t ≤ T) (hlam : 0 ≤ lam) :
    ∃ Θ₀ : ℝ, 0 ≤ Θ₀ ∧ S84Adm lam t M w Θ₀ := by
  obtain ⟨B1, B2, hB⟩ := sol.bdd
  have h00 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht.le⟩
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans ((hB 0 h00 0).1)
  have hB2 : 0 ≤ B2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (w 0)) 0)) (hB 0 h00 0).2
  have hT : 0 < T := ht.trans_le htT
  refine ⟨max B1 B2 * T ^ (3 / 4 : ℝ), by positivity, fun s hs => ?_⟩
  have hsI : s ∈ Set.Icc 0 t := ⟨hs.1, hs.2.le⟩
  set τ : ℝ := t - s with hτ
  have hτ0 : 0 < τ := sub_pos.2 hs.2
  have hτT : τ ≤ T := by linarith [hs.1]
  have hwt : T ^ (-(3 / 4 : ℝ)) ≤ s84_wt lam t s := by
    have h1 : T ^ (-(3 / 4 : ℝ)) ≤ τ ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hτ0 hτT (by norm_num)
    have h2 : 1 ≤ Real.exp (lam * τ) := Real.one_le_exp (by positivity)
    have h3 : 0 < τ ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hτ0 _
    unfold s84_wt
    nlinarith
  have hone : T ^ (3 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hT]; simp
  have hmax : max B1 B2 ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s := by
    have hm0 : 0 ≤ max B1 B2 := le_max_of_le_left hB1
    calc max B1 B2 = max B1 B2 * (T ^ (3 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ))) := by rw [hone, mul_one]
      _ ≤ max B1 B2 * (T ^ (3 / 4 : ℝ) * s84_wt lam t s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwt (by positivity)) hm0
      _ = _ := by ring
  have hjb : ∀ y : Euc d, 1 ≤ jbracket y ^ M := fun y => Real.one_le_rpow (s83_one_le_jb y) hM
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · calc ‖fderiv ℝ (w s) y‖ ≤ B1 := (hB s hsI y).1
      _ ≤ max B1 B2 := le_max_left _ _
      _ ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s := hmax
      _ ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s * jbracket y ^ M := by
          have h0 : 0 ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s :=
            le_trans (le_max_of_le_left hB1) hmax
          nlinarith [hjb y]
  · have hd1 : Differentiable ℝ (fderiv ℝ (w s)) :=
      ((sol.c2 s hsI).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have hmv := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ (w s)) (C := B2) (fun y _ => hd1 y) (fun y _ => (hB s hsI y).2)
      (Set.mem_univ x) (Set.mem_univ x')
    have hh := s84_norm_le_sqrt hx
    have hS0 : 0 ≤ ‖x' - x‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have h0 : 0 ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s := le_trans (le_max_of_le_left hB1) hmax
    calc ‖fderiv ℝ (w s) x' - fderiv ℝ (w s) x‖ ≤ B2 * ‖x' - x‖ := hmv
      _ ≤ B2 * (‖x' - x‖ ^ (1 / 2 : ℝ) / 2) := mul_le_mul_of_nonneg_left hh hB2
      _ ≤ max B1 B2 * ‖x' - x‖ ^ (1 / 2 : ℝ) := by
          have := le_max_right B1 B2
          nlinarith [mul_nonneg hS0 (sub_nonneg.2 this), mul_nonneg hS0 hB2]
      _ ≤ (max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s) * ‖x' - x‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hmax hS0
      _ ≤ (max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
          have := mul_nonneg h0 hS0
          nlinarith [hjb x]

/-- Fixed point of the improvement `Θ ↦ A + Θ/2`. -/
theorem s84_adm_fix {lam t M : ℝ} {w : ℝ → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h0 : ∃ Θ₀ : ℝ, 0 ≤ Θ₀ ∧ S84Adm lam t M w Θ₀)
    (hstep : ∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M w Θ → S84Adm lam t M w (A + Θ / 2)) :
    S84Adm lam t M w (2 * A) := by
  obtain ⟨Θ₀, hΘ₀, hadm₀⟩ := h0
  set Θ₁ : ℝ := max Θ₀ (2 * A) with hΘ₁
  have hadm₁ : S84Adm lam t M w Θ₁ := hadm₀.mono (le_max_left _ _)
  have hge : 2 * A ≤ Θ₁ := le_max_right _ _
  have hn : ∀ n : ℕ, S84Adm lam t M w (2 * A + (Θ₁ - 2 * A) / 2 ^ n) := by
    intro n
    induction n with
    | zero => simpa using hadm₁
    | succ n ih =>
      have hpos : 0 ≤ 2 * A + (Θ₁ - 2 * A) / 2 ^ n := by
        have : 0 ≤ (Θ₁ - 2 * A) / 2 ^ n := div_nonneg (by linarith) (by positivity)
        linarith
      have := hstep _ hpos ih
      have e : 2 * A + (Θ₁ - 2 * A) / 2 ^ (n + 1) = A + (2 * A + (Θ₁ - 2 * A) / 2 ^ n) / 2 := by
        rw [pow_succ]; ring
      rw [e]; exact this
  apply s84_adm_closed
  intro η hη
  obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one (show 0 < η / (Θ₁ - 2 * A + 1) by
    have : 0 ≤ Θ₁ - 2 * A := by linarith
    positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine (hn n).mono ?_
  have h2n : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [one_div_pow]
  rw [h2n] at hn'
  have hd : 0 ≤ Θ₁ - 2 * A := by linarith
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have : (Θ₁ - 2 * A) / 2 ^ n ≤ η := by
    rw [div_le_iff₀ hp]
    rw [div_lt_div_iff₀ hp (by positivity)] at hn'
    nlinarith
  linarith

end HRS.MS.Wad
