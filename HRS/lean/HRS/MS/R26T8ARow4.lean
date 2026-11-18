import HRS.MS.R26T8ARow3
import HRS.MS.R26T8AP11s

/-!
# S8.2 row lemma, step 4: weighted pointwise jets of the shifted integrand
`r26t8a_row_Gd u x = if u = 0 then 0 else rho (x-u) F x (x-u)`;
`r26t8a_row_Gd_bound`: `‖D^j_x Gd‖ <= 2^j K A <x>^M (1+|x-u|)^(-(d+1)) env(u)` when `N = M+d+1`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

def r26t8a_row_Gd (ρ : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (u x : Euc d) : ℝ :=
  if u = 0 then 0 else ρ (x - u) * F x (x - u)

theorem r26t8a_row_Gd_contDiff (k : ℕ) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ (k : WithTop ℕ∞) ρ)
    {F : Euc d → Euc d → ℝ} (hF : ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry F) {p : Euc d × Euc d | p.1 ≠ p.2})
    (u : Euc d) : ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_row_Gd ρ F u) := by
  by_cases hu : u = 0
  · have e0 : r26t8a_row_Gd ρ F u = fun _ => (0 : ℝ) := by funext x; simp [r26t8a_row_Gd, hu]
    rw [e0]; exact contDiff_const
  · have e : r26t8a_row_Gd ρ F u = fun x' => ρ (x' - u) * F x' (x' - u) := by
      funext x'; simp [r26t8a_row_Gd, hu]
    rw [e]
    have hl : ContDiff ℝ (k : WithTop ℕ∞) (fun x' : Euc d => (x', x' - u)) :=
      contDiff_id.prodMk (contDiff_id.sub contDiff_const)
    have hg := hF.comp_contDiff hl (fun x' => by
      intro h; apply hu
      have h' : x' - (x' - u) = 0 := sub_eq_zero.2 h
      simpa using h')
    exact (hρ.comp (contDiff_id.sub contDiff_const)).mul hg

theorem r26t8a_row_Gd_bound {M : ℝ} (hM : 0 ≤ M) (k b : ℕ) (σ A K : ℝ) (hA : 0 ≤ A) {ρ : Euc d → ℝ}
    (hρ : ContDiff ℝ (k : WithTop ℕ∞) ρ)
    (hK : ∀ i ≤ k, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ y‖ ≤ K * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)))
    {F : Euc d → Euc d → ℝ} (hF : Conormal k b M σ A F) {u : Euc d} (hu : u ≠ 0) (x : Euc d) (j : ℕ) (hj : j ≤ k) :
    ‖iteratedFDeriv ℝ j (r26t8a_row_Gd ρ F u) x‖ ≤
      2 ^ j * K * jbracket x ^ M * (A * ((1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) *
        (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b))) := by
  have e : r26t8a_row_Gd ρ F u = fun x' => ρ (x' - u) * F x' (x' - u) := by
    funext x'; simp [r26t8a_row_Gd, hu]
  rw [e]
  have h := r26t8a_row_pt k b M σ A K (M + (d : ℝ) + 1) hρ hK hF hu x j hj
  refine h.trans ?_
  set r : ℝ := ‖x - u‖ with hr
  set Env : ℝ := 1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b with hEnv
  have hK0 : 0 ≤ K := by
    have h0 := (norm_nonneg _).trans (hK 0 (Nat.zero_le _) 0)
    have hp : 0 < (1 + ‖(0 : Euc d)‖) ^ (-(M + (d : ℝ) + 1)) := Real.rpow_pos_of_pos (by simp) _
    exact nonneg_of_mul_nonneg_left h0 hp
  have hEnv0 : 0 ≤ Env := by
    rw [hEnv]
    have : 0 ≤ (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    positivity
  have hr1 : 0 < 1 + r := by positivity
  have hjb : jbracket (x - u) ^ M ≤ (1 + r) ^ M :=
    Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_one_add _) hM
  have hpw : pairWeight M x (x - u) ≤ jbracket x ^ M * (1 + r) ^ M := by
    unfold pairWeight
    exact mul_le_mul_of_nonneg_left hjb (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hexp : (1 + r) ^ (-(M + (d : ℝ) + 1)) * (1 + r) ^ M = (1 + r) ^ (-((d : ℝ) + 1)) := by
    rw [← Real.rpow_add hr1]; congr 1; ring
  have hrp : 0 ≤ (1 + r) ^ (-(M + (d : ℝ) + 1)) := Real.rpow_nonneg hr1.le _
  calc 2 ^ j * (K * (1 + r) ^ (-(M + (d : ℝ) + 1))) * (A * pairWeight M x (x - u) * Env)
      ≤ 2 ^ j * (K * (1 + r) ^ (-(M + (d : ℝ) + 1))) * (A * (jbracket x ^ M * (1 + r) ^ M) * Env) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw hA) hEnv0
    _ = 2 ^ j * K * jbracket x ^ M * (A * (((1 + r) ^ (-(M + (d : ℝ) + 1)) * (1 + r) ^ M) * Env)) := by ring
    _ = _ := by rw [hexp]

end HRS.MS.R26T8A
