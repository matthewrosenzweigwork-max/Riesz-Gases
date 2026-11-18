import HRS.MS.WadAux103

/-!
# S8.3, packet S8F-4: mild-solution structure of the iterated differences and the weight bound of one nonlocal term

`s8f_sol_of_s84`: an `S84Sol` is an `S8eSol` with source `𝓑_ρ w`.  `s8f_Dif_sol`: for every `small` list `ξs`, `s8f_Dif a ξs w` is an
`S8eSol` with source `s8f_Dif a ξs q` and any datum constant dominating its terminal values (iteration of `s8e_shift_sol_gen`).
`s8f_C2b_of_sol`: the time slices of an `S8eSol` are `C²_b`.  `s8f_adm_shift`: the admissible bounds survive a shift `‖z‖ < 1/4` at the price `3^M`.
`s8f_term_wt`: the weighted size of one nonlocal term `s8f_term a ρ w I J s`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_sol_of_s84 {ρ : Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (sol : S84Sol ρ a ν t M Φ w) :
    S8eSol (fun s y => s84_Bop ρ (w s) y) a ν t M Φ w :=
  ⟨sol.c2, sol.hqc, sol.hqb, sol.mild, sol.term_cont, sol.term_wt, sol.bdd⟩

theorem s8f_Dif_sol {a ν t M Φ0 : ℝ} (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) (ht : 0 < t) (N : ℕ)
    {q w : ℝ → Euc d → ℝ} (sol : S8eSol q a ν t M Φ0 w) (Φd : List (Euc d) → ℝ) (h0 : Φd [] = Φ0)
    (hdat : ∀ ξs : List (Euc d), s8f_small N ξs → Wt M (Φd ξs) (s8f_Dif a ξs w t)) :
    ∀ ξs : List (Euc d), s8f_small N ξs →
      S8eSol (s8f_Dif a ξs q) a ν t M (Φd ξs) (s8f_Dif a ξs w) := by
  intro ξs
  induction ξs with
  | nil =>
    intro _
    rw [h0]
    exact sol
  | cons ξ rest ih =>
    intro hsm
    obtain ⟨hsr, hξ⟩ := s8f_small_cons hsm
    have := s8e_shift_sol_gen ha hν hM ht (ih hsr) (ζ := ξ) (by linarith) (Φu := Φd (ξ :: rest))
      (hdat (ξ :: rest) hsm)
    exact this

theorem s8f_C2b_of_sol {q w : ℝ → Euc d → ℝ} {a ν t M Φ : ℝ} (sol : S8eSol q a ν t M Φ w) :
    ∃ B : ℝ, ∀ r ∈ Set.Icc 0 t, s84_C2b (fun y => w r y) B := by
  obtain ⟨B1, B2, hB⟩ := sol.bdd
  refine ⟨max B1 B2, fun r hr => ⟨sol.c2 r hr, fun y => ⟨(hB r hr y).1.trans (le_max_left _ _),
    (hB r hr y).2.trans (le_max_right _ _)⟩⟩⟩

theorem s8f_adm_shift {lam t M Θ : ℝ} {u : ℝ → Euc d → ℝ} (hM : 0 ≤ M) (hΘ : 0 ≤ Θ)
    (hadm : S84Adm lam t M u Θ) {s : ℝ} (hs : s ∈ Set.Ico 0 t) {z : Euc d} (hz : ‖z‖ < 1 / 4) :
    (∀ y, ‖fderiv ℝ (fun y' => u s (y' + z)) y‖ ≤ (3 ^ M * Θ * s84_wt lam t s) * jbracket y ^ M) ∧
    (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
      ‖fderiv ℝ (fun y' => u s (y' + z)) x' - fderiv ℝ (fun y' => u s (y' + z)) x‖ ≤
        (3 ^ M * Θ * s84_wt lam t s) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) := by
  obtain ⟨hA1, hA2⟩ := hadm s hs
  have hw0 := s84_wt_nonneg lam t s hs.2.le
  have hfd : ∀ y, fderiv ℝ (fun y' => u s (y' + z)) y = fderiv ℝ (u s) (y + z) := fun y => by
    rw [fderiv_comp_add_right]
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · rw [hfd]
    refine (hA1 (y + z)).trans ?_
    calc Θ * s84_wt lam t s * jbracket (y + z) ^ M
        ≤ Θ * s84_wt lam t s * (3 ^ M * jbracket y ^ M) :=
          mul_le_mul_of_nonneg_left (s8e_jb_shift hM hz y) (by positivity)
      _ = _ := by ring
  · rw [hfd, hfd]
    have hx' : ‖(x' + z) - (x + z)‖ ≤ 1 / 4 := by rwa [add_sub_add_right_eq_sub]
    have := hA2 (x + z) (x' + z) hx'
    rw [add_sub_add_right_eq_sub] at this
    refine this.trans ?_
    have hS := Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)
    calc Θ * s84_wt lam t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket (x + z) ^ M
        ≤ Θ * s84_wt lam t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M) :=
          mul_le_mul_of_nonneg_left (s8e_jb_shift hM hz x) (by positivity)
      _ = _ := by ring

theorem s8f_term_wt {M Kc C' cs : ℝ}
    (hKc : ∀ {σ : Euc d → ℝ} {C : ℝ}, 0 ≤ C → Differentiable ℝ σ →
      (∀ x, |σ x| ≤ C * Real.exp (-cs * ‖x‖ ^ 2) ∧ ‖fderiv ℝ σ x‖ ≤ C * Real.exp (-cs * ‖x‖ ^ 2)) →
      ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop σ h x| ≤ Kc * C * (V + H) * jbracket x ^ M)
    (hM : 0 ≤ M) (hKc0 : 0 ≤ Kc) (hC' : 0 ≤ C') {a : ℝ} {ρ : Euc d → ℝ} {w : ℝ → Euc d → ℝ}
    {I J : List (Euc d)} {lam t Θ s : ℝ}
    (hGB : s8f_GB (0 + 1) C' cs (fun y => s8f_Dif a I (fun _ => ρ) s y)) (hΘ : 0 ≤ Θ)
    (hadm : S84Adm lam t M (s8f_Dif a J w) Θ) (hs : s ∈ Set.Ico 0 t) (hζ : ‖s8e_zs a I.sum s‖ < 1 / 4) :
    Wt M (Kc * C' * (2 * (3 ^ M * Θ * s84_wt lam t s))) (fun y => s8f_term a ρ w I J s y) := by
  intro y
  obtain ⟨hD, hH⟩ := s8f_adm_shift hM hΘ hadm hs hζ
  have hw0 := s84_wt_nonneg lam t s hs.2.le
  have h3 : 0 ≤ (3 : ℝ) ^ M := Real.rpow_nonneg (by norm_num) _
  have hV : 0 ≤ 3 ^ M * Θ * s84_wt lam t s := by positivity
  obtain ⟨hdf, hgb⟩ := s8f_GB_basic hGB
  have := hKc hC' hdf hgb hV hV hD hH y
  rw [Real.norm_eq_abs]
  refine this.trans (le_of_eq ?_)
  ring

end HRS.MS.Wad
