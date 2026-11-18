import HRS.MS.WadAux104

/-!
# S8.3, packet S8F-5: admissible bounds for all iterated differences of a classical solution

`s8f_jets`: for the classical solution `f` of terminal datum `φ` and every list `ξs` with `Σ‖ξ_i‖ ≤ 1/8`, `|ξs| ≤ N`, the iterated flow-shifted difference
`Δ_{ξs} f` satisfies the admissible bound `S84Adm lam t M (Δ_{ξs} f) (K Φ ∏‖ξ_i‖)` and `|Δ_{ξs} f_r(y)| ≤ K Φ ∏‖ξ_i‖ ⟨y⟩^M`, where `Φ`
dominates the terminal values: `Wt M (Φ ∏‖ξ_i‖) (Δ_J f_t)` for every `small` list `J`.  `lam, K` depend only on `d, a, β, T, M, ρβ, N`.
Proof: induction on the length of `ξs`; the source of `Δ_{ξs} f` is `𝓑_ρ Δ_{ξs} f + Σ term I J` (`s8f_Dif_source`), the nonlocal terms involve only
shorter lists (induction hypothesis), and `s8e_apriori_gen` closes the step.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_GB.of_le {k k' : ℕ} {C c : ℝ} {g : Euc d → ℝ} (h : s8f_GB k C c g) (hk : k' ≤ k) :
    s8f_GB k' C c g :=
  ⟨h.1.of_le (by exact_mod_cast hk), fun i hi => h.2 i (hi.trans hk)⟩

theorem s8f_abs_sum_le {α : Type} (l : List α) (f : α → ℝ) {b : ℝ} (h : ∀ p ∈ l, |f p| ≤ b) :
    |(l.map f).sum| ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := h p (List.mem_cons_self)
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    calc |f p + (l.map f).sum| ≤ |f p| + |(l.map f).sum| := abs_add_le _ _
      _ ≤ b + l.length * b := add_le_add h1 h2
      _ = _ := by ring

theorem s8f_norm_list_sum_le (I : List (Euc d)) : ‖I.sum‖ ≤ (I.map (fun e => ‖e‖)).sum := by
  induction I with
  | nil => simp
  | cons e I ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add_right ih _)

def s8f_Claim (a β T M : ℝ) (ρβ : Euc d → ℝ) (N : ℕ) (lam Kn : ℝ) (m : ℕ) : Prop :=
  ∀ {t Φ : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
    IsClassicalAdjointW (critCoeff d a β ρβ) t φ f → 0 ≤ Φ →
    (∀ J : List (Euc d), s8f_small N J → Wt M (Φ * (J.map (fun e => ‖e‖)).prod) (s8f_Dif a J f t)) →
    ∀ ξs : List (Euc d), s8f_small N ξs → ξs.length < m →
      S84Adm lam t M (s8f_Dif a ξs f) (Kn * Φ * (ξs.map (fun e => ‖e‖)).prod) ∧
      ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |s8f_Dif a ξs f r y| ≤
        Kn * Φ * (ξs.map (fun e => ‖e‖)).prod * jbracket y ^ M

theorem s8f_Claim.mono {a β T M : ℝ} {ρβ : Euc d → ℝ} {N : ℕ} {lam Kn Kn' : ℝ} {m m' : ℕ}
    (h : s8f_Claim a β T M ρβ N lam Kn m) (hK : Kn ≤ Kn') (hm : m' ≤ m) :
    s8f_Claim a β T M ρβ N lam Kn' m' := by
  intro t Φ φ f ht htT hf hΦ hdat ξs hξs hlen
  obtain ⟨h1, h2⟩ := h ht htT hf hΦ hdat ξs hξs (lt_of_lt_of_le hlen hm)
  have hP := s8f_prod_nonneg ξs
  have hle : Kn * Φ * (ξs.map (fun e => ‖e‖)).prod ≤ Kn' * Φ * (ξs.map (fun e => ‖e‖)).prod :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hΦ) hP
  refine ⟨h1.mono hle, fun r hr y => (h2 r hr y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (s83_jb_pos y).le _)

theorem s8f_norm_le_sum {I : List (Euc d)} {ξ : Euc d} (h : ξ ∈ I) : ‖ξ‖ ≤ (I.map (fun e => ‖e‖)).sum := by
  induction I with
  | nil => simp at h
  | cons e I ih =>
    simp only [List.map_cons, List.sum_cons]
    have := s8f_sum_nonneg I
    rcases List.mem_cons.1 h with rfl | h'
    · linarith
    · have := ih h'
      linarith [norm_nonneg e]

theorem s8f_step (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (N : ℕ) {CB : ℝ}
    (hCB : ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop ρβ h x| ≤ CB * (V + H) * jbracket x ^ M)
    {lam K : ℝ} (hK : 0 ≤ K)
    (hgen : ∀ {t Φ Ex : ℝ} {q w : ℝ → Euc d → ℝ}, 0 < t → t ≤ T → 0 ≤ Ex →
      S8eSol q a β⁻¹ t M Φ w →
      (∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M w Θ → ∀ s ∈ Set.Ico 0 t,
        Wt M ((2 * CB * Θ + Ex) * s84_wt lam t s) (q s)) →
      S84Adm lam t M w (K * (Φ + Ex)) ∧
        ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |w r y| ≤ K * (Φ + Ex) * jbracket y ^ M)
    {C0 c0 : ℝ} (hC0 : 0 ≤ C0) (hc0 : 0 < c0) (hGBρ : s8f_GB (N + 1) C0 c0 ρβ)
    {Kc : ℝ} (hKc0 : 0 ≤ Kc)
    (hKc : ∀ {σ : Euc d → ℝ} {C : ℝ}, 0 ≤ C → Differentiable ℝ σ →
      (∀ x, |σ x| ≤ C * Real.exp (-(c0 / 2 ^ N) * ‖x‖ ^ 2) ∧
        ‖fderiv ℝ σ x‖ ≤ C * Real.exp (-(c0 / 2 ^ N) * ‖x‖ ^ 2)) →
      ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop σ h x| ≤ Kc * C * (V + H) * jbracket x ^ M)
    (m : ℕ) (Kprev : ℝ) (hKp : 0 ≤ Kprev) (hprev : s8f_Claim a β T M ρβ N lam Kprev m) :
    ∃ Kn : ℝ, 0 ≤ Kn ∧ s8f_Claim a β T M ρβ N lam Kn (m + 1) := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  set cs : ℝ := c0 / 2 ^ N with hcsdef
  have hcs : 0 < cs := by positivity
  set E : ℝ := Real.exp c0 with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp hc0.le
  have h3 : 0 ≤ (3 : ℝ) ^ M := Real.rpow_nonneg (by norm_num) _
  set W0 : ℝ := Kc * C0 * E ^ N * (2 * 3 ^ M * Kprev) with hW0def
  have hW0 : 0 ≤ W0 := by positivity
  refine ⟨max Kprev (K * (1 + 2 ^ m * W0)), le_max_of_le_left hKp, ?_⟩
  intro t Φ φ f ht htT hf hΦ hdat ξs hξs hlen
  rcases Nat.lt_or_ge ξs.length m with hlt | hge
  · exact (hprev.mono (le_max_left _ _) le_rfl) ht htT hf hΦ hdat ξs hξs hlt
  have hlenm : ξs.length = m := by omega
  -- the solution and its iterated differences
  have hΦ0 : Wt M Φ φ := by
    have := hdat [] ⟨by simp, by simp⟩
    simpa [s8f_Dif, hf.terminal] using this
  have sol0 := s84_sol_of_classical a β ha hβ ρβ ht hf hΦ0
  have solq := s8f_sol_of_s84 sol0
  have solJ := s8f_Dif_sol ha hν hM ht N solq (fun J => Φ * (J.map (fun e => ‖e‖)).prod) (by simp) hdat
  have HC : ∀ J, s8f_small N J → ∀ s ∈ Set.Icc 0 t, ∃ B, s84_C2b (fun y => s8f_Dif a J f s y) B := by
    intro J hJ s hs
    obtain ⟨B, hB⟩ := s8f_C2b_of_sol (solJ J hJ)
    exact ⟨B, hB s hs⟩
  have hGBI : ∀ I : List (Euc d), s8f_small N I → ∀ s : ℝ, 0 ≤ s →
      s8f_GB (0 + 1) (C0 * E ^ N * (I.map (fun e => ‖e‖)).prod) cs (fun y => s8f_Dif a I (fun _ => ρβ) s y) := by
    intro I hI s hs
    have h1 := s8f_GB_dif a ha.le hc0.le I 1 (hGBρ.of_le (by have := hI.1; omega)) s hs
      (fun ξ hξ => ((s8f_norm_le_sum hξ).trans hI.2).trans (by norm_num))
    refine h1.mono ?_ hcs.le ?_
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hE1 hI.1) hC0)
        (s8f_prod_nonneg I)
    · exact div_le_div_of_nonneg_left hc0.le (by positivity) (pow_le_pow_right₀ (by norm_num) hI.1)
  have HG : ∀ I, s8f_small N I → ∀ s ∈ Set.Icc 0 t, s84_GaussReg (fun y => s8f_Dif a I (fun _ => ρβ) s y) :=
    fun I hI s hs => s8f_GB_gaussReg (hGBI I hI s hs.1) hcs
  have ident := s8f_Dif_source hd ha.le ρβ f N HG HC ξs hξs
  set P : ℝ := (ξs.map (fun e => ‖e‖)).prod with hPdef
  have hP : 0 ≤ P := s8f_prod_nonneg ξs
  set Ex : ℝ := 2 ^ m * W0 * Φ * P with hExdef
  have hEx : 0 ≤ Ex := by positivity
  have hq : ∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M (s8f_Dif a ξs f) Θ → ∀ s ∈ Set.Ico 0 t,
      Wt M ((2 * CB * Θ + Ex) * s84_wt lam t s) (s8f_Dif a ξs (fun s y => s84_Bop ρβ (f s) y) s) := by
    intro Θ hΘ hadm s hs y
    have hsI : s ∈ Set.Icc 0 t := ⟨hs.1, hs.2.le⟩
    have hw0 := s84_wt_nonneg lam t s hs.2.le
    have hj : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
    rw [Real.norm_eq_abs, ident s hsI y]
    have hmain := s84_q_wt (w := s8f_Dif a ξs f) hCB hΘ hadm hs y
    rw [Real.norm_eq_abs] at hmain
    have hterm : ∀ p ∈ s8f_Sr ξs, |s8f_term a ρβ f p.1 p.2 s y| ≤
        (W0 * Φ * P) * s84_wt lam t s * jbracket y ^ M := by
      intro p hp
      obtain ⟨hperm, hne⟩ := s8f_Sr_perm ξs p hp
      obtain ⟨hI, hJ⟩ := s8f_small_perm hξs hperm
      have hlen2 : p.2.length < m := by
        have h1 := hperm.length_eq
        rw [List.length_append] at h1
        have : 0 < p.1.length := List.length_pos_iff.2 hne
        omega
      obtain ⟨hadm2, -⟩ := hprev ht htT hf hΦ hdat p.2 hJ hlen2
      have hζ : ‖s8e_zs a p.1.sum s‖ < 1 / 4 :=
        lt_of_le_of_lt ((s8e_zs_norm ha.le hs.1 _).trans ((s8f_norm_list_sum_le p.1).trans hI.2))
          (by norm_num)
      have hΘ2 : 0 ≤ Kprev * Φ * (p.2.map (fun e => ‖e‖)).prod :=
        mul_nonneg (mul_nonneg hKp hΦ) (s8f_prod_nonneg _)
      have hwt := s8f_term_wt hKc hM hKc0 (mul_nonneg (mul_nonneg hC0 (by positivity))
        (s8f_prod_nonneg p.1)) (a := a) (ρ := ρβ) (w := f) (I := p.1) (J := p.2) (lam := lam) (t := t)
        (hGBI p.1 hI s hs.1) hΘ2 hadm2 hs hζ y
      rw [Real.norm_eq_abs] at hwt
      refine hwt.trans (le_of_eq ?_)
      have hprod : P = (p.1.map (fun e => ‖e‖)).prod * (p.2.map (fun e => ‖e‖)).prod := by
        rw [hPdef, ← List.prod_append, ← List.map_append]
        exact ((hperm.map _).prod_eq).symm
      rw [hprod, hW0def]
      ring
    have hsum := s8f_abs_sum_le (s8f_Sr ξs) (fun p => s8f_term a ρβ f p.1 p.2 s y) hterm
    have hlenS : ((s8f_Sr ξs).length : ℝ) ≤ 2 ^ m := by
      have := s8f_Sr_length ξs
      rw [hlenm] at this
      have : (s8f_Sr ξs).length ≤ 2 ^ m := by omega
      exact_mod_cast this
    have hb0 : 0 ≤ (W0 * Φ * P) * s84_wt lam t s * jbracket y ^ M := by positivity
    calc |s84_Bop ρβ (fun y' => s8f_Dif a ξs f s y') y +
          ((s8f_Sr ξs).map (fun p => s8f_term a ρβ f p.1 p.2 s y)).sum|
        ≤ |s84_Bop ρβ (fun y' => s8f_Dif a ξs f s y') y| +
          |((s8f_Sr ξs).map (fun p => s8f_term a ρβ f p.1 p.2 s y)).sum| := abs_add_le _ _
      _ ≤ 2 * CB * Θ * s84_wt lam t s * jbracket y ^ M +
          (s8f_Sr ξs).length * ((W0 * Φ * P) * s84_wt lam t s * jbracket y ^ M) := add_le_add hmain hsum
      _ ≤ 2 * CB * Θ * s84_wt lam t s * jbracket y ^ M +
          2 ^ m * ((W0 * Φ * P) * s84_wt lam t s * jbracket y ^ M) := by
          gcongr
      _ = _ := by rw [hExdef]; ring
  have hres := hgen ht htT hEx (solJ ξs hξs) hq
  have hfin : K * (Φ * P + Ex) ≤ max Kprev (K * (1 + 2 ^ m * W0)) * Φ * P := by
    have e1 : K * (Φ * P + Ex) = K * (1 + 2 ^ m * W0) * Φ * P := by rw [hExdef]; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hΦ) hP
  refine ⟨hres.1.mono hfin, fun r hr y => (hres.2 r hr y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg (s83_jb_pos y).le _)

end HRS.MS.Wad
