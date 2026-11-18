import HRS.MS.WadAux34

/-!
# S8.3, packet D7d (Route A): differences of classical solutions and Lipschitz dependence on the datum

`s84_sol_sub`: if `w₁, w₂` are `S84Sol`s on `[0,t]` then `w₁ - w₂` is an `S84Sol` (the source `𝓑` is additive on
`C²_b`, `s84_Bop_sub`, and the Mehler semigroup is linear), with any `Φ` bounding the terminal difference.
`s84_apriori_sub`: hence `|w₁_r(y) - w₂_r(y)| ≤ K Φ ⟨y⟩^M` with `K` independent of the solutions.
In particular classical solutions with the same terminal datum coincide and the solution map is
`C_M`-Lipschitz, which is the estimate behind the extension of `U_t` from `C_c^∞` to `C_M`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s84_C2b_of_sol {ρ : Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ}
    (sol : S84Sol ρ a ν t M Φ w) {r : ℝ} (hr : r ∈ Set.Icc 0 t) :
    ∃ B, s84_C2b (w r) B := by
  obtain ⟨B1, B2, hB⟩ := sol.bdd
  exact ⟨max B1 B2, sol.c2 r hr, fun y => ⟨(hB r hr y).1.trans (le_max_left _ _),
    (hB r hr y).2.trans (le_max_right _ _)⟩⟩

theorem s84_P_sub {a ν : ℝ} (ha : 0 < a) (hν : 0 < ν) {r t' : ℝ} (hrt : r ≤ t') {f g : Euc d → ℝ}
    (hf : Continuous f) (hg : Continuous g) {K : ℝ} {p : ℕ}
    (hfb : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ p) (hgb : ∀ y, |g y| ≤ K * (1 + ‖y‖) ^ p) (x : Euc d) :
    s83_P a ν (t' - r) (fun y => f y - g y) x = s83_P a ν (t' - r) f x - s83_P a ν (t' - r) g x := by
  rw [s83_P_eq_Y, s83_P_eq_Y, s83_P_eq_Y]
  exact integral_sub (s83_int_Y hf hfb ha hν.le hrt x) (s83_int_Y hg hgb ha hν.le hrt x)

theorem s84_P_sub_wt {a ν M C : ℝ} (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) {τ : ℝ} (hτ : 0 ≤ τ)
    {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) (hfw : Wt M C f) (hgw : Wt M C g)
    (x : Euc d) :
    s83_P a ν τ (fun y => f y - g y) x = s83_P a ν τ f x - s83_P a ν τ g x := by
  have hσ : |s83_ms a ν τ| ≤ Real.sqrt (ν / a) := s83_abs_ms_le ha hν.le hτ
  exact integral_sub (s83_int_shift hf hM hfw hσ x) (s83_int_shift hg hM hgw hσ x)

theorem s84_sol_sub (hd : 2 ≤ d) {a ν : ℝ} (ha : 0 < a) (hν : 0 < ν) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ)
    {t M Φ₁ Φ₂ Φ : ℝ} {w₁ w₂ : ℝ → Euc d → ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (sol₁ : S84Sol ρ a ν t M Φ₁ w₁) (sol₂ : S84Sol ρ a ν t M Φ₂ w₂)
    (hΦ : Wt M Φ (fun y => w₁ t y - w₂ t y)) :
    S84Sol ρ a ν t M Φ (fun r y => w₁ r y - w₂ r y) := by
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
  have hlin : ∀ s ∈ Set.Icc 0 t, ∀ y, s84_Bop ρ (fun y => w₁ s y - w₂ s y) y =
      s84_Bop ρ (w₁ s) y - s84_Bop ρ (w₂ s) y := fun s hs y => by
    obtain ⟨B₁, h1⟩ := s84_C2b_of_sol sol₁ hs
    obtain ⟨B₂, h2⟩ := s84_C2b_of_sol sol₂ hs
    exact s84_Bop_sub hd hρ h1 h2 y
  obtain ⟨K₁, p₁, hq₁⟩ := sol₁.hqb
  obtain ⟨K₂, p₂, hq₂⟩ := sol₂.hqb
  have hK₁ : 0 ≤ K₁ := by
    have := (abs_nonneg _).trans (hq₁ 0 h0I 0)
    simpa using this
  have hK₂ : 0 ≤ K₂ := by
    have := (abs_nonneg _).trans (hq₂ 0 h0I 0)
    simpa using this
  have hmono : ∀ (p q : ℕ) (y : Euc d), p ≤ q → (1 + ‖y‖) ^ p ≤ (1 + ‖y‖) ^ q := fun p q y hpq =>
    pow_le_pow_right₀ (by linarith [norm_nonneg y]) hpq
  have hb1 : ∀ s ∈ Set.Icc 0 t, ∀ y, |s84_Bop ρ (w₁ s) y| ≤ (K₁ + K₂) * (1 + ‖y‖) ^ (max p₁ p₂) :=
    fun s hs y => by
      have e1 := (hq₁ s hs y).trans (mul_le_mul_of_nonneg_left (hmono p₁ (max p₁ p₂) y (le_max_left _ _)) hK₁)
      have : 0 ≤ K₂ * (1 + ‖y‖) ^ (max p₁ p₂) := by positivity
      nlinarith
  have hb2 : ∀ s ∈ Set.Icc 0 t, ∀ y, |s84_Bop ρ (w₂ s) y| ≤ (K₁ + K₂) * (1 + ‖y‖) ^ (max p₁ p₂) :=
    fun s hs y => by
      have e2 := (hq₂ s hs y).trans (mul_le_mul_of_nonneg_left (hmono p₂ (max p₁ p₂) y (le_max_right _ _)) hK₂)
      have : 0 ≤ K₁ * (1 + ‖y‖) ^ (max p₁ p₂) := by positivity
      nlinarith
  have hqc1 : ∀ s ∈ Set.Icc 0 t, Continuous (fun y => s84_Bop ρ (w₁ s) y) := fun s hs =>
    s84_sol_qcont sol₁ hs
  have hqc2 : ∀ s ∈ Set.Icc 0 t, Continuous (fun y => s84_Bop ρ (w₂ s) y) := fun s hs =>
    s84_sol_qcont sol₂ hs
  obtain ⟨B1a, B2a, hBa⟩ := sol₁.bdd
  obtain ⟨B1b, B2b, hBb⟩ := sol₂.bdd
  refine ⟨fun r hr => (sol₁.c2 r hr).sub (sol₂.c2 r hr), ?_, ?_, ?_, ?_, hΦ, ?_⟩
  · have := sol₁.hqc.sub sol₂.hqc
    refine this.congr fun p hp => ?_
    simp only [Pi.sub_apply]
    exact hlin p.1 hp.1 p.2
  · refine ⟨K₁ + K₂ + (K₁ + K₂), max p₁ p₂, fun s hs y => ?_⟩
    rw [hlin s hs y]
    refine (abs_sub _ _).trans ?_
    have e1 := hb1 s hs y
    have e2 := hb2 s hs y
    linarith
  · intro r hr x
    have hrt : r ≤ t := hr.2
    have m1 := sol₁.mild r hr x
    have m2 := sol₂.mild r hr x
    have hP0 : s83_P a ν (t - r) (fun y => w₁ t y - w₂ t y) x =
        s83_P a ν (t - r) (w₁ t) x - s83_P a ν (t - r) (w₂ t) x :=
      s84_P_sub_wt ha hν hM (sub_nonneg.2 hrt) sol₁.term_cont sol₂.term_cont
        (sol₁.term_wt.mono (le_max_left Φ₁ Φ₂)) (sol₂.term_wt.mono (le_max_right Φ₁ Φ₂)) x
    have hI : (∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (fun y => w₁ s y - w₂ s y) y) x) =
        (∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w₁ s) y) x) -
          ∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w₂ s) y) x := by
      rw [← intervalIntegral.integral_sub (s84_hint ha hν sol₁ hr x) (s84_hint ha hν sol₂ hr x)]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le hrt] at hs
      have hs' : s ∈ Set.Icc 0 t := ⟨hr.1.trans hs.1, hs.2⟩
      have hfun : (fun y => s84_Bop ρ (fun y => w₁ s y - w₂ s y) y) =
          fun y => s84_Bop ρ (w₁ s) y - s84_Bop ρ (w₂ s) y := funext (hlin s hs')
      show s83_P a ν (s - r) (fun y => s84_Bop ρ (fun y => w₁ s y - w₂ s y) y) x =
        s83_P a ν (s - r) (fun y => s84_Bop ρ (w₁ s) y) x - s83_P a ν (s - r) (fun y => s84_Bop ρ (w₂ s) y) x
      rw [hfun]
      exact s84_P_sub ha hν hs.1 (hqc1 s hs') (hqc2 s hs') (hb1 s hs') (hb2 s hs') x
    show w₁ r x - w₂ r x = s83_P a ν (t - r) (fun y => w₁ t y - w₂ t y) x +
      ∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (fun y => w₁ s y - w₂ s y) y) x
    rw [hP0, hI, m1, m2]; ring
  · exact sol₁.term_cont.sub sol₂.term_cont
  · refine ⟨B1a + B1b, B2a + B2b, fun r hr y => ?_⟩
    have d1 : Differentiable ℝ (w₁ r) := (sol₁.c2 r hr).differentiable (by norm_num)
    have d2 : Differentiable ℝ (w₂ r) := (sol₂.c2 r hr).differentiable (by norm_num)
    have dd1 : Differentiable ℝ (fderiv ℝ (w₁ r)) :=
      ((sol₁.c2 r hr).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have dd2 : Differentiable ℝ (fderiv ℝ (w₂ r)) :=
      ((sol₂.c2 r hr).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have e1 : fderiv ℝ (fun y => w₁ r y - w₂ r y) = fun y => fderiv ℝ (w₁ r) y - fderiv ℝ (w₂ r) y := by
      funext y; exact fderiv_sub (d1 y) (d2 y)
    rw [e1]
    refine ⟨(norm_sub_le _ _).trans (add_le_add (hBa r hr y).1 (hBb r hr y).1), ?_⟩
    have e2 : fderiv ℝ (fun y => fderiv ℝ (w₁ r) y - fderiv ℝ (w₂ r) y) y =
        fderiv ℝ (fderiv ℝ (w₁ r)) y - fderiv ℝ (fderiv ℝ (w₂ r)) y := fderiv_sub (dd1 y) (dd2 y)
    rw [e2]
    have n1 := hBa r hr y
    have n2 := hBb r hr y
    exact le_trans (norm_sub_le (fderiv ℝ (fderiv ℝ (w₁ r)) y) (fderiv ℝ (fderiv ℝ (w₂ r)) y))
      (add_le_add n1.2 n2.2)

/-- **Lipschitz dependence on the terminal datum.** -/
theorem s84_apriori_sub (hd : 2 ≤ d) {a ν T M : ℝ} (ha : 0 < a) (hν : 0 < ν) (hT : 0 < T) (hM : 0 ≤ M)
    {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ₁ Φ₂ Φ : ℝ} {w₁ w₂ : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      S84Sol ρ a ν t M Φ₁ w₁ → S84Sol ρ a ν t M Φ₂ w₂ → Wt M Φ (fun y => w₁ t y - w₂ t y) →
      ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |w₁ r y - w₂ r y| ≤ K * Φ * jbracket y ^ M := by
  obtain ⟨K, hK0, hK⟩ := s84_apriori hd ha hν hT hM hρ
  exact ⟨K, hK0, fun ht htT sol₁ sol₂ hΦ => hK ht htT (s84_sol_sub hd ha hν hρ hM ht sol₁ sol₂ hΦ)⟩

end HRS.MS.Wad
