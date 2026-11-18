import HRS.MS.FixEqP3Aux8
import HRS.MS.FixEqP3Aux7

/-!
# S5.7 `fixed_equation` (worker S57P), part 21: the noise kernels of a family

The weight `w = √(2 q ρ)` (jointly measurable, `∫ w(r,x)² dx = 2q`), the gradient field `A_t φ (r,x) = ∇U^{r,t}φ (x)` (continuous, linear in `φ`,
bounded by the `C^1` jets of the orbit) and the terminal-time Hölder bound `|A_t φ - A_s φ| ≤ B_d (t-s)` (`s57p_td_bound`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_td_bound {C : WholeCoeff d} {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} (hθ : IsUlCutoff θ)
    (Fm : S57pFam C θ T (n + 1) K) (hn4 : 4 ≤ n) {φ : Euc d → ℝ} {Bφ Bg : ℝ} (hBφ : 0 ≤ Bφ) (hBg : 0 ≤ Bg)
    (hφ : ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) φ)
    (hφb : ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l φ x‖ ≤ Bφ)
    (hg : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ ((n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (generatorW C u φ) ∧
      ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ l (generatorW C u φ) x‖ ≤ Bg)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∀ r ∈ Set.Icc (0 : ℝ) s, ∀ i ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => propagatorW C r t φ y - propagatorW C r s φ y) x‖ ≤
        |K| * (s57pCu θ hθ (n + 1) * Bg) * (t - s) := by
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  intro r hr i hi x
  rw [s57p_td_int hθ Fm hn4 hBφ hBg hφ hφb hg hs hst ht r hr i hi x]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
    (f := fun u => iteratedFDeriv ℝ i (propagatorW C r u (generatorW C u φ)) x)
    (C := |K| * (s57pCu θ hθ (n + 1) * Bg)) (fun u hu => by
      rw [Set.uIoc_of_le hst] at hu
      have huT : u ∈ Set.Icc (0 : ℝ) T := ⟨hs.trans hu.1.le, hu.2.trans ht⟩
      exact ((hCu Fm.adj hBg (hg u huT).1 (hg u huT).2 u huT).2 r ⟨hr.1, hr.2.trans hu.1.le⟩).2 i (by omega) x)
  rw [abs_of_nonneg (sub_nonneg.2 hst)] at this
  exact this

/-! ### The weight -/

/-- the clamped density -/
def s57pρc (T : ℝ) (ρ : ℝ → Euc d → ℝ) (p : ℝ × Euc d) : ℝ := ρ (max 0 (min p.1 T)) p.2

theorem s57p_rhoc_meas {s : ℝ} {Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ}
    {T : ℝ} (hD : S57pFeData s Q ν c ρ T) (hT : 0 ≤ T) : Measurable (s57pρc T ρ) := by
  obtain ⟨A, hA, hdec, hpt⟩ := hD.rho
  have hcl : ∀ r : ℝ, max 0 (min r T) ∈ Set.Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hclc : Continuous fun r : ℝ => max 0 (min r T) := continuous_const.max (continuous_id.min continuous_const)
  let u : Euc d → ℝ → ℝ := fun x r => ρ (max 0 (min r T)) x
  have hu1 : ∀ r, Continuous fun x => u x r := fun r =>
    (rg_decay_parts (n := 3) (by norm_num) (a := fun _ => A) (fun _ => hA) (hdec _ (hcl r))).1.continuous
  have hu2 : ∀ x, Measurable (u x) := fun x =>
    ((hpt x).comp_continuous hclc hcl).measurable
  have := measurable_uncurry_of_continuous_of_measurable hu1 hu2
  exact this.comp measurable_swap

/-- the weight `√(2 q ρ)` -/
def s57pw (T q : ℝ) (ρ : ℝ → Euc d → ℝ) : ℝ × Euc d → ℝ := fun p => Real.sqrt (2 * q * s57pρc T ρ p)

theorem s57p_wdata {s : ℝ} {Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ}
    {T : ℝ} (hD : S57pFeData s Q ν c ρ T) (hT : 0 ≤ T) {q : ℝ} (hq : 0 ≤ q)
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t)) : S57pKd T (s57pw T q ρ) (2 * q) := by
  refine ⟨hT, ?_, by positivity, fun r hr => ?_⟩
  · exact (measurable_const.mul (s57p_rhoc_meas hD hT)).sqrt
  · have hcl : max 0 (min r T) = r := by rw [min_eq_left hr.2, max_eq_right hr.1]
    have hP := hprob r hr
    have hint : Integrable (ρ r) := Integrable.of_integral_ne_zero (by rw [hP.integral_one]; norm_num)
    have e : ∀ x : Euc d, s57pw T q ρ (r, x) ^ 2 = 2 * q * ρ r x := by
      intro x
      simp only [s57pw, s57pρc, hcl]
      rw [Real.sq_sqrt (mul_nonneg (by positivity) (hP.nonneg x))]
    simp_rw [e]
    have e2 : ∀ x : Euc d, ENNReal.ofReal (2 * q * ρ r x) = ENNReal.ofReal (2 * q) * ENNReal.ofReal (ρ r x) :=
      fun x => ENNReal.ofReal_mul (by positivity)
    simp_rw [e2]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall hP.nonneg), hP.integral_one]
    simp

/-! ### The gradient field -/

/-- `A_t φ (r,x) = ∇ U^{r,t} φ (x)` (with `r` clamped to `[0,t]`) -/
def s57pA (C : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (p : ℝ × Euc d) : Euc d :=
  gradient (propagatorW C (max 0 (min p.1 t)) t φ) p.2

theorem s57p_norm_gradient (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [norm_iteratedFDeriv_one]
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

theorem s57p_A_cont {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} (ht : 0 ≤ t)
    (h : IsClassicalAdjointW C t φ (fun r => propagatorW C r t φ)) : Continuous (s57pA C t φ) := by
  have h1 := h.cont_c2 1 (by norm_num)
  have hcl : Continuous fun q : ℝ × Euc d => ((⟨max 0 (min q.1 t), le_max_left _ _,
      max_le ht (min_le_right _ _)⟩ : Set.Icc (0 : ℝ) t), q.2) :=
    (((continuous_const.max ((continuous_fst).min continuous_const)).subtype_mk _).prodMk continuous_snd)
  have h2 := h1.comp hcl
  have e : s57pA C t φ = fun q : ℝ × Euc d => s57pLg d (iteratedFDeriv ℝ 1 (propagatorW C (max 0 (min q.1 t)) t φ) q.2) := by
    funext q; exact s57p_gradient_eq_Lg _ _
  rw [e]
  exact (s57pLg d).continuous.comp h2

theorem s57p_A_bound {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} (ht : 0 ≤ t) {B : ℝ}
    (hb : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ 1 (propagatorW C r t φ) x‖ ≤ B) (p : ℝ × Euc d) :
    ‖s57pA C t φ p‖ ≤ B := by
  unfold s57pA
  rw [s57p_norm_gradient]
  exact hb _ ⟨le_max_left _ _, max_le ht (min_le_right _ _)⟩ _

theorem s57p_gradient_lin2 {f₁ f₂ : Euc d → ℝ} (h₁ : ContDiff ℝ 1 f₁) (h₂ : ContDiff ℝ 1 f₂) (a b : ℝ) (x : Euc d) :
    gradient (fun y => a * f₁ y + b * f₂ y) x = a • gradient f₁ x + b • gradient f₂ x := by
  rw [s57p_gradient_eq_Lg, s57p_gradient_eq_Lg, s57p_gradient_eq_Lg, s57p_iter_lin2 h₁ h₂, map_add, map_smul, map_smul]

theorem s57p_A_sub {C : WholeCoeff d} {t : ℝ} {φ ψ : Euc d → ℝ} (ht : 0 ≤ t) (p : ℝ × Euc d)
    (h₁ : ContDiff ℝ 1 (propagatorW C (max 0 (min p.1 t)) t φ)) (h₂ : ContDiff ℝ 1 (propagatorW C (max 0 (min p.1 t)) t ψ)) :
    s57pA C t φ p - s57pA C t ψ p = gradient (fun y => propagatorW C (max 0 (min p.1 t)) t φ y -
      propagatorW C (max 0 (min p.1 t)) t ψ y) p.2 := by
  unfold s57pA
  rw [HRS.MS.Fcau.fcau_gradient_sub h₁ h₂]

end HRS.MS.FixEq
