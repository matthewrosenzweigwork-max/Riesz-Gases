import HRS.MS.FixEqP3Aux10

/-!
# S5.7 `fixed_equation` (worker S57P), part 23: Hilbert-Schmidt bounds of the noise kernels

`‖κ_t(φ_α)‖² ≤ 2q T (C_a λ_α^e)²` and `‖κ_{t₂}(φ_α) - κ_{t₁}(φ_α)‖² ≤ 2q((C_dλ_α^e)²(t₂-t₁)²T + (C_aλ_α^e)²(t₂-t₁))`
(`e = (J-m)/2`), hence `∑_α ‖κ_t α‖² < ∞` and `∑_α ‖κ_{t₂} α - κ_{t₁} α‖² ≤ K_h |t₂ - t₁|` (`s57p_kappa_hs`).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

theorem s57p_summable_J (hd : 1 ≤ d) {m : ℝ} {J : ℕ} (hm : (J : ℝ) + d < m) :
    Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m) := by
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have h := (summable_oscEigenvalue_rpow_iff (d := d) (by omega) (m - J)).2 (by linarith)
  simpa [neg_sub] using h

theorem s57p_A_holder {C : WholeCoeff d} {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) {φ : Euc d → ℝ} {B : ℝ}
    (hc₁ : ∀ r ∈ Set.Icc (0 : ℝ) t₁, ContDiff ℝ 1 (propagatorW C r t₁ φ))
    (hc₂ : ∀ r ∈ Set.Icc (0 : ℝ) t₂, ContDiff ℝ 1 (propagatorW C r t₂ φ))
    (hb : ∀ r ∈ Set.Icc (0 : ℝ) t₁, ∀ x,
      ‖iteratedFDeriv ℝ 1 (fun y => propagatorW C r t₂ φ y - propagatorW C r t₁ φ y) x‖ ≤ B)
    (p : ℝ × Euc d) (hp : p.1 ∈ Set.Icc (0 : ℝ) t₁) : ‖s57pA C t₂ φ p - s57pA C t₁ φ p‖ ≤ B := by
  unfold s57pA
  have e1 : max 0 (min p.1 t₂) = p.1 := by rw [min_eq_left (hp.2.trans h12), max_eq_right hp.1]
  have e2 : max 0 (min p.1 t₁) = p.1 := by rw [min_eq_left hp.2, max_eq_right hp.1]
  rw [e1, e2, ← HRS.MS.Fcau.fcau_gradient_sub (hc₂ p.1 ⟨hp.1, hp.2.trans h12⟩) (hc₁ p.1 hp), s57p_norm_gradient]
  exact hb p.1 hp p.2

variable {θ : Euc d → ℝ} {T : ℝ} {n : ℕ} {K : ℝ} {s : ℝ} {M Q : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ}
  {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {A Λc νbar : ℝ} {m : ℝ} {J : ℕ} {Ca Cd : ℝ}

theorem s57p_kappa_norm (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) (hCa : 0 ≤ Ca) {q : ℝ} (hq : 0 ≤ q)
    (α : MultiIndex d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)‖ ^ 2 ≤
      T * (2 * q) * (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 := by
  obtain ⟨h1, h2⟩ := (hbd α).1 t ht
  exact s57p_el_norm (s57p_wdata Fx.fe Fx.hT hq Fx.prob) (s57p_A_cont ht.1 h1).aestronglyMeasurable
    (t := t) (Ba := Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2))
    (fun p _ => s57p_A_bound ht.1 (fun r hr x => (h2 r hr).2 1 (by omega) x) p)

theorem s57p_kappa_holder (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) {q : ℝ} (hq : 0 ≤ q)
    (α : MultiIndex d) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (h2T : t₂ ≤ T) :
    ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₂ (oscTestFun m α) -
        s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₁ (oscTestFun m α)‖ ^ 2 ≤
      (2 * q) * ((Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 * (t₂ - t₁) ^ 2 * T +
        (Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 * (t₂ - t₁)) := by
  have ht1 : t₁ ∈ Set.Icc (0 : ℝ) T := ⟨h0, h12.trans h2T⟩
  have ht2 : t₂ ∈ Set.Icc (0 : ℝ) T := ⟨h0.trans h12, h2T⟩
  obtain ⟨h1a, h1b⟩ := (hbd α).1 t₁ ht1
  obtain ⟨h2a, h2b⟩ := (hbd α).1 t₂ ht2
  have hB1 : ∀ p, ‖s57pA (fixedEqCoeff s M Q ν c ρ) t₁ (oscTestFun m α) p‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    s57p_A_bound ht1.1 (fun r hr x => (h1b r hr).2 1 (by omega) x)
  have hB2 : ∀ p, ‖s57pA (fixedEqCoeff s M Q ν c ρ) t₂ (oscTestFun m α) p‖ ≤ Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    s57p_A_bound ht2.1 (fun r hr x => (h2b r hr).2 1 (by omega) x)
  exact s57p_el_holder (s57p_wdata Fx.fe Fx.hT hq Fx.prob) (s57p_A_cont ht2.1 h2a).aestronglyMeasurable
    (s57p_A_cont ht1.1 h1a).aestronglyMeasurable (s := t₁) (t := t₂)
    (Ba := Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) (Bd := Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) h12
    (fun p _ => hB2 p) (fun p _ => hB1 p)
    (fun p hp => s57p_A_holder h0 h12 (fun r hr => (h1b r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)))
      (fun r hr => (h2b r hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ n + 1)))
      (fun r hr x => (hbd α).2 t₁ t₂ h0 h12 h2T r hr 1 (by have := Fx.hn4; omega) x) p hp)

theorem s57p_kappa_hs (Fx : S57pFx θ T n K s M Q ν c ρ A Λc νbar)
    (hbd : S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd) (hCa : 0 ≤ Ca) (hCd : 0 ≤ Cd) {q : ℝ} (hq : 0 ≤ q)
    (hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ ((J : ℝ) - m)) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, Summable fun α : MultiIndex d =>
      ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t (oscTestFun m α)‖ ^ 2) ∧
    ∀ t₁ ∈ Set.Icc (0 : ℝ) T, ∀ t₂ ∈ Set.Icc (0 : ℝ) T,
      ∑' α : MultiIndex d, ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₂ (oscTestFun m α) -
          s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₁ (oscTestFun m α)‖ ^ 2 ≤
        (2 * q * ((Cd ^ 2 * T ^ 2 + Ca ^ 2) * ∑' α : MultiIndex d, oscEigenvalue d α ^ ((J : ℝ) - m))) * |t₂ - t₁| := by
  have hT := Fx.hT
  have hsq : ∀ (C0 : ℝ) (α : MultiIndex d), (C0 * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ^ 2 =
      C0 ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m) := by
    intro C0 α; rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  have hpos : ∀ α : MultiIndex d, 0 < oscEigenvalue d α ^ ((J : ℝ) - m) := fun α => Real.rpow_pos_of_pos (oscEv_pos α) _
  refine ⟨fun t ht => ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_)
      (hsum.mul_left (T * (2 * q) * Ca ^ 2))
    refine (s57p_kappa_norm Fx hbd hCa hq α ht).trans (le_of_eq ?_)
    rw [hsq]; ring
  · have hk : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) T → b ∈ Set.Icc (0 : ℝ) T → a ≤ b → ∀ α : MultiIndex d,
        ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ b (oscTestFun m α) -
          s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ a (oscTestFun m α)‖ ^ 2 ≤
        (2 * q * (Cd ^ 2 * T ^ 2 + Ca ^ 2)) * oscEigenvalue d α ^ ((J : ℝ) - m) * (b - a) := by
      intro a b ha hb hab α
      refine (s57p_kappa_holder Fx hbd hq α ha.1 hab hb.2).trans ?_
      rw [hsq, hsq]
      have h1 : 0 ≤ b - a := sub_nonneg.2 hab
      have h2 : b - a ≤ T := by linarith [ha.1, hb.2]
      have h3 : (b - a) ^ 2 * T ≤ T ^ 2 * (b - a) := by nlinarith [mul_nonneg h1 hT]
      have h4 := hpos α
      have h5 : 0 ≤ Cd ^ 2 * oscEigenvalue d α ^ ((J : ℝ) - m) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 h5, mul_nonneg (mul_nonneg hq (sq_nonneg Ca)) (mul_nonneg h4.le h1)]
    intro t₁ ht₁ t₂ ht₂
    have hsym : ∀ α : MultiIndex d, ‖s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₂ (oscTestFun m α) -
          s57pκ (fixedEqCoeff s M Q ν c ρ) T q ρ t₁ (oscTestFun m α)‖ ^ 2 ≤
        (2 * q * (Cd ^ 2 * T ^ 2 + Ca ^ 2)) * oscEigenvalue d α ^ ((J : ℝ) - m) * |t₂ - t₁| := by
      intro α
      rcases le_total t₁ t₂ with h | h
      · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact hk t₁ t₂ ht₁ ht₂ h α
      · rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub, ← norm_neg, neg_sub]
        exact hk t₂ t₁ ht₂ ht₁ h α
    have hs2 : Summable fun α : MultiIndex d => (2 * q * (Cd ^ 2 * T ^ 2 + Ca ^ 2)) * oscEigenvalue d α ^ ((J : ℝ) - m) *
        |t₂ - t₁| := (hsum.mul_left (2 * q * (Cd ^ 2 * T ^ 2 + Ca ^ 2))).mul_right _
    refine (Summable.tsum_le_tsum hsym (Summable.of_nonneg_of_le (fun α => sq_nonneg _) hsym hs2) hs2).trans (le_of_eq ?_)
    rw [tsum_mul_right, tsum_mul_left]
    ring

end HRS.MS.FixEq
