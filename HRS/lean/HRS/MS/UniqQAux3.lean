import HRS.MS.UniqQAux2

/-!
# UNIQ-Q, part 3: linearity, translation, second differences, the power sum, the discrete Duhamel identity

(plan: `UniqQAux1`.)

* `uniqq_ouSg_sub/add`, `uniqq_ouSg_trans`: linearity of `P_τ` on the class `UqCB1` and the translation identity
  `P_τ g (x + a) = P_τ (g(· + e^{-τQ} a)) (x)`.
* `uniqq_second_diff`: `|Δ_aΔ_e P_τ g| ≤ C τ^{-(1+β)/2} B |a|^β |e|` for `g ∈ UqCB1 g B M`, `β ∈ [0,1]`.
* `uniqq_sum_rpow`: `∑_{i=1}^{m} i^{-γ} ≤ m^{1-γ}/(1-γ)`, `0 ≤ γ < 1`.
* `uniqq_tel`: `v 0 = ∑_{i<k} P_{ih} E_i + P_{kh} v_k`, `E_i = v_i - P_h v_{i+1}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem uniqq_int_cb {g : Euc d → ℝ} (hg : Continuous g) {B : ℝ} (hb : ∀ y, |g y| ≤ B)
    (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) (x : Euc d) :
    Integrable (fun y => g (ouExp Q τ x + y)) (ouLaw Q ν τ) :=
  Integrable.of_bound (hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb _)

theorem uniqq_ouSg_sub (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {f f' : Euc d → ℝ} {B B' M M' : ℝ}
    (hf : UqCB1 f B M) (hf' : UqCB1 f' B' M') (x : Euc d) :
    ouSg Q ν τ (fun y => f y - f' y) x = ouSg Q ν τ f x - ouSg Q ν τ f' x := by
  unfold ouSg
  exact integral_sub (uniqq_int_cb hf.1.continuous hf.2.1 Q ν τ x)
    (uniqq_int_cb hf'.1.continuous hf'.2.1 Q ν τ x)

theorem uniqq_ouSg_add (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {f f' : Euc d → ℝ} {B B' M M' : ℝ}
    (hf : UqCB1 f B M) (hf' : UqCB1 f' B' M') (x : Euc d) :
    ouSg Q ν τ (fun y => f y + f' y) x = ouSg Q ν τ f x + ouSg Q ν τ f' x := by
  unfold ouSg
  exact integral_add (uniqq_int_cb hf.1.continuous hf.2.1 Q ν τ x)
    (uniqq_int_cb hf'.1.continuous hf'.2.1 Q ν τ x)

theorem uniqq_ouSg_trans (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) (g : Euc d → ℝ) (x a : Euc d) :
    ouSg Q ν τ g (x + a) = ouSg Q ν τ (fun y => g (y + ouExp Q τ a)) x := by
  unfold ouSg
  congr 1
  funext y
  rw [map_add]
  congr 1
  abel

/-- `min 2 z ≤ 2^{1-β} z^β` -/
theorem uniqq_min_le {z β : ℝ} (hz : 0 ≤ z) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    min 2 z ≤ (2 : ℝ) ^ (1 - β) * z ^ β := by
  rcases le_total z 2 with h | h
  · rw [min_eq_right h]
    have : z = z ^ (1 - β) * z ^ β := by
      rw [← Real.rpow_add' hz (by linarith)]; simp
    calc z = z ^ (1 - β) * z ^ β := this
      _ ≤ (2 : ℝ) ^ (1 - β) * z ^ β := by
        gcongr
  · rw [min_eq_left h]
    have : (2 : ℝ) = (2 : ℝ) ^ (1 - β) * (2 : ℝ) ^ β := by
      rw [← Real.rpow_add (by norm_num)]; simp
    calc (2 : ℝ) = (2 : ℝ) ^ (1 - β) * (2 : ℝ) ^ β := this
      _ ≤ (2 : ℝ) ^ (1 - β) * z ^ β := by
        gcongr

/-- **second differences of `P_τ g`** -/
theorem uniqq_second_diff (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T0 : ℝ) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ T0 → ∀ (g : Euc d → ℝ) (B M : ℝ), UqCB1 g B M →
      ∀ x a e : Euc d,
        |ouSg Q ν τ g (x + a + e) - ouSg Q ν τ g (x + a) - ouSg Q ν τ g (x + e) + ouSg Q ν τ g x| ≤
          C3 * τ ^ (-((1 + β) / 2)) * B * ‖a‖ ^ β * ‖e‖ := by
  obtain ⟨Cl, hCl0, hCl⟩ := uniqq_lip Q hν T0
  obtain ⟨K, hK1, hK⟩ := ul2_exp_bound Q T0
  have hK0 : 0 < K := by linarith
  refine ⟨Cl * (Cl * K) ^ β * 2 ^ (1 - β) * 2 ^ ((1 + β) / 2), by positivity,
    fun τ hτ hτT g B M hg x a e => ?_⟩
  set θ : ℝ := τ / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθT : θ ≤ T0 := by rw [hθ]; linarith
  have hKθ : ‖ouExp Q θ‖ ≤ K := hK θ (by rw [abs_of_pos hθ0]; exact hθT)
  have hB := hg.B_nonneg
  have hg1 : UqCB1 (ouSg Q ν θ g) B (M * K) := uniqq_cb1_ouSg Q ν hKθ hg
  have hgc : Continuous g := hg.1.continuous
  have hsg : ∀ y, ouSg Q ν τ g y = ouSg Q ν θ (ouSg Q ν θ g) y := by
    intro y
    have := ul4_semigroup Q hν.le hθ0.le hθ0.le hgc hg.2.1 y
    rwa [show θ + θ = τ by rw [hθ]; ring] at this
  set gt : Euc d → ℝ := ouSg Q ν θ g with hgt
  set A' : Euc d →L[ℝ] Euc d := ouExp Q θ with hA'
  set k : Euc d → ℝ := fun y => gt (y + A' a) - gt y with hk
  have hk1 : UqCB1 k (B + B) (M * K + M * K) :=
    uniqq_cb1_sub (uniqq_cb1_trans hg1 (A' a)) hg1
  set z : ℝ := Cl * K * θ ^ (-(1 / 2 : ℝ)) * ‖a‖ with hz
  have hz0 : 0 ≤ z := by positivity
  have hkB : ∀ y, |k y| ≤ B * min 2 z := by
    intro y
    have h1 : |k y| ≤ B * 2 := by
      have := (abs_sub (gt (y + A' a)) (gt y)).trans (add_le_add (hg1.2.1 _) (hg1.2.1 y))
      simp only [hk]; linarith
    have h2 : |k y| ≤ B * z := by
      have := hCl θ hθ0 hθT g B M hg (y + A' a) y
      have h3 : ‖y + A' a - y‖ ≤ K * ‖a‖ := by
        rw [add_sub_cancel_left]
        exact (A'.le_opNorm a).trans (mul_le_mul_of_nonneg_right hKθ (norm_nonneg _))
      simp only [hk]
      refine this.trans ?_
      calc Cl * θ ^ (-(1 / 2 : ℝ)) * B * ‖y + A' a - y‖ ≤ Cl * θ ^ (-(1 / 2 : ℝ)) * B * (K * ‖a‖) := by
            gcongr
        _ = B * z := by rw [hz]; ring
    rw [mul_min_of_nonneg _ _ hB]
    exact le_min h1 h2
  have hk2 : UqCB1 k (B * min 2 z) (M * K + M * K) := ⟨hk1.1, hkB, hk1.2.2⟩
  -- the identity
  have hid : ouSg Q ν τ g (x + a + e) - ouSg Q ν τ g (x + a) - ouSg Q ν τ g (x + e) + ouSg Q ν τ g x =
      ouSg Q ν θ k (x + e) - ouSg Q ν θ k x := by
    have ht : ∀ y, ouSg Q ν θ gt (y + a) - ouSg Q ν θ gt y = ouSg Q ν θ k y := by
      intro y
      rw [uniqq_ouSg_trans, ← uniqq_ouSg_sub Q ν θ (uniqq_cb1_trans hg1 (A' a)) hg1]
    rw [hsg, hsg, hsg, hsg]
    have h1 := ht (x + e)
    have h2 := ht x
    rw [show x + e + a = x + a + e by abel] at h1
    linarith
  rw [hid]
  have hlip := hCl θ hθ0 hθT k (B * min 2 z) _ hk2 (x + e) x
  rw [add_sub_cancel_left] at hlip
  refine hlip.trans ?_
  have hmin : B * min 2 z ≤ B * ((2 : ℝ) ^ (1 - β) * z ^ β) :=
    mul_le_mul_of_nonneg_left (uniqq_min_le hz0 hβ0 hβ1) hB
  have e1 : z ^ β = (Cl * K) ^ β * θ ^ (-(β / 2)) * ‖a‖ ^ β := by
    rw [hz, Real.mul_rpow (by positivity) (norm_nonneg _), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hθ0.le]
    congr 3
    ring
  have e2 : θ ^ (-(1 / 2 : ℝ)) * θ ^ (-(β / 2)) = θ ^ (-((1 + β) / 2)) := by
    rw [← Real.rpow_add hθ0]; congr 1; ring
  have e3 : θ ^ (-((1 + β) / 2)) = 2 ^ ((1 + β) / 2) * τ ^ (-((1 + β) / 2)) := by
    have : τ = 2 * θ := by rw [hθ]; ring
    rw [this, Real.mul_rpow (by norm_num) hθ0.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
    simp
  calc Cl * θ ^ (-(1 / 2 : ℝ)) * (B * min 2 z) * ‖e‖
      ≤ Cl * θ ^ (-(1 / 2 : ℝ)) * (B * ((2 : ℝ) ^ (1 - β) * z ^ β)) * ‖e‖ := by gcongr
    _ = Cl * (Cl * K) ^ β * 2 ^ (1 - β) * (θ ^ (-(1 / 2 : ℝ)) * θ ^ (-(β / 2))) * B * ‖a‖ ^ β * ‖e‖ := by
        rw [e1]; ring
    _ = _ := by rw [e2, e3]; ring

theorem uniqq_pow_step {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {m : ℝ} (hm : 0 ≤ m) :
    (1 - γ) * (m + 1) ^ (-γ) ≤ (m + 1) ^ (1 - γ) - m ^ (1 - γ) := by
  have hm1 : 0 < m + 1 := by linarith
  have hp0 : 0 ≤ 1 - γ := by linarith
  have hp1 : 1 - γ ≤ 1 := by linarith
  have h := rpow_one_add_le_one_add_mul_self (s := -1 / (m + 1)) (by
    rw [le_div_iff₀ hm1]; linarith) hp0 hp1
  have e1 : 1 + -1 / (m + 1) = m / (m + 1) := by field_simp; ring
  rw [e1] at h
  have h2 : (m / (m + 1)) ^ (1 - γ) * (m + 1) ^ (1 - γ) = m ^ (1 - γ) := by
    rw [← Real.mul_rpow (div_nonneg hm hm1.le) hm1.le, div_mul_cancel₀ _ hm1.ne']
  have h3 : (m + 1) ^ (1 - γ) = (m + 1) ^ (-γ) * (m + 1) := by
    rw [show 1 - γ = -γ + 1 by ring, Real.rpow_add hm1, Real.rpow_one]
  have h4 := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hm1.le (1 - γ))
  rw [h2] at h4
  have h5 : (1 + (1 - γ) * (-1 / (m + 1))) * (m + 1) ^ (1 - γ) =
      (m + 1) ^ (1 - γ) - (1 - γ) * (m + 1) ^ (-γ) := by
    rw [h3]; field_simp; ring
  linarith

theorem uniqq_sum_rpow {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) (m : ℕ) :
    ∑ i ∈ Finset.range m, ((i + 1 : ℕ) : ℝ) ^ (-γ) ≤ (m : ℝ) ^ (1 - γ) / (1 - γ) := by
  have hp : 0 < 1 - γ := by linarith
  induction m with
  | zero => simp [Real.zero_rpow hp.ne']
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hs := uniqq_pow_step h0 h1 (m := (m : ℝ)) (Nat.cast_nonneg m)
    have e : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [e]
    have : ((m : ℝ) + 1) ^ (-γ) ≤ (((m : ℝ) + 1) ^ (1 - γ) - (m : ℝ) ^ (1 - γ)) / (1 - γ) := by
      rw [le_div_iff₀ hp]; linarith
    calc _ ≤ (m : ℝ) ^ (1 - γ) / (1 - γ) + (((m : ℝ) + 1) ^ (1 - γ) - (m : ℝ) ^ (1 - γ)) / (1 - γ) :=
          add_le_add ih this
      _ = _ := by ring

/-- **the discrete Duhamel identity** -/
theorem uniqq_tel (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 ≤ ν) {h : ℝ} (hh : 0 ≤ h) {K : ℝ}
    (hK : ‖ouExp Q h‖ ≤ K) {v : ℕ → Euc d → ℝ} {Bv Mv : ℝ} (hv : ∀ k, UqCB1 (v k) Bv Mv)
    (y : Euc d) (k : ℕ) :
    v 0 y = ∑ i ∈ Finset.range k,
        ouSg Q ν ((i : ℝ) * h) (fun z => v i z - ouSg Q ν h (v (i + 1)) z) y +
      ouSg Q ν ((k : ℝ) * h) (v k) y := by
  induction k with
  | zero => simp [ouSg_zero Q hν]
  | succ k ih =>
    rw [ih, Finset.sum_range_succ]
    have hP : UqCB1 (ouSg Q ν h (v (k + 1))) Bv (Mv * K) := uniqq_cb1_ouSg Q ν hK (hv (k + 1))
    have hE : UqCB1 (fun z => v k z - ouSg Q ν h (v (k + 1)) z) (Bv + Bv) (Mv + Mv * K) :=
      uniqq_cb1_sub (hv k) hP
    have e1 : v k = fun z => (v k z - ouSg Q ν h (v (k + 1)) z) + ouSg Q ν h (v (k + 1)) z := by
      funext z; ring
    have e2 : ouSg Q ν ((k : ℝ) * h) (v k) y =
        ouSg Q ν ((k : ℝ) * h) (fun z => v k z - ouSg Q ν h (v (k + 1)) z) y +
          ouSg Q ν (((k + 1 : ℕ) : ℝ) * h) (v (k + 1)) y := by
      conv_lhs => rw [e1]
      rw [uniqq_ouSg_add Q ν _ hE hP]
      congr 1
      have := ul4_semigroup Q hν (mul_nonneg (Nat.cast_nonneg k) hh) hh (hv (k + 1)).1.continuous
        (hv (k + 1)).2.1 y
      rw [← this]
      congr 1
      push_cast; ring
    rw [e2]
    ring

end HRS.MS.UniqQ
