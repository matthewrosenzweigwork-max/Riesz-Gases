import HRS.PDE.MovFAux12
import HRS.PDE.MovAAux23

/-!
# MOVF Aux13: Lipschitz estimate of the transport field in terms of the distance to a stationary density
(bridge B).  `movf_lip_diff`: if `mfeTransport D ρβ = 0` then `Lip(mfeTransport D ρ) ≤ K ‖ρ - ρβ‖_{C²}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_lip_mul {f g : Torus d → ℝ} {La Lb Bf Bg : ℝ} (hf : KernelGrad.IsLipschitz La f)
    (hg : KernelGrad.IsLipschitz Lb g) (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    KernelGrad.IsLipschitz (La * Bg + Bf * Lb) (fun x => f x * g x) := by
  intro x y
  have e : f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := hf x y
  have h2 := hg x y
  have h3 : |f x - f y| * |g x| ≤ La * KernelGrad.tdist x y * Bg :=
    mul_le_mul h1 (hBg x) (abs_nonneg _) ((abs_nonneg _).trans h1)
  have h4 : |f y| * |g x - g y| ≤ Bf * (Lb * KernelGrad.tdist x y) :=
    mul_le_mul (hBf y) h2 (abs_nonneg _) ((abs_nonneg _).trans (hBf y))
  nlinarith

theorem movf_lip_inv {q : Torus d → ℝ} {Lq c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x, c₀ ≤ q x)
    (hq : KernelGrad.IsLipschitz Lq q) :
    KernelGrad.IsLipschitz (Lq / c₀ ^ 2) (fun x => 1 / q x) := by
  intro x y
  have hx := lt_of_lt_of_le hc₀ (hlow x)
  have hy := lt_of_lt_of_le hc₀ (hlow y)
  have e : 1 / q x - 1 / q y = (q y - q x) / (q x * q y) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hx hy)]
  have h1 : |q y - q x| ≤ Lq * KernelGrad.tdist x y := by
    have := hq y x
    rwa [KernelGrad.tdist_sub_comm y x] at this
  have hd : c₀ ^ 2 ≤ q x * q y := by rw [sq]; exact mul_le_mul (hlow x) (hlow y) hc₀.le hx.le
  have ht := KernelGrad.tdist_nonneg x y
  have hL : 0 ≤ Lq * KernelGrad.tdist x y := (abs_nonneg _).trans h1
  calc |q y - q x| / (q x * q y) ≤ (Lq * KernelGrad.tdist x y) / (q x * q y) :=
        div_le_div_of_nonneg_right h1 (mul_pos hx hy).le
    _ ≤ (Lq * KernelGrad.tdist x y) / c₀ ^ 2 :=
        div_le_div_of_nonneg_left hL (by positivity) hd
    _ = Lq / c₀ ^ 2 * KernelGrad.tdist x y := by ring

theorem movf_abs_inv {q : Torus d → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x, c₀ ≤ q x) (x : Torus d) :
    |1 / q x| ≤ 1 / c₀ := by
  have hx := lt_of_lt_of_le hc₀ (hlow x)
  rw [abs_of_pos (by positivity)]
  exact one_div_le_one_div_of_le hc₀ (hlow x)

theorem movf_lip_diff (D : DynData d) (hκ : 0 < D.invβ) (c₀ Λ : ℝ) (hc₀ : 0 < c₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ ρβ : Torus d → ℝ}, Torus.IsCk 2 ρ → Torus.IsCk 2 ρβ →
      (∀ x, c₀ ≤ ρ x) → (∀ x, c₀ ≤ ρβ x) → Torus.cbNorm 2 ρ ≤ Λ → Torus.cbNorm 2 ρβ ≤ Λ →
      (∀ x, mfeTransport D ρβ x = 0) →
      IsLipschitzVF (K * Torus.cbNorm 2 (fun x => ρ x - ρβ x)) (mfeTransport D ρ) := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have hL1 := mova_L1_nonneg (periodicRiesz d D.s)
  set K1 : ℝ := 1 / c₀ + Λ / c₀ ^ 2 with hK1
  set K2 : ℝ := 2 * Λ / c₀ ^ 2 + 2 * Λ ^ 2 / c₀ ^ 3 with hK2
  refine ⟨max 0 (d * (D.invβ * (K1 + K2) + mova_L1 (periodicRiesz d D.s))), le_max_left _ _, ?_⟩
  intro ρ ρβ hρ hρβ hlow hlowβ hΛ hΛβ heq
  have hρ1 := mova_isCk_one_of_two hρ
  have hρβ1 := mova_isCk_one_of_two hρβ
  have hpos : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le hc₀ (hlow x)
  have hposβ : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le hc₀ (hlowβ x)
  have hΛ0 : 0 ≤ Λ := (le_trans (abs_nonneg _) (mova_abs_le_cbNorm_two hρ 0)).trans hΛ
  have hh2 : Torus.IsCk 2 (fun x => ρ x - ρβ x) := mova_isCk_sub hρ hρβ
  have hh1 : Torus.IsCk 1 (fun x => ρ x - ρβ x) := mova_isCk_one_of_two hh2
  set δ : ℝ := Torus.cbNorm 2 (fun x => ρ x - ρβ x) with hδ
  have hδ0 : 0 ≤ δ := KernelGrad.cbNorm_nonneg' _ 2
  have hLip : ∀ {f : Torus d → ℝ}, Torus.IsCk 2 f → Torus.cbNorm 2 f ≤ Λ → KernelGrad.IsLipschitz Λ f :=
    fun {f} hf hfΛ a b => ((PDE.R2Aux.isLipschitz_of_cbNorm (mova_isCk_one_of_two hf)) a b).trans
      (mul_le_mul_of_nonneg_right ((KernelGrad.cbNorm_mono (by norm_num : 1 ≤ 2)).trans hfΛ)
        (KernelGrad.tdist_nonneg a b))
  have hρL := hLip hρ hΛ
  have hρβL := hLip hρβ hΛβ
  have hhL : KernelGrad.IsLipschitz δ (fun x => ρ x - ρβ x) := fun a b =>
    ((PDE.R2Aux.isLipschitz_of_cbNorm hh1) a b).trans
      (mul_le_mul_of_nonneg_right (KernelGrad.cbNorm_mono (by norm_num : 1 ≤ 2))
        (KernelGrad.tdist_nonneg a b))
  have hρ_b : ∀ x, |ρ x| ≤ Λ := fun x => (mova_abs_le_cbNorm_two hρ x).trans hΛ
  have hρβ_b : ∀ x, |ρβ x| ≤ Λ := fun x => (mova_abs_le_cbNorm_two hρβ x).trans hΛβ
  have hh_b : ∀ x, |ρ x - ρβ x| ≤ δ := fun x => mova_abs_le_cbNorm_two hh2 x
  have hinvρ := movf_lip_inv hc₀ hlow hρL
  have hinvρβ := movf_lip_inv hc₀ hlowβ hρβL
  have hcomp : ∀ j : Fin d, ∀ x y : Torus d,
      |(mfeTransport D ρ x).ofLp j - (mfeTransport D ρ y).ofLp j| ≤
        (D.invβ * (K1 + K2) + mova_L1 (periodicRiesz d D.s)) * δ * KernelGrad.tdist x y := by
    intro j x y
    have hdh : ∀ z, Torus.partialDeriv j (fun y => ρ y - ρβ y) z =
        Torus.partialDeriv j ρ z - Torus.partialDeriv j ρβ z := fun z => mova_partialDeriv_sub j hρ1 hρβ1 z
    have hdh_b : ∀ z, |Torus.partialDeriv j (fun y => ρ y - ρβ y) z| ≤ δ := fun z =>
      mova_abs_partialDeriv_le hh2 j z
    have hdh_L : KernelGrad.IsLipschitz δ (Torus.partialDeriv j (fun y => ρ y - ρβ y)) :=
      fun a b => mova_isLipschitz_partialDeriv hh2 j a b
    have hdβ_b : ∀ z, |Torus.partialDeriv j ρβ z| ≤ Λ := fun z =>
      (mova_abs_partialDeriv_le hρβ j z).trans hΛβ
    have hdβ_L : KernelGrad.IsLipschitz Λ (Torus.partialDeriv j ρβ) := fun a b =>
      (mova_isLipschitz_partialDeriv hρβ j a b).trans (mul_le_mul_of_nonneg_right hΛβ
        (KernelGrad.tdist_nonneg a b))
    -- T1
    have hT1 := movf_lip_mul hdh_L hinvρ hdh_b (movf_abs_inv hc₀ hlow)
    -- T2
    have hm1 := movf_lip_mul hdβ_L hhL hdβ_b hh_b
    have hm1b : ∀ z, |Torus.partialDeriv j ρβ z * (ρ z - ρβ z)| ≤ Λ * δ := fun z => by
      rw [abs_mul]; exact mul_le_mul (hdβ_b z) (hh_b z) (abs_nonneg _) hΛ0
    have hm2 := movf_lip_mul hm1 hinvρ hm1b (movf_abs_inv hc₀ hlow)
    have hm2b : ∀ z, |Torus.partialDeriv j ρβ z * (ρ z - ρβ z) * (1 / ρ z)| ≤ Λ * δ * (1 / c₀) := fun z => by
      rw [abs_mul]
      exact mul_le_mul (hm1b z) (movf_abs_inv hc₀ hlow z) (abs_nonneg _) (mul_nonneg hΛ0 hδ0)
    have hm3 := movf_lip_mul hm2 hinvρβ hm2b (movf_abs_inv hc₀ hlowβ)
    -- the decomposition of the log-derivative difference
    have hq : ∀ z, Torus.partialDeriv j ρ z / ρ z - Torus.partialDeriv j ρβ z / ρβ z =
        Torus.partialDeriv j (fun y => ρ y - ρβ y) z * (1 / ρ z) -
          Torus.partialDeriv j ρβ z * (ρ z - ρβ z) * (1 / ρ z) * (1 / ρβ z) := by
      intro z
      have h1 := hpos z
      have h2 := hposβ z
      rw [hdh z]
      field_simp
      ring
    have hcdif : ∀ z, convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) z -
        convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) z =
        convFun (periodicRiesz d D.s) (Torus.partialDeriv j (fun y => ρ y - ρβ y)) z := by
      intro z
      have e : Torus.partialDeriv j (fun y => ρ y - ρβ y) =
          fun y => Torus.partialDeriv j ρ y - Torus.partialDeriv j ρβ y := funext hdh
      rw [e, mova_convFun_sub_right hgi (mova_continuous_partialDeriv hρ1 j)
        (mova_continuous_partialDeriv hρβ1 j) z]
    have hconv := mova_convFun_lipschitz hgi (mova_continuous_partialDeriv hh1 j) hdh_L x y
    have hz : ∀ z, (mfeTransport D ρ z).ofLp j = D.invβ * (Torus.partialDeriv j ρ z / ρ z -
        Torus.partialDeriv j ρβ z / ρβ z) +
        (convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) z -
          convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) z) := by
      intro z
      have h0 := heq z
      have hj : (mfeTransport D ρβ z).ofLp j = 0 := by rw [h0]; rfl
      rw [mova_mfeTransport_apply D hρβ hposβ] at hj
      rw [mova_mfeTransport_apply D hρ hpos]
      linarith
    rw [hz x, hz y]
    have e2 : D.invβ * (Torus.partialDeriv j ρ x / ρ x - Torus.partialDeriv j ρβ x / ρβ x) +
        (convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) x -
          convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) x) -
        (D.invβ * (Torus.partialDeriv j ρ y / ρ y - Torus.partialDeriv j ρβ y / ρβ y) +
          (convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) y -
            convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) y)) =
        D.invβ * ((Torus.partialDeriv j (fun y => ρ y - ρβ y) x * (1 / ρ x) -
            Torus.partialDeriv j (fun y => ρ y - ρβ y) y * (1 / ρ y)) -
          (Torus.partialDeriv j ρβ x * (ρ x - ρβ x) * (1 / ρ x) * (1 / ρβ x) -
            Torus.partialDeriv j ρβ y * (ρ y - ρβ y) * (1 / ρ y) * (1 / ρβ y))) +
        (convFun (periodicRiesz d D.s) (Torus.partialDeriv j (fun y => ρ y - ρβ y)) x -
          convFun (periodicRiesz d D.s) (Torus.partialDeriv j (fun y => ρ y - ρβ y)) y) := by
      rw [hq x, hq y, hcdif x, hcdif y]; ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hκ]
    have b1 := hT1 x y
    have b3 := hm3 x y
    have hab : |(Torus.partialDeriv j (fun y => ρ y - ρβ y) x * (1 / ρ x) -
            Torus.partialDeriv j (fun y => ρ y - ρβ y) y * (1 / ρ y)) -
          (Torus.partialDeriv j ρβ x * (ρ x - ρβ x) * (1 / ρ x) * (1 / ρβ x) -
            Torus.partialDeriv j ρβ y * (ρ y - ρβ y) * (1 / ρ y) * (1 / ρβ y))| ≤
        (K1 + K2) * δ * KernelGrad.tdist x y := by
      refine (abs_sub _ _).trans ?_
      have c1 : (δ * (1 / c₀) + δ * (Λ / c₀ ^ 2)) = K1 * δ := by rw [hK1]; ring
      have c2 : ((Λ * δ + Λ * δ) * (1 / c₀) + Λ * δ * (Λ / c₀ ^ 2)) * (1 / c₀) +
          Λ * δ * (1 / c₀) * (Λ / c₀ ^ 2) = K2 * δ := by rw [hK2]; ring
      rw [c1] at b1
      rw [c2] at b3
      nlinarith [b1, b3]
    have := mul_le_mul_of_nonneg_left hab hκ.le
    nlinarith [this, hconv]
  intro x y
  have hsum : ‖mfeTransport D ρ x - mfeTransport D ρ y‖ ≤
      ∑ j : Fin d, (D.invβ * (K1 + K2) + mova_L1 (periodicRiesz d D.s)) * δ * KernelGrad.tdist x y := by
    refine (mova_norm_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [PiLp.sub_apply]
    exact hcomp j x y
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  have ht := KernelGrad.tdist_nonneg x y
  have : (0 : ℝ) ≤ δ * KernelGrad.tdist x y := mul_nonneg hδ0 ht
  have hm := le_max_right 0 (d * (D.invβ * (K1 + K2) + mova_L1 (periodicRiesz d D.s)))
  nlinarith [mul_le_mul_of_nonneg_right hm this]

end HRS

end
