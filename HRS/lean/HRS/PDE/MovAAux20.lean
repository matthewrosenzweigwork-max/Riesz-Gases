import HRS.PDE.MovAAux19

/-!
# MOVA Aux20: uniform bounds from `MovTraj`: positive infimum and Lipschitz bound of the transport field.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_traj_c0 {T : ℝ} (hT : 0 ≤ T) {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, c₀ ≤ ρ r x := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  obtain ⟨p, -, hp⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_isMinOn
    (Set.nonempty_iff_univ_nonempty.1 ⟨(⟨0, h0⟩, 0)⟩) (mova_cont_rho hρt).continuousOn
  refine ⟨ρ p.1 p.2, hpos _ p.1.2 _, fun r hr x => ?_⟩
  exact hp (Set.mem_univ (⟨r, hr⟩, x))

theorem mova_mfeTransport_apply (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (j : Fin d) (x : Torus d) :
    (mfeTransport D ρ x).ofLp j = D.invβ * (Torus.partialDeriv j ρ x / ρ x) +
      convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) x + Torus.partialDeriv j D.V x := by
  have hρ1 := mova_isCk_one_of_two hρ
  unfold mfeTransport
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mova_grad_apply]
  rw [mova_partialDeriv_log j hρ1 hpos x, mova_convGradConv_eq (b15_one_le_d D) D.hs0 D.hsd hρ1 j x]

theorem mova_lip_mfeTransport (D : DynData d) (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hρ : Torus.IsCk 2 ρ) {c₀ Λ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x, c₀ ≤ ρ x)
    (hΛ : Torus.cbNorm 2 ρ ≤ Λ) :
    IsLipschitzVF (d * (D.invβ * (Λ / c₀ + Λ * Λ / (c₀ * c₀)) +
      mova_L1 (periodicRiesz d D.s) * Λ + Torus.cbNorm 2 D.V)) (mfeTransport D ρ) := by
  have hρ1 := mova_isCk_one_of_two hρ
  have hpos : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le hc₀ (hlow x)
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have hΛ0 : 0 ≤ Λ := (le_trans (abs_nonneg _) (mova_abs_le_cbNorm_two hρ 0)).trans hΛ
  have hLρ : KernelGrad.IsLipschitz Λ ρ := fun a b =>
    ((PDE.R2Aux.isLipschitz_of_cbNorm hρ1) a b).trans (mul_le_mul_of_nonneg_right
      ((KernelGrad.cbNorm_mono (by norm_num : 1 ≤ 2)).trans hΛ) (KernelGrad.tdist_nonneg a b))
  have hcomp : ∀ j : Fin d, ∀ x y : Torus d,
      |(mfeTransport D ρ x).ofLp j - (mfeTransport D ρ y).ofLp j| ≤
        (D.invβ * (Λ / c₀ + Λ * Λ / (c₀ * c₀)) + mova_L1 (periodicRiesz d D.s) * Λ +
          Torus.cbNorm 2 D.V) * KernelGrad.tdist x y := by
    intro j x y
    have ht := KernelGrad.tdist_nonneg x y
    have hdρc := mova_continuous_partialDeriv hρ1 j
    have hla : KernelGrad.IsLipschitz Λ (Torus.partialDeriv j ρ) := fun a b =>
      (mova_isLipschitz_partialDeriv hρ j a b).trans (mul_le_mul_of_nonneg_right hΛ
        (KernelGrad.tdist_nonneg a b))
    have hconv := mova_convFun_lipschitz hgi hdρc hla x y
    have hVl := mova_isLipschitz_partialDeriv hV j x y
    have hax := (mova_abs_partialDeriv_le hρ j y).trans hΛ
    have hρx := hpos x
    have hρy := hpos y
    have hq : |Torus.partialDeriv j ρ x / ρ x - Torus.partialDeriv j ρ y / ρ y| ≤
        (Λ / c₀ + Λ * Λ / (c₀ * c₀)) * KernelGrad.tdist x y := by
      have e : Torus.partialDeriv j ρ x / ρ x - Torus.partialDeriv j ρ y / ρ y =
          (Torus.partialDeriv j ρ x - Torus.partialDeriv j ρ y) / ρ x +
            Torus.partialDeriv j ρ y * (ρ y - ρ x) / (ρ x * ρ y) := by
        field_simp; ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have b1 : |(Torus.partialDeriv j ρ x - Torus.partialDeriv j ρ y) / ρ x| ≤
          Λ / c₀ * KernelGrad.tdist x y := by
        rw [abs_div, abs_of_pos hρx]
        calc |Torus.partialDeriv j ρ x - Torus.partialDeriv j ρ y| / ρ x
            ≤ (Λ * KernelGrad.tdist x y) / ρ x :=
              div_le_div_of_nonneg_right (hla x y) hρx.le
          _ ≤ (Λ * KernelGrad.tdist x y) / c₀ :=
              div_le_div_of_nonneg_left (mul_nonneg hΛ0 ht) hc₀ (hlow x)
          _ = Λ / c₀ * KernelGrad.tdist x y := by ring
      have b2 : |Torus.partialDeriv j ρ y * (ρ y - ρ x) / (ρ x * ρ y)| ≤
          Λ * Λ / (c₀ * c₀) * KernelGrad.tdist x y := by
        rw [abs_div, abs_mul, abs_of_pos (mul_pos hρx hρy)]
        have hn : |Torus.partialDeriv j ρ y| * |ρ y - ρ x| ≤ Λ * (Λ * KernelGrad.tdist x y) := by
          refine mul_le_mul hax ?_ (abs_nonneg _) hΛ0
          have := hLρ y x
          rwa [KernelGrad.tdist_sub_comm y x] at this
        have hd : c₀ * c₀ ≤ ρ x * ρ y := mul_le_mul (hlow x) (hlow y) hc₀.le hρx.le
        calc |Torus.partialDeriv j ρ y| * |ρ y - ρ x| / (ρ x * ρ y)
            ≤ (Λ * (Λ * KernelGrad.tdist x y)) / (ρ x * ρ y) :=
              div_le_div_of_nonneg_right hn (mul_pos hρx hρy).le
          _ ≤ (Λ * (Λ * KernelGrad.tdist x y)) / (c₀ * c₀) :=
              div_le_div_of_nonneg_left (mul_nonneg hΛ0 (mul_nonneg hΛ0 ht)) (mul_pos hc₀ hc₀) hd
          _ = Λ * Λ / (c₀ * c₀) * KernelGrad.tdist x y := by ring
      linarith
    rw [mova_mfeTransport_apply D hρ hpos, mova_mfeTransport_apply D hρ hpos]
    have e2 : D.invβ * (Torus.partialDeriv j ρ x / ρ x) + convFun (periodicRiesz d D.s)
        (Torus.partialDeriv j ρ) x + Torus.partialDeriv j D.V x -
        (D.invβ * (Torus.partialDeriv j ρ y / ρ y) + convFun (periodicRiesz d D.s)
          (Torus.partialDeriv j ρ) y + Torus.partialDeriv j D.V y) =
        D.invβ * (Torus.partialDeriv j ρ x / ρ x - Torus.partialDeriv j ρ y / ρ y) +
          (convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) x -
            convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρ) y) +
          (Torus.partialDeriv j D.V x - Torus.partialDeriv j D.V y) := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    rw [abs_mul, abs_of_pos hκ]
    have h1 : D.invβ * |Torus.partialDeriv j ρ x / ρ x - Torus.partialDeriv j ρ y / ρ y| ≤
        D.invβ * ((Λ / c₀ + Λ * Λ / (c₀ * c₀)) * KernelGrad.tdist x y) :=
      mul_le_mul_of_nonneg_left hq hκ.le
    nlinarith
  intro x y
  have hsum : ‖mfeTransport D ρ x - mfeTransport D ρ y‖ ≤
      ∑ j : Fin d, (D.invβ * (Λ / c₀ + Λ * Λ / (c₀ * c₀)) + mova_L1 (periodicRiesz d D.s) * Λ +
        Torus.cbNorm 2 D.V) * KernelGrad.tdist x y := by
    refine (mova_norm_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [PiLp.sub_apply]
    exact hcomp j x y
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc _ ≤ _ := hsum
    _ = _ := by ring

end HRS
