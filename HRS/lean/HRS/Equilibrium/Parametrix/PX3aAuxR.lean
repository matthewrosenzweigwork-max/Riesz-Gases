import HRS.Equilibrium.Parametrix.PX3aAuxQ

/-!
# Packet PX3a auxiliaries R: `ofChart` of the Newton chart (no symmetry)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma newtonPot_bound_uniform (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a c : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |iteratedFDeriv ℝ (a + c) (newtonPot d g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ - 2 + c)) * lw r ^ (b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := by
  have key : ∀ c : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d × Euc d → ℝ} {A : ℝ} (_h : SrcCls d σ b m A g), 0 ≤ A →
      ∀ {a : ℕ}, a + c ≤ m → ∀ {r : ℝ}, 0 < r → r < 1 / 8 → ∀ (X0 z0 : Euc d), ‖z0‖ = r →
      ∀ (u : Fin a → Euc d) (v : Fin c → Euc d),
      |iteratedFDeriv ℝ (a + c) (newtonPot d g) (X0, z0) (pat u v)| ≤
        C * A * (1 + r ^ (-(σ - 2 + c)) * lw r ^ (b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)) *
          ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) := fun c => newtonPot_bound hd c hσ b m
  choose Cf hCf0 hCf using key
  refine ⟨∑ c ∈ Finset.range (m + 1), Cf c, Finset.sum_nonneg fun c _ => hCf0 c,
    fun {g} {A} h hA a c hac r hr hr1 X0 z0 hz0 u v => ?_⟩
  have hle : Cf c ≤ ∑ c ∈ Finset.range (m + 1), Cf c :=
    Finset.single_le_sum (f := Cf) (fun i _ => hCf0 i) (Finset.mem_range.mpr (by omega))
  refine (hCf c h hA hac hr hr1 X0 z0 hz0 u v).trans ?_
  have hT : 0 ≤ 1 + r ^ (-(σ - 2 + (c : ℝ))) * lw r ^ (b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) := by
    have : 0 ≤ r ^ (-(σ - 2 + (c : ℝ))) * lw r ^ (b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) :=
      mul_nonneg (Real.rpow_nonneg hr.le _) (pow_nonneg (lw_pos _).le _)
    linarith
  have hP : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
    mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hA) hT) hP

theorem newton_ofChart_general (hd : 2 ≤ d) {ν : ℝ} (hν : 0 < ν) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) m (C * B)
        (ofChart (newtonChart d ν (toChart F))) := by
  obtain ⟨Cq, hCq0, hCq⟩ := newton_conormal_of_pot hd hν hσ b m
    (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)
    (fun c => by split_ifs <;> omega) (fun c => by split_ifs <;> omega)
  obtain ⟨K1, hK1, hsrc⟩ := srcCls_chart (d := d) σ b m
  obtain ⟨Cu, hCu0, hCu⟩ := newtonPot_bound_uniform hd hσ b m
  refine ⟨Cq * (Cu * K1), by positivity, fun B F hB hF => ?_⟩
  refine hCq (Cu * K1) B F (by positivity) hB hF ?_
  intro a c hac r hr hr1 X z hz u v
  have hg := hsrc B F hB hF
  have := hCu hg (mul_nonneg hK1 hB) hac hr hr1 X z hz u v
  refine this.trans (le_of_eq ?_)
  ring

end HRS.Parx

end
