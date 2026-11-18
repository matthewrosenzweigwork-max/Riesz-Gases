import HRS.Sections.Sec7Setting

/-!
# Packet REGSET: `Regime.reg` and `Regime.relax` of `HRS/Sections/Sec7Setting.lean`

Relocated proofs (the frozen statements remain `sorry` in the spec file).  Both follow from the
coefficient-level solution `ρc` at a large Sobolev index `K` (supplied by `Regime.sol`), the uniform
`H^K` bound / the `H^r` exponential decay of Proposition 5.1 (`HRS.PDE.finite_reg_uniform_bounds`,
`HRS.PDE.finite_reg_decay`) and the Sobolev embedding `HRS.PDE.toFun_isCk_le`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.PDE HRS.Sec7

namespace HRS.MC.RegSet

variable {d : ℕ}

/-- The Sobolev index `K = ⌊d/2+6⌋ + j + 2` is large enough. -/
theorem rgs_K_gt (d j : ℕ) :
    (d : ℝ) / 2 + 6 < ((⌊(d : ℝ) / 2 + 6⌋₊ + j + 2 : ℕ) : ℝ) ∧
    (d : ℝ) / 2 + j + 1 < ((⌊(d : ℝ) / 2 + 6⌋₊ + j + 2 : ℕ) : ℝ) := by
  have h := Nat.lt_floor_add_one ((d : ℝ) / 2 + 6)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast
  constructor <;> linarith

/-- The coefficient solution of the regime at a Sobolev index above `d/2 + j + 1`. -/
theorem rgs_sol (R : Regime d) (j : ℕ) :
    ∃ (K : ℕ) (ρc : ℝ → Coeff d), (d : ℝ) / 2 + j + 1 < K ∧ (d : ℝ) / 2 + 6 < K ∧
      IsMFSolutionHK d R.D.s R.D.V R.β⁻¹ (K : ℝ) R.ρ₀ ρc ∧
      ∀ t : ℝ, 0 ≤ t → R.ρ t = mfPath ρc t := by
  obtain ⟨h1, h2⟩ := rgs_K_gt d j
  obtain ⟨ρc, hρc, hρ⟩ := R.sol (⌊(d : ℝ) / 2 + 6⌋₊ + j + 2) h1
  exact ⟨_, ρc, h2, h1, by rw [R.hDβ] at hρc; exact hρc, hρ⟩

theorem reg_proof (R : Regime d) (j : ℕ) : ∃ Λ : ℝ, ∀ T : ℝ, IsRegularMF j Λ T R.ρ := by
  obtain ⟨K, ρc, hK1, hK2, hsol, hρ⟩ := rgs_sol R j
  have hH := R.finiteRegHyp K hK2
  have hd : 1 ≤ d := by have := R.hd; omega
  obtain ⟨c, C, hc, H⟩ := finite_reg_uniform_bounds hd R.D.s R.β R.β K R.D.V R.ρ₀ hH
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨E, hE⟩ := toFun_isCk_le (d := d) j (K : ℝ) (by linarith)
  refine ⟨|E| * C, fun T t ht => ?_⟩
  have hb := (H R.β ⟨le_rfl, le_rfl⟩ ρc hsol t ht.1).2
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd R.D.s R.β R.β K R.D.V R.ρ₀ hH R.β
    ⟨le_rfl, le_rfl⟩ ρc hsol t ht.1
  have hmem : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht.1)
  obtain ⟨h1, h2⟩ := hE _ hmem hreal
  rw [hρ t ht.1]
  refine ⟨h1, h2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_right (le_abs_self E) (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hb (abs_nonneg _))

example := (@reg_proof : type_of% @HRS.Sec7.Regime.reg)

theorem relax_proof (R : Regime d) (j : ℕ) : ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
    Torus.cbNorm j (fun x => R.ρ t x - R.ρβ x) ≤ C * Real.exp (-c * t) := by
  obtain ⟨K, ρc, hK1, hK2, hsol, hρ⟩ := rgs_sol R j
  have hH := R.finiteRegHyp K hK2
  have hd : 1 ≤ d := by have := R.hd; omega
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨Cr, cr, hCr, hcr, hdec⟩ := finite_reg_decay hd R.D.s R.β R.β K R.D.V R.ρ₀ hH
    ((d : ℝ) / 2 + j + 1) (by linarith) hK1
  obtain ⟨E, hE⟩ := toFun_isCk_le (d := d) j ((d : ℝ) / 2 + j + 1) (by linarith)
  obtain ⟨hth, hsm, hpos⟩ := R.thermal
  have hcont : Continuous R.ρβ := ClassicalAux.continuous_of_isCk
    (ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hsm)
  have hSob : MemSobolev (K : ℝ) R.ρβ := MFSemigroup.memSobolev_of_isSmooth hsm _
  have hK0 : (d : ℝ) / 2 < K := by linarith
  have hmβ : MemHs (K : ℝ) (coeffOf R.ρβ) := (ProdAux.memHs_of_memSobolev (K : ℝ) hSob).1
  have hsumβ := summable_norm_of_memHs (K : ℝ) hK0 _ hmβ
  have hrealβ : IsRealCoeff (coeffOf R.ρβ) :=
    isRealCoeff_coeffOf R.ρβ (MFThermalReg.integrable_of_cont hcont)
  have hρβeq : toFun (coeffOf R.ρβ) = R.ρβ := MFThermalReg.toFun_coeffOf hcont hsumβ
  refine ⟨|E| * Cr, cr, hcr, fun t ht => ?_⟩
  have hreal := MFGlobal.isRealCoeff_of_isMFSolutionHK hd R.D.s R.β R.β K R.D.V R.ρ₀ hH R.β
    ⟨le_rfl, le_rfl⟩ ρc hsol t ht
  have hmt : MemHs (K : ℝ) (ρc t) := hsol.cont.1 t (Set.mem_Ici.2 ht)
  have hsumt := summable_norm_of_memHs (K : ℝ) hK0 _ hmt
  obtain ⟨hmz, hzn⟩ := hdec R.β ⟨le_rfl, le_rfl⟩ ρc hsol R.ρβ hth hcont hpos hSob t ht
  have hrealz : IsRealCoeff (ρc t - coeffOf R.ρβ) := fun k => by
    simp only [Pi.sub_apply, map_sub]; rw [hreal k, hrealβ k]
  have hzeq : (fun y => R.ρ t y - R.ρβ y) = toFun (ρc t - coeffOf R.ρβ) := by
    funext y
    rw [hρ t ht, MFApriori.Aux.toFun_sub _ _ hsumt hsumβ, hρβeq]
    rfl
  obtain ⟨-, hzCb⟩ := hE _ hmz hrealz
  rw [hzeq, mul_assoc]
  exact hzCb.trans ((mul_le_mul_of_nonneg_right (le_abs_self E) (Real.sqrt_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hzn (abs_nonneg _)))

example := (@relax_proof : type_of% @HRS.Sec7.Regime.relax)

end HRS.MC.RegSet

end
