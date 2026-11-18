import HRS.MS.S104eEx1

/-!
# S10.4 (nonlinear), packet S104E-6: terminal time `t = 0` of `S104eHex`

`s104e_hex_zero`: for every resulting solution and every Hermite datum `φ_α`, `f ≡ φ_α` is a classical adjoint solution on `[0,0]` along the nonlinear coefficient:
`generatorW` at time `0` of a Schwartz-type datum is `DatD` (continuous, bounded) by `s103c_g1_datd`, with `ρ^0` in `U2Dec` (Gaussian bounds).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r HRS.MS.R2WinOrbNL HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s104e_hex_zero (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (εstar c₁ C₁ : ℝ) {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    {ρ : ℝ → Euc d → ℝ} (hres : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) (α : MultiIndex d) :
    ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) 0
      (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) f := by
  set M : ℕ := 10 * d + 98 with hM
  set Lnat : ℕ := d + M + ⌈s⌉₊ + 4 with hLnat
  have hL : (d : ℝ) + M + s + 3 < (Lnat : ℝ) := by
    have : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    rw [hLnat]; push_cast; linarith
  obtain ⟨C, hC0, hC⟩ := s103c_g1_datd hd hs0 hsd a β M hL
  obtain ⟨c, K0, hc, hK0, hG⟩ := s104e_gauss_rho hd hs0 hsd ha hβ εstar c₁ C₁ (M + 1) (by omega) hρβ hres
  obtain ⟨P, hP0, hP⟩ := s104e_u2dec_of_gauss (d := d) hc (M + 1) Lnat
  obtain ⟨hc0, hb0⟩ := hG 0 le_rfl
  have hU : U2Dec (M + 1) (Lnat : ℝ) (P * K0) (ρ 0) := hP (ρ 0) K0 hK0 hc0 hb0
  obtain ⟨Kφ, hKφ0, hKφ⟩ := s103c_phi_syn3 (d := d) (M + 2) (by omega)
  have hφ := hKφ α
  have hAφ : 0 ≤ Kφ * s103_b d α := mul_nonneg hKφ0 (s103_b_nonneg α)
  have hD := hC (P * K0) (Kφ * s103_b d α) (ρ 0) _ (by positivity) hAφ hU hφ
  set φ : Euc d → ℝ := oscTestFun ((24 * d + 240 : ℕ) : ℝ) α with hφdef
  have hφ' : oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α = φ := rfl
  rw [hφ']
  set Cf := (quadraticGradientDyn d s a β).coeff ρ with hCf
  have hgen : (fun x => generatorW Cf 0 φ x) =
      fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ 0)) 0 φ x :=
    funext fun x => s103n_gen_frozen ρ 0 φ x
  set A : ℝ := C * ((1 + P * K0) * (Kφ * s103_b d α)) with hA
  have hDg : DatD M A (fun x => generatorW Cf 0 φ x) := by rw [hgen]; exact hD
  have hgc : Continuous (fun x => generatorW Cf 0 φ x) := hDg.1.continuous
  have hgb : ∀ x, |generatorW Cf 0 φ x| ≤ A := fun x => by
    have := hDg.2.1 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hA0 : 0 ≤ A := hDg.nonneg
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by exact_mod_cast (by omega : 2 ≤ M + 2))
  refine ⟨fun _ => φ, ?_⟩
  refine ⟨fun r _ => hφ2, fun j hj => ⟨Kφ * s103_b d α, fun r _ x => hφ.bd.2 j (by omega) x⟩,
    fun j hj => ?_, rfl, fun x r hr => absurd hr.2 (not_lt.2 hr.1.le), ?_, ⟨A, fun r hr x => ?_⟩⟩
  · exact (hφ2.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp continuous_snd
  · have : (fun p : Set.Icc (0 : ℝ) 0 × Euc d => generatorW Cf (p.1 : ℝ) φ p.2) =
        fun p => generatorW Cf 0 φ p.2 := by
      funext p
      rw [show ((p.1 : ℝ)) = 0 from le_antisymm p.1.2.2 p.1.2.1]
    rw [this]
    exact hgc.comp continuous_snd
  · rw [show r = 0 from le_antisymm hr.2 hr.1]
    calc |generatorW Cf 0 φ x| ≤ A := hgb x
      _ ≤ A * (1 + ‖x‖) := by nlinarith [norm_nonneg x]

end HRS.MS.S104e
