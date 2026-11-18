import HRS.MS.WsStatAux10

/-!
# S21 packet D4: the stationary setup family with `OscAdjointInput` discharged

`s21_setup_family`: for a thermal equilibrium `rho` and `T > 0` there are `theta`, `Lam`, `K` (so `b = s21Bounds d s a beta T theta Lam K C0`
is valid, `b.s = s`, `b.T = T`, `b.m = wholeSpaceIndex d`; `s21Bounds_eq : b = {b_0 with C0 := C0}` by `rfl`) and a threshold `C0thr` such that
for every `C0 >= C0thr` there is `S : WholeSetup b` with

* `S.rho N t = rho`, `S.invbeta N = beta^{-1}`, `S.kappa N = sqrt(N beta)` (`N >= 1`), hence `S.dyn N` is the dynamics
  `quadraticGradientDyn d s a beta` (`s21_dyn_eq`);
* `OscAdjointInput (S.coeff N) b.m b.T` for every `N` (packet E).

So the S5.6 machinery (`general_paths_proof`, `s56_*`) applies to the stationary quadratic model with no unproved hypothesis; the
constant `C0` is free above `C0thr`, hence can be taken above the `C0min` of the S5.6 statements (which depends on
`s21Bounds ... 0` only).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.S85
open HRS (Euc)

variable {d : ℕ}

theorem s21Bounds_eq (s a β T : ℝ) (θ : Euc d → ℝ) (Λ K C₀ : ℝ) :
    s21Bounds d s a β T θ Λ K C₀ = { s21Bounds d s a β T θ Λ K 0 with C₀ := C₀ } := rfl

theorem s21_coeff_setup {s a β T : ℝ} {θ : Euc d → ℝ} {Λ K C₀ : ℝ}
    (S : WholeSetup (s21Bounds d s a β T θ Λ K C₀)) {ρ : Euc d → ℝ}
    (hρ' : ∀ N t, S.ρ N t = ρ) (hinv' : ∀ N, S.invβ N = β⁻¹) (N : ℕ) :
    S.coeff N = (⟨s, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff (fun _ => ρ) := by
  have h1 : S.ρ N = fun _ => ρ := funext (hρ' N)
  unfold WholeSetup.coeff WholeSetup.dyn
  rw [h1, hinv' N]
  rfl

theorem s21_setup_family (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β T : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hT : 0 < T) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ (θ : Euc d → ℝ) (Λ K : ℝ), IsUlCutoff θ ∧ (s21Bounds d s a β T θ Λ K 0).Valid ∧
      ∃ C₀thr : ℝ, 0 ≤ C₀thr ∧ ∀ C₀ : ℝ, C₀thr ≤ C₀ →
        ∃ S : WholeSetup (s21Bounds d s a β T θ Λ K C₀),
          (∀ N t, S.ρ N t = ρ) ∧ (∀ N, S.invβ N = β⁻¹) ∧
          (∀ N : ℕ, 1 ≤ N → S.κ N = Real.sqrt ((N : ℝ) * β)) ∧
          (∀ N, OscAdjointInput (S.coeff N) (s21Bounds d s a β T θ Λ K C₀).m
            (s21Bounds d s a β T θ Λ K C₀).T) := by
  obtain ⟨θ, hθ⟩ := HRS.MS.S52B.s52b_exists_ulCutoff d
  obtain ⟨Λ, K, C₀thr, hthr, hS⟩ := s21_stationary_setup hd hs0 hsd ha hβ hT hθ hρ
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by rw [hρeq]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  refine ⟨θ, Λ, K, hθ, s21Bounds_valid hd hs0 hsd hβ hT hθ Λ K 0, C₀thr, hthr, fun C₀ hC₀ => ?_⟩
  obtain ⟨S, h1, h2, h3⟩ := hS C₀ hC₀
  refine ⟨S, h1, h2, h3, fun N => ?_⟩
  rw [s21_coeff_setup S h1 h2 N, s85_coeff_fv (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ ρ]
  have hm : (24 : ℝ) * d + 240 ≤ (s21Bounds d s a β T θ Λ K C₀).m := by
    show (24 : ℝ) * d + 240 ≤ ((wholeSpaceIndex d : ℕ) : ℝ)
    unfold wholeSpaceIndex; push_cast; exact le_rfl
  exact s21_oscAdjointInput hd hs0 hsd (inv_pos.2 hβ) (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ hSch T hT.le
    _ hm

end HRS.MS.S21
