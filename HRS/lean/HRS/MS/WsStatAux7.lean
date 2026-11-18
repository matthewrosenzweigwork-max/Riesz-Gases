import HRS.MS.WsStatAux6
import HRS.MS.FeatDecAux12
import HRS.MS.OrbFeatAux1

/-!
# S21 packet D3: the stationary `WholeBounds` / `WholeSetup` of S2.1 (i)

Data for the stationary quadratic gradient dynamics `quadraticGradientDyn d s a beta` along the constant path `rho_beta`:

* `s21Bounds d s a beta T theta Lam K C0 : WholeBounds d`: `M = -1`, `Q = a . 1`, `c = 0`, `k = d + 9`, `m = 24 d + 240`
  (`wholeSpaceIndex d`), `nu_* = beta^{-1}`, `L = 6d + 58 + 2s`;  `s21Bounds_valid`: the standing constraints hold
  (`k > d/2 + 8`, `m > J + 3d + 4` with `J = 8d + 76`, `L > 3d + 3k + 2s + 30`).
* `s21_stationary_setup`: for a thermal equilibrium `rho`, after choosing the cutoff `theta` and the constants `Lam`, `K`,
  for every `C0 >=` a threshold there is a `WholeSetup (s21Bounds ... C0)` with `S.rho N t = rho`, `S.invbeta N = beta^{-1}`,
  `S.kappa N = sqrt(N beta)` for `N >= 1` (so `sigma_N = sqrt(N beta)`, `A_N = 1`, `q_N = 1`, `S.dyn N = quadraticGradientDyn`).
  Fields: `mf` (`s21_mf_stationary`), `dens` (Schwartz), `adjoint` (`s85_witness5`), `regime` (R1 / R3), `force`
  (`ulw_coeffHyp`), `energy_nonneg` (packet A).

The scale choice `kappa_N = sqrt(N beta)` (not `sqrt N`) is forced by `sigmaScale N kappa invbeta = min kappa sqrt(N/invbeta)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

def s21Bounds (d : ℕ) (s a β T : ℝ) (θ : Euc d → ℝ) (Λ K C₀ : ℝ) : WholeBounds d where
  θ := θ
  s := s
  T := T
  M := -1
  Q := a • (1 : Matrix (Fin d) (Fin d) ℝ)
  c := 0
  k := d + 9
  m := ((wholeSpaceIndex d : ℕ) : ℝ)
  νstar := β⁻¹
  Λ := Λ
  K := K
  L := 6 * (d : ℝ) + 58 + 2 * s
  C₀ := C₀

theorem s21Bounds_valid (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β T : ℝ} (hβ : 0 < β)
    (hT : 0 < T) {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (Λ K C₀ : ℝ) :
    (s21Bounds d s a β T θ Λ K C₀).Valid where
  hd := hd
  hs0 := hs0
  hsd := hsd
  hT := hT
  hQ := by
    show (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm
    unfold Matrix.IsSymm; simp
  hθ := hθ
  hk := by
    show (d : ℝ) / 2 + 8 < ((d + 9 : ℕ) : ℝ)
    push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  hm := by
    show (((4 * (d + 9) + 4 * d + 40 : ℕ) : ℝ)) + 3 * d + 4 < ((wholeSpaceIndex d : ℕ) : ℝ)
    unfold wholeSpaceIndex
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  hL := by
    show 3 * (d : ℝ) + 3 * ((d + 9 : ℕ) : ℝ) + 2 * s + 30 < 6 * (d : ℝ) + 58 + 2 * s
    push_cast; linarith
  hν := (inv_pos.2 hβ).le

theorem s21_stationary_setup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β T : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hT : 0 < T) {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ Λ K : ℝ, ∃ C₀thr : ℝ, 0 ≤ C₀thr ∧ ∀ C₀ : ℝ, C₀thr ≤ C₀ →
      ∃ S : WholeSetup (s21Bounds d s a β T θ Λ K C₀),
        (∀ N t, S.ρ N t = ρ) ∧ (∀ N, S.invβ N = β⁻¹) ∧
        (∀ N : ℕ, 1 ≤ N → S.κ N = Real.sqrt ((N : ℝ) * β)) := by
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by rw [hρeq]; exact s21_schwartz_thermal hd hs0 hsd ha hβ
  obtain ⟨hρprob, ψ, hψ⟩ := hSch
  -- weighted bounds
  have hL0 : (0 : ℝ) ≤ 6 * (d : ℝ) + 58 + 2 * s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨hcd, Λw, hw⟩ := HRS.MS.UlW.ulw_schwartz_wsup ψ ((d + 9) + 6 + ⌈(d : ℝ) / 2⌉₊) hL0
  -- the force bound
  obtain ⟨Λf, hΛf⟩ := HRS.MS.UlW.ulw_coeffHyp hd hs0 hsd 0 hρprob ⟨ψ, hψ⟩ T
  -- the adjoint input
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  obtain ⟨K, hK⟩ := HRS.MS.S85.s85_witness5 hd s hs0 hsd θ hθ (d + 10) (by omega) T β⁻¹
    (a • (1 : Matrix (Fin d) (Fin d) ℝ)) (-1) 0 ρ hT.le (inv_pos.2 hβ) hQ ⟨hρprob, ψ, hψ⟩
  -- the completion threshold
  obtain ⟨C₀thr, hC₀thr, hcomp⟩ := s21_clause1_stationary hd hs0 hsd ha hβ
  refine ⟨max Λw Λf, K, C₀thr, hC₀thr, fun C₀ hC₀ => ?_⟩
  refine ⟨{ invβ := fun _ => β⁻¹
            ρ := fun _ _ => ρ
            κ := fun N => if N = 0 then 1 else Real.sqrt ((N : ℝ) * β)
            hinvβ := fun N => ⟨(inv_pos.2 hβ).le, le_rfl⟩
            hκ := fun N => ?_
            mf := fun N => s21_mf_stationary hd hs0 hsd ha hβ hρ T
            dens := fun N t ht => ⟨?_, ?_⟩
            adjoint := fun N => ?_
            regime := fun N => ?_
            force := fun hs N t ht x => ?_
            energy_nonneg := fun N hN t ht X hX => ?_ }, fun _ _ => rfl, fun _ => rfl, fun N hN => ?_⟩
  · -- `kappa N > 0`
    show 0 < (if N = 0 then (1 : ℝ) else Real.sqrt ((N : ℝ) * β))
    split_ifs with h
    · exact one_pos
    · have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h
      exact Real.sqrt_pos.2 (mul_pos hN hβ)
  · show ContDiff ℝ ((((d + 9) + 6 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : ℕ∞) : WithTop ℕ∞) ρ
    rw [← hψ]
    exact_mod_cast hcd
  · show weightedSupE ((d + 9) + 6 + ⌈(d : ℝ) / 2⌉₊) (6 * (d : ℝ) + 58 + 2 * s) ρ ≤
      ENNReal.ofReal (max Λw Λf)
    rw [← hψ]
    exact hw.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact hK
  · by_cases h : s ≤ (d : ℝ) - 2
    · exact Or.inl ⟨PDE.Regime.R1, 0, h⟩
    · exact Or.inl ⟨PDE.Regime.R3, β⁻¹, by
        show (d : ℝ) - 2 < s ∧ 0 < β⁻¹ ∧ β⁻¹ ≤ β⁻¹
        exact ⟨by linarith, inv_pos.2 hβ, le_rfl⟩⟩
  · have := hΛf.regular.2 hs t ht x
    exact this.trans (le_max_right _ _)
  · exact hcomp C₀ hC₀ ρ hρ N hN X hX
  · show (if N = 0 then (1 : ℝ) else Real.sqrt ((N : ℝ) * β)) = Real.sqrt ((N : ℝ) * β)
    rw [if_neg (by omega)]

end HRS.MS.S21
