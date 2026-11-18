import HRS.MS.WadAux86
import HRS.MS.WadAux54

/-!
# S8.3, packet S8E-4, part 3: weighted Lipschitz bound for the extension `s85_Ulim`

`s8e_ulim_lip`: for `f ∈ C_M` with `Wt M Φ0 f` and `|f(y+z) - f(y)| ≤ Λ ‖z‖ ⟨y⟩^M` (`‖z‖ < 1/4`), `0 < t ≤ T`,
`‖ζ‖ < 1/8`:  `|U_t f (x+ζ) - U_t f (x)| ≤ K (Φ0 + 3^M (Λ + Φ0)) ‖ζ‖ ⟨x⟩^M`.  Proof: `s8e_density_lip` gives
`C_c^∞` approximants with the same weighted Lipschitz bound, `s8e_diff_bound` for their classical solutions
(`s8d_Ucc_eq_add`: `U_t φ = w_0 + const`), and passage to the limit `s85_Ulim_spec`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_ulim_lip {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ0 Λ : ℝ} {f : Euc d → ℝ}, 0 < t → t ≤ T → MemCM M f → Wt M Φ0 f → 0 ≤ Λ →
      (∀ y z : Euc d, ‖z‖ < 1 / 4 → |f (y + z) - f y| ≤ Λ * ‖z‖ * jbracket y ^ M) →
      ∀ ζ : Euc d, ‖ζ‖ < 1 / 8 → ∀ x : Euc d,
        |s85_Ulim a β ρβ M t f (x + ζ) - s85_Ulim a β ρβ M t f x| ≤
          K * (Φ0 + 3 ^ M * (Λ + Φ0)) * ‖ζ‖ * jbracket x ^ M := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨K, hK0, hK⟩ := s8e_diff_bound hd ha hβ hT hM hρ
  refine ⟨K, hK0, ?_⟩
  intro t Φ0 Λ f ht htT hf hΦ0 hΛ hLf ζ hζ x
  have hΦ00 : 0 ≤ Φ0 := hΦ0.nonneg
  have hex : ∀ n : ℕ, ∃ φ : Euc d → ℝ, S85Cc φ ∧ Wt M (1 / ((n : ℝ) + 1)) (fun y => φ y - f y) ∧
      ∀ y z : Euc d, ‖z‖ < 1 / 4 → |φ (y + z) - φ y| ≤ 3 ^ M * (Λ + Φ0) * ‖z‖ * jbracket y ^ M :=
    fun n => s8e_density_lip hM hf hΦ0 hΛ hLf (by positivity)
  choose φ hcc hclose hLφ using hex
  have happ : S85Approx M f φ := ⟨hcc, 1, zero_le_one, hclose⟩
  have hsp := s85_Ulim_spec H ht.le htT happ
  choose w hw using fun n => s85_exists_cl hd ha hβ hρ ht.le (hcc n)
  have hΛ' : 0 ≤ 3 ^ M * (Λ + Φ0) := by positivity
  have hbd : ∀ n : ℕ, |s85_Ucc a β ρβ t (φ n) (x + ζ) - s85_Ucc a β ρβ t (φ n) x| ≤
      K * (Φ0 + 1 / ((n : ℝ) + 1) + 3 ^ M * (Λ + Φ0)) * ‖ζ‖ * jbracket x ^ M := by
    intro n
    have hWφ : Wt M (Φ0 + 1 / ((n : ℝ) + 1)) (φ n) := fun y => by
      have h1 := hclose n y
      have h2 := hΦ0 y
      have h3 : ‖φ n y‖ ≤ ‖φ n y - f y‖ + ‖f y‖ := by
        have := norm_add_le (φ n y - f y) (f y)
        simpa using this
      nlinarith
    obtain ⟨c, hc⟩ := s8d_Ucc_eq_add hd ha hβ hρ ht.le (hw n)
    have h := hK ht htT (hw n) hWφ hΛ' (hLφ n) ζ hζ x
    rw [hc]
    simp only [add_sub_add_right_eq_sub]
    refine h.trans (le_of_eq ?_)
    ring
  have hl1 : Tendsto (fun n : ℕ => |s85_Ucc a β ρβ t (φ n) (x + ζ) - s85_Ucc a β ρβ t (φ n) x|) atTop
      (𝓝 |s85_Ulim a β ρβ M t f (x + ζ) - s85_Ulim a β ρβ M t f x|) :=
    (((hsp (x + ζ)).sub (hsp x)).abs)
  have hl2 : Tendsto (fun n : ℕ => K * (Φ0 + 1 / ((n : ℝ) + 1) + 3 ^ M * (Λ + Φ0)) * ‖ζ‖ * jbracket x ^ M)
      atTop (𝓝 (K * (Φ0 + 0 + 3 ^ M * (Λ + Φ0)) * ‖ζ‖ * jbracket x ^ M)) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    exact ((((this.const_add Φ0).add_const _).const_mul K).mul_const _).mul_const _
  have := le_of_tendsto_of_tendsto hl1 hl2 (Eventually.of_forall hbd)
  simpa using this

end HRS.MS.Wad
