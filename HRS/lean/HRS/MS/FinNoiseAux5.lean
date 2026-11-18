import HRS.MS.FinNoiseAux4
import HRS.MS.FeatDecTie

/-!
# S8.6 `finite_noise`, packet P1d (S86): joint measurability, `S86Feat` and a global bound for the critical model

* `s86_feat_meas`: `(r, x) ↦ gradFeature C m Hz i (max r 0) x` is Borel on `ℝ × ℝ^d`
  (Carathéodory: continuous in `x`, Borel in `r`).
* `s86_feat_data`: for the critical model the hypotheses `S86Feat` hold (S8.5, `s85_uniq`, thermal density
  unique and Schwartz) and `‖gradFeature … (max r 0) x‖ ≤ B` for all `r, x` with `B` independent of `ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.MS.S52B

variable {d : ℕ} {m : ℝ} (C : WholeCoeff d) {Hz : ℝ}

theorem s86_one_le_jb (y : Euc d) : 1 ≤ jbracket y := by
  unfold jbracket
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖y‖])

theorem s86_feat_cont (h : S86Feat C m Hz) (hHz : 0 ≤ Hz) (i : Fin d) (r : ℝ) :
    Continuous fun x : Euc d => gradFeature C m Hz i (max r 0) x := by
  by_cases hr : Hz ≤ max r 0
  · have : (fun x : Euc d => gradFeature C m Hz i (max r 0) x) =
        fun x => gradFeature C m Hz i Hz x := funext fun x => s86_feat_clamp C m Hz i x _ hr
    rw [this]; exact h.cont i Hz ⟨hHz, le_rfl⟩
  · exact h.cont i _ ⟨le_max_right _ _, (not_le.1 hr).le⟩

theorem s86_feat_meas (h : S86Feat C m Hz) (hHz : 0 ≤ Hz) (i : Fin d) :
    Measurable fun p : ℝ × Euc d => gradFeature C m Hz i (max p.1 0) p.2 := by
  have key : Measurable (Function.uncurry fun (x : Euc d) (r : ℝ) =>
      gradFeature C m Hz i (max r 0) x) :=
    measurable_uncurry_of_continuous_of_measurable (s86_feat_cont C h hHz i)
      (fun x => s86_feat_meas_r C h hHz i x)
  have e : (fun p : ℝ × Euc d => gradFeature C m Hz i (max p.1 0) p.2) =
      (Function.uncurry fun (x : Euc d) (r : ℝ) => gradFeature C m Hz i (max r 0) x) ∘
        Prod.swap := by
    funext p; rfl
  rw [e]
  exact key.comp measurable_swap

theorem s86_feat_data (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (Hz : ℝ) (hHz : 0 < Hz) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ →
      S86Feat (critCoeff d a β ρ) m Hz ∧
      ∀ (i : Fin d) (r : ℝ) (x : Euc d), ‖gradFeature (critCoeff d a β ρ) m Hz i (max r 0) x‖ ≤ B := by
  obtain ⟨Cf, hCf⟩ := HRS.MS.S85.feature_decay_proof hd a β ha hβ m hm Hz hHz
  refine ⟨max Cf 0, le_max_right _ _, fun ρ hρ => ?_⟩
  obtain ⟨hex, hrest⟩ := hCf ρ hρ
  have hs0' : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hEq : ρ = thermalDensity d ((d : ℝ) / 2) a β :=
    (HRS.MS.S85.s85_thermal_eq hd hs0' hsd ha hβ hρ).1
  have hS : IsSchwartzDensity ρ := by
    rw [hEq]; exact HRS.MS.S85.s85_thermal_schwartz hd hs0' hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  have huniq : S52bUniq (critCoeff d a β ρ) Hz := by
    rw [HRS.MS.S85.s85_crit_eq, HRS.MS.S85.s85_coeff_fv _ hQ]
    exact HRS.MS.S85.s85_uniq hd hs0'.le hsd (inv_pos.2 hβ) _ hQ hS Hz
  have hfeat : S86Feat (critCoeff d a β ρ) m Hz :=
    { gen := fun t φ => rfl
      uniq := huniq
      ex := fun α t ht => (hex α t ht).2
      feat := fun i r hr x => (hrest i r hr).1 x
      cont := fun i r hr => ((hrest i r hr).2.1.continuous) }
  refine ⟨hfeat, fun i r x => ?_⟩
  have hr : min (max r 0) Hz ∈ Icc (0 : ℝ) Hz :=
    ⟨le_min (le_max_right _ _) hHz.le, min_le_right _ _⟩
  have hge : gradFeature (critCoeff d a β ρ) m Hz i (max r 0) x =
      gradFeature (critCoeff d a β ρ) m Hz i (min (max r 0) Hz) x := by
    by_cases h : Hz ≤ max r 0
    · rw [min_eq_right h]; exact s86_feat_clamp _ m Hz i x _ h
    · rw [min_eq_left (not_le.1 h).le]
  rw [hge]
  have h3 := (hrest i _ hr).2.2 x 0 (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero] at h3
  have hj : (1 : ℝ) ≤ jbracket x ^ ((d : ℝ) / 2 + 2) :=
    Real.one_le_rpow (s86_one_le_jb x) (by positivity)
  have := (le_mul_of_one_le_left (norm_nonneg _) hj).trans h3
  exact this.trans (le_max_left _ _)

end HRS.MS.FinNoise
