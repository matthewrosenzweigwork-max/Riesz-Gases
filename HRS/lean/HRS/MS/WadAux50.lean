import HRS.MS.WadAux49

/-!
# S8.3 (Route A): every `IsWeightedSemigroup` is the extension `s85_Ulim`

`s85_semigroup_unique`: for `U` with `IsWeightedSemigroup (critCoeff …) (withDensityReal ρβ) M U` (`M > 0`),
`U t f = s85_Ulim … t f` for all `t ≥ 0`, `f ∈ C_M`.  (On `C_c^∞` by uniqueness of the projected backward solution,
then by the density of `C_c^∞` and the bounded linear structure of `U`.)  This reduces the second conjunct of the
frozen S8.3 to statements about `s85_Ulim`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_Cc_memCM (M : ℝ) {φ : Euc d → ℝ} (hφ : S85Cc φ) : MemCM M φ := by
  refine ⟨hφ.1.continuous, ?_⟩
  have hev : ∀ᶠ x in cocompact (Euc d), φ x / jbracket x ^ M = 0 := by
    filter_upwards [hφ.2.compl_mem_cocompact] with x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_div]
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem s85_memCM_sub {M : ℝ} {f g : Euc d → ℝ} (hf : MemCM M f) (hg : MemCM M g) : MemCM M (f - g) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  have := hf.2.sub hg.2
  simpa [Pi.sub_apply, sub_div] using this

theorem s85_semigroup_unique (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {M : ℝ} (hM : 0 < M)
    {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) {t : ℝ}
    (ht : 0 ≤ t) {f : Euc d → ℝ} (hf : MemCM M f) : U t f = s85_Ulim a β ρβ M t f := by
  have H : S85Hyp d a β (t + 1) M ρβ := ⟨hd, ha, hβ, by linarith, hM.le, hρ⟩
  have htT : t ≤ t + 1 := by linarith
  -- on C_c^∞
  have hcc : ∀ {φ : Euc d → ℝ}, S85Cc φ → U t φ = s85_Ulim a β ρβ M t φ := by
    intro φ hφ
    obtain ⟨f', hf', hUf'⟩ := hU.classical t ht φ hφ.1 hφ.2
    obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ ht hφ
    funext x
    rw [hUf', s85_proj_unique hd ha hβ hρ ht hf' hw x, s85_Ulim_cc H ht htT hφ,
      s85_Ucc_eq hd ha hβ hρ ht hw]
  obtain ⟨K, hK⟩ := hU.bdd t ht
  have hK' := hK t ⟨ht, le_rfl⟩
  set K₀ : ℝ := max K 0 with hK₀
  have hK₀0 : 0 ≤ K₀ := le_max_right _ _
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM.le hf
  obtain ⟨Kd, C, hKd0, hC0, hdist⟩ := s85_approx_dist H ht htT hφ
  have hcc' := hφ.1
  obtain ⟨-, C', hC'0, hC⟩ := hφ
  funext x
  have hJ0 : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
  have hbound : ∀ n : ℕ, |U t f x - s85_Ulim a β ρβ M t f x| ≤
      (K₀ * (C' / ((n : ℝ) + 1)) + Kd * (C / ((n : ℝ) + 1))) * jbracket x ^ M := by
    intro n
    have hφm : MemCM M (φ n) := s85_Cc_memCM M (hcc' n)
    have hgm : MemCM M (f - φ n) := s85_memCM_sub hf hφm
    have hsplit : U t f x = U t (f - φ n) x + U t (φ n) x := by
      have := hU.add t ht (f - φ n) (φ n) hgm hφm
      rw [sub_add_cancel] at this
      exact congrFun this x
    have hWt : Wt M (C' / ((n : ℝ) + 1)) (f - φ n) := by
      intro y
      show ‖f y - φ n y‖ ≤ _
      rw [norm_sub_rev]; exact hC n y
    have hCn : 0 ≤ C' / ((n : ℝ) + 1) := by positivity
    have h1 := hK' (f - φ n) hgm
    have h2 : weightedSupE 0 (-M) (U t (f - φ n)) ≤ ENNReal.ofReal (K₀ * (C' / ((n : ℝ) + 1))) := by
      calc weightedSupE 0 (-M) (U t (f - φ n)) ≤ ENNReal.ofReal K * weightedSupE 0 (-M) (f - φ n) := h1
        _ ≤ ENNReal.ofReal K₀ * ENNReal.ofReal (C' / ((n : ℝ) + 1)) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _))
              ((s83_wsup0_le_iff hCn _).2 hWt)
        _ = ENNReal.ofReal (K₀ * (C' / ((n : ℝ) + 1))) := (ENNReal.ofReal_mul hK₀0).symm
    have h3 := (s83_wsup0_le_iff (mul_nonneg hK₀0 hCn) _).1 h2 x
    rw [Real.norm_eq_abs] at h3
    have h4 := hdist n x
    rw [← s85_Ulim_cc H ht htT (hcc' n) x] at h4
    have e : U t f x - s85_Ulim a β ρβ M t f x = U t (f - φ n) x +
        (s85_Ulim a β ρβ M t (φ n) x - s85_Ulim a β ρβ M t f x) := by
      rw [hsplit, ← hcc (hcc' n)]; ring
    rw [e]
    calc |U t (f - φ n) x + (s85_Ulim a β ρβ M t (φ n) x - s85_Ulim a β ρβ M t f x)|
        ≤ |U t (f - φ n) x| + |s85_Ulim a β ρβ M t (φ n) x - s85_Ulim a β ρβ M t f x| := abs_add_le _ _
      _ ≤ K₀ * (C' / ((n : ℝ) + 1)) * jbracket x ^ M + Kd * (C / ((n : ℝ) + 1)) * jbracket x ^ M :=
          add_le_add h3 h4
      _ = (K₀ * (C' / ((n : ℝ) + 1)) + Kd * (C / ((n : ℝ) + 1))) * jbracket x ^ M := by ring
  have hlim0 : Tendsto (fun n : ℕ => (K₀ * C' + Kd * C) * jbracket x ^ M * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((K₀ * C' + Kd * C) * jbracket x ^ M)
  have hb2 : ∀ n : ℕ, |U t f x - s85_Ulim a β ρβ M t f x| ≤
      (K₀ * C' + Kd * C) * jbracket x ^ M * (1 / ((n : ℝ) + 1)) := fun n => by
    refine (hbound n).trans (le_of_eq ?_)
    ring
  have := ge_of_tendsto' hlim0 hb2
  have h0 := abs_nonneg (U t f x - s85_Ulim a β ρβ M t f x)
  have h1 : |U t f x - s85_Ulim a β ρβ M t f x| = 0 := le_antisymm this h0
  exact sub_eq_zero.1 (abs_eq_zero.1 h1)

end HRS.MS.Wad
