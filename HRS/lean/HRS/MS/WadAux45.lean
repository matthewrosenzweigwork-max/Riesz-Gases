import HRS.MS.WadAux44

/-!
# S8.3, packet D8 (Route A), part 4: the semigroup law and existence of the weighted semigroup

`s85_Ulim_ext`: the extension agrees with `w_0 - μ(w_0) + μ(φ')` for any datum `φ' ∈ C_M` that is the terminal
value of a frozen classical solution.  `s85_semigroup_cc`, `s85_semigroup`: `U_{t+s} = U_t U_s`.
`s85_exists_semigroup`: `IsWeightedSemigroup (critCoeff …) (withDensityReal ρβ) M (s85_Ulim …)`
(the existence conjunct of the frozen S8.3).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_Ucc_memCM {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) {φ : Euc d → ℝ} (hφ : S85Cc φ) : MemCM M (s85_Ucc a β ρβ t φ) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨hc, C', hw⟩ := s85_Ucc_props hd ha hβ hT (M' := M / 2) (by positivity) hρ ht0 htT hφ
  exact s85_cm_of_wt (by linarith) hc hw

theorem s85_Ulim_ext {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {w : ℝ → Euc d → ℝ} {φ' : Euc d → ℝ}
    (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ' w) (hφ' : MemCM M φ') (x : Euc d) :
    s85_Ulim a β ρβ M t φ' x = s85_V ρβ w φ' x := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨K, hK0, hK⟩ := s85_V_bound hd ha hβ hT hM hρ
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hφ'
  have sp := s85_Ulim_spec H ht0 htT hφ x
  obtain ⟨hcc, C, hC0, hC⟩ := hφ
  have hex : ∀ n, ∃ wn, IsClassicalAdjointW (critCoeff d a β ρβ) t (φ n) wn := fun n =>
    s85_exists_cl hd ha hβ hρ ht0 (hcc n)
  choose wn hwn using hex
  have hU : ∀ n, s85_Ucc a β ρβ t (φ n) x = s85_V ρβ (wn n) (φ n) x := fun n =>
    s85_Ucc_eq hd ha hβ hρ ht0 (hwn n) x
  have hlim0 : Tendsto (fun n : ℕ => K * C * jbracket x ^ M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K * C * jbracket x ^ M)
  have h0 : Tendsto (fun n : ℕ => s85_V ρβ (wn n) (φ n) x - s85_V ρβ w φ' x) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hlim0
    have := hK ht0 htT (hwn n) hw (hC n) x
    rw [Real.norm_eq_abs]
    calc _ ≤ K * (C / ((n : ℝ) + 1)) * jbracket x ^ M := this
      _ = K * C * jbracket x ^ M * (1 / ((n : ℝ) + 1)) := by ring
  have hlim : Tendsto (fun n : ℕ => s85_Ucc a β ρβ t (φ n) x) atTop (𝓝 (s85_V ρβ w φ' x)) := by
    have := h0.add_const (s85_V ρβ w φ' x)
    simp only [zero_add, sub_add_cancel] at this
    exact this.congr fun n => (hU n).symm
  exact tendsto_nhds_unique sp hlim

theorem s85_semigroup_cc {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ T) {φ : Euc d → ℝ} (hφ : S85Cc φ) (x : Euc d) :
    s85_Ulim a β ρβ M (t + s) φ x = s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s φ) x := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  have hts0 : 0 ≤ t + s := add_nonneg ht hs
  have hsT : s ≤ T := by linarith
  have htT : t ≤ T := by linarith
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ hts0 hφ
  have hgs : IsClassicalAdjointW (critCoeff d a β ρβ) s φ (fun r => w (r + t)) :=
    s85_G_to_cl (s85_G_shift (fun r r' h x => s85_gen_time a β ρβ r r' h x) ht hs (s85_cl_to_G hw))
  have hres : IsClassicalAdjointW (critCoeff d a β ρβ) t (w t) w :=
    s85_G_to_cl (s85_G_restrict (le_add_of_nonneg_right hs) (s85_cl_to_G hw))
  set c₀ : ℝ := HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ - ∫ z, w t z ∂(HRS.Whole.withDensityReal ρβ)
    with hc₀
  have hφ' : ∀ y, s85_Ulim a β ρβ M s φ y = w t y + c₀ := by
    intro y
    rw [s85_Ulim_cc H hs hsT hφ, s85_Ucc_eq hd ha hβ hρ hs hgs]
    unfold s85_V
    simp only [zero_add]
    rw [hc₀]
    ring
  have hu' : IsClassicalAdjointW (critCoeff d a β ρβ) t (fun y => w t y + c₀) (fun r y => w r y + c₀) := by
    have := s85_transfer (G := generatorW (critCoeff d a β ρβ)) (G' := generatorW (critCoeff d a β ρβ))
      (s85_cl_to_G hres) (κ := fun _ => c₀) (κ' := fun _ => 0) continuousOn_const continuousOn_const
      (fun r _ => hasDerivAt_const r c₀)
      (fun r _ x => by simpa using s85_gen_add_const a β ρβ r (w r) c₀ x)
    exact s85_G_to_cl this
  have hmem : MemCM M (fun y => w t y + c₀) := by
    have e : (fun y => w t y + c₀) = s85_Ucc a β ρβ s φ := funext fun y =>
      ((hφ' y).symm.trans (s85_Ulim_cc H hs hsT hφ y))
    rw [e]
    exact s85_Ucc_memCM H hMpos hs hsT hφ
  have e : s85_Ulim a β ρβ M s φ = fun y => w t y + c₀ := funext hφ'
  rw [e, s85_Ulim_ext H ht htT hu' hmem x, s85_Ulim_cc H hts0 hts hφ, s85_Ucc_eq hd ha hβ hρ hts0 hw]
  obtain ⟨i0, iφ⟩ := s85_cl_int hd ha hβ hρ hts0 hw
  obtain ⟨-, it⟩ := s85_cl_int hd ha hβ hρ ht hres
  unfold s85_V
  have e1 : ∫ z, (w 0 z + c₀) ∂(HRS.Whole.withDensityReal ρβ) =
      ∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ) + c₀ := by
    rw [integral_add i0 (integrable_const c₀)]; simp
  have e2 : HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) (fun y => w t y + c₀) =
      ∫ z, w t z ∂(HRS.Whole.withDensityReal ρβ) + c₀ := by
    unfold HRS.Whole.pair
    rw [integral_add it (integrable_const c₀)]; simp
  rw [e1, e2, hc₀]
  ring

theorem s85_semigroup {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s ≤ T) {f : Euc d → ℝ} (hf : MemCM M f)
    (x : Euc d) :
    s85_Ulim a β ρβ M (t + s) f x = s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  have hts0 : 0 ≤ t + s := add_nonneg ht hs
  have hsT : s ≤ T := by linarith
  have htT : t ≤ T := by linarith
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  obtain ⟨Kb, hKb0, hKb⟩ := s85_Ulim_bound H
  obtain ⟨K₁, C₁, hK₁0, hC₁0, hd1⟩ := s85_approx_dist H hs hsT hφ
  obtain ⟨K₂, C₂, hK₂0, hC₂0, hd2⟩ := s85_approx_dist H hts0 hts hφ
  have hcc := hφ.1
  have hmf : MemCM M (s85_Ulim a β ρβ M s f) := s85_Ulim_memCM H hMpos hs hsT hf
  have hJ0 : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
  have hbound : ∀ n : ℕ, |s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x| ≤
      (K₂ * C₂ + Kb * (K₁ * C₁)) * jbracket x ^ M * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hgn : MemCM M (s85_Ulim a β ρβ M s (φ n)) := by
      have e : s85_Ulim a β ρβ M s (φ n) = s85_Ucc a β ρβ s (φ n) :=
        funext fun y => s85_Ulim_cc H hs hsT (hcc n) y
      rw [e]; exact s85_Ucc_memCM H hMpos hs hsT (hcc n)
    have t1 : |s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M (t + s) (φ n) x| ≤
        K₂ * (C₂ / ((n : ℝ) + 1)) * jbracket x ^ M := by
      rw [s85_Ulim_cc H hts0 hts (hcc n), abs_sub_comm]
      exact hd2 n x
    have t2 : s85_Ulim a β ρβ M (t + s) (φ n) x =
        s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s (φ n)) x := s85_semigroup_cc H hMpos ht hs hts (hcc n) x
    have t3 : |s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s (φ n)) x -
        s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x| ≤
        Kb * (K₁ * (C₁ / ((n : ℝ) + 1))) * jbracket x ^ M := by
      refine hKb ht htT hgn hmf (Φ := K₁ * (C₁ / ((n : ℝ) + 1))) (fun y => ?_) x
      show ‖s85_Ulim a β ρβ M s (φ n) y - s85_Ulim a β ρβ M s f y‖ ≤ _
      rw [Real.norm_eq_abs, s85_Ulim_cc H hs hsT (hcc n) y]
      exact hd1 n y
    have e : s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x =
        (s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M (t + s) (φ n) x) +
          (s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s (φ n)) x -
            s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x) := by
      rw [← t2]; ring
    rw [e]
    calc _ ≤ |s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M (t + s) (φ n) x| +
          |s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s (φ n)) x -
            s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x| := abs_add_le _ _
      _ ≤ K₂ * (C₂ / ((n : ℝ) + 1)) * jbracket x ^ M +
          Kb * (K₁ * (C₁ / ((n : ℝ) + 1))) * jbracket x ^ M := add_le_add t1 t3
      _ = (K₂ * C₂ + Kb * (K₁ * C₁)) * jbracket x ^ M * (1 / ((n : ℝ) + 1)) := by ring
  have hlim0 : Tendsto (fun n : ℕ => (K₂ * C₂ + Kb * (K₁ * C₁)) * jbracket x ^ M * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((K₂ * C₂ + Kb * (K₁ * C₁)) * jbracket x ^ M)
  have := ge_of_tendsto' hlim0 hbound
  have h0 := abs_nonneg (s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x)
  have h1 : |s85_Ulim a β ρβ M (t + s) f x - s85_Ulim a β ρβ M t (s85_Ulim a β ρβ M s f) x| = 0 :=
    le_antisymm this h0
  exact sub_eq_zero.1 (abs_eq_zero.1 h1)

end HRS.MS.Wad
