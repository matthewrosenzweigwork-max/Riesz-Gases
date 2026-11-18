import HRS.MS.R2ChaosAux52

/-!
# HRS.MS.R2ChaosAux53 -- S9.6 (P1, part 2): the truncations `h^j = h 1_{max(|x|,|y|) ≤ j}`

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.  `s95_part g j` is the truncation (`s95_cut (-1) j`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

section Trunc

variable {s Pw B : ℝ}

theorem s94_polyB_nonneg (hd : 2 ≤ d) {h : Euc d → Euc d → ℝ} (hh : IsR2PolyPairKernel s Pw B h) : 0 ≤ B := by
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
  obtain ⟨x0, y0, hxy0⟩ := exists_pair_ne (Euc d)
  have h1 := hh.bound x0 y0 hxy0
  have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (x0 - y0)
  have hj : 0 < (jbracket x0 + jbracket y0) ^ Pw :=
    Real.rpow_pos_of_pos (by linarith [s95_one_le_jb x0, s95_one_le_jb y0]) _
  have h2 : 0 < (jbracket x0 + jbracket y0) ^ Pw * (1 + rieszWeight s (x0 - y0)) := by positivity
  have := (abs_nonneg _).trans h1
  rw [mul_assoc] at this
  exact (mul_nonneg_iff_of_pos_right h2).mp this

theorem s94_trunc_poly {g : Euc d → Euc d → ℝ} (hg : IsR2PolyPairKernel s Pw B g) (j : ℕ) :
    IsR2PolyPairKernel s Pw B (s95_part g j) where
  measurable := s95_cut_meas hg.measurable _ _
  symm := s95_cut_symm hg.symm _ _
  bound x y hxy := (s95_cut_abs_le _ _ g x y).trans (hg.bound x y hxy)

theorem s94_trunc_bdd (hd : 2 ≤ d) (hPw : 0 ≤ Pw) {g : Euc d → Euc d → ℝ} (hg : IsR2PolyPairKernel s Pw B g) (j : ℕ) :
    IsBoundedPairKernel s (B * 2 ^ Pw * (1 + (j : ℝ)) ^ Pw) (s95_part g j) :=
  s95_cut_bounded hPw hg (-1) (Nat.cast_nonneg j) (s94_polyB_nonneg hd hg)

theorem s94_trunc_family_meas {h : ℝ → Euc d → Euc d → ℝ}
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2) (j : ℕ) :
    Measurable fun q : ℝ × Euc d × Euc d => s95_part (h q.1) j q.2.1 q.2.2 := by
  unfold s95_part s95_cut
  refine Measurable.ite ?_ hmeas measurable_const
  exact (measurableSet_lt measurable_const
    ((measurable_fst.comp measurable_snd).norm.max (measurable_snd.comp measurable_snd).norm)).inter
    (measurableSet_le ((measurable_fst.comp measurable_snd).norm.max (measurable_snd.comp measurable_snd).norm)
      measurable_const)

section Lq

variable {M L C₀ c₀ : ℝ} {ρ : Euc d → ℝ}

theorem s94_trunc_lq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw) {g : Euc d → Euc d → ℝ}
    (hg : IsR2PolyPairKernel s Pw B g) {q : ℝ} (hq : 1 ≤ q) (hqs : q * s < d) :
    Tendsto (fun j : ℕ => eLpNorm (fun z : Euc d × Euc d => s95_part g j z.1 z.2 - g z.1 z.2) (ENNReal.ofReal q)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set ν := (Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ) with hν
  have hq0 : 0 < q := by linarith
  have hmem := s94_poly_memLp hd hs0 hs hρ hG hPw (s94_polyB_nonneg hd hg) hg hq hqs
  have hgm := hg.measurable
  have hcm : ∀ j : ℕ, Measurable fun z : Euc d × Euc d => s95_part g j z.1 z.2 :=
    fun j => s95_cut_meas hg.measurable _ _
  have hlin : ∀ j : ℕ, ∫⁻ z : Euc d × Euc d, ‖s95_part g j z.1 z.2 - g z.1 z.2‖ₑ ^ q ∂ν ≤ ⊤ := fun _ => le_top
  have hlim : Tendsto (fun j : ℕ => ∫⁻ z : Euc d × Euc d, ‖s95_part g j z.1 z.2 - g z.1 z.2‖ₑ ^ q ∂ν) atTop (𝓝 0) := by
    have hbound : ∫⁻ z : Euc d × Euc d, ‖g z.1 z.2‖ₑ ^ q ∂ν ≠ ⊤ := by
      have := hmem
      have h2 : eLpNorm (fun z : Euc d × Euc d => g z.1 z.2) (ENNReal.ofReal q) ν < ⊤ := this
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top
        hgm.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le] at h2
      intro htop
      rw [htop] at h2
      rw [one_div, ENNReal.top_rpow_of_pos (by positivity : 0 < q⁻¹)] at h2
      exact lt_irrefl _ h2
    have := tendsto_lintegral_of_dominated_convergence (μ := ν)
      (F := fun (j : ℕ) (z : Euc d × Euc d) => ‖s95_part g j z.1 z.2 - g z.1 z.2‖ₑ ^ q)
      (f := fun _ => 0) (fun z => ‖g z.1 z.2‖ₑ ^ q)
      (fun j => ((hcm j).sub hgm).enorm.pow_const q) (fun j => ae_of_all _ fun z => by
        have : ‖s95_part g j z.1 z.2 - g z.1 z.2‖ₑ ≤ ‖g z.1 z.2‖ₑ := by
          unfold s95_part s95_cut
          split_ifs <;> simp
        exact ENNReal.rpow_le_rpow this hq0.le) hbound
      (ae_of_all _ fun z => by
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨J, hJ⟩ := exists_nat_ge (max ‖z.1‖ ‖z.2‖)
        filter_upwards [eventually_ge_atTop J] with j hj
        have := s95_part_eq g (x := z.1) (y := z.2) (hJ.trans (by exact_mod_cast hj))
        simp [this, ENNReal.zero_rpow_of_pos hq0])
    simpa using this
  have hm2 : ∀ j : ℕ, AEStronglyMeasurable (fun z : Euc d × Euc d => s95_part g j z.1 z.2 - g z.1 z.2) ν :=
    fun j => ((hcm j).sub hgm).aestronglyMeasurable
  have e : ∀ j : ℕ, eLpNorm (fun z : Euc d × Euc d => s95_part g j z.1 z.2 - g z.1 z.2) (ENNReal.ofReal q) ν =
      (∫⁻ z : Euc d × Euc d, ‖s95_part g j z.1 z.2 - g z.1 z.2‖ₑ ^ q ∂ν) ^ (1 / q) := fun j => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top (hm2 j),
      ENNReal.toReal_ofReal hq0.le]
  simp_rw [e]
  have hq1' : 0 < 1 / q := by positivity
  have h3 : Tendsto (fun j : ℕ => (∫⁻ z : Euc d × Euc d, ‖s95_part g j z.1 z.2 - g z.1 z.2‖ₑ ^ q ∂ν) ^ (1 / q))
      atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / q))) := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto 0).comp hlim
  rwa [ENNReal.zero_rpow_of_pos hq1'] at h3

end Lq

end Trunc

end HRS.MS.R2Chaos
