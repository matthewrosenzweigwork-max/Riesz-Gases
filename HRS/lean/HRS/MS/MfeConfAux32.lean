import HRS.MS.MfeConfAux31

/-!
# S.B.1, packet F3 (part 13): the limit of the smoothed Gibbs integrals at one time

Fix one density `ρ0` (`Sb1Rho`), a Lipschitz transport field `u`, a sequence of admissible kernels `k_n → k` (pointwise off
`0`) with `|∇k_n(z) e| ≤ σ|z|^{-s-1}|e|` uniformly.  With `F_n = e^{-βN En_{k_n}}`, `P_n = 𝖥_N^{h_n}`,
`h_n(x,y) = ∇k_n(x-y)·(u(x)-u(y))`:

* `sb1_K_tendsto`: `∫ F_n dμ^N → ∫ F dμ^N`;
* `sb1_Phi_tendsto`: `∫ F_n P_n dμ^N → ∫ F P dμ^N`;
* `sb1_Phi_abs_le`: `|∫ F_n P_n dμ^N| ≤ C_w · 2 σ L C_s`, uniformly in `n`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- `h_k(x,y) = ∇k(x-y)·(u(x)-u(y))` -/
def sb1hk (k : Euc d → ℝ) (u : Euc d → Euc d) (x y : Euc d) : ℝ := fderiv ℝ k (x - y) (u x - u y)

/-- `F = e^{-βN En}` -/
def sb1FF (k : Euc d → ℝ) (β : ℝ) (N : ℕ) (ρ0 : Euc d → ℝ) (X : Whole.EucConfig d N) : ℝ :=
  Real.exp (-β * N * sb1En k ρ0 X)

/-- `P = 𝖥_N^{h_k}` -/
def sb1PE (k : Euc d → ℝ) (u : Euc d → Euc d) (ρ0 : Euc d → ℝ) (X : Whole.EucConfig d N) : ℝ :=
  Whole.pairEnergy (sb1hk k u) X (Whole.withDensityReal ρ0)

/-- the constant bounding the row integrals of `|z|^{-s}` -/
def sb1Cs (d : ℕ) (s Cρ : ℝ) : ℝ := Cρ * sb1Isig d s + 1

section Single

variable {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ}

theorem sb1_row_Cs (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) (x : Euc d) :
    Integrable (fun y => ρ0 y * ‖x - y‖ ^ (-s)) ∧ ∫ y, ρ0 y * ‖x - y‖ ^ (-s) ≤ sb1Cs d s Cρ := by
  obtain ⟨hI, hIb⟩ := sb1_conv_loc hd hs0 hsd R.dens.nonneg R.dens.measurable R.integrable R.le x
  exact ⟨hI, by rw [R.int_one] at hIb; unfold sb1Cs; exact hIb⟩

theorem sb1_int_wd (R : Sb1Rho ρ0 Cρ M1) {g : Euc d → ℝ} :
    Integrable g (Whole.withDensityReal ρ0) ↔ Integrable (fun y => ρ0 y * g y) := by
  unfold Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' R.dens.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (R.dens.nonneg y)]

theorem sb1_pair_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) :
    Integrable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s))
      ((Whole.withDensityReal ρ0).prod (Whole.withDensityReal ρ0)) ∧
    ∫ p : Euc d × Euc d, ‖p.1 - p.2‖ ^ (-s) ∂((Whole.withDensityReal ρ0).prod (Whole.withDensityReal ρ0)) ≤
      sb1Cs d s Cρ := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hm : Measurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s)) :=
    (measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _
  have hrow : ∀ x : Euc d, Integrable (fun y => ‖x - y‖ ^ (-s)) (Whole.withDensityReal ρ0) ∧
      ∫ y, ‖x - y‖ ^ (-s) ∂(Whole.withDensityReal ρ0) ≤ sb1Cs d s Cρ := fun x => by
    obtain ⟨hI, hIb⟩ := sb1_row_Cs hd hs0 hsd R x
    exact ⟨(sb1_int_wd R).2 hI, by rw [sb1_integral_wd R.dens.measurable R.dens.nonneg]; exact hIb⟩
  have hint : Integrable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s))
      ((Whole.withDensityReal ρ0).prod (Whole.withDensityReal ρ0)) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => (hrow x).1, ?_⟩
    refine Integrable.of_bound (C := sb1Cs d s Cρ) ?_ (Eventually.of_forall fun x => ?_)
    · exact (hm.norm.stronglyMeasurable.integral_prod_right' (ν := Whole.withDensityReal ρ0)).aestronglyMeasurable
    · show ‖∫ y, ‖‖x - y‖ ^ (-s)‖ ∂(Whole.withDensityReal ρ0)‖ ≤ sb1Cs d s Cρ
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖‖x - y‖ ^ (-s)‖ ∂(Whole.withDensityReal ρ0) = ∫ y, ‖x - y‖ ^ (-s) ∂(Whole.withDensityReal ρ0) :=
            integral_congr_ae (Eventually.of_forall fun y => Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _))
        _ ≤ _ := (hrow x).2
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  calc ∫ x, ∫ y, ‖(x, y).1 - (x, y).2‖ ^ (-s) ∂(Whole.withDensityReal ρ0) ∂(Whole.withDensityReal ρ0)
      ≤ ∫ _x, sb1Cs d s Cρ ∂(Whole.withDensityReal ρ0) :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => integral_nonneg fun y =>
          Real.rpow_nonneg (norm_nonneg _) _) (integrable_const _) (Eventually.of_forall fun x => (hrow x).2)
    _ = sb1Cs d s Cρ := by simp

theorem sb1_pairX_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) {i j : Fin N} (hij : i ≠ j) :
    Integrable (fun X : Whole.EucConfig d N => ‖X i - X j‖ ^ (-s))
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ∧
    ∫ X : Whole.EucConfig d N, ‖X i - X j‖ ^ (-s) ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≤
      sb1Cs d s Cρ := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  obtain ⟨hI, hIb⟩ := sb1_pair_int hd hs0 hsd R
  refine ⟨HRS.integrable_pair_comp _ hij (H := fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s)) hI, ?_⟩
  calc ∫ X : Whole.EucConfig d N, ‖X i - X j‖ ^ (-s) ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)
      = ∫ p : Euc d × Euc d, ‖p.1 - p.2‖ ^ (-s) ∂((Whole.withDensityReal ρ0).prod (Whole.withDensityReal ρ0)) :=
        HRS.integral_pair_comp _ hij (H := fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s)) hI
    _ ≤ _ := hIb

theorem sb1_PG_meas {h : Euc d → Euc d → ℝ} (R : Sb1Rho ρ0 Cρ M1)
    (hm : Measurable (fun p : Euc d × Euc d => h p.1 p.2)) : Measurable (sb1PG h ρ0) := by
  have : StronglyMeasurable (fun p : Euc d × Euc d => ρ0 p.2 * h p.1 p.2) :=
    ((R.dens.measurable.comp measurable_snd).mul hm).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume)).measurable

theorem sb1_PG_abs_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {h : Euc d → Euc d → ℝ} (hb : ∀ x y, |h x y| ≤ c₀ * ‖x - y‖ ^ (-s)) (x : Euc d) :
    |sb1PG h ρ0 x| ≤ c₀ * sb1Cs d s Cρ := by
  obtain ⟨hI, hIb⟩ := sb1_row_Cs hd hs0 hsd R x
  have hI' : Integrable (fun y => ρ0 y * (c₀ * ‖x - y‖ ^ (-s))) := by
    have := hI.const_mul c₀
    simpa [mul_left_comm] using this
  have h1 := norm_integral_le_of_norm_le hI' (f := fun y => ρ0 y * h x y) (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hb x y) (R.dens.nonneg y))
  rw [Real.norm_eq_abs] at h1
  unfold sb1PG
  refine h1.trans ?_
  calc ∫ y, ρ0 y * (c₀ * ‖x - y‖ ^ (-s)) = c₀ * ∫ y, ρ0 y * ‖x - y‖ ^ (-s) := by
        rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun y => by ring)
    _ ≤ c₀ * sb1Cs d s Cρ := mul_le_mul_of_nonneg_left hIb hc₀

theorem sb1_pairE_abs_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    {h : Euc d → Euc d → ℝ} (hb : ∀ x y, |h x y| ≤ c₀ * ‖x - y‖ ^ (-s)) (hN : 1 ≤ N)
    (X : Whole.EucConfig d N) :
    |Whole.pairEnergy h X (Whole.withDensityReal ρ0)| ≤
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, c₀ * ‖X i - X j‖ ^ (-s) +
        (3 / 2) * (c₀ * sb1Cs d s Cρ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sb1_pairEnergy_eq R.dens h X]
  have hPG := sb1_PG_abs_le hd hs0 hsd R hc₀ hb
  have t1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| ≤
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, c₀ * ‖X i - X j‖ ^ (-s) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_))
      (by positivity)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hb _ _)
  have t2 : |(1 / (N : ℝ)) * ∑ i, sb1PG h ρ0 (X i)| ≤ c₀ * sb1Cs d s Cρ := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc 1 / (N : ℝ) * |∑ i, sb1PG h ρ0 (X i)| ≤ 1 / (N : ℝ) * ∑ _i : Fin N, c₀ * sb1Cs d s Cρ :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hPG _))
            (by positivity)
      _ = c₀ * sb1Cs d s Cρ := by
          have hNne : (N : ℝ) ≠ 0 := hn.ne'
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have t3 : |(1 / 2) * ∫ x, ρ0 x * sb1PG h ρ0 x| ≤ (1 / 2) * (c₀ * sb1Cs d s Cρ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have := norm_integral_le_of_norm_le (R.integrable.const_mul (c₀ * sb1Cs d s Cρ))
      (f := fun x => ρ0 x * sb1PG h ρ0 x) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg x)]
        nlinarith [hPG x, R.dens.nonneg x])
    rw [Real.norm_eq_abs, integral_const_mul, R.int_one] at this
    linarith
  calc _ ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) -
        (1 / (N : ℝ)) * ∑ i, sb1PG h ρ0 (X i)| + |(1 / 2) * ∫ x, ρ0 x * sb1PG h ρ0 x| := abs_add_le _ _
    _ ≤ (|(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)| +
        |(1 / (N : ℝ)) * ∑ i, sb1PG h ρ0 (X i)|) + |(1 / 2) * ∫ x, ρ0 x * sb1PG h ρ0 x| :=
        add_le_add (abs_sub _ _) le_rfl
    _ ≤ _ := by linarith [t1, t2, t3]

theorem sb1_pairE_meas (R : Sb1Rho ρ0 Cρ M1) {h : Euc d → Euc d → ℝ}
    (hm : Measurable (fun p : Euc d × Euc d => h p.1 p.2)) :
    Measurable (fun X : Whole.EucConfig d N => Whole.pairEnergy h X (Whole.withDensityReal ρ0)) := by
  have e : (fun X : Whole.EucConfig d N => Whole.pairEnergy h X (Whole.withDensityReal ρ0)) = fun X =>
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
        - (1 / (N : ℝ)) * ∑ i, sb1PG h ρ0 (X i) + (1 / 2) * ∫ x, ρ0 x * sb1PG h ρ0 x :=
    funext fun X => sb1_pairEnergy_eq R.dens h X
  rw [e]
  refine Measurable.add (Measurable.sub (Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => hm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))) _)
    (Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      (sb1_PG_meas R hm).comp (measurable_pi_apply i)) _)) measurable_const

end Single

end HRS.MS.MfeConf
