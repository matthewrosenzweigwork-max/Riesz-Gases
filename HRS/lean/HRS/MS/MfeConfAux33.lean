import HRS.MS.MfeConfAux32

/-!
# S.B.1, packet F3 (part 14): the one-time limits `K_n → K`, `Φ_n → Φ` and the uniform bound of `Φ_n`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- `C_w = exp(βN(C_G + κ M₁))` -/
def sb1CwR (d : ℕ) (s Cρ M1 β : ℝ) (N : ℕ) : ℝ := Real.exp (β * N * (sb1CG d s Cρ M1 + sb1kap s * M1))

section Conv

variable {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ} {kn : ℕ → Euc d → ℝ} {k : Euc d → ℝ}

theorem sb1_En_meas {k : Euc d → ℝ} (hk : Sb1KerU d s k) (R : Sb1Rho ρ0 Cρ M1) :
    Measurable (sb1En k ρ0 : Whole.EucConfig d N → ℝ) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have := sb1_measurable_modulatedEnergy (N := N) hk.meas (Whole.withDensityReal ρ0)
  have e : (sb1En k ρ0 : Whole.EucConfig d N → ℝ) =
      fun X => Whole.modulatedEnergy k X (Whole.withDensityReal ρ0) :=
    funext fun X => (sb1_modEnergy_eq R.dens k X).symm
  rw [e]; exact this

theorem sb1_FF_meas {k : Euc d → ℝ} (hk : Sb1KerU d s k) (R : Sb1Rho ρ0 Cρ M1) (β : ℝ) :
    Measurable (sb1FF k β N ρ0 : Whole.EucConfig d N → ℝ) :=
  Real.measurable_exp.comp ((sb1_En_meas hk R).const_mul _)

theorem sb1_G_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hkn : ∀ n, Sb1KerU d s (kn n))
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1) (x : Euc d) :
    Tendsto (fun n => sb1G (kn n) ρ0 x) atTop (𝓝 (sb1G k ρ0 x)) := by
  obtain ⟨hI, -⟩ := sb1_Om_conv hd hs0 hsd R.dens.nonneg R.dens.measurable R.integrable R.le R.mom x
  refine tendsto_integral_of_dominated_convergence (fun y => ρ0 y * sb1Om s (x - y))
    (fun n => (R.dens.measurable.mul ((hkn n).meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    hI (fun n => ?_) ?_
  · filter_upwards [sb1_ae_ne hd x] with y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
    exact mul_le_mul_of_nonneg_left (sb1_k_abs_le hs0 (hkn n) (sub_ne_zero.2 (Ne.symm hy))) (R.dens.nonneg y)
  · filter_upwards [sb1_ae_ne hd x] with y hy
    exact (hconv _ (sub_ne_zero.2 (Ne.symm hy))).const_mul _

theorem sb1_c_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hkn : ∀ n, Sb1KerU d s (kn n))
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1) :
    Tendsto (fun n => sb1c (kn n) ρ0) atTop (𝓝 (sb1c k ρ0)) := by
  have hb : Integrable (fun x => ρ0 x * ‖x‖ + sb1CG d s Cρ M1 * ρ0 x) := R.mom.add (R.integrable.const_mul _)
  refine tendsto_integral_of_dominated_convergence (fun x => ρ0 x * ‖x‖ + sb1CG d s Cρ M1 * ρ0 x)
    (fun n => (R.dens.measurable.mul (sb1_G_meas (hkn n) R)).aestronglyMeasurable) hb
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · have h := sb1_G_abs_le hd hs0 hsd (hkn n) R x
    have h0 := R.dens.nonneg x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    nlinarith [mul_le_mul_of_nonneg_left h h0, sb1_log_le_norm x]
  · exact (sb1_G_tendsto hd hs0 hsd hkn hconv R x).const_mul _

theorem sb1_En_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hkn : ∀ n, Sb1KerU d s (kn n))
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1)
    (X : Whole.EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    Tendsto (fun n => sb1En (kn n) ρ0 X) atTop (𝓝 (sb1En k ρ0 X)) := by
  unfold sb1En
  refine ((tendsto_const_nhds.mul ?_).sub (tendsto_const_nhds.mul ?_)).add
    (tendsto_const_nhds.mul (sb1_c_tendsto hd hs0 hsd hkn hconv R))
  · exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j hj =>
      hconv _ (sub_ne_zero.2 (hX i j (Finset.ne_of_mem_erase hj).symm))
  · exact tendsto_finset_sum _ fun i _ => sb1_G_tendsto hd hs0 hsd hkn hconv R (X i)

theorem sb1_K_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hkn : ∀ n, Sb1KerU d s (kn n)) (hk : Sb1KerU d s k)
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1) :
    Tendsto (fun n => ∫ X : Whole.EucConfig d N, sb1FF (kn n) β N ρ0 X
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)) atTop
      (𝓝 (∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0))) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hae := HRS.MS.Wr.ae_injective_pi_Euc (N := N) (HRS.MS.Wr.wr12_atomless hd ρ0)
  refine tendsto_integral_of_dominated_convergence (fun _ => sb1CwR d s Cρ M1 β N)
    (fun n => (sb1_FF_meas (hkn n) R β).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun X => ?_) ?_
  · unfold sb1FF
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact sb1_E_le hd hs0 hsd hN hβ (hkn n) R X
  · filter_upwards [hae] with X hX
    exact (Real.continuous_exp.tendsto _).comp ((sb1_En_tendsto hd hs0 hsd hkn hconv R X hX).const_mul (-β * N))

variable {hn : ℕ → Euc d → Euc d → ℝ} {h : Euc d → Euc d → ℝ} {c₀ : ℝ}

theorem sb1_PG_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) (hc₀ : 0 ≤ c₀)
    (hb : ∀ n x y, |hn n x y| ≤ c₀ * ‖x - y‖ ^ (-s))
    (hm : ∀ n, Measurable (fun p : Euc d × Euc d => hn n p.1 p.2))
    (hconvh : ∀ x y, x ≠ y → Tendsto (fun n => hn n x y) atTop (𝓝 (h x y))) (x : Euc d) :
    Tendsto (fun n => sb1PG (hn n) ρ0 x) atTop (𝓝 (sb1PG h ρ0 x)) := by
  obtain ⟨hI, -⟩ := sb1_row_Cs hd hs0 hsd R x
  have hI' : Integrable (fun y => ρ0 y * (c₀ * ‖x - y‖ ^ (-s))) := by
    have := hI.const_mul c₀
    simpa [mul_left_comm] using this
  refine tendsto_integral_of_dominated_convergence (fun y => ρ0 y * (c₀ * ‖x - y‖ ^ (-s)))
    (fun n => (R.dens.measurable.mul ((hm n).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    hI' (fun n => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hb n x y) (R.dens.nonneg y)
  · filter_upwards [sb1_ae_ne hd x] with y hy
    exact (hconvh x y (Ne.symm hy)).const_mul _

theorem sb1_cPG_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) (hc₀ : 0 ≤ c₀)
    (hb : ∀ n x y, |hn n x y| ≤ c₀ * ‖x - y‖ ^ (-s))
    (hm : ∀ n, Measurable (fun p : Euc d × Euc d => hn n p.1 p.2))
    (hconvh : ∀ x y, x ≠ y → Tendsto (fun n => hn n x y) atTop (𝓝 (h x y))) :
    Tendsto (fun n => ∫ x, ρ0 x * sb1PG (hn n) ρ0 x) atTop (𝓝 (∫ x, ρ0 x * sb1PG h ρ0 x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => (c₀ * sb1Cs d s Cρ) * ρ0 x)
    (fun n => (R.dens.measurable.mul (sb1_PG_meas R (hm n))).aestronglyMeasurable)
    (R.integrable.const_mul _) (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => (sb1_PG_tendsto hd hs0 hsd R hc₀ hb hm hconvh x).const_mul _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (R.dens.nonneg x)]
  nlinarith [sb1_PG_abs_le hd hs0 hsd R hc₀ (hb n) x, R.dens.nonneg x]

theorem sb1_pairE_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) (hc₀ : 0 ≤ c₀)
    (hb : ∀ n x y, |hn n x y| ≤ c₀ * ‖x - y‖ ^ (-s))
    (hm : ∀ n, Measurable (fun p : Euc d × Euc d => hn n p.1 p.2))
    (hconvh : ∀ x y, x ≠ y → Tendsto (fun n => hn n x y) atTop (𝓝 (h x y)))
    (X : Whole.EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    Tendsto (fun n => Whole.pairEnergy (hn n) X (Whole.withDensityReal ρ0)) atTop
      (𝓝 (Whole.pairEnergy h X (Whole.withDensityReal ρ0))) := by
  simp_rw [sb1_pairEnergy_eq R.dens]
  refine ((tendsto_const_nhds.mul ?_).sub (tendsto_const_nhds.mul ?_)).add
    (tendsto_const_nhds.mul (sb1_cPG_tendsto hd hs0 hsd R hc₀ hb hm hconvh))
  · exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j hj =>
      hconvh _ _ (hX i j (Finset.ne_of_mem_erase hj).symm)
  · exact tendsto_finset_sum _ fun i _ => sb1_PG_tendsto hd hs0 hsd R hc₀ hb hm hconvh (X i)

/-- integrable majorant of `|pairEnergy|` -/
def sb1Bmaj (d : ℕ) (s c₀ Cs : ℝ) (N : ℕ) (X : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, c₀ * ‖X i - X j‖ ^ (-s) + (3 / 2) * (c₀ * Cs)

theorem sb1_Bmaj_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : Sb1Rho ρ0 Cρ M1) {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
    (hN : 1 ≤ N) :
    Integrable (sb1Bmaj d s c₀ (sb1Cs d s Cρ) N : Whole.EucConfig d N → ℝ)
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ∧
    ∫ X : Whole.EucConfig d N, sb1Bmaj d s c₀ (sb1Cs d s Cρ) N X
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≤ 2 * (c₀ * sb1Cs d s Cρ) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hCs : 0 ≤ sb1Cs d s Cρ := by
    unfold sb1Cs; have := R.C_nonneg; have := sb1Isig_nonneg (d := d) s; positivity
  have hint : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      Integrable (fun X : Whole.EucConfig d N => c₀ * ‖X i - X j‖ ^ (-s))
        (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := fun i j hj =>
    ((sb1_pairX_int hd hs0 hsd R (Finset.ne_of_mem_erase hj).symm).1).const_mul c₀
  have hI1 : Integrable (fun X : Whole.EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, c₀ * ‖X i - X j‖ ^ (-s))
      (Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j hj => hint i j hj
  refine ⟨(hI1.const_mul _).add (integrable_const _), ?_⟩
  unfold sb1Bmaj
  rw [integral_add (hI1.const_mul _) (integrable_const _), integral_const_mul,
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j hj => hint i j hj)]
  have e1 : ∀ i : Fin N, ∫ X : Whole.EucConfig d N, ∑ j ∈ Finset.univ.erase i, c₀ * ‖X i - X j‖ ^ (-s)
      ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≤ ((N : ℝ) - 1) * (c₀ * sb1Cs d s Cρ) := by
    intro i
    rw [integral_finset_sum _ (fun j hj => hint i j hj)]
    calc ∑ j ∈ Finset.univ.erase i, ∫ X : Whole.EucConfig d N, c₀ * ‖X i - X j‖ ^ (-s)
          ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)
        ≤ ∑ _j ∈ Finset.univ.erase i, c₀ * sb1Cs d s Cρ := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (sb1_pairX_int hd hs0 hsd R (Finset.ne_of_mem_erase hj).symm).2 hc₀
      _ = ((N : ℝ) - 1) * (c₀ * sb1Cs d s Cρ) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp [Nat.cast_sub hN]
  have e2 : ∑ i : Fin N, ∫ X : Whole.EucConfig d N, ∑ j ∈ Finset.univ.erase i, c₀ * ‖X i - X j‖ ^ (-s)
      ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) ≤ N * (((N : ℝ) - 1) * (c₀ * sb1Cs d s Cρ)) := by
    calc _ ≤ ∑ _i : Fin N, ((N : ℝ) - 1) * (c₀ * sb1Cs d s Cρ) := Finset.sum_le_sum fun i _ => e1 i
      _ = _ := by simp
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hc0 : 0 ≤ c₀ * sb1Cs d s Cρ := mul_nonneg hc₀ hCs
  have hn0 : (0 : ℝ) < N := by linarith
  have h3 : 1 / (2 * (N : ℝ) ^ 2) * (N * (((N : ℝ) - 1) * (c₀ * sb1Cs d s Cρ))) ≤ (1 / 2) * (c₀ * sb1Cs d s Cρ) := by
    have : 1 / (2 * (N : ℝ) ^ 2) * (N * (((N : ℝ) - 1) * (c₀ * sb1Cs d s Cρ))) =
        ((N - 1) / (2 * N)) * (c₀ * sb1Cs d s Cρ) := by field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ hc0
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2))
  linarith

theorem sb1_FF_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hkn : ∀ n, Sb1KerU d s (kn n))
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1) {β : ℝ}
    (X : Whole.EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    Tendsto (fun n => sb1FF (kn n) β N ρ0 X) atTop (𝓝 (sb1FF k β N ρ0 X)) := by
  unfold sb1FF
  exact (Real.continuous_exp.tendsto _).comp ((sb1_En_tendsto hd hs0 hsd hkn hconv R X hX).const_mul (-β * N))

theorem sb1_Phi_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hkn : ∀ n, Sb1KerU d s (kn n)) (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z)))
    (R : Sb1Rho ρ0 Cρ M1) (hc₀ : 0 ≤ c₀)
    (hb : ∀ n x y, |hn n x y| ≤ c₀ * ‖x - y‖ ^ (-s))
    (hm : ∀ n, Measurable (fun p : Euc d × Euc d => hn n p.1 p.2))
    (hconvh : ∀ x y, x ≠ y → Tendsto (fun n => hn n x y) atTop (𝓝 (h x y))) :
    Tendsto (fun n => ∫ X : Whole.EucConfig d N, sb1FF (kn n) β N ρ0 X *
        Whole.pairEnergy (hn n) X (Whole.withDensityReal ρ0)
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)) atTop
      (𝓝 (∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X * Whole.pairEnergy h X (Whole.withDensityReal ρ0)
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0))) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hae := HRS.MS.Wr.ae_injective_pi_Euc (N := N) (HRS.MS.Wr.wr12_atomless hd ρ0)
  obtain ⟨hBi, -⟩ := sb1_Bmaj_int hd hs0 hsd R hc₀ hN
  refine tendsto_integral_of_dominated_convergence
    (fun X => sb1CwR d s Cρ M1 β N * sb1Bmaj d s c₀ (sb1Cs d s Cρ) N X)
    (fun n => ((sb1_FF_meas (hkn n) R β).mul (sb1_pairE_meas R (hm n))).aestronglyMeasurable)
    (hBi.const_mul _) (fun n => Eventually.of_forall fun X => ?_) ?_
  · unfold sb1FF
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (sb1_E_le hd hs0 hsd hN hβ (hkn n) R X) (sb1_pairE_abs_le hd hs0 hsd R hc₀ (hb n) hN X)
      (abs_nonneg _) (Real.exp_pos _).le
  · filter_upwards [hae] with X hX
    exact (sb1_FF_tendsto hd hs0 hsd hkn hconv R X hX).mul
      (sb1_pairE_tendsto hd hs0 hsd R hc₀ hb hm hconvh X hX)

theorem sb1_Phi_abs_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    {k' : Euc d → ℝ} (hk' : Sb1KerU d s k') (R : Sb1Rho ρ0 Cρ M1) (hc₀ : 0 ≤ c₀)
    {h' : Euc d → Euc d → ℝ} (hb : ∀ x y, |h' x y| ≤ c₀ * ‖x - y‖ ^ (-s)) :
    |∫ X : Whole.EucConfig d N, sb1FF k' β N ρ0 X * Whole.pairEnergy h' X (Whole.withDensityReal ρ0)
        ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0)| ≤
      sb1CwR d s Cρ M1 β N * (2 * (c₀ * sb1Cs d s Cρ)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  obtain ⟨hBi, hBb⟩ := sb1_Bmaj_int hd hs0 hsd R hc₀ hN
  have h1 := norm_integral_le_of_norm_le (hBi.const_mul (sb1CwR d s Cρ M1 β N))
    (f := fun X : Whole.EucConfig d N => sb1FF k' β N ρ0 X * Whole.pairEnergy h' X (Whole.withDensityReal ρ0))
    (Eventually.of_forall fun X => by
      unfold sb1FF
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (sb1_E_le hd hs0 hsd hN hβ hk' R X) (sb1_pairE_abs_le hd hs0 hsd R hc₀ hb hN X)
        (abs_nonneg _) (Real.exp_pos _).le)
  rw [Real.norm_eq_abs, integral_const_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left hBb (Real.exp_pos _).le)

end Conv

end HRS.MS.MfeConf
