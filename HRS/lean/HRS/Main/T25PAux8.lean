import HRS.Main.T25PAux7

/-!
# T25P, part 8: `‖Ψ_a‖_{L²(P)} ≤ C J_N/√N`, uniformly in the window start
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.MovLog

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_alg (x m : ℝ) (hx : 0 < x) :
    (x ^ (-m)) ^ 2 / x ^ (-(m - 2)) * (x ^ 2) ^ 2 = x ^ (-(m - 2)) := by
  have h1 : (x ^ (-m)) ^ 2 = x ^ (-m * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have h2 : (x ^ 2) ^ 2 = x ^ (4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  rw [h1, h2, ← Real.rpow_sub hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem t25p_Psi_L2 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) {cr : ℝ} (hcr : 0 < cr) {T : ℝ} (hT : 0 < T) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        (∫⁻ ω, (t25p_Psi d s ρ m cr a T X ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal
          ((CΨ * logMomentScale d s N p₀ (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) / Real.sqrt N) := by
  classical
  obtain ⟨c2, hc20, hc2⟩ := t25p_mode_L2 hd htr p₀ hp₀
  have hSb : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-(m - 2)) := by
    have := summable_jp_rpow (d := d) ((m - 2) / 2) (by linarith)
    refine this.congr fun j => ?_
    congr 1
    ring
  set Sb : ℝ := ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (-(m - 2)) with hSbdef
  have hSb0 : 0 ≤ Sb := tsum_nonneg fun j => Real.rpow_nonneg (Torus.jp_pos _).le _
  set W₀ : ℝ := 1 / cr + T with hW₀
  have hW₀0 : 0 ≤ W₀ := by positivity
  refine ⟨Sb * W₀ * c2, by positivity, ?_⟩
  intro N hN a ha Ω _ P _ X₀ W X hP hfilt hac hfin
  obtain ⟨ℱ, W', hF⟩ := hfilt
  set J : ℝ := logMomentScale d s N p₀ (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hJ
  have hJ1 : 1 ≤ J := t25p_J_ge_one hd htr hN P hP hp₀ hac hfin
  have hJ0 : 0 ≤ J := by linarith
  have hNpos : 0 < N := by omega
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  have hT' : 0 < a + T := by linarith
  set w := t25p_w cr a with hwdef
  have hwm : Measurable w := (t25p_w_cont cr a).measurable
  have hw0 : ∀ r, 0 ≤ w r := fun r => (t25p_w_pos cr a r).le
  have hAE := fun j => t25p_y_aemeas hd htr hT' P hF.progressive j
  -- time-integrated mode functionals
  set Fj : NonzeroLattice d → Ω → ℝ≥0∞ := fun j ω =>
    ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (w r) * ‖t25p_y d s ρ X j r ω‖ₑ with hFj
  have hjointm : ∀ j, AEMeasurable (fun p : ℝ × Ω => ENNReal.ofReal (w p.1) * ‖t25p_y d s ρ X j p.1 p.2‖ₑ)
      ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) := fun j =>
    (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).aemeasurable.mul (hAE j).1.enorm
  have hFjm : ∀ j, AEMeasurable (Fj j) P := fun j => (hjointm j).lintegral_prod_left'
  have hjointm2 : ∀ j, AEMeasurable
      (fun p : ℝ × Ω => ENNReal.ofReal (w p.1) * ‖t25p_y d s ρ X j p.1 p.2‖ₑ ^ 2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) := fun j =>
    (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).aemeasurable.mul
      ((hAE j).1.enorm.pow_const 2)
  -- Step A: Cauchy-Schwarz in time
  have hWint : ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (w r) ≤ ENNReal.ofReal W₀ :=
    t25p_w_lintegral_le hcr ha hT.le
  have hA : ∀ j ω, Fj j ω ^ 2 ≤ ENNReal.ofReal W₀ *
      ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (w r) * ‖t25p_y d s ρ X j r ω‖ₑ ^ 2 := by
    intro j ω
    have := t25p_cs_time (volume.restrict (Set.Ioc (0 : ℝ) (a + T))) hwm hw0 ((hAE j).2 ω)
    exact this.trans (mul_le_mul' hWint le_rfl)
  -- Step A': moments of `F_j`
  have hEF : ∀ j, ∫⁻ ω, Fj j ω ^ 2 ∂P ≤ ENNReal.ofReal (W₀ * W₀ * ((c2 * Lattice.jp j.1 ^ 2 * J / Real.sqrt N) ^ 2)) := by
    intro j
    have hy2 : ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∫⁻ ω, ‖t25p_y d s ρ X j r ω‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal ((c2 * Lattice.jp j.1 ^ 2 * J) / Real.sqrt N) ^ 2 := fun r hr =>
      hc2 N hN (a + T) hT' P X₀ W X hP ⟨ℱ, W', hF⟩ hac hfin j r hr
    calc ∫⁻ ω, Fj j ω ^ 2 ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal W₀ *
            ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (w r) * ‖t25p_y d s ρ X j r ω‖ₑ ^ 2) ∂P :=
          lintegral_mono fun ω => hA j ω
      _ = ENNReal.ofReal W₀ * ∫⁻ ω, (∫⁻ r in Set.Ioc 0 (a + T),
            ENNReal.ofReal (w r) * ‖t25p_y d s ρ X j r ω‖ₑ ^ 2) ∂P := by
          rw [lintegral_const_mul'' _ ((hjointm2 j).lintegral_prod_left')]
      _ = ENNReal.ofReal W₀ * ∫⁻ r in Set.Ioc 0 (a + T), (∫⁻ ω,
            ENNReal.ofReal (w r) * ‖t25p_y d s ρ X j r ω‖ₑ ^ 2 ∂P) := by
          rw [← lintegral_lintegral_swap (hjointm2 j)]
      _ ≤ ENNReal.ofReal W₀ * ∫⁻ r in Set.Ioc 0 (a + T),
            ENNReal.ofReal (w r) * ENNReal.ofReal ((c2 * Lattice.jp j.1 ^ 2 * J) / Real.sqrt N) ^ 2 := by
          refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul' le_rfl (hy2 r ⟨hr.1.le, hr.2⟩)
      _ = ENNReal.ofReal W₀ * ((∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (w r)) *
            ENNReal.ofReal ((c2 * Lattice.jp j.1 ^ 2 * J) / Real.sqrt N) ^ 2) := by
          rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      _ ≤ ENNReal.ofReal W₀ * (ENNReal.ofReal W₀ *
            ENNReal.ofReal ((c2 * Lattice.jp j.1 ^ 2 * J) / Real.sqrt N) ^ 2) :=
          mul_le_mul' le_rfl (mul_le_mul' hWint le_rfl)
      _ = ENNReal.ofReal (W₀ * W₀ * ((c2 * Lattice.jp j.1 ^ 2 * J / Real.sqrt N) ^ 2)) := by
          have hb : 0 ≤ (c2 * Lattice.jp j.1 ^ 2 * J) / Real.sqrt N := by positivity
          rw [← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul hW₀0, ← ENNReal.ofReal_mul hW₀0]
          congr 1
          ring
  -- Step B: Cauchy-Schwarz over the modes
  set bj : NonzeroLattice d → ℝ := fun j => Lattice.jp j.1 ^ (-(m - 2)) with hbj
  have hbpos : ∀ j, 0 < bj j := fun j => Real.rpow_pos_of_pos (Torus.jp_pos _) _
  set aj : NonzeroLattice d → ℝ := fun j => Lattice.jp j.1 ^ (-m) with haj
  have hapos : ∀ j, 0 < aj j := fun j => Real.rpow_pos_of_pos (Torus.jp_pos _) _
  have hPsi : ∀ ω, t25p_Psi d s ρ m cr a T X ω = ∑' j : NonzeroLattice d,
      ENNReal.ofReal (Real.sqrt (bj j)) * (ENNReal.ofReal (aj j / Real.sqrt (bj j)) * Fj j ω) := by
    intro ω
    unfold t25p_Psi
    refine tsum_congr fun j => ?_
    have hsb : 0 < Real.sqrt (bj j) := Real.sqrt_pos.2 (hbpos j)
    rw [← mul_assoc, ← ENNReal.ofReal_mul hsb.le]
    have : Real.sqrt (bj j) * (aj j / Real.sqrt (bj j)) = aj j := by field_simp
    rw [this]
  have hPsi2 : ∀ ω, (t25p_Psi d s ρ m cr a T X ω) ^ 2 ≤ ENNReal.ofReal Sb *
      ∑' j : NonzeroLattice d, ENNReal.ofReal ((aj j / Real.sqrt (bj j)) ^ 2) * Fj j ω ^ 2 := by
    intro ω
    rw [hPsi ω]
    refine (t25p_cs_tsum _ _).trans ?_
    refine mul_le_mul' (le_of_eq ?_) (le_of_eq ?_)
    · rw [hSbdef, ENNReal.ofReal_tsum_of_nonneg (fun j => (hbpos j).le) hSb]
      refine tsum_congr fun j => ?_
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hbpos j).le]
    · refine tsum_congr fun j => ?_
      rw [mul_pow, ← ENNReal.ofReal_pow (by have := hapos j; have := hbpos j; positivity)]
  -- Step C: the expectation
  have hmeasj : ∀ j, AEMeasurable (fun ω => ENNReal.ofReal ((aj j / Real.sqrt (bj j)) ^ 2) * Fj j ω ^ 2) P :=
    fun j => (hFjm j).pow_const 2 |>.const_mul _
  have hEPsi : ∫⁻ ω, (t25p_Psi d s ρ m cr a T X ω) ^ 2 ∂P ≤
      ENNReal.ofReal (Sb * Sb * (W₀ * W₀ * (c2 * c2 * J * J / N))) := by
    calc ∫⁻ ω, (t25p_Psi d s ρ m cr a T X ω) ^ 2 ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal Sb *
            ∑' j : NonzeroLattice d, ENNReal.ofReal ((aj j / Real.sqrt (bj j)) ^ 2) * Fj j ω ^ 2 ∂P :=
          lintegral_mono fun ω => hPsi2 ω
      _ = ENNReal.ofReal Sb * ∑' j : NonzeroLattice d,
            ∫⁻ ω, ENNReal.ofReal ((aj j / Real.sqrt (bj j)) ^ 2) * Fj j ω ^ 2 ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeasj]
      _ ≤ ENNReal.ofReal Sb * ∑' j : NonzeroLattice d, ENNReal.ofReal ((aj j / Real.sqrt (bj j)) ^ 2) *
            ENNReal.ofReal (W₀ * W₀ * ((c2 * Lattice.jp j.1 ^ 2 * J / Real.sqrt N) ^ 2)) := by
          refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun j => ?_)
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul' le_rfl (hEF j)
      _ = ENNReal.ofReal Sb * ∑' j : NonzeroLattice d,
            ENNReal.ofReal (bj j * (W₀ * W₀ * (c2 * c2 * J * J / N))) := by
          congr 1
          refine tsum_congr fun j => ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 1
          have hx := (Torus.jp_pos j.1)
          have hid := t25p_alg (Lattice.jp j.1) m hx
          have hs2 : (Real.sqrt (bj j)) ^ 2 = bj j := Real.sq_sqrt (hbpos j).le
          have hsN : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
          have e1 : (aj j / Real.sqrt (bj j)) ^ 2 = (aj j) ^ 2 / bj j := by
            rw [div_pow, hs2]
          rw [e1, div_pow, hsN, mul_pow, mul_pow]
          have hq : (aj j) ^ 2 / bj j * (Lattice.jp j.1 ^ 2) ^ 2 = bj j := by
            simpa only [haj, hbj] using hid
          calc (aj j) ^ 2 / bj j * (W₀ * W₀ * (c2 ^ 2 * (Lattice.jp j.1 ^ 2) ^ 2 * J ^ 2 / (N : ℝ)))
              = ((aj j) ^ 2 / bj j * (Lattice.jp j.1 ^ 2) ^ 2) * (W₀ * W₀ * (c2 ^ 2 * J ^ 2 / (N : ℝ))) := by
                ring
            _ = _ := by rw [hq]; ring
      _ = ENNReal.ofReal (Sb * Sb * (W₀ * W₀ * (c2 * c2 * J * J / N))) := by
          have hnn : ∀ j, 0 ≤ bj j * (W₀ * W₀ * (c2 * c2 * J * J / N)) := fun j => by
            have := hbpos j
            positivity
          have hsum : ∑' j : NonzeroLattice d, bj j * (W₀ * W₀ * (c2 * c2 * J * J / N)) =
              Sb * (W₀ * W₀ * (c2 * c2 * J * J / N)) := by
            rw [tsum_mul_right]
          rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hSb.mul_right _), hsum, ← ENNReal.ofReal_mul hSb0]
          congr 1
          ring
  -- the square root
  calc (∫⁻ ω, (t25p_Psi d s ρ m cr a T X ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Sb * Sb * (W₀ * W₀ * (c2 * c2 * J * J / N)))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hEPsi (by norm_num)
    _ = ENNReal.ofReal ((Sb * W₀ * c2 * J) / Real.sqrt N) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        have hsN : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
        have h1 : Sb * Sb * (W₀ * W₀ * (c2 * c2 * J * J / N)) = ((Sb * W₀ * c2 * J) / Real.sqrt N) ^ 2 := by
          rw [div_pow, hsN]
          ring
        rw [h1, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    _ = ENNReal.ofReal ((Sb * W₀ * c2 * J) / Real.sqrt N) := rfl

end HRS.T25P
