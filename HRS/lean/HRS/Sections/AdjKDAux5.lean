import HRS.Sections.AdjKDAux4

/-!
# ADJKD, part 5: the deterministic `E_m`-valued convolution estimate (ingredient of packet B2)

`adjkdEps m j` is the unit vector of `E_m` with Fourier coefficient `δ_{ij}`.  For a strongly continuous
evolution `V^{t,r}` on `E_m` with `‖V^{t,r}‖ ≤ C_V` and real functions `y_j(r)` with
`∑_j ⟨j⟩^{-m} ∫|y_j| < ∞`, the coordinate series `Y_k(r) = ∑_j ⟨V^{t,r} ε_j, e_k⟩ y_j(r)` are integrable and
`‖(∫_0^t Y_k dr)_k‖_{E_m} ≤ C_V ∑_j ⟨j⟩^{-m} ∫|y_j|` (`adjkd_abs_convolution`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

/-- The unit vector of `E_m` with `F̂(i) = δ_{ij}`. -/
def adjkdEps (m : ℝ) (j : NonzeroLattice d) : NegSobolev d m :=
  (lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 j (Lattice.jp j.1 ^ (-m)) :
    lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem adjkdEps_coord (m : ℝ) (j i : NonzeroLattice d) :
    NegSobolev.coord (adjkdEps m j) i = if i = j then Lattice.jp j.1 ^ (-m) else 0 := by
  unfold NegSobolev.coord adjkdEps
  by_cases h : i = j
  · subst h
    simp [lp.single_apply_self]
  · rw [lp.single_apply_ne _ _ _ h]
    simp [h]

theorem adjkdEps_fourier (m : ℝ) (j i : NonzeroLattice d) :
    NegSobolev.fourierCoeff (adjkdEps m j) i = if i = j then 1 else 0 := by
  unfold NegSobolev.fourierCoeff
  rw [adjkdEps_coord]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    rw [← Real.rpow_add (Torus.jp_pos _)]
    simp
  · simp [h]

theorem adjkdEps_norm (m : ℝ) (j : NonzeroLattice d) : ‖adjkdEps m j‖ = Lattice.jp j.1 ^ (-m) := by
  have h := lp.norm_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num) j
    (Lattice.jp j.1 ^ (-m))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)] at h
  exact h

/-- The coordinate `F ↦ F̂(k)` as a continuous linear functional. -/
def adjkdCoord (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.fourierCoeff F k
      map_add' := fun F G => by
        unfold NegSobolev.fourierCoeff NegSobolev.coord
        rw [← mul_add]; rfl
      map_smul' := fun r F => by
        show Lattice.jp k.1 ^ m * (r * NegSobolev.coord F k) =
          r * (Lattice.jp k.1 ^ m * NegSobolev.coord F k)
        ring }
    (Lattice.jp k.1 ^ m) (fun F => by
      show |Lattice.jp k.1 ^ m * NegSobolev.coord F k| ≤ _
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le
      exact lp.norm_apply_le_norm (by norm_num) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) k)

theorem adjkdCoord_apply (m : ℝ) (k : NonzeroLattice d) (F : NegSobolev d m) :
    adjkdCoord m k F = NegSobolev.fourierCoeff F k := rfl

theorem adjkd_abs_fourierCoeff_le (m : ℝ) (k : NonzeroLattice d) (F : NegSobolev d m) :
    |NegSobolev.fourierCoeff F k| ≤ Lattice.jp k.1 ^ m * ‖F‖ := by
  unfold NegSobolev.fourierCoeff
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le
  exact lp.norm_apply_le_norm (by norm_num) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) k

/-! ### Duality: the coefficients of the propagator are the coordinates of `V ε_j` -/

theorem adjkd_dual_coeff {m : ℝ} {D : DynData d} {ρ : ℝ → Torus d → ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution D ρ m Vev)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (j k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k =
      Torus.funRealCoeff (propagator D ρ r t (Torus.realMode k)) j := by
  classical
  rw [← adjkd_eval_realMode, hdual r t hr hrt _ _ (adjkd_isSmooth_realMode k)]
  unfold NegSobolev.eval
  rw [tsum_eq_single j]
  · rw [adjkdEps_fourier]; simp
  · intro i hi
    rw [adjkdEps_fourier, if_neg hi, zero_mul]

/-! ### A generic integrability lemma for series -/

theorem adjkd_integrable_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    [Countable ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ι → α → E) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hs : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ ≠ ⊤) : Integrable (fun a => ∑' i, F i a) μ := by
  have hm : ∀ i, AEMeasurable (fun a => ‖F i a‖ₑ) μ := fun i => (hF i).enorm
  have hlt : ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ ≠ ⊤ := by rw [lintegral_tsum hm]; exact hs
  have hae : ∀ᵐ a ∂μ, ∑' i, ‖F i a‖ₑ < ⊤ := ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlt
  have hsum : ∀ᵐ a ∂μ, Summable fun i => F i a := by
    filter_upwards [hae] with a ha
    refine Summable.of_norm ?_
    have : ∑' i, (‖F i a‖₊ : ℝ≥0∞) ≠ ⊤ := by
      simpa [enorm] using ha.ne
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset ι)))
      (f := fun (S : Finset ι) a => ∑ i ∈ S, F i a) (fun S => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hF i
    · filter_upwards [hsum] with a ha using ha.hasSum
  · unfold HasFiniteIntegral
    calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ :=
          lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ < ⊤ := hlt.lt_top


/-! ### The deterministic convolution estimate -/

theorem adjkd_abs_convolution {m t CV : ℝ} (ht : 0 ≤ t)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hcont : ∀ z, ContinuousOn (fun r => Vev t r z) (Set.Icc 0 t))
    (hbd : ∀ r ∈ Set.Icc 0 t, ‖Vev t r‖ ≤ CV)
    (y : NonzeroLattice d → ℝ → ℝ) (hy : ∀ j, AEMeasurable (y j) (volume.restrict (Set.Ioc 0 t)))
    (hI : ∑' j, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) * ∫⁻ r in Set.Ioc 0 t, ‖y j r‖ₑ ≠ ⊤) :
    (∀ k : NonzeroLattice d, IntegrableOn (fun r => ∑' j : NonzeroLattice d,
        NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r) (Set.Ioc 0 t)) ∧
    (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
        (∫ r in Set.Ioc 0 t, ∑' j : NonzeroLattice d,
          NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r) ^ 2)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal CV * ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
        ∫⁻ r in Set.Ioc 0 t, ‖y j r‖ₑ := by
  classical
  set μt : Measure ℝ := volume.restrict (Set.Ioc 0 t) with hμt
  have hCV : 0 ≤ CV := le_trans (norm_nonneg _) (hbd 0 ⟨le_rfl, ht⟩)
  set wj : NonzeroLattice d → ℝ := fun j => Lattice.jp j.1 ^ (-m) with hwj
  have hwpos : ∀ j, 0 < wj j := fun j => Real.rpow_pos_of_pos (Torus.jp_pos _) _
  set Ij : NonzeroLattice d → ℝ≥0∞ := fun j => ∫⁻ r, ‖y j r‖ₑ ∂μt with hIj
  have hIfin : ∀ j, Ij j ≠ ⊤ := by
    intro j h
    have h1 : ENNReal.ofReal (wj j) * Ij j ≠ ⊤ := ne_top_of_le_ne_top hI
      (ENNReal.le_tsum (f := fun j => ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
        ∫⁻ r in Set.Ioc 0 t, ‖y j r‖ₑ) j)
    apply h1
    rw [h]
    exact ENNReal.mul_top (by simpa using hwpos j)
  have hyint : ∀ j, Integrable (y j) μt := fun j => ⟨(hy j).aestronglyMeasurable, (hIfin j).lt_top⟩
  have hIr : ∀ j, ENNReal.ofReal (∫ r, ‖y j r‖ ∂μt) = Ij j := fun j =>
    ofReal_integral_norm_eq_lintegral_enorm (hyint j)
  set Jj : NonzeroLattice d → ℝ := fun j => ∫ r, ‖y j r‖ ∂μt with hJj
  have hJ0 : ∀ j, 0 ≤ Jj j := fun j => integral_nonneg fun r => norm_nonneg _
  have hmeasIoc : MeasurableSet (Set.Ioc (0 : ℝ) t) := measurableSet_Ioc
  -- measurability and bounds of `r ↦ V^{t,r} ε_j`
  have hu_meas : ∀ z : NegSobolev d m, AEStronglyMeasurable (fun r => Vev t r z) μt := fun z =>
    ((hcont z).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable hmeasIoc
  have hmem : ∀ᵐ r ∂μt, r ∈ Set.Icc (0 : ℝ) t := by
    filter_upwards [ae_restrict_mem hmeasIoc] with r hr using ⟨hr.1.le, hr.2⟩
  have hu_bd : ∀ (j : NonzeroLattice d), ∀ᵐ r ∂μt, ‖Vev t r (adjkdEps m j)‖ ≤ CV * wj j := by
    intro j
    filter_upwards [hmem] with r hr
    calc ‖Vev t r (adjkdEps m j)‖ ≤ ‖Vev t r‖ * ‖adjkdEps m j‖ := (Vev t r).le_opNorm _
      _ ≤ CV * wj j := by
        rw [adjkdEps_norm]
        exact mul_le_mul_of_nonneg_right (hbd r hr) (hwpos j).le
  -- the vectors `w_j = ∫ y_j V ε_j`
  have hf_int : ∀ j, Integrable (fun r => y j r • Vev t r (adjkdEps m j)) μt := by
    intro j
    refine Integrable.mono' ((hyint j).norm.mul_const (CV * wj j))
      ((hy j).aestronglyMeasurable.smul (hu_meas _)) ?_
    filter_upwards [hu_bd j] with r hr
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hr (norm_nonneg _) |>.trans_eq (by ring)
  set wvec : NonzeroLattice d → NegSobolev d m :=
    fun j => ∫ r, y j r • Vev t r (adjkdEps m j) ∂μt with hwvec
  have hw_norm : ∀ j, ‖wvec j‖ ≤ (CV * wj j) * Jj j := by
    intro j
    calc ‖wvec j‖ ≤ ∫ r, ‖y j r‖ * (CV * wj j) ∂μt := by
          refine norm_integral_le_of_norm_le ((hyint j).norm.mul_const _) ?_
          filter_upwards [hu_bd j] with r hr
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ = (CV * wj j) * Jj j := by rw [integral_mul_const]; ring
  have hsumJ : Summable fun j => wj j * Jj j := by
    have h1 := ENNReal.summable_toReal hI
    refine h1.congr fun j => ?_
    have e : (∫⁻ (r : ℝ), ‖y j r‖ₑ ∂μt) = Ij j := rfl
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwpos j).le, e, ← hIr j,
      ENNReal.toReal_ofReal (hJ0 j)]
  have hsumB : Summable fun j => (CV * wj j) * Jj j :=
    (hsumJ.mul_left CV).congr fun j => by ring
  have hsum_w : Summable fun j => ‖wvec j‖ := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hw_norm hsumB
  have hsum_wv : Summable wvec := hsum_w.of_norm
  set Gv : NegSobolev d m := ∑' j, wvec j with hGv
  have hGnorm : ‖Gv‖ ≤ ∑' j, (CV * wj j) * Jj j :=
    (norm_tsum_le_tsum_norm hsum_w).trans (hsum_w.tsum_le_tsum hw_norm hsumB)
  -- coordinates of `Gv`
  have hcoord : ∀ k : NonzeroLattice d, NegSobolev.fourierCoeff Gv k =
      ∫ r, ∑' j, NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r ∂μt ∧
      Integrable (fun r => ∑' j, NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r) μt := by
    intro k
    set a : NonzeroLattice d → ℝ → ℝ :=
      fun j r => NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k with ha
    have ha_meas : ∀ j, AEStronglyMeasurable (fun r => a j r * y j r) μt := by
      intro j
      have : AEStronglyMeasurable (fun r => a j r) μt :=
        ((adjkdCoord m k).continuous.comp_continuousOn (hcont (adjkdEps m j))
          |>.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable hmeasIoc
      exact this.mul (hy j).aestronglyMeasurable
    have ha_bd : ∀ j, ∀ᵐ r ∂μt, |a j r| ≤ Lattice.jp k.1 ^ m * (CV * wj j) := by
      intro j
      filter_upwards [hu_bd j] with r hr
      exact (adjkd_abs_fourierCoeff_le m k _).trans (mul_le_mul_of_nonneg_left hr
        (Real.rpow_nonneg (Torus.jp_pos _).le _))
    have hfin : ∑' j, ∫⁻ r, ‖a j r * y j r‖ₑ ∂μt ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Lattice.jp k.1 ^ m * CV) *
        ∑' j, ENNReal.ofReal (wj j) * Ij j) ?_ ?_
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI
      · rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun j => ?_
        calc ∫⁻ r, ‖a j r * y j r‖ₑ ∂μt
            ≤ ∫⁻ r, ENNReal.ofReal (Lattice.jp k.1 ^ m * (CV * wj j)) * ‖y j r‖ₑ ∂μt := by
              refine lintegral_mono_ae ?_
              filter_upwards [ha_bd j] with r hr
              rw [enorm_mul]
              refine mul_le_mul' ?_ le_rfl
              rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
              exact ENNReal.ofReal_le_ofReal hr
          _ = ENNReal.ofReal (Lattice.jp k.1 ^ m * (CV * wj j)) * Ij j := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ = ENNReal.ofReal (Lattice.jp k.1 ^ m * CV) * (ENNReal.ofReal (wj j) * Ij j) := by
              rw [show Lattice.jp k.1 ^ m * (CV * wj j) = (Lattice.jp k.1 ^ m * CV) * wj j by ring,
                ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) hCV), mul_assoc]
    refine ⟨?_, adjkd_integrable_tsum (fun j r => a j r * y j r) ha_meas hfin⟩
    have h1 : NegSobolev.fourierCoeff Gv k = ∑' j, NegSobolev.fourierCoeff (wvec j) k :=
      (adjkdCoord m k).map_tsum hsum_wv
    have h2 : ∀ j, NegSobolev.fourierCoeff (wvec j) k = ∫ r, a j r * y j r ∂μt := by
      intro j
      show adjkdCoord m k (∫ r, y j r • Vev t r (adjkdEps m j) ∂μt) = _
      rw [← ContinuousLinearMap.integral_comp_comm (adjkdCoord m k) (hf_int j)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only [map_smul, smul_eq_mul, adjkdCoord_apply]
      ring
    rw [h1, integral_tsum ha_meas hfin]
    exact tsum_congr h2
  refine ⟨fun k => (hcoord k).2, ?_⟩
  -- the norm of `Gv`
  obtain ⟨hcs, hGn⟩ := NegSobolev.coord_sq Gv
  have hterm : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * m) *
      (∫ r, ∑' j, NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r ∂μt) ^ 2 =
        NegSobolev.coord Gv k ^ 2 := by
    intro k
    have h1 : NegSobolev.coord Gv k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff Gv k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
      simp
    rw [h1, (hcoord k).1, mul_pow, Torus.jp_rpow_sq]
    congr 2
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hcs, ← hGn]
  have hpow : (ENNReal.ofReal (‖Gv‖ ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal ‖Gv‖ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hpow]
  refine (ENNReal.ofReal_le_ofReal hGnorm).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (mul_nonneg hCV (hwpos j).le) (hJ0 j)) hsumB,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hCV (hwpos j).le), ENNReal.ofReal_mul hCV, hIr j]
  ring

end HRS.AdjK
