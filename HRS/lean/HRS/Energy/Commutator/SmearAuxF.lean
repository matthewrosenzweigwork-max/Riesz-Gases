import HRS.Energy.Commutator.SmearAuxE

/-!
# Auxiliary lemmas for `Smear.lean` (packet CM-S2), part F: uniform bound for the slice kernels `sliceG d l`

`|sliceG d l w| ≤ e * sliceGfull d 1 w + 1 + Kc d` for all `l ≥ 0`, `w ≠ 0` (domination for the
limit `l → 0⁺` in the Coulomb slice), and `sliceG d l w → sliceG d 0 w`.
-/
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators Pointwise
noncomputable section
namespace HRS.Commutator.SmearAux
variable {d : ℕ}

theorem one_add_psiFn_nonneg (w : Torus d) {t : ℝ} (ht : 0 < t) :
    0 ≤ 1 + psiFn w (4 * Real.pi ^ 2 * t) := by
  have hbox := centeredRep_mem_Box w
  have hbp : KernelAux.boxPt (fun i => KernelGrad.centeredRep w i) = w := by
    conv_rhs => rw [← KernelGrad.mk_centeredRep w]
    rfl
  have h := SliceAux.heat_pointwise (fun i => KernelGrad.centeredRep w i) 0 ht
  rw [hbp] at h
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at h
  rw [h]
  exact tsum_nonneg fun m => SliceAux.heatTerm_nonneg _ m 0 ht

theorem one_le_enorm {k : Lattice d} (hk : k ≠ 0) : 1 ≤ Lattice.enorm k := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  have h1 : (1:ℝ) ≤ |(k i : ℝ)| := by
    have : (1:ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  unfold Lattice.enorm
  refine h1.trans ?_
  have := abs_apply_le_norm (Lattice.toEuc k) i
  simpa [Lattice.toEuc] using this

/-- the constant `Θ = ∑_{k ≠ 0} e^{-|k|²}` -/
def thetaC (d : ℕ) : ℝ := ∑' k : Lattice d, if k = 0 then 0 else Real.exp (-1 * Lattice.enorm k ^ 2)

theorem summable_thetaC (d : ℕ) : Summable (fun k : Lattice d => if k = 0 then (0:ℝ) else Real.exp (-1 * Lattice.enorm k ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_gauss_lattice d 1 one_pos)
  · split_ifs <;> positivity
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl

theorem abs_psiFn_le (x : Torus d) {u : ℝ} (hu : 1 ≤ u) :
    |psiFn x u| ≤ thetaC d * Real.exp (1 - u) := by
  have hu0 : 0 < u := by linarith
  unfold psiFn thetaC
  rw [← tsum_mul_right, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (psi_summable x hu0).norm).trans ?_
  · refine Summable.tsum_le_tsum (fun k => ?_) (psi_summable x hu0).norm ((summable_thetaC d).mul_right _)
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : 1 ≤ Lattice.enorm k ^ 2 := by
        have := one_le_enorm hk; nlinarith
      have h2 : Real.exp (-u * Lattice.enorm k ^ 2) ≤ Real.exp (-1 * Lattice.enorm k ^ 2) * Real.exp (1 - u) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      calc Real.exp (-u * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
          ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by
            gcongr; exact abs_cosMode_le k x
        _ ≤ _ := by rw [mul_one]; exact h2


theorem integrableOn_psi0 {w : Torus d} (hw : w ≠ 0) :
    IntegrableOn (fun t : ℝ => psiFn w (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
  have := SliceAux.integrableOn_slice_psi (d := d) (le_refl (0:ℝ)) hw
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp

theorem sliceG_zero_eq (w : Torus d) :
    sliceG d 0 w = ∫ t in Ioi (0 : ℝ), psiFn w (4 * Real.pi ^ 2 * t) := by
  unfold sliceG; simp

theorem sliceG_tendsto {w : Torus d} (hw : w ≠ 0) :
    Tendsto (fun l : ℝ => sliceG d l w) (𝓝[>] 0) (𝓝 (sliceG d 0 w)) := by
  rw [sliceG_zero_eq]
  unfold sliceG
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖psiFn w (4 * Real.pi ^ 2 * t)‖) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with l hl
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
    refine (psi_continuousOn _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 0 < 4 * Real.pi ^ 2 * t
    positivity
  · filter_upwards [self_mem_nhdsWithin] with l hl
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have hl' : (0:ℝ) < l := hl
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-l * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) < t := ht; nlinarith
    exact mul_le_of_le_one_left (norm_nonneg _) this
  · exact (integrableOn_psi0 hw).norm
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have : Tendsto (fun l : ℝ => Real.exp (-l * t)) (𝓝[>] 0) (𝓝 1) := by
      have h0 : Tendsto (fun l : ℝ => -l * t) (𝓝 0) (𝓝 0) :=
        ((continuous_neg.mul continuous_const : Continuous fun l : ℝ => -l * t).tendsto' 0 0 (by simp))
      have h := (Real.continuous_exp.tendsto 0).comp h0
      simpa [Function.comp_def] using h.mono_left nhdsWithin_le_nhds
    simpa using this.mul_const (psiFn w (4 * Real.pi ^ 2 * t))


theorem integrableOn_exp_P {l : ℝ} (hl : 0 < l) {w : Torus d} (hw : w ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t))) (Ioi 0) := by
  have hI := SliceAux.integrableOn_slice_psi hl.le hw
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this
  have := hE.add hI
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

theorem sliceGfull_eq_integral {l : ℝ} (hl : 0 < l) {w : Torus d} (hw : w ≠ 0) :
    sliceGfull d l w = ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) := by
  have hI := SliceAux.integrableOn_slice_psi hl.le hw
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this
  have hE' : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) = 1 / l := by
    rw [integral_exp_mul_Ioi (by linarith : -l < 0)]
    simp
  unfold sliceGfull sliceG
  have : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) =
      1 / l + ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn w (4 * Real.pi ^ 2 * t) := by
    rw [← hE', ← integral_add hE hI]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [this]; ring

/-- the constant bounding the tail `∫_1^∞ |Ψ|`. -/
def Kc (d : ℕ) : ℝ := ∫ t in Ioi (1 : ℝ), thetaC d * Real.exp (1 - 4 * Real.pi ^ 2 * t)

theorem sliceG_abs_le {w : Torus d} (hw : w ≠ 0) {l : ℝ} (hl : 0 ≤ l) :
    |sliceG d l w| ≤ Real.exp 1 * sliceGfull d 1 w + 1 + Kc d := by
  have hψ := integrableOn_psi0 hw
  have hpi : (0:ℝ) < 4 * Real.pi ^ 2 := by positivity
  -- step 1
  have h1 : |sliceG d l w| ≤ ∫ t in Ioi (0 : ℝ), ‖psiFn w (4 * Real.pi ^ 2 * t)‖ := by
    unfold sliceG
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hψ.norm ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun t ht => ?_))
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-l * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) < t := ht; nlinarith
    exact mul_le_of_le_one_left (norm_nonneg _) this
  refine h1.trans ?_
  -- step 2: split at 1
  have hn : IntegrableOn (fun t : ℝ => ‖psiFn w (4 * Real.pi ^ 2 * t)‖) (Ioi 0) := hψ.norm
  have hnA : IntegrableOn (fun t : ℝ => ‖psiFn w (4 * Real.pi ^ 2 * t)‖) (Ioc 0 1) :=
    hn.mono_set Ioc_subset_Ioi_self
  have hnB : IntegrableOn (fun t : ℝ => ‖psiFn w (4 * Real.pi ^ 2 * t)‖) (Ioi 1) :=
    hn.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsplit : ∫ t in Ioi (0 : ℝ), ‖psiFn w (4 * Real.pi ^ 2 * t)‖ =
      (∫ t in Ioc (0 : ℝ) 1, ‖psiFn w (4 * Real.pi ^ 2 * t)‖) + ∫ t in Ioi (1 : ℝ), ‖psiFn w (4 * Real.pi ^ 2 * t)‖ := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hnA hnB,
      Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  rw [hsplit]
  have hP : IntegrableOn (fun t : ℝ => Real.exp (-1 * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t))) (Ioi 0) :=
    integrableOn_exp_P one_pos hw
  have hG := sliceGfull_eq_integral (d := d) one_pos hw
  have hPA : IntegrableOn (fun t : ℝ => Real.exp 1 * (Real.exp (-1 * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)))) (Ioc 0 1) :=
    (hP.mono_set Ioc_subset_Ioi_self).const_mul _
  have hA : ∫ t in Ioc (0 : ℝ) 1, ‖psiFn w (4 * Real.pi ^ 2 * t)‖ ≤ Real.exp 1 * sliceGfull d 1 w + 1 := by
    have h1 : ∫ t in Ioc (0 : ℝ) 1, ‖psiFn w (4 * Real.pi ^ 2 * t)‖ ≤
        ∫ t in Ioc (0 : ℝ) 1, (Real.exp 1 * (Real.exp (-1 * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t))) + 1) := by
      refine setIntegral_mono_on hnA (hPA.add (integrableOn_const (by simp))) measurableSet_Ioc fun t ht => ?_
      have hP0 := one_add_psiFn_nonneg w (d := d) ht.1
      have he : 1 ≤ Real.exp 1 * Real.exp (-1 * t) := by
        rw [← Real.exp_add]; apply Real.one_le_exp; linarith [ht.2]
      rw [Real.norm_eq_abs, abs_le']
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right he hP0]
    refine h1.trans ?_
    rw [integral_add hPA (integrableOn_const (by simp)), integral_const_mul]
    simp only [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one,
      smul_eq_mul, mul_one, one_smul]
    have h2 : ∫ t in Ioc (0 : ℝ) 1, Real.exp (-1 * t) * (1 + psiFn w (4 * Real.pi ^ 2 * t)) ≤ sliceGfull d 1 w := by
      rw [hG]
      refine setIntegral_mono_set hP ?_ Ioc_subset_Ioi_self.eventuallyLE
      exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
        mul_nonneg (Real.exp_pos _).le (one_add_psiFn_nonneg w ht))
    nlinarith [Real.exp_pos 1]
  have hB : ∫ t in Ioi (1 : ℝ), ‖psiFn w (4 * Real.pi ^ 2 * t)‖ ≤ Kc d := by
    unfold Kc
    have hg : IntegrableOn (fun t : ℝ => thetaC d * Real.exp (1 - 4 * Real.pi ^ 2 * t)) (Ioi 1) := by
      have this : IntegrableOn (fun t : ℝ => thetaC d * Real.exp 1 * Real.exp (-(4 * Real.pi ^ 2) * t)) (Ioi 1) :=
        (integrableOn_exp_mul_Ioi (a := -(4 * Real.pi ^ 2)) (by linarith) (1 : ℝ)).const_mul (thetaC d * Real.exp 1)
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      show _ = _
      rw [show 1 - 4 * Real.pi ^ 2 * t = 1 + -(4 * Real.pi ^ 2) * t by ring, Real.exp_add]; ring
    refine setIntegral_mono_on hnB hg measurableSet_Ioi fun t ht => ?_
    have := abs_psiFn_le w (u := 4 * Real.pi ^ 2 * t) (by
      have : (1:ℝ) < t := ht
      nlinarith [Real.pi_gt_three])
    rwa [Real.norm_eq_abs]
  linarith

end HRS.Commutator.SmearAux
