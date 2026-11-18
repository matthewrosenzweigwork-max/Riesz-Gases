import HRS.Energy.Commutator.RenormStjFinal

/-!
# Route S, packet STJ: the sharp self energy for `d = 1` (the case `s = 0`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

/-- the one-dimensional Yukawa profile is convex on `(0, ∞)` (`Γ'' = l Γ ≥ 0`) -/
theorem yukawa_convex_d1 {l : ℝ} (hl : 0 < l) : ConvexOn ℝ (Ioi (0 : ℝ)) (yukawa 1 l) := by
  have hyk := yukawa_ode (d := 1) le_rfl hl
  have hdiff : ∀ r : ℝ, 0 < r → HasDerivAt (yukawa 1 l) (deriv (yukawa 1 l) r) r := fun r hr =>
    SmearAux.hasDerivAt_yukawa le_rfl hl hr
  have hder2 : ∀ r : ℝ, 0 < r → deriv (deriv (yukawa 1 l)) r = l * yukawa 1 l r := by
    intro r hr
    have h := hyk.2.2.1 r hr
    simpa using h
  have hdd : ∀ r : ℝ, 0 < r → DifferentiableAt ℝ (deriv (yukawa 1 l)) r := by
    intro r hr
    refine differentiableAt_of_deriv_ne_zero ?_
    rw [hder2 r hr]
    exact (mul_pos hl (hyk.1 r hr)).ne'
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0) ?_ ?_ ?_
  · exact fun r hr => (hdiff r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioi] at hr
    exact (hdiff r hr).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · exact fun r hr => (hdd r hr).continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Ioi] at hr
      exact (hdd r hr).differentiableWithinAt
    · intro r hr
      rw [interior_Ioi] at hr
      rw [hder2 r hr]
      exact (mul_pos hl (hyk.1 r hr)).le

theorem yukawa_pair_d1 {l η k : ℝ} (hl : 0 < l) (hη : 0 ≤ η) (hk : η < k) :
    2 * yukawa 1 l k ≤ yukawa 1 l (k - η) + yukawa 1 l (k + η) := by
  have h := (yukawa_convex_d1 hl).2 (show k - η ∈ Ioi (0 : ℝ) from by simp [mem_Ioi]; linarith)
    (show k + η ∈ Ioi (0 : ℝ) from by simp [mem_Ioi]; linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • (k - η) + (1 / 2 : ℝ) • (k + η) = k := by simp only [smul_eq_mul]; ring
  rw [e] at h
  simp only [smul_eq_mul] at h
  linarith

/-- the point `η` of the circle, as an element of `ℝ¹` -/
def e1 (η : ℝ) : Euc 1 := WithLp.toLp 2 (fun _ => η)

theorem norm_toEuc_d1 (m : Lattice 1) : ‖Lattice.toEuc m‖ = |((m 0 : ℤ) : ℝ)| := by
  simp [EuclideanSpace.norm_eq, Lattice.toEuc, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

theorem norm_e1_sub_d1 (η : ℝ) (m : Lattice 1) : ‖e1 η - Lattice.toEuc m‖ = |η - ((m 0 : ℤ) : ℝ)| := by
  simp [e1, EuclideanSpace.norm_eq, Lattice.toEuc, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

theorem lattice_pair_d1 {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∑' m : Lattice 1, ENNReal.ofReal (yukawa 1 l (max ‖Lattice.toEuc m‖ η)) ≤
      ∑' m : Lattice 1, ENNReal.ofReal (yukawa 1 l ‖e1 η - Lattice.toEuc m‖) := by
  set A : Lattice 1 → ℝ≥0∞ := fun m => ENNReal.ofReal (yukawa 1 l (max ‖Lattice.toEuc m‖ η)) with hA
  set B : Lattice 1 → ℝ≥0∞ := fun m => ENNReal.ofReal (yukawa 1 l ‖e1 η - Lattice.toEuc m‖) with hB
  have hpt : ∀ m : Lattice 1, A m + A (-m) ≤ B m + B (-m) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hA, hB, neg_zero]
      have h1 : ‖Lattice.toEuc (0 : Lattice 1)‖ = 0 := by simp [norm_toEuc_d1]
      have h2 : ‖e1 η - Lattice.toEuc (0 : Lattice 1)‖ = η := by
        simp [norm_e1_sub_d1, abs_of_pos hη]
      rw [h1, h2, max_eq_right hη.le]
    · have hm0 : m 0 ≠ 0 := fun h => hm (by ext i; fin_cases i; simpa using h)
      have hk : (1 : ℝ) ≤ |((m 0 : ℤ) : ℝ)| := by
        have : (1 : ℤ) ≤ |m 0| := Int.one_le_abs hm0
        have h' : ((1 : ℤ) : ℝ) ≤ ((|m 0| : ℤ) : ℝ) := by exact_mod_cast this
        simpa [Int.cast_abs] using h'
      set k := |((m 0 : ℤ) : ℝ)| with hkdef
      have hnm : ((-m) 0 : ℤ) = -(m 0) := by simp
      have e1' : max ‖Lattice.toEuc m‖ η = k := by rw [norm_toEuc_d1, max_eq_left]; linarith
      have e2' : max ‖Lattice.toEuc (-m)‖ η = k := by
        rw [norm_toEuc_d1, hnm]; push_cast; rw [abs_neg, max_eq_left]; linarith
      simp only [hA, hB]
      rw [e1', e2', norm_e1_sub_d1, norm_e1_sub_d1, hnm]
      push_cast
      have hpair := yukawa_pair_d1 hl hη.le (show η < k by linarith)
      have hk0 : ∀ r : ℝ, 0 ≤ yukawa 1 l r := fun r => SmearAux.yukawa_nonneg 1 l r
      have key : |η - (m 0 : ℝ)| = k - η ∧ |η - (-(m 0 : ℝ))| = k + η ∨
          |η - (m 0 : ℝ)| = k + η ∧ |η - (-(m 0 : ℝ))| = k - η := by
        rcases le_total 0 (m 0 : ℝ) with h | h
        · left
          have : k = (m 0 : ℝ) := by rw [hkdef, abs_of_nonneg h]
          rw [this]
          constructor
          · rw [abs_of_nonpos (by linarith)]; ring
          · rw [abs_of_nonneg (by linarith)]; ring
        · right
          have : k = -(m 0 : ℝ) := by rw [hkdef, abs_of_nonpos h]
          rw [this]
          constructor
          · rw [abs_of_nonneg (by linarith)]; ring
          · rw [abs_of_nonpos (by linarith)]; ring
      have hs : ENNReal.ofReal (yukawa 1 l k) + ENNReal.ofReal (yukawa 1 l k) ≤
          ENNReal.ofReal (yukawa 1 l (k - η)) + ENNReal.ofReal (yukawa 1 l (k + η)) := by
        rw [← ENNReal.ofReal_add (hk0 _) (hk0 _), ← ENNReal.ofReal_add (hk0 _) (hk0 _)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hs
      · rw [h1, h2, add_comm (ENNReal.ofReal (yukawa 1 l (k + η)))]; exact hs
  have h2 : 2 * ∑' m, A m ≤ 2 * ∑' m, B m := by
    have e1 : ∑' m, A (-m) = ∑' m, A m := (Equiv.neg (Lattice 1)).tsum_eq A
    have e2 : ∑' m, B (-m) = ∑' m, B m := (Equiv.neg (Lattice 1)).tsum_eq B
    calc 2 * ∑' m, A m = ∑' m, A m + ∑' m, A (-m) := by rw [e1, two_mul]
      _ = ∑' m, (A m + A (-m)) := (ENNReal.tsum_add).symm
      _ ≤ ∑' m, (B m + B (-m)) := ENNReal.tsum_le_tsum hpt
      _ = ∑' m, B m + ∑' m, B (-m) := ENNReal.tsum_add
      _ = 2 * ∑' m, B m := by rw [e2, two_mul]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2

theorem Gint_le_d1 {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∫ x, sliceGfull 1 l x ∂(smearT 1 l η) ≤ sliceGfull 1 l (Torus.mk (e1 η)) := by
  have hη2 : η < 1 / 2 := by linarith
  have hd1 : 1 ≤ 1 := le_rfl
  haveI hν : IsFiniteMeasure (smearEuc 1 l η) := isFiniteMeasure_smearEuc 1 l η
  set ν := smearEuc 1 l η with hνdef
  have hNewt : ∀ z : Euc 1, ∫⁻ y, ENNReal.ofReal (yukawa 1 l ‖y - z‖) ∂ν =
      ENNReal.ofReal (yukawa 1 l (max ‖z‖ η)) := by
    intro z
    exact SmearAux.newton_yukawa' hd1 hl hη z _
      (fun s hs => by rw [integral_smearEuc hd1 hl hη (SmearAux.contDiff_gφ s _).continuous]; ring)
      (Eventually.of_forall fun y => SmearAux.integrableOn_yk_d1 hl (norm_nonneg _))
  have hnull : ∀ᵐ y ∂ν, Torus.mk y ≠ (0 : Torus 1) := by
    have h := EnergyAux.smearT_singleton_zero hd1 (l := l) hη hη2
    have h' : ν (Torus.mk ⁻¹' {0}) = 0 := by
      have := h
      unfold smearT at this
      rwa [Measure.map_apply Torus.continuous_mk.measurable (measurableSet_singleton _)] at this
    rw [ae_iff]
    have e : {a : Euc 1 | ¬ Torus.mk a ≠ (0 : Torus 1)} = Torus.mk ⁻¹' {0} := by ext a; simp
    rw [e]; exact h'
  have hmeasG : Measurable fun y : Euc 1 => sliceGfull 1 l (Torus.mk y) :=
    (EnergyAux.measurable_sliceGfull l).comp Torus.continuous_mk.measurable
  have hL : ∫⁻ y, ENNReal.ofReal (sliceGfull 1 l (Torus.mk y)) ∂ν =
      ∑' m : Lattice 1, ENNReal.ofReal (yukawa 1 l (max ‖Lattice.toEuc m‖ η)) := by
    calc ∫⁻ y, ENNReal.ofReal (sliceGfull 1 l (Torus.mk y)) ∂ν
        = ∫⁻ y, ∑' m : Lattice 1, ENNReal.ofReal (yukawa 1 l ‖y - Lattice.toEuc m‖) ∂ν := by
          refine lintegral_congr_ae ?_
          filter_upwards [hnull] with y hy
          obtain ⟨hs, he⟩ := SmearAux.periodization_vec (d := 1) hl hy
          rw [he, ENNReal.ofReal_tsum_of_nonneg (fun m => SmearAux.yukawa_nonneg 1 l _) hs]
      _ = ∑' m : Lattice 1, ∫⁻ y, ENNReal.ofReal (yukawa 1 l ‖y - Lattice.toEuc m‖) ∂ν := by
          refine lintegral_tsum fun m => ?_
          exact (ENNReal.measurable_ofReal.comp ((SmearAux.measurable_yukawa (d := 1) l).comp
            (measurable_norm.comp (measurable_id.sub_const _)))).aemeasurable
      _ = _ := tsum_congr fun m => hNewt _
  have hmk0 : Torus.mk (e1 η) ≠ (0 : Torus 1) := by
    intro h
    have h1 := KernelGrad.tdist_mk (d := 1) (y := e1 η) (fun i => by
      simp [e1, abs_of_pos hη]; linarith)
    rw [h, CoercAux.tdist_self] at h1
    have hne : ‖e1 η‖ = η := by
      simp [e1, EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, abs_of_pos hη]
    rw [hne] at h1
    linarith
  have hR : ENNReal.ofReal (sliceGfull 1 l (Torus.mk (e1 η))) =
      ∑' m : Lattice 1, ENNReal.ofReal (yukawa 1 l ‖e1 η - Lattice.toEuc m‖) := by
    obtain ⟨hs, he⟩ := SmearAux.periodization_vec (d := 1) hl hmk0
    rw [he, ENNReal.ofReal_tsum_of_nonneg (fun m => SmearAux.yukawa_nonneg 1 l _) hs]
  have hineq : ∫⁻ y, ENNReal.ofReal (sliceGfull 1 l (Torus.mk y)) ∂ν ≤
      ENNReal.ofReal (sliceGfull 1 l (Torus.mk (e1 η))) := by
    rw [hL, hR]; exact lattice_pair_d1 hl hη hη8
  have hint : ∫ x, sliceGfull 1 l x ∂(smearT 1 l η) = ∫ y, sliceGfull 1 l (Torus.mk y) ∂ν := by
    unfold smearT
    exact integral_map Torus.continuous_mk.measurable.aemeasurable
      (EnergyAux.measurable_sliceGfull l).aestronglyMeasurable
  rw [hint, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y =>
    EnergyAux.sliceGfull_nonneg hl _) hmeasG.aestronglyMeasurable]
  calc (∫⁻ y, ENNReal.ofReal (sliceGfull 1 l (Torus.mk y)) ∂ν).toReal
      ≤ (ENNReal.ofReal (sliceGfull 1 l (Torus.mk (e1 η)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hineq
    _ = sliceGfull 1 l (Torus.mk (e1 η)) := ENNReal.toReal_ofReal (EnergyAux.sliceGfull_nonneg hl _)

/-- the sharp self energy bound for `d = 1`: `S_l(η) ≤ 𝒢_l(η) + 2 ∫ f_{l,η}` -/
theorem Self_le_G_d1 {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    Self 1 l η ≤ sliceG 1 l (Torus.mk (e1 η)) + 2 * ∫ z : Torus 1, fTrunc 1 l η z := by
  have hη2 : η < 1 / 2 := by linarith
  have hd : 1 ≤ 1 := le_rfl
  set σ := smearT 1 l η with hσ
  haveI : IsFiniteMeasure σ := (smearT_structure hd hl hη hη2).1
  have hGi := integrable_G_smearT hd hl hη hη2
  have h0 : ∀ᵐ x ∂σ, x ≠ 0 := by
    rw [ae_iff]; simpa using EnergyAux.smearT_singleton_zero hd hη hη2
  have hfd : ∀ x, 0 ≤ fTrunc 1 l η x := fun x => le_max_right _ _
  have hfle : ∀ᵐ x ∂σ, fTrunc 1 l η x ≤ sliceGfull 1 l x := by
    filter_upwards [h0] with x hx
    have := EnergyAux.g_sub_f_pos hd hl hη hx
    linarith
  have hfi : Integrable (fTrunc 1 l η) σ := by
    refine Integrable.mono' hGi (EnergyAux.measurable_fTrunc l η).aestronglyMeasurable ?_
    filter_upwards [hfle] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hfd x)]; exact hx
  have hinner : ∀ᵐ x ∂σ, ∫ y, sliceGfull 1 l (x - y) ∂σ = sliceGfull 1 l x - fTrunc 1 l η x := by
    filter_upwards [h0] with x hx
    exact sliceGfull_conv_smear hd hl hη hη2 x hx
  have hdbl : ∫ x, ∫ y, sliceGfull 1 l (x - y) ∂σ ∂σ =
      ∫ x, sliceGfull 1 l x ∂σ - ∫ x, fTrunc 1 l η x ∂σ := by
    rw [integral_congr_ae hinner, integral_sub hGi hfi]
  have hm := smearT_real_univ hd hl hη hη2
  have hmass : mass 1 l η = 1 - l * ∫ z : Torus 1, fTrunc 1 l η z := hm
  have hF0 : 0 ≤ ∫ z : Torus 1, fTrunc 1 l η z := integral_nonneg hfd
  have hfs : 0 ≤ ∫ x, fTrunc 1 l η x ∂σ := integral_nonneg hfd
  have hG := Gint_le_d1 hl hη hη8
  unfold Self
  rw [hdbl]
  have e : sliceGfull 1 l (Torus.mk (e1 η)) = sliceG 1 l (Torus.mk (e1 η)) + 1 / l := rfl
  set F := ∫ z : Torus 1, fTrunc 1 l η z with hF
  have hm2 : (mass 1 l η) ^ 2 / l ≥ 1 / l - 2 * F := by
    rw [hmass]
    have : (1 - l * F) ^ 2 / l = 1 / l - 2 * F + l * F ^ 2 := by field_simp; ring
    rw [this]
    have : 0 ≤ l * F ^ 2 := by positivity
    linarith
  linarith

end HRS.Commutator.Stj
