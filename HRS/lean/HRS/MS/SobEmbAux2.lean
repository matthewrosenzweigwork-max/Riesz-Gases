import HRS.MS.SobEmbAux1

/-!
# SA1, Aux2: the one-derivative step `W^{1,a} → L^r` (power trick, vector valued)

For `1 ≤ q < d`, `q'⁻¹ = q⁻¹ - d⁻¹`, `γ ≥ 1`, set `a = γ q`, `r = γ q'`.  Then for `C¹` `u` with values in a finite dimensional
normed space `‖u‖_r ≤ K (‖u‖_a + ‖Du‖_a)` (`sa1_step`).  For `γ = 1` this is the global GNS inequality; for `γ > 1` it is
applied to `x ↦ ‖e (u x)‖^γ` (`e` a linear equivalence onto a Euclidean space, so that the `γ`-th power of the norm is `C¹`) and
Hölder's inequality.  (`γ > 1` is needed e.g. for `p_𝔠 = d`.)
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

variable {d : ℕ}

theorem sa1_cast (x y : ℝ≥0) : (x : ℝ≥0∞) * ENNReal.ofReal (y : ℝ) = ((y * x : ℝ≥0) : ℝ≥0∞) := by
  rw [ENNReal.ofReal_coe_nnreal, mul_comm, ENNReal.coe_mul]

/-- `x^θ y^(1-θ) ≤ x + y`. -/
theorem sa1_amgm (x y : ℝ≥0∞) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : x ^ θ * y ^ (1 - θ) ≤ x + y := by
  rcases le_total x y with hxy | hxy
  · calc x ^ θ * y ^ (1 - θ) ≤ y ^ θ * y ^ (1 - θ) := by gcongr
      _ = y := by rw [← ENNReal.rpow_add_of_nonneg _ _ h0 (by linarith), add_sub_cancel, ENNReal.rpow_one]
      _ ≤ x + y := le_add_self
  · calc x ^ θ * y ^ (1 - θ) ≤ x ^ θ * x ^ (1 - θ) := by gcongr
      _ = x := by rw [← ENNReal.rpow_add_of_nonneg _ _ h0 (by linarith), add_sub_cancel, ENNReal.rpow_one]
      _ ≤ x + y := le_self_add

theorem sa1_step_euc {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] {q q' γ : ℝ≥0}
    (hq : 1 ≤ q) (hqd : (q : ℝ) < d) (hq' : (q' : ℝ)⁻¹ = (q : ℝ)⁻¹ - (d : ℝ)⁻¹) (hγ : 1 < γ) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ w : EuclideanSpace ℝ (Fin d) → F', ContDiff ℝ 1 w →
      eLpNorm w ((γ * q : ℝ≥0) : ℝ≥0∞) volume < ⊤ → eLpNorm (fderiv ℝ w) ((γ * q : ℝ≥0) : ℝ≥0∞) volume < ⊤ →
      eLpNorm w ((γ * q' : ℝ≥0) : ℝ≥0∞) volume ≤
        K * (eLpNorm w ((γ * q : ℝ≥0) : ℝ≥0∞) volume + eLpNorm (fderiv ℝ w) ((γ * q : ℝ≥0) : ℝ≥0∞) volume) := by
  obtain ⟨K0, hK0, hGNS⟩ := sa1_gns_global (F := ℝ) (d := d) hq hqd hq'
  have hγ1 : (1 : ℝ) < γ := by exact_mod_cast hγ
  have hγ0 : (0 : ℝ) < γ := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set a : ℝ≥0 := γ * q with ha
  set r : ℝ≥0 := γ * q' with hr
  have ha1 : (a : ℝ) = γ * q := by simp [ha]
  have hr1 : (r : ℝ) = γ * q' := by simp [hr]
  set δ : ℝ≥0 := γ - 1 with hδ
  have hδ1 : (δ : ℝ) = γ - 1 := by rw [hδ, NNReal.coe_sub hγ.le]; simp
  have hδ0 : (0 : ℝ) < δ := by rw [hδ1]; linarith
  set b : ℝ≥0 := a / δ with hb
  have hbδ : b * δ = a := by
    rw [hb]; exact div_mul_cancel₀ _ (by exact_mod_cast hδ0.ne')
  refine ⟨(K0 * γ) ^ (1 / (γ : ℝ)), by positivity, fun w hw hA hA' => ?_⟩
  have hwc : Continuous w := hw.continuous
  have hdw : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by simp)
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ‖w x‖ ^ (γ : ℝ) with hv
  have hv_cd : ContDiff ℝ 1 v := hw.norm_rpow hγ1
  have hvc : Continuous v := hv_cd.continuous
  have hvq : eLpNorm v (q : ℝ≥0∞) volume = eLpNorm w (a : ℝ≥0∞) volume ^ (γ : ℝ) := by
    rw [hv, eLpNorm_norm_rpow w hwc.aestronglyMeasurable hγ0, sa1_cast]
  have hvq' : eLpNorm v (q' : ℝ≥0∞) volume = eLpNorm w (r : ℝ≥0∞) volume ^ (γ : ℝ) := by
    rw [hv, eLpNorm_norm_rpow w hwc.aestronglyMeasurable hγ0, sa1_cast]
  have hvfin : eLpNorm v (q : ℝ≥0∞) volume < ⊤ := by
    rw [hvq]; exact ENNReal.rpow_lt_top_of_nonneg hγ0.le hA.ne
  have h1 := hGNS v hv_cd hvfin
  have hdv : ∀ x, ‖fderiv ℝ v x‖ ≤ (γ : ℝ) * (‖w x‖ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ w x‖) := by
    intro x
    have := norm_fderiv_norm_rpow_le (hw.differentiable (by simp)) (x := x) hγ1
    rw [mul_assoc] at this
    exact this
  have hq0 : q ≠ 0 := by positivity
  have ha0 : a ≠ 0 := by positivity
  have hδ0' : δ ≠ 0 := by
    intro h; rw [h] at hδ0; simp at hδ0
  have hb0 : b ≠ 0 := by rw [hb]; exact div_ne_zero ha0 hδ0'
  have hholder : ENNReal.HolderTriple (b : ℝ≥0∞) (a : ℝ≥0∞) (q : ℝ≥0∞) := by
    refine ⟨?_⟩
    have hNN : b⁻¹ + a⁻¹ = q⁻¹ := by
      apply NNReal.eq
      have hbR : (b : ℝ) = γ * q / (γ - 1) := by rw [hb, NNReal.coe_div, ha1, hδ1]
      have hq0' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
      have hg1 : (γ : ℝ) - 1 ≠ 0 := by linarith
      rw [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_inv, NNReal.coe_inv, hbR, ha1]
      field_simp
      ring
    rw [← ENNReal.coe_inv hb0, ← ENNReal.coe_inv ha0, ← ENNReal.coe_inv hq0, ← ENNReal.coe_add, hNN]
  have hfe : eLpNorm (fun x => ‖w x‖ ^ ((γ : ℝ) - 1)) (b : ℝ≥0∞) volume =
      eLpNorm w (a : ℝ≥0∞) volume ^ ((γ : ℝ) - 1) := by
    rw [eLpNorm_norm_rpow w hwc.aestronglyMeasurable (by linarith), ← hδ1, sa1_cast, mul_comm δ b, hbδ]
  have h2 : eLpNorm (fderiv ℝ v) (q : ℝ≥0∞) volume ≤
      (γ : ℝ≥0∞) * (eLpNorm w (a : ℝ≥0∞) volume ^ ((γ : ℝ) - 1) * eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume) := by
    have hH := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := (b : ℝ≥0∞)) (q := (a : ℝ≥0∞)) (r := (q : ℝ≥0∞))
      (μ := volume) (f := fun x => ‖w x‖ ^ ((γ : ℝ) - 1)) (g := fun x => ‖fderiv ℝ w x‖)
      (fun s t : ℝ => s * t) 1 continuous_mul
      ((hwc.norm.rpow_const (fun _ => Or.inr (by linarith))).aestronglyMeasurable)
      hdw.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simp only [norm_mul, norm_norm, NNReal.coe_one, one_mul]
        exact le_of_eq rfl)
    rw [hfe, eLpNorm_norm _ hdw.aestronglyMeasurable] at hH
    calc eLpNorm (fderiv ℝ v) (q : ℝ≥0∞) volume
        ≤ eLpNorm (fun x => (γ : ℝ) • (‖w x‖ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ w x‖)) (q : ℝ≥0∞) volume :=
          eLpNorm_mono_real (hv_cd.continuous_fderiv (by simp)).aestronglyMeasurable
            (fun x => by simpa using hdv x)
      _ = ‖(γ : ℝ)‖ₑ * eLpNorm (fun x => ‖w x‖ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ w x‖) (q : ℝ≥0∞) volume := by
          exact eLpNorm_const_smul (γ : ℝ) (fun x => ‖w x‖ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ w x‖) _ _
      _ ≤ (γ : ℝ≥0∞) * (eLpNorm w (a : ℝ≥0∞) volume ^ ((γ : ℝ) - 1) * eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume) := by
          rw [Real.enorm_eq_ofReal hγ0.le, ENNReal.ofReal_coe_nnreal]
          gcongr
          simpa using hH
  have hX : eLpNorm w (r : ℝ≥0∞) volume ^ (γ : ℝ) ≤ (K0 : ℝ≥0∞) *
      ((γ : ℝ≥0∞) * (eLpNorm w (a : ℝ≥0∞) volume ^ ((γ : ℝ) - 1) * eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume)) := by
    rw [← hvq']
    exact h1.trans (by gcongr)
  have hinv : (0 : ℝ) ≤ 1 / (γ : ℝ) := by positivity
  have hθ : 1 / (γ : ℝ) = 1 - ((γ : ℝ) - 1) / γ := by field_simp; ring
  have hcoe : (((K0 * γ) ^ (1 / (γ : ℝ)) : ℝ≥0) : ℝ≥0∞) = ((K0 : ℝ≥0∞) * γ) ^ (1 / (γ : ℝ)) := by
    rw [ENNReal.coe_rpow_of_nonneg _ hinv, ENNReal.coe_mul]
  rw [hcoe]
  calc eLpNorm w (r : ℝ≥0∞) volume
      = (eLpNorm w (r : ℝ≥0∞) volume ^ (γ : ℝ)) ^ (1 / (γ : ℝ)) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hγ0.ne', ENNReal.rpow_one]
    _ ≤ ((K0 : ℝ≥0∞) * ((γ : ℝ≥0∞) * (eLpNorm w (a : ℝ≥0∞) volume ^ ((γ : ℝ) - 1) *
          eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume))) ^ (1 / (γ : ℝ)) := ENNReal.rpow_le_rpow hX hinv
    _ = ((K0 : ℝ≥0∞) * γ) ^ (1 / (γ : ℝ)) * (eLpNorm w (a : ℝ≥0∞) volume ^ (((γ : ℝ) - 1) / γ) *
          eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume ^ (1 - ((γ : ℝ) - 1) / γ)) := by
        have e1 : (eLpNorm w (a : ℝ≥0∞) volume ^ ((γ : ℝ) - 1) * eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume) ^
            (1 / (γ : ℝ)) = eLpNorm w (a : ℝ≥0∞) volume ^ (((γ : ℝ) - 1) / γ) *
              eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume ^ (1 - ((γ : ℝ) - 1) / γ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ← ENNReal.rpow_mul, ← hθ]
          congr 2
          ring
        rw [← mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hinv, e1]
    _ ≤ ((K0 : ℝ≥0∞) * γ) ^ (1 / (γ : ℝ)) * (eLpNorm w (a : ℝ≥0∞) volume +
          eLpNorm (fderiv ℝ w) (a : ℝ≥0∞) volume) := by
        gcongr
        exact sa1_amgm _ _ (div_nonneg (by linarith) hγ0.le) (by rw [div_le_one hγ0]; linarith)


theorem sa1_eLpNorm_clm {α G H : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] H) (f : α → G)
    (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun x => L (f x)) p μ ≤ (‖L‖₊ : ℝ≥0∞) * eLpNorm f p μ := by
  have hm : AEStronglyMeasurable (fun x => L (f x)) μ := L.continuous.comp_aestronglyMeasurable hf
  exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hm (Eventually.of_forall fun x => L.le_opNNNorm _) p

/-- **The one-derivative step** `‖u‖_{γq'} ≤ K (‖u‖_{γq} + ‖Du‖_{γq})` for `C¹` maps into a finite dimensional normed space,
`1 ≤ q < d`, `q'⁻¹ = q⁻¹ - d⁻¹`, `γ ≥ 1`. -/
theorem sa1_step {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {q q' γ : ℝ≥0} (hq : 1 ≤ q) (hqd : (q : ℝ) < d) (hq' : (q' : ℝ)⁻¹ = (q : ℝ)⁻¹ - (d : ℝ)⁻¹) (hγ : 1 ≤ γ) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ u : EuclideanSpace ℝ (Fin d) → F, ContDiff ℝ 1 u →
      eLpNorm u ((γ * q' : ℝ≥0) : ℝ≥0∞) volume ≤
        K * (eLpNorm u ((γ * q : ℝ≥0) : ℝ≥0∞) volume + eLpNorm (fderiv ℝ u) ((γ * q : ℝ≥0) : ℝ≥0∞) volume) := by
  rcases hγ.eq_or_lt with rfl | hγ1
  · obtain ⟨K0, hK0, h⟩ := sa1_gns_global (F := F) (d := d) hq hqd hq'
    refine ⟨K0, hK0, fun u hu => ?_⟩
    simp only [one_mul]
    by_cases hA : eLpNorm u (q : ℝ≥0∞) volume < ⊤
    · exact (h u hu hA).trans (by gcongr; exact le_add_self)
    · rw [not_lt, top_le_iff] at hA
      rw [hA, top_add, ENNReal.mul_top (by exact_mod_cast hK0.ne')]
      exact le_top
  · let F' := EuclideanSpace ℝ (Fin (finrank ℝ F))
    obtain ⟨K1, hK1, h⟩ := sa1_step_euc (F' := F') (d := d) hq hqd hq' hγ1
    let e : F ≃L[ℝ] F' := toEuclidean
    set c1 : ℝ≥0 := ‖(e : F →L[ℝ] F')‖₊ with hc1
    set c2 : ℝ≥0 := ‖(e.symm : F' →L[ℝ] F)‖₊ with hc2
    refine ⟨(c2 + 1) * K1 * (c1 + 1), by positivity, fun u hu => ?_⟩
    set a : ℝ≥0∞ := ((γ * q : ℝ≥0) : ℝ≥0∞) with ha
    set r : ℝ≥0∞ := ((γ * q' : ℝ≥0) : ℝ≥0∞) with hr
    have hKpos : (K1 : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK1.ne'
    by_cases hA : eLpNorm u a volume = ⊤ ∨ eLpNorm (fderiv ℝ u) a volume = ⊤
    · have : eLpNorm u a volume + eLpNorm (fderiv ℝ u) a volume = ⊤ := by
        rcases hA with h1 | h1 <;> simp [h1]
      rw [this, ENNReal.mul_top]
      · exact le_top
      · simp only [ne_eq, ENNReal.coe_eq_zero, mul_eq_zero, not_or]
        exact ⟨⟨by positivity, hK1.ne'⟩, by positivity⟩
    simp only [not_or] at hA
    have huc : Continuous u := hu.continuous
    have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
    set w : EuclideanSpace ℝ (Fin d) → F' := fun x => e (u x) with hw
    have hw_cd : ContDiff ℝ 1 w := e.contDiff.comp hu
    have hfw : ∀ x, fderiv ℝ w x = (e : F →L[ℝ] F').comp (fderiv ℝ u x) := fun x => by
      rw [hw]; exact e.comp_fderiv
    have hwA : eLpNorm w a volume ≤ c1 * eLpNorm u a volume :=
      sa1_eLpNorm_clm (e : F →L[ℝ] F') u huc.aestronglyMeasurable a
    have hwA' : eLpNorm (fderiv ℝ w) a volume ≤ c1 * eLpNorm (fderiv ℝ u) a volume := by
      have hmeas : AEStronglyMeasurable (fderiv ℝ w) volume := (hw_cd.continuous_fderiv (by simp)).aestronglyMeasurable
      refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hmeas (Eventually.of_forall fun x => ?_) a)
      rw [hfw x]
      exact ContinuousLinearMap.opNNNorm_comp_le _ _
    have h1 := h w hw_cd (lt_of_le_of_lt hwA (ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.2 hA.1)))
      (lt_of_le_of_lt hwA' (ENNReal.mul_lt_top ENNReal.coe_lt_top (lt_top_iff_ne_top.2 hA.2)))
    have hu_eq : u = fun x => (e.symm : F' →L[ℝ] F) (w x) := by
      funext x; simp [hw]
    have hur : eLpNorm u r volume ≤ c2 * eLpNorm w r volume := by
      conv_lhs => rw [hu_eq]
      exact sa1_eLpNorm_clm (e.symm : F' →L[ℝ] F) w hw_cd.continuous.aestronglyMeasurable r
    calc eLpNorm u r volume ≤ c2 * eLpNorm w r volume := hur
      _ ≤ c2 * (K1 * (eLpNorm w a volume + eLpNorm (fderiv ℝ w) a volume)) := by gcongr
      _ ≤ c2 * (K1 * (c1 * eLpNorm u a volume + c1 * eLpNorm (fderiv ℝ u) a volume)) := by gcongr
      _ = ((c2 * K1 * c1 : ℝ≥0) : ℝ≥0∞) * (eLpNorm u a volume + eLpNorm (fderiv ℝ u) a volume) := by
          push_cast; ring
      _ ≤ (((c2 + 1) * K1 * (c1 + 1) : ℝ≥0) : ℝ≥0∞) * (eLpNorm u a volume + eLpNorm (fderiv ℝ u) a volume) := by
          have hle : (c2 * K1 * c1 : ℝ≥0) ≤ (c2 + 1) * K1 * (c1 + 1) :=
            mul_le_mul' (mul_le_mul' le_self_add le_rfl) le_self_add
          gcongr

end HRS.SA1
