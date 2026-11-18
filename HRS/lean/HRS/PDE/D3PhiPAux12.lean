import HRS.PDE.D3PhiPAux11

/-!
# D3PHIP, helper 12: the proof of `d3phi_approx_Lp`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3pp_approx_Lp (q : Measure (Torus n)) [IsProbabilityMeasure q] {ρ : Torus n → ℝ}
    (hρc : Continuous ρ) (hρ : ∀ x, 0 < ρ x) {ν : Measure (Torus n)} [IsProbabilityMeasure ν]
    (hac : ν ≪ q) {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hfin : eLpNorm (ν.rnDeriv q) (ENNReal.ofReal p₀) q < ⊤) :
    ∃ g : ℕ → Torus n → ℝ, (∀ k, Torus.IsSmooth (g k)) ∧ (∀ k x, 0 < g k x) ∧
      (∀ k, ∫ x, g k x * ρ x ∂q = 1) ∧
      (∀ φ : Torus n → ℝ, Continuous φ →
        Tendsto (fun k => ∫ x, g k x * ρ x * φ x ∂q) atTop (𝓝 (∫ x, φ x ∂ν))) ∧
      Tendsto (fun k => eLpNorm (fun x => ENNReal.ofReal (g k x * ρ x)) (ENNReal.ofReal p₀) q) atTop
        (𝓝 (eLpNorm (ν.rnDeriv q) (ENNReal.ofReal p₀) q)) := by
  set P0 : ℝ≥0∞ := ENNReal.ofReal p₀ with hP0
  have hP1 : 1 ≤ P0 := by rw [hP0]; exact ENNReal.one_le_ofReal.2 hp₀.le
  have hPt : P0 ≠ ⊤ := ENNReal.ofReal_ne_top
  set H₀ : Torus n → ℝ := fun x => (ν.rnDeriv q x).toReal with hH₀
  have hH₀m : Measurable H₀ := (Measure.measurable_rnDeriv ν q).ennreal_toReal
  have hH₀0 : ∀ x, 0 ≤ H₀ x := fun x => ENNReal.toReal_nonneg
  have hrn_m : AEStronglyMeasurable (ν.rnDeriv q) q := (Measure.measurable_rnDeriv ν q).aestronglyMeasurable
  have hnormeq : eLpNorm (ν.rnDeriv q) P0 q = eLpNorm H₀ P0 q := by
    refine eLpNorm_congr_enorm_ae hrn_m hH₀m.aestronglyMeasurable ?_
    filter_upwards [Measure.rnDeriv_lt_top ν q] with x hx
    simp only [hH₀, enorm_eq_self, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have hH₀L : MemLp H₀ P0 q := by rw [memLp_iff, ← hnormeq]; exact hfin
  -- bounds on ρ
  obtain ⟨R0, hR0⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hρc.continuousOn
  set R : ℝ := max R0 0 with hR
  have hR0' : 0 ≤ R := le_max_right _ _
  have hρR : ∀ x, ρ x ≤ R := fun x => by
    have := hR0 x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  obtain ⟨x0, -, hx0⟩ := (isCompact_univ (X := Torus n)).exists_isMinOn ⟨(0 : Torus n), trivial⟩
    hρc.continuousOn
  set ρm : ℝ := ρ x0 with hρm
  have hρm0 : 0 < ρm := hρ x0
  have hρmin : ∀ x, ρm ≤ ρ x := fun x => hx0 (Set.mem_univ x)
  -- f₀
  set f₀ : Torus n → ℝ := fun x => H₀ x / ρ x with hf₀
  have hf₀m : Measurable f₀ := hH₀m.div hρc.measurable
  have hf₀0 : ∀ x, 0 ≤ f₀ x := fun x => div_nonneg (hH₀0 x) (hρ x).le
  have hf₀L : MemLp f₀ P0 q := by
    refine MemLp.of_le_mul (c := 1 / ρm) hH₀L hf₀m.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf₀0 x), abs_of_nonneg (hH₀0 x)]
    show H₀ x / ρ x ≤ 1 / ρm * H₀ x
    calc H₀ x / ρ x ≤ H₀ x / ρm := div_le_div_of_nonneg_left (hH₀0 x) hρm0 (hρmin x)
      _ = 1 / ρm * H₀ x := by ring
  have hf₀ρ : ∀ x, f₀ x * ρ x = H₀ x := fun x => by
    simp only [hf₀]; field_simp [(hρ x).ne']
  -- approximants
  set ε : ℕ → ℝ := fun k => (1 / ((k : ℝ) + 1)) / (2 * (R + 1)) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hε]; positivity
  have hex : ∀ k, ∃ g : Torus n → ℝ, Torus.IsSmooth g ∧ (∀ x, 0 < g x) ∧
      eLpNorm (fun x => g x - f₀ x) P0 q ≤ ENNReal.ofReal (ε k) := fun k =>
    d3pp_smooth_pos_approx q hP1 hPt hf₀L hf₀0 (hεpos k)
  choose gt hgts hgtpos hgtd using hex
  have hεR : ∀ k, R * ε k ≤ 1 / 2 := fun k => by
    simp only [hε]
    have hk : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [← div_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hR0' (sub_nonneg.2 hk), hR0']
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simp only [hε]
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using this.div_const (2 * (R + 1))
  -- finiteness of the norm of f₀
  set a : ℝ := (eLpNorm f₀ P0 q).toReal with ha
  have haf : eLpNorm f₀ P0 q = ENNReal.ofReal a := by
    rw [ha, ENNReal.ofReal_toReal hf₀L.ne]
  have hεle1 : ∀ k, ε k ≤ 1 := fun k => by
    have := hεR k
    simp only [hε]
    have hk : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc _ ≤ 1 / ((k : ℝ) + 1) := div_le_self (by positivity) (by linarith)
      _ ≤ 1 := hk
  have hgtc : ∀ k, Continuous (gt k) := fun k => d1c_continuous_of_isSmooth (hgts k)
  -- eLpNorm bound on gt
  have hgtn : ∀ k, eLpNorm (gt k) P0 q ≤ ENNReal.ofReal (a + 1) := fun k => by
    have h1 : gt k = f₀ + (fun x => gt k x - f₀ x) := by funext x; simp
    rw [h1]
    refine (eLpNorm_add_le hP1).trans ?_
    rw [haf]
    calc _ ≤ ENNReal.ofReal a + ENNReal.ofReal (ε k) := add_le_add le_rfl (hgtd k)
      _ = ENNReal.ofReal (a + ε k) := (ENNReal.ofReal_add (by positivity) (hεpos k).le).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [hεle1 k])
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  -- normalising constants
  set m : ℕ → ℝ := fun k => ∫ x, gt k x * ρ x ∂q with hm
  have hf₀int : ∫ x, f₀ x * ρ x ∂q = 1 := by
    have : ∫ x, f₀ x * ρ x ∂q = ∫ x, H₀ x ∂q := integral_congr_ae (ae_of_all _ hf₀ρ)
    rw [this, hH₀, Measure.integral_toReal_rnDeriv hac]
    simp
  have hH₀int : Integrable H₀ q := Measure.integrable_toReal_rnDeriv
  have hmk : ∀ k, |m k - 1| ≤ R * ε k := fun k => by
    have hint1 : Integrable (fun x => gt k x * ρ x) q := d3a_hint q ((hgtc k).mul hρc)
    have hint2 : Integrable (fun x => f₀ x * ρ x) q := hH₀int.congr (ae_of_all _ fun x => (hf₀ρ x).symm)
    have e : m k - 1 = ∫ x, (gt k x - f₀ x) * ρ x ∂q := by
      have e0 : m k - 1 = (∫ x, gt k x * ρ x ∂q) - ∫ x, f₀ x * ρ x ∂q := by rw [hf₀int]
      rw [e0, ← integral_sub hint1 hint2]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e, ← Real.norm_eq_abs]
    have hFm : AEStronglyMeasurable (fun x => (gt k x - f₀ x) * ρ x) q :=
      (((hgtc k).measurable.sub hf₀m).mul hρc.measurable).aestronglyMeasurable
    have hbd : eLpNorm (fun x => (gt k x - f₀ x) * ρ x) P0 q ≤ ENNReal.ofReal R * ENNReal.ofReal (ε k) := by
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := fun x => gt k x - f₀ x) (c := R) hFm
        (ae_of_all _ fun x => ?_) P0).trans (by gcongr; exact hgtd k)
      rw [norm_mul, Real.norm_eq_abs (ρ x), abs_of_pos (hρ x), mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa using hρR x) (norm_nonneg _)
    have hfinF : eLpNorm (fun x => (gt k x - f₀ x) * ρ x) P0 q ≠ ⊤ :=
      (hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
    refine (d3pp_int_le hFm hP1 hfinF).trans ?_
    rw [← ENNReal.ofReal_mul hR0'] at hbd
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd).trans (by
      rw [ENNReal.toReal_ofReal (by positivity)])
  have hm_half : ∀ k, 1 / 2 ≤ m k := fun k => by
    have := hmk k
    rw [abs_le] at this
    linarith [this.1, hεR k]
  have hmpos : ∀ k, 0 < m k := fun k => lt_of_lt_of_le (by norm_num) (hm_half k)
  -- distance to H₀
  set Dk : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x) P0 q with hDk
  set C : ℝ := R * (2 * R * (a + 1) + 1) with hC
  have hDle : ∀ k, Dk k ≤ ENNReal.ofReal (C * ε k) := fun k => by
    have hpt : ∀ x, (m k)⁻¹ * gt k x * ρ x - H₀ x =
        ρ x * (((m k)⁻¹ - 1) * gt k x + (gt k x - f₀ x)) := fun x => by
      rw [← hf₀ρ x]; ring
    have hmeas : AEStronglyMeasurable (fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x) q :=
      ((((hgtc k).measurable.const_mul _).mul hρc.measurable).sub hH₀m).aestronglyMeasurable
    have h1 : Dk k ≤ ENNReal.ofReal R * eLpNorm (fun x => ((m k)⁻¹ - 1) * gt k x + (gt k x - f₀ x)) P0 q := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas (ae_of_all _ fun x => ?_) P0
      rw [hpt x, norm_mul, Real.norm_eq_abs (ρ x), abs_of_pos (hρ x)]
      exact mul_le_mul_of_nonneg_right (hρR x) (norm_nonneg _)
    have h2 : eLpNorm (fun x => ((m k)⁻¹ - 1) * gt k x + (gt k x - f₀ x)) P0 q ≤
        ENNReal.ofReal (|(m k)⁻¹ - 1| * (a + 1)) + ENNReal.ofReal (ε k) := by
      refine (eLpNorm_add_le (f := fun x => ((m k)⁻¹ - 1) * gt k x)
        (g := fun x => gt k x - f₀ x) hP1).trans (add_le_add ?_ (hgtd k))
      have : (fun x => ((m k)⁻¹ - 1) * gt k x) = ((m k)⁻¹ - 1) • gt k := by funext x; simp
      rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
      rw [ENNReal.ofReal_mul (abs_nonneg _)]
      exact by gcongr; exact hgtn k
    have h3 : |(m k)⁻¹ - 1| ≤ 2 * R * ε k := by
      have hmk' := hmk k
      have : (m k)⁻¹ - 1 = (1 - m k) / m k := by field_simp [(hmpos k).ne']
      rw [this, abs_div, abs_of_pos (hmpos k), abs_sub_comm, div_le_iff₀ (hmpos k)]
      have := hm_half k
      nlinarith [abs_nonneg (m k - 1), hmk']
    have h4 : ENNReal.ofReal (|(m k)⁻¹ - 1| * (a + 1)) + ENNReal.ofReal (ε k) ≤
        ENNReal.ofReal ((2 * R * (a + 1) + 1) * ε k) := by
      rw [← ENNReal.ofReal_add (by positivity) (hεpos k).le]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ a + 1)]
    calc Dk k ≤ _ := h1
      _ ≤ ENNReal.ofReal R * ENNReal.ofReal ((2 * R * (a + 1) + 1) * ε k) :=
          by gcongr; exact h2.trans h4
      _ = ENNReal.ofReal (C * ε k) := by
          rw [← ENNReal.ofReal_mul hR0']; congr 1; simp only [hC]; ring
  have hD0 : Tendsto Dk atTop (𝓝 0) := by
    have h : Tendsto (fun k => ENNReal.ofReal (C * ε k)) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal (hε0.const_mul C))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) hDle
  -- the final sequence
  refine ⟨fun k x => (m k)⁻¹ * gt k x, fun k => d3b_smooth_const_mul (hgts k), fun k x =>
    mul_pos (inv_pos.2 (hmpos k)) (hgtpos k x), fun k => ?_, ?_, ?_⟩
  · simp only [mul_assoc]
    rw [integral_const_mul]
    have : ∫ x, gt k x * ρ x ∂q = m k := rfl
    rw [this, inv_mul_cancel₀ (hmpos k).ne']
  · -- narrow convergence
    intro φ hφ
    obtain ⟨M0, hM0⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hφ.continuousOn
    set M : ℝ := max M0 0 with hM
    have hM0' : 0 ≤ M := le_max_right _ _
    have hφM : ∀ x, ‖φ x‖ ≤ M := fun x => (hM0 x (Set.mem_univ x)).trans (le_max_left _ _)
    have hconv : ∫ x, φ x ∂ν = ∫ x, H₀ x * φ x ∂q := (integral_toReal_rnDeriv_mul hac).symm
    have hHφ : Integrable (fun x => H₀ x * φ x) q :=
      (hH₀int.const_mul M).mono' (hH₀m.mul hφ.measurable).aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hH₀0 x), mul_comm]
        exact mul_le_mul_of_nonneg_right (by simpa using hφM x) (hH₀0 x))
    have hC0 : 0 ≤ C := by simp only [hC]; positivity
    have hbound : ∀ k, ‖∫ x, (m k)⁻¹ * gt k x * ρ x * φ x ∂q - ∫ x, φ x ∂ν‖ ≤ M * (C * ε k) := fun k => by
      have hint1 : Integrable (fun x => (m k)⁻¹ * gt k x * ρ x * φ x) q :=
        d3a_hint q ((((hgtc k).const_mul _).mul hρc).mul hφ)
      have e : ∫ x, (m k)⁻¹ * gt k x * ρ x * φ x ∂q - ∫ x, φ x ∂ν =
          ∫ x, ((m k)⁻¹ * gt k x * ρ x - H₀ x) * φ x ∂q := by
        rw [hconv, ← integral_sub hint1 hHφ]
        exact integral_congr_ae (ae_of_all _ fun x => by ring)
      rw [e]
      have hFm : AEStronglyMeasurable (fun x => ((m k)⁻¹ * gt k x * ρ x - H₀ x) * φ x) q :=
        (((((hgtc k).measurable.const_mul _).mul hρc.measurable).sub hH₀m).mul hφ.measurable).aestronglyMeasurable
      have hDm : AEStronglyMeasurable (fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x) q :=
        ((((hgtc k).measurable.const_mul _).mul hρc.measurable).sub hH₀m).aestronglyMeasurable
      have hbd : eLpNorm (fun x => ((m k)⁻¹ * gt k x * ρ x - H₀ x) * φ x) P0 q ≤
          ENNReal.ofReal M * ENNReal.ofReal (C * ε k) := by
        refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x) (c := M) hFm
          (ae_of_all _ fun x => ?_) P0).trans (by gcongr; exact hDle k)
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hφM x) (norm_nonneg _)
      have hfinF : eLpNorm (fun x => ((m k)⁻¹ * gt k x * ρ x - H₀ x) * φ x) P0 q ≠ ⊤ :=
        (hbd.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)).ne
      refine (d3pp_int_le hFm hP1 hfinF).trans ?_
      rw [← ENNReal.ofReal_mul hM0'] at hbd
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd).trans (by
        rw [ENNReal.toReal_ofReal (by have := hεpos k; positivity)])
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun k => M * (C * ε k)) atTop (𝓝 0) := by
      simpa using (hε0.const_mul C).const_mul M
    exact squeeze_zero (fun _ => norm_nonneg _) hbound h0
  · -- convergence of the norms
    have hGc : ∀ k, Continuous fun x => (m k)⁻¹ * gt k x * ρ x := fun k =>
      ((hgtc k).const_mul _).mul hρc
    have hG0 : ∀ k x, 0 ≤ (m k)⁻¹ * gt k x * ρ x := fun k x =>
      mul_nonneg (mul_nonneg (inv_pos.2 (hmpos k)).le (hgtpos k x).le) (hρ x).le
    have hGn : ∀ k, eLpNorm (fun x => ENNReal.ofReal ((m k)⁻¹ * gt k x * ρ x)) P0 q =
        eLpNorm (fun x => (m k)⁻¹ * gt k x * ρ x) P0 q := fun k =>
      eLpNorm_congr_enorm_ae
        ((ENNReal.measurable_ofReal.comp (hGc k).measurable).aestronglyMeasurable)
        (hGc k).aestronglyMeasurable
        (ae_of_all _ fun x => by
          simp only [enorm_eq_self, Real.enorm_eq_ofReal (hG0 k x)])
    simp_rw [hGn]
    rw [hnormeq]
    have hb : eLpNorm H₀ P0 q ≠ ⊤ := hH₀L.ne
    have hup : ∀ k, eLpNorm (fun x => (m k)⁻¹ * gt k x * ρ x) P0 q ≤ eLpNorm H₀ P0 q + Dk k := fun k => by
      have h1 : (fun x => (m k)⁻¹ * gt k x * ρ x) = H₀ + (fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x) := by
        funext x; simp
      rw [h1]
      exact eLpNorm_add_le hP1
    have hlo : ∀ k, eLpNorm H₀ P0 q - Dk k ≤ eLpNorm (fun x => (m k)⁻¹ * gt k x * ρ x) P0 q := fun k => by
      rw [tsub_le_iff_right]
      have h1 : H₀ = (fun x => (m k)⁻¹ * gt k x * ρ x) - (fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x) := by
        funext x; simp
      calc eLpNorm H₀ P0 q = eLpNorm ((fun x => (m k)⁻¹ * gt k x * ρ x) -
            (fun x => (m k)⁻¹ * gt k x * ρ x - H₀ x)) P0 q := by rw [← h1]
        _ ≤ _ := eLpNorm_sub_le hP1
    have hl : Tendsto (fun k => eLpNorm H₀ P0 q - Dk k) atTop (𝓝 (eLpNorm H₀ P0 q)) := by
      simpa using ENNReal.Tendsto.sub tendsto_const_nhds hD0 (Or.inl hb)
    have hu : Tendsto (fun k => eLpNorm H₀ P0 q + Dk k) atTop (𝓝 (eLpNorm H₀ P0 q)) := by
      simpa using tendsto_const_nhds.add hD0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu hlo hup

end HRS
