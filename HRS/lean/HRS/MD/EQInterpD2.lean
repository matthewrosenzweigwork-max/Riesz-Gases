import HRS.MD.EQInterpProj
import HRS.MD.EQInterpCb

/-!
# EQ-INTERP packet, part 6: the `d₂` clause (frequency cut-off `P_R` and `C_b²` composition; TeX L4149-4158)

* `tail_sq`, `sq_norm_sub_cutoff_le`: `‖w - P_R w‖²_{𝒳_m} ≤ R^{-2(m-q)} sup_t ‖w^t‖²_{E_q}`;
* `d2_interp`: for laws `μ, ν` on `𝒳_{m,T}` with `∫ qSq q ≤ A` and `d₂^{𝒳_{m₁}}(e_*μ, e_*ν) ≤ ε`,
  `d₂^{𝒳_m}(μ, ν) ≤ 2 R^{-(m-q)}(1+A) + R^{2(m₁-m)} ε` for every `R ≥ 1` (`P:eq:stationary-smooth-projection`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ}

theorem exists_max_norm {m T : ℝ} (hT : 0 ≤ T) (z : PathSpace d m T) :
    ∃ t₀ : Set.Icc (0 : ℝ) T, ‖z‖ ≤ ‖z.at' t₀‖ := by
  have hne : (Set.Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, hT⟩
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => ‖z.at' t‖ :=
    (show Continuous fun t : Set.Icc (0 : ℝ) T => z.at' t from
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from z).continuous).norm
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := hne.to_subtype
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcont.continuousOn
  refine ⟨t₀, (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => ?_⟩
  exact ht₀ (Set.mem_univ t)

theorem tail_sq {m q R : ℝ} (hq : q ≤ m) (hR : 1 ≤ R) (F G : NegSobolev d m)
    (hG : ∀ k, NegSobolev.coord G k = if Lattice.jp k.1 ≤ R then NegSobolev.coord F k else 0) :
    ENNReal.ofReal (‖F - G‖ ^ 2) ≤ ENNReal.ofReal (R ^ (-2 * (m - q))) * ce q F := by
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (F - G)
  rw [h2, ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) h1]
  simp only [ce, HRS.MD.EQ29.coordEnergy]
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  have hsub : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
  rw [hsub, hG k]
  by_cases hk : Lattice.jp k.1 ≤ R
  · simp [hk]
  · rw [if_neg hk, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hjR : R ≤ Lattice.jp k.1 := (not_le.1 hk).le
    have hj := Torus.jp_pos k.1
    have hRpos : 0 < R := by linarith
    set e : ℝ := 2 * (m - q) with he
    have he0 : 0 ≤ e := by rw [he]; linarith
    have hkey : 1 ≤ R ^ (-2 * (m - q)) * Lattice.jp k.1 ^ e := by
      have h1 : R ^ e ≤ Lattice.jp k.1 ^ e := Real.rpow_le_rpow hRpos.le hjR he0
      have h2 : R ^ (-2 * (m - q)) = (R ^ e)⁻¹ := by
        rw [← Real.rpow_neg hRpos.le]; congr 1; rw [he]; ring
      rw [h2]
      have h3 : 0 < R ^ e := Real.rpow_pos_of_pos hRpos _
      rw [inv_mul_eq_div, le_div_iff₀ h3]; linarith
    have hjp : Lattice.jp k.1 ^ (-2 * q) * (Lattice.jp k.1 ^ m) ^ 2 = Lattice.jp k.1 ^ e := by
      rw [Torus.jp_rpow_sq, ← Real.rpow_add hj]; congr 1; rw [he]; ring
    have hf : NegSobolev.fourierCoeff F k = Lattice.jp k.1 ^ m * NegSobolev.coord F k := rfl
    have : R ^ (-2 * (m - q)) * (Lattice.jp k.1 ^ (-2 * q) * NegSobolev.fourierCoeff F k ^ 2) =
        (R ^ (-2 * (m - q)) * Lattice.jp k.1 ^ e) * NegSobolev.coord F k ^ 2 := by
      rw [hf, mul_pow, ← hjp]; ring
    rw [this]
    simp only [sub_zero]
    nlinarith [sq_nonneg (NegSobolev.coord F k)]

theorem sq_norm_sub_cutoff_le {m m₁ T q R : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (hq : q ≤ m) (hR : 1 ≤ R)
    (w : PathSpace d m T) :
    ENNReal.ofReal (‖w - cutoff R m m₁ hR hmm T w‖ ^ 2) ≤
      ENNReal.ofReal (R ^ (-2 * (m - q))) * qSq q w := by
  obtain ⟨t₀, ht₀⟩ := exists_max_norm hT (w - cutoff R m m₁ hR hmm T w)
  have h1 : ((w - cutoff R m m₁ hR hmm T w).at' t₀) = w.at' t₀ - (cutoff R m m₁ hR hmm T w).at' t₀ :=
    rfl
  calc ENNReal.ofReal (‖w - cutoff R m m₁ hR hmm T w‖ ^ 2)
      ≤ ENNReal.ofReal (‖(w - cutoff R m m₁ hR hmm T w).at' t₀‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ht₀ 2)
    _ ≤ ENNReal.ofReal (R ^ (-2 * (m - q))) * ce q (w.at' t₀) := by
        rw [h1]
        exact tail_sq hq hR _ _ (fun k => coord_cutoff hR hmm T w t₀ k)
    _ ≤ _ := by
        gcongr
        exact le_iSup (fun t => ce q (w.at' t)) t₀


theorem abs_diff_cutoff_le {m m₁ T q R : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (hq : q ≤ m) (hR : 1 ≤ R)
    {Φ : PathSpace d m T → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 2) (w : PathSpace d m T) :
    ENNReal.ofReal |Φ w - Φ (cutoff R m m₁ hR hmm T w)| ≤
      ENNReal.ofReal (R ^ (-(m - q))) * (1 + qSq q w) := by
  have hR0 : 0 < R := by linarith
  set v := w - cutoff R m m₁ hR hmm T w with hv
  have hlip : |Φ w - Φ (cutoff R m m₁ hR hmm T w)| ≤ ‖v‖ := cb_lipschitz hΦ _ _
  have hρ0 : 0 < R ^ (-(m - q)) := Real.rpow_pos_of_pos hR0 _
  by_cases hs : qSq q w = ⊤
  · rw [hs]
    simp only [add_top]
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hρ0).ne']
    exact le_top
  · set σ := (qSq q w).toReal with hσ
    have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
    have hsσ : qSq q w = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hs).symm
    have hB := sq_norm_sub_cutoff_le hmm hT hq hR w
    rw [hsσ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR0.le _)] at hB
    have hB' : ‖v‖ ^ 2 ≤ R ^ (-2 * (m - q)) * σ :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg hR0.le _) hσ0)).1 hB
    have hρ2 : (R ^ (-(m - q))) ^ 2 = R ^ (-2 * (m - q)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hR0.le]; congr 1; ring
    have hsq : ‖v‖ ^ 2 ≤ (R ^ (-(m - q)) * (1 + σ)) ^ 2 := by
      rw [mul_pow, hρ2]
      calc ‖v‖ ^ 2 ≤ R ^ (-2 * (m - q)) * σ := hB'
        _ ≤ R ^ (-2 * (m - q)) * (1 + σ) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hR0.le _)
          nlinarith
    have hv1 : ‖v‖ ≤ R ^ (-(m - q)) * (1 + σ) :=
      (abs_le_of_sq_le_sq' hsq (by positivity)).2
    calc ENNReal.ofReal |Φ w - Φ (cutoff R m m₁ hR hmm T w)| ≤ ENNReal.ofReal (R ^ (-(m - q)) * (1 + σ)) :=
          ENNReal.ofReal_le_ofReal (hlip.trans hv1)
      _ = ENNReal.ofReal (R ^ (-(m - q))) * (1 + qSq q w) := by
          rw [ENNReal.ofReal_mul hρ0.le, hsσ, ENNReal.ofReal_add (by norm_num) hσ0]; simp

theorem tail_integral {m m₁ T q R A : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (hq : q ≤ m) (hR : 1 ≤ R)
    (hA : 0 ≤ A) (μ : Measure (PathSpace d m T)) [IsProbabilityMeasure μ]
    (hμ : ∫⁻ w, qSq q w ∂μ ≤ ENNReal.ofReal A) {Φ : PathSpace d m T → ℝ}
    (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 2) :
    ∫ w, |Φ w - Φ (cutoff R m m₁ hR hmm T w)| ∂μ ≤ R ^ (-(m - q)) * (1 + A) := by
  have hR0 : 0 < R := by linarith
  have hρ0 : 0 < R ^ (-(m - q)) := Real.rpow_pos_of_pos hR0 _
  have hcont : Continuous fun w => |Φ w - Φ (cutoff R m m₁ hR hmm T w)| :=
    (hΦ.1.continuous.sub (hΦ.1.continuous.comp (cutoff R m m₁ hR hmm T).continuous)).abs
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w => abs_nonneg _)
    hcont.aestronglyMeasurable]
  have h1 : ∫⁻ w, ENNReal.ofReal |Φ w - Φ (cutoff R m m₁ hR hmm T w)| ∂μ ≤
      ENNReal.ofReal (R ^ (-(m - q))) * (1 + ENNReal.ofReal A) := by
    calc ∫⁻ w, ENNReal.ofReal |Φ w - Φ (cutoff R m m₁ hR hmm T w)| ∂μ
        ≤ ∫⁻ w, ENNReal.ofReal (R ^ (-(m - q))) * (1 + qSq q w) ∂μ :=
          lintegral_mono fun w => abs_diff_cutoff_le hmm hT hq hR hΦ w
      _ = ENNReal.ofReal (R ^ (-(m - q))) * (1 + ∫⁻ w, qSq q w ∂μ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left measurable_const]
          simp
      _ ≤ _ := by gcongr
  have h2 : ENNReal.ofReal (R ^ (-(m - q))) * (1 + ENNReal.ofReal A) =
      ENNReal.ofReal (R ^ (-(m - q)) * (1 + A)) := by
    rw [ENNReal.ofReal_mul hρ0.le, ENNReal.ofReal_add (by norm_num) hA]; simp
  rw [h2] at h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

theorem smoothDist_nonneg' {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (P Q : Measure B) : 0 ≤ smoothDist 2 P Q :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem smoothDist_bdd {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    BddAbove (Set.range fun Φ : CbUnitBall B 2 => |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q|) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨Φ, rfl⟩
  have hb : ∀ (ρ : Measure B) [IsProbabilityMeasure ρ], |∫ z, Φ.1 z ∂ρ| ≤ 1 := by
    intro ρ _
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := Φ.1) (C := 1)
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using cb_abs_le_one Φ.2 z)
    simpa using this
  have h1 := hb P
  have h2 := hb Q
  calc |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q| ≤ |∫ z, Φ.1 z ∂P| + |∫ z, Φ.1 z ∂Q| := abs_sub _ _
    _ ≤ 2 := by linarith

theorem smoothDist_le_two {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : smoothDist 2 P Q ≤ 2 := by
  refine Real.iSup_le (fun Φ => ?_) (by norm_num)
  have hb : ∀ (ρ : Measure B) [IsProbabilityMeasure ρ], |∫ z, Φ.1 z ∂ρ| ≤ 1 := by
    intro ρ _
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := Φ.1) (C := 1)
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using cb_abs_le_one Φ.2 z)
    simpa using this
  have h1 := hb P
  have h2 := hb Q
  calc |∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q| ≤ |∫ z, Φ.1 z ∂P| + |∫ z, Φ.1 z ∂Q| := abs_sub _ _
    _ ≤ 2 := by linarith


/-- `d₂` interpolation (TeX `P:eq:stationary-smooth-projection`, L4155-4158). -/
theorem d2_interp {m m₁ T q R A ε : ℝ} (hmm : m ≤ m₁) (hT : 0 ≤ T) (hq : q ≤ m) (hR : 1 ≤ R)
    (hA : 0 ≤ A) (μ ν : Measure (PathSpace d m T)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∫⁻ w, qSq q w ∂μ ≤ ENNReal.ofReal A) (hν : ∫⁻ w, qSq q w ∂ν ≤ ENNReal.ofReal A)
    (hε : smoothDist 2 (μ.map (epath hmm T)) (ν.map (epath hmm T)) ≤ ε) :
    smoothDist 2 μ ν ≤ 2 * (R ^ (-(m - q)) * (1 + A)) + (R ^ (m₁ - m)) ^ 2 * ε := by
  have hR0 : 0 < R := by linarith
  have hem : Measurable (epath hmm T : PathSpace d m T → PathSpace d m₁ T) :=
    (epath hmm T).continuous.measurable
  haveI : IsProbabilityMeasure (μ.map (epath hmm T)) := (Measure.isProbabilityMeasure_map_iff hem.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (ν.map (epath hmm T)) := (Measure.isProbabilityMeasure_map_iff hem.aemeasurable).2 inferInstance
  have hε0 : 0 ≤ ε := (smoothDist_nonneg' _ _).trans hε
  have hΛ1 : 1 ≤ R ^ (m₁ - m) := Real.one_le_rpow hR (sub_nonneg.2 hmm)
  have hρ0 : 0 < R ^ (-(m - q)) := Real.rpow_pos_of_pos hR0 _
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨Φ, hΦ⟩ := Φ
  have hΦc : Continuous Φ := hΦ.1.continuous
  set P := cutoff R m m₁ hR hmm T with hP
  have hPc : Continuous P := P.continuous
  have hint : ∀ (ρ : Measure (PathSpace d m T)) [IsProbabilityMeasure ρ] (f : PathSpace d m T → ℝ),
      Continuous f → (∀ x, |f x| ≤ 1) → Integrable f ρ := fun ρ _ f hf hb =>
    Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hb x)
  have hi1 : ∀ (ρ : Measure (PathSpace d m T)) [IsProbabilityMeasure ρ], Integrable Φ ρ :=
    fun ρ _ => hint ρ Φ hΦc (cb_abs_le_one hΦ)
  have hi2 : ∀ (ρ : Measure (PathSpace d m T)) [IsProbabilityMeasure ρ], Integrable (fun w => Φ (P w)) ρ :=
    fun ρ _ => hint ρ _ (hΦc.comp hPc) (fun x => cb_abs_le_one hΦ _)
  -- tails
  have htail : ∀ (ρ : Measure (PathSpace d m T)) [IsProbabilityMeasure ρ],
      ∫⁻ w, qSq q w ∂ρ ≤ ENNReal.ofReal A →
      |∫ w, Φ w ∂ρ - ∫ w, Φ (P w) ∂ρ| ≤ R ^ (-(m - q)) * (1 + A) := by
    intro ρ _ hρ
    rw [← integral_sub (hi1 ρ) (hi2 ρ)]
    exact (abs_integral_le_integral_abs).trans (tail_integral hmm hT hq hR hA ρ hρ hΦ)
  -- composition
  set Λ := R ^ (m₁ - m) with hΛ
  have hΨ := cb_comp (projPath R m m₁ hR hmm T) hΛ1 (norm_projPath_le hR hmm T) hΦ
  have hΨle : |∫ y, (Λ ^ 2)⁻¹ * Φ (projPath R m m₁ hR hmm T y) ∂(μ.map (epath hmm T)) -
      ∫ y, (Λ ^ 2)⁻¹ * Φ (projPath R m m₁ hR hmm T y) ∂(ν.map (epath hmm T))| ≤ ε := by
    refine le_trans ?_ hε
    exact le_ciSup (f := fun Φ' : CbUnitBall (PathSpace d m₁ T) 2 =>
      |∫ z, Φ'.1 z ∂(μ.map (epath hmm T)) - ∫ z, Φ'.1 z ∂(ν.map (epath hmm T))|)
      (smoothDist_bdd _ _) ⟨_, hΨ⟩
  have hmapint : ∀ ρ : Measure (PathSpace d m T),
      ∫ y, (Λ ^ 2)⁻¹ * Φ (projPath R m m₁ hR hmm T y) ∂(ρ.map (epath hmm T)) =
        (Λ ^ 2)⁻¹ * ∫ w, Φ (P w) ∂ρ := by
    intro ρ
    have hc : Continuous fun y => (Λ ^ 2)⁻¹ * Φ (projPath R m m₁ hR hmm T y) :=
      continuous_const.mul (hΦc.comp (projPath R m m₁ hR hmm T).continuous)
    rw [integral_map hem.aemeasurable hc.aestronglyMeasurable, integral_const_mul]
    rfl
  rw [hmapint μ, hmapint ν, ← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < (Λ ^ 2)⁻¹)] at hΨle
  have hmid : |∫ w, Φ (P w) ∂μ - ∫ w, Φ (P w) ∂ν| ≤ Λ ^ 2 * ε := by
    have : 0 < Λ ^ 2 := by positivity
    rw [inv_mul_le_iff₀ this] at hΨle
    exact hΨle
  have t1 := htail μ hμ
  have t2 := htail ν hν
  have e1 := abs_le.1 t1
  have e2 := abs_le.1 t2
  have e3 := abs_le.1 hmid
  exact abs_le.2 ⟨by linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2],
    by linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]⟩

end HRS.MD.EQInterp
