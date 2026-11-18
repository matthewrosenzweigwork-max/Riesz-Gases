import HRS.Energy.Commutator.RenormStjField

/-!
# Route S, packet STJ: the field term after the pick of the radius (Young, powers of `r`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem measurable_fieldF_uncurry {N : ℕ} (X : Fin N → Torus d) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (i : Fin N) : Measurable fun p : ℝ × Torus d => fieldF p.1 X μ i p.2 := by
  unfold fieldF
  have hs : Measurable fun p : ℝ × Torus d => ∑ j ∈ Finset.univ.erase i, SliceAux.sgv p.1 (p.2 - X j) :=
    Finset.measurable_sum _ fun j _ =>
      SliceAux.measurable_sgv.comp (measurable_fst.prodMk (measurable_snd.sub_const (X j)))
  have h1 : Measurable fun p : ℝ × Torus d => (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, SliceAux.sgv p.1 (p.2 - X j) :=
    hs.const_smul (1 / (N : ℝ))
  have h2 : Measurable fun p : ℝ × Torus d => ∫ y, SliceAux.sgv p.1 (p.2 - y) ∂μ := by
    have : StronglyMeasurable (fun q : (ℝ × Torus d) × Torus d => SliceAux.sgv q.1.1 (q.1.2 - q.2)) :=
      (SliceAux.measurable_sgv.comp (measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd))).stronglyMeasurable
    exact (this.integral_prod_right' (ν := μ)).measurable
  exact h1.sub h2

theorem cflm_lintegral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ ρ : ℝ, 0 < ρ →
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l ρ) ≤
        ENNReal.ofReal (Cp * ρ ^ ((d : ℝ) - 2 - s)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := cfl_stieltjes hd hs0 hs hsd
  refine ⟨Cp, hCp0, fun ρ hρ => ?_⟩
  obtain ⟨hint, hle⟩ := hCp ρ hρ
  have h1 : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l ρ) =
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s) * cfl d l ρ) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    rw [← cfl_eq_cflm hd hl' hρ, ← ENNReal.ofReal_mul (Real.rpow_nonneg hl'.le _)]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint]
  · exact ENNReal.ofReal_le_ofReal hle
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun l hl => ?_)
    have hl' : (0 : ℝ) < l := hl
    exact mul_nonneg (Real.rpow_nonneg hl'.le _) (cfl_pos hd hl' hρ).le

/-- the local field energy, `l`-integrated with the weight `l^{-β}` -/
def Yloc (d : ℕ) (s r : ℝ) (a : Torus d) (F : ℝ → Torus d → Euc d) : ℝ≥0∞ :=
  ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
    ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0)

theorem T_alg_B {r η κd L N : ℝ} (hN : 0 < N) (hr : 0 < r) (hηr : η ≤ r) (hη : 0 ≤ η)
    (hL : 0 ≤ L) (hκd : 0 ≤ κd) :
    L * η * (2 * (4 / r) ^ d) * (1 / (2 * (1 * r ^ (1 - (d : ℝ)) / N)) * κd) ≤
      L * ((4 ^ d * κd) * N) := by
  have hu : r ^ (1 - (d : ℝ)) * r ^ d = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr]; simp
  have hup : 0 < r ^ (1 - (d : ℝ)) := Real.rpow_pos_of_pos hr _
  have hrd : 0 < r ^ d := pow_pos hr d
  have e1 : L * η * (2 * (4 / r) ^ d) * (1 / (2 * (1 * r ^ (1 - (d : ℝ)) / N)) * κd) =
      (η / (r ^ (1 - (d : ℝ)) * r ^ d)) * (L * 4 ^ d * κd * N) := by
    rw [div_pow]; field_simp
  rw [e1, hu]
  have hK : 0 ≤ L * 4 ^ d * κd * N := by positivity
  have : η / r ≤ 1 := (div_le_one hr).mpr hηr
  calc η / r * (L * 4 ^ d * κd * N) ≤ 1 * (L * 4 ^ d * κd * N) :=
        mul_le_mul_of_nonneg_right this hK
    _ = L * ((4 ^ d * κd) * N) := by ring

theorem ofReal_comb {a b c e f g : ℝ} (Y : ℝ≥0∞) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hf : 0 ≤ f) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * ENNReal.ofReal e +
        ENNReal.ofReal f * (ENNReal.ofReal g * Y))) =
      ENNReal.ofReal (a * b * (c * e)) + ENNReal.ofReal (a * b * (f * g)) * Y := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hg : ENNReal.ofReal (a * b * (f * g)) =
      ENNReal.ofReal a * ENNReal.ofReal b * (ENNReal.ofReal f * ENNReal.ofReal g) := by
    rw [ENNReal.ofReal_mul hab, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hf]
  have he : ENNReal.ofReal (a * b * (c * e)) =
      ENNReal.ofReal a * ENNReal.ofReal b * (ENNReal.ofReal c * ENNReal.ofReal e) := by
    rw [ENNReal.ofReal_mul hab, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hc]
  rw [hg, he]; ring

theorem T_i_total (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ KT1 KT2 : ℝ, 0 ≤ KT1 ∧ 0 ≤ KT2 ∧ ∀ {N : ℕ}, 0 < N → ∀ {r η L : ℝ}, 0 < r → r ≤ 1 / 8 →
      r / 2 ≤ η → η < r → 0 ≤ L → ∀ {a : Torus d} {F : ℝ → Torus d → Euc d},
      (Measurable fun p : ℝ × Torus d => F p.1 p.2) →
      ((∫⁻ x, Phi d s r F x ∂(chC d η a)) *
        ((volume : Measure (Euc d)).toSphere univ * ENNReal.ofReal ((r / 2) ^ d)) ≤
        ∫⁻ x : Torus d, (if r / 2 < KernelGrad.tdist x a ∧ KernelGrad.tdist x a < r then Phi d s r F x else 0)) →
      ∫⁻ l in Ioi (0 : ℝ), Tmaj d s r η L a F l ≤
        ENNReal.ofReal (L * (KT1 * r ^ (-s) / N)) + ENNReal.ofReal (L * KT2 * N) * Yloc d s r a F := by
  obtain ⟨Cp, hCp0, hCp⟩ := cflm_lintegral hd hs0 hs hsd
  set ω : ℝ := (volume : Measure (Euc d)).real (Metric.ball 0 1) with hω
  have hω0 : 0 < ω := ball_real_pos hd
  have hκd0 : 0 < SmearAux.kappa d := SmearAux.kappa_pos d hd
  refine ⟨4 ^ (2 + s) * ω * Cp, 4 ^ d * SmearAux.kappa d, by positivity, by positivity, ?_⟩
  intro N hN r η L hr hr8 hrη hηr hL a F hF hpick
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hη0 : 0 < η := by linarith
  have hup : 0 < r ^ (1 - (d : ℝ)) := Real.rpow_pos_of_pos hr _
  set κ : ℝ := 1 * r ^ (1 - (d : ℝ)) / N with hκ
  have hκ0 : 0 < κ := by positivity
  have h1 := T_l_bound hd s hr hr8 hrη hηr (L := L) hF hpick
  have h2 := Phi_B_le hd s hr hr8 hκ0 a hF
  have hI := hCp (r / 4) (by positivity)
  have hZ : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
        (∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0)) ≤
      ENNReal.ofReal (SmearAux.kappa d) * Yloc d s r a F := by
    unfold Yloc
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    have hc : cflm d l (r / 4) ≤ SmearAux.kappa d := by
      rw [← cfl_eq_cflm hd hl' (by positivity)]; exact cfl_le_kappa hd hl' (by positivity)
    calc ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (cflm d l (r / 4)) *
          (∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0))
        ≤ ENNReal.ofReal (l ^ (-bexp d s)) * ENNReal.ofReal (SmearAux.kappa d) *
          (∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then ENNReal.ofReal (‖F l x‖ ^ 2) else 0)) :=
        mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hc)) le_rfl
      _ = _ := by ring
  have hvb : (volume : Measure (Euc d)) (Metric.ball 0 1) = ENNReal.ofReal ω :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hc1 : ENNReal.ofReal (κ / 2) * (ENNReal.ofReal (r ^ d) * (volume : Measure (Euc d)) (Metric.ball 0 1)) =
      ENNReal.ofReal (κ / 2 * (r ^ d * ω)) := by
    rw [hvb, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  have hcomb := ofReal_comb (a := L * η) (b := 2 * (4 / r) ^ d) (c := κ / 2 * (r ^ d * ω))
    (e := Cp * (r / 4) ^ ((d : ℝ) - 2 - s)) (f := 1 / (2 * κ)) (g := SmearAux.kappa d)
    (Yloc d s r a F) (by positivity) (by positivity) (by positivity) (by positivity)
  calc ∫⁻ l in Ioi (0 : ℝ), Tmaj d s r η L a F l
      ≤ ENNReal.ofReal (L * η) * (ENNReal.ofReal (2 * (4 / r) ^ d) *
          ∫⁻ x : Torus d, (if KernelGrad.tdist x a < r then Phi d s r F x else 0)) := h1
    _ ≤ ENNReal.ofReal (L * η) * (ENNReal.ofReal (2 * (4 / r) ^ d) *
          (ENNReal.ofReal (κ / 2 * (r ^ d * ω)) * ENNReal.ofReal (Cp * (r / 4) ^ ((d : ℝ) - 2 - s)) +
            ENNReal.ofReal (1 / (2 * κ)) * (ENNReal.ofReal (SmearAux.kappa d) * Yloc d s r a F))) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl ?_)
        refine h2.trans (add_le_add ?_ (mul_le_mul' le_rfl hZ))
        rw [← hc1]
        exact mul_le_mul' le_rfl hI
    _ = ENNReal.ofReal (L * η * (2 * (4 / r) ^ d) * (κ / 2 * (r ^ d * ω) * (Cp * (r / 4) ^ ((d : ℝ) - 2 - s)))) +
          ENNReal.ofReal (L * η * (2 * (4 / r) ^ d) * (1 / (2 * κ) * SmearAux.kappa d)) * Yloc d s r a F := hcomb
    _ ≤ _ := by
        refine add_le_add (ENNReal.ofReal_le_ofReal ?_) (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
        · have h := T_alg_A (d := d) (s := s) (κh := 1) (ω := ω) (Cp := Cp) hNr hr hηr.le hη0.le one_pos hL hω0.le hCp0
          refine h.trans (le_of_eq ?_)
          ring
        · have h := T_alg_B (d := d) (κd := SmearAux.kappa d) hNr hr hηr.le hη0.le hL hκd0.le
          refine h.trans (le_of_eq ?_)
          ring

end HRS.Commutator.Stj
