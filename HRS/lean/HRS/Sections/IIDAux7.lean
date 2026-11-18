import HRS.Sections.IIDAux6

/-!
# IID helper chain, part 7: `W₂` from `W₁` and fourth moments (see the chain plan in `IIDAux1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section W2

variable {d : ℕ} {m : ℝ}

/-- Elementary interpolation `t² ≤ a t + t⁴/a²`. -/
lemma sq_le_interp {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) : t ^ 2 ≤ a * t + a⁻¹ ^ 2 * t ^ 4 := by
  rcases le_or_gt t a with h | h
  · have : t ^ 2 ≤ a * t := by nlinarith
    have : 0 ≤ a⁻¹ ^ 2 * t ^ 4 := by positivity
    linarith
  · have h1 : 1 ≤ t * a⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ ha]; linarith
    have h2 : 1 ≤ (t * a⁻¹) ^ 2 := by nlinarith
    have h3 : a⁻¹ ^ 2 * t ^ 4 = t ^ 2 * (t * a⁻¹) ^ 2 := by ring
    have h4 : t ^ 2 ≤ t ^ 2 * (t * a⁻¹) ^ 2 := by nlinarith [sq_nonneg t]
    have : 0 ≤ a * t := by positivity
    linarith

lemma w2_of_l1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → NegSobolev d m) (hX : Measurable X) (hY : Measurable Y) {J M : ℝ} (hJ : 0 < J)
    (hM : 0 < M) (h1 : ∫⁻ ω, ‖X ω - Y ω‖ₑ ∂P ≤ ENNReal.ofReal J)
    (h4 : ∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal M) :
    wassersteinE 2 (law P X) (law P Y) ≤
      ENNReal.ofReal (Real.sqrt (2 * M ^ ((1 : ℝ) / 3) * (J ^ ((1 : ℝ) / 3)) ^ 2)) := by
  have hm : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hπ : IsCoupling (P.map fun ω => (X ω, Y ω)) (law P X) (law P Y) := by
    constructor
    · rw [Measure.map_map measurable_fst hm]; rfl
    · rw [Measure.map_map measurable_snd hm]; rfl
  set u : ℝ := J ^ ((1 : ℝ) / 3) with hu
  set v : ℝ := M ^ ((1 : ℝ) / 3) with hv
  have hu0 : 0 < u := Real.rpow_pos_of_pos hJ _
  have hv0 : 0 < v := Real.rpow_pos_of_pos hM _
  have hu3 : u ^ 3 = J := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hJ.le]; norm_num
  have hv3 : v ^ 3 = M := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num
  set a : ℝ := v / u with ha
  have ha0 : 0 < a := div_pos hv0 hu0
  refine (HRS.HilbertCLTAux.wE2_le_of_cost hπ (c := 2 * v * u ^ 2) ?_).trans ?_
  · have hmeas : Measurable fun z : NegSobolev d m × NegSobolev d m =>
        ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const 2)
    rw [lintegral_map hmeas hm]
    have hpt : ∀ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ 2) ≤
        ENNReal.ofReal a * ‖X ω - Y ω‖ₑ + ENNReal.ofReal (a⁻¹ ^ 2) * ‖X ω - Y ω‖ₑ ^ 4 := by
      intro ω
      have := sq_le_interp (norm_nonneg (X ω - Y ω)) ha0
      calc ENNReal.ofReal (‖X ω - Y ω‖ ^ 2)
          ≤ ENNReal.ofReal (a * ‖X ω - Y ω‖ + a⁻¹ ^ 2 * ‖X ω - Y ω‖ ^ 4) := ENNReal.ofReal_le_ofReal this
        _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha0.le,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hme : Measurable fun ω => ‖X ω - Y ω‖ₑ := (hX.sub hY).enorm
    calc ∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ 2) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal a * ‖X ω - Y ω‖ₑ + ENNReal.ofReal (a⁻¹ ^ 2) * ‖X ω - Y ω‖ₑ ^ 4) ∂P :=
          lintegral_mono hpt
      _ = ENNReal.ofReal a * ∫⁻ ω, ‖X ω - Y ω‖ₑ ∂P +
          ENNReal.ofReal (a⁻¹ ^ 2) * ∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 4 ∂P := by
          rw [lintegral_add_left (hme.const_mul _), lintegral_const_mul _ hme,
            lintegral_const_mul _ (hme.pow_const 4)]
      _ ≤ ENNReal.ofReal a * ENNReal.ofReal J + ENNReal.ofReal (a⁻¹ ^ 2) * ENNReal.ofReal M := by
          gcongr
      _ = ENNReal.ofReal (a * J + a⁻¹ ^ 2 * M) := by
          rw [← ENNReal.ofReal_mul ha0.le, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (2 * v * u ^ 2) := by
          congr 1
          rw [ha, ← hu3, ← hv3]
          field_simp
          ring
  · refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (le_of_eq ?_))
    ring

end W2

section Moments

open HRS.InitialDataAux
variable {d : ℕ} {m : ℝ}

/-- The centred single-sample vector `δ_x - μ` in `E_m`. -/
def yv (m : ℝ) (μ : Measure (Torus d)) (x : Torus d) : NegSobolev d m :=
  NegSobolev.ofMeasureDiff m (Measure.dirac x) μ

lemma coord_yv (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (x : Torus d)
    (k : NonzeroLattice d) :
    NegSobolev.coord (yv m μ x) k = scMode m k x - pair μ (scMode m k) := by
  unfold yv
  rw [coord_ofMeasureDiff hm]
  have h1 : Torus.measureRealCoeff (Measure.dirac x) k = Torus.realMode k x := by
    unfold Torus.measureRealCoeff
    simp
  have h2 : pair μ (scMode m k) = Lattice.jp k.1 ^ (-m) * Torus.measureRealCoeff μ k := by
    unfold pair scMode Torus.measureRealCoeff
    rw [integral_const_mul]
  rw [h1, h2]; simp only [scMode]; ring

lemma fld_eq_sum (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (X : Config d N) :
    fld m N μ X = (Real.sqrt N)⁻¹ • ∑ i, yv m μ (X i) := by
  refine Subtype.ext (funext fun k => ?_)
  show NegSobolev.coord (fld m N μ X) k = NegSobolev.coord ((Real.sqrt N)⁻¹ • ∑ i, yv m μ (X i)) k
  rw [coord_fld hm hN μ X k, coord_smul', coord_sum']
  simp only [coord_yv hm]

lemma norm_yv_le (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (x : Torus d) : ‖yv m μ x‖ ≤ Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) :=
  norm_ofMeasureDiff_le hm _ _

lemma continuous_yv (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Continuous (yv m μ) := by
  have : yv m μ = fun x => wA m hm x - NegSobolev.ofMeasureDiff m μ (0 : Measure (Torus d)) := by
    funext x
    refine Subtype.ext (funext fun k => ?_)
    show NegSobolev.coord (yv m μ x) k = NegSobolev.coord (wA m hm x -
      NegSobolev.ofMeasureDiff m μ (0 : Measure (Torus d))) k
    rw [coord_yv hm, coord_sub', coord_wA, coord_ofMeasureDiff hm]
    unfold pair scMode Torus.measureRealCoeff
    rw [integral_const_mul]
    simp
  rw [this]
  exact (continuous_wA m hm).sub continuous_const

lemma integral_yv (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∫ x, yv m μ x ∂μ = 0 := by
  have hint : Integrable (yv m μ) μ := by
    refine Integrable.of_bound (continuous_yv hm μ).aestronglyMeasurable
      (Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))))
      (Filter.Eventually.of_forall fun x => norm_yv_le hm μ x)
  refine lp.ext (funext fun k => ?_)
  have h1 : NegSobolev.coord (∫ x, yv m μ x ∂μ) k = ∫ x, NegSobolev.coord (yv m μ x) k ∂μ := by
    have := (negCoordCLM (m := m) k).integral_comp_comm hint
    exact this.symm
  show NegSobolev.coord (∫ x, yv m μ x ∂μ) k = 0
  rw [h1]
  simp_rw [coord_yv hm]
  have hc : Integrable (scMode m k) μ :=
    (continuous_scMode m k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hc (integrable_const _)]
  simp [pair]


open HRS.HilbertCLTAux in
lemma fourth_fld (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    ∫ X, ‖fld m N μ X‖ ^ 4 ∂(Measure.pi fun _ : Fin N => μ) ≤
      192 * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ^ 2 := by
  haveI := negSobolev_secondCountable d m
  set Z : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hB := fourth_moment_pi μ (yv m μ) (continuous_yv hm μ).measurable
    (Real.sqrt_nonneg (8 * Z)) (norm_yv_le hm μ) (integral_yv hm μ) N
  have e : ∀ X : Config d N, ‖fld m N μ X‖ ^ 4 = ((N : ℝ)⁻¹) ^ 2 * ‖∑ i : Fin N, yv m μ (X i)‖ ^ 4 := by
    intro X
    rw [fld_eq_sum hm hN μ X, norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hNpos.le]
    rw [inv_pow]
  simp_rw [e]
  rw [integral_const_mul]
  have hB4 : Real.sqrt (8 * Z) ^ 4 = (8 * Z) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hB4, Real.sq_sqrt (by positivity)] at hB
  calc ((N : ℝ)⁻¹) ^ 2 * ∫ X, ‖∑ i : Fin N, yv m μ (X i)‖ ^ 4 ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((N : ℝ)⁻¹) ^ 2 * (N * (8 * Z) ^ 2 + 3 * N * (N - 1) * (8 * Z) ^ 2) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ 192 * Z ^ 2 := by
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have : ((N : ℝ)⁻¹) ^ 2 * (N * (8 * Z) ^ 2 + 3 * N * (N - 1) * (8 * Z) ^ 2) =
            (3 - 2 * (N : ℝ)⁻¹) * (64 * Z ^ 2) := by
          field_simp; ring
        rw [this]
        have : 0 ≤ (N : ℝ)⁻¹ := by positivity
        nlinarith [sq_nonneg Z]

open HRS.HilbertCLTAux in
lemma second_gauss (hm : (d : ℝ) < 2 * m) {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov ρ)) :
    ∫ F, ‖F‖ ^ 2 ∂γ ≤ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) := by
  haveI := negSobolev_secondCountable d m
  have h := lintegral_sq_tail_le γ id measurable_id (∅ : Finset (NonzeroLattice d)) (summable_two_jp hm)
    (fun k => mul_nonneg zero_le_two (Real.rpow_nonneg (Torus.jp_pos _).le _))
    (fun k => coord_gauss_sq_lintegral hγ k)
  have hp : ∀ F : NegSobolev d m, projT (∅ : Finset (NonzeroLattice d)) F = 0 := fun F => by
    unfold projT; rw [Finset.sum_empty]; rfl
  simp only [id, hp, sub_zero, Finset.notMem_empty, ite_false] at h
  rw [tsum_mul_left] at h
  have hi := HRS.EdgeAux.gaussian_integrable_pow hγ.1 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun F => by positivity)
    hi.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg zero_le_two (tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _)) ?_
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun F => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma fourth_gauss (hm : (d : ℝ) < 2 * m) {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    {γ : Measure (NegSobolev d m)} [IsProbabilityMeasure γ]
    (hγ : IsCenteredGaussianWithCov m γ (iidCov ρ)) :
    ∫ F, ‖F‖ ^ 4 ∂γ ≤ 12 * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ^ 2 := by
  haveI := negSobolev_secondCountable d m
  have h1 := HRS.EdgeAux.gaussian_fourth_le hγ.1
  have h2 := second_gauss hm hγ
  have h0 : 0 ≤ ∫ F, ‖F‖ ^ 2 ∂γ := integral_nonneg fun F => by positivity
  calc _ ≤ 3 * (∫ F, ‖F‖ ^ 2 ∂γ) ^ 2 := h1
    _ ≤ 3 * (2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ^ 2 := by gcongr
    _ = _ := by ring

end Moments

end HRS.IID
