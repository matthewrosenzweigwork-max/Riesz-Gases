import HRS.MS.CritWholeOmitted

/-!
# S8.1 XS (S81c), CR06: `L²` bound of the conditional linear term `L_f(Y) = λ ∑_{j≠i} h_f(Y_j) - β ∫ f (g*μ) dμ`

`h_f(z) = ∫ f(y) g(y-z) dμ(y)`.  The pole variance bound controls `∑_j h_f(Y_j)`, the bounded relative marginal density
(CR02) the mean, and the a.e. identity `∫ f v_Y dμ = L_f(Y)` is Fubini (finite for a.e. `Y` since `h_f < ∞` a.e.).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- Cauchy-Schwarz for square-integrable functions. -/
theorem s81c_cs2 {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a b : Euc d → ℝ} (ha : Measurable a)
    (hb : Measurable b) (ha2 : Integrable (fun y => a y ^ 2) μ) (hb2 : Integrable (fun y => b y ^ 2) μ) :
    (∫ y, a y * b y ∂μ) ^ 2 ≤ (∫ y, a y ^ 2 ∂μ) * ∫ y, b y ^ 2 ∂μ := by
  have hab : Integrable (fun y => a y * b y) μ := by
    refine Integrable.mono' ((ha2.add hb2).const_mul (1 / 2)) (ha.mul hb).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    show |a y| * |b y| ≤ 1 / 2 * (a y ^ 2 + b y ^ 2)
    nlinarith [sq_nonneg (|a y| - |b y|), sq_abs (a y), sq_abs (b y), abs_nonneg (a y), abs_nonneg (b y)]
  have key : ∀ t : ℝ, 0 ≤ (∫ y, a y ^ 2 ∂μ) * (t * t) + (-2 * ∫ y, a y * b y ∂μ) * t + ∫ y, b y ^ 2 ∂μ := by
    intro t
    have h_a2 : Integrable (fun y => t * t * a y ^ 2) μ := ha2.const_mul _
    have h_ab : Integrable (fun y => 2 * t * (a y * b y)) μ := hab.const_mul _
    have h_sub : Integrable (fun y => t * t * a y ^ 2 - 2 * t * (a y * b y)) μ := h_a2.sub h_ab
    have : (∫ y, a y ^ 2 ∂μ) * (t * t) + (-2 * ∫ y, a y * b y ∂μ) * t + ∫ y, b y ^ 2 ∂μ =
        ∫ y, (t * a y - b y) ^ 2 ∂μ := by
      have e : ∀ y, (t * a y - b y) ^ 2 = t * t * a y ^ 2 - 2 * t * (a y * b y) + b y ^ 2 := fun y => by ring
      simp_rw [e]
      rw [integral_add h_sub hb2, integral_sub h_a2 h_ab, integral_const_mul, integral_const_mul]
      ring
    rw [this]
    exact integral_nonneg fun y => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- `h_f(z) = ∫ f(y) g(y - z) dμ(y)`. -/
def s81c_h (D : Data d M βm βp) (f : Euc d → ℝ) (z : Euc d) : ℝ := ∫ y, f y * critG d (y - z) ∂(mu D)

theorem s81c_h_meas (hd : 1 ≤ d) (D : Data d M βm βp) {f : Euc d → ℝ} (hf : Measurable f) :
    Measurable (s81c_h D f) := by
  haveI := s81c_prob D
  have h : StronglyMeasurable fun q : Euc d × Euc d => f q.2 * critG d (q.2 - q.1) :=
    ((hf.comp measurable_snd).mul ((s81b_critG_meas hd).comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := mu D)).measurable

theorem s81c_h_nonneg (hd : 1 ≤ d) (D : Data d M βm βp) {f : Euc d → ℝ} (hf0 : ∀ y, 0 ≤ f y) (z : Euc d) :
    0 ≤ s81c_h D f z :=
  integral_nonneg fun y => mul_nonneg (hf0 y) (s81b_critG_nonneg hd _)

/-- `L²(μ)` bound of `h_f` from an extended-real majorant. -/
theorem s81c_h_sq (hd : 1 ≤ d) (D : Data d M βm βp) {f : Euc d → ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (G : Euc d → ℝ≥0∞) {Ch : ℝ} (hCh : 0 ≤ Ch) (hG : ∀ z, ENNReal.ofReal (s81c_h D f z) ≤ G z)
    (hGI : ∫⁻ z, G z ^ 2 ∂(mu D) ≤ ENNReal.ofReal Ch) :
    Integrable (fun z => s81c_h D f z ^ 2) (mu D) ∧ ∫ z, s81c_h D f z ^ 2 ∂(mu D) ≤ Ch := by
  have hm : Measurable fun z => s81c_h D f z ^ 2 := (s81c_h_meas hd D hfm).pow_const 2
  refine Q34.integrable_of_lintegral_le hm (fun z => sq_nonneg _) hCh ?_
  refine le_trans (lintegral_mono fun z => ?_) hGI
  rw [ENNReal.ofReal_pow (s81c_h_nonneg hd D hf0 z)]
  exact pow_le_pow_left' (hG z) 2

/-- The centred `L²` norm from the extended variance. -/
theorem s81c_eLp_centered {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) {V : ℝ} (hV0 : 0 ≤ V) (hV : evariance X P ≤ ENNReal.ofReal V) :
    MemLp X 2 P ∧ eLpNorm (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P ≤ ENNReal.ofReal (Real.sqrt V) := by
  have hmem : MemLp X 2 P := (evariance_lt_top_iff_memLp hX.aestronglyMeasurable).1
    (lt_of_le_of_lt hV ENNReal.ofReal_lt_top)
  refine ⟨hmem, ?_⟩
  have hc : MemLp (fun ω => X ω - ∫ ω', X ω' ∂P) 2 P := hmem.sub (memLp_const _)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hc.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h1 : ∫⁻ ω, ‖X ω - ∫ ω', X ω' ∂P‖ₑ ^ 2 ∂P = evariance X P := by rfl
  rw [h1]
  calc evariance X P ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal V) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hV (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt V) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hV0 (by norm_num), ← Real.sqrt_eq_rpow]

/-- `L²` norm of an affine functional of `n-1` of `n` identically-centred square-integrable variables. -/
theorem s81c_L2_affine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (i : Fin n) (u : Fin n → Ω → ℝ) (hum : ∀ j, Measurable (u j)) (hmem : ∀ j, MemLp (u j) 2 P) {m : ℝ}
    (hm : ∀ j, ∫ ω, u j ω ∂P = m) {Q : ℝ} (hQ0 : 0 ≤ Q) (hi : eLpNorm (u i) 2 P ≤ ENNReal.ofReal (Real.sqrt Q))
    {V : ℝ} (hV0 : 0 ≤ V) (hV : evariance (fun ω => ∑ j, u j ω) P ≤ ENNReal.ofReal V) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    MemLp (fun ω => a * ∑ j ∈ Finset.univ.erase i, u j ω - b) 2 P ∧
      eLpNorm (fun ω => a * ∑ j ∈ Finset.univ.erase i, u j ω - b) 2 P ≤
        ENNReal.ofReal (a * Real.sqrt V + a * Real.sqrt Q + |a * (n * m) - b|) := by
  set S : Ω → ℝ := fun ω => ∑ j, u j ω with hS
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hum j
  obtain ⟨hSmem, hSc⟩ := s81c_eLp_centered P hSm hV0 hV
  have hES : ∫ ω, S ω ∂P = n * m := by
    simp only [hS]
    rw [integral_finset_sum _ fun j _ => (hmem j).integrable one_le_two]
    simp [hm]
  have hL : (fun ω => a * ∑ j ∈ Finset.univ.erase i, u j ω - b) =
      (a • (fun ω => S ω - ∫ ω', S ω' ∂P)) + (fun _ => a * ∫ ω', S ω' ∂P - b) - a • u i := by
    funext ω
    have : ∑ j ∈ Finset.univ.erase i, u j ω = S ω - u i ω := by
      rw [hS]; simp only
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  have hm1 : MemLp (a • (fun ω => S ω - ∫ ω', S ω' ∂P)) 2 P := (hSmem.sub (memLp_const _)).const_smul a
  have hm2 : MemLp (fun _ : Ω => a * ∫ ω', S ω' ∂P - b) 2 P := memLp_const _
  have hm3 : MemLp (a • u i) 2 P := (hmem i).const_smul a
  rw [hL]
  refine ⟨(hm1.add hm2).sub hm3, ?_⟩
  refine (eLpNorm_sub_le one_le_two).trans ?_
  refine (add_le_add (eLpNorm_add_le one_le_two) le_rfl).trans ?_
  have e1 : eLpNorm (a • (fun ω => S ω - ∫ ω', S ω' ∂P)) 2 P ≤ ENNReal.ofReal (a * Real.sqrt V) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ha, ENNReal.ofReal_mul ha]
    exact mul_le_mul' le_rfl hSc
  have e2 : eLpNorm (fun _ : Ω => a * ∫ ω', S ω' ∂P - b) 2 P = ENNReal.ofReal |a * (n * m) - b| := by
    rw [eLpNorm_const _ two_ne_zero (IsProbabilityMeasure.ne_zero P), hES]
    simp [Real.enorm_eq_ofReal_abs]
  have e3 : eLpNorm (a • u i) 2 P ≤ ENNReal.ofReal (a * Real.sqrt Q) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ha, ENNReal.ofReal_mul ha]
    exact mul_le_mul' le_rfl hi
  calc _ ≤ ENNReal.ofReal (a * Real.sqrt V) + ENNReal.ofReal |a * (n * m) - b| + ENNReal.ofReal (a * Real.sqrt Q) := by
        rw [← e2]; exact add_le_add (add_le_add e1 le_rfl) e3
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

theorem s81c_nu_le {μ : Measure (Euc d)} {φ : Euc d → ℝ} {Cq : ℝ} (hφ : ∀ z, 0 ≤ φ z ∧ φ z ≤ Cq) :
    μ.withDensity (fun z => ENNReal.ofReal (φ z)) ≤ ENNReal.ofReal Cq • μ := by
  have : μ.withDensity (fun z => ENNReal.ofReal (φ z)) ≤ μ.withDensity (fun _ => ENNReal.ofReal Cq) :=
    withDensity_mono (Filter.Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal (hφ z).2)
  rwa [withDensity_const] at this

theorem s81c_coord_integral {n : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (P : Measure (EucConfig d n)) {φ : Euc d → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z)
    (hcoord : ∀ j : Fin n, P.map (fun Y => Y j) = μ.withDensity (fun z => ENNReal.ofReal (φ z))) (j : Fin n)
    {ψ : Euc d → ℝ} (hψ : Measurable ψ) : ∫ Y, ψ (Y j) ∂P = ∫ z, φ z * ψ z ∂μ := by
  rw [← integral_map (measurable_pi_apply j).aemeasurable hψ.aestronglyMeasurable, hcoord j,
    s81b_integral_withDensity hφm hφ0]

/-- `eLpNorm` in `L²` of a square-integrable variable through its second moment. -/
theorem s81c_eLp_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hsq : Integrable (fun ω => X ω ^ 2) P) :
    eLpNorm X 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, X ω ^ 2 ∂P)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hX.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have : ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂P = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.rpow_two, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  rw [this, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun ω => sq_nonneg _) (by norm_num), Real.sqrt_eq_rpow]

/-- Fubini: `∫ h_f dμ = ∫ f (g*μ) dμ`. -/
theorem s81c_h_integral (hd : 1 ≤ d) (D : Data d M βm βp) {f : Euc d → ℝ} (hfm : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) (hfconv : Integrable (fun y => f y * convMeasure (critG d) (mu D) y) (mu D)) :
    ∫ z, s81c_h D f z ∂(mu D) = ∫ y, f y * convMeasure (critG d) (mu D) y ∂(mu D) := by
  haveI := s81c_prob D
  have hg := s81b_critG_meas hd
  have hs0 := s81c_hs0 hd
  have hFm : Measurable fun q : Euc d × Euc d => f q.2 * critG d (q.2 - q.1) :=
    (hfm.comp measurable_snd).mul (hg.comp (measurable_snd.sub measurable_fst))
  have hF0 : ∀ q : Euc d × Euc d, 0 ≤ f q.2 * critG d (q.2 - q.1) := fun q =>
    mul_nonneg (hf0 _) (s81b_critG_nonneg hd _)
  have hgI : ∀ y, Integrable (fun z => critG d (y - z)) (mu D) := fun y =>
    (wr13a_potential_bound hd hs0 (s81c_hsd hd) D.prob D.bound y).1
  have hint : Integrable (fun q : Euc d × Euc d => f q.2 * critG d (q.2 - q.1)) ((mu D).prod (mu D)) := by
    refine (Q34.integrable_of_lintegral_le hFm hF0 (c := ∫ y, f y * convMeasure (critG d) (mu D) y ∂(mu D))
      (integral_nonneg fun y => mul_nonneg (hf0 y) (wr13a_conv_nonneg hs0 (mu D) y)) ?_).1
    rw [lintegral_prod_symm _ hFm.ennreal_ofReal.aemeasurable]
    have : ∀ y, ∫⁻ z, ENNReal.ofReal (f y * critG d (y - z)) ∂(mu D) =
        ENNReal.ofReal (f y * convMeasure (critG d) (mu D) y) := fun y => by
      have h1 : ∀ z, ENNReal.ofReal (f y * critG d (y - z)) = ENNReal.ofReal (f y) * ENNReal.ofReal (critG d (y - z)) :=
        fun z => ENNReal.ofReal_mul (hf0 y)
      simp_rw [h1]
      have hm : Measurable fun z : Euc d => ENNReal.ofReal (critG d (y - z)) :=
        (hg.comp (measurable_const.sub measurable_id)).ennreal_ofReal
      rw [lintegral_const_mul _ hm,
        ← ofReal_integral_eq_lintegral_ofReal (hgI y) (Filter.Eventually.of_forall fun z =>
          s81b_critG_nonneg hd _), ← ENNReal.ofReal_mul (hf0 y)]
      rfl
    simp_rw [this]
    rw [← ofReal_integral_eq_lintegral_ofReal hfconv (Filter.Eventually.of_forall fun y =>
      mul_nonneg (hf0 y) (wr13a_conv_nonneg hs0 (mu D) y))]
  unfold s81c_h
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_const_mul]
  rfl

set_option maxHeartbeats 1600000 in
theorem s81c_linear_core (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 < D.beta) {m : ℕ} (i : Fin (m + 1)) (x : Euc d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (P : Measure (EucConfig d (m + 1))) [IsProbabilityMeasure P]
    {Cq Cv Ch δ : ℝ} (hCq : 1 ≤ Cq) (hCv : 0 ≤ Cv) (hCh : 0 ≤ Ch) (hδ : 0 ≤ δ)
    {φ : Euc d → ℝ} (hφm : Measurable φ) (hφ0 : ∀ z, 0 ≤ φ z ∧ φ z ≤ Cq)
    (hcoord : ∀ j : Fin (m + 1), P.map (fun Y => Y j) = (mu D).withDensity (fun z => ENNReal.ofReal (φ z)))
    (hφ2 : Integrable (fun z => (φ z - 1) ^ 2) (mu D)) (hφ2n : ∫ z, (φ z - 1) ^ 2 ∂(mu D) ≤ (Cq * δ) ^ 2)
    (hvar : ∀ ψ : Euc d → ℝ, Measurable ψ →
      evariance (fun Y : EucConfig d (m + 1) => ∑ j, ψ (Y j)) P ≤
        ENNReal.ofReal (Cv * ((m + 1 : ℕ) : ℝ)) * ∫⁻ z, ‖ψ z‖ₑ ^ 2 ∂(mu D))
    {f : Euc d → ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hfconv : Integrable (fun y => f y * convMeasure (critG d) (mu D) y) (mu D))
    (hh2 : Integrable (fun z => s81c_h D f z ^ 2) (mu D)) (hhC : ∫ z, s81c_h D f z ^ 2 ∂(mu D) ≤ Ch) :
    MemLp (linearPart D (m + 2) i f) 2 P ∧
      eLpNorm (linearPart D (m + 2) i f) 2 P ≤ ENNReal.ofReal (
        D.beta / ((m + 2 : ℕ) : ℝ) * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * Ch) +
          D.beta / ((m + 2 : ℕ) : ℝ) * Real.sqrt (Cq * Ch) + D.beta * (Real.sqrt Ch * (Cq * δ)) +
          D.beta / ((m + 2 : ℕ) : ℝ) * Real.sqrt Ch) := by
  haveI := s81c_prob D
  have hhm := s81c_h_meas hd D hfm
  have hνle : (mu D).withDensity (fun z => ENNReal.ofReal (φ z)) ≤ ENNReal.ofReal Cq • mu D := s81c_nu_le hφ0
  set N : ℝ := ((m + 2 : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by positivity
  set a : ℝ := D.beta / N with ha
  have ha0 : 0 ≤ a := by positivity
  -- second moments of h(Y_j)
  have hsqν : Integrable (fun z => s81c_h D f z ^ 2) ((mu D).withDensity (fun z => ENNReal.ofReal (φ z))) :=
    (hh2.smul_measure (c := ENNReal.ofReal Cq) ENNReal.ofReal_ne_top).mono_measure hνle
  have hsqP : ∀ j : Fin (m + 1), Integrable (fun Y : EucConfig d (m + 1) => s81c_h D f (Y j) ^ 2) P := fun j => by
    have := hsqν
    rw [← hcoord j] at this
    exact (integrable_map_measure (hhm.pow_const 2).aestronglyMeasurable (measurable_pi_apply j).aemeasurable).1 this
  have hmemP : ∀ j : Fin (m + 1), MemLp (fun Y : EucConfig d (m + 1) => s81c_h D f (Y j)) 2 P := fun j =>
    (memLp_two_iff_integrable_sq (hhm.comp (measurable_pi_apply j)).aestronglyMeasurable).2 (hsqP j)
  have hQ : ∀ j : Fin (m + 1), ∫ Y, s81c_h D f (Y j) ^ 2 ∂P ≤ Cq * Ch := fun j => by
    rw [s81c_coord_integral P hφm (fun z => (hφ0 z).1) hcoord j (hhm.pow_const 2)]
    calc ∫ z, φ z * s81c_h D f z ^ 2 ∂(mu D) ≤ ∫ z, Cq * s81c_h D f z ^ 2 ∂(mu D) := by
          refine integral_mono ?_ (hh2.const_mul _) fun z => ?_
          · exact Integrable.mono' (hh2.const_mul Cq) (hφm.mul (hhm.pow_const 2)).aestronglyMeasurable
              (Filter.Eventually.of_forall fun z => by
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 z).1, abs_of_nonneg (sq_nonneg _)]
                exact mul_le_mul_of_nonneg_right (hφ0 z).2 (sq_nonneg _))
          · exact mul_le_mul_of_nonneg_right (hφ0 z).2 (sq_nonneg _)
      _ = Cq * ∫ z, s81c_h D f z ^ 2 ∂(mu D) := integral_const_mul _ _
      _ ≤ Cq * Ch := mul_le_mul_of_nonneg_left hhC (by linarith)
  have hi : eLpNorm (fun Y : EucConfig d (m + 1) => s81c_h D f (Y i)) 2 P ≤ ENNReal.ofReal (Real.sqrt (Cq * Ch)) := by
    have h := s81c_eLp_sq (P := P) (X := fun Y : EucConfig d (m + 1) => s81c_h D f (Y i))
      (hhm.comp (measurable_pi_apply i)) (hsqP i)
    rw [h]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hQ i))
  -- the mean
  set m' : ℝ := ∫ z, φ z * s81c_h D f z ∂(mu D) with hm'
  have hmean : ∀ j : Fin (m + 1), ∫ Y, s81c_h D f (Y j) ∂P = m' := fun j =>
    s81c_coord_integral P hφm (fun z => (hφ0 z).1) hcoord j hhm
  -- the variance
  have hV : evariance (fun Y : EucConfig d (m + 1) => ∑ j, s81c_h D f (Y j)) P ≤
      ENNReal.ofReal (Cv * ((m + 1 : ℕ) : ℝ) * Ch) := by
    refine (hvar _ hhm).trans ?_
    have : ∫⁻ z, ‖s81c_h D f z‖ₑ ^ 2 ∂(mu D) = ENNReal.ofReal (∫ z, s81c_h D f z ^ 2 ∂(mu D)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hh2 (Filter.Eventually.of_forall fun z => sq_nonneg _)]
      refine lintegral_congr fun z => ?_
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [this, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hhC (by positivity))
  -- c_f and the bound on the mean
  set cf : ℝ := ∫ y, f y * convMeasure (critG d) (mu D) y ∂(mu D) with hcf
  have hcfh : ∫ z, s81c_h D f z ∂(mu D) = cf := s81c_h_integral hd D hfm hf0 hfconv
  have hCS1 : |∫ z, s81c_h D f z ∂(mu D)| ≤ Real.sqrt Ch := by
    have := s81c_cs2 (μ := mu D) (a := fun _ => (1 : ℝ)) (b := s81c_h D f) measurable_const hhm
      (integrable_const _) hh2
    simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] at this
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (this.trans (by simpa using hhC))
  have hCS2 : |∫ z, (φ z - 1) * s81c_h D f z ∂(mu D)| ≤ Real.sqrt Ch * (Cq * δ) := by
    have := s81c_cs2 (μ := mu D) (a := fun z => φ z - 1) (b := s81c_h D f) (hφm.sub_const 1) hhm hφ2 hh2
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((∫ z, (φ z - 1) * s81c_h D f z ∂(mu D)) ^ 2)
        ≤ Real.sqrt ((Cq * δ) ^ 2 * Ch) := Real.sqrt_le_sqrt (this.trans (by
          exact mul_le_mul hφ2n hhC (integral_nonneg fun z => sq_nonneg _) (sq_nonneg _)))
      _ = Real.sqrt Ch * (Cq * δ) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]; ring
  have hhI : Integrable (s81c_h D f) (mu D) :=
    ((memLp_two_iff_integrable_sq hhm.aestronglyMeasurable).2 hh2).integrable one_le_two
  have hφhI : Integrable (fun z => φ z * s81c_h D f z) (mu D) := by
    refine Integrable.mono' (hhI.norm.const_mul Cq) (hφm.mul hhm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 z).1]
    exact mul_le_mul_of_nonneg_right (hφ0 z).2 (abs_nonneg _)
  have hmc : m' - cf = ∫ z, (φ z - 1) * s81c_h D f z ∂(mu D) := by
    rw [hm', ← hcfh, ← integral_sub hφhI hhI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring
  have hn : ((m + 1 : ℕ) : ℝ) = N - 1 := by rw [hN]; push_cast; ring
  have han : a * ((m + 1 : ℕ) : ℝ) - D.beta = -a := by
    rw [ha, hn]; field_simp; ring
  have han0 : 0 ≤ a * ((m + 1 : ℕ) : ℝ) := by positivity
  have hanb : a * ((m + 1 : ℕ) : ℝ) ≤ D.beta := by linarith [han, ha0]
  have hbound : |a * (((m + 1 : ℕ) : ℝ) * m') - D.beta * cf| ≤
      D.beta * (Real.sqrt Ch * (Cq * δ)) + a * Real.sqrt Ch := by
    have e : a * (((m + 1 : ℕ) : ℝ) * m') - D.beta * cf =
        a * ((m + 1 : ℕ) : ℝ) * (m' - cf) + (a * ((m + 1 : ℕ) : ℝ) - D.beta) * cf := by ring
    rw [e, han]
    have hcf' : |cf| ≤ Real.sqrt Ch := by rw [← hcfh]; exact hCS1
    calc |a * ((m + 1 : ℕ) : ℝ) * (m' - cf) + -a * cf| ≤ |a * ((m + 1 : ℕ) : ℝ) * (m' - cf)| + |-a * cf| :=
          abs_add_le _ _
      _ = a * ((m + 1 : ℕ) : ℝ) * |m' - cf| + a * |cf| := by
          rw [abs_mul, abs_of_nonneg han0, abs_mul, abs_neg, abs_of_nonneg ha0]
      _ ≤ D.beta * (Real.sqrt Ch * (Cq * δ)) + a * Real.sqrt Ch := by
          rw [hmc]
          exact add_le_add (mul_le_mul hanb hCS2 (abs_nonneg _) hβ0.le)
            (mul_le_mul_of_nonneg_left hcf' ha0)
  obtain ⟨hmemL, hnormL⟩ := s81c_L2_affine P i (fun j Y => s81c_h D f (Y j))
    (fun j => hhm.comp (measurable_pi_apply j)) hmemP hmean (Q := Cq * Ch) (by positivity) hi
    (V := Cv * ((m + 1 : ℕ) : ℝ) * Ch) (by positivity) hV ha0 (D.beta * cf)
  have hL : linearPart D (m + 2) i f = fun Y : EucConfig d (m + 1) =>
      a * ∑ j ∈ Finset.univ.erase i, s81c_h D f (Y j) - D.beta * cf := rfl
  rw [hL]
  refine ⟨hmemL, hnormL.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  linarith [hbound]

theorem s81c_linear_ae (hd : 1 ≤ d) (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1))
    (P : Measure (EucConfig d (m + 1))) {Cq : ℝ} {φ : Euc d → ℝ} (hφ0 : ∀ z, 0 ≤ φ z ∧ φ z ≤ Cq)
    (hcoord : ∀ j : Fin (m + 1), P.map (fun Y => Y j) = (mu D).withDensity (fun z => ENNReal.ofReal (φ z)))
    {f : Euc d → ℝ} (hfm : Measurable f)
    (hfconv : Integrable (fun y => f y * convMeasure (critG d) (mu D) y) (mu D))
    (hfin : ∀ᵐ z ∂(mu D), Integrable (fun y => f y * critG d (y - z)) (mu D)) :
    ∀ᵐ Y ∂P, Integrable (fun y => f y * field D (m + 2) i Y y) (mu D) ∧
      (∫ y, f y * field D (m + 2) i Y y ∂(mu D)) = linearPart D (m + 2) i f Y := by
  have hac := Measure.absolutelyContinuous_of_le_smul (s81c_nu_le (μ := mu D) hφ0)
  have hfin' : ∀ᵐ z ∂((mu D).withDensity (fun z => ENNReal.ofReal (φ z))),
      Integrable (fun y => f y * critG d (y - z)) (mu D) := hac.ae_le hfin
  have h1 : ∀ j : Fin (m + 1), ∀ᵐ Y ∂P, Integrable (fun y => f y * critG d (y - Y j)) (mu D) := fun j => by
    refine ae_of_ae_map (f := fun Y : EucConfig d (m + 1) => Y j)
      (p := fun z => Integrable (fun y => f y * critG d (y - z)) (mu D)) (measurable_pi_apply j).aemeasurable ?_
    rw [hcoord j]; exact hfin'
  filter_upwards [ae_all_iff.2 h1] with Y hY
  have e : ∀ y, f y * field D (m + 2) i Y y =
      D.beta / ((m + 2 : ℕ) : ℝ) * ∑ j ∈ (Finset.univ : Finset (Fin (m + 2 - 1))).erase i, (f y * critG d (y - Y j)) -
        D.beta * (f y * convMeasure (critG d) (mu D) y) := fun y => by
    unfold field
    rw [← Finset.mul_sum]; ring
  have hsum : Integrable (fun y => ∑ j ∈ (Finset.univ : Finset (Fin (m + 2 - 1))).erase i,
      (f y * critG d (y - Y j))) (mu D) := integrable_finset_sum _ fun j _ => hY j
  have hI : Integrable (fun y => f y * field D (m + 2) i Y y) (mu D) := by
    simp_rw [e]
    exact (hsum.const_mul _).sub (hfconv.const_mul _)
  refine ⟨hI, ?_⟩
  simp_rw [e]
  rw [integral_sub (hsum.const_mul _) (hfconv.const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum ((Finset.univ : Finset (Fin (m + 2 - 1))).erase i) fun j _ => hY j]
  rfl

theorem s81c_lin_num {m : ℕ} {β βp Cv Cq Ch δ : ℝ} (hβ0 : 0 < β) (hββp : β ≤ βp) (hCv : 0 ≤ Cv) (hCq : 1 ≤ Cq)
    (hCh : 0 ≤ Ch) (hδ : 0 ≤ δ) :
    β / ((m + 2 : ℕ) : ℝ) * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * Ch) +
          β / ((m + 2 : ℕ) : ℝ) * Real.sqrt (Cq * Ch) + β * (Real.sqrt Ch * (Cq * δ)) +
          β / ((m + 2 : ℕ) : ℝ) * Real.sqrt Ch ≤
      βp * (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq) *
        (((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) + δ) := by
  set N : ℝ := ((m + 2 : ℕ) : ℝ) with hN
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hN0 : 0 < N := by linarith
  set r : ℝ := Real.sqrt N with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hN0
  have hrr : r * r = N := Real.mul_self_sqrt hN0.le
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; linarith
  have hNr : N ^ (-(1 / 2 : ℝ)) = 1 / r := by
    rw [Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hNr]
  have hβN : β / N = β / (r * r) := by rw [hrr]
  have e1 : Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * Ch) ≤ Real.sqrt (Cv * Ch) * r := by
    calc Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * Ch) ≤ Real.sqrt (Cv * Ch * N) :=
          Real.sqrt_le_sqrt (by
            have : ((m + 1 : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
            nlinarith [mul_nonneg hCv hCh])
      _ = _ := Real.sqrt_mul (mul_nonneg hCv hCh) N
  have hK : 0 ≤ Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq := by
    have := Real.sqrt_nonneg (Cv * Ch); have := Real.sqrt_nonneg (Cq * Ch); have := Real.sqrt_nonneg Ch
    have : 0 ≤ Real.sqrt Ch * Cq := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    linarith
  have hs1 := Real.sqrt_nonneg (Cv * Ch)
  have hs2 := Real.sqrt_nonneg (Cq * Ch)
  have hs3 := Real.sqrt_nonneg Ch
  have hbr : β / (r * r) ≤ β / r := by
    apply div_le_div_of_nonneg_left hβ0.le hr0
    nlinarith
  have hbr' : β / (r * r) * r = β / r := by field_simp
  -- term bounds
  have T1 : β / N * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * Ch) ≤ β * Real.sqrt (Cv * Ch) * (1 / r) := by
    rw [hβN]
    calc β / (r * r) * Real.sqrt (Cv * ((m + 1 : ℕ) : ℝ) * Ch) ≤ β / (r * r) * (Real.sqrt (Cv * Ch) * r) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = _ := by field_simp
  have T2 : β / N * Real.sqrt (Cq * Ch) ≤ β * Real.sqrt (Cq * Ch) * (1 / r) := by
    rw [hβN]
    calc β / (r * r) * Real.sqrt (Cq * Ch) ≤ β / r * Real.sqrt (Cq * Ch) := mul_le_mul_of_nonneg_right hbr hs2
      _ = _ := by ring
  have T4 : β / N * Real.sqrt Ch ≤ β * Real.sqrt Ch * (1 / r) := by
    rw [hβN]
    calc β / (r * r) * Real.sqrt Ch ≤ β / r * Real.sqrt Ch := mul_le_mul_of_nonneg_right hbr hs3
      _ = _ := by ring
  have hr_inv : 0 ≤ 1 / r := by positivity
  have hcq : 0 ≤ Real.sqrt Ch * Cq := mul_nonneg hs3 (by linarith)
  have hsum : β * Real.sqrt (Cv * Ch) * (1 / r) + β * Real.sqrt (Cq * Ch) * (1 / r) + β * (Real.sqrt Ch * (Cq * δ)) +
      β * Real.sqrt Ch * (1 / r) = β * ((Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch) * (1 / r) +
        Real.sqrt Ch * Cq * δ) := by ring
  have hfin : β * ((Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch) * (1 / r) + Real.sqrt Ch * Cq * δ) ≤
      βp * (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq) * (1 / r + δ) := by
    have h1 : (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch) * (1 / r) + Real.sqrt Ch * Cq * δ ≤
        (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq) * (1 / r + δ) := by
      nlinarith [mul_nonneg hcq hr_inv, mul_nonneg (add_nonneg (add_nonneg hs1 hs2) hs3) hδ]
    have h2 : 0 ≤ (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch) * (1 / r) + Real.sqrt Ch * Cq * δ := by
      positivity
    calc β * ((Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch) * (1 / r) + Real.sqrt Ch * Cq * δ)
        ≤ βp * ((Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch) * (1 / r) + Real.sqrt Ch * Cq * δ) :=
          mul_le_mul_of_nonneg_right hββp h2
      _ ≤ βp * ((Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq) * (1 / r + δ)) :=
          mul_le_mul_of_nonneg_left h1 (hβ0.le.trans hββp)
      _ = _ := by ring
  linarith [T1, T2, T4, hsum, hfin]


theorem s81c_ofReal_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : α → ℝ} (hF0 : ∀ a, 0 ≤ F a) :
    ENNReal.ofReal (∫ a, F a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (F a) ∂μ := by
  by_cases hF : Integrable F μ
  · exact (ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall hF0)).le
  · rw [integral_undef hF]; simp

theorem s81c_gI (hd : 1 ≤ d) (D : Data d M βm βp) (z : Euc d) : Integrable (fun y => critG d (y - z)) (mu D) := by
  haveI := s81c_prob D
  have h := (wr13a_potential_bound hd (s81c_hs0 hd) (s81c_hsd hd) D.prob D.bound z).1
  have e : (fun y => critG d (y - z)) = fun y => critG d (z - y) := funext fun y => wr13a_g_sub_swap _ _
  rw [e]; exact h

theorem s81c_h_le_conv (hd : 1 ≤ d) (D : Data d M βm βp) {f : Euc d → ℝ} (hfm : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (z : Euc d) : s81c_h D f z ≤ convMeasure (critG d) (mu D) z := by
  haveI := s81c_prob D
  unfold s81c_h convMeasure
  have e : ∫ y, critG d (z - y) ∂(mu D) = ∫ y, critG d (y - z) ∂(mu D) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => (wr13a_g_sub_swap _ _).symm)
  rw [e]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => mul_nonneg (hf0 y) (s81b_critG_nonneg hd _))
    (s81c_gI hd D z) (Filter.Eventually.of_forall fun y => ?_)
  calc f y * critG d (y - z) ≤ 1 * critG d (y - z) := mul_le_mul_of_nonneg_right (hf1 y) (s81b_critG_nonneg hd _)
    _ = _ := one_mul _

set_option maxHeartbeats 1600000 in
theorem s81c_conditional_linear_L2 (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f ∈ weightedTests D N x t,
        (∀ᵐ Y ∂(pole D N x t),
          Integrable (fun y => f y * field D N i Y y) (mu D) ∧
          (∫ y, f y * field D N i Y y ∂(mu D)) = linearPart D N i f Y) ∧
        MemLp (linearPart D N i f) 2 (pole D N x t) ∧
        eLpNorm (linearPart D N i f) 2 (pole D N x t) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 / 2 : ℝ)) +
            deltaN d ((d : ℝ) / 2) N)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cq, hCq1, hCq⟩ := s81b_cavity_relative_L2 hd M βm βp hβm hβ
  obtain ⟨Cv, hCv0, hCv⟩ := wr13b_pole_variance hd (s81c_hs0 hd1) (s81c_hsd hd1) βp M
  obtain ⟨C2, hC20, hC2⟩ := s81b_two_pole_moments hd M 2 le_rfl
  set Mg : ℝ := |potentialBound d ((d : ℝ) / 2) M| with hMg
  set Ch : ℝ := Mg ^ 2 + C2 with hCh
  have hCh0 : 0 ≤ Ch := by positivity
  have hβp : 0 < βp := hβm.trans_le hβ
  refine ⟨βp * (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq), by positivity,
    fun D N hN i x t ht f hf => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd1 D hβ0.le _ x ht.1
  obtain ⟨-, hn2, -, -, -⟩ := s81c_num_facts hd1 hN
  set δ : ℝ := deltaN d ((d : ℝ) / 2) (m + 2) with hδ
  have hδ0 : 0 ≤ δ := (inv_nonneg.2 (Nat.cast_nonneg _)).trans (s81c_num_facts hd1 hN).1
  obtain ⟨q, -, -, -, -, -, -, -, hpole⟩ := hCq D (m + 2) hN
  obtain ⟨φ, hφm, hφeq, hφ0, hφmem, hφn⟩ := hpole x t ht
  have hcoord : ∀ j : Fin (m + 1), P.map (fun Y => Y j) = (mu D).withDensity (fun z => ENNReal.ofReal (φ z)) := by
    intro j
    have h := s81c_marg_coord hd1 D hβ0.le hN x ht.1 j
    rw [hP]
    exact h.trans hφeq
  have hφ2 : Integrable (fun z => (φ z - 1) ^ 2) (mu D) :=
    (memLp_two_iff_integrable_sq (hφm.sub_const 1).aestronglyMeasurable).1 hφmem
  have hφ2n : ∫ z, (φ z - 1) ^ 2 ∂(mu D) ≤ (Cq * δ) ^ 2 := by
    have : Real.sqrt (∫ z, (φ z - 1) ^ 2 ∂(mu D)) ≤ Cq * δ := hφn
    exact ((Real.sqrt_le_left (by positivity)).1 this)
  have hvar : ∀ ψ : Euc d → ℝ, Measurable ψ →
      evariance (fun Y : EucConfig d (m + 1) => ∑ j, ψ (Y j)) P ≤
        ENNReal.ofReal (Cv * ((m + 1 : ℕ) : ℝ)) * ∫⁻ z, ‖ψ z‖ₑ ^ 2 ∂(mu D) := by
    intro ψ hψ
    have h := hCv D.rho D.prob D.bound D.beta hβ0 hββp (m + 2) hN x t ht ψ hψ
    rw [hP]
    refine h.trans (mul_le_mul' le_rfl (lintegral_mono fun y => ?_))
    have h1 : ENNReal.ofReal (Real.exp (-(t * (D.beta / ((m + 2 : ℕ) : ℝ))) * rieszKernel d ((d : ℝ) / 2) (x - y))) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      exact s81c_poleFactor_le_one hd1 D hβ0.le (m + 2) x ht.1 y
    calc ‖ψ y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (D.beta / ((m + 2 : ℕ) : ℝ))) * rieszKernel d ((d : ℝ) / 2) (x - y)))
        ≤ ‖ψ y‖ₑ ^ 2 * 1 := by gcongr
      _ = ‖ψ y‖ₑ ^ 2 := mul_one _
  -- the generic estimate
  have key : ∀ f : Euc d → ℝ, Measurable f → (∀ y, 0 ≤ f y) →
      Integrable (fun y => f y * convMeasure (critG d) (mu D) y) (mu D) →
      (∀ᵐ z ∂(mu D), Integrable (fun y => f y * critG d (y - z)) (mu D)) →
      Integrable (fun z => s81c_h D f z ^ 2) (mu D) → ∫ z, s81c_h D f z ^ 2 ∂(mu D) ≤ Ch →
      (∀ᵐ Y ∂(pole D (m + 2) x t), Integrable (fun y => f y * field D (m + 2) i Y y) (mu D) ∧
          (∫ y, f y * field D (m + 2) i Y y ∂(mu D)) = linearPart D (m + 2) i f Y) ∧
        MemLp (linearPart D (m + 2) i f) 2 (pole D (m + 2) x t) ∧
        eLpNorm (linearPart D (m + 2) i f) 2 (pole D (m + 2) x t) ≤
          ENNReal.ofReal (βp * (Real.sqrt (Cv * Ch) + Real.sqrt (Cq * Ch) + Real.sqrt Ch + Real.sqrt Ch * Cq) *
            (((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) + δ)) := by
    intro f hfm hf0 hfconv hfin hh2 hhC
    obtain ⟨hmem, hnorm⟩ := s81c_linear_core hd1 D hβ0 i x ht P hCq1 hCv0.le hCh0 hδ0 hφm hφ0 hcoord hφ2 hφ2n
      hvar hfm hf0 hfconv hh2 hhC
    have hae := s81c_linear_ae hd1 D i P hφ0 hcoord hfm hfconv hfin
    rw [hP] at hae hmem hnorm
    exact ⟨hae, hmem, hnorm.trans (ENNReal.ofReal_le_ofReal
      (s81c_lin_num hβ0 hββp hCv0.le hCq1 hCh0 hδ0))⟩
  simp only [weightedTests, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  have hpf := s81c_poleFactor_meas hd1 D (m + 2) x t
  have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
  have hpf1 := s81c_poleFactor_le_one hd1 D hβ0.le (m + 2) x ht.1
  have hg := s81b_critG_meas hd1
  have hconvm := s81b_conv_meas hd1 D
  have hMgnn : 0 ≤ potentialBound d ((d : ℝ) / 2) M := s81c_Mg_nonneg hd1 D
  have hMg' : potentialBound d ((d : ℝ) / 2) M = Mg := by rw [hMg, abs_of_nonneg hMgnn]
  have hconvb : ∀ y, convMeasure (critG d) (mu D) y ≤ Mg := fun y => by
    rw [← hMg']; exact s81c_conv_le hd1 D y
  have hconv0 : ∀ y, 0 ≤ convMeasure (critG d) (mu D) y := fun y => wr13a_conv_nonneg (s81c_hs0 hd1) (mu D) y
  have hMgnn' : 0 ≤ Mg := abs_nonneg _
  rcases hf with rfl | rfl
  · -- the pole factor
    have hh := s81c_h_sq hd1 D hpf hpf0 (fun _ => ENNReal.ofReal Mg) hCh0
      (fun z => ENNReal.ofReal_le_ofReal ((s81c_h_le_conv hd1 D hpf hpf0 hpf1 z).trans (hconvb z)))
      (by
        rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_pow hMgnn']
        exact ENNReal.ofReal_le_ofReal (by rw [hCh]; nlinarith [sq_nonneg C2, hC20]))
    refine key _ hpf hpf0 ?_ (Filter.Eventually.of_forall fun z => ?_) hh.1 hh.2
    · refine Integrable.of_bound (C := Mg) (hpf.mul hconvm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpf0 y) (hconv0 y))]
      calc _ ≤ 1 * Mg := mul_le_mul (hpf1 y) (hconvb y) (hconv0 y) zero_le_one
        _ = Mg := one_mul _
    · refine Integrable.mono' (s81c_gI hd1 D z) (hpf.mul (hg.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpf0 y) (s81b_critG_nonneg hd1 _))]
      calc _ ≤ 1 * critG d (y - z) := mul_le_mul_of_nonneg_right (hpf1 y) (s81b_critG_nonneg hd1 _)
        _ = _ := one_mul _
  · -- the singular test
    set f2 : Euc d → ℝ := fun y => critG d (x - y) * poleFactor D (m + 2) x t y with hf2
    have hf2m : Measurable f2 := (hg.comp (measurable_const.sub measurable_id)).mul hpf
    have hf20 : ∀ y, 0 ≤ f2 y := fun y => mul_nonneg (s81b_critG_nonneg hd1 _) (hpf0 y)
    obtain ⟨hTPm, hTPI⟩ := hC2 D.rho D.prob D.bound x
    have hgx : Integrable (fun y => critG d (x - y)) (mu D) :=
      (wr13a_potential_bound hd1 (s81c_hs0 hd1) (s81c_hsd hd1) D.prob D.bound x).1
    have hptw : ∀ z y, ENNReal.ofReal (f2 y * critG d (y - z)) ≤
        ENNReal.ofReal (critG d (x - y) * critG d (y - z)) := fun z y =>
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by calc f2 y ≤ critG d (x - y) * 1 := mul_le_mul_of_nonneg_left (hpf1 y) (s81b_critG_nonneg hd1 _)
              _ = _ := mul_one _) (s81b_critG_nonneg hd1 _))
    have hinner : ∀ z, ∫⁻ y, ENNReal.ofReal (f2 y * critG d (y - z)) ∂(mu D) ≤ twoPole D.rho x z := fun z =>
      lintegral_mono (hptw z)
    have hh := s81c_h_sq hd1 D hf2m hf20 (twoPole D.rho x) hCh0
      (fun z => (s81c_ofReal_integral_le (fun y => mul_nonneg (hf20 y) (s81b_critG_nonneg hd1 _))).trans (hinner z))
      (hTPI.trans (ENNReal.ofReal_le_ofReal (by rw [hCh]; nlinarith [sq_nonneg Mg])))
    refine key _ hf2m hf20 ?_ ?_ hh.1 hh.2
    · refine Integrable.mono' (hgx.mul_const Mg) (hf2m.mul hconvm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf20 y) (hconv0 y))]
      exact mul_le_mul (by calc f2 y ≤ critG d (x - y) * 1 := mul_le_mul_of_nonneg_left (hpf1 y) (s81b_critG_nonneg hd1 _)
                            _ = _ := mul_one _) (hconvb y) (hconv0 y) (s81b_critG_nonneg hd1 _)
    · have hlt : ∀ᵐ z ∂(mu D), twoPole D.rho x z ^ 2 < ⊤ :=
        ae_lt_top (hTPm.pow_const 2) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTPI)
      filter_upwards [hlt] with z hz
      have hz' : twoPole D.rho x z < ⊤ := by
        by_contra h
        rw [not_lt, top_le_iff] at h
        rw [h] at hz; simp at hz
      refine (Q34.integrable_of_lintegral_le (μ := mu D) (f := fun y => f2 y * critG d (y - z))
        (hf2m.mul (hg.comp (measurable_id.sub measurable_const)))
        (fun y => mul_nonneg (hf20 y) (s81b_critG_nonneg hd1 _)) (c := (twoPole D.rho x z).toReal)
        ENNReal.toReal_nonneg ?_).1
      rw [ENNReal.ofReal_toReal hz'.ne]
      exact hinner z

end HRS.Whole.S81b
