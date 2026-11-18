import HRS.MS.CritWholeCRDefs

/-!
# S8.1 XS (S81c), CR03: the exact conditional kernel of one pole coordinate given the others

Whole-space port of `HRS.L48` (`L48Aux1`): disintegration of the pole law along coordinate `i`
(`Fin.insertNth`), the exponent update through the permutation `Fin.cycleRange`, deterministic bounds
`exp(-3 β Mg) ≤ Z_Y ≤ exp(β Mg)`, and the identification of `condMean` with the native conditional expectation.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- The cavity field of the other particles `r` (indexed by `Fin m`). -/
def s81c_k (D : Data d M βm βp) (N : ℕ) {m : ℕ} (r : Fin m → Euc d) (y : Euc d) : ℝ :=
  (D.beta / N) * ∑ j, critG d (y - r j) - D.beta * convMeasure (critG d) (mu D) y

theorem s81c_sum_erase {m : ℕ} (i : Fin (m + 1)) (f : Fin (m + 1) → ℝ) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j' : Fin m, f (i.succAbove j') := by
  have h := Fin.sum_univ_succAbove f i
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 1))) f (Finset.mem_univ i)
  linarith

theorem s81c_field_eq (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (Y : EucConfig d (m + 1))
    (y : Euc d) : field D (m + 2) i Y y = s81c_k D (m + 2) (Fin.removeNth i Y) y := by
  unfold field s81c_k
  have h : ∑ j ∈ (Finset.univ : Finset (Fin (m + 2 - 1))).erase i, critG d (y - Y j) =
      ∑ j' : Fin m, critG d (y - Fin.removeNth i Y j') :=
    s81c_sum_erase i (fun j => critG d (y - Y j))
  rw [h]

/-- The pole exponent with coordinate `i` equal to `y`. -/
theorem s81c_Ep_insertNth (D : Data d M βm βp) {m : ℕ} (N : ℕ) (x : Euc d) (t : ℝ) (i : Fin (m + 1))
    (y : Euc d) (r : Fin m → Euc d) :
    wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / N) D.beta x t (Fin.insertNth i y r : EucConfig d (m + 1)) =
      wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / N) D.beta x t r +
        (-(t * (D.beta / N)) * critG d (x - y) - s81c_k D N r y) := by
  have h1 : (Fin.insertNth i y r : EucConfig d (m + 1)) = (Fin.cons y r : EucConfig d (m + 1)) ∘ i.cycleRange := by
    have := Fin.insertNth_comp_cycleRange_symm i y r
    rw [← this]
    funext j
    simp
  have : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  rw [h1, wr13b_Ep_perm, wr13a_Ep_cons]
  unfold s81c_k
  ring

theorem s81c_lintegral_pi_insertNth {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} (i : Fin (n + 1)) (F : (Fin (n + 1) → E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ X, F X ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫⁻ y, ∫⁻ r, F (Fin.insertNth i y r) ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have e := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i).symm
  have h1 := e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F
  rw [← h1]
  have hm : Measurable fun p : E × (Fin n → E) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm p) :=
    hF.comp (MeasurableEquiv.measurable _)
  rw [lintegral_prod _ hm.aemeasurable]
  rfl

/-- The `y`-dependent exponent of the conditional density of coordinate `i`. -/
def s81c_a (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} (r : Fin m → Euc d) (y : Euc d) : ℝ :=
  -(t * (D.beta / N)) * critG d (x - y) - s81c_k D N r y

theorem s81c_meas_a_joint (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} :
    Measurable fun q : Euc d × (Fin m → Euc d) => s81c_a D N x t q.2 q.1 := by
  have hg := s81b_critG_meas hd
  have hc := s81b_conv_meas hd D
  unfold s81c_a s81c_k
  exact ((hg.comp (measurable_const.sub measurable_fst)).const_mul _).sub
    (((Finset.measurable_sum _ fun j _ => hg.comp (measurable_fst.sub
      ((measurable_pi_apply j).comp measurable_snd))).const_mul _).sub
      ((hc.comp measurable_fst).const_mul _))

theorem s81c_meas_a_rj (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} :
    Measurable fun q : (Fin m → Euc d) × Euc d => s81c_a D N x t q.1 q.2 := by
  have hg := s81b_critG_meas hd
  have hc := s81b_conv_meas hd D
  unfold s81c_a s81c_k
  exact ((hg.comp (measurable_const.sub measurable_snd)).const_mul _).sub
    (((Finset.measurable_sum _ fun j _ => hg.comp (measurable_snd.sub
      ((measurable_pi_apply j).comp measurable_fst))).const_mul _).sub
      ((hc.comp measurable_snd).const_mul _))

theorem s81c_meas_a_slice (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ}
    (r : Fin m → Euc d) : Measurable fun y : Euc d => s81c_a D N x t r y :=
  Measurable.of_uncurry_left (f := fun (r : Fin m → Euc d) (y : Euc d) => s81c_a D N x t r y)
    (s81c_meas_a_rj hd D N x t)

theorem s81c_core_aux (hd : 1 ≤ d) (D : Data d M βm βp) {m : ℕ} (x : Euc d) (t : ℝ) (i : Fin (m + 1))
    (u : Euc d → ℝ≥0∞) (hu : Measurable u) (v : (Fin m → Euc d) → ℝ≥0∞) (hv : Measurable v) :
    ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) *
        (v (Fin.removeNth i Y) * u (Y i)) ∂(Measure.pi fun _ : Fin (m + 1) => mu D) =
      ∫⁻ r, (ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t r)) *
        v r) * ∫⁻ y, ENNReal.ofReal (Real.exp (s81c_a D (m + 2) x t r y)) * u y ∂(mu D)
        ∂(Measure.pi fun _ : Fin m => mu D) := by
  have hs0 : 0 < ((d : ℝ) / 2) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  have hEp : ∀ {n : ℕ}, Measurable (fun Y : EucConfig d n =>
      wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y) := fun {n} =>
    wr13a_Ep_meas hs0 (mu D) _ D.beta x t
  have hrem : Measurable fun Y : EucConfig d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hF : Measurable fun Y : EucConfig d (m + 1) =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) *
        (v (Fin.removeNth i Y) * u (Y i)) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEp)).mul
      ((hv.comp hrem).mul (hu.comp (measurable_pi_apply i)))
  rw [s81c_lintegral_pi_insertNth (mu D) i _ hF]
  simp only [Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  simp_rw [s81c_Ep_insertNth D (m + 2) x t i]
  have hA0 := s81c_meas_a_joint hd D (m + 2) x t (m := m)
  have hEr : Measurable fun r : Fin m → Euc d =>
      wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t r := hEp
  have hjoint : Measurable fun q : Euc d × (Fin m → Euc d) =>
      ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t q.2 +
        s81c_a D (m + 2) x t q.2 q.1)) * (v q.2 * u q.1) := by
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)).mul
      ((hv.comp measurable_snd).mul (hu.comp measurable_fst))
    exact (hEr.comp measurable_snd).add hA0
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun r => ?_
  have hyr : Measurable fun y : Euc d => ENNReal.ofReal (Real.exp (s81c_a D (m + 2) x t r y)) * u y :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (s81c_meas_a_slice hd D _ x t r))).mul hu
  rw [← lintegral_const_mul _ hyr]
  refine lintegral_congr fun y => ?_
  have : s81c_a D (m + 2) x t r y = -(t * (D.beta / ((m + 2 : ℕ) : ℝ))) * critG d (x - y) - s81c_k D (m + 2) r y := rfl
  simp only [this, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

theorem s81c_prob (D : Data d M βm βp) : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob

theorem s81c_hs0 (hd : 1 ≤ d) : 0 < ((d : ℝ) / 2) := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem s81c_hsd (hd : 1 ≤ d) : ((d : ℝ) / 2) < d := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

/-- the bound `‖g*μ‖_∞ ≤ Mg`. -/
theorem s81c_conv_le (hd : 1 ≤ d) (D : Data d M βm βp) (z : Euc d) :
    convMeasure (critG d) (mu D) z ≤ potentialBound d ((d : ℝ) / 2) M :=
  wr13a_conv_le_density hd (s81c_hs0 hd) (s81c_hsd hd) D.prob D.bound z

theorem s81c_Mg_nonneg (hd : 1 ≤ d) (D : Data d M βm βp) : 0 ≤ potentialBound d ((d : ℝ) / 2) M :=
  wr13a_potentialBound_nonneg hd (s81c_hs0 hd) (s81c_hsd hd) D.prob D.bound

theorem s81c_a_le (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d) {t : ℝ} (ht : 0 ≤ t)
    {m : ℕ} (r : Fin m → Euc d) (y : Euc d) :
    s81c_a D N x t r y ≤ D.beta * potentialBound d ((d : ℝ) / 2) M := by
  have hs0 := s81c_hs0 hd
  have hlam : 0 ≤ D.beta / N := div_nonneg hβ0 (Nat.cast_nonneg _)
  have h1 : 0 ≤ (t * (D.beta / N)) * critG d (x - y) :=
    mul_nonneg (mul_nonneg ht hlam) (wr13a_g_nonneg hs0 _)
  have h2 : 0 ≤ (D.beta / N) * ∑ j, critG d (y - r j) :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
  have h3 : D.beta * convMeasure (critG d) (mu D) y ≤ D.beta * potentialBound d ((d : ℝ) / 2) M :=
    mul_le_mul_of_nonneg_left (s81c_conv_le hd D y) hβ0
  unfold s81c_a s81c_k
  nlinarith

theorem s81c_exp_a_integrable (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d)
    {t : ℝ} (ht : 0 ≤ t) {m : ℕ} (r : Fin m → Euc d) :
    Integrable (fun y => Real.exp (s81c_a D N x t r y)) (mu D) := by
  haveI := s81c_prob D
  exact Integrable.of_bound (C := Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M))
    (Real.measurable_exp.comp (s81c_meas_a_slice hd D N x t r)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (s81c_a_le hd D hβ0 N x ht r y))

theorem s81c_Z_bounds (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (x : Euc d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {m : ℕ} (r : Fin m → Euc d) :
    Real.exp (-(D.beta * potentialBound d ((d : ℝ) / 2) M)) ≤
        ∫ y, Real.exp (s81c_a D (m + 2) x t r y) ∂(mu D) ∧
      ∫ y, Real.exp (s81c_a D (m + 2) x t r y) ∂(mu D) ≤ Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M) := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hsd := s81c_hsd hd
  set Mg := potentialBound d ((d : ℝ) / 2) M with hMg
  have hMg0 : 0 ≤ Mg := s81c_Mg_nonneg hd D
  have hint : ∀ z, Integrable (fun y => rieszKernel d ((d : ℝ) / 2) (z - y)) (mu D) := fun z =>
    (wr13a_potential_bound hd hs0 hsd D.prob D.bound z).1
  have hconv : ∀ z, convMeasure (rieszKernel d ((d : ℝ) / 2)) (mu D) z ≤ Mg := s81c_conv_le hd D
  constructor
  · set lam : ℝ := D.beta / ((m + 2 : ℕ) : ℝ) with hlamdef
    have hlam : 0 ≤ lam := div_nonneg hβ0 (Nat.cast_nonneg _)
    obtain ⟨hui, huK⟩ := wr13a_u_integral hs0 hint hconv hlam ht.1 x r
    set u : Euc d → ℝ := fun y => lam * ∑ j, rieszKernel d ((d : ℝ) / 2) (y - r j) +
      t * lam * rieszKernel d ((d : ℝ) / 2) (x - y) with hu
    have hu0 : ∀ y, 0 ≤ u y := fun y =>
      add_nonneg (mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _))
        (mul_nonneg (mul_nonneg ht.1 hlam) (wr13a_g_nonneg hs0 _))
    have hj := wr13a_jensen (mu D) hui hu0 huK
    have hK : lam * (t + m) * Mg ≤ D.beta * Mg := by
      refine mul_le_mul_of_nonneg_right ?_ hMg0
      rw [hlamdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      push_cast
      nlinarith [ht.2, hβ0, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hge : ∀ y, Real.exp (-(u y)) ≤ Real.exp (s81c_a D (m + 2) x t r y) := fun y => by
      refine Real.exp_le_exp.2 ?_
      have := mul_nonneg hβ0 (wr13a_conv_nonneg hs0 (mu D) y)
      have e : s81c_a D (m + 2) x t r y = -(u y) + D.beta * convMeasure (critG d) (mu D) y := by
        simp only [s81c_a, s81c_k, hu, hlamdef]; ring
      rw [e]; linarith
    have hum : Measurable u :=
      ((Finset.measurable_sum _ fun j _ =>
        (wr13a_g_meas hs0).comp (measurable_id.sub measurable_const)).const_mul lam).add
        (((wr13a_g_meas hs0).comp (measurable_const.sub measurable_id)).const_mul (t * lam))
    have hint2 : Integrable (fun y => Real.exp (-(u y))) (mu D) :=
      Integrable.of_bound (C := 1) (Real.measurable_exp.comp hum.neg).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (by linarith [hu0 y]))
    calc Real.exp (-(D.beta * Mg)) ≤ Real.exp (-(lam * (t + m) * Mg)) :=
          Real.exp_le_exp.2 (by linarith)
      _ ≤ ∫ y, Real.exp (-(u y)) ∂(mu D) := hj
      _ ≤ _ := integral_mono hint2 (s81c_exp_a_integrable hd D hβ0 _ x ht.1 r) hge
  · calc ∫ y, Real.exp (s81c_a D (m + 2) x t r y) ∂(mu D) ≤ ∫ y, Real.exp (D.beta * Mg) ∂(mu D) :=
          integral_mono (s81c_exp_a_integrable hd D hβ0 _ x ht.1 r) (integrable_const _) fun y =>
            Real.exp_le_exp.2 (s81c_a_le hd D hβ0 _ x ht.1 r y)
      _ = _ := by simp

/-- Numerator `N_r(φ) = ∫ φ e^{a_r} dμ` and normaliser `Z_r = ∫ e^{a_r} dμ` as functions of the other particles. -/
def s81c_Nr (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} (φ : Euc d → ℝ) (r : Fin m → Euc d) : ℝ :=
  ∫ y, φ y * Real.exp (s81c_a D N x t r y) ∂(mu D)

def s81c_Zr (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} (r : Fin m → Euc d) : ℝ :=
  ∫ y, Real.exp (s81c_a D N x t r y) ∂(mu D)

theorem s81c_exp_a_eq (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} (r : Fin m → Euc d) (y : Euc d) :
    Real.exp (s81c_a D N x t r y) = poleFactor D N x t y * Real.exp (-s81c_k D N r y) := by
  unfold s81c_a poleFactor
  rw [← Real.exp_add, sub_eq_add_neg]

theorem s81c_exp_a_le_pf (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d) (t : ℝ)
    {m : ℕ} (r : Fin m → Euc d) (y : Euc d) :
    Real.exp (s81c_a D N x t r y) ≤ Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M) * poleFactor D N x t y := by
  have hs0 := s81c_hs0 hd
  have hlam : 0 ≤ D.beta / N := div_nonneg hβ0 (Nat.cast_nonneg _)
  rw [s81c_exp_a_eq, mul_comm]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
  have h2 : 0 ≤ (D.beta / N) * ∑ j, critG d (y - r j) :=
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => wr13a_g_nonneg hs0 _)
  have h3 : D.beta * convMeasure (critG d) (mu D) y ≤ D.beta * potentialBound d ((d : ℝ) / 2) M :=
    mul_le_mul_of_nonneg_left (s81c_conv_le hd D y) hβ0
  unfold s81c_k
  linarith

theorem s81c_poleFactor_le_one (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d) {t : ℝ}
    (ht : 0 ≤ t) (y : Euc d) : poleFactor D N x t y ≤ 1 := by
  unfold poleFactor
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.2 (mul_nonneg ht (div_nonneg hβ0 (Nat.cast_nonneg _)))) (wr13a_g_nonneg (s81c_hs0 hd) _)

theorem s81c_poleFactor_meas (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) :
    Measurable (poleFactor D N x t) := by
  unfold poleFactor
  exact Real.measurable_exp.comp (((s81b_critG_meas hd).comp (measurable_const.sub measurable_id)).const_mul _)

theorem s81c_integrable_Nr (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d) {t : ℝ}
    (ht : 0 ≤ t) {m : ℕ} (r : Fin m → Euc d) {φ : Euc d → ℝ} (hφm : Measurable φ)
    (hφi : Integrable (fun y => φ y * poleFactor D N x t y) (mu D)) :
    Integrable (fun y => φ y * Real.exp (s81c_a D N x t r y)) (mu D) := by
  refine Integrable.mono' (hφi.norm.const_mul (Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M)))
    (hφm.mul (Real.measurable_exp.comp (s81c_meas_a_slice hd D N x t r))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_mul,
    abs_of_pos (show 0 < poleFactor D N x t y from Real.exp_pos _)]
  calc |φ y| * Real.exp (s81c_a D N x t r y) ≤ |φ y| * (Real.exp (D.beta * potentialBound d ((d : ℝ) / 2) M) *
        poleFactor D N x t y) := mul_le_mul_of_nonneg_left (s81c_exp_a_le_pf hd D hβ0 N x t r y) (abs_nonneg _)
    _ = _ := by ring

theorem s81c_meas_Zr (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} :
    Measurable (fun r : Fin m → Euc d => s81c_Zr D N x t r) := by
  haveI := s81c_prob D
  unfold s81c_Zr
  have h : StronglyMeasurable fun q : (Fin m → Euc d) × Euc d => Real.exp (s81c_a D N x t q.1 q.2) :=
    (Real.measurable_exp.comp (s81c_meas_a_rj hd D N x t)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := mu D)).measurable

theorem s81c_meas_Nr (hd : 1 ≤ d) (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) {m : ℕ} {φ : Euc d → ℝ}
    (hφm : Measurable φ) : Measurable (fun r : Fin m → Euc d => s81c_Nr D N x t φ r) := by
  haveI := s81c_prob D
  unfold s81c_Nr
  have h : StronglyMeasurable fun q : (Fin m → Euc d) × Euc d =>
      φ q.2 * Real.exp (s81c_a D N x t q.1 q.2) :=
    ((hφm.comp measurable_snd).mul (Real.measurable_exp.comp (s81c_meas_a_rj hd D N x t))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := mu D)).measurable

theorem s81c_condZ_eq (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (x : Euc d) (t : ℝ)
    (Y : EucConfig d (m + 1)) :
    condZ D (m + 2) i x t Y = s81c_Zr D (m + 2) x t (Fin.removeNth i Y) := by
  unfold condZ s81c_Zr
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [s81c_exp_a_eq, s81c_field_eq D i Y y]

theorem s81c_condMean_eq (D : Data d M βm βp) {m : ℕ} (i : Fin (m + 1)) (x : Euc d) (t : ℝ) (f : Euc d → ℝ)
    (Y : EucConfig d (m + 1)) :
    condMean D (m + 2) i x t f Y =
      s81c_Nr D (m + 2) x t f (Fin.removeNth i Y) / s81c_Zr D (m + 2) x t (Fin.removeNth i Y) := by
  unfold condMean s81c_Nr
  rw [s81c_condZ_eq D i x t Y]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [s81c_exp_a_eq, s81c_field_eq D i Y y]
  ring

theorem s81c_lintegral_pole (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (x : Euc d) {t : ℝ}
    (ht : 0 ≤ t) (F : EucConfig d (m + 1) → ℝ≥0∞) (hF : Measurable F) (P : Measure (EucConfig d (m + 1)))
    (hP : P = pole D (m + 2) x t) :
    ∫⁻ Y, F Y ∂P =
      (∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y))
        ∂(Measure.pi fun _ : Fin (m + 1) => mu D))⁻¹ *
      ∫⁻ Y, F Y * ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y))
        ∂(Measure.pi fun _ : Fin (m + 1) => mu D) := by
  haveI := s81c_prob D
  have hs0 := s81c_hs0 hd
  have hP' : pole D (m + 2) x t = wr13a_tilt (Measure.pi fun _ : Fin (m + 1) => mu D)
      (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t) :=
    wr13a_poleLaw_eq hs0 (s81c_conv_le hd D) hβ0 ht (m + 2) x
  rw [hP, hP']
  exact wr13a_lintegral_tilt _ (wr13a_Ep_meas hs0 (mu D) _ D.beta x t) F hF

theorem s81c_core (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (x : Euc d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (m + 1)) (φ : Euc d → ℝ) (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφi : Integrable (fun y => φ y * poleFactor D (m + 2) x t y) (mu D))
    (χ : (Fin m → Euc d) → ℝ≥0∞) (hχ : Measurable χ) (P : Measure (EucConfig d (m + 1)))
    (hP : P = pole D (m + 2) x t) :
    ∫⁻ Y, χ (Fin.removeNth i Y) * ENNReal.ofReal (φ (Y i)) ∂P =
      ∫⁻ Y, χ (Fin.removeNth i Y) * ENNReal.ofReal (s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) /
        s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) ∂P := by
  haveI := s81c_prob D
  have hTrm : Measurable fun r : Fin m → Euc d => s81c_Nr D (m + 2) x t φ r / s81c_Zr D (m + 2) x t r :=
    (s81c_meas_Nr hd D _ x t hφm).div (s81c_meas_Zr hd D _ x t)
  have hrem : Measurable fun Y : EucConfig d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hF1 : Measurable fun Y : EucConfig d (m + 1) => χ (Fin.removeNth i Y) * ENNReal.ofReal (φ (Y i)) :=
    (hχ.comp hrem).mul (hφm.comp (measurable_pi_apply i)).ennreal_ofReal
  have hF2 : Measurable fun Y : EucConfig d (m + 1) => χ (Fin.removeNth i Y) *
      ENNReal.ofReal (s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) / s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) :=
    (hχ.comp hrem).mul (hTrm.comp hrem).ennreal_ofReal
  rw [s81c_lintegral_pole hd D hβ0 x ht.1 _ hF1 P hP, s81c_lintegral_pole hd D hβ0 x ht.1 _ hF2 P hP]
  congr 1
  have hu1 : Measurable fun y : Euc d => ENNReal.ofReal (φ y) := hφm.ennreal_ofReal
  have e1 := s81c_core_aux hd D x t i (fun y => ENNReal.ofReal (φ y)) hu1 χ hχ
  have e2 := s81c_core_aux hd D x t i (fun _ => 1) measurable_const
    (fun r => χ r * ENNReal.ofReal (s81c_Nr D (m + 2) x t φ r / s81c_Zr D (m + 2) x t r))
    (hχ.mul hTrm.ennreal_ofReal)
  simp only [mul_one] at e2
  have c1 : ∀ Y : EucConfig d (m + 1), χ (Fin.removeNth i Y) * ENNReal.ofReal (φ (Y i)) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) =
      ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) *
        (χ (Fin.removeNth i Y) * ENNReal.ofReal (φ (Y i))) := fun Y => mul_comm _ _
  have c2 : ∀ Y : EucConfig d (m + 1), χ (Fin.removeNth i Y) *
      ENNReal.ofReal (s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) / s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) *
      ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) =
      ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) *
        (χ (Fin.removeNth i Y) * ENNReal.ofReal (s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) /
          s81c_Zr D (m + 2) x t (Fin.removeNth i Y))) := fun Y => mul_comm _ _
  simp_rw [c1, c2]
  have e1' : ∫⁻ Y, ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t Y)) *
      (χ (Fin.removeNth i Y) * ENNReal.ofReal (φ (Y i))) ∂(Measure.pi fun _ : Fin (m + 1) => mu D) =
      ∫⁻ r, (ENNReal.ofReal (Real.exp (wr13a_Ep d ((d : ℝ) / 2) (mu D) (D.beta / ((m + 2 : ℕ) : ℝ)) D.beta x t r)) *
        χ r) * ∫⁻ y, ENNReal.ofReal (Real.exp (s81c_a D (m + 2) x t r y)) * ENNReal.ofReal (φ y) ∂(mu D)
        ∂(Measure.pi fun _ : Fin m => mu D) := e1
  rw [e1', e2]
  refine lintegral_congr fun r => ?_
  have hint := s81c_integrable_Nr hd D hβ0 (m + 2) x ht.1 r hφm hφi
  have hZi := s81c_exp_a_integrable hd D hβ0 (m + 2) x ht.1 r
  have hbd := s81c_Z_bounds hd D hβ0 x ht r
  have hZpos : 0 < s81c_Zr D (m + 2) x t r := lt_of_lt_of_le (Real.exp_pos _) hbd.1
  have hN : ∫⁻ y, ENNReal.ofReal (Real.exp (s81c_a D (m + 2) x t r y)) * ENNReal.ofReal (φ y) ∂(mu D) =
      ENNReal.ofReal (s81c_Nr D (m + 2) x t φ r) := by
    unfold s81c_Nr
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => mul_nonneg (hφ0 y) (Real.exp_pos _).le)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (hφ0 y), mul_comm]
  have hZ : ∫⁻ y, ENNReal.ofReal (Real.exp (s81c_a D (m + 2) x t r y)) ∂(mu D) =
      ENNReal.ofReal (s81c_Zr D (m + 2) x t r) := by
    unfold s81c_Zr
    rw [ofReal_integral_eq_lintegral_ofReal hZi (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
  have hN0 : 0 ≤ s81c_Nr D (m + 2) x t φ r :=
    integral_nonneg fun y => mul_nonneg (hφ0 y) (Real.exp_pos _).le
  rw [hN, hZ]
  have : ENNReal.ofReal (s81c_Nr D (m + 2) x t φ r / s81c_Zr D (m + 2) x t r) *
      ENNReal.ofReal (s81c_Zr D (m + 2) x t r) = ENNReal.ofReal (s81c_Nr D (m + 2) x t φ r) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hN0 hZpos.le)]
    congr 1
    field_simp
  rw [← this]
  ring

theorem s81c_Tbound (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (x : Euc d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (r : Fin m → Euc d) {φ : Euc d → ℝ} (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφi : Integrable (fun y => φ y * poleFactor D (m + 2) x t y) (mu D)) :
    0 ≤ s81c_Nr D (m + 2) x t φ r / s81c_Zr D (m + 2) x t r ∧
      s81c_Nr D (m + 2) x t φ r / s81c_Zr D (m + 2) x t r ≤
        Real.exp (2 * (D.beta * potentialBound d ((d : ℝ) / 2) M)) * ∫ y, φ y * poleFactor D (m + 2) x t y ∂(mu D) := by
  have hbd := s81c_Z_bounds hd D hβ0 x ht r
  have hZpos : 0 < s81c_Zr D (m + 2) x t r := lt_of_lt_of_le (Real.exp_pos _) hbd.1
  have hN0 : 0 ≤ s81c_Nr D (m + 2) x t φ r :=
    integral_nonneg fun y => mul_nonneg (hφ0 y) (Real.exp_pos _).le
  refine ⟨div_nonneg hN0 hZpos.le, ?_⟩
  set K : ℝ := D.beta * potentialBound d ((d : ℝ) / 2) M with hK
  set I : ℝ := ∫ y, φ y * poleFactor D (m + 2) x t y ∂(mu D) with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => mul_nonneg (hφ0 y) (Real.exp_pos _).le
  have hN : s81c_Nr D (m + 2) x t φ r ≤ Real.exp K * I := by
    unfold s81c_Nr
    rw [hI, ← integral_const_mul]
    refine integral_mono (s81c_integrable_Nr hd D hβ0 _ x ht.1 r hφm hφi) (hφi.const_mul _) fun y => ?_
    calc φ y * Real.exp (s81c_a D (m + 2) x t r y) ≤ φ y * (Real.exp K * poleFactor D (m + 2) x t y) :=
          mul_le_mul_of_nonneg_left (s81c_exp_a_le_pf hd D hβ0 _ x t r y) (hφ0 y)
      _ = _ := by ring
  rw [div_le_iff₀ hZpos]
  calc s81c_Nr D (m + 2) x t φ r ≤ Real.exp K * I := hN
    _ = Real.exp (2 * K) * I * Real.exp (-K) := by
        have h : Real.exp (2 * K) * Real.exp (-K) = Real.exp K := by
          rw [← Real.exp_add]; congr 1; ring
        calc Real.exp K * I = (Real.exp (2 * K) * Real.exp (-K)) * I := by rw [h]
          _ = _ := by ring
    _ ≤ Real.exp (2 * K) * I * s81c_Zr D (m + 2) x t r :=
        mul_le_mul_of_nonneg_left hbd.1 (mul_nonneg (Real.exp_pos _).le hI0)

theorem s81c_set_eq (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (x : Euc d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (m + 1)) {φ : Euc d → ℝ} (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hφi : Integrable (fun y => φ y * poleFactor D (m + 2) x t y) (mu D))
    {A : Set (Fin m → Euc d)} (hA : MeasurableSet A) (P : Measure (EucConfig d (m + 1)))
    (hP : P = pole D (m + 2) x t) :
    ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, φ (Y i) ∂P =
      ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A,
        (s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) / s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) ∂P := by
  haveI := s81c_prob D
  have hrem : Measurable fun Y : EucConfig d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hSm : MeasurableSet ((fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A) := hrem hA
  set χ : (Fin m → Euc d) → ℝ≥0∞ := A.indicator (fun _ => 1) with hχdef
  have hχm : Measurable χ := measurable_const.indicator hA
  have hconv : ∀ G : EucConfig d (m + 1) → ℝ, Measurable G → (∀ Y, 0 ≤ G Y) →
      ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, G Y ∂P =
        (∫⁻ Y, χ (Fin.removeNth i Y) * ENNReal.ofReal (G Y) ∂P).toReal := by
    intro G hG hG0
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0) hG.aestronglyMeasurable,
      ← lintegral_indicator hSm]
    congr 1
    refine lintegral_congr fun Y => ?_
    by_cases h : Fin.removeNth i Y ∈ A
    · have h' : Y ∈ (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A := h
      rw [Set.indicator_of_mem h', hχdef, Set.indicator_of_mem h]; simp
    · have h' : Y ∉ (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A := h
      rw [Set.indicator_of_notMem h', hχdef, Set.indicator_of_notMem h]; simp
  have hTrm : Measurable fun r : Fin m → Euc d => s81c_Nr D (m + 2) x t φ r / s81c_Zr D (m + 2) x t r :=
    (s81c_meas_Nr hd D _ x t hφm).div (s81c_meas_Zr hd D _ x t)
  have hφY : Measurable fun Y : EucConfig d (m + 1) => φ (Y i) := hφm.comp (measurable_pi_apply i)
  rw [hconv _ hφY (fun Y => hφ0 _),
    hconv (fun Y => s81c_Nr D (m + 2) x t φ (Fin.removeNth i Y) / s81c_Zr D (m + 2) x t (Fin.removeNth i Y))
      (hTrm.comp hrem) (fun Y => (s81c_Tbound hd D hβ0 x ht _ hφm hφ0 hφi).1)]
  congr 1
  exact s81c_core hd D hβ0 x ht i φ hφm hφ0 hφi χ hχm P hP

theorem s81c_int_mono {w : Euc d → ℝ} (hw : ∀ y, 0 ≤ w y) {μ : Measure (Euc d)} {f g : Euc d → ℝ}
    (hg : Measurable g) (hwm : Measurable w) (hle : ∀ y, |g y| ≤ |f y|)
    (hf : Integrable (fun y => f y * w y) μ) : Integrable (fun y => g y * w y) μ := by
  refine Integrable.mono' hf.norm (hg.mul hwm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw y)]
  exact mul_le_mul_of_nonneg_right (hle y) (hw y)

theorem s81c_int_f_pf (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d) {t : ℝ}
    (ht : 0 ≤ t) {f : Euc d → ℝ} (hfm : Measurable f)
    (hf2 : Integrable (fun y => f y ^ 2 * poleFactor D N x t y) (mu D)) :
    Integrable (fun y => f y * poleFactor D N x t y) (mu D) := by
  haveI := s81c_prob D
  have hpf := s81c_poleFactor_meas hd D N x t
  have hpf1 := s81c_poleFactor_le_one hd D hβ0 N x ht
  have hpfi : Integrable (fun y => poleFactor D N x t y) (mu D) :=
    Integrable.of_bound (C := 1) hpf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (show 0 < poleFactor D N x t y from Real.exp_pos _)]; exact hpf1 y)
  refine Integrable.mono' ((hf2.add hpfi).const_mul (1 / 2))
    (hfm.mul hpf).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hp0 : 0 < poleFactor D N x t y := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp0]
  have : |f y| ≤ (f y ^ 2 + 1) / 2 := by
    nlinarith [sq_nonneg (|f y| - 1), sq_abs (f y)]
  calc |f y| * poleFactor D N x t y ≤ (f y ^ 2 + 1) / 2 * poleFactor D N x t y :=
        mul_le_mul_of_nonneg_right this hp0.le
    _ = 1 / 2 * (f y ^ 2 * poleFactor D N x t y + poleFactor D N x t y) := by ring

theorem s81c_pole_prob (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) (N : ℕ) (x : Euc d) {t : ℝ}
    (ht : 0 ≤ t) : IsProbabilityMeasure (pole D N x t) := by
  haveI := s81c_prob D
  exact wr13b_poleLaw_isProb (s81c_hs0 hd) (s81c_conv_le hd D) hβ0 ht N x

set_option maxHeartbeats 800000 in
theorem s81c_cond_kernel_m (hd : 1 ≤ d) (D : Data d M βm βp) (hβ0 : 0 ≤ D.beta) {m : ℕ} (x : Euc d) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin (m + 1)) {f : Euc d → ℝ} (hfm : Measurable f)
    (hf2 : Integrable (fun y => f y ^ 2 * poleFactor D (m + 2) x t y) (mu D))
    (P : Measure (EucConfig d (m + 1))) (hP : P = pole D (m + 2) x t) :
    MemLp (fun Y : EucConfig d (m + 1) => f (Y i)) 2 P ∧
      StronglyMeasurable[othersSigma i] (condMean D (m + 2) i x t f) ∧
      P[(fun Y : EucConfig d (m + 1) => f (Y i)) | othersSigma i] =ᵐ[P] condMean D (m + 2) i x t f := by
  haveI := s81c_prob D
  have hPprob : IsProbabilityMeasure P := by
    rw [hP]; exact s81c_pole_prob hd D hβ0 _ x ht.1
  have hpf := s81c_poleFactor_meas hd D (m + 2) x t
  have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
  have hfi := s81c_int_f_pf hd D hβ0 (m + 2) x ht.1 hfm hf2
  set K : ℝ := 2 * (D.beta * potentialBound d ((d : ℝ) / 2) M) with hK
  have hrem : Measurable fun Y : EucConfig d (m + 1) => Fin.removeNth i Y :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  have hfY : Measurable fun Y : EucConfig d (m + 1) => f (Y i) := hfm.comp (measurable_pi_apply i)
  -- the positive and negative parts
  set fp : Euc d → ℝ := fun y => max (f y) 0 with hfp
  set fn : Euc d → ℝ := fun y => max (-f y) 0 with hfn
  have hfpm : Measurable fp := hfm.max measurable_const
  have hfnm : Measurable fn := hfm.neg.max measurable_const
  have hfp0 : ∀ y, 0 ≤ fp y := fun y => le_max_right _ _
  have hfn0 : ∀ y, 0 ≤ fn y := fun y => le_max_right _ _
  have hfp_le : ∀ y, |fp y| ≤ |f y| := fun y => by
    rw [abs_of_nonneg (hfp0 y)]; exact max_le (le_abs_self _) (abs_nonneg _)
  have hfn_le : ∀ y, |fn y| ≤ |f y| := fun y => by
    rw [abs_of_nonneg (hfn0 y)]; exact max_le (neg_le_abs _) (abs_nonneg _)
  have hfpi := s81c_int_mono hpf0 hfpm hpf hfp_le hfi
  have hfni := s81c_int_mono hpf0 hfnm hpf hfn_le hfi
  have hfsplit : ∀ y, f y = fp y - fn y := fun y => by
    simp only [hfp, hfn]
    rcases le_total (f y) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  -- f(Y_i)^2 is integrable
  have hsq : Integrable (fun Y : EucConfig d (m + 1) => f (Y i) ^ 2) P := by
    have hcore := s81c_core hd D hβ0 x ht i (fun y => f y ^ 2) (hfm.pow_const 2) (fun y => sq_nonneg _) hf2
      (fun _ => 1) measurable_const P hP
    set c : ℝ := Real.exp K * ∫ y, f y ^ 2 * poleFactor D (m + 2) x t y ∂(mu D) with hc
    have hc0 : 0 ≤ c := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hpf0 y))
    refine (Q34.integrable_of_lintegral_le (hfY.pow_const 2) (fun Y => sq_nonneg _) hc0 ?_).1
    have h1 : ∫⁻ Y, ENNReal.ofReal (f (Y i) ^ 2) ∂P =
        ∫⁻ Y, ENNReal.ofReal (s81c_Nr D (m + 2) x t (fun y => f y ^ 2) (Fin.removeNth i Y) /
          s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) ∂P := by
      simpa only [one_mul] using hcore
    rw [h1]
    calc ∫⁻ Y, ENNReal.ofReal (s81c_Nr D (m + 2) x t (fun y => f y ^ 2) (Fin.removeNth i Y) /
          s81c_Zr D (m + 2) x t (Fin.removeNth i Y)) ∂P ≤ ∫⁻ _Y, ENNReal.ofReal c ∂P :=
          lintegral_mono fun Y => ENNReal.ofReal_le_ofReal
            (s81c_Tbound hd D hβ0 x ht _ (hfm.pow_const 2) (fun y => sq_nonneg _) hf2).2
      _ = ENNReal.ofReal c := by simp
  have hmem : MemLp (fun Y : EucConfig d (m + 1) => f (Y i)) 2 P :=
    (memLp_two_iff_integrable_sq hfY.aestronglyMeasurable).2 hsq
  have hfYi : Integrable (fun Y : EucConfig d (m + 1) => f (Y i)) P := hmem.integrable one_le_two
  -- T parts
  set Tp : (Fin m → Euc d) → ℝ := fun r => s81c_Nr D (m + 2) x t fp r / s81c_Zr D (m + 2) x t r with hTp
  set Tn : (Fin m → Euc d) → ℝ := fun r => s81c_Nr D (m + 2) x t fn r / s81c_Zr D (m + 2) x t r with hTn
  have hTpm : Measurable Tp := (s81c_meas_Nr hd D _ x t hfpm).div (s81c_meas_Zr hd D _ x t)
  have hTnm : Measurable Tn := (s81c_meas_Nr hd D _ x t hfnm).div (s81c_meas_Zr hd D _ x t)
  have hTpb := fun r => s81c_Tbound hd D hβ0 x ht r hfpm hfp0 hfpi
  have hTnb := fun r => s81c_Tbound hd D hβ0 x ht r hfnm hfn0 hfni
  have hcm : ∀ r, s81c_Nr D (m + 2) x t f r / s81c_Zr D (m + 2) x t r = Tp r - Tn r := fun r => by
    simp only [hTp, hTn, ← sub_div]
    congr 1
    unfold s81c_Nr
    rw [← integral_sub (s81c_integrable_Nr hd D hβ0 _ x ht.1 r hfpm hfpi)
      (s81c_integrable_Nr hd D hβ0 _ x ht.1 r hfnm hfni)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hfsplit y]
    ring_nf
  have hcmeq : condMean D (m + 2) i x t f = fun Y : EucConfig d (m + 1) => Tp (Fin.removeNth i Y) - Tn (Fin.removeNth i Y) := by
    funext Y
    rw [s81c_condMean_eq D i x t f Y, hcm]
  have hTpi : Integrable (fun Y : EucConfig d (m + 1) => Tp (Fin.removeNth i Y)) P :=
    Integrable.of_bound (C := Real.exp K * ∫ y, fp y * poleFactor D (m + 2) x t y ∂(mu D))
      (hTpm.comp hrem).aestronglyMeasurable (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hTpb _).1]; exact (hTpb _).2)
  have hTni : Integrable (fun Y : EucConfig d (m + 1) => Tn (Fin.removeNth i Y)) P :=
    Integrable.of_bound (C := Real.exp K * ∫ y, fn y * poleFactor D (m + 2) x t y ∂(mu D))
      (hTnm.comp hrem).aestronglyMeasurable (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hTnb _).1]; exact (hTnb _).2)
  have hm : othersSigma (d := d) i ≤ MeasurableSpace.pi :=
    (measurable_pi_iff.2 fun j => measurable_pi_apply _ :
      Measurable (fun (Y : EucConfig d (m + 1)) (j : {j // j ≠ i}) => Y j)).comap_le
  have hΛ : Measurable fun (w : {j : Fin (m + 1) // j ≠ i} → Euc d) =>
      (fun j' : Fin m => w ⟨i.succAbove j', Fin.succAbove_ne i j'⟩) :=
    measurable_pi_iff.2 fun j' => measurable_pi_apply _
  have hsm : StronglyMeasurable[othersSigma i] (condMean D (m + 2) i x t f) := by
    have hG : Measurable[othersSigma i] fun Y : EucConfig d (m + 1) => Tp (Fin.removeNth i Y) - Tn (Fin.removeNth i Y) := by
      have h1 := ((hTpm.sub hTnm).comp hΛ).comp
        (comap_measurable (m := MeasurableSpace.pi)
          (fun (Y : EucConfig d (m + 1)) (j : {j // j ≠ i}) => Y j))
      exact h1
    rw [hcmeq]
    exact hG.stronglyMeasurable
  refine ⟨hmem, hsm, ?_⟩
  have hbdd : ∃ B : ℝ, ∀ Y : EucConfig d (m + 1), |condMean D (m + 2) i x t f Y| ≤ B := by
    refine ⟨Real.exp K * ∫ y, fp y * poleFactor D (m + 2) x t y ∂(mu D) +
      Real.exp K * ∫ y, fn y * poleFactor D (m + 2) x t y ∂(mu D), fun Y => ?_⟩
    rw [hcmeq]
    simp only
    calc |Tp (Fin.removeNth i Y) - Tn (Fin.removeNth i Y)| ≤ |Tp (Fin.removeNth i Y)| + |Tn (Fin.removeNth i Y)| :=
          abs_sub _ _
      _ ≤ _ := by
          rw [abs_of_nonneg (hTpb _).1, abs_of_nonneg (hTnb _).1]
          exact add_le_add (hTpb _).2 (hTnb _).2
  obtain ⟨B, hB⟩ := hbdd
  have hcmm : Measurable (condMean D (m + 2) i x t f) := by
    rw [hcmeq]; exact (hTpm.comp hrem).sub (hTnm.comp hrem)
  have hcmi : Integrable (condMean D (m + 2) i x t f) P :=
    Integrable.of_bound (C := B) hcmm.aestronglyMeasurable (Filter.Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs]; exact hB Y)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hfYi (fun S _ _ => hcmi.integrableOn) ?_
    hsm.aestronglyMeasurable).symm
  intro S hS hSfin
  obtain ⟨A', hA', rfl⟩ := (MeasurableSpace.measurableSet_comap).1 hS
  have hSm : MeasurableSet ((fun (Y : EucConfig d (m + 1)) (j : {j // j ≠ i}) => Y j) ⁻¹' A') := hm _ hS
  choose c' hc' using fun j : {j : Fin (m + 1) // j ≠ i} => Fin.exists_succAbove_eq j.2
  let Λ' : (Fin m → Euc d) → ({j : Fin (m + 1) // j ≠ i} → Euc d) := fun r j => r (c' j)
  have hΛ'm : Measurable Λ' := measurable_pi_iff.2 fun j => measurable_pi_apply _
  set A : Set (Fin m → Euc d) := Λ' ⁻¹' A' with hAdef
  have hAm : MeasurableSet A := hΛ'm hA'
  have hS_eq : ((fun (Y : EucConfig d (m + 1)) (j : {j // j ≠ i}) => Y j) ⁻¹' A') =
      (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A := by
    ext Y
    simp only [Set.mem_preimage, hAdef]
    have : (fun j : {j // j ≠ i} => Y j) = Λ' (Fin.removeNth i Y) := by
      funext j
      simp only [Λ', Fin.removeNth]
      rw [hc' j]
    rw [this]
  rw [hS_eq]
  have e1 := s81c_set_eq hd D hβ0 x ht i hfpm hfp0 hfpi hAm P hP
  have e2 := s81c_set_eq hd D hβ0 x ht i hfnm hfn0 hfni hAm P hP
  have hfp_i : Integrable (fun Y : EucConfig d (m + 1) => fp (Y i)) P :=
    hfYi.pos_part
  have hfn_i : Integrable (fun Y : EucConfig d (m + 1) => fn (Y i)) P :=
    hfYi.neg_part
  have lhs : ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, f (Y i) ∂P =
      ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, fp (Y i) ∂P -
        ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, fn (Y i) ∂P := by
    rw [← integral_sub hfp_i.integrableOn hfn_i.integrableOn]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Y => hfsplit _)
  have rhs : ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, condMean D (m + 2) i x t f Y ∂P =
      ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, Tp (Fin.removeNth i Y) ∂P -
        ∫ Y in (fun Y : EucConfig d (m + 1) => Fin.removeNth i Y) ⁻¹' A, Tn (Fin.removeNth i Y) ∂P := by
    rw [← integral_sub hTpi.integrableOn hTni.integrableOn, hcmeq]
  rw [lhs, rhs]
  rw [e1, e2]

/-- CR03: the exact conditional kernel of one pole coordinate given the others. -/
theorem s81c_conditional_kernel (hd : 2 ≤ d) (M βm βp : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ i : Fin (N - 1), ∀ x : Euc d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (∀ Y, C⁻¹ ≤ condZ D N i x t Y ∧ condZ D N i x t Y ≤ C) ∧
        ∀ f : Euc d → ℝ, Measurable f →
          Integrable (fun y => f y ^ 2 * poleFactor D N x t y) (mu D) →
          MemLp (fun Y => f (Y i)) 2 (pole D N x t) ∧
          StronglyMeasurable[othersSigma i] (condMean D N i x t f) ∧
          (pole D N x t)[(fun Y => f (Y i)) | othersSigma i] =ᵐ[pole D N x t]
            condMean D N i x t f := by
  have hd1 : 1 ≤ d := by omega
  set Mg : ℝ := potentialBound d ((d : ℝ) / 2) M with hMg
  have hβp : 0 ≤ βp := (hβm.trans_le hβ).le
  refine ⟨Real.exp (βp * |Mg|), Real.one_le_exp (by positivity), fun D N hN i x t ht => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hMg0 : 0 ≤ Mg := s81c_Mg_nonneg hd1 D
  have hββ : D.beta ≤ βp := D.beta_mem.2
  refine ⟨fun Y => ?_, fun f hfm hf2 => s81c_cond_kernel_m hd1 D hβ0.le x ht i hfm hf2 (pole D (m + 2) x t) rfl⟩
  rw [s81c_condZ_eq D i x t Y]
  obtain ⟨h1, h2⟩ := s81c_Z_bounds hd1 D hβ0.le x ht (Fin.removeNth i Y)
  have hb : D.beta * Mg ≤ βp * |Mg| :=
    mul_le_mul hββ (le_abs_self _) hMg0 hβp
  refine ⟨?_, h2.trans (Real.exp_le_exp.2 hb)⟩
  rw [← Real.exp_neg]
  exact le_trans (Real.exp_le_exp.2 (neg_le_neg hb)) h1

end HRS.Whole.S81b
