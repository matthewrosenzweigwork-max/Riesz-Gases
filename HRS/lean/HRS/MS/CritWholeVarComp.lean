import HRS.MS.CritWholeObservation
import HRS.MS.CritWholePrefactor
import HRS.Equilibrium.L49Aux7

/-!
# S8.1 XS (S81c), CR08: comparison of the pole variance of `∑_i g(x - Y_i)` with `(N-1) ∫ g² e^{-tλg} dμ`

The generic covariance identity `L49.l49_variance_identity` (with the sub-σ-algebras `othersSigma i`) reduces the comparison to
three inputs: the diagonal `E f_i² ≈ ∫ g² e^{-tλg}` (prefactor, CR05), `E T_i² ≤ C` and the covariances
`Cov(S, T_i) = Cov(S, T_i - F/B)` (Cauchy-Schwarz with CR07 and the pole variance).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- Generic comparison from the three inputs of the variance identity. -/
theorem s81c_var_compare {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    (m : Fin n → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ) (f : Fin n → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 P)
    (hfm : ∀ i j, j ≠ i → StronglyMeasurable[m i] (f j)) {q dq τ κ : ℝ} (c : Fin n → ℝ)
    (hdiag : ∀ i, |∫ ω, f i ω ^ 2 ∂P - q| ≤ dq) (hT : ∀ i, ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P ≤ τ)
    (hcov : ∀ i, |∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i) ∂P| ≤ κ) :
    |variance (fun ω => ∑ j, f j ω) P - n * q| ≤ n * (dq + τ + κ) := by
  have hSm : MemLp (fun ω => ∑ j, f j ω) 2 P := memLp_finsetSum _ fun j _ => hf j
  have hES : ∫ ω, ∑ j, f j ω ∂P = ∑ j, ∫ ω', f j ω' ∂P :=
    integral_finset_sum _ fun j _ => (hf j).integrable one_le_two
  have hvar : variance (fun ω => ∑ j, f j ω) P = ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) ^ 2 ∂P := by
    rw [variance_eq_integral hSm.aestronglyMeasurable.aemeasurable, hES]
  have hid := L49.l49_variance_identity m hm f hf hfm
  have hcen : ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) ∂P = 0 := by
    rw [integral_sub (hSm.integrable one_le_two) (integrable_const _), hES]; simp
  have hshift : ∀ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - ∫ ω', f i ω' ∂P) ∂P =
      ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i) ∂P := by
    intro i
    have hT' : MemLp (P[f i | m i]) 2 P := (hf i).condExp (by norm_num)
    have hF : MemLp (fun ω => ∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) 2 P := hSm.sub (memLp_const _)
    have i1 : Integrable (fun ω => (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i)) P :=
      hF.integrable_mul (hT'.sub (memLp_const _))
    have i2 : Integrable (fun ω => (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * (c i - ∫ ω', f i ω' ∂P)) P :=
      (hF.integrable one_le_two).mul_const _
    have e : ∀ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - ∫ ω', f i ω' ∂P) =
        (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i) +
          (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * (c i - ∫ ω', f i ω' ∂P) := fun ω => by ring
    simp_rw [e]
    rw [integral_add i1 i2, integral_mul_const, hcen]; simp
  rw [hvar, hid]
  simp_rw [hshift]
  have hdiag' : ∀ i, |(∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P) - q| ≤ dq + τ := fun i => by
    have h0 : 0 ≤ ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have h1 := hdiag i
    have h2 := hT i
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  calc |∑ i, (∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P) +
        ∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i) ∂P - n * q|
      = |∑ i, ((∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P) - q) +
        ∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i) ∂P| := by
          congr 1
          rw [Finset.sum_sub_distrib]; simp; ring
    _ ≤ |∑ i, ((∫ ω, f i ω ^ 2 ∂P - ∫ ω, ((P[f i | m i]) ω) ^ 2 ∂P) - q)| +
        |∑ i, ∫ ω, (∑ j, f j ω - ∑ j, ∫ ω', f j ω' ∂P) * ((P[f i | m i]) ω - c i) ∂P| := abs_add_le _ _
    _ ≤ ∑ i : Fin n, (dq + τ) + ∑ i : Fin n, κ := by
          refine add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hdiag' i))
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hcov i))
    _ = n * (dq + τ + κ) := by simp; ring

/-- Cauchy-Schwarz in `L²(P)`. -/
theorem s81c_csP {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {a b : Ω → ℝ}
    (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    (∫ ω, a ω * b ω ∂P) ^ 2 ≤ (∫ ω, a ω ^ 2 ∂P) * ∫ ω, b ω ^ 2 ∂P := by
  have ha2 : Integrable (fun ω => a ω ^ 2) P := ha.integrable_sq
  have hb2 : Integrable (fun ω => b ω ^ 2) P := hb.integrable_sq
  have hab : Integrable (fun ω => a ω * b ω) P := ha.integrable_mul hb
  have key : ∀ t : ℝ, 0 ≤ (∫ ω, a ω ^ 2 ∂P) * (t * t) + (-2 * ∫ ω, a ω * b ω ∂P) * t + ∫ ω, b ω ^ 2 ∂P := by
    intro t
    have h_a2 : Integrable (fun ω => t * t * a ω ^ 2) P := ha2.const_mul _
    have h_ab : Integrable (fun ω => 2 * t * (a ω * b ω)) P := hab.const_mul _
    have h_sub : Integrable (fun ω => t * t * a ω ^ 2 - 2 * t * (a ω * b ω)) P := h_a2.sub h_ab
    have : (∫ ω, a ω ^ 2 ∂P) * (t * t) + (-2 * ∫ ω, a ω * b ω ∂P) * t + ∫ ω, b ω ^ 2 ∂P =
        ∫ ω, (t * a ω - b ω) ^ 2 ∂P := by
      have e : ∀ ω, (t * a ω - b ω) ^ 2 = t * t * a ω ^ 2 - 2 * t * (a ω * b ω) + b ω ^ 2 := fun ω => by ring
      simp_rw [e]
      rw [integral_add h_sub hb2, integral_sub h_a2 h_ab, integral_const_mul, integral_const_mul]
      ring
    rw [this]
    exact integral_nonneg fun ω => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem s81c_sq_le_of_eLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {b : Ω → ℝ}
    (hb : MemLp b 2 P) (hbm : Measurable b) {e : ℝ} (he : 0 ≤ e) (h : eLpNorm b 2 P ≤ ENNReal.ofReal e) :
    ∫ ω, b ω ^ 2 ∂P ≤ e ^ 2 := by
  rw [s81c_eLp_sq hbm hb.integrable_sq, ENNReal.ofReal_le_ofReal_iff he] at h
  have := Real.sqrt_le_left he |>.1 h
  exact this

theorem s81c_logJ (d : ℕ) {u : ℝ} (hd : 1 ≤ d) : wr13c_J d ((d : ℝ) / 2) u = 1 + |Real.log u| := by
  unfold wr13c_J
  have : ¬ (2 * ((d : ℝ) / 2) < d) := by
    have : (2 : ℝ) * ((d : ℝ) / 2) = d := by ring
    rw [this]; exact lt_irrefl _
  rw [if_neg this, if_pos (by ring)]

theorem s81c_sqRow_le (hd : 2 ≤ d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ), 0 < t → 0 < D.beta → 0 < N →
      Integrable (fun y => critG d (x - y) ^ 2 * poleFactor D N x t y) (mu D) ∧
        squareRow D N x t ≤ C * logMajorant D N t := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC0, hC⟩ := wr13c_radial_J_integral hd1 (s81c_hs0 hd1) (s81c_hsd hd1) M
  refine ⟨C, hC0, fun D N x t ht hβ0 hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 < t * (D.beta / N) := by positivity
  obtain ⟨hI, hB⟩ := hC D.rho D.prob D.bound (t * (D.beta / N)) hu x
  have e : ∀ y, critG d (x - y) ^ 2 * poleFactor D N x t y =
      rieszKernel d ((d : ℝ) / 2) (x - y) ^ 2 * Real.exp (-(t * (D.beta / N) * rieszKernel d ((d : ℝ) / 2) (x - y))) := by
    intro y; unfold poleFactor; congr 1; congr 1; ring
  simp_rw [e]
  refine ⟨hI, ?_⟩
  unfold squareRow logMajorant
  simp_rw [e]
  rw [s81c_logJ d hd1] at hB
  exact hB

set_option maxHeartbeats 3200000 in
theorem s81c_pole_variance_comparison (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N →
      ∀ x : Euc d, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
        MemLp (poleSum d N x) 2 (pole D N x t) ∧
        |Var[poleSum d N x; pole D N x t] -
            ((N - 1 : ℕ) : ℝ) * squareRow D N x t| ≤
          C * ((N - 1 : ℕ) : ℝ) *
            (1 + Real.sqrt (logMajorant D N t) +
              Real.sqrt (deltaN d ((d : ℝ) / 2) N) * logMajorant D N t) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C5, hC50, hC5⟩ := s81c_pole_prefactor hd M βm βp hβm hβ
  obtain ⟨C7, hC70, hC7⟩ := s81c_conditional_observation hd M βm βp hβm hβ
  obtain ⟨Cv, hCv0, hCv⟩ := wr13b_pole_variance hd (s81c_hs0 hd1) (s81c_hsd hd1) βp M
  obtain ⟨Cj, hCj0, hCj⟩ := s81c_sqRow_le (βm := βm) (βp := βp) hd M
  refine ⟨C5 * Cj + C7 + C7 * Real.sqrt (Cv * Cj), by positivity, fun D N hN x t ht => ?_⟩
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  haveI := s81c_prob D
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  obtain ⟨P, hP⟩ : ∃ P : Measure (EucConfig d (m + 1)), P = pole D (m + 2) x t := ⟨_, rfl⟩
  have hPprob : IsProbabilityMeasure P := by rw [hP]; exact s81c_pole_prob hd1 D hβ0.le _ x ht.1.le
  obtain ⟨hsqI, hsq⟩ := hCj D (m + 2) x t ht.1 hβ0 (by omega)
  set L : ℝ := logMajorant D (m + 2) t with hL
  have hL1 : 1 ≤ L := by rw [hL]; unfold logMajorant; linarith [abs_nonneg (Real.log (t * (D.beta / ((m + 2 : ℕ) : ℝ))))]
  set sqRow : ℝ := squareRow D (m + 2) x t with hsqRow
  have hsqRow0 : 0 ≤ sqRow := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  set δ : ℝ := deltaN d ((d : ℝ) / 2) (m + 2) with hδ
  have hδ0 : 0 ≤ δ := (inv_nonneg.2 (Nat.cast_nonneg _)).trans (s81c_num_facts hd1 hN).1
  set f : Fin (m + 1) → EucConfig d (m + 1) → ℝ := fun i Y => critG d (x - Y i) with hf
  have hg := s81b_critG_meas hd1
  have hfmeas : ∀ i, Measurable (f i) := fun i => hg.comp (measurable_const.sub (measurable_pi_apply i))
  have hobs := fun i : Fin (m + 1) => hC7 D (m + 2) hN i x t ht
  have hmemP : ∀ i, MemLp (f i) 2 P := fun i => by
    have h := (hobs i).1
    rw [hP]; exact h
  have hS : MemLp (fun Y : EucConfig d (m + 1) => ∑ j, f j Y) 2 P := memLp_finsetSum _ fun j _ => hmemP j
  have hm : ∀ i : Fin (m + 1), othersSigma (d := d) i ≤ MeasurableSpace.pi := fun i =>
    (measurable_pi_iff.2 fun j => measurable_pi_apply _ :
      Measurable (fun (Y : EucConfig d (m + 1)) (j : {j : Fin (m + 1) // j ≠ i}) => Y j)).comap_le
  have hfm : ∀ i j : Fin (m + 1), j ≠ i → StronglyMeasurable[othersSigma i] (f j) := by
    intro i j hj
    have hΛ : Measurable fun w : {k : Fin (m + 1) // k ≠ i} → Euc d => critG d (x - w ⟨j, hj⟩) :=
      hg.comp (measurable_const.sub (measurable_pi_apply (⟨j, hj⟩ : {k : Fin (m + 1) // k ≠ i})))
    have h1 := hΛ.comp (comap_measurable (m := MeasurableSpace.pi)
      (fun (Y : EucConfig d (m + 1)) (k : {k : Fin (m + 1) // k ≠ i}) => Y k))
    exact (h1 : Measurable[othersSigma i] (f j)).stronglyMeasurable
  -- the diagonal
  have hdiag : ∀ i : Fin (m + 1), |∫ Y, f i Y ^ 2 ∂P - sqRow| ≤ C5 * Real.sqrt δ * (Cj * L) := by
    intro i
    obtain ⟨hprem, hden, hpre⟩ := hC5 D (m + 2) hN i x t ht'
    have hpf := s81c_poleFactor_meas hd1 D (m + 2) x t
    have hpf0 : ∀ y, 0 ≤ poleFactor D (m + 2) x t y := fun y => (Real.exp_pos _).le
    have hpre0 : ∀ y, 0 ≤ prefactor D (m + 2) i x t y := fun y => by
      rw [s81c_prefactor_eq]
      exact integral_nonneg fun Y => (s81c_W_bounds hd1 D hβ0.le i x ht' Y y).1
    have hgm2 : Measurable fun z : Euc d => critG d (x - z) ^ 2 :=
      (hg.comp (measurable_const.sub measurable_id)).pow_const 2
    have hφm : Measurable fun z => poleFactor D (m + 2) x t z * prefactor D (m + 2) i x t z := hpf.mul hprem
    have hmap : P.map (fun Y => Y i) = (mu D).withDensity
        (fun z => ENNReal.ofReal (poleFactor D (m + 2) x t z * prefactor D (m + 2) i x t z)) := by
      have h := s81c_marg_coord hd1 D hβ0.le hN x ht.1.le i
      rw [hP]; exact h.trans hden
    have hint : ∫ Y, f i Y ^ 2 ∂P =
        ∫ z, poleFactor D (m + 2) x t z * prefactor D (m + 2) i x t z * critG d (x - z) ^ 2 ∂(mu D) := by
      have := integral_map (μ := P) (φ := fun Y : EucConfig d (m + 1) => Y i) (f := fun z : Euc d => critG d (x - z) ^ 2)
        (measurable_pi_apply i).aemeasurable hgm2.aestronglyMeasurable
      rw [hmap, s81b_integral_withDensity hφm (fun z => mul_nonneg (hpf0 z) (hpre0 z))] at this
      exact this.symm
    rw [hint, hsqRow]
    unfold squareRow
    have hI1 : Integrable (fun z => poleFactor D (m + 2) x t z * prefactor D (m + 2) i x t z *
        critG d (x - z) ^ 2) (mu D) := by
      refine Integrable.mono' (hsqI.const_mul (1 + C5 * Real.sqrt δ)) (hφm.mul hgm2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      have h1 := hpre z
      have h2 : prefactor D (m + 2) i x t z ≤ 1 + C5 * Real.sqrt δ := by linarith [(abs_le.1 h1).2]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hpf0 z) (hpre0 z)) (sq_nonneg _))]
      calc poleFactor D (m + 2) x t z * prefactor D (m + 2) i x t z * critG d (x - z) ^ 2
          = prefactor D (m + 2) i x t z * (critG d (x - z) ^ 2 * poleFactor D (m + 2) x t z) := by ring
        _ ≤ (1 + C5 * Real.sqrt δ) * (critG d (x - z) ^ 2 * poleFactor D (m + 2) x t z) :=
            mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg _) (hpf0 z))
    have hdiff : ∫ z, poleFactor D (m + 2) x t z * prefactor D (m + 2) i x t z * critG d (x - z) ^ 2 ∂(mu D) -
        ∫ y, critG d (x - y) ^ 2 * poleFactor D (m + 2) x t y ∂(mu D) =
        ∫ z, (critG d (x - z) ^ 2 * poleFactor D (m + 2) x t z) * (prefactor D (m + 2) i x t z - 1) ∂(mu D) := by
      rw [← integral_sub hI1 hsqI]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only; ring
    rw [hdiff]
    calc |∫ z, (critG d (x - z) ^ 2 * poleFactor D (m + 2) x t z) * (prefactor D (m + 2) i x t z - 1) ∂(mu D)|
        ≤ ∫ z, C5 * Real.sqrt δ * (critG d (x - z) ^ 2 * poleFactor D (m + 2) x t z) ∂(mu D) := by
          refine (abs_integral_le_integral_abs).trans (integral_mono ?_ (hsqI.const_mul _) fun z => ?_)
          · exact (hI1.sub hsqI |>.congr (Filter.Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring)).abs
          · rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hpf0 z))]
            calc _ ≤ (critG d (x - z) ^ 2 * poleFactor D (m + 2) x t z) * (C5 * Real.sqrt δ) :=
                  mul_le_mul_of_nonneg_left (hpre z) (mul_nonneg (sq_nonneg _) (hpf0 z))
              _ = _ := mul_comm _ _
      _ = C5 * Real.sqrt δ * ∫ y, critG d (x - y) ^ 2 * poleFactor D (m + 2) x t y ∂(mu D) := integral_const_mul _ _
      _ ≤ C5 * Real.sqrt δ * (Cj * L) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
  -- the conditional second moments
  have hT : ∀ i : Fin (m + 1), ∫ Y, ((P[f i | othersSigma i]) Y) ^ 2 ∂P ≤ C7 := by
    intro i
    have hTmem : MemLp (P[f i | othersSigma i]) 2 P := (hmemP i).condExp (by norm_num)
    have hl := (hobs i).2.2.2
    have hl' : ∫⁻ Y, ‖(P[f i | othersSigma i]) Y‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C7 := by rw [hP]; exact hl
    have e : ∫⁻ Y, ‖(P[f i | othersSigma i]) Y‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ Y, ((P[f i | othersSigma i]) Y) ^ 2 ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal hTmem.integrable_sq (Filter.Eventually.of_forall fun Y => sq_nonneg _)]
      refine lintegral_congr fun Y => ?_
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e, ENNReal.ofReal_le_ofReal_iff hC70] at hl'
    exact hl'
  -- the variance of the sum
  set n : ℝ := ((m + 1 : ℕ) : ℝ) with hn
  have hvarS : variance (fun Y : EucConfig d (m + 1) => ∑ j, f j Y) P ≤ Cv * n * sqRow := by
    have h := hCv D.rho D.prob D.bound D.beta hβ0 hββp (m + 2) hN x t ht' (fun z => critG d (x - z))
      (hg.comp (measurable_const.sub measurable_id))
    have hl : ∫⁻ y, ‖critG d (x - y)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (D.beta / ((m + 2 : ℕ) : ℝ))) *
        rieszKernel d ((d : ℝ) / 2) (x - y))) ∂(withDensityReal D.rho) = ENNReal.ofReal sqRow := by
      rw [hsqRow]; unfold squareRow
      rw [ofReal_integral_eq_lintegral_ofReal hsqI (Filter.Eventually.of_forall fun y =>
        mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
      rfl
    have hle : evariance (fun Y : EucConfig d (m + 1) => ∑ j, f j Y) P ≤ ENNReal.ofReal (Cv * n * sqRow) := by
      rw [hP]
      refine h.trans ?_
      rw [hl, ← ENNReal.ofReal_mul (by positivity)]
      exact le_rfl
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  -- the covariances
  have hcov : ∀ i : Fin (m + 1), |∫ Y, (∑ j, f j Y - ∑ j, ∫ Y', f j Y' ∂P) *
      ((P[f i | othersSigma i]) Y - poleF D (m + 2) x t / poleB D (m + 2) x t) ∂P| ≤
      Real.sqrt (Cv * n * sqRow) * (C7 * (((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) := by
    intro i
    have hTmem : MemLp (P[f i | othersSigma i]) 2 P := (hmemP i).condExp (by norm_num)
    have hFc : MemLp (fun Y : EucConfig d (m + 1) => ∑ j, f j Y - ∑ j, ∫ Y', f j Y' ∂P) 2 P :=
      hS.sub (memLp_const _)
    have hBc : MemLp (fun Y => (P[f i | othersSigma i]) Y - poleF D (m + 2) x t / poleB D (m + 2) x t) 2 P :=
      hTmem.sub (memLp_const _)
    have hcs := s81c_csP hFc hBc
    have hF2 : ∫ Y, (∑ j, f j Y - ∑ j, ∫ Y', f j Y' ∂P) ^ 2 ∂P ≤ Cv * n * sqRow := by
      have hES : ∫ Y, ∑ j, f j Y ∂P = ∑ j, ∫ Y', f j Y' ∂P :=
        integral_finsetSum _ fun j _ => (hmemP j).integrable one_le_two
      have := variance_eq_integral (μ := P) hS.aestronglyMeasurable.aemeasurable
      rw [hES] at this
      rw [← this]; exact hvarS
    have hB2 : ∫ Y, ((P[f i | othersSigma i]) Y - poleF D (m + 2) x t / poleB D (m + 2) x t) ^ 2 ∂P ≤
        (C7 * (((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2 := by
      have hr0 : 0 ≤ ((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
      refine s81c_sq_le_of_eLp hBc ?_ (by positivity) ?_
      · exact (stronglyMeasurable_condExp.mono (hm i) |>.measurable).sub_const _
      · have h := (hobs i).2.1
        rw [hP]; exact h
    have habs : |∫ Y, (∑ j, f j Y - ∑ j, ∫ Y', f j Y' ∂P) *
        ((P[f i | othersSigma i]) Y - poleF D (m + 2) x t / poleB D (m + 2) x t) ∂P| ≤
        Real.sqrt ((Cv * n * sqRow) * (C7 * (((m + 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt (hcs.trans ?_)
      exact mul_le_mul hF2 hB2 (integral_nonneg fun _ => sq_nonneg _) (by positivity)
    refine habs.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- the scale r = N^{-1/2}
  set N' : ℝ := ((m + 2 : ℕ) : ℝ) with hN'
  have hN'0 : 0 < N' := by rw [hN']; positivity
  set r : ℝ := N' ^ (-(1 / 2 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hN'0.le _
  have hrr : r ^ 2 = 1 / N' := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hN'0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hnN : n ≤ N' := by rw [hn, hN']; push_cast; linarith
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hLnn : 0 ≤ L := by linarith
  have hk : Real.sqrt (Cv * n * sqRow) * (C7 * r) ≤ C7 * (Real.sqrt (Cv * Cj) * Real.sqrt L) := by
    have h1 : Real.sqrt (Cv * n * sqRow) * r = Real.sqrt (Cv * n * sqRow * r ^ 2) := by
      rw [Real.sqrt_mul (show 0 ≤ Cv * n * sqRow by positivity) (r ^ 2), Real.sqrt_sq hr0]
    have h2 : Cv * n * sqRow * r ^ 2 ≤ Cv * Cj * L := by
      rw [hrr]
      have : n * (1 / N') ≤ 1 := by rw [mul_one_div, div_le_one hN'0]; exact hnN
      calc Cv * n * sqRow * (1 / N') = (Cv * sqRow) * (n * (1 / N')) := by ring
        _ ≤ (Cv * sqRow) * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = Cv * sqRow := mul_one _
        _ ≤ Cv * (Cj * L) := mul_le_mul_of_nonneg_left hsq hCv0.le
        _ = Cv * Cj * L := by ring
    calc Real.sqrt (Cv * n * sqRow) * (C7 * r) = C7 * (Real.sqrt (Cv * n * sqRow) * r) := by ring
      _ ≤ C7 * Real.sqrt (Cv * Cj * L) := by
          rw [h1]; exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) hC70
      _ = _ := by rw [Real.sqrt_mul (by positivity)]
  have hcov' : ∀ i : Fin (m + 1), |∫ Y, (∑ j, f j Y - ∑ j, ∫ Y', f j Y' ∂P) *
      ((P[f i | othersSigma i]) Y - poleF D (m + 2) x t / poleB D (m + 2) x t) ∂P| ≤
      C7 * (Real.sqrt (Cv * Cj) * Real.sqrt L) := fun i => (hcov i).trans hk
  have hvc := s81c_var_compare (P := P) (fun i => othersSigma (d := d) i) hm f hmemP hfm (q := sqRow)
    (dq := C5 * Real.sqrt δ * (Cj * L)) (τ := C7) (κ := C7 * (Real.sqrt (Cv * Cj) * Real.sqrt L))
    (fun _ => poleF D (m + 2) x t / poleB D (m + 2) x t) hdiag hT hcov'
  rw [← hP]
  refine ⟨hS, hvc.trans ?_⟩
  have hsL := Real.sqrt_nonneg L
  have hsδ := Real.sqrt_nonneg δ
  have hcv := Real.sqrt_nonneg (Cv * Cj)
  have hC1 : 0 ≤ C5 * Cj := by positivity
  have hC2 : 0 ≤ C7 * Real.sqrt (Cv * Cj) := by positivity
  have hfin : C5 * Real.sqrt δ * (Cj * L) + C7 + C7 * (Real.sqrt (Cv * Cj) * Real.sqrt L) ≤
      (C5 * Cj + C7 + C7 * Real.sqrt (Cv * Cj)) * (1 + Real.sqrt L + Real.sqrt δ * L) := by
    have p1 : 0 ≤ Real.sqrt δ * L := mul_nonneg hsδ hLnn
    nlinarith [mul_nonneg hC1 p1, mul_nonneg hC1 hsL, mul_nonneg hC2 p1, mul_nonneg hC2 hsL,
      mul_nonneg hC70 p1, mul_nonneg hC70 hsL, mul_nonneg hC1 hC70, hC1, hC2, hC70]
  calc n * (C5 * Real.sqrt δ * (Cj * L) + C7 + C7 * (Real.sqrt (Cv * Cj) * Real.sqrt L))
      ≤ n * ((C5 * Cj + C7 + C7 * Real.sqrt (Cv * Cj)) * (1 + Real.sqrt L + Real.sqrt δ * L)) :=
        mul_le_mul_of_nonneg_left hfin hn0
    _ = _ := by
        have hcast : ((m + 2 - 1 : ℕ) : ℝ) = n := rfl
        rw [hcast]; ring

end HRS.Whole.S81b
