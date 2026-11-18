import HRS.MS.CritWholeCavityL2

/-!
# S8.1 XS, CR10: sup-norm control of the full marginal density `θ_N`

From the exact cavity equation `wr13d_log_theta`, `log θ = β E + (β/N) A + D_N - log Z` with `E = g*(μ - ν_n)`,
`A = g*ν_n ≥ 0`, `D_N ≥ 0`; the critical convolution estimate `|g*(hμ)| ≤ √(C log H) ‖h‖₂ + ‖h‖_∞ C/H` (TT01 rows) gives
`|E| ≲ √δ_N`; normalisation `∫ θ dμ = 1` pins `log Z`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.Wr

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

/-- Cauchy-Schwarz in the form `(∫ a b)² ≤ (∫ a²)(∫ b²)` for bounded measurable `a, b` on a probability space. -/
theorem s81b_cs {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a b : Euc d → ℝ} (ha : Measurable a)
    (hb : Measurable b) {Ba Bb : ℝ} (hab : ∀ y, |a y| ≤ Ba) (hbb : ∀ y, |b y| ≤ Bb) :
    (∫ y, a y * b y ∂μ) ^ 2 ≤ (∫ y, a y ^ 2 ∂μ) * ∫ y, b y ^ 2 ∂μ := by
  have hI : ∀ (u v : Euc d → ℝ), Measurable u → Measurable v → ∀ {Bu Bv : ℝ}, (∀ y, |u y| ≤ Bu) →
      (∀ y, |v y| ≤ Bv) → Integrable (fun y => u y * v y) μ := by
    intro u v hu hv Bu Bv hub hvb
    refine Integrable.of_bound (C := Bu * Bv) (hu.mul hv).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hub y) (hvb y) (abs_nonneg _) ((abs_nonneg _).trans (hub y))
  have h2 : ∀ (u : Euc d → ℝ), Measurable u → ∀ {Bu : ℝ}, (∀ y, |u y| ≤ Bu) →
      Integrable (fun y => u y ^ 2) μ := fun u hu Bu hub => by
    simpa [sq] using hI u u hu hu hub hub
  have key : ∀ t : ℝ, 0 ≤ (∫ y, a y ^ 2 ∂μ) * (t * t) + (-2 * ∫ y, a y * b y ∂μ) * t + ∫ y, b y ^ 2 ∂μ := by
    intro t
    have ha2 := h2 a ha hab
    have hb2 := h2 b hb hbb
    have hab' := hI a b ha hb hab hbb
    have h_a2 : Integrable (fun y => t * t * a y ^ 2) μ := ha2.const_mul _
    have h_ab : Integrable (fun y => 2 * t * (a y * b y)) μ := hab'.const_mul _
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

theorem s81b_conv_L2_bound (hd : 2 ≤ d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) → ∀ H : ℝ, 2 ≤ H → ∀ x : Euc d,
      ∀ h : Euc d → ℝ, Measurable h → ∀ Bh : ℝ, (∀ y, |h y| ≤ Bh) →
        |∫ y, critG d (x - y) * h y ∂(withDensityReal ρ)| ≤
          Real.sqrt (C * Real.log H) * l2Norm (withDensityReal ρ) h + Bh * (C / H) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hC0, hC⟩ := s81b_critical_truncation_rows hd M
  refine ⟨C, hC0, fun ρ hρ hM H hH x h hhm Bh hBh => ?_⟩
  have hprob := Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hTailI, hSqI, hTail, hSq⟩ := hC ρ hρ hM H hH x
  have hH0 : 0 < H := by linarith
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hBh 0)
  have hkern : ∀ z : Euc d, 0 ≤ critG d z := fun z => s81b_critG_nonneg hd1 z
  have hT0 : ∀ z : Euc d, 0 ≤ truncKernel d ((d : ℝ) / 2) H z := fun z => le_min (hkern z) hH0.le
  have hTm : Measurable fun y : Euc d => truncKernel d ((d : ℝ) / 2) H (x - y) :=
    (s81b_trunc_meas hd1 H).comp (measurable_const.sub measurable_id)
  have hTb : ∀ y, |truncKernel d ((d : ℝ) / 2) H (x - y)| ≤ H := fun y => by
    rw [abs_of_nonneg (hT0 _)]; exact min_le_right _ _
  have hTi : Integrable (fun y => truncKernel d ((d : ℝ) / 2) H (x - y) * h y) (withDensityReal ρ) :=
    Integrable.of_bound (C := H * Bh) (hTm.mul hhm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hTb y) (hBh y) (abs_nonneg _) hH0.le)
  have hGi : Integrable (fun y => tailG d H (x - y) * h y) (withDensityReal ρ) :=
    Integrable.mono' (hTailI.const_mul Bh)
      ((((s81b_tailG_meas hd1 H).comp (measurable_const.sub measurable_id)).mul hhm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s81b_tailG_nonneg hd1 H hH0.le _)]
        calc _ ≤ tailG d H (x - y) * Bh := mul_le_mul_of_nonneg_left (hBh y) (s81b_tailG_nonneg hd1 H hH0.le _)
          _ = Bh * tailG d H (x - y) := mul_comm _ _)
  have hsplit : ∀ y, critG d (x - y) * h y =
      truncKernel d ((d : ℝ) / 2) H (x - y) * h y + tailG d H (x - y) * h y := fun y => by
    simp only [tailG]; ring
  simp_rw [hsplit]
  rw [integral_add hTi hGi]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have hcs := s81b_cs (μ := withDensityReal ρ) hTm hhm hTb hBh
    have hSq' : ∫ y, truncKernel d ((d : ℝ) / 2) H (x - y) ^ 2 ∂(withDensityReal ρ) ≤ C * Real.log H := hSq
    have hl : l2Norm (withDensityReal ρ) h ^ 2 = ∫ y, h y ^ 2 ∂(withDensityReal ρ) := by
      unfold l2Norm; rw [Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((∫ y, truncKernel d ((d : ℝ) / 2) H (x - y) * h y ∂(withDensityReal ρ)) ^ 2)
        ≤ Real.sqrt ((C * Real.log H) * l2Norm (withDensityReal ρ) h ^ 2) := by
          refine Real.sqrt_le_sqrt (hcs.trans ?_)
          rw [hl]
          exact mul_le_mul_of_nonneg_right hSq' (integral_nonneg fun y => sq_nonneg _)
      _ = _ := by
          have hl0 : 0 ≤ l2Norm (withDensityReal ρ) h := Real.sqrt_nonneg _
          rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hl0]
  · have : |∫ y, tailG d H (x - y) * h y ∂(withDensityReal ρ)| ≤
        ∫ y, Bh * tailG d H (x - y) ∂(withDensityReal ρ) := by
      refine (abs_integral_le_integral_abs).trans (integral_mono hGi.abs (hTailI.const_mul Bh) fun y => ?_)
      rw [abs_mul, abs_of_nonneg (s81b_tailG_nonneg hd1 H hH0.le _)]
      calc _ ≤ tailG d H (x - y) * Bh := mul_le_mul_of_nonneg_left (hBh y) (s81b_tailG_nonneg hd1 H hH0.le _)
        _ = _ := mul_comm _ _
    refine this.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hTail hBh0

theorem s81b_delta_facts (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    (1 : ℝ) / N ≤ deltaN d ((d : ℝ) / 2) N ∧ deltaN d ((d : ℝ) / 2) N * Real.log N ≤ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hδ : deltaN d ((d : ℝ) / 2) N = (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N) := by
    simp only [deltaN, lt_self_iff_false, if_false, if_true]
  have hl : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]
  rw [hδ, hl]
  refine ⟨?_, ?_⟩
  · rw [one_div, ← mul_one (N : ℝ)⁻¹]
    nlinarith [inv_pos.2 hN0]
  · have hexp : Real.exp (Real.log N) = N := Real.exp_log hN0
    have h3 : 1 + Real.log N + (Real.log N) ^ 2 / 2 ≤ N := by
      have := Real.quadratic_le_exp_of_nonneg hL
      rwa [hexp] at this
    have : (1 + Real.log N) * Real.log N ≤ 4 * N := by nlinarith
    calc (N : ℝ)⁻¹ * (1 + Real.log N) * Real.log N = (N : ℝ)⁻¹ * ((1 + Real.log N) * Real.log N) := by ring
      _ ≤ (N : ℝ)⁻¹ * (4 * N) := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hN0.le)
      _ = 4 := by field_simp

theorem s81b_abs_exp_sub_one (v : ℝ) : |Real.exp v - 1| ≤ |v| * Real.exp |v| := by
  rcases le_or_gt 0 v with hv | hv
  · rw [abs_of_nonneg hv, abs_of_nonneg (by linarith [Real.add_one_le_exp v])]
    have h1 := Real.add_one_le_exp (-v)
    have h2 : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos v, Real.exp_pos (-v)]
  · rw [abs_of_neg hv, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hv.le] : Real.exp v - 1 ≤ 0)]
    have h1 := Real.add_one_le_exp v
    have h2 : 1 ≤ Real.exp (-v) := Real.one_le_exp (by linarith)
    nlinarith

set_option maxHeartbeats 800000 in
theorem s81b_full_density_sup (hd : 2 ≤ d) (M βm βp : ℝ) (hβm : 0 < βm) (hβ : βm ≤ βp) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ D : Data d M βm βp, ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      C⁻¹ ≤ theta D N x ∧ |theta D N x - 1| ≤ C * Real.sqrt (deltaN d ((d : ℝ) / 2) N) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < ((d : ℝ) / 2) := by linarith
  have hsd : ((d : ℝ) / 2) < d := by linarith
  have hβp : 0 < βp := hβm.trans_le hβ
  obtain ⟨C1, hC10, hC1⟩ := s81b_conv_L2_bound hd M
  obtain ⟨Cq, hCq1, hCq⟩ := s81b_cavity_relative_L2 hd M βm βp hβm hβ
  obtain ⟨Cd, hCd0, hCd⟩ := wr13c2_insDefect_le hd hs0 hsd hβm βp M
  set Mg : ℝ := max (potentialBound d ((d : ℝ) / 2) M) 0 with hMgdef
  have hMg : 0 ≤ Mg := le_max_right _ _
  set K : ℝ := βp * (2 * Cq * Real.sqrt C1 + (Cq + 1) * C1) + βp * Cq * Mg + Cd with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨1 + Real.exp (2 * K) + 2 * K * Real.exp (2 * K), by
    have := Real.exp_pos (2 * K); nlinarith [mul_nonneg hK0 this.le], fun D N hN x => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hβ0 : 0 < D.beta := hβm.trans_le D.beta_mem.1
  have hββp : D.beta ≤ βp := D.beta_mem.2
  have hprob : IsProbabilityMeasure (mu D) := Q34.isProbabilityMeasure_nu D.prob
  have hconv := wr13a_conv_le_density hd1 hs0 hsd D.prob D.bound
  have hN0 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hNn : ((m + 1 : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) - 1 := by push_cast; ring
  set δ : ℝ := deltaN d ((d : ℝ) / 2) (m + 2) with hδdef
  obtain ⟨hδ1, hδL⟩ := s81b_delta_facts hd1 hN
  obtain ⟨hδpos, hδle⟩ := wr13c_deltaN_pos_le_one hd1 hs0 hsd (by omega : 1 ≤ m + 2)
  set sδ : ℝ := Real.sqrt δ with hsδ
  have hsδ0 : 0 ≤ sδ := Real.sqrt_nonneg _
  have hsδ2 : sδ ^ 2 = δ := Real.sq_sqrt hδpos.le
  have hsδ1 : sδ ≤ 1 := by rw [hsδ]; exact Real.sqrt_le_one.2 hδle
  have hδs : δ ≤ sδ := by nlinarith
  obtain ⟨q, hqm, hνq, hq0, -, hql, -, -, -⟩ := hCq D (m + 2) hN
  set Z : ℝ := wr13d_Z d ((d : ℝ) / 2) (m + 1) D.beta (mu D) with hZdef
  have hcq1 : ∀ y, 0 ≤ q y ∧ q y ≤ Cq := hq0
  have key : ∀ y : Euc d, |Real.log (theta D (m + 2) y) + Real.log Z| ≤ K * sδ := by
    intro y
    -- the exact cavity equation
    have hlog : Real.log (theta D (m + 2) y) = D.beta * convMeasure (critG d) (mu D) y +
        (insertionDefect d ((d : ℝ) / 2) (m + 2) D.beta (mu D) y +
          -(D.beta / ((m + 2 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) *
            ∫ z, critG d (y - z) ∂(firstMarginal (cavity D (m + 2)))) - Real.log Z :=
      wr13d_log_theta hd hs0 hsd D.prob D.bound hβ0.le (n := m + 1) (by omega) y
    have hg0 : ∀ z, 0 ≤ critG d (y - z) := fun z => s81b_critG_nonneg hd1 _
    have hgi : Integrable (fun z => critG d (y - z)) (mu D) :=
      (wr13a_potential_bound hd1 hs0 hsd D.prob D.bound y).1
    have hgm : Measurable fun z => critG d (y - z) :=
      (s81b_critG_meas hd1).comp (measurable_const.sub measurable_id)
    set conv : ℝ := convMeasure (critG d) (mu D) y with hconvdef
    have hconv_le : conv ≤ Mg := (hconv y).trans (le_max_left _ _)
    have hconv0 : 0 ≤ conv := integral_nonneg hg0
    set A : ℝ := ∫ z, critG d (y - z) ∂(firstMarginal (cavity D (m + 2))) with hAdef
    have hA : A = ∫ z, q z * critG d (y - z) ∂(mu D) := by
      rw [hAdef, hνq]; exact s81b_integral_withDensity hqm (fun z => (hq0 z).1) _
    have hqgi : Integrable (fun z => q z * critG d (y - z)) (mu D) :=
      Integrable.mono' (hgi.const_mul Cq) (hqm.mul hgm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 z).1 (hg0 z))]
          exact mul_le_mul_of_nonneg_right (hq0 z).2 (hg0 z))
    have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun z => mul_nonneg (hq0 z).1 (hg0 z)
    have hAle : A ≤ Cq * Mg := by
      rw [hA]
      calc _ ≤ ∫ z, Cq * critG d (y - z) ∂(mu D) :=
            integral_mono hqgi (hgi.const_mul Cq) fun z => mul_le_mul_of_nonneg_right (hq0 z).2 (hg0 z)
        _ = Cq * conv := integral_const_mul _ _
        _ ≤ Cq * Mg := mul_le_mul_of_nonneg_left hconv_le (by linarith [(hq0 0).1, (hq0 0).2])
    -- E = conv - A
    have hE : conv - A = ∫ z, critG d (y - z) * (1 - q z) ∂(mu D) := by
      rw [hA, hconvdef]
      unfold convMeasure
      rw [← integral_sub hgi hqgi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only; ring
    have hq1 : ∀ z, |1 - q z| ≤ Cq + 1 := fun z => by
      rw [abs_le]; constructor <;> linarith [(hq0 z).1, (hq0 z).2]
    have hEb := hC1 D.rho D.prob D.bound (m + 2 : ℕ) (by exact_mod_cast hN) y (fun z => 1 - q z)
      (measurable_const.sub hqm) (Cq + 1) hq1
    have hl2 : l2Norm (mu D) (fun z => 1 - q z) ≤ Cq * δ := by
      rw [s81b_l2_symm]; exact hql
    have hlogN : 0 ≤ Real.log ((m + 2 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m + 2))
    have hEb' : |conv - A| ≤ 2 * Cq * Real.sqrt C1 * sδ + (Cq + 1) * C1 * sδ := by
      rw [hE]
      refine hEb.trans (add_le_add ?_ ?_)
      · -- the logarithmic term
        have h1 : Real.sqrt (C1 * Real.log ((m + 2 : ℕ) : ℝ)) * (Cq * δ) ≤ 2 * Cq * Real.sqrt C1 * sδ := by
          have e : Real.sqrt (C1 * Real.log ((m + 2 : ℕ) : ℝ)) * δ ≤ 2 * Real.sqrt C1 * sδ := by
            have h4 : Real.sqrt (δ * Real.log ((m + 2 : ℕ) : ℝ)) ≤ 2 := by
              calc _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hδL
                _ = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            have hsq : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδpos.le
            calc Real.sqrt (C1 * Real.log ((m + 2 : ℕ) : ℝ)) * δ
                = Real.sqrt C1 * (Real.sqrt (δ * Real.log ((m + 2 : ℕ) : ℝ)) * sδ) := by
                  rw [Real.sqrt_mul hC10, Real.sqrt_mul hδpos.le]
                  calc _ = Real.sqrt C1 * Real.sqrt (Real.log ((m + 2 : ℕ) : ℝ)) * (Real.sqrt δ * Real.sqrt δ) := by
                        rw [hsq]
                    _ = _ := by rw [hsδ]; ring
              _ ≤ Real.sqrt C1 * (2 * sδ) := by gcongr
              _ = _ := by ring
          calc _ = Cq * (Real.sqrt (C1 * Real.log ((m + 2 : ℕ) : ℝ)) * δ) := by ring
            _ ≤ Cq * (2 * Real.sqrt C1 * sδ) := mul_le_mul_of_nonneg_left e (by linarith [(hq0 0).1, (hq0 0).2])
            _ = _ := by ring
        calc _ ≤ Real.sqrt (C1 * Real.log ((m + 2 : ℕ) : ℝ)) * (Cq * δ) :=
              mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg _)
          _ ≤ _ := h1
      · have : C1 / ((m + 2 : ℕ) : ℝ) ≤ C1 * δ := by
          rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hδ1 hC10
        calc (Cq + 1) * (C1 / ((m + 2 : ℕ) : ℝ)) ≤ (Cq + 1) * (C1 * sδ) :=
              mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left hδs hC10))
                (by linarith [(hq0 0).1, (hq0 0).2])
          _ = _ := by ring
    obtain ⟨-, hD0, hDle, -⟩ := hCd D.rho D.prob D.bound D.beta D.beta_mem.1 hββp (m + 2) hN y
    have hT : Real.log (theta D (m + 2) y) + Real.log Z = D.beta * (conv - A) +
        (D.beta / ((m + 2 : ℕ) : ℝ)) * A + insertionDefect d ((d : ℝ) / 2) (m + 2) D.beta (mu D) y := by
      rw [hlog, hNn]
      field_simp
      ring
    have hEnn : 0 ≤ 2 * Cq * Real.sqrt C1 * sδ + (Cq + 1) * C1 * sδ := by
      have := hq0 0; have := (hq0 0).1; positivity
    have hCq0 : 0 ≤ Cq := le_trans (hq0 0).1 (hq0 0).2
    rw [abs_le] at hEb' ⊢
    have h1 : D.beta * (conv - A) ≤ βp * (2 * Cq * Real.sqrt C1 * sδ + (Cq + 1) * C1 * sδ) :=
      (mul_le_mul_of_nonneg_left hEb'.2 hβ0.le).trans (mul_le_mul_of_nonneg_right hββp hEnn)
    have h2 : -(βp * (2 * Cq * Real.sqrt C1 * sδ + (Cq + 1) * C1 * sδ)) ≤ D.beta * (conv - A) := by
      have := mul_le_mul_of_nonneg_left hEb'.1 hβ0.le
      have h3 := mul_le_mul_of_nonneg_right hββp hEnn
      nlinarith
    have h4 : (D.beta / ((m + 2 : ℕ) : ℝ)) * A ≤ βp * Cq * Mg * sδ := by
      have e1 : D.beta / ((m + 2 : ℕ) : ℝ) ≤ βp * δ := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul hββp hδ1 (by positivity) hβp.le
      calc (D.beta / ((m + 2 : ℕ) : ℝ)) * A ≤ (βp * δ) * (Cq * Mg) :=
            mul_le_mul e1 hAle hA0 (by positivity)
        _ ≤ (βp * sδ) * (Cq * Mg) := by gcongr
        _ = _ := by ring
    have h5 : 0 ≤ (D.beta / ((m + 2 : ℕ) : ℝ)) * A := by positivity
    have h6 : insertionDefect d ((d : ℝ) / 2) (m + 2) D.beta (mu D) y ≤ Cd * sδ :=
      hDle.trans (mul_le_mul_of_nonneg_left hδs hCd0)
    rw [hT]
    constructor <;> nlinarith [mul_nonneg hβp.le hMg, mul_nonneg hCq0 hMg, mul_nonneg hCd0 hsδ0,
      mul_nonneg (mul_nonneg hβp.le hCq0) hMg]
  -- normalisation
  have hθm : Measurable (theta D (m + 2)) := wr13d_theta_meas hd hs0 hsd D.prob D.bound hβ0.le (m + 1)
  have hθpos : ∀ y, 0 < theta D (m + 2) y := fun y =>
    wr13d_theta_pos hd hs0 hsd D.prob D.bound hβ0.le (by omega : 1 ≤ m + 1) y
  have hθint : Integrable (theta D (m + 2)) (mu D) :=
    Integrable.of_bound (C := Real.exp (2 * D.beta * potentialBound d ((d : ℝ) / 2) M)) hθm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (hθpos y)]
        exact wr13d_theta_le hd hs0 hsd D.prob D.bound hβ0.le (m + 1) y)
  have hint1 : ∫ y, theta D (m + 2) y ∂(mu D) = 1 :=
    wr13d_theta_integral hd hs0 hsd D.prob D.bound hβ0.le (by omega : 1 ≤ m + 1)
  have hbd : ∀ y, Real.exp (-(K * sδ) - Real.log Z) ≤ theta D (m + 2) y ∧
      theta D (m + 2) y ≤ Real.exp (K * sδ - Real.log Z) := fun y => by
    have h := abs_le.1 (key y)
    have e : theta D (m + 2) y = Real.exp (Real.log (theta D (m + 2) y)) := (Real.exp_log (hθpos y)).symm
    rw [e]
    exact ⟨Real.exp_le_exp.2 (by linarith [h.1]), Real.exp_le_exp.2 (by linarith [h.2])⟩
  have hlo : Real.exp (-(K * sδ) - Real.log Z) ≤ 1 := by
    rw [← hint1]
    calc _ = ∫ y, Real.exp (-(K * sδ) - Real.log Z) ∂(mu D) := by simp
      _ ≤ _ := integral_mono (integrable_const _) hθint fun y => (hbd y).1
  have hhi : 1 ≤ Real.exp (K * sδ - Real.log Z) := by
    rw [← hint1]
    calc _ ≤ ∫ y, Real.exp (K * sδ - Real.log Z) ∂(mu D) :=
          integral_mono hθint (integrable_const _) fun y => (hbd y).2
      _ = _ := by simp
  have hZ1 := Real.exp_le_one_iff.1 hlo
  have hZ2 := Real.one_le_exp_iff.1 hhi
  have hε : K * sδ ≤ K := by nlinarith
  have hv : |Real.log (theta D (m + 2) x)| ≤ 2 * (K * sδ) := by
    have h := abs_le.1 (key x)
    rw [abs_le]; constructor <;> linarith
  refine ⟨?_, ?_⟩
  · have e : theta D (m + 2) x = Real.exp (Real.log (theta D (m + 2) x)) := (Real.exp_log (hθpos x)).symm
    rw [e]
    have : (1 + Real.exp (2 * K) + 2 * K * Real.exp (2 * K))⁻¹ ≤ (Real.exp (2 * K))⁻¹ :=
      inv_anti₀ (Real.exp_pos _) (by nlinarith [mul_nonneg hK0 (Real.exp_pos (2 * K)).le])
    refine this.trans ?_
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 hv).1])
  · have e : theta D (m + 2) x = Real.exp (Real.log (theta D (m + 2) x)) := (Real.exp_log (hθpos x)).symm
    rw [e]
    refine (s81b_abs_exp_sub_one _).trans ?_
    have h1 : Real.exp |Real.log (theta D (m + 2) x)| ≤ Real.exp (2 * K) :=
      Real.exp_le_exp.2 (hv.trans (by linarith))
    calc |Real.log (theta D (m + 2) x)| * Real.exp |Real.log (theta D (m + 2) x)|
        ≤ (2 * (K * sδ)) * Real.exp (2 * K) :=
          mul_le_mul hv h1 (Real.exp_pos _).le (by positivity)
      _ = (2 * K * Real.exp (2 * K)) * sδ := by ring
      _ ≤ (1 + Real.exp (2 * K) + 2 * K * Real.exp (2 * K)) * sδ := by
          refine mul_le_mul_of_nonneg_right ?_ hsδ0
          nlinarith [Real.exp_pos (2 * K)]

end HRS.Whole.S81b
