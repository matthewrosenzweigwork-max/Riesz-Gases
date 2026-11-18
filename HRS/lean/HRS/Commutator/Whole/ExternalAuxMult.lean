import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.LocalAuxFC
import HRS.Commutator.Whole.RieszAux

/-!
# X-MULT auxiliary: dyadic (Littlewood-Paley) kernels of smooth symbols

Helper lemmas for `mult_kernel_bounds`, `mult_kernel_bessel` and for `kernel_remainder`
(all names prefixed `cmxMY_`).

Route (replacing the Mikhlin theorem): a symbol `q` vanishing on `B(0,1)` is split with the dyadic
partition `∑_{j ≥ 0} ρ(2^{-j} ξ) = 1` on `|ξ| ≥ 1`, `ρ = χ - χ(2 ·)`; the `j`-th piece is
`2^{-jγ} θ_j(2^{-j} ξ)` with `θ_j` smooth supported in `|η| ≤ 2` and bounded in `C^n` uniformly in `j`;
its kernel is `2^{j(d-γ)} Θ_j(2^j x)`, `Θ_j = 𝓕⁻θ_j`, rapidly decaying uniformly in `j`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- Scaling of the Fourier transform. -/
lemma cmxMY_fourier_comp_smul (f : Euc d → ℂ) {c : ℝ} (hc : 0 < c) (ξ : Euc d) :
    𝓕 (fun x => f (c • x)) ξ = ((c ^ d)⁻¹ : ℝ) • 𝓕 f (c⁻¹ • ξ) := by
  simp only [Real.fourier_eq]
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Euc d)))
    (fun y : Euc d => (𝐞 (-inner ℝ y (c⁻¹ • ξ)) : Circle) • f y) c
  have e : ∀ x : Euc d, (fun y : Euc d => (𝐞 (-inner ℝ y (c⁻¹ • ξ)) : Circle) • f y) (c • x)
      = (𝐞 (-inner ℝ x ξ) : Circle) • f (c • x) := by
    intro x
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    congr 3
    field_simp
  simp_rw [e] at h
  rw [h]
  simp [finrank_euclideanSpace, abs_of_pos, hc]

/-- Decay of the Fourier transform of a smooth function supported in `B̄(0,2)` with bounded
derivatives: `‖x‖^n ‖𝓕⁻θ(x)‖ ≤ (2n+2)^n ∑_{i ≤ n} B_i vol(B̄(0,2))`. -/
lemma cmxMY_decay (θ : Euc d → ℂ) (hθ : ContDiff ℝ ∞ θ) (hs : ∀ η : Euc d, 2 < ‖η‖ → θ η = 0)
    (n : ℕ) (B : ℕ → ℝ) (hB : ∀ i ≤ n, ∀ η, ‖iteratedFDeriv ℝ i θ η‖ ≤ B i) (x : Euc d) :
    ‖x‖ ^ n * ‖𝓕⁻ θ x‖ ≤ (2 * (n : ℝ) + 2) ^ n *
      ∑ i ∈ Finset.range (n + 1), B i * (volume (closedBall (0 : Euc d) 2)).toReal := by
  have hcs : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) 2) ?_
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  have hint : ∀ i : ℕ, Integrable (fun v : Euc d => ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖) := by
    intro i
    have h1 : Continuous (fun v : Euc d => ‖iteratedFDeriv ℝ i θ v‖) :=
      (hθ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
    have h2 : HasCompactSupport (fun v : Euc d => ‖iteratedFDeriv ℝ i θ v‖) :=
      (hcs.iteratedFDeriv i).norm
    simpa using h1.integrable_of_hasCompactSupport h2
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := ⊤) (f := θ) (k := 0)
    (n := n) hθ (fun k m hk _ => by
      have : k = 0 := by simpa using hk
      subst this
      exact hint m) le_rfl le_top (-x)
  have hts : tsupport θ ⊆ closedBall (0 : Euc d) 2 := by
    refine closure_minimal ?_ isClosed_closedBall
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  have hbd : ∀ i ≤ n, ∫ v : Euc d, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ ≤
      B i * (volume (closedBall (0 : Euc d) 2)).toReal := by
    intro i hi
    have hnn : ∀ v : Euc d, 0 ≤ ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ := fun v => by positivity
    have hpt : ∀ v : Euc d, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ ≤
        (closedBall (0 : Euc d) 2).indicator (fun _ => B i) v := by
      intro v
      by_cases hv : v ∈ closedBall (0 : Euc d) 2
      · rw [Set.indicator_of_mem hv]; simpa using hB i hi v
      · rw [Set.indicator_of_notMem hv]
        have : iteratedFDeriv ℝ i θ v = 0 := by
          by_contra h0
          exact hv (hts (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) i (subset_closure h0)))
        simp [this]
    have hind : Integrable ((closedBall (0 : Euc d) 2).indicator (fun _ => B i)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    calc _ ≤ ∫ v : Euc d, (closedBall (0 : Euc d) 2).indicator (fun _ => B i) v :=
          integral_mono (hint i) hind hpt
      _ = _ := by
          rw [integral_indicator_const _ measurableSet_closedBall]
          simp [Measure.real, mul_comm]
  rw [Real.fourierInv_eq_fourier_neg]
  simp only [norm_neg, norm_iteratedFDeriv_zero] at key ⊢
  refine key.trans ?_
  have hsum : ∑ p ∈ ({0} : Finset ℕ) ×ˢ Finset.range (n + 1),
      ∫ v : Euc d, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 θ v‖ =
      ∑ i ∈ Finset.range (n + 1), ∫ v : Euc d, ‖v‖ ^ 0 * ‖iteratedFDeriv ℝ i θ v‖ := by
    rw [Finset.singleton_product, Finset.sum_map]
    rfl
  have h2 : ((2:ℝ) * ((0:ℕ):ℝ) + 2) ^ n ≤ (2 * (n : ℝ) + 2) ^ n := by
    gcongr; simp
  simp only [pow_zero, one_mul, zero_add, Finset.range_one, hsum]
  refine le_trans (mul_le_mul_of_nonneg_right h2 (Finset.sum_nonneg fun i _ => ?_)) ?_
  · exact integral_nonneg fun v => by positivity
  gcongr with i hi
  simpa using hbd i (by simpa [Nat.lt_succ_iff] using hi)

/-! ### Dyadic sums -/

/-- dyadic term -/
def cmxMY_term (a : ℝ) (N : ℕ) (r : ℝ) (j : ℕ) : ℝ := ((2:ℝ)^j)^a / (1 + (2:ℝ)^j * r)^N

lemma cmxMY_term_nonneg (a : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) (j : ℕ) : 0 ≤ cmxMY_term a N r j := by
  unfold cmxMY_term; positivity

lemma cmxMY_two_pow_rpow_le {a b : ℝ} (hab : a ≤ b) (j : ℕ) :
    ((2:ℝ)^j)^a ≤ ((2:ℝ)^j)^b :=
  Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hab

lemma cmxMY_term_le_pow {a : ℝ} {N : ℕ} {r : ℝ} (hr : 0 < r) (j : ℕ) :
    cmxMY_term a N r j ≤ ((2:ℝ)^j)^(a - N) / r ^ N := by
  have h2j : (0:ℝ) < (2:ℝ)^j := by positivity
  have h1 : ((2:ℝ)^j * r)^N ≤ (1 + (2:ℝ)^j * r)^N := by
    gcongr; linarith
  have h2 : ((2:ℝ)^j)^a / (1 + (2:ℝ)^j * r)^N ≤ ((2:ℝ)^j)^a / ((2:ℝ)^j * r)^N := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  refine h2.trans (le_of_eq ?_)
  have h3 : ((2:ℝ)^j)^a / ((2:ℝ)^j)^(N:ℝ) = ((2:ℝ)^j)^(a - N) := by
    rw [Real.rpow_sub h2j]
  rw [mul_pow, ← div_div, ← Real.rpow_natCast ((2:ℝ)^j) N, h3]

/-- geometric bound of the dyadic terms -/
lemma cmxMY_term_geom {a : ℝ} {N : ℕ} (hN : a + 1 ≤ N) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    cmxMY_term a N r j ≤ (1 / 2 : ℝ) ^ j * (r ^ N)⁻¹ := by
  refine (cmxMY_term_le_pow hr j).trans ?_
  have h4 : ((2:ℝ)^j)^(a - N) ≤ ((2:ℝ)^j)^(-1:ℝ) :=
    cmxMY_two_pow_rpow_le (by linarith) j
  calc ((2:ℝ)^j)^(a - N) / r ^ N ≤ ((2:ℝ)^j)^(-1:ℝ) / r ^ N := by gcongr
    _ = (1 / 2 : ℝ) ^ j * (r ^ N)⁻¹ := by
      rw [Real.rpow_neg_one, div_eq_mul_inv, one_div, inv_pow]

lemma cmxMY_term_summable {a : ℝ} {N : ℕ} (hN : a + 1 ≤ N) {r : ℝ} (hr : 0 < r) :
    Summable (cmxMY_term a N r) :=
  Summable.of_nonneg_of_le (cmxMY_term_nonneg a N hr.le) (cmxMY_term_geom hN hr)
    ((summable_geometric_two).mul_right _)

/-- near-field bound of the dyadic sum -/
lemma cmxMY_term_tsum_near {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : a + 1 ≤ N) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) :
    ∑' j, cmxMY_term a N r j ≤ ((2:ℝ) ^ a * (1 / ((2:ℝ) ^ a - 1) + 2)) * r ^ (-a) := by
  have hsum := cmxMY_term_summable hN hr
  have hex : ∃ j : ℕ, 1 ≤ (2:ℝ)^j * r := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / r) (by norm_num : (1:ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hr] at hn
    linarith
  classical
  set j₀ := Nat.find hex with hj₀
  have h1 : 1 ≤ (2:ℝ)^j₀ * r := Nat.find_spec hex
  have hP : ((2:ℝ)^j₀)^a ≤ 2 ^ a * r ^ (-a) := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · rw [h0]
      simp only [pow_zero, Real.one_rpow]
      have : 1 ≤ r ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
      have : (1:ℝ) ≤ 2 ^ a := Real.one_le_rpow (by norm_num) ha.le
      nlinarith
    · obtain ⟨k, hk⟩ : ∃ k, j₀ = k + 1 := ⟨j₀ - 1, by omega⟩
      have hmin : ¬ (1 ≤ (2:ℝ)^k * r) := Nat.find_min hex (by omega)
      have h2 : (2:ℝ)^j₀ ≤ 2 / r := by
        rw [le_div_iff₀ hr, hk, pow_succ]
        rw [not_le] at hmin
        nlinarith
      calc ((2:ℝ)^j₀)^a ≤ (2 / r)^a := Real.rpow_le_rpow (by positivity) h2 ha.le
        _ = 2 ^ a * r ^ (-a) := by
          rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  rw [← hsum.sum_add_tsum_nat_add j₀]
  have hfin : ∑ i ∈ Finset.range j₀, cmxMY_term a N r i ≤ ((2:ℝ)^j₀)^a / (2 ^ a - 1) := by
    have hx : (1:ℝ) < 2 ^ a := Real.one_lt_rpow (by norm_num) ha
    calc ∑ i ∈ Finset.range j₀, cmxMY_term a N r i ≤ ∑ i ∈ Finset.range j₀, ((2:ℝ)^a)^i := by
          apply Finset.sum_le_sum
          intro i _
          unfold cmxMY_term
          have hi0 : 0 ≤ (2:ℝ)^i * r := by positivity
          have hle : 1 ≤ (1 + (2:ℝ)^i * r)^N := one_le_pow₀ (by linarith)
          calc ((2:ℝ)^i)^a / (1 + (2:ℝ)^i * r)^N ≤ ((2:ℝ)^i)^a / 1 := by
                apply div_le_div_of_nonneg_left (by positivity) one_pos hle
            _ = ((2:ℝ)^a)^i := by
                rw [div_one, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
                  ← Real.rpow_mul (by norm_num), mul_comm]
      _ = (((2:ℝ)^a)^j₀ - 1) / (2 ^ a - 1) := geom_sum_eq hx.ne' j₀
      _ ≤ ((2:ℝ)^j₀)^a / (2 ^ a - 1) := by
          have : ((2:ℝ)^a)^j₀ = ((2:ℝ)^j₀)^a := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), mul_comm]
          rw [this]
          gcongr
          linarith
  have htail : ∑' i, cmxMY_term a N r (i + j₀) ≤ 2 * ((2:ℝ)^j₀)^a := by
    have hle : ∀ i, cmxMY_term a N r (i + j₀) ≤ (1 / 2 : ℝ) ^ i * ((2:ℝ)^j₀)^a := by
      intro i
      refine (cmxMY_term_le_pow hr (i + j₀)).trans ?_
      have e1 : ((2:ℝ)^(i + j₀))^(a - N) = ((2:ℝ)^i)^(a - N) * ((2:ℝ)^j₀)^(a - N) := by
        rw [pow_add, Real.mul_rpow (by positivity) (by positivity)]
      have e2 : ((2:ℝ)^i)^(a - N) ≤ (1 / 2 : ℝ) ^ i := by
        refine (cmxMY_two_pow_rpow_le (b := -1) (by linarith) i).trans ?_
        rw [Real.rpow_neg_one, one_div, inv_pow]
      have e3 : ((2:ℝ)^j₀)^(a - N) / r ^ N ≤ ((2:ℝ)^j₀)^a := by
        have h2j : (0:ℝ) < (2:ℝ)^j₀ := by positivity
        rw [Real.rpow_sub h2j, Real.rpow_natCast, div_div, div_le_iff₀ (by positivity)]
        have : (1:ℝ) ≤ ((2:ℝ)^j₀ * r)^N := one_le_pow₀ h1
        rw [mul_pow] at this
        have hp : 0 ≤ ((2:ℝ)^j₀)^a := by positivity
        nlinarith
      calc ((2:ℝ)^(i + j₀))^(a - N) / r ^ N
          = ((2:ℝ)^i)^(a - N) * (((2:ℝ)^j₀)^(a - N) / r ^ N) := by rw [e1]; ring
        _ ≤ (1 / 2 : ℝ) ^ i * ((2:ℝ)^j₀)^a := by
            apply mul_le_mul e2 e3 (by positivity) (by positivity)
    have hs : Summable fun i => cmxMY_term a N r (i + j₀) := (summable_nat_add_iff j₀).2 hsum
    calc ∑' i, cmxMY_term a N r (i + j₀) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ i * ((2:ℝ)^j₀)^a :=
          hs.tsum_le_tsum hle ((summable_geometric_two).mul_right _)
      _ = 2 * ((2:ℝ)^j₀)^a := by rw [tsum_mul_right, tsum_geometric_two]
  have hx : (1:ℝ) < (2:ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  have hpos : 0 < (2:ℝ) ^ a - 1 := by linarith
  calc _ ≤ ((2:ℝ)^j₀)^a / (2 ^ a - 1) + 2 * ((2:ℝ)^j₀)^a := add_le_add hfin htail
    _ = ((2:ℝ)^j₀)^a * (1 / (2 ^ a - 1) + 2) := by ring
    _ ≤ (2 ^ a * r ^ (-a)) * (1 / (2 ^ a - 1) + 2) := by
        gcongr
    _ = _ := by ring


end HRS.Commutator.Whole
