/-
# HRS.Equilibrium.Response — thermal and finite-particle response (EQ-01c)

Section 4.V of the main manuscript (source lines 5079-5234): Lemma 4.18
`M:V:lem:thermal-response-rates` and Lemma 4.19 `M:V:lem:finite-response-rates`.

Setting (source lines 1019-1033, 5079-5097): `d ≥ 2`, `d/2 ≤ s < d`, fixed `β > 0`, a fixed
frequency `k ≠ 0`, `φ(x) = cos(2πk·x)` (not `L²`-normalised), `V_θ = -θφ/β`, `θ ∈ ℝ`;
`μ_θ = ρ_θ dx` the thermal equilibrium measure of `V_θ` (unique for `β > 0`), `m_{N,θ}` the
first marginal of the canonical law `P_{N,θ} = P_{N,β}[V_θ]`,
`Y_{N,θ} = √N(μ_N(φ) - m_{N,θ}(φ))`, `G_θ ∼ N(0, C_{β,μ_θ}(φ,φ))`, and
`M_N(θ) = m_{N,θ}(φ)`, `M(θ) = μ_θ(φ)`, `C_N(θ) = E[Y_{N,θ}²]`, `C(θ) = E[G_θ²]`.
-/
import HRS.Equilibrium.PoleCavity

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-- The rate-family potential `V_θ = -θφ/β`, `φ = cos(2πk·x)` (`H:eq:rate-family`). -/
def rateV (k : Lattice d) (β θ : ℝ) (x : Torus d) : ℝ := -θ * Torus.cosMode k x / β

/-- The canonical law `P_{N,θ}` of the rate family. -/
def rateGibbs (d : ℕ) (s : ℝ) (k : Lattice d) (β θ : ℝ) (N : ℕ) : Measure (Config d N) :=
  canonicalGibbs (periodicRiesz d s) (rateV k β θ) N β

/-- `M_N(θ) = m_{N,θ}(φ)` (`V:eq:response-means`). -/
def rateMeanN (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  pair (firstMarginal (rateGibbs d s k β θ N)) (Torus.cosMode k)

/-- `Y_{N,θ} = √N(μ_N(φ) - m_{N,θ}(φ))` (`H:eq:rate-family-variables`). -/
def rateY (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) (X : Config d N) : ℝ :=
  Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, Torus.cosMode k (X i) - rateMeanN d s k β N θ)

/-- `C_N(θ) = E[Y_{N,θ}²]` (`V:eq:response-means`). -/
def rateVarN (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  ∫ X, rateY d s k β N θ X ^ 2 ∂(rateGibbs d s k β θ N)

/-- The supercritical bias `b_{β,μ}(φ)` of `H:eq:supercritical-bias` (source lines 976-980),
`b_{β,μ} = |𝕊^{d-1}| Γ(2-p)/(s p (p-1)) β^p (R_{β,μ} P_μ ρ) μ`, `p = d/s`, tested on `φ`. -/
def supercriticalBias (d : ℕ) (s β : ℝ) (ρ φ : Torus d → ℝ) : ℝ :=
  sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1)) * β ^ ((d : ℝ) / s) *
    ∫ x, responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x * φ x ∂(withDensityReal ρ)

section Rates

variable {s : ℝ}

/-- Lemma 4.18 `M:V:lem:thermal-response-rates` (source lines 5142-5155): for the family of
thermal densities `ρ_θ` of `V_θ`,
* `θ ↦ ρ_θ` is smooth into every Sobolev space, encoded as joint `C^∞` smoothness of
  `(θ, x) ↦ ρ_θ(x)` on `ℝ × ℝ^d` (equivalent on the torus);
* `V:eq:thermal-response-rates`: `∂_θ ρ_θ / ρ_θ = R_θ P_θ φ` (the response equation holds for
  it) and `M'(θ) = C(θ) = C_{β,μ_θ}(φ,φ)`;
* if `s > d/2`, `B(θ) = b_{β,μ_θ}(φ)` is smooth, `B(0) = 0` and
  `B'(0) = |𝕊^{d-1}| Γ(2-p) β^p / (2 s p (p-1) (1 + β ĝ(k))²) > 0`, `p = d/s`. -/
theorem thermal_response_rates (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Euc d => ρ p.1 (Torus.mk p.2)) ∧
    (∀ θ, IsResponse (periodicRiesz d s) (withDensityReal (ρ θ)) β (Torus.cosMode k)
      (fun x => deriv (fun θ' => ρ θ' x) θ / ρ θ x)) ∧
    (∀ θ, HasDerivAt (fun θ' => pair (withDensityReal (ρ θ')) (Torus.cosMode k))
      (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
        (Torus.cosMode k) (Torus.cosMode k)) θ) ∧
    ((d : ℝ) / 2 < s →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k)) ∧
        supercriticalBias d s β (ρ 0) (Torus.cosMode k) = 0 ∧
        HasDerivAt (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k))
          (sphereArea d * Real.Gamma (2 - d / s) * β ^ ((d : ℝ) / s) /
            (2 * s * (d / s) * (d / s - 1) * (1 + β * rieszCoeff d s k) ^ 2)) 0 ∧
        0 < sphereArea d * Real.Gamma (2 - d / s) * β ^ ((d : ℝ) / s) /
            (2 * s * (d / s) * (d / s - 1) * (1 + β * rieszCoeff d s k) ^ 2)) := by
  sorry

/-- every torus point has a representative in the half-open box. -/
theorem resp_exists_box (z : Torus d) : ∃ y ∈ KernelAux.Box d, KernelAux.boxPt y = z := by
  refine ⟨fun i => ((AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i) : Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : ℝ),
    fun i => ?_, ?_⟩
  · exact (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i)).2
  · funext i
    simp [KernelAux.boxPt]


theorem resp_mp_pair_sub {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun X : Fin N → Torus d => X i - X j) volume volume := by
  have h1 : MeasurePreserving (fun X : Fin N → Torus d => (X i, X j)) volume
      (volume.prod volume) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    exact pi_map_pair (volume : Measure (Torus d)) hij
  have h2 : MeasurePreserving (fun z : Torus d × Torus d => z.1 - z.2) (volume.prod volume)
      volume :=
    measurePreserving_fst.comp (measurePreserving_sub_prod volume volume)
  exact h2.comp h1

theorem resp_mp_perm {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    MeasurePreserving (fun X : Fin N → Torus d => fun k => X (τ k)) volume volume := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin N => (volume : Measure (Torus d))) τ.symm
  have e : (fun X : Fin N → Torus d => fun k => X (τ k)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => Torus d) τ.symm) := by
    funext X k
    show X (τ k) = (Equiv.piCongrLeft (fun _ : Fin N => Torus d) τ.symm X) k
    rw [Equiv.piCongrLeft_apply]
    simp
  rw [e]
  exact h

theorem resp_ae_pair {N : ℕ} {g gm : Torus d → ℝ}
    (hgm : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = g x) :
    ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)), ∀ i j, i < j → gm (X i - X j) = g (X i - X j) := by
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  by_cases hij : i < j
  · have hne : i ≠ j := ne_of_lt hij
    filter_upwards [((resp_mp_pair_sub (d := d) hne).quasiMeasurePreserving).ae hgm] with X hX
    intro _
    exact hX
  · filter_upwards with X
    intro h
    exact absurd h hij

theorem resp_sum_lt_symm {N : ℕ} (F : Fin N → Fin N → ℝ) (hF : ∀ a b, F a b = F b a) :
    2 * (∑ a, ∑ b, if a < b then F a b else 0) = ∑ a, ∑ b, if a ≠ b then F a b else 0 := by
  have h1 : (∑ a, ∑ b, if a < b then F a b else 0) = ∑ a, ∑ b, if b < a then F a b else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hF]
  rw [two_mul]
  nth_rewrite 1 [h1]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · subst h; simp
  · simp [h, h.ne', not_lt.2 h.le]

theorem resp_pairSum_eq_ite {N : ℕ} (g : Torus d → ℝ) (X : Fin N → Torus d) :
    pairSum g X = ∑ a, ∑ b, if a < b then g (X a - X b) else 0 := by
  unfold pairSum
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]

theorem resp_pairSum_perm {N : ℕ} {g : Torus d → ℝ} (heven : ∀ x, g (-x) = g x)
    (τ : Equiv.Perm (Fin N)) (X : Fin N → Torus d) :
    pairSum g (fun k => X (τ k)) = pairSum g X := by
  set Φ : Fin N → Fin N → ℝ := fun a b => if a ≠ b then g (X a - X b) else 0 with hΦdef
  have hE : ∀ a b, (if a ≠ b then g (X (τ a) - X (τ b)) else 0) = Φ (τ a) (τ b) := by
    intro a b
    simp only [hΦdef, ne_eq, τ.injective.eq_iff]
  have hsum : ∑ a, ∑ b, Φ (τ a) (τ b) = ∑ a, ∑ b, Φ a b := by
    calc ∑ a, ∑ b, Φ (τ a) (τ b) = ∑ a, ∑ b, Φ (τ a) b :=
          Finset.sum_congr rfl fun a _ => Equiv.sum_comp τ (Φ (τ a))
      _ = ∑ a, ∑ b, Φ a b := Equiv.sum_comp τ (fun a => ∑ b, Φ a b)
  have hF : ∀ a b, g (X a - X b) = g (X b - X a) := fun a b => by
    rw [← neg_sub, heven]
  have hL := resp_sum_lt_symm (fun a b => g (X (τ a) - X (τ b)))
    (fun a b => by show g (X (τ a) - X (τ b)) = g (X (τ b) - X (τ a)); rw [← neg_sub, heven])
  have hR := resp_sum_lt_symm (fun a b => g (X a - X b)) (fun a b => hF a b)
  beta_reduce at hL hR
  have hL2 : ∑ a, ∑ b, (if a ≠ b then g (X (τ a) - X (τ b)) else 0) = ∑ a, ∑ b, Φ a b := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hE a b
  have hR2 : ∑ a, ∑ b, (if a ≠ b then g (X a - X b) else 0) = ∑ a, ∑ b, Φ a b := rfl
  rw [resp_pairSum_eq_ite, resp_pairSum_eq_ite]
  beta_reduce
  linarith


theorem resp_integrable_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ := by
  refine Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hB x

theorem resp_hasDerivAt_phi {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {S h : α → ℝ} {M B : ℝ} (hSm : Measurable S) (hS : ∀ x, |S x| ≤ M) (hM : 0 ≤ M)
    (hh : Measurable h) (hhB : ∀ x, |h x| ≤ B) (hB : 0 ≤ B) (θ : ℝ) :
    HasDerivAt (fun t => ∫ x, h x * Real.exp (t * S x) ∂μ)
      (∫ x, h x * S x * Real.exp (θ * S x) ∂μ) θ := by
  set R : ℝ := |θ| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hdiff : ∀ x, ∀ t ∈ Metric.ball θ 1,
      HasDerivAt (fun t => h x * Real.exp (t * S x)) (h x * S x * Real.exp (t * S x)) t := by
    intro x t _
    have h1 : HasDerivAt (fun t : ℝ => t * S x) (S x) t := by
      simpa using (hasDerivAt_id t).mul_const (S x)
    have h2 := (h1.exp).const_mul (h x)
    convert h2 using 1
    ring
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Metric.ball θ 1,
      ‖h x * S x * Real.exp (t * S x)‖ ≤ B * M * Real.exp (R * M) := by
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have htR : |t| ≤ R := by
      rw [Metric.mem_ball, Real.dist_eq] at ht
      have := abs_sub_abs_le_abs_sub t θ
      rw [hR]
      linarith
    have hexp : Real.exp (t * S x) ≤ Real.exp (R * M) := by
      apply Real.exp_le_exp.2
      calc t * S x ≤ |t * S x| := le_abs_self _
        _ = |t| * |S x| := abs_mul _ _
        _ ≤ R * M := mul_le_mul htR (hS x) (abs_nonneg _) hR0
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |h x| * |S x| ≤ B * M := mul_le_mul (hhB x) (hS x) (abs_nonneg _) hB
    calc |h x| * |S x| * Real.exp (t * S x) ≤ B * M * Real.exp (t * S x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ B * M * Real.exp (R * M) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hB hM)
  have hmeas : ∀ t, Measurable (fun x => h x * Real.exp (t * S x)) := fun t =>
    hh.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hSm))
  have hmeas' : ∀ t, Measurable (fun x => h x * S x * Real.exp (t * S x)) := fun t =>
    ((hh.mul hSm)).mul (Real.continuous_exp.measurable.comp (measurable_const.mul hSm))
  have hint : Integrable (fun x => h x * Real.exp (θ * S x)) μ := by
    refine resp_integrable_bdd μ (hmeas θ) (B := B * Real.exp (R * M)) fun x => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (θ * S x) ≤ Real.exp (R * M) := by
      apply Real.exp_le_exp.2
      calc θ * S x ≤ |θ * S x| := le_abs_self _
        _ = |θ| * |S x| := abs_mul _ _
        _ ≤ R * M := mul_le_mul (by rw [hR]; linarith) (hS x) (abs_nonneg _) hR0
    exact mul_le_mul (hhB x) hexp (Real.exp_pos _).le hB
  have hint' : Integrable (fun x => h x * S x * Real.exp (θ * S x)) μ := by
    refine resp_integrable_bdd μ (hmeas' θ) (B := B * M * Real.exp (R * M)) fun x => ?_
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (θ * S x) ≤ Real.exp (R * M) := by
      apply Real.exp_le_exp.2
      calc θ * S x ≤ |θ * S x| := le_abs_self _
        _ = |θ| * |S x| := abs_mul _ _
        _ ≤ R * M := mul_le_mul (by rw [hR]; linarith) (hS x) (abs_nonneg _) hR0
    have h1 : |h x| * |S x| ≤ B * M := mul_le_mul (hhB x) (hS x) (abs_nonneg _) hB
    exact (mul_le_mul h1 hexp (Real.exp_pos _).le (mul_nonneg hB hM))
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := θ)
    (s := Metric.ball θ 1) (F := fun t x => h x * Real.exp (t * S x))
    (F' := fun t x => h x * S x * Real.exp (t * S x))
    (bound := fun _ => B * M * Real.exp (R * M))
    (Metric.ball_mem_nhds θ one_pos)
    (Filter.Eventually.of_forall fun t => (hmeas t).aestronglyMeasurable)
    hint (hmeas' θ).aestronglyMeasurable hbound (integrable_const _)
    (by
      filter_upwards with x
      intro t ht
      exact hdiff x t ht)
  exact this.2

theorem resp_contDiff_phi {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {S : α → ℝ} {M : ℝ} (hSm : Measurable S) (hS : ∀ x, |S x| ≤ M) (hM : 0 ≤ M) (n : ℕ) :
    ∀ (h : α → ℝ) (B : ℝ), Measurable h → (∀ x, |h x| ≤ B) → 0 ≤ B →
      ContDiff ℝ (n : WithTop ℕ∞) (fun t => ∫ x, h x * Real.exp (t * S x) ∂μ) := by
  induction n with
  | zero =>
    intro h B hh hhB hB
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_iff_continuousAt.2 fun θ => ?_
    exact (resp_hasDerivAt_phi μ hSm hS hM hh hhB hB θ).continuousAt
  | succ n ih =>
    intro h B hh hhB hB
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl]
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun θ => (resp_hasDerivAt_phi μ hSm hS hM hh hhB hB θ).differentiableAt, fun hω => ?_, ?_⟩
    · exfalso
      exact absurd hω (by simp)
    · have hder : deriv (fun t => ∫ x, h x * Real.exp (t * S x) ∂μ) =
          fun t => ∫ x, (h x * S x) * Real.exp (t * S x) ∂μ := by
        funext t
        exact (resp_hasDerivAt_phi μ hSm hS hM hh hhB hB t).deriv
      rw [hder]
      refine ih (fun x => h x * S x) (B * M) (hh.mul hSm) (fun x => ?_) (mul_nonneg hB hM)
      rw [abs_mul]
      exact mul_le_mul (hhB x) (hS x) (abs_nonneg _) hB

theorem resp_contDiff_phi_inf {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {S : α → ℝ} {M : ℝ} (hSm : Measurable S) (hS : ∀ x, |S x| ≤ M) (hM : 0 ≤ M)
    (h : α → ℝ) (B : ℝ) (hh : Measurable h) (hhB : ∀ x, |h x| ≤ B) (hB : 0 ≤ B) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∫ x, h x * Real.exp (t * S x) ∂μ) :=
  contDiff_infty.2 fun n => resp_contDiff_phi μ hSm hS hM n h B hh hhB hB


/-! ### EQ-01c helpers for `finite_response_rates` (canonical Gibbs derivative identities) -/

section RespFinite

theorem resp_periodicRiesz_lower (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ c : ℝ, ∀ x : Torus d, x ≠ 0 → -c ≤ periodicRiesz d s x := by
  have hd0 : 0 < d := by omega
  obtain ⟨r, δ, hδ, hr, hsing⟩ := periodicRiesz_local_singularity hd hs hsd
  obtain ⟨C1, C2, hC1, hC2, hbd⟩ := KernelAux.periodicRiesz_box_bound hd hs.le hsd
  have hrc : Continuous (fun y : Fin d → ℝ => r (KernelAux.boxPt y)) := by
    have h1 : Continuous (Torus.lift r) := by
      unfold Torus.IsSmooth Torus.IsCk at hr
      exact hr.continuous
    have h2 : (fun y : Fin d → ℝ => r (KernelAux.boxPt y)) =
        fun y => Torus.lift r (WithLp.toLp 2 y) := by
      funext y
      simp only [Torus.lift, Function.comp]
      congr 1
    rw [h2]
    exact h1.comp (PiLp.continuous_toLp 2 _)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := fun _ : Fin d => (-1 : ℝ)) (b := fun _ => 1)).exists_bound_of_continuousOn
    hrc.continuousOn
  have hMb : ∀ y ∈ KernelAux.Box d, |r (KernelAux.boxPt y)| ≤ ‖M‖ := by
    intro y hy
    have hyI : y ∈ Set.Icc (fun _ : Fin d => (-1 : ℝ)) (fun _ => 1) := by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := hy i; simp only [Set.mem_Ioc] at this; linarith [this.1]
      · have := hy i; simp only [Set.mem_Ioc] at this; linarith [this.2]
    have := hM y hyI
    simpa [Real.norm_eq_abs] using this.trans (le_abs_self M)
  set a : ℝ := (s + d) / 2 with ha_def
  have ha : 0 < a := by
    have : (0 : ℝ) ≤ d := by positivity
    rw [ha_def]; linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  refine ⟨max ‖M‖ (C1 * (δ / d) ^ (-a) + C2), fun x hx => ?_⟩
  obtain ⟨y, hyB, rfl⟩ := resp_exists_box x
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hx
    funext i
    simp [KernelAux.boxPt]
  set ye : Euc d := WithLp.toLp 2 y with hye
  have hmk : Torus.mk ye = KernelAux.boxPt y := by
    funext i
    simp [Torus.mk, KernelAux.boxPt, hye]
  by_cases hA : ‖ye‖ < δ
  · have hyne : ye ≠ 0 := by
      intro h0
      apply hy0
      funext i
      have := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h0) i
      simpa [hye] using this
    have hsg := hsing ye hA hyne
    rw [hmk] at hsg
    have hpos : 0 ≤ ‖ye‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    have hr' := hMb y hyB
    have hle : -‖M‖ ≤ r (KernelAux.boxPt y) := by
      have := neg_abs_le (r (KernelAux.boxPt y))
      linarith [le_abs_self ‖M‖, abs_le.mp hr']
    have : -max ‖M‖ (C1 * (δ / d) ^ (-a) + C2) ≤ -‖M‖ := by
      have := le_max_left ‖M‖ (C1 * (δ / d) ^ (-a) + C2)
      linarith
    rw [hsg]
    linarith
  · push Not at hA
    have hyn : δ / d ≤ ‖y‖ := by
      have h1 := KernelAux2.norm_toLp_le_card_mul hd0 y
      have h2 : ‖ye‖ ≤ d * ‖y‖ := h1
      rw [div_le_iff₀ hdpos]
      linarith
    have hyp : 0 < δ / d := by positivity
    have hgb := hbd y hyB hy0
    have hpow : ‖y‖ ^ (-a) ≤ (δ / d) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hyp hyn (by linarith)
    have hC : C1 * ‖y‖ ^ (-a) + C2 ≤ C1 * (δ / d) ^ (-a) + C2 := by
      nlinarith
    have hgb' : -(C1 * (δ / d) ^ (-a) + C2) ≤ periodicRiesz d s (KernelAux.boxPt y) := by
      have := abs_le.mp (hgb.trans hC)
      linarith [this.1]
    have : -max ‖M‖ (C1 * (δ / d) ^ (-a) + C2) ≤ -(C1 * (δ / d) ^ (-a) + C2) := by
      have := le_max_right ‖M‖ (C1 * (δ / d) ^ (-a) + C2)
      linarith
    linarith

theorem resp_good_kernel (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ gm : Torus d → ℝ, Measurable gm ∧ ∃ c : ℝ, 0 ≤ c ∧ (∀ x, -c ≤ gm x) ∧
      ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x := by
  obtain ⟨c0, hc0⟩ := resp_periodicRiesz_lower hd hs hsd
  have hc : 0 ≤ max c0 0 := le_max_right _ _
  have hae := KernelAux.aestronglyMeasurable_periodicRiesz hd hs.le hsd
  have hg'm : Measurable (hae.mk _) := hae.stronglyMeasurable_mk.measurable
  refine ⟨fun x => max (hae.mk _ x) (-(max c0 0)), hg'm.max measurable_const,
    max c0 0, hc, fun x => le_max_right _ _, ?_⟩
  have h1 : ∀ᵐ x ∂(volume : Measure (Torus d)), hae.mk _ x = periodicRiesz d s x :=
    hae.ae_eq_mk.symm
  have h2 : ∀ᵐ x ∂(volume : Measure (Torus d)), x ≠ 0 := KernelAux.torus_ae_ne (by omega)
  filter_upwards [h1, h2] with x hx1 hx2
  show max (hae.mk _ x) (-(max c0 0)) = periodicRiesz d s x
  rw [hx1]
  exact max_eq_left (by linarith [hc0 x hx2, le_max_left c0 0])

theorem resp_pairSum_measurable {N : ℕ} {gm : Torus d → ℝ} (hgm : Measurable gm) :
    Measurable (fun X : Fin N → Torus d => pairSum gm X) := by
  unfold pairSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem resp_pairSum_lower {N : ℕ} {gm : Torus d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hgc : ∀ x, -c ≤ gm x) (X : Fin N → Torus d) : -(c * N * N) ≤ pairSum gm X := by
  unfold pairSum
  calc -(c * N * N) = ∑ _i : Fin N, -(c * N) := by simp; ring
    _ ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), gm (X i - X j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hcard : ((Finset.univ.filter (fun j => i < j)).card : ℝ) ≤ N := by
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
        calc -(c * N) ≤ -(c * ((Finset.univ.filter (fun j => i < j)).card : ℝ)) := by
              nlinarith
          _ = ∑ _j ∈ Finset.univ.filter (fun j => i < j), -c := by
              simp [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun j _ => hgc _

/-- The pair weight `exp(-(β/N) ∑_{i<j} g(x_i - x_j))` of the canonical Gibbs law. -/
def respW (gm : Torus d → ℝ) (β : ℝ) {N : ℕ} (X : Fin N → Torus d) : ℝ :=
  Real.exp (-(β * (1 / (N : ℝ))) * pairSum gm X)

/-- The one-body statistic `S(X) = ∑_i cos(2π k·x_i)`. -/
def respS (k : Lattice d) {N : ℕ} (X : Fin N → Torus d) : ℝ :=
  ∑ i, Torus.cosMode k (X i)

/-- `∫ S^j · W · exp(θ S)`: the tilted moments `A_j(θ)`. -/
def respA (k : Lattice d) (gm : Torus d → ℝ) (β : ℝ) (N : ℕ) (j : ℕ) (θ : ℝ) : ℝ :=
  ∫ X : Fin N → Torus d, (respS k X ^ j * respW gm β X) * Real.exp (θ * respS k X)

theorem respS_continuous (k : Lattice d) (N : ℕ) :
    Continuous (fun X : Fin N → Torus d => respS k X) := by
  unfold respS
  exact continuous_finset_sum _ fun i _ => (Torus.continuous_cosMode k).comp (continuous_apply i)

theorem respS_abs_le (k : Lattice d) {N : ℕ} (X : Fin N → Torus d) : |respS k X| ≤ N := by
  unfold respS
  calc |∑ i, Torus.cosMode k (X i)| ≤ ∑ i, |Torus.cosMode k (X i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := Torus.norm_cosMode_le k (X i)
        rwa [Real.norm_eq_abs] at this
    _ = N := by simp

theorem respS_perm (k : Lattice d) {N : ℕ} (τ : Equiv.Perm (Fin N)) (X : Fin N → Torus d) :
    respS k (fun j => X (τ j)) = respS k X := by
  unfold respS
  exact Equiv.sum_comp τ (fun i => Torus.cosMode k (X i))

theorem respW_measurable {N : ℕ} (gm : Torus d → ℝ) (hgm : Measurable gm) (β : ℝ) :
    Measurable (fun X : Fin N → Torus d => respW gm β X) := by
  unfold respW
  exact Real.continuous_exp.measurable.comp
    (measurable_const.mul (resp_pairSum_measurable hgm))

theorem respW_pos (gm : Torus d → ℝ) (β : ℝ) {N : ℕ} (X : Fin N → Torus d) :
    0 < respW gm β X :=
  Real.exp_pos _

theorem respW_bound (gm : Torus d → ℝ) {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c)
    (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N) (X : Fin N → Torus d) :
    respW gm β X ≤ Real.exp (β * c * N) := by
  unfold respW
  apply Real.exp_le_exp.2
  have hP := resp_pairSum_lower hc hgc X
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 ≤ β * (1 / (N : ℝ)) := by positivity
  have key : β * (1 / (N : ℝ)) * (c * N * N) = β * c * N := by
    field_simp
  have := mul_le_mul_of_nonneg_left hP hq
  linarith

theorem resp_ham_eq (g : Torus d → ℝ) {N : ℕ} (k : Lattice d) (β θ : ℝ) (hβ : β ≠ 0)
    (X : Fin N → Torus d) :
    -β * canonicalHamiltonian g (rateV k β θ) X =
      θ * respS k X + -(β * (1 / (N : ℝ))) * pairSum g X := by
  have hV : ∑ i, rateV k β θ (X i) = -(θ / β) * respS k X := by
    unfold respS rateV
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold canonicalHamiltonian pairSum
  rw [mul_add, hV]
  field_simp

theorem resp_ae_dens (g gm : Torus d → ℝ)
    (hgm : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = g x) {N : ℕ} (k : Lattice d) (β θ : ℝ)
    (hβ : β ≠ 0) :
    ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)),
      Real.exp (-β * canonicalHamiltonian g (rateV k β θ) X) =
        Real.exp (θ * respS k X) * respW gm β X := by
  filter_upwards [resp_ae_pair (N := N) hgm] with X hX
  have hP : pairSum gm X = pairSum g X := by
    unfold pairSum
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      hX i j (Finset.mem_filter.1 hj).2
  unfold respW
  rw [hP, ← Real.exp_add, resp_ham_eq g k β θ hβ X]

theorem resp_rateGibbs_eq (g gm : Torus d → ℝ)
    (hgm : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = g x) {N : ℕ} (k : Lattice d) (β θ : ℝ)
    (hβ : β ≠ 0) :
    canonicalGibbs g (rateV k β θ) N β =
      (ENNReal.ofReal (∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X))⁻¹ •
        (volume : Measure (Fin N → Torus d)).withDensity
          (fun X => ENNReal.ofReal (Real.exp (θ * respS k X) * respW gm β X)) := by
  have e1 : canonicalPartition g (rateV k β θ) N β =
      ∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X :=
    integral_congr_ae (resp_ae_dens g gm hgm k β θ hβ)
  have e2 : (volume : Measure (Fin N → Torus d)).withDensity
      (fun X => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g (rateV k β θ) X))) =
      (volume : Measure (Fin N → Torus d)).withDensity
      (fun X => ENNReal.ofReal (Real.exp (θ * respS k X) * respW gm β X)) :=
    withDensity_congr_ae (by
      filter_upwards [resp_ae_dens g gm hgm k β θ hβ] with X hX
      exact congrArg ENNReal.ofReal hX)
  unfold canonicalGibbs
  rw [e2, e1]

theorem resp_integral_smul_withDensity {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (D : α → ℝ) (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) (f : α → ℝ) :
    ∫ x, f x ∂((ENNReal.ofReal (∫ x, D x ∂ν))⁻¹ • ν.withDensity (fun x => ENNReal.ofReal (D x))) =
      (∫ x, D x ∂ν)⁻¹ * ∫ x, D x * f x ∂ν := by
  have hDm' : Measurable (fun x => ENNReal.ofReal (D x)) := ENNReal.measurable_ofReal.comp hD
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hDm'
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hZ : 0 ≤ ∫ x, D x ∂ν := integral_nonneg hD0
  have hf : ∀ x, (ENNReal.ofReal (D x)).toReal • f x = D x * f x := fun x => by
    rw [ENNReal.toReal_ofReal (hD0 x), smul_eq_mul]
  simp only [hf]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ, smul_eq_mul]

theorem resp_integrable_term (k : Lattice d) (gm : Torus d → ℝ) (hgm : Measurable gm)
    (β : ℝ) (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N' : ℕ} (hN : 0 < N')
    (j : ℕ) (θ : ℝ) :
    Integrable (fun X : Fin N' → Torus d => (respS k X ^ j * respW gm β X) * Real.exp (θ * respS k X))
      (volume : Measure (Fin N' → Torus d)) := by
  refine resp_integrable_bdd _ ?_ (B := (N' : ℝ) ^ j * Real.exp (β * c * N') * Real.exp (|θ| * N')) ?_
  · exact ((((respS_continuous k N').measurable.pow_const j).mul
      (respW_measurable gm hgm β)).mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul (respS_continuous k N').measurable)))
  · intro X
    rw [abs_mul, abs_mul, abs_pow, abs_of_pos (respW_pos gm β X), abs_of_pos (Real.exp_pos _)]
    have hS := respS_abs_le k X
    have hW := respW_bound gm hβ hc hgc hN X
    have hexp : Real.exp (θ * respS k X) ≤ Real.exp (|θ| * N') := by
      apply Real.exp_le_exp.2
      calc θ * respS k X ≤ |θ * respS k X| := le_abs_self _
        _ = |θ| * |respS k X| := abs_mul _ _
        _ ≤ |θ| * N' := mul_le_mul_of_nonneg_left hS (abs_nonneg _)
    have hSp : |respS k X| ^ j ≤ (N' : ℝ) ^ j := pow_le_pow_left₀ (abs_nonneg _) hS j
    have h1 : |respS k X| ^ j * respW gm β X ≤ (N' : ℝ) ^ j * Real.exp (β * c * N') :=
      mul_le_mul hSp hW (le_of_lt (respW_pos gm β X)) (by positivity)
    exact mul_le_mul h1 hexp (Real.exp_pos _).le (by positivity)

end RespFinite

section RespFinite2

theorem resp_pair_firstMarginal {N : ℕ} (hN : 0 < N) (P : Measure (Config d N))
    (φ : Torus d → ℝ) (hφ : Continuous φ) :
    pair (firstMarginal P) φ = ∫ X, φ (X ⟨0, hN⟩) ∂P := by
  unfold pair firstMarginal
  rw [dif_pos hN]
  exact integral_map (measurable_pi_apply _).aemeasurable hφ.aestronglyMeasurable

theorem resp_D_perm (g gm : Torus d → ℝ) (heven : ∀ x, g (-x) = g x)
    (hgm : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = g x) {N : ℕ} (k : Lattice d) (β θ : ℝ)
    (τ : Equiv.Perm (Fin N)) :
    ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)),
      Real.exp (θ * respS k (fun j => X (τ j))) * respW gm β (fun j => X (τ j)) =
        Real.exp (θ * respS k X) * respW gm β X := by
  have hT := resp_mp_perm (d := d) (N := N) τ
  have hA : ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)), pairSum gm X = pairSum g X := by
    filter_upwards [resp_ae_pair (N := N) hgm] with X hX
    unfold pairSum
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      hX i j (Finset.mem_filter.1 hj).2
  have hB : ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)),
      pairSum gm (fun j => X (τ j)) = pairSum g (fun j => X (τ j)) :=
    hT.quasiMeasurePreserving.ae hA
  filter_upwards [hA, hB] with X hXA hXB
  unfold respW
  rw [hXB, resp_pairSum_perm heven τ X, respS_perm k τ X, ← hXA]

theorem resp_integral_cos_perm (k : Lattice d) {N : ℕ} (hN : 0 < N)
    (D : (Fin N → Torus d) → ℝ) (hDm : Measurable D) (B : ℝ) (hB : ∀ X, |D X| ≤ B)
    (hD : ∀ τ : Equiv.Perm (Fin N),
      ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)), D (fun j => X (τ j)) = D X)
    (i : Fin N) :
    ∫ X, Torus.cosMode k (X i) * D X ∂(volume : Measure (Fin N → Torus d)) =
      ∫ X, Torus.cosMode k (X ⟨0, hN⟩) * D X ∂(volume : Measure (Fin N → Torus d)) := by
  set i0 : Fin N := ⟨0, hN⟩ with hi0
  set τ : Equiv.Perm (Fin N) := Equiv.swap i0 i with hτ
  have hT := resp_mp_perm (d := d) (N := N) τ
  have hF : Measurable (fun X : Fin N → Torus d => Torus.cosMode k (X i) * D X) :=
    ((Torus.continuous_cosMode k).measurable.comp (measurable_pi_apply i)).mul hDm
  have step1 : ∫ X, Torus.cosMode k (X i) * D X ∂(volume : Measure (Fin N → Torus d)) =
      ∫ X, Torus.cosMode k ((fun j => X (τ j)) i) * D (fun j => X (τ j))
        ∂(volume : Measure (Fin N → Torus d)) := by
    conv_lhs => rw [← hT.map_eq]
    exact integral_map hT.measurable.aemeasurable hF.aestronglyMeasurable
  have hτi : τ i = i0 := Equiv.swap_apply_right i0 i
  have step2 : ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)),
      Torus.cosMode k ((fun j => X (τ j)) i) * D (fun j => X (τ j)) =
        Torus.cosMode k (X i0) * D X := by
    filter_upwards [hD τ] with X hX
    show Torus.cosMode k (X (τ i)) * D (fun j => X (τ j)) = Torus.cosMode k (X i0) * D X
    rw [hτi, hX]
  rw [step1]
  exact integral_congr_ae step2

theorem resp_integral_sum_cos (k : Lattice d) {N : ℕ} (hN : 0 < N)
    (D : (Fin N → Torus d) → ℝ) (hDm : Measurable D) (B : ℝ) (hB : ∀ X, |D X| ≤ B)
    (hD : ∀ τ : Equiv.Perm (Fin N),
      ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)), D (fun j => X (τ j)) = D X) :
    ∫ X, respS k X * D X ∂(volume : Measure (Fin N → Torus d)) =
      (N : ℝ) * ∫ X, Torus.cosMode k (X ⟨0, hN⟩) * D X ∂(volume : Measure (Fin N → Torus d)) := by
  have hint : ∀ i : Fin N,
      Integrable (fun X : Fin N → Torus d => Torus.cosMode k (X i) * D X)
        (volume : Measure (Fin N → Torus d)) := by
    intro i
    refine resp_integrable_bdd _
      (((Torus.continuous_cosMode k).measurable.comp (measurable_pi_apply i)).mul hDm) (B := B) ?_
    intro X
    rw [abs_mul]
    have hc : |Torus.cosMode k (X i)| ≤ 1 := by
      have := Torus.norm_cosMode_le k (X i)
      rwa [Real.norm_eq_abs] at this
    calc |Torus.cosMode k (X i)| * |D X| ≤ 1 * B := mul_le_mul hc (hB X) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  unfold respS
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => hint i)]
  have h1 : ∀ i : Fin N, ∫ X, Torus.cosMode k (X i) * D X ∂(volume : Measure (Fin N → Torus d)) =
      ∫ X, Torus.cosMode k (X ⟨0, hN⟩) * D X ∂(volume : Measure (Fin N → Torus d)) :=
    fun i => resp_integral_cos_perm k hN D hDm B hB hD i
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem resp_respA_zero_eq (k : Lattice d) (gm : Torus d → ℝ) (β : ℝ) (N : ℕ) (θ : ℝ) :
    respA k gm β N 0 θ = ∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X := by
  unfold respA
  congr 1
  funext X
  ring

theorem resp_respA_zero_pos (k : Lattice d) (gm : Torus d → ℝ) (hgm : Measurable gm) {β : ℝ}
    (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    0 < respA k gm β N 0 θ := by
  have hint := resp_integrable_term k gm hgm β hβ hc hgc hN 0 θ
  have hpos : ∀ X : Fin N → Torus d,
      0 < (respS k X ^ 0 * respW gm β X) * Real.exp (θ * respS k X) := fun X =>
    mul_pos (by rw [pow_zero, one_mul]; exact respW_pos gm β X) (Real.exp_pos _)
  unfold respA
  rw [integral_pos_iff_support_of_nonneg (fun X => (hpos X).le) hint]
  have hsupp : Function.support (fun X : Fin N → Torus d =>
      (respS k X ^ 0 * respW gm β X) * Real.exp (θ * respS k X)) = Set.univ :=
    Set.eq_univ_of_forall fun X => (hpos X).ne'
  rw [hsupp, measure_univ]
  exact zero_lt_one

theorem resp_respA_hasDerivAt (k : Lattice d) (gm : Torus d → ℝ) (hgm : Measurable gm) {β : ℝ}
    (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N) (j : ℕ)
    (θ : ℝ) :
    HasDerivAt (fun t => respA k gm β N j t) (respA k gm β N (j + 1) θ) θ := by
  have hSm : Measurable (fun X : Fin N → Torus d => respS k X) :=
    (respS_continuous k N).measurable
  have hSb : ∀ X : Fin N → Torus d, |respS k X| ≤ (N : ℝ) := respS_abs_le k
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hh : Measurable (fun X : Fin N → Torus d => respS k X ^ j * respW gm β X) :=
    (hSm.pow_const j).mul (respW_measurable gm hgm β)
  have hhB : ∀ X : Fin N → Torus d, |respS k X ^ j * respW gm β X| ≤
      (N : ℝ) ^ j * Real.exp (β * c * N) := fun X => by
    rw [abs_mul, abs_pow, abs_of_pos (respW_pos gm β X)]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSb X) j) (respW_bound gm hβ hc hgc hN X)
      (respW_pos gm β X).le (by positivity)
  have hmain := resp_hasDerivAt_phi (volume : Measure (Fin N → Torus d))
    (S := fun X => respS k X) (h := fun X => respS k X ^ j * respW gm β X) hSm hSb hNr hh hhB
    (by positivity) θ
  beta_reduce at hmain
  unfold respA
  convert hmain using 1
  congr 1
  funext X
  ring

theorem resp_respA_contDiff (k : Lattice d) (gm : Torus d → ℝ) (hgm : Measurable gm) {β : ℝ}
    (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => respA k gm β N j t) := by
  have hSm : Measurable (fun X : Fin N → Torus d => respS k X) :=
    (respS_continuous k N).measurable
  have hSb : ∀ X : Fin N → Torus d, |respS k X| ≤ (N : ℝ) := respS_abs_le k
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hh : Measurable (fun X : Fin N → Torus d => respS k X ^ j * respW gm β X) :=
    (hSm.pow_const j).mul (respW_measurable gm hgm β)
  have hhB : ∀ X : Fin N → Torus d, |respS k X ^ j * respW gm β X| ≤
      (N : ℝ) ^ j * Real.exp (β * c * N) := fun X => by
    rw [abs_mul, abs_pow, abs_of_pos (respW_pos gm β X)]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hSb X) j) (respW_bound gm hβ hc hgc hN X)
      (respW_pos gm β X).le (by positivity)
  exact resp_contDiff_phi_inf (volume : Measure (Fin N → Torus d)) hSm hSb hNr
    (fun X => respS k X ^ j * respW gm β X) ((N : ℝ) ^ j * Real.exp (β * c * N)) hh hhB
    (by positivity)

theorem resp_integral_comb4 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f0 f1 f2 f3 : α → ℝ) (h0 : Integrable f0 μ) (h1 : Integrable f1 μ)
    (h2 : Integrable f2 μ) (h3 : Integrable f3 μ) (a b c e : ℝ) :
    ∫ x, (a * f3 x - b * f2 x + c * f1 x - e * f0 x) ∂μ =
      a * ∫ x, f3 x ∂μ - b * ∫ x, f2 x ∂μ + c * ∫ x, f1 x ∂μ - e * ∫ x, f0 x ∂μ := by
  have i3 : Integrable (fun x => a * f3 x) μ := h3.const_mul a
  have i2 : Integrable (fun x => b * f2 x) μ := h2.const_mul b
  have i1 : Integrable (fun x => c * f1 x) μ := h1.const_mul c
  have i0 : Integrable (fun x => e * f0 x) μ := h0.const_mul e
  have i32 : Integrable (fun x => a * f3 x - b * f2 x) μ := i3.sub i2
  have i321 : Integrable (fun x => a * f3 x - b * f2 x + c * f1 x) μ := i32.add i1
  rw [integral_sub i321 i0, integral_add i32 i1, integral_sub i3 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul]

theorem resp_integral_comb3 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f0 f1 f2 : α → ℝ) (h0 : Integrable f0 μ) (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (a b c : ℝ) :
    ∫ x, (a * f2 x - b * f1 x + c * f0 x) ∂μ =
      a * ∫ x, f2 x ∂μ - b * ∫ x, f1 x ∂μ + c * ∫ x, f0 x ∂μ := by
  have i2 : Integrable (fun x => a * f2 x) μ := h2.const_mul a
  have i1 : Integrable (fun x => b * f1 x) μ := h1.const_mul b
  have i0 : Integrable (fun x => c * f0 x) μ := h0.const_mul c
  have i21 : Integrable (fun x => a * f2 x - b * f1 x) μ := i2.sub i1
  rw [integral_add i21 i0, integral_sub i2 i1, integral_const_mul, integral_const_mul,
    integral_const_mul]

end RespFinite2

/-- Lemma 4.19 `M:V:lem:finite-response-rates` (source lines 5220-5233),
`V:eq:finite-response-rates`: for each fixed `N ≥ 2`, `M_N` and `C_N` are smooth,
`M_N' = C_N` and `C_N'(θ) = √N E[Y_{N,θ}³]`. -/
theorem finite_response_rates (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (N : ℕ) (hN : 2 ≤ N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rateMeanN d s k β N) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rateVarN d s k β N) ∧
    (∀ θ, HasDerivAt (rateMeanN d s k β N) (rateVarN d s k β N θ) θ) ∧
    (∀ θ, HasDerivAt (rateVarN d s k β N)
      (Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)) θ) := by
  have hs0 : 0 < s := by
    have h1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨gm, hgm_m, c, hc, hgc, hgm_ae⟩ := resp_good_kernel hd hs0 hsd
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := hNr.ne'
  have hβne : β ≠ 0 := hβ.ne'
  have hSm : Measurable (fun X : Fin N → Torus d => respS k X) :=
    (respS_continuous k N).measurable
  have hSb : ∀ X : Fin N → Torus d, |respS k X| ≤ (N : ℝ) := respS_abs_le k
  have hGibbs : ∀ θ : ℝ, rateGibbs d s k β θ N =
      (ENNReal.ofReal (∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X))⁻¹ •
        (volume : Measure (Fin N → Torus d)).withDensity
          (fun X => ENNReal.ofReal (Real.exp (θ * respS k X) * respW gm β X)) :=
    fun θ => resp_rateGibbs_eq (periodicRiesz d s) gm hgm_ae k β θ hβne
  have hDm : ∀ θ : ℝ, Measurable (fun X : Fin N → Torus d => Real.exp (θ * respS k X) * respW gm β X) :=
    fun θ => (Real.continuous_exp.measurable.comp (measurable_const.mul hSm)).mul
      (respW_measurable gm hgm_m β)
  have hD0 : ∀ (θ : ℝ) (X : Fin N → Torus d), 0 ≤ Real.exp (θ * respS k X) * respW gm β X :=
    fun θ X => (mul_pos (Real.exp_pos _) (respW_pos gm β X)).le
  have hDb : ∀ (θ : ℝ) (X : Fin N → Torus d),
      |Real.exp (θ * respS k X) * respW gm β X| ≤ Real.exp (|θ| * N) * Real.exp (β * c * N) := by
    intro θ X
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (respW_pos gm β X)]
    refine mul_le_mul ?_ (respW_bound gm hβ hc hgc hNpos X) (respW_pos gm β X).le (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    calc θ * respS k X ≤ |θ * respS k X| := le_abs_self _
      _ = |θ| * |respS k X| := abs_mul _ _
      _ ≤ |θ| * N := mul_le_mul_of_nonneg_left (hSb X) (abs_nonneg _)
  have hDperm : ∀ (θ : ℝ) (τ : Equiv.Perm (Fin N)),
      ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)),
        Real.exp (θ * respS k (fun j => X (τ j))) * respW gm β (fun j => X (τ j)) =
          Real.exp (θ * respS k X) * respW gm β X :=
    fun θ τ => resp_D_perm (periodicRiesz d s) gm (fun x => periodicRiesz_neg x) hgm_ae k β θ τ
  have hexpect : ∀ (θ : ℝ) (f : (Fin N → Torus d) → ℝ), Measurable f →
      ∫ X, f X ∂(rateGibbs d s k β θ N) =
        (respA k gm β N 0 θ)⁻¹ *
          ∫ X, Real.exp (θ * respS k X) * respW gm β X * f X ∂(volume : Measure (Fin N → Torus d)) := by
    intro θ f _
    rw [hGibbs θ, resp_respA_zero_eq]
    exact resp_integral_smul_withDensity _ _ (hDm θ) (hD0 θ) f
  have hsumid : ∀ θ : ℝ,
      ∫ X, respS k X * (Real.exp (θ * respS k X) * respW gm β X) ∂(volume : Measure (Fin N → Torus d)) =
        (N : ℝ) * ∫ X, Torus.cosMode k (X ⟨0, hNpos⟩) * (Real.exp (θ * respS k X) * respW gm β X)
          ∂(volume : Measure (Fin N → Torus d)) :=
    fun θ => resp_integral_sum_cos k hNpos (fun X => Real.exp (θ * respS k X) * respW gm β X)
      (hDm θ) (Real.exp (|θ| * N) * Real.exp (β * c * N)) (hDb θ) (hDperm θ)
  have hA1 : ∀ θ : ℝ, respA k gm β N 1 θ =
      ∫ X, respS k X * (Real.exp (θ * respS k X) * respW gm β X)
        ∂(volume : Measure (Fin N → Torus d)) := by
    intro θ
    unfold respA
    congr 1
    funext X
    ring
  -- the first moment identity
  have hK1 : ∀ θ : ℝ, rateMeanN d s k β N θ =
      respA k gm β N 1 θ / ((N : ℝ) * respA k gm β N 0 θ) := by
    intro θ
    have hZ : 0 < respA k gm β N 0 θ := resp_respA_zero_pos k gm hgm_m hβ hc hgc hNpos θ
    have hcos : ∫ X, Torus.cosMode k (X ⟨0, hNpos⟩) * (Real.exp (θ * respS k X) * respW gm β X)
        ∂(volume : Measure (Fin N → Torus d)) = respA k gm β N 1 θ / (N : ℝ) := by
      rw [hA1 θ, hsumid θ]
      field_simp
    have hcomm : ∫ X, Real.exp (θ * respS k X) * respW gm β X * Torus.cosMode k (X ⟨0, hNpos⟩)
        ∂(volume : Measure (Fin N → Torus d)) =
        ∫ X, Torus.cosMode k (X ⟨0, hNpos⟩) * (Real.exp (θ * respS k X) * respW gm β X)
          ∂(volume : Measure (Fin N → Torus d)) := by
      congr 1
      funext X
      ring
    unfold rateMeanN
    rw [resp_pair_firstMarginal hNpos _ (Torus.cosMode k) (Torus.continuous_cosMode k)]
    have h := hexpect θ (fun X => Torus.cosMode k (X ⟨0, hNpos⟩))
      (((Torus.continuous_cosMode k).measurable).comp (measurable_pi_apply _))
    beta_reduce at h
    rw [h, hcomm, hcos]
    have hZne : respA k gm β N 0 θ ≠ 0 := hZ.ne'
    field_simp
  have hYc : ∀ θ : ℝ, Continuous (fun X : Fin N → Torus d => rateY d s k β N θ X) := by
    intro θ
    unfold rateY
    exact continuous_const.mul ((continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (Torus.continuous_cosMode k).comp (continuous_apply i))).sub continuous_const)
  have hSY : ∀ (θ : ℝ) (X : Fin N → Torus d), ∑ i, Torus.cosMode k (X i) = respS k X := fun _ _ => rfl
  -- the variance identity
  have hK2 : ∀ θ : ℝ, rateVarN d s k β N θ = (1 / (N : ℝ)) *
      (respA k gm β N 2 θ / respA k gm β N 0 θ -
        respA k gm β N 1 θ / respA k gm β N 0 θ * (respA k gm β N 1 θ / respA k gm β N 0 θ)) := by
    intro θ
    have hZ : 0 < respA k gm β N 0 θ := resp_respA_zero_pos k gm hgm_m hβ hc hgc hNpos θ
    have hZne : respA k gm β N 0 θ ≠ 0 := hZ.ne'
    have hM := hK1 θ
    have hT0 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 0 θ
    have hT1 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 1 θ
    have hT2 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 2 θ
    have hpt : ∀ X : Fin N → Torus d,
        Real.exp (θ * respS k X) * respW gm β X * rateY d s k β N θ X ^ 2 =
          (1 / (N : ℝ)) * ((respS k X ^ 2 * respW gm β X) * Real.exp (θ * respS k X)) -
            2 * rateMeanN d s k β N θ * ((respS k X ^ 1 * respW gm β X) * Real.exp (θ * respS k X)) +
            (N : ℝ) * rateMeanN d s k β N θ ^ 2 *
              ((respS k X ^ 0 * respW gm β X) * Real.exp (θ * respS k X)) := by
      intro X
      unfold rateY
      rw [hSY θ X, mul_pow, Real.sq_sqrt hNr.le]
      field_simp
      ring
    have hint : ∫ X, Real.exp (θ * respS k X) * respW gm β X * rateY d s k β N θ X ^ 2
        ∂(volume : Measure (Fin N → Torus d)) =
        (1 / (N : ℝ)) * respA k gm β N 2 θ - 2 * rateMeanN d s k β N θ * respA k gm β N 1 θ +
          (N : ℝ) * rateMeanN d s k β N θ ^ 2 * respA k gm β N 0 θ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact resp_integral_comb3 _ _ _ _ hT0 hT1 hT2 _ _ _
    have hf := hexpect θ (fun X => rateY d s k β N θ X ^ 2)
      ((hYc θ).measurable.pow_const 2)
    beta_reduce at hf
    unfold rateVarN
    rw [hf, hint, hM]
    field_simp
    ring
  -- the third-cumulant identity
  have hK3 : ∀ θ : ℝ, Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N) =
      (1 / (N : ℝ)) * (respA k gm β N 3 θ / respA k gm β N 0 θ -
        3 * (respA k gm β N 1 θ / respA k gm β N 0 θ) * (respA k gm β N 2 θ / respA k gm β N 0 θ) +
        2 * (respA k gm β N 1 θ / respA k gm β N 0 θ) * (respA k gm β N 1 θ / respA k gm β N 0 θ) *
          (respA k gm β N 1 θ / respA k gm β N 0 θ)) := by
    intro θ
    have hZ : 0 < respA k gm β N 0 θ := resp_respA_zero_pos k gm hgm_m hβ hc hgc hNpos θ
    have hZne : respA k gm β N 0 θ ≠ 0 := hZ.ne'
    have hM := hK1 θ
    have hT0 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 0 θ
    have hT1 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 1 θ
    have hT2 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 2 θ
    have hT3 := resp_integrable_term k gm hgm_m β hβ hc hgc hNpos 3 θ
    have hpt : ∀ X : Fin N → Torus d,
        Real.sqrt N * (Real.exp (θ * respS k X) * respW gm β X * rateY d s k β N θ X ^ 3) =
          (1 / (N : ℝ)) * ((respS k X ^ 3 * respW gm β X) * Real.exp (θ * respS k X)) -
            3 * rateMeanN d s k β N θ * ((respS k X ^ 2 * respW gm β X) * Real.exp (θ * respS k X)) +
            3 * (N : ℝ) * rateMeanN d s k β N θ ^ 2 *
              ((respS k X ^ 1 * respW gm β X) * Real.exp (θ * respS k X)) -
            (N : ℝ) ^ 2 * rateMeanN d s k β N θ ^ 3 *
              ((respS k X ^ 0 * respW gm β X) * Real.exp (θ * respS k X)) := by
      intro X
      unfold rateY
      rw [hSY θ X]
      have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNr.le
      have h4 : Real.sqrt N ^ 4 = (N : ℝ) ^ 2 := by
        have : Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 := by ring
        rw [this, hsq]
      have e : Real.sqrt N * (Real.exp (θ * respS k X) * respW gm β X *
          (Real.sqrt N * (1 / (N : ℝ) * respS k X - rateMeanN d s k β N θ)) ^ 3) =
          Real.exp (θ * respS k X) * respW gm β X * (Real.sqrt N ^ 4) *
            (1 / (N : ℝ) * respS k X - rateMeanN d s k β N θ) ^ 3 := by ring
      rw [e, h4]
      field_simp
      ring
    have hI : Real.sqrt N * ∫ X, Real.exp (θ * respS k X) * respW gm β X * rateY d s k β N θ X ^ 3
        ∂(volume : Measure (Fin N → Torus d)) =
        (1 / (N : ℝ)) * respA k gm β N 3 θ - 3 * rateMeanN d s k β N θ * respA k gm β N 2 θ +
          3 * (N : ℝ) * rateMeanN d s k β N θ ^ 2 * respA k gm β N 1 θ -
          (N : ℝ) ^ 2 * rateMeanN d s k β N θ ^ 3 * respA k gm β N 0 θ := by
      rw [← integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact resp_integral_comb4 _ _ _ _ _ hT0 hT1 hT2 hT3 _ _ _ _
    have hf := hexpect θ (fun X => rateY d s k β N θ X ^ 3)
      ((hYc θ).measurable.pow_const 3)
    beta_reduce at hf
    rw [hf]
    have e1 : Real.sqrt N * ((respA k gm β N 0 θ)⁻¹ *
        ∫ X, Real.exp (θ * respS k X) * respW gm β X * rateY d s k β N θ X ^ 3
          ∂(volume : Measure (Fin N → Torus d))) =
        (respA k gm β N 0 θ)⁻¹ * (Real.sqrt N *
          ∫ X, Real.exp (θ * respS k X) * respW gm β X * rateY d s k β N θ X ^ 3
            ∂(volume : Measure (Fin N → Torus d))) := by ring
    rw [e1, hI, hM]
    field_simp
    ring
  -- smoothness and derivatives
  have hA0c := resp_respA_contDiff k gm hgm_m hβ hc hgc hNpos 0
  have hA1c := resp_respA_contDiff k gm hgm_m hβ hc hgc hNpos 1
  have hA2c := resp_respA_contDiff k gm hgm_m hβ hc hgc hNpos 2
  have hZne : ∀ θ : ℝ, respA k gm β N 0 θ ≠ 0 := fun θ =>
    (resp_respA_zero_pos k gm hgm_m hβ hc hgc hNpos θ).ne'
  have hfunM : rateMeanN d s k β N = fun θ => respA k gm β N 1 θ / ((N : ℝ) * respA k gm β N 0 θ) :=
    funext hK1
  have hfunV : rateVarN d s k β N = fun θ => (1 / (N : ℝ)) *
      (respA k gm β N 2 θ / respA k gm β N 0 θ -
        respA k gm β N 1 θ / respA k gm β N 0 θ * (respA k gm β N 1 θ / respA k gm β N 0 θ)) :=
    funext hK2
  have cdM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rateMeanN d s k β N) := by
    rw [hfunM]
    exact hA1c.div (contDiff_const.mul hA0c) (fun θ => mul_ne_zero hNne (hZne θ))
  have cdV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rateVarN d s k β N) := by
    rw [hfunV]
    exact contDiff_const.mul ((hA2c.div hA0c (fun θ => hZne θ)).sub
      ((hA1c.div hA0c (fun θ => hZne θ)).mul (hA1c.div hA0c (fun θ => hZne θ))))
  have hdA0 : ∀ θ : ℝ, HasDerivAt (fun t => respA k gm β N 0 t) (respA k gm β N 1 θ) θ :=
    fun θ => resp_respA_hasDerivAt k gm hgm_m hβ hc hgc hNpos 0 θ
  have hdA1 : ∀ θ : ℝ, HasDerivAt (fun t => respA k gm β N 1 t) (respA k gm β N 2 θ) θ :=
    fun θ => resp_respA_hasDerivAt k gm hgm_m hβ hc hgc hNpos 1 θ
  have hdA2 : ∀ θ : ℝ, HasDerivAt (fun t => respA k gm β N 2 t) (respA k gm β N 3 θ) θ :=
    fun θ => resp_respA_hasDerivAt k gm hgm_m hβ hc hgc hNpos 2 θ
  have hMderiv : ∀ θ : ℝ, HasDerivAt (rateMeanN d s k β N) (rateVarN d s k β N θ) θ := by
    intro θ
    rw [hfunM]
    have hd0 : HasDerivAt (fun t => (N : ℝ) * respA k gm β N 0 t) ((N : ℝ) * respA k gm β N 1 θ) θ :=
      (hdA0 θ).const_mul (N : ℝ)
    have h := (hdA1 θ).div hd0 (mul_ne_zero hNne (hZne θ))
    convert h using 1
    rw [hK2 θ]
    field_simp
  have hVderiv : ∀ θ : ℝ, HasDerivAt (rateVarN d s k β N)
      (Real.sqrt N * ∫ X, rateY d s k β N θ X ^ 3 ∂(rateGibbs d s k β θ N)) θ := by
    intro θ
    rw [hfunV, hK3 θ]
    have hq : HasDerivAt (fun t => respA k gm β N 1 t / respA k gm β N 0 t)
        ((respA k gm β N 2 θ * respA k gm β N 0 θ - respA k gm β N 1 θ * respA k gm β N 1 θ) /
          respA k gm β N 0 θ ^ 2) θ := (hdA1 θ).div (hdA0 θ) (hZne θ)
    have hq2 : HasDerivAt (fun t => respA k gm β N 2 t / respA k gm β N 0 t)
        ((respA k gm β N 3 θ * respA k gm β N 0 θ - respA k gm β N 2 θ * respA k gm β N 1 θ) /
          respA k gm β N 0 θ ^ 2) θ := (hdA2 θ).div (hdA0 θ) (hZne θ)
    have hC := (hq2.sub (hq.mul hq)).const_mul (1 / (N : ℝ))
    convert hC using 1
    field_simp
    ring
  exact ⟨cdM, cdV, hMderiv, hVderiv⟩

/-- Lemma 4.19, `V:eq:response-subGaussian` (source lines 5227-5233): for every compact
interval `I = [a, b]` there is `D_I ≥ 2` with
`P_{N,θ}(|Y_{N,θ}| > x) + P(|G_θ| > x) ≤ 4 e^{-x²/(2D_I)}` for `x ≥ 0`, `N ≥ 2`, `θ ∈ I`, where
`G_θ ∼ N(0, C_{β,μ_θ}(φ,φ))`. -/
theorem response_subGaussian (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (a b : ℝ) :
    ∃ D : ℝ, 2 ≤ D ∧ ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc a b,
      rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
          gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
            (Torus.cosMode k) (Torus.cosMode k)).toNNReal {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := by
  sorry

end Rates

end HRS

end
