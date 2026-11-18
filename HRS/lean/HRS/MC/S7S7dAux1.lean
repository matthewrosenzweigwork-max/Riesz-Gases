import HRS.MC.S7WQ

/-!
# Packet `s7_S7d_uniform_limits`, helper 1: uniformity of weak convergence over a bounded Lipschitz class

Plan of the whole packet (file prefix `S7S7d`; this is the analytic core; the particle/Gaussian side follows).

Let `E_r = NegSobolev d r`, `Q_N = sed_Q d s N γ ρ`, `W_N = zetaE r Q_N`, `f_Φ = steinSolG G Φ` for `Φ` in the
`C_b^5` unit ball.  Facts: `‖D^j f_Φ‖ ≤ 1/j` for `1 ≤ j ≤ 5` (`stein_bounds`), so `D^2 f`, `D^3 f`, `D^4 f` are
bounded and `D^3 f, D^4 f` are Lipschitz constants of `D^2 f`, `D^3 f`, uniformly over the ball.

(R2) Write `Y_{kl} = sed_Y Q_N (v_k . grad phi_l)` and `T^{kl}_N(Φ) = E[Y_{kl} D²f(W_N)[ε_k,ε_l]]`,
`L^{kl}(Φ) = Σ_j T_{klj} E D³f(G)[ε_k,ε_l,ε_j]`.  For each fixed `(k,l)`:
  (a) truncate `W_N` to the modes of a finite set `S ∋ k,l` (`‖W - Π_S W‖ ≤ Σ_{m∉S}|W_m|`, `E|W_m| ≤ c ⟨m⟩^{-r}`);
  (b) finite-dimensional core: for the class `{Ψ bounded, Lipschitz}` on `R^p`, `E[Y Ψ(cs_N)]` converges to its
      limit UNIFORMLY (this file: `s7d_uniform_weak`; coupling with the `W_2` convergence from `WQ`, the `4`th
      moments of `Y, cs_N` from `S7b`/`B7`, joint weak convergence from `sed_B10b_clt` for the family `(w, phi_κ)`),
      the pointwise limit being identified by `sed_B13b_linear_limit` (uniqueness of limits);
  (c) the Gaussian side: `law (coordinates of G) = N(0, sed_Cmat)`, `D³f(Π_S G) → D³f(G)` with `‖D⁴f‖ ≤ 1/4`,
      tails in `j` from `|T_{klj}| ≤ C b_k b_l b_j`.
  Then the double sum over `(k,l)` is split into the finite block `S×S` (finitely many pairs, each `≤ ε`) and the
  tail, dominated by `C Σ_{(k,l) ∉ S×S} b_k b_l` uniformly in `N` and `Φ`.
(R3) identical with `B_k` (S7b(ii), `0 < γ`), `sed_B9a_quadratic_limit_lin_proof` for the joint weak convergence of
  `(B_N, cs_N)`, `sed_B13c_chaos_limit_proof` for the identification and `|Q_{k;lj}| ≤ C b_k b_l b_j`.

This file: for a sequence `μ_N → ν` weakly in a separable Banach space with uniformly bounded fourth moments and a
continuous linear functional `h`, `∫ h Ψ dμ_N → ∫ h Ψ dν` uniformly over `{|Ψ| ≤ M, Ψ L-Lipschitz}`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.MC.Sec7.WQ

section Coupling

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]

theorem s7d_coupling_prob {π : Measure (B × B)} {μ ν : Measure B} [IsProbabilityMeasure μ]
    (hπ : IsCoupling π μ ν) : IsProbabilityMeasure π := by
  refine ⟨?_⟩
  have := congrArg (fun m : Measure B => m Set.univ) hπ.1
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at this
  rw [this]
  exact measure_univ

theorem s7d_pointwise {a b D η Ψ1 Ψ2 M κ : ℝ} {L : ℝ} (hη : 0 < η) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hab : |a - b| ≤ κ * D) (h1 : |Ψ1| ≤ M) (h2 : |Ψ1 - Ψ2| ≤ L * D) :
    |a * Ψ1 - b * Ψ2| ≤ (M * κ * η / 2) + ((M * κ + L) / (2 * η)) * D ^ 2 + (L * η / 2) * b ^ 2 := by
  have e : a * Ψ1 - b * Ψ2 = (a - b) * Ψ1 + b * (Ψ1 - Ψ2) := by ring
  have h3 : |a * Ψ1 - b * Ψ2| ≤ M * κ * D + L * (|b| * D) := by
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 : |a - b| * |Ψ1| ≤ (κ * D) * M :=
      mul_le_mul hab h1 (abs_nonneg _) (by positivity)
    have t2 : |b| * |Ψ1 - Ψ2| ≤ |b| * (L * D) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    nlinarith
  have k1 : D ≤ η / 2 + D ^ 2 / (2 * η) := by
    have : 2 * η * D ≤ η ^ 2 + D ^ 2 := by nlinarith [sq_nonneg (D - η)]
    have h2η : 0 < 2 * η := by positivity
    calc D = (2 * η * D) / (2 * η) := by field_simp
      _ ≤ (η ^ 2 + D ^ 2) / (2 * η) := div_le_div_of_nonneg_right this h2η.le
      _ = η / 2 + D ^ 2 / (2 * η) := by field_simp
  have k2 : |b| * D ≤ η * b ^ 2 / 2 + D ^ 2 / (2 * η) := by
    have : 2 * η * (|b| * D) ≤ η ^ 2 * b ^ 2 + D ^ 2 := by
      nlinarith [sq_nonneg (η * |b| - D), sq_abs b]
    have h2η : 0 < 2 * η := by positivity
    calc |b| * D = (2 * η * (|b| * D)) / (2 * η) := by field_simp
      _ ≤ (η ^ 2 * b ^ 2 + D ^ 2) / (2 * η) := div_le_div_of_nonneg_right this h2η.le
      _ = η * b ^ 2 / 2 + D ^ 2 / (2 * η) := by field_simp
  calc |a * Ψ1 - b * Ψ2| ≤ M * κ * D + L * (|b| * D) := h3
    _ ≤ M * κ * (η / 2 + D ^ 2 / (2 * η)) + L * (η * b ^ 2 / 2 + D ^ 2 / (2 * η)) := by
        gcongr
    _ = _ := by field_simp; ring

theorem s7d_transfer_bound {μ ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {π : Measure (B × B)} (hπ : IsCoupling π μ ν) (h : B →L[ℝ] ℝ) {M : ℝ} (L : ℝ≥0)
    (hμ2 : Integrable (fun x : B => h x ^ 2) μ) (hν2 : Integrable (fun x : B => h x ^ 2) ν)
    {Cν : ℝ} (hCν : ∫ x, h x ^ 2 ∂ν ≤ Cν) {η : ℝ} (hη : 0 < η)
    (hcost : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ η ^ 2)
    (hcostI : Integrable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π)
    {Ψ : B → ℝ} (hΨb : ∀ x, |Ψ x| ≤ M) (hΨL : LipschitzWith L Ψ) :
    |∫ x, h x * Ψ x ∂μ - ∫ x, h x * Ψ x ∂ν| ≤ η * (M * ‖h‖ + L * (Cν + 1) / 2) := by
  haveI := s7d_coupling_prob hπ
  have hΨc : Continuous Ψ := hΨL.continuous
  have hhc : Continuous h := h.continuous
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΨb 0)
  have hmeas : AEStronglyMeasurable (fun x => h x * Ψ x) μ := (hhc.mul hΨc).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun x => h x * Ψ x) ν := (hhc.mul hΨc).aestronglyMeasurable
  have hint : ∀ (ξ : Measure B) [IsFiniteMeasure ξ], Integrable (fun x => h x ^ 2) ξ →
      Integrable (fun x => h x * Ψ x) ξ := by
    intro ξ _ hξ
    refine Integrable.mono' ((integrable_const M).add (hξ.const_mul M))
      (hhc.mul hΨc).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have : |h x| ≤ 1 + h x ^ 2 := by nlinarith [sq_abs (h x), abs_nonneg (h x), sq_nonneg (|h x| - 1)]
    calc |h x| * |Ψ x| ≤ (1 + h x ^ 2) * M := mul_le_mul this (hΨb x) (abs_nonneg _) (by positivity)
      _ = M + M * h x ^ 2 := by ring
  have e1 : ∫ x, h x * Ψ x ∂μ = ∫ z, h z.1 * Ψ z.1 ∂π := by
    have := integral_map (μ := π) (φ := Prod.fst) measurable_fst.aemeasurable
      (f := fun x => h x * Ψ x) (by rw [hπ.1]; exact hmeas)
    rw [hπ.1] at this
    exact this
  have e2 : ∫ x, h x * Ψ x ∂ν = ∫ z, h z.2 * Ψ z.2 ∂π := by
    have := integral_map (μ := π) (φ := Prod.snd) measurable_snd.aemeasurable
      (f := fun x => h x * Ψ x) (by rw [hπ.2]; exact hmeas')
    rw [hπ.2] at this
    exact this
  have hi1 : Integrable (fun z : B × B => h z.1 * Ψ z.1) π := by
    have := hint μ hμ2
    rw [← hπ.1] at this
    exact (integrable_map_measure (by rw [hπ.1]; exact hmeas) measurable_fst.aemeasurable).1 this
  have hi2 : Integrable (fun z : B × B => h z.2 * Ψ z.2) π := by
    have := hint ν hν2
    rw [← hπ.2] at this
    exact (integrable_map_measure (by rw [hπ.2]; exact hmeas') measurable_snd.aemeasurable).1 this
  have hh2 : Integrable (fun z : B × B => h z.2 ^ 2) π := by
    have := hν2
    rw [← hπ.2] at this
    exact (integrable_map_measure
      ((hhc.pow 2).aestronglyMeasurable.mono_ac (by rw [hπ.2])) measurable_snd.aemeasurable).1 this
  have hh2int : ∫ z, h z.2 ^ 2 ∂π = ∫ x, h x ^ 2 ∂ν := by
    have := integral_map (μ := π) (φ := Prod.snd) measurable_snd.aemeasurable
      (f := fun x => h x ^ 2) (by rw [hπ.2]; exact (hhc.pow 2).aestronglyMeasurable)
    rw [hπ.2] at this
    exact this.symm
  rw [e1, e2, ← integral_sub hi1 hi2]
  set c1 : ℝ := M * ‖h‖ * η / 2 with hc1
  set c2 : ℝ := (M * ‖h‖ + L) / (2 * η) with hc2
  set c3 : ℝ := L * η / 2 with hc3
  have hc2' : 0 ≤ c2 := by positivity
  have hc3' : 0 ≤ c3 := by positivity
  have hg : Integrable (fun z : B × B => c1 + c2 * ‖z.1 - z.2‖ ^ 2 + c3 * h z.2 ^ 2) π :=
    ((integrable_const c1).add (hcostI.const_mul c2)).add (hh2.const_mul c3)
  have hbd : ‖∫ z : B × B, (h z.1 * Ψ z.1 - h z.2 * Ψ z.2) ∂π‖ ≤
      ∫ z : B × B, (c1 + c2 * ‖z.1 - z.2‖ ^ 2 + c3 * h z.2 ^ 2) ∂π := by
    refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    have hab : |h z.1 - h z.2| ≤ ‖h‖ * ‖z.1 - z.2‖ := by
      have t := h.le_opNorm (z.1 - z.2)
      rw [map_sub, Real.norm_eq_abs] at t
      exact t
    have hlip : |Ψ z.1 - Ψ z.2| ≤ L * ‖z.1 - z.2‖ := by
      have := hΨL.dist_le_mul z.1 z.2
      rwa [Real.dist_eq, dist_eq_norm] at this
    exact s7d_pointwise hη (norm_nonneg _) hM (norm_nonneg _) L.2 hab (hΨb _) hlip
  have hval : ∫ z : B × B, (c1 + c2 * ‖z.1 - z.2‖ ^ 2 + c3 * h z.2 ^ 2) ∂π =
      c1 + c2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π + c3 * ∫ z, h z.2 ^ 2 ∂π := by
    have h12 : Integrable (fun z : B × B => c1 + c2 * ‖z.1 - z.2‖ ^ 2) π :=
      (integrable_const c1).add (hcostI.const_mul c2)
    rw [integral_add (f := fun z : B × B => c1 + c2 * ‖z.1 - z.2‖ ^ 2)
        (g := fun z : B × B => c3 * h z.2 ^ 2) h12 (hh2.const_mul c3),
      integral_add (f := fun _ : B × B => c1) (g := fun z : B × B => c2 * ‖z.1 - z.2‖ ^ 2)
        (integrable_const c1) (hcostI.const_mul c2)]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
  rw [Real.norm_eq_abs] at hbd
  refine hbd.trans ?_
  rw [hval, hh2int]
  have t2 : c2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ c2 * η ^ 2 := mul_le_mul_of_nonneg_left hcost hc2'
  have t3 : c3 * ∫ x, h x ^ 2 ∂ν ≤ c3 * Cν := mul_le_mul_of_nonneg_left hCν hc3'
  calc c1 + c2 * ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π + c3 * ∫ x, h x ^ 2 ∂ν ≤ c1 + c2 * η ^ 2 + c3 * Cν := by
        linarith
    _ = η * (M * ‖h‖ + L * (Cν + 1) / 2) := by
        rw [hc1, hc2, hc3]; field_simp; ring

end Coupling

section Uniform

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem s7d_rpow_four (x : ℝ) : x ^ ((2 : ℝ) + 2) = x ^ 4 := by
  have : ((2 : ℝ) + 2) = ((4 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_natCast]

theorem s7d_uniform_weak (μ : ℕ → Measure B) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (hweak : ∀ F : B → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun N => ∫ x, F x ∂(μ N)) atTop (𝓝 (∫ x, F x ∂ν)))
    {C4 : ℝ} (hmom : ∀ N, Integrable (fun x : B => ‖x‖ ^ ((2 : ℝ) + 2)) (μ N) ∧
      ∫ x, ‖x‖ ^ ((2 : ℝ) + 2) ∂(μ N) ≤ C4)
    (h : B →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Ψ : B → ℝ, (∀ x, |Ψ x| ≤ M) → LipschitzWith L Ψ →
      |∫ x, h x * Ψ x ∂(μ N) - ∫ x, h x * Ψ x ∂ν| ≤ ε := by
  have hW := HRS.MC.Sec7.WQ.s7_WQ_weak_ui_wasserstein_proof μ ν hweak 2 2 (by norm_num) (by norm_num)
    ⟨C4, hmom⟩
  obtain ⟨hνi, hνC⟩ := wq_limit_moment (r := (2 : ℝ) + 2) (by norm_num) μ ν hweak
    (fun N => hmom N)
  simp only [s7d_rpow_four] at hνi hνC hmom
  have hC4 : 0 ≤ C4 := (integral_nonneg fun x => by positivity).trans (hmom 0).2
  set κ : ℝ := ‖h‖ with hκ
  have hκ0 : 0 ≤ κ := norm_nonneg _
  -- second moments of `h`
  have hh2 : ∀ x : B, h x ^ 2 ≤ κ ^ 2 * (1 + ‖x‖ ^ 4) := fun x => by
    have h1 : |h x| ≤ κ * ‖x‖ := by
      have := h.le_opNorm x
      simpa [Real.norm_eq_abs] using this
    have h2 : h x ^ 2 ≤ (κ * ‖x‖) ^ 2 := by
      rw [← sq_abs (h x)]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 4 := by nlinarith [sq_nonneg (‖x‖ ^ 2 - 1), sq_nonneg ‖x‖]
    calc h x ^ 2 ≤ (κ * ‖x‖) ^ 2 := h2
      _ = κ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ κ ^ 2 * (1 + ‖x‖ ^ 4) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have hint2 : ∀ (ξ : Measure B) [IsFiniteMeasure ξ], Integrable (fun x : B => ‖x‖ ^ 4) ξ →
      Integrable (fun x : B => h x ^ 2) ξ := fun ξ _ hξ =>
    Integrable.mono' ((integrable_const 1 |>.add hξ).const_mul (κ ^ 2))
      (h.continuous.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hh2 x)
  have hbd2 : ∀ (ξ : Measure B) [IsProbabilityMeasure ξ], Integrable (fun x : B => ‖x‖ ^ 4) ξ →
      ∀ C : ℝ, ∫ x, ‖x‖ ^ 4 ∂ξ ≤ C → ∫ x, h x ^ 2 ∂ξ ≤ κ ^ 2 * (1 + C) := by
    intro ξ _ hξ C hC
    calc ∫ x, h x ^ 2 ∂ξ ≤ ∫ x, κ ^ 2 * (1 + ‖x‖ ^ 4) ∂ξ :=
          integral_mono (hint2 ξ hξ) ((integrable_const 1 |>.add hξ).const_mul (κ ^ 2))
            (fun x => hh2 x)
      _ = κ ^ 2 * (1 + ∫ x, ‖x‖ ^ 4 ∂ξ) := by
          rw [integral_const_mul, integral_add (integrable_const 1) hξ]; simp
      _ ≤ κ ^ 2 * (1 + C) := by gcongr
  set Cν : ℝ := κ ^ 2 * (1 + C4) with hCν
  have hCνν : ∫ x, h x ^ 2 ∂ν ≤ Cν := hbd2 ν hνi C4 hνC
  have hCν0 : 0 ≤ Cν := by positivity
  set K : ℝ := M * κ + L * (Cν + 1) / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set η : ℝ := ε / (K + 1) with hη
  have hηpos : 0 < η := by positivity
  have hev : ∀ᶠ N in atTop, wassersteinE 2 (μ N) ν < ENNReal.ofReal η :=
    hW.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hηpos))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN Ψ hΨb hΨL => ?_⟩
  have hlt := hN₀ N hN
  unfold wassersteinE at hlt
  obtain ⟨π, hπ⟩ := iInf_lt_iff.1 hlt
  have hπc : IsCoupling π.1 (μ N) ν := π.2
  haveI := s7d_coupling_prob hπc
  -- the cost
  have hcostE : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π.1 < ENNReal.ofReal (η ^ 2) := by
    have h1 : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π.1) ^ (1 / (2 : ℝ)) <
        ENNReal.ofReal η := hπ
    have h2 := ENNReal.rpow_lt_rpow h1 (show (0 : ℝ) < 2 by norm_num)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      ENNReal.rpow_one, ENNReal.ofReal_rpow_of_pos hηpos] at h2
    have hrp : ∀ z : B × B, ‖z.1 - z.2‖ ^ (2 : ℝ) = ‖z.1 - z.2‖ ^ 2 := fun z => by
      rw [Real.rpow_two]
    simp only [hrp] at h2
    have : η ^ (2 : ℝ) = η ^ 2 := Real.rpow_two η
    rw [this] at h2
    exact h2
  have hcostm : AEMeasurable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π.1 :=
    (((continuous_fst.sub continuous_snd).norm.pow 2).measurable).aemeasurable
  have hcostI : Integrable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π.1 := by
    refine ⟨hcostm.aestronglyMeasurable, ?_⟩
    have := (hasFiniteIntegral_iff_ofReal (μ := π.1) (f := fun z : B × B => ‖z.1 - z.2‖ ^ 2)
      (Eventually.of_forall fun z => by positivity)).2 (hcostE.trans ENNReal.ofReal_lt_top)
    exact this
  have hcost : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π.1 ≤ η ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
      hcostm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hcostE.le
  have hμ2 : Integrable (fun x : B => h x ^ 2) (μ N) := hint2 _ (hmom N).1
  have hν2 : Integrable (fun x : B => h x ^ 2) ν := hint2 _ hνi
  have := s7d_transfer_bound hπc h L hμ2 hν2 hCνν hηpos hcost hcostI hΨb hΨL
  refine this.trans ?_
  rw [← hK, hη]
  have : ε / (K + 1) * K ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  linarith

end Uniform

end HRS.MC.Sec7.S7d

end
