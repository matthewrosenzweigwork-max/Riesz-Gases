import HRS.MP.SelfSimP4Spec
import HRS.Stochastic.Ito
import HRS.Stochastic.EmpiricalIto

/-!
# MP-SSP4FLOW: `p4_flow_hyp` (weak forward equation with non-compact tests, second moments, narrow continuity)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4f_`.  Theorem `p4_flow_hyp_proof`, tied to
`HRS.MP.SelfSimP4.p4_flow_hyp`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

variable {d N : ℕ}

/-! ### Gronwall with forcing and the pathwise moment bound -/

theorem p4f_gronwall_forced {φ f : ℝ → ℝ} {T κ a : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ)
    (hφ : ContinuousOn φ (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T)) (hf0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ f s)
    (h : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ a + ∫ r in (0 : ℝ)..t, (κ * φ r + f r)) :
    ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ Real.exp (κ * t) * (a + ∫ r in (0 : ℝ)..t, f r) := by
  set cl : ℝ → ℝ := fun r => max 0 (min r T) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ r, cl r ∈ Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcle : ∀ r ∈ Icc (0 : ℝ) T, cl r = r := fun r hr => by
    simp only [hcl]; rw [min_eq_left hr.2]; exact max_eq_right hr.1
  set φt : ℝ → ℝ := fun r => φ (cl r) with hφt
  set ft : ℝ → ℝ := fun r => f (cl r) with hft
  have hφtc : Continuous φt := hφ.comp_continuous hclc hclm
  have hftc : Continuous ft := hf.comp_continuous hclc hclm
  have hint : ∀ t ∈ Icc (0 : ℝ) T, ∀ (u : ℝ → ℝ) (ut : ℝ → ℝ), (∀ r ∈ Icc (0 : ℝ) T, ut r = u r) →
      ∫ r in (0 : ℝ)..t, ut r = ∫ r in (0 : ℝ)..t, u r := by
    intro t ht u ut hu
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    exact hu r ⟨hr.1, hr.2.trans ht.2⟩
  have hφe : ∀ r ∈ Icc (0 : ℝ) T, φt r = φ r := fun r hr => by simp only [hφt]; rw [hcle r hr]
  have hfe : ∀ r ∈ Icc (0 : ℝ) T, ft r = f r := fun r hr => by simp only [hft]; rw [hcle r hr]
  set G : ℝ → ℝ := fun t => a + ∫ r in (0 : ℝ)..t, (κ * φt r + ft r) with hG
  have hcont : Continuous fun r => κ * φt r + ft r := (continuous_const.mul hφtc).add hftc
  have hGd : ∀ x, HasDerivAt G (κ * φt x + ft x) x := fun x =>
    (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add a
  have hGφ : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ G t := by
    intro t ht
    have h1 := h t ht
    have e : ∫ r in (0 : ℝ)..t, (κ * φt r + ft r) = ∫ r in (0 : ℝ)..t, (κ * φ r + f r) :=
      hint t ht (fun r => κ * φ r + f r) (fun r => κ * φt r + ft r) fun r hr => by
        simp only [hφe r hr, hfe r hr]
    simp only [hG]; rw [e]; exact h1
  set I : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, Real.exp (-κ * s) * ft s with hI
  have hIc : Continuous fun s => Real.exp (-κ * s) * ft s :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hftc
  have hId : ∀ x, HasDerivAt I (Real.exp (-κ * x) * ft x) x := fun x =>
    (hIc.integral_hasStrictDerivAt 0 x).hasDerivAt
  set H : ℝ → ℝ := fun x => Real.exp (-κ * x) * G x - I x with hH
  have hHd : ∀ x, HasDerivAt H (Real.exp (-κ * x) * (κ * (φt x - G x))) x := fun x => by
    have h1 : HasDerivAt (fun x => Real.exp (-κ * x)) (Real.exp (-κ * x) * (-κ)) x := by
      have := ((hasDerivAt_id x).const_mul (-κ)).exp
      simpa [mul_comm] using this
    have h2 := (h1.mul (hGd x)).sub (hId x)
    convert h2 using 1
    ring
  have hanti : AntitoneOn H (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (fun x _ => (hHd x).continuousAt.continuousWithinAt)
      (fun x _ => (hHd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hHd x).deriv]
    have hx' : x ∈ Icc (0 : ℝ) T := interior_subset hx
    have := hGφ x hx'
    rw [hφe x hx'] at *
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (mul_nonpos_of_nonneg_of_nonpos hκ (by linarith))
  intro t ht
  have h0 : H 0 = a := by simp [hH, hG, hI]
  have h1 : H t ≤ H 0 := hanti ⟨le_rfl, hT⟩ ht ht.1
  rw [h0] at h1
  have hI_le : I t ≤ ∫ r in (0 : ℝ)..t, f r := by
    have e : ∫ r in (0 : ℝ)..t, f r = ∫ r in (0 : ℝ)..t, ft r :=
      (hint t ht f ft fun r hr => hfe r hr).symm
    rw [e]
    refine intervalIntegral.integral_mono_on ht.1 ?_ ?_ fun s hs => ?_
    · exact (hIc.intervalIntegrable 0 t)
    · exact hftc.intervalIntegrable 0 t
    · have : Real.exp (-κ * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hs.1])
      have h3 : 0 ≤ ft s := by
        rw [hfe s ⟨hs.1, hs.2.trans ht.2⟩]; exact hf0 s ⟨hs.1, hs.2.trans ht.2⟩
      nlinarith
  have h2 : Real.exp (-κ * t) * G t ≤ a + ∫ r in (0 : ℝ)..t, f r := by
    simp only [hH] at h1; linarith
  have h3 : G t ≤ Real.exp (κ * t) * (a + ∫ r in (0 : ℝ)..t, f r) := by
    have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (κ * t)).le
    rw [← mul_assoc, ← Real.exp_add, show κ * t + -κ * t = 0 by ring, Real.exp_zero, one_mul] at this
    exact this
  exact (hGφ t ht).trans h3

theorem p4f_cs_time {n : ℝ → ℝ} (hn : Continuous n) {T : ℝ} (hT : 0 < T) :
    (∫ s in (0 : ℝ)..T, n s) ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, n s ^ 2 := by
  set I := ∫ s in (0 : ℝ)..T, n s with hI
  set J := ∫ s in (0 : ℝ)..T, n s ^ 2 with hJ
  set c := I / T with hc
  have h0 : 0 ≤ ∫ s in (0 : ℝ)..T, (n s - c) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le fun s _ => sq_nonneg _
  have hi1 : IntervalIntegrable (fun s => n s ^ 2) volume 0 T := (hn.pow 2).intervalIntegrable 0 T
  have hi2 : IntervalIntegrable (fun s => 2 * c * n s) volume 0 T :=
    (continuous_const.mul hn).intervalIntegrable 0 T
  have hi3 : IntervalIntegrable (fun _ : ℝ => c ^ 2) volume 0 T := intervalIntegrable_const
  have e : ∫ s in (0 : ℝ)..T, (n s - c) ^ 2 = J - 2 * c * I + c ^ 2 * T := by
    have : ∀ s, (n s - c) ^ 2 = (n s ^ 2 - 2 * c * n s) + c ^ 2 := fun s => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul]
    simp [hJ, hI, mul_comm]
  rw [e] at h0
  have : c * T = I := by rw [hc]; field_simp
  have h2 : 2 * c * I = 2 * c ^ 2 * T := by rw [← this]; ring
  nlinarith [this]

/-- Pathwise moment bound for `Z_t = Z_0 + ∫_0^t B(s, Z_s) ds + σ' n_t` with `‖B(s,z)‖ ≤ a₀ + b‖z‖`. -/
theorem p4f_pathwise_moment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Z Nz : ℝ → E} {B : ℝ → E → E} (hZc : Continuous Z) (hNc : Continuous Nz) {σ' a₀ b : ℝ}
    (hσ : 0 ≤ σ') (ha₀ : 0 ≤ a₀) (hb : 0 ≤ b) {T : ℝ} (hT : 0 ≤ T)
    (hB : Continuous (Function.uncurry B))
    (hBb : ∀ s ∈ Icc (0 : ℝ) T, ∀ z, ‖B s z‖ ≤ a₀ + b * ‖z‖)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T, Z t = Z 0 + (∫ s in Icc (0 : ℝ) t, B s (Z s)) + σ' • Nz t) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖Z t‖ ≤ Real.exp (b * T) * (‖Z 0‖ + a₀ * T +
      b * σ' * ∫ s in (0 : ℝ)..T, ‖Nz s‖) + σ' * ‖Nz t‖ := by
  set n : ℝ → ℝ := fun s => ‖Nz s‖ with hn
  set φ : ℝ → ℝ := fun t => ‖Z t - σ' • Nz t‖ with hφ
  have hnc : Continuous n := hNc.norm
  have hφc : Continuous φ := (hZc.sub (hNc.const_smul σ')).norm
  have hn0 : ∀ s, 0 ≤ n s := fun s => norm_nonneg _
  have hsplit : ∀ t, ‖Z t‖ ≤ φ t + σ' * n t := fun t => by
    have : Z t = (Z t - σ' • Nz t) + σ' • Nz t := by abel
    calc ‖Z t‖ = ‖(Z t - σ' • Nz t) + σ' • Nz t‖ := by rw [← this]
      _ ≤ ‖Z t - σ' • Nz t‖ + ‖σ' • Nz t‖ := norm_add_le _ _
      _ = φ t + σ' * n t := by rw [norm_smul, Real.norm_of_nonneg hσ]
  have hBZ : Continuous fun s => B s (Z s) := hB.comp (continuous_id.prodMk hZc)
  have hineq : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ ‖Z 0‖ +
      ∫ r in (0 : ℝ)..t, (b * φ r + (a₀ + b * σ' * n r)) := by
    intro t ht
    have h1 : Z t - σ' • Nz t = Z 0 + ∫ s in Icc (0 : ℝ) t, B s (Z s) := by
      rw [hZeq t ht]; abel
    have h3 : φ t ≤ ‖Z 0‖ + ∫ s in Icc (0 : ℝ) t, ‖B s (Z s)‖ := by
      simp only [hφ]
      rw [h1]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_integral_le_integral_norm _))
    have h4 : ∫ s in Icc (0 : ℝ) t, ‖B s (Z s)‖ ≤
        ∫ s in Icc (0 : ℝ) t, (b * φ s + (a₀ + b * σ' * n s)) := by
      refine setIntegral_mono_on (hBZ.norm.integrableOn_Icc)
        ((((continuous_const.mul hφc).add (continuous_const.add (continuous_const.mul hnc)))).integrableOn_Icc)
        measurableSet_Icc fun s hs => ?_
      calc ‖B s (Z s)‖ ≤ a₀ + b * ‖Z s‖ := hBb s ⟨hs.1, hs.2.trans ht.2⟩ _
        _ ≤ a₀ + b * (φ s + σ' * n s) := by
            have := hsplit s
            nlinarith [mul_le_mul_of_nonneg_left this hb]
        _ = b * φ s + (a₀ + b * σ' * n s) := by ring
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    linarith
  have hf0 : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a₀ + b * σ' * n s := fun s _ => by
    have := hn0 s; positivity
  have hg := p4f_gronwall_forced (φ := φ) (f := fun s => a₀ + b * σ' * n s) hT hb hφc.continuousOn
    (continuous_const.add (continuous_const.mul hnc)).continuousOn hf0 hineq
  intro t ht
  refine (hsplit t).trans ?_
  have h5 := hg t ht
  have h6 : ∫ r in (0 : ℝ)..t, (a₀ + b * σ' * n r) = a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r := by
    have hc : Continuous fun r => b * σ' * n r := continuous_const.mul hnc
    rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable 0 t),
      intervalIntegral.integral_const_mul]
    simp [mul_comm]
  rw [h6] at h5
  have h7 : ∫ r in (0 : ℝ)..t, n r ≤ ∫ r in (0 : ℝ)..T, n r := by
    have h8 := intervalIntegral.integral_add_adjacent_intervals
      (hnc.intervalIntegrable (μ := volume) 0 t) (hnc.intervalIntegrable (μ := volume) t T)
    have h9 : 0 ≤ ∫ r in t..T, n r := intervalIntegral.integral_nonneg ht.2 (fun s _ => hn0 s)
    linarith
  have hI0 : 0 ≤ ∫ r in (0 : ℝ)..t, n r := intervalIntegral.integral_nonneg ht.1 (fun s _ => hn0 s)
  have hA : 0 ≤ ‖Z 0‖ + (a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r) := by
    have := ht.1; positivity
  have hAle : ‖Z 0‖ + (a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r) ≤
      ‖Z 0‖ + a₀ * T + b * σ' * ∫ r in (0 : ℝ)..T, n r := by
    have h10 : a₀ * t ≤ a₀ * T := mul_le_mul_of_nonneg_left ht.2 ha₀
    have h11 : b * σ' * ∫ r in (0 : ℝ)..t, n r ≤ b * σ' * ∫ r in (0 : ℝ)..T, n r :=
      mul_le_mul_of_nonneg_left h7 (mul_nonneg hb hσ)
    linarith
  have hexp : Real.exp (b * t) ≤ Real.exp (b * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hb)
  have h12 : Real.exp (b * t) * (‖Z 0‖ + (a₀ * t + b * σ' * ∫ r in (0 : ℝ)..t, n r)) ≤
      Real.exp (b * T) * (‖Z 0‖ + a₀ * T + b * σ' * ∫ r in (0 : ℝ)..T, n r) :=
    mul_le_mul hexp hAle hA (Real.exp_pos _).le
  have h13 : φ t ≤ Real.exp (b * T) * (‖Z 0‖ + a₀ * T + b * σ' * ∫ r in (0 : ℝ)..T, n r) :=
    h5.trans h12
  show _ ≤ _ + σ' * n t
  linarith


/-! ### The integrated equation in vector form -/

/-- The noise directions `σ_k = √(2ν) e_k`. -/
def p4f_sigma (d N : ℕ) (ν : ℝ) (k : Fin N × Fin d) : EucConfig d N :=
  Real.sqrt (2 * ν) • configBasis d N k

theorem p4f_noise_sum (ν : ℝ) (c : Fin N × Fin d → ℝ) (i : Fin N) (j : Fin d) :
    (∑ k : Fin N × Fin d, c k • p4f_sigma d N ν k) i j = Real.sqrt (2 * ν) * c (i, j) := by
  simp [p4f_sigma, configBasis, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  ring

theorem p4f_basis_sum (c : Fin N × Fin d → ℝ) (i : Fin N) (j : Fin d) :
    (∑ k : Fin N × Fin d, c k • configBasis d N k) i j = c (i, j) := by
  simp [configBasis, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]

theorem p4f_norm_noise_sq (c : Fin N × Fin d → ℝ) :
    ‖∑ k : Fin N × Fin d, c k • configBasis d N k‖ ^ 2 ≤ ∑ k : Fin N × Fin d, c k ^ 2 := by
  set x : EucConfig d N := ∑ k : Fin N × Fin d, c k • configBasis d N k with hx
  have hsum : 0 ≤ ∑ k : Fin N × Fin d, c k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hle : ‖x‖ ≤ Real.sqrt (∑ k : Fin N × Fin d, c k ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [← Real.sqrt_sq (norm_nonneg (x i))]
    refine Real.sqrt_le_sqrt ?_
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    have : ∀ j, x i j = c (i, j) := fun j => p4f_basis_sum c i j
    simp only [this]
    calc ∑ j : Fin d, c (i, j) ^ 2 = ∑ k ∈ (Finset.univ : Finset (Fin d)).map
          ⟨fun j => (i, j), fun a b h => (Prod.mk.inj h).2⟩, c k ^ 2 := by
            rw [Finset.sum_map]; rfl
      _ ≤ ∑ k : Fin N × Fin d, c k ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ k : Fin N × Fin d, c k ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := Real.sq_sqrt hsum

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem p4f_Xeq {P : Measure Ω} {ν S : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : P4AddSol P ν b S ℱ W' W Y) :
    ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ S →
      Y t ζ = Y 0 ζ + (∫ s in Icc (0 : ℝ) t, b ((Real.toNNReal s : ℝ≥0) : ℝ) (Y (Real.toNNReal s) ζ)) +
        ∑ k, (W' t ζ k - W' 0 ζ k) • p4f_sigma d N ν k := by
  filter_upwards [hY.eqn, hY.filtered.coords] with ζ h hc t ht
  obtain ⟨hint, heq⟩ := h t ht
  have hcongr : ∀ i, ∫ s in Icc (0 : ℝ) t, b ((Real.toNNReal s : ℝ≥0) : ℝ) (Y (Real.toNNReal s) ζ) i =
      ∫ s in Icc (0 : ℝ) t, b s (Y (Real.toNNReal s) ζ) i := fun i =>
    setIntegral_congr_fun measurableSet_Icc fun s hs => by
      simp [Real.coe_toNNReal _ hs.1]
  have hint' : ∀ i, Integrable (fun s => b ((Real.toNNReal s : ℝ≥0) : ℝ) (Y (Real.toNNReal s) ζ) i)
      (volume.restrict (Icc (0 : ℝ) t)) := fun i =>
    (hint i).congr_fun (fun s hs => by simp [Real.coe_toNNReal _ hs.1]) measurableSet_Icc
  ext i j
  rw [Pi.add_apply, Pi.add_apply, eval_integral hint' i, hcongr i]
  rw [heq i]
  have hn : ((∑ k : Fin N × Fin d, (W' t ζ k - W' 0 ζ k) • p4f_sigma d N ν k) i).ofLp j =
      Real.sqrt (2 * ν) * (W' t ζ (i, j) - W' 0 ζ (i, j)) :=
    p4f_noise_sum ν (fun k => W' t ζ k - W' 0 ζ k) i j
  simp only [PiLp.add_apply]
  rw [hn]
  simp [hc]


/-! ### Second moments -/

theorem p4f_lint_four {P : Measure Ω} {a b c : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (ha0 : ∀ ζ, 0 ≤ a ζ) (hb0 : ∀ ζ, 0 ≤ b ζ) (hc0 : ∀ ζ, 0 ≤ c ζ)
    {c₁ c₂ c₃ c₄ : ℝ} (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) (h3 : 0 ≤ c₃) (h4 : 0 ≤ c₄) :
    ∫⁻ ζ, ENNReal.ofReal (c₁ * a ζ + c₂ + c₃ * b ζ + c₄ * c ζ) ∂P ≤
      ENNReal.ofReal c₁ * ∫⁻ ζ, ENNReal.ofReal (a ζ) ∂P + ENNReal.ofReal c₂ * P univ +
      ENNReal.ofReal c₃ * ∫⁻ ζ, ENNReal.ofReal (b ζ) ∂P +
      ENNReal.ofReal c₄ * ∫⁻ ζ, ENNReal.ofReal (c ζ) ∂P := by
  have e : ∀ ζ, ENNReal.ofReal (c₁ * a ζ + c₂ + c₃ * b ζ + c₄ * c ζ) =
      ENNReal.ofReal c₁ * ENNReal.ofReal (a ζ) + ENNReal.ofReal c₂ +
      ENNReal.ofReal c₃ * ENNReal.ofReal (b ζ) + ENNReal.ofReal c₄ * ENNReal.ofReal (c ζ) := by
    intro ζ
    have := ha0 ζ; have := hb0 ζ; have := hc0 ζ
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h3, ENNReal.ofReal_mul h4]
  have m1 : Measurable fun ζ => ENNReal.ofReal c₁ * ENNReal.ofReal (a ζ) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp ha)
  have m2 : Measurable fun _ : Ω => ENNReal.ofReal c₂ := measurable_const
  have m3 : Measurable fun ζ => ENNReal.ofReal c₃ * ENNReal.ofReal (b ζ) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp hb)
  have m4 : Measurable fun ζ => ENNReal.ofReal c₄ * ENNReal.ofReal (c ζ) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp hc)
  simp_rw [e]
  rw [lintegral_add_left (f := fun ζ => ENNReal.ofReal c₁ * ENNReal.ofReal (a ζ) + ENNReal.ofReal c₂ +
      ENNReal.ofReal c₃ * ENNReal.ofReal (b ζ)) ((m1.add m2).add m3),
    lintegral_add_left (f := fun ζ => ENNReal.ofReal c₁ * ENNReal.ofReal (a ζ) + ENNReal.ofReal c₂)
      (m1.add m2),
    lintegral_add_left (f := fun ζ => ENNReal.ofReal c₁ * ENNReal.ofReal (a ζ)) m1, lintegral_const_mul (f := fun ζ => ENNReal.ofReal (a ζ)) _ (ENNReal.measurable_ofReal.comp ha),
    lintegral_const, lintegral_const_mul (f := fun ζ => ENNReal.ofReal (b ζ)) _ (ENNReal.measurable_ofReal.comp hb),
    lintegral_const_mul (f := fun ζ => ENNReal.ofReal (c ζ)) _ (ENNReal.measurable_ofReal.comp hc)]

/-- Sum of squares of the coordinates of the Brownian motion at real time `s`. -/
def p4f_q (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (s : ℝ) (ζ : Ω) : ℝ :=
  ∑ k : Fin N × Fin d, (W' (Real.toNNReal s) ζ k) ^ 2

theorem p4f_q_nonneg (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (s : ℝ) (ζ : Ω) :
    0 ≤ p4f_q W' s ζ := Finset.sum_nonneg fun k _ => sq_nonneg _

theorem p4f_continuous_q {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hc : ∀ ζ, Continuous fun t => W' t ζ) (ζ : Ω) : Continuous fun s => p4f_q W' s ζ := by
  unfold p4f_q
  refine continuous_finset_sum _ fun k _ => ?_
  exact (((continuous_apply k).comp (hc ζ)).comp continuous_real_toNNReal).pow 2

theorem p4f_measurable_q {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W') (s : ℝ) :
    Measurable (p4f_q W' s) := by
  unfold p4f_q
  refine Finset.measurable_sum _ fun k _ => ?_
  have h : Measurable (W' (Real.toNNReal s)) := (hW'.adapted _).mono (ℱ.le _) le_rfl
  exact ((measurable_pi_apply k).comp h).pow_const 2

theorem p4f_measurable_q_uncurry {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W') :
    Measurable (Function.uncurry fun (s : ℝ) (ζ : Ω) => p4f_q W' s ζ) :=
  measurable_uncurry_of_continuous_of_measurable (fun ζ => p4f_continuous_q hW'.cont ζ)
    (p4f_measurable_q hW')

theorem p4f_lintegral_q {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W') {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ ζ, ENNReal.ofReal (p4f_q W' s ζ) ∂P = ENNReal.ofReal (Fintype.card (Fin N × Fin d) * s) := by
  have hint : ∀ k : Fin N × Fin d, Integrable (fun ζ => (W' (Real.toNNReal s) ζ k) ^ 2) P := fun k =>
    (hW'.memLp_coord (Real.toNNReal s) k ENNReal.ofNat_ne_top).integrable_sq
  have h1 : Integrable (fun ζ => p4f_q W' s ζ) P := integrable_finset_sum _ fun k _ => hint k
  rw [← ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun ζ => p4f_q_nonneg W' s ζ)]
  congr 1
  unfold p4f_q
  rw [integral_finset_sum _ fun k _ => hint k]
  have : ∀ k : Fin N × Fin d, ∫ ζ, (W' (Real.toNNReal s) ζ k) ^ 2 ∂P = s := fun k => by
    have := (hW'.hasLaw_coord (Real.toNNReal s) k).integral_comp (f := fun x : ℝ => x ^ 2)
      (by fun_prop)
    rw [integral_sq_gaussianReal_zero, Real.coe_toNNReal _ hs] at this
    exact this
  simp [this]


theorem p4f_drift_growth {S : ℝ} {b : ℝ → EucConfig d N → EucConfig d N}
    (hbc : Continuous (Function.uncurry b)) {K : ℝ≥0} (hK : ∀ τ ∈ Icc (0 : ℝ) S, LipschitzWith K (b τ)) :
    ∃ a₀ : ℝ, 0 ≤ a₀ ∧ ∀ s ∈ Icc (0 : ℝ) S, ∀ z, ‖b s z‖ ≤ a₀ + (K : ℝ) * ‖z‖ := by
  obtain ⟨a₁, ha₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn
    (f := fun s => b s 0) (hbc.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨max a₁ 0, le_max_right _ _, fun s hs z => ?_⟩
  have h1 : ‖b s 0‖ ≤ max a₁ 0 := (ha₁ s hs).trans (le_max_left _ _)
  have h2 : ‖b s z - b s 0‖ ≤ K * ‖z‖ := by
    have := (hK s hs).dist_le_mul z 0
    rwa [dist_eq_norm, dist_eq_norm, sub_zero] at this
  calc ‖b s z‖ = ‖b s 0 + (b s z - b s 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖b s 0‖ + ‖b s z - b s 0‖ := norm_add_le _ _
    _ ≤ max a₁ 0 + K * ‖z‖ := add_le_add h1 h2

theorem p4f_real_step {E u v w Z y : ℝ} (hE0 : 0 ≤ E) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hy : 0 ≤ y) (hZ : 0 ≤ Z) (hle : Z ≤ E * (u + v + w) + y) :
    Z ^ 2 ≤ 6 * E ^ 2 * (u ^ 2 + v ^ 2 + w ^ 2) + 2 * y ^ 2 := by
  have hX0 : 0 ≤ E * (u + v + w) := mul_nonneg hE0 (by positivity)
  have hsq3 : (u + v + w) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + w ^ 2) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w)]
  have h1 : Z ^ 2 ≤ (E * (u + v + w) + y) ^ 2 := pow_le_pow_left₀ hZ hle 2
  have h2 : (E * (u + v + w) + y) ^ 2 ≤ 2 * (E * (u + v + w)) ^ 2 + 2 * y ^ 2 := by
    nlinarith [sq_nonneg (E * (u + v + w) - y)]
  have h3 : 2 * (E * (u + v + w)) ^ 2 ≤ 6 * E ^ 2 * (u ^ 2 + v ^ 2 + w ^ 2) := by
    have e : 2 * (E * (u + v + w)) ^ 2 = 2 * E ^ 2 * (u + v + w) ^ 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsq3 (by positivity : (0 : ℝ) ≤ 2 * E ^ 2)
    linarith
  linarith

theorem p4f_moment {P : Measure Ω} [IsProbabilityMeasure P] {ν : ℝ} (hν : 0 ≤ ν) {S : ℝ} (hS : 0 < S)
    {b : ℝ → EucConfig d N → EucConfig d N} (hbc : Continuous (Function.uncurry b))
    (hbl : ∃ K : ℝ≥0, ∀ τ ∈ Icc (0 : ℝ) S, LipschitzWith K (b τ))
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : P4AddSol P ν b S ℱ W' W Y)
    (hm0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (Y 0)) < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) S,
      ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (Y (Real.toNNReal t))) ≤ C := by
  obtain ⟨K, hK⟩ := hbl
  have hbrown := hY.filtered.brownian
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le t) le_rfl
  obtain ⟨a₀, ha₀0, hBb⟩ := p4f_drift_growth hbc hK
  set σ' : ℝ := Real.sqrt (2 * ν) with hσ'
  have hσ0 : 0 ≤ σ' := Real.sqrt_nonneg _
  set E : ℝ := Real.exp (K * S) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set c₁ : ℝ := 6 * E ^ 2 with hc₁
  set c₂ : ℝ := 6 * E ^ 2 * (a₀ * S) ^ 2 with hc₂
  set c₃ : ℝ := 6 * E ^ 2 * (((K : ℝ) * σ') ^ 2 * S) with hc₃
  set c₄ : ℝ := 2 * σ' ^ 2 with hc₄
  have hpath : ∀ᵐ ζ ∂P, ∀ t ∈ Icc (0 : ℝ) S, ‖Y (Real.toNNReal t) ζ‖ ^ 2 ≤
      c₁ * ‖Y 0 ζ‖ ^ 2 + c₂ + c₃ * (∫ s in (0 : ℝ)..S, p4f_q W' s ζ) + c₄ * p4f_q W' t ζ := by
    filter_upwards [p4f_Xeq hY] with ζ hX t ht
    set Z : ℝ → EucConfig d N := fun s => Y (Real.toNNReal s) ζ with hZ
    set Nz : ℝ → EucConfig d N := fun s => ∑ k : Fin N × Fin d,
      W' (Real.toNNReal s) ζ k • configBasis d N k with hNz
    have hZc : Continuous Z := (hY.cont ζ).comp continuous_real_toNNReal
    have hNc : Continuous Nz := by
      refine continuous_finset_sum _ fun k _ => ?_
      exact (((continuous_apply k).comp (hbrown.cont ζ)).comp continuous_real_toNNReal).smul
        continuous_const
    have hZeq : ∀ t ∈ Icc (0 : ℝ) S, Z t = Z 0 + (∫ s in Icc (0 : ℝ) t, b s (Z s)) + σ' • Nz t := by
      intro t ht
      have h := hX (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
      rw [Real.coe_toNNReal _ ht.1] at h
      have hW0 : ∀ k, W' 0 ζ k = 0 := fun k => congrFun (hbrown.zero ζ) k
      have hn : ∑ k, (W' (Real.toNNReal t) ζ k - W' 0 ζ k) • p4f_sigma d N ν k = σ' • Nz t := by
        simp only [hW0, sub_zero, hNz, p4f_sigma, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm]
      have hi : ∫ s in Icc (0 : ℝ) t, b ((Real.toNNReal s : ℝ≥0) : ℝ) (Y (Real.toNNReal s) ζ) =
          ∫ s in Icc (0 : ℝ) t, b s (Z s) :=
        setIntegral_congr_fun measurableSet_Icc fun s hs => by
          simp [hZ, Real.coe_toNNReal _ hs.1]
      rw [hn, hi] at h
      simpa [hZ] using h
    have hmom := p4f_pathwise_moment (Z := Z) (Nz := Nz) (B := b) (a₀ := a₀) (b := (K : ℝ))
      hZc hNc hσ0 ha₀0 K.2 hS.le hbc hBb hZeq t ht
    set J : ℝ := ∫ s in (0 : ℝ)..S, ‖Nz s‖ with hJ
    set Q : ℝ := ∫ s in (0 : ℝ)..S, p4f_q W' s ζ with hQ
    have hNq : ∀ s, ‖Nz s‖ ^ 2 ≤ p4f_q W' s ζ := fun s =>
      p4f_norm_noise_sq (fun k => W' (Real.toNNReal s) ζ k)
    have hJ2 : J ^ 2 ≤ S * Q := by
      refine (p4f_cs_time hNc.norm hS).trans (mul_le_mul_of_nonneg_left ?_ hS.le)
      exact intervalIntegral.integral_mono_on hS.le ((hNc.norm.pow 2).intervalIntegrable 0 S)
        ((p4f_continuous_q hbrown.cont ζ).intervalIntegrable 0 S) fun s _ => hNq s
    have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hS.le fun s _ => norm_nonneg _
    have hu0 : 0 ≤ ‖Y 0 ζ‖ := norm_nonneg _
    set u : ℝ := ‖Y 0 ζ‖ with hu
    set v : ℝ := a₀ * S with hv
    set w : ℝ := (K : ℝ) * σ' * J with hw
    have hv0 : 0 ≤ v := mul_nonneg ha₀0 hS.le
    have hw0 : 0 ≤ w := mul_nonneg (mul_nonneg K.2 hσ0) hJ0
    have hZ0 : Z 0 = Y 0 ζ := by simp [hZ]
    have hZt : Z t = Y (Real.toNNReal t) ζ := rfl
    rw [hZ0] at hmom
    have hy0 : 0 ≤ σ' * ‖Nz t‖ := mul_nonneg hσ0 (norm_nonneg _)
    have hw2 : w ^ 2 ≤ ((K : ℝ) * σ') ^ 2 * (S * Q) := by
      have : w ^ 2 = ((K : ℝ) * σ') ^ 2 * J ^ 2 := by rw [hw]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hJ2 (sq_nonneg _)
    have hy2 : (σ' * ‖Nz t‖) ^ 2 ≤ σ' ^ 2 * p4f_q W' t ζ := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hNq t) (sq_nonneg _)
    have hle : ‖Y (Real.toNNReal t) ζ‖ ≤ E * (u + v + w) + σ' * ‖Nz t‖ := by
      rw [← hZt]; exact hmom
    have h1 := p4f_real_step hE0 hu0 hv0 hw0 hy0 (norm_nonneg _) hle
    have h4 : 6 * E ^ 2 * w ^ 2 ≤ 6 * E ^ 2 * (((K : ℝ) * σ') ^ 2 * (S * Q)) :=
      mul_le_mul_of_nonneg_left hw2 (by positivity)
    have h5 : 2 * (σ' * ‖Nz t‖) ^ 2 ≤ 2 * (σ' ^ 2 * p4f_q W' t ζ) :=
      mul_le_mul_of_nonneg_left hy2 (by norm_num)
    calc ‖Y (Real.toNNReal t) ζ‖ ^ 2 ≤ 6 * E ^ 2 * (u ^ 2 + v ^ 2 + w ^ 2) +
          2 * (σ' * ‖Nz t‖) ^ 2 := h1
      _ ≤ c₁ * u ^ 2 + c₂ + c₃ * Q + c₄ * p4f_q W' t ζ := by
          simp only [hc₁, hc₂, hc₃, hc₄, hv]
          nlinarith [h4, h5]
  -- measurability
  have hqm : ∀ s, Measurable (p4f_q W' s) := p4f_measurable_q hbrown
  have hqu := p4f_measurable_q_uncurry hbrown
  have hQm : Measurable fun ζ => ∫ s in (0 : ℝ)..S, p4f_q W' s ζ := by
    simp_rw [intervalIntegral.integral_of_le hS.le]
    exact ((hqu.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) S))).measurable
  have hQ0 : ∀ ζ, 0 ≤ ∫ s in (0 : ℝ)..S, p4f_q W' s ζ := fun ζ =>
    intervalIntegral.integral_nonneg hS.le fun s _ => p4f_q_nonneg W' s ζ
  set card : ℝ := ((Fintype.card (Fin N × Fin d) : ℕ) : ℝ) with hcard
  have hQeq : ∀ ζ, ENNReal.ofReal (∫ s in (0 : ℝ)..S, p4f_q W' s ζ) =
      ∫⁻ s in Icc (0 : ℝ) S, ENNReal.ofReal (p4f_q W' s ζ) := by
    intro ζ
    rw [intervalIntegral.integral_of_le hS.le, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      ((p4f_continuous_q hbrown.cont ζ).integrableOn_Icc)
      (ae_of_all _ fun s => p4f_q_nonneg W' s ζ)
  have hQint : ∫⁻ ζ, ENNReal.ofReal (∫ s in (0 : ℝ)..S, p4f_q W' s ζ) ∂P ≤
      ENNReal.ofReal (card * S) * ENNReal.ofReal S := by
    simp_rw [hQeq]
    rw [lintegral_lintegral_swap]
    · calc ∫⁻ s in Icc (0 : ℝ) S, ∫⁻ ζ, ENNReal.ofReal (p4f_q W' s ζ) ∂P
          ≤ ∫⁻ s in Icc (0 : ℝ) S, ENNReal.ofReal (card * S) := by
            refine setLIntegral_mono measurable_const fun s hs => ?_
            rw [p4f_lintegral_q hbrown hs.1]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg _))
        _ = ENNReal.ofReal (card * S) * ENNReal.ofReal S := by
            rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    · exact ((ENNReal.measurable_ofReal.comp (hqu.comp measurable_swap)).aemeasurable)
  have hfm : Measurable fun x : EucConfig d N => ENNReal.ofReal (‖x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
  have hl0 : ∫⁻ ζ, ENNReal.ofReal (‖Y 0 ζ‖ ^ 2) ∂P < ⊤ := by
    rw [law, lintegral_map hfm (hYm 0)]
      at hm0
    exact hm0
  have hnm : Measurable fun ζ => ‖Y 0 ζ‖ ^ 2 := (measurable_norm.comp (hYm 0)).pow_const 2
  refine ⟨ENNReal.ofReal c₁ * ∫⁻ ζ, ENNReal.ofReal (‖Y 0 ζ‖ ^ 2) ∂P + ENNReal.ofReal c₂ * P univ +
      ENNReal.ofReal c₃ * (ENNReal.ofReal (card * S) * ENNReal.ofReal S) +
      ENNReal.ofReal c₄ * ENNReal.ofReal (card * S), ?_, fun t ht => ?_⟩
  · simp only [measure_univ, mul_one]
    refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top hl0, ENNReal.ofReal_lt_top⟩, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)⟩,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  · rw [law, lintegral_map hfm (hYm _)]
    calc ∫⁻ ζ, ENNReal.ofReal (‖Y (Real.toNNReal t) ζ‖ ^ 2) ∂P
        ≤ ∫⁻ ζ, ENNReal.ofReal (c₁ * ‖Y 0 ζ‖ ^ 2 + c₂ +
            c₃ * (∫ s in (0 : ℝ)..S, p4f_q W' s ζ) + c₄ * p4f_q W' t ζ) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpath] with ζ hζ
          exact ENNReal.ofReal_le_ofReal (hζ t ht)
      _ ≤ ENNReal.ofReal c₁ * ∫⁻ ζ, ENNReal.ofReal (‖Y 0 ζ‖ ^ 2) ∂P + ENNReal.ofReal c₂ * P univ +
          ENNReal.ofReal c₃ * ∫⁻ ζ, ENNReal.ofReal (∫ s in (0 : ℝ)..S, p4f_q W' s ζ) ∂P +
          ENNReal.ofReal c₄ * ∫⁻ ζ, ENNReal.ofReal (p4f_q W' t ζ) ∂P :=
          p4f_lint_four hnm hQm (hqm t) (fun ζ => sq_nonneg _) hQ0 (fun ζ => p4f_q_nonneg W' t ζ)
            (by positivity) (by positivity) (by positivity) (by positivity)
      _ ≤ _ := by
          rw [p4f_lintegral_q hbrown ht.1]
          refine add_le_add (add_le_add (add_le_add le_rfl le_rfl) (mul_le_mul' le_rfl hQint))
            (mul_le_mul' le_rfl ?_)
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg _))


/-! ### Narrow continuity -/

theorem p4f_narrow {P : Measure Ω} [IsProbabilityMeasure P] {ν S : ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : P4AddSol P ν b S ℱ W' W Y)
    {g : EucConfig d N → ℝ} (hg : Continuous g) (hb : ∃ C : ℝ, ∀ x, |g x| ≤ C) :
    ContinuousOn (fun t : ℝ => ∫ x, g x ∂(law P (Y (Real.toNNReal t)))) (Icc 0 S) := by
  obtain ⟨C, hC⟩ := hb
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le t) le_rfl
  have h := continuousOn_of_dominated (μ := P) (s := Icc (0 : ℝ) S)
    (F := fun (t : ℝ) (ζ : Ω) => g (Y (Real.toNNReal t) ζ)) (bound := fun _ => |C|)
    (fun t _ => (hg.measurable.comp (hYm _)).aestronglyMeasurable)
    (fun t _ => ae_of_all _ fun ζ => by
      rw [Real.norm_eq_abs]; exact (hC _).trans (le_abs_self C))
    (integrable_const _)
    (ae_of_all _ fun ζ => (hg.comp ((hY.cont ζ).comp continuous_real_toNNReal)).continuousOn)
  refine h.congr fun t _ => ?_
  rw [law, integral_map (hYm _).aemeasurable hg.aestronglyMeasurable]


/-! ### The weak forward equation -/

theorem p4f_gen_cont {ν : ℝ} {b : ℝ → EucConfig d N → EucConfig d N}
    (hbc : Continuous (Function.uncurry b)) {g : EucConfig d N → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (fun p : ℝ × EucConfig d N => p4Gen ν b p.1 g p.2) := by
  have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  unfold p4Gen
  refine (continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)).add ?_
  · exact ((h2.comp continuous_snd).clm_apply continuous_const).clm_apply continuous_const
  · exact (h1.comp continuous_snd).clm_apply hbc

theorem p4f_gen_eq {ν : ℝ} (hν : 0 ≤ ν) {b : ℝ → EucConfig d N → EucConfig d N}
    {g : EucConfig d N → ℝ} (r : ℝ) (x : EucConfig d N) :
    p4Gen ν b r g x = fderiv ℝ g x (b r x) +
      (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
        fderiv ℝ (fderiv ℝ g) x (p4f_sigma d N ν k) (p4f_sigma d N ν k) := by
  have h2 : Real.sqrt (2 * ν) * Real.sqrt (2 * ν) = 2 * ν := Real.mul_self_sqrt (by linarith)
  have hσ : ∀ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ g) x (p4f_sigma d N ν k) (p4f_sigma d N ν k) =
      (2 * ν) * fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k) := by
    intro k
    simp only [p4f_sigma, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k)) * h2
  unfold p4Gen
  rw [Finset.sum_congr rfl (fun k _ => hσ k), ← Finset.mul_sum]
  ring

theorem p4f_psiL2 {P : Measure Ω} [IsProbabilityMeasure P] {S : ℝ} {ℱ : Filtration ℝ mΩ}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hprog : IsProgressive ℱ (ofNNRealTime Y))
    {g : EucConfig d N → ℝ} (hg : P4Test g) (σ : Fin N × Fin d → EucConfig d N) :
    IsProgressiveL2 P ℱ
      (itoIntegrand S Set.univ (fun _ x => g x) (ofNNRealTime Y) (fun _ _ => σ)) := by
  obtain ⟨C, hC⟩ := hg.bdd
  have hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ C := fun x =>
    le_trans (by nlinarith [norm_nonneg (fderiv ℝ g x), norm_nonneg x, (hC x).2.1]) (hC x).2.1
  have hk : ∀ k : Fin N × Fin d, IsProgressive ℱ
      (fun s ζ => itoIntegrand S Set.univ (fun _ x => g x) (ofNNRealTime Y) (fun _ _ => σ) s ζ k) := by
    intro k
    have hc : Continuous (fun q : ℝ × EucConfig d N => fderiv ℝ g q.2 (σ k)) :=
      ((hg.smooth.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply continuous_const
    have hm : Measurable (Function.uncurry (fun (s : ℝ) (y : EucConfig d N) =>
        if s ∈ Icc 0 S then fderiv ℝ g y (σ k) else 0)) :=
      Measurable.ite (measurableSet_Icc.preimage measurable_fst) hc.measurable measurable_const
    have h := isProgressive_comp_measurable' (ofNNRealTime Y) hprog
      (fun (s : ℝ) (y : EucConfig d N) => if s ∈ Icc 0 S then fderiv ℝ g y (σ k) else 0) hm
    have e : (fun s ζ => itoIntegrand S Set.univ (fun _ x => g x) (ofNNRealTime Y)
          (fun _ _ => σ) s ζ k) =
        fun s ζ => if s ∈ Icc 0 S then fderiv ℝ g (ofNNRealTime Y s ζ) (σ k) else 0 := by
      funext s ζ
      unfold itoIntegrand
      by_cases hs : s ∈ Icc 0 S
      · simp [Set.indicator, hs]
      · simp [Set.indicator, hs]
    rw [e]
    exact h
  refine IsProgressiveL2.of_bounded P (isProgressive_pi hk)
    (max C 0 * ∑ j : Fin N × Fin d, ‖σ j‖) ?_
  intro s ζ k
  unfold itoIntegrand
  by_cases hs : s ∈ Icc 0 S
  · simp only [Set.indicator, hs, if_true, Set.mem_univ, Set.mem_setOf_eq]
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ g (ofNNRealTime Y s ζ) (σ k)‖
        ≤ ‖fderiv ℝ g (ofNNRealTime Y s ζ)‖ * ‖σ k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max C 0 * ‖σ k‖ :=
          mul_le_mul_of_nonneg_right ((hDg _).trans (le_max_left _ _)) (norm_nonneg _)
      _ ≤ max C 0 * ∑ j : Fin N × Fin d, ‖σ j‖ :=
          mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => norm_nonneg (σ j))
            (Finset.mem_univ k)) (le_max_right _ _)
  · simp only [Set.indicator, hs, if_false, abs_zero]
    exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => norm_nonneg _)

theorem p4f_fp {P : Measure Ω} [IsProbabilityMeasure P] {ν : ℝ} (hν : 0 ≤ ν) {S : ℝ} (hS : 0 < S)
    {b : ℝ → EucConfig d N → EucConfig d N} (hbc : Continuous (Function.uncurry b))
    (hbl : ∃ K : ℝ≥0, ∀ τ ∈ Icc (0 : ℝ) S, LipschitzWith K (b τ))
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : P4AddSol P ν b S ℱ W' W Y)
    {g : EucConfig d N → ℝ} (hg : P4Test g) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    ∫ x, g x ∂(law P (Y (Real.toNNReal t))) = ∫ x, g x ∂(law P (Y (Real.toNNReal 0))) +
      ∫ r in Icc (0 : ℝ) t, ∫ x, p4Gen ν b r g x ∂(law P (Y (Real.toNNReal r))) := by
  have hS0 : 0 ≤ S := hS.le
  obtain ⟨K, hK⟩ := hbl
  obtain ⟨a₀, ha₀0, hBb⟩ := p4f_drift_growth hbc hK
  obtain ⟨C, hC⟩ := hg.bdd
  have hgc : Continuous g := hg.smooth.continuous
  have hbm : Measurable fun p : ℝ × EucConfig d N => b p.1 p.2 := hbc.measurable
  set σ : Fin N × Fin d → EucConfig d N := p4f_sigma d N ν with hσdef
  have hbrown := hY.filtered.brownian
  have hXmeas : ∀ s, Measurable (Y s) := fun s => (hY.filtered.adapted s).mono (ℱ.le s) le_rfl
  set bp : ℝ≥0 → Ω → EucConfig d N := fun τ ζ => b (τ : ℝ) (Y τ ζ) with hbpdef
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (Y 0) := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · exact (hY.filtered.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
    · have h := hY.filtered.progressive.adapted s
      have e : ofNNRealTime Y s = Y 0 := by
        funext ζ
        simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
      rw [e] at h
      exact h
  have hbprog : IsProgressive ℱ (ofNNRealTime bp) := by
    have h := isProgressive_comp_measurable' (ofNNRealTime Y) hY.filtered.progressive
      (fun s x => b ((Real.toNNReal s : ℝ≥0) : ℝ) x)
      (hbm.comp ((measurable_fst.real_toNNReal.coe_nnreal_real).prodMk measurable_snd))
    exact h
  have hτ : ((Real.toNNReal S : ℝ≥0) : ℝ) = S := Real.coe_toNNReal S hS0
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn (fun s : ℝ => bp (Real.toNNReal s) ζ) (Icc 0 S) := by
    filter_upwards [hY.eqn] with ζ h
    have hi := (h (Real.toNNReal S) (le_of_eq hτ)).1
    rw [hτ] at hi
    refine integrable_pi_iff.2 fun i => ?_
    refine (hi i).congr_fun (fun s hs => ?_) measurableSet_Icc
    simp [hbpdef, Real.coe_toNNReal _ hs.1]
  have hXeq := p4f_Xeq hY
  have hito := ito_formula_additive_time_independent (P := P) (ℱ := ℱ) hbrown hS0 g hg.smooth σ Y
    hXmeas hX₀ bp hbprog hbint hXeq
  have hΨL2 := p4f_psiL2 (P := P) (S := S) hY.filtered.progressive hg σ
  -- the generator is bounded on `[0,S]`
  obtain ⟨CG, hCG⟩ : ∃ CG : ℝ, ∀ s ∈ Icc (0 : ℝ) S, ∀ x, |p4Gen ν b s g x| ≤ CG := by
    refine ⟨|ν| * (C * ∑ k : Fin N × Fin d, ‖configBasis d N k‖ * ‖configBasis d N k‖) +
      (a₀ + K) * C, fun s hs x => ?_⟩
    have h1 : |∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k)| ≤
        C * ∑ k : Fin N × Fin d, ‖configBasis d N k‖ * ‖configBasis d N k‖ := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k)‖
          ≤ ‖fderiv ℝ (fderiv ℝ g) x‖ * ‖configBasis d N k‖ * ‖configBasis d N k‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ C * ‖configBasis d N k‖ * ‖configBasis d N k‖ := by
            gcongr
            exact (hC x).2.2
        _ = C * (‖configBasis d N k‖ * ‖configBasis d N k‖) := by ring
    have h2 : |fderiv ℝ g x (b s x)| ≤ (a₀ + K) * C := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ g x (b s x)‖ ≤ ‖fderiv ℝ g x‖ * ‖b s x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ g x‖ * ((a₀ + K) * (1 + ‖x‖)) := by
            gcongr
            refine (hBb s hs x).trans ?_
            have := norm_nonneg x
            nlinarith [K.2]
        _ = (a₀ + K) * (‖fderiv ℝ g x‖ * (1 + ‖x‖)) := by ring
        _ ≤ (a₀ + K) * C := by
            gcongr
            exact (hC x).2.1
    unfold p4Gen
    calc |ν * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k) +
          fderiv ℝ g x (b s x)|
        ≤ |ν * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ g) x (configBasis d N k) (configBasis d N k)| +
          |fderiv ℝ g x (b s x)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
  -- the sampled generator
  set t' : ℝ≥0 := Real.toNNReal t with ht'
  have htt : (t' : ℝ) = t := Real.coe_toNNReal t ht.1
  have htS : t ∈ Icc (0 : ℝ) S := ht
  set Gs : ℝ → Ω → ℝ := fun s ζ => p4Gen ν b (clampTI t s) g (Y (Real.toNNReal s) ζ) with hGs
  have hcore : ∀ᵐ ζ ∂P, g (Y t' ζ) = g (Y 0 ζ) + (∫ s in Icc (0 : ℝ) t, Gs s ζ) +
      itoIntegral P ℱ W' (itoIntegrand S Set.univ (fun _ x => g x) (ofNNRealTime Y)
        (fun _ _ => σ)) t ζ := by
    filter_upwards [hito, localItoIntegral_eq_itoIntegral hbrown hΨL2] with ζ hζ hloc
    have h := hζ t' (by rw [htt]; exact ht.2)
    rw [htt, hloc t] at h
    rw [h]
    congr 2
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [hGs, hbpdef, clampTI_of_mem hs, Real.coe_toNNReal _ hs.1]
    rw [p4f_gen_eq hν]
  have hMLp := memLp_two_itoIntegral hbrown hΨL2 t
  have hMint := integral_itoIntegral hbrown hΨL2 t
  have : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hGcl : Continuous (fun q : ℝ × EucConfig d N => p4Gen ν b (clampTI t q.1) g q.2) :=
    (p4f_gen_cont hbc hg.smooth).comp (((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd)
  have hYp : Measurable (fun p : ℝ × Ω => Y (Real.toNNReal p.1) p.2) :=
    measurable_of_progressive hY.filtered.progressive
  have hpair : Measurable (fun p : ℝ × Ω => (p.1, Y (Real.toNNReal p.1) p.2)) :=
    measurable_fst.prodMk hYp
  have hprodm : Measurable (fun p : ℝ × Ω => Gs p.1 p.2) := by
    have h := (hGcl.measurable).comp hpair
    exact h
  have hprodint : Integrable (fun p : ℝ × Ω => Gs p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) t)).prod P) :=
    Integrable.of_bound hprodm.aestronglyMeasurable CG (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact hCG _ ⟨(clampTI_mem ht.1 p.1).1, (clampTI_mem ht.1 p.1).2.trans ht.2⟩ _)
  have hIint : Integrable (fun ζ => ∫ s in Icc (0 : ℝ) t, Gs s ζ) P := hprodint.integral_prod_right
  have hm0 : Measurable g := hgc.measurable
  have hg0int : Integrable (fun ζ => g (Y 0 ζ)) P :=
    Integrable.of_bound (hm0.comp (hXmeas 0)).aestronglyMeasurable C
      (ae_of_all _ fun ζ => by rw [Real.norm_eq_abs]; exact (hC _).1)
  have hMi : Integrable (itoIntegral P ℱ W'
      (itoIntegrand S Set.univ (fun _ x => g x) (ofNNRealTime Y) (fun _ _ => σ)) t) P :=
    hMLp.integrable one_le_two
  have hIeq : ∫ ζ, (∫ s in Icc (0 : ℝ) t, Gs s ζ) ∂P =
      ∫ r in Icc (0 : ℝ) t, ∫ x, p4Gen ν b r g x ∂(law P (Y (Real.toNNReal r))) := by
    have hswap := integral_integral_swap (μ := volume.restrict (Icc (0 : ℝ) t)) (ν := P)
      (f := fun s ζ => Gs s ζ) hprodint
    rw [← hswap]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hg1 : Measurable (fun x : EucConfig d N => p4Gen ν b r g x) :=
      ((p4f_gen_cont hbc hg.smooth).comp (continuous_const.prodMk continuous_id)).measurable
    rw [law, integral_map (hXmeas _).aemeasurable hg1.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only [hGs, clampTI_of_mem hr]
  have hint0 : ∫ ζ, g (Y t' ζ) ∂P = ∫ ζ, (g (Y 0 ζ) + (∫ s in Icc (0 : ℝ) t, Gs s ζ) +
      itoIntegral P ℱ W' (itoIntegrand S Set.univ (fun _ x => g x) (ofNNRealTime Y)
        (fun _ _ => σ)) t ζ) ∂P := integral_congr_ae hcore
  have hA : Integrable (fun ζ => g (Y 0 ζ) + ∫ s in Icc (0 : ℝ) t, Gs s ζ) P := hg0int.add hIint
  rw [integral_add hA hMi, integral_add hg0int hIint, hMint, add_zero] at hint0
  rw [law, integral_map (hXmeas _).aemeasurable hgc.aestronglyMeasurable, law,
    integral_map (hXmeas _).aemeasurable hgc.aestronglyMeasurable, ← hIeq, Real.toNNReal_zero]
  exact hint0


/-! ### The interface lemma -/

theorem p4_flow_hyp_proof {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : ℝ} (hν : 0 ≤ ν) {S : ℝ} (hS : 0 < S) {b : ℝ → EucConfig d N → EucConfig d N}
    (hbc : Continuous (Function.uncurry b)) (hbl : ∃ K : ℝ≥0, ∀ τ ∈ Set.Icc (0 : ℝ) S, LipschitzWith K (b τ))
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : P4AddSol P ν b S ℱ W' W Y)
    (hm0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (Y 0)) < ⊤) :
    P4FlowHyp ν b S (fun r => law P (Y (Real.toNNReal r))) := by
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le t) le_rfl
  refine ⟨fun t => ?_, p4f_moment hν hS hbc hbl hY hm0, fun g hg hb => p4f_narrow hY hg hb,
    fun g hg t ht => p4f_fp hν hS hbc hbl hY hg ht⟩
  exact (Measure.isProbabilityMeasure_map_iff (hYm _).aemeasurable).2 inferInstance

example := (@p4_flow_hyp_proof : type_of% @HRS.MP.SelfSimP4.p4_flow_hyp)

end HRS.MP.SelfSimP4Impl
