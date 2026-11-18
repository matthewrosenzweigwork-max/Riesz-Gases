import HRS.Equilibrium.MarginalExpFamily
import HRS.External.Entropy

/-!
# HRS.MS.SharpInsAux1 -- S7.6 `sharp_insertion_radius`, abstract part

Packet S76, namespace `HRS.MS.S76`, helper prefix `s76_`.  No frozen file is edited.

* `s76_defect_eq`: for a probability space, a measurable integrable `X ≤ 0`,
  `cgf X P 1 - E X = ∫_0^1 (1 - t) Var_{P_t}(X) dt`, where `P_t = P.tilted (t X)` (the integrand is
  integrable on `(0,1]`): `φ(x) = F(x) + (1-x) F'(x)` has derivative `(1-x) F''(x) ≥ 0`.
* `s76_cov_sq_le`: `cov(S,T)² ≤ Var S Var T` (discriminant of `c ↦ Var(S + c T)`).
* `s76_var_compare`: for an exchangeable probability law `Q` on `E^n` and nonnegative `ψ, χ` with
  `Σψ(Y_i), Σχ(Y_i) ∈ L²(Q)`:
  `|Var(Σ(ψ+χ)(Y_i)) - n E ψ(Y_0)²| ≤ n²(c₂ + c₁²) + v_T + 2 √(v_S v_T)` whenever
  `E ψ(Y_0) ≤ c₁`, `E ψ(Y_0)ψ(Y_1) ≤ c₂`, `Var Σψ ≤ v_S`, `Var Σχ ≤ v_T`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.S76

/-! ### The defect as a weighted integral of the variance -/

section Defect

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

theorem s76_defect_eq (hXm : Measurable X) (hb : ∀ ω, X ω ≤ 0) (hXi : Integrable X P) :
    IntegrableOn (fun t => (1 - t) * Var[X; P.tilted (fun ω => t * X ω)]) (Ioc (0 : ℝ) 1) ∧
      cgf X P 1 - P[X] =
        ∫ t in Ioc (0 : ℝ) 1, (1 - t) * Var[X; P.tilted (fun ω => t * X ω)] := by
  set F := cgf X P with hFdef
  set H : ℝ → ℝ := fun u => (P.tilted (fun ω => u * X ω))[X] with hHdef
  set V : ℝ → ℝ := fun t => Var[X; P.tilted (fun ω => t * X ω)] with hVdef
  set φ : ℝ → ℝ := fun x => F x + (1 - x) * H x with hφdef
  have hF : ∀ t, 0 < t → HasDerivAt F (H t) t := fun t ht =>
    HRS.MarginalAux.EF.hasDerivAt_cgf hXm hb ht
  have hH : ∀ t, 0 < t → HasDerivAt H (V t) t := fun t ht =>
    HRS.MarginalAux.EF.hasDerivAt_mean hXm hb ht
  have hφ : ∀ t, 0 < t → HasDerivAt φ ((1 - t) * V t) t := by
    intro t ht
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h2 := (hF t ht).add (h1.mul (hH t ht))
    convert h2 using 1
    ring
  have hlimH : Tendsto H (𝓝[>] 0) (𝓝 (P[X])) :=
    HRS.MarginalAux.EF.tendsto_mean_zero hXm hb hXi
  have hlimF : Tendsto F (𝓝[>] 0) (𝓝 0) := HRS.MarginalAux.EF.tendsto_cgf_zero hXm hb
  have hlimφ : Tendsto φ (𝓝[>] 0) (𝓝 (P[X])) := by
    have h1 : Tendsto (fun x : ℝ => (1 - x) * H x) (𝓝[>] 0) (𝓝 ((1 - 0) * P[X])) :=
      ((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds).mul hlimH
    have h2 := hlimF.add h1
    simpa using h2
  have hφ0 : φ 0 = P[X] := by
    simp only [hφdef, hFdef, hHdef, cgf_zero, zero_mul, sub_zero, one_mul, zero_add]
    have h0 : P.tilted (fun _ : Ω => (0 : ℝ)) = P := tilted_zero P
    rw [h0]
  have hcont : ContinuousOn φ (Icc 0 1) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      rw [continuousWithinAt_Icc_iff_Ici zero_lt_one, ← continuousWithinAt_Ioi_iff_Ici]
      rw [ContinuousWithinAt, hφ0]
      exact hlimφ
    · exact (hφ x h).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt φ ((1 - x) * V x) x := fun x hx => hφ x hx.1
  have hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ (1 - x) * V x := fun x hx =>
    mul_nonneg (by linarith [hx.2]) (variance_nonneg _ _)
  have hint : IntegrableOn (fun x => (1 - x) * V x) (Ioc (0 : ℝ) 1) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hpos
  refine ⟨hint, ?_⟩
  have hint' : IntervalIntegrable (fun x => (1 - x) * V x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint'
  rw [intervalIntegral.integral_of_le zero_le_one] at hftc
  rw [hftc, hφ0]
  simp [hφdef]

end Defect

/-! ### Covariance Cauchy-Schwarz -/

section Cov

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem s76_cov_sq_le {S T : Ω → ℝ} (hS : MemLp S 2 μ) (hT : MemLp T 2 μ) :
    cov[S, T; μ] ^ 2 ≤ Var[S; μ] * Var[T; μ] := by
  have h : ∀ c : ℝ, 0 ≤ Var[T; μ] * (c * c) + (2 * cov[S, T; μ]) * c + Var[S; μ] := by
    intro c
    have h1 := variance_nonneg (S + c • T) μ
    have h2 : Var[S + c • T; μ] = Var[S; μ] + 2 * cov[S, c • T; μ] + Var[c • T; μ] :=
      variance_add hS (hT.const_smul c)
    rw [h2, covariance_smul_right, variance_smul] at h1
    nlinarith [h1]
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith [this]

end Cov

/-! ### Exchangeable sums -/

section Exch

open HRS.External.Entropy (IsExchangeable)

variable {E : Type*} [MeasurableSpace E]

theorem s76_exists_perm {n : ℕ} (a b : Fin n) (hab : a ≠ b) (i j : Fin n) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin n), σ i = a ∧ σ j = b := by
  set τ1 : Equiv.Perm (Fin n) := Equiv.swap i a with hτ1
  have hj' : τ1 j ≠ a := by
    intro h
    have : τ1 j = τ1 i := by rw [h, hτ1, Equiv.swap_apply_left]
    exact hij (τ1.injective this).symm
  refine ⟨τ1.trans (Equiv.swap (τ1 j) b), ?_, ?_⟩
  · simp only [Equiv.trans_apply, hτ1, Equiv.swap_apply_left]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact hj'.symm
    · exact hab
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

theorem s76_pair_eq {n : ℕ} {Q : Measure (Fin n → E)} (hex : IsExchangeable Q)
    (a b : Fin n) (hab : a ≠ b) {i j : Fin n} (hij : i ≠ j) :
    Q.map (fun Y => (Y i, Y j)) = Q.map (fun Y => (Y a, Y b)) := by
  obtain ⟨σ, hσi, hσj⟩ := s76_exists_perm a b hab i j hij
  have hσ := hex σ
  have hm : Measurable fun (x : Fin n → E) k => x (σ k) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  have hp : Measurable (fun Y : Fin n → E => (Y i, Y j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  conv_lhs => rw [← hσ]
  rw [Measure.map_map hp hm]
  congr 1
  funext Y
  simp [Function.comp, hσi, hσj]

theorem s76_coord_eq {n : ℕ} {Q : Measure (Fin n → E)} (hex : IsExchangeable Q)
    (i a : Fin n) {F : E → ℝ} (hF : Measurable F) :
    ∫ Y, F (Y i) ∂Q = ∫ Y, F (Y a) ∂Q := by
  have h := hex.marginal_eq i a
  have e1 : ∫ Y, F (Y i) ∂Q = ∫ y, F y ∂(Q.map (fun Y => Y i)) :=
    (integral_map (measurable_pi_apply i).aemeasurable hF.aestronglyMeasurable).symm
  have e2 : ∫ Y, F (Y a) ∂Q = ∫ y, F y ∂(Q.map (fun Y => Y a)) :=
    (integral_map (measurable_pi_apply a).aemeasurable hF.aestronglyMeasurable).symm
  rw [e1, e2, h]

theorem s76_pair_integral {n : ℕ} {Q : Measure (Fin n → E)} (hex : IsExchangeable Q)
    (a b : Fin n) (hab : a ≠ b) {i j : Fin n} (hij : i ≠ j) {ψ : E → ℝ} (hψ : Measurable ψ) :
    ∫ Y, ψ (Y i) * ψ (Y j) ∂Q = ∫ Y, ψ (Y a) * ψ (Y b) ∂Q := by
  have hG : Measurable (fun p : E × E => ψ p.1 * ψ p.2) :=
    (hψ.comp measurable_fst).mul (hψ.comp measurable_snd)
  have hp : ∀ i j : Fin n, Measurable (fun Y : Fin n → E => (Y i, Y j)) := fun i j =>
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have e : ∀ i j : Fin n, ∫ Y, ψ (Y i) * ψ (Y j) ∂Q =
      ∫ p, ψ p.1 * ψ p.2 ∂(Q.map (fun Y => (Y i, Y j))) := fun i j =>
    (integral_map (hp i j).aemeasurable hG.aestronglyMeasurable).symm
  rw [e i j, e a b, s76_pair_eq hex a b hab hij]

/-- The variance of an exchangeable sum, in terms of three moments. -/
theorem s76_var_sum {n : ℕ} {Q : Measure (Fin n → E)} [IsProbabilityMeasure Q]
    (hex : IsExchangeable Q) (a b : Fin n) (hab : a ≠ b) {ψ : E → ℝ} (hψ : Measurable ψ)
    (hmem : ∀ i, MemLp (fun Y : Fin n → E => ψ (Y i)) 2 Q) :
    Var[fun Y : Fin n → E => ∑ i, ψ (Y i); Q] =
      n * ∫ Y, ψ (Y a) ^ 2 ∂Q + n * (n - 1) * ∫ Y, ψ (Y a) * ψ (Y b) ∂Q -
        n ^ 2 * (∫ Y, ψ (Y a) ∂Q) ^ 2 := by
  set aa : ℝ := ∫ Y, ψ (Y a) ^ 2 ∂Q with haa
  set bb : ℝ := ∫ Y, ψ (Y a) * ψ (Y b) ∂Q with hbb
  set cc : ℝ := ∫ Y, ψ (Y a) ∂Q with hcc
  have hS : MemLp (fun Y : Fin n → E => ∑ i, ψ (Y i)) 2 Q :=
    memLp_finsetSum _ fun i _ => hmem i
  rw [variance_eq_sub hS]
  have hES : ∫ Y, (fun Y : Fin n → E => ∑ i, ψ (Y i)) Y ∂Q = n * cc := by
    have : ∀ i, Integrable (fun Y : Fin n → E => ψ (Y i)) Q := fun i =>
      (hmem i).integrable (by norm_num)
    rw [integral_finsetSum _ fun i _ => this i]
    have h2 : ∀ i, ∫ Y, ψ (Y i) ∂Q = cc := fun i => s76_coord_eq hex i a hψ
    simp [h2]
  have hES2 : ∫ Y, ((fun Y : Fin n → E => ∑ i, ψ (Y i)) ^ 2) Y ∂Q =
      n * aa + n * (n - 1) * bb := by
    have e1 : ∀ Y : Fin n → E, ((fun Y : Fin n → E => ∑ i, ψ (Y i)) ^ 2) Y =
        ∑ i, ∑ j, ψ (Y i) * ψ (Y j) := by
      intro Y
      simp only [Pi.pow_apply, sq]
      rw [Finset.sum_mul_sum]
    simp_rw [e1]
    have hint : ∀ i j, Integrable (fun Y : Fin n → E => ψ (Y i) * ψ (Y j)) Q := fun i j =>
      (hmem i).integrable_mul (hmem j)
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    have e2 : ∀ i, ∫ Y, ∑ j, ψ (Y i) * ψ (Y j) ∂Q = n * bb + (aa - bb) := by
      intro i
      rw [integral_finsetSum _ fun j _ => hint i j]
      have h3 : ∀ j, ∫ Y, ψ (Y i) * ψ (Y j) ∂Q = bb + if i = j then (aa - bb) else 0 := by
        intro j
        by_cases hij : i = j
        · subst hij
          have := s76_coord_eq hex i a (hψ.pow_const 2)
          simp only [ite_true]
          have h4 : ∫ Y, ψ (Y i) * ψ (Y i) ∂Q = aa := by
            show _ = ∫ Y, ψ (Y a) ^ 2 ∂Q
            simpa [sq] using this
          linarith
        · simp only [hij, ite_false, add_zero]
          exact s76_pair_integral hex a b hab hij hψ
      simp_rw [h3]
      rw [Finset.sum_add_distrib]
      simp
    simp_rw [e2]
    simp
    ring
  rw [hES2, hES]
  ring

end Exch

/-! ### Comparison of the variance of `S + T` with the diagonal term -/

section Compare

open HRS.External.Entropy (IsExchangeable)

variable {E : Type*} [MeasurableSpace E]

theorem s76_var_compare {n : ℕ} {Q : Measure (Fin n → E)} [IsProbabilityMeasure Q]
    (hex : IsExchangeable Q) (a b : Fin n) (hab : a ≠ b) {ψ χ : E → ℝ}
    (hψ : Measurable ψ) (hψ0 : ∀ y, 0 ≤ ψ y)
    (hS : MemLp (fun Y : Fin n → E => ∑ i, ψ (Y i)) 2 Q)
    (hT : MemLp (fun Y : Fin n → E => ∑ i, χ (Y i)) 2 Q)
    {c1 c2 vS vT : ℝ} (h1 : ∫ Y, ψ (Y a) ∂Q ≤ c1) (h2 : ∫ Y, ψ (Y a) * ψ (Y b) ∂Q ≤ c2)
    (hvS : Var[fun Y : Fin n → E => ∑ i, ψ (Y i); Q] ≤ vS)
    (hvT : Var[fun Y : Fin n → E => ∑ i, χ (Y i); Q] ≤ vT) :
    |Var[fun Y : Fin n → E => ∑ i, (ψ (Y i) + χ (Y i)); Q] - n * ∫ Y, ψ (Y a) ^ 2 ∂Q| ≤
      n ^ 2 * (c2 + c1 ^ 2) + vT + 2 * Real.sqrt (vS * vT) := by
  -- each coordinate is in `L²`
  have hmem : ∀ i, MemLp (fun Y : Fin n → E => ψ (Y i)) 2 Q := by
    intro i
    refine hS.mono (measurable_pi_apply i |> hψ.comp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψ0 _),
      abs_of_nonneg (Finset.sum_nonneg fun j _ => hψ0 _)]
    exact Finset.single_le_sum (f := fun j => ψ (Y j)) (fun j _ => hψ0 _) (Finset.mem_univ i)
  have hVS := s76_var_sum hex a b hab hψ hmem
  set aa : ℝ := ∫ Y, ψ (Y a) ^ 2 ∂Q with haa
  set bb : ℝ := ∫ Y, ψ (Y a) * ψ (Y b) ∂Q with hbb
  set cc : ℝ := ∫ Y, ψ (Y a) ∂Q with hcc
  have hbb0 : 0 ≤ bb := integral_nonneg fun Y => mul_nonneg (hψ0 _) (hψ0 _)
  have hcc0 : 0 ≤ cc := integral_nonneg fun Y => hψ0 _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : 1 ≤ n := by
      rcases n with _ | n
      · exact absurd (a.2) (by simp)
      · omega
    have : (1 : ℝ) ≤ n := by exact_mod_cast this
    linarith
  have hc2 : 0 ≤ c2 := hbb0.trans h2
  have hVS_diff : |Var[fun Y : Fin n → E => ∑ i, ψ (Y i); Q] - n * aa| ≤ n ^ 2 * (c2 + c1 ^ 2) := by
    rw [hVS]
    have e : n * aa + n * (n - 1) * bb - n ^ 2 * cc ^ 2 - n * aa = n * (n - 1) * bb - n ^ 2 * cc ^ 2 := by
      ring
    rw [e, abs_le]
    have hcc1 : cc ≤ c1 := h1
    have hcc2 : cc ^ 2 ≤ c1 ^ 2 := by nlinarith
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    constructor
    · have : 0 ≤ (n : ℝ) * (n - 1) * bb := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hcc2 hn2, sq_nonneg cc, mul_nonneg hn2 hc2]
    · have h3 : (n : ℝ) * (n - 1) * bb ≤ (n : ℝ) ^ 2 * c2 := by
        have : (n : ℝ) * (n - 1) ≤ (n : ℝ) ^ 2 := by nlinarith
        calc (n : ℝ) * (n - 1) * bb ≤ (n : ℝ) ^ 2 * bb := mul_le_mul_of_nonneg_right this hbb0
          _ ≤ (n : ℝ) ^ 2 * c2 := mul_le_mul_of_nonneg_left h2 hn2
      nlinarith [mul_nonneg hn2 (sq_nonneg c1), sq_nonneg cc, mul_nonneg hn2 (sq_nonneg cc)]
  -- the covariance
  have hSum : (fun Y : Fin n → E => ∑ i, (ψ (Y i) + χ (Y i))) =
      (fun Y : Fin n → E => ∑ i, ψ (Y i)) + (fun Y : Fin n → E => ∑ i, χ (Y i)) := by
    funext Y; simp [Finset.sum_add_distrib]
  rw [hSum, variance_add hS hT]
  have hcov := s76_cov_sq_le hS hT
  have hVS0 := variance_nonneg (fun Y : Fin n → E => ∑ i, ψ (Y i)) Q
  have hVT0 := variance_nonneg (fun Y : Fin n → E => ∑ i, χ (Y i)) Q
  have hcov' : |cov[fun Y : Fin n → E => ∑ i, ψ (Y i), fun Y : Fin n → E => ∑ i, χ (Y i); Q]| ≤
      Real.sqrt (vS * vT) := by
    refine Real.abs_le_sqrt (hcov.trans ?_)
    exact mul_le_mul hvS hvT hVT0 (hVS0.trans hvS)
  set Vs := Var[fun Y : Fin n → E => ∑ i, ψ (Y i); Q] with hVs
  set Vt := Var[fun Y : Fin n → E => ∑ i, χ (Y i); Q] with hVt
  set cv := cov[fun Y : Fin n → E => ∑ i, ψ (Y i), fun Y : Fin n → E => ∑ i, χ (Y i); Q] with hcv
  have hd : |Vs + 2 * cv + Vt - n * aa| ≤ |Vs - n * aa| + 2 * |cv| + Vt := by
    have : Vs + 2 * cv + Vt - n * aa = (Vs - n * aa) + 2 * cv + Vt := by ring
    rw [this]
    calc |(Vs - n * aa) + 2 * cv + Vt| ≤ |(Vs - n * aa) + 2 * cv| + |Vt| := abs_add_le _ _
      _ ≤ |Vs - n * aa| + |2 * cv| + |Vt| := by gcongr; exact abs_add_le _ _
      _ = |Vs - n * aa| + 2 * |cv| + Vt := by
          rw [abs_mul, abs_of_nonneg hVT0]; norm_num
  linarith

end Compare

end HRS.MS.S76
