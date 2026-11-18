import HRS.MC.S7FCW5A

/-!
# S7FCW5: relocated proof of `s7_FC_C2_wick_param` (FC-C2, generic jointly measurable Wick limit)

The statement is copied verbatim from `HRS/MC/S7FCPlan.lean` (namespace `HRS.MC.Sec7.FCPlan`); it is proved here in
namespace `HRS.MC.Sec7.S7FCW5` and tied to the frozen statement in `HRS/MC/S7FCW5Tie.lean`.

Route.  (1) Fix a subsequence `m` (from `ε` and `K` only) with `ε (m j) ≤ ((1/2)^j)^2 / (2(K²+1))`.
(2) For each `t ≥ 0`, `Y_j(t,·)` (finite sections over `F (m j)`) is Cauchy in `L²` by `S7FCW5_pair`, so a.s. convergent
(`ae_tendsto_of_cauchy_eLpNorm`).  (3) `Q := limsup_j Y_j` where the liminf and limsup agree, `0` elsewhere: jointly
measurable since each `Y_j` is.  (4) For every finite `S`, Fatou plus `S7FCW5_pair` give
`∫⁻ ‖Q_t - W_S‖ₑ² ≤ ofReal (K² tailHS S)`, and `tailHS S → 0` along `atTop` (`htail`, `S ⊇ F n`), which is `IsHalfWick`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW5

open HRS HRS.Sec7 HRS.MC.QRSpec

variable {d : ℕ}

theorem s7_FC_C2_wick_param_proof {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r : ℝ)
    (X : ℝ → Ω → NegSobolev d r) (hXm : Measurable (Function.uncurry X)) (K : ℝ)
    (hG : ∀ t : ℝ, 0 ≤ t → HasFiniteGaussianCoeffs P (X t) ∧ ModeCovBound P (X t) K)
    (μ : ℝ → Measure (Torus d)) (h : Torus d → Torus d → ℝ)
    (hcm : ∀ k l : NonzeroLattice d, Measurable fun t => wickCoeff (μ t) h k l)
    (hA : ∀ t : ℝ, 0 ≤ t →
      Summable fun p : NonzeroLattice d × NonzeroLattice d => wickCoeff (μ t) h p.1 p.2 ^ 2)
    (F : ℕ → Finset (NonzeroLattice d)) (hF : ∀ n, F n ≤ F (n + 1)) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (htail : ∀ t : ℝ, 0 ≤ t → ∀ n, tailHS (wickCoeff (μ t) h) (F n) ≤ ε n) :
    ∃ Q : ℝ → Ω → ℝ, Measurable (Function.uncurry Q) ∧
      ∀ t : ℝ, 0 ≤ t → IsHalfWick P (X t) (μ t) h (Q t) := by
  have hpt : ∀ t : ℝ, Measurable fun ω : Ω => ((t, ω) : ℝ × Ω) := fun t => measurable_prodMk_left
  -- Step 1: a fast subsequence, chosen from `ε` and `K` only (not from `t`)
  have hbpos : ∀ j : ℕ, (0 : ℝ) < ((1 / 2 : ℝ) ^ j) ^ 2 / (2 * (K ^ 2 + 1)) := fun j => by positivity
  obtain ⟨m, hm, hmε⟩ := Filter.extraction_forall_of_eventually
    (P := fun j n => ε n ≤ ((1 / 2 : ℝ) ^ j) ^ 2 / (2 * (K ^ 2 + 1)))
    (fun j => (hε.eventually (gt_mem_nhds (hbpos j))).mono fun n hn => hn.le)
  -- Step 2: the finite sections `Y_j` and their jointly measurable limit `Qp`
  obtain ⟨Ym, hYm⟩ : ∃ Ym : ℕ → ℝ × Ω → ℝ, ∀ j p,
      Ym j p = wickSection P (X p.1) (μ p.1) h (F (m j)) p.2 := ⟨_, fun _ _ => rfl⟩
  have hYt : ∀ j t ω, Ym j (t, ω) = wickSection P (X t) (μ t) h (F (m j)) ω :=
    fun j t ω => hYm j (t, ω)
  have hYmeas : ∀ j, Measurable (Ym j) := fun j => by
    have e : Ym j = fun p : ℝ × Ω => wickSection P (X p.1) (μ p.1) h (F (m j)) p.2 := funext (hYm j)
    rw [e]
    exact S7FCW5_sec_meas P hXm μ h hcm (F (m j))
  obtain ⟨Qp, hQp⟩ : ∃ Qp : ℝ × Ω → ℝ, ∀ p, Qp p =
      if Filter.liminf (fun j => Ym j p) atTop = Filter.limsup (fun j => Ym j p) atTop
        then Filter.limsup (fun j => Ym j p) atTop else 0 := ⟨_, fun _ => rfl⟩
  have hQm : Measurable Qp := by
    have e : Qp = fun p : ℝ × Ω =>
        if Filter.liminf (fun j => Ym j p) atTop = Filter.limsup (fun j => Ym j p) atTop
          then Filter.limsup (fun j => Ym j p) atTop else 0 := funext hQp
    rw [e]
    exact Measurable.ite (measurableSet_eq_fun (Measurable.liminf hYmeas) (Measurable.limsup hYmeas))
      (Measurable.limsup hYmeas) measurable_const
  -- Step 3: `L²`-Cauchy along the subsequence, hence a.s. convergence, for each `t ≥ 0`
  have hconv : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, Tendsto (fun j => Ym j (t, ω)) atTop (𝓝 (Qp (t, ω))) := by
    intro t ht
    have hB : ∑' i : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ i) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
      exact ENNReal.ofReal_ne_top
    have hcs : ∀ N n k : ℕ, N ≤ n → N ≤ k →
        eLpNorm (fun ω => Ym n (t, ω) - Ym k (t, ω)) 2 P < ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
      intro N n k hn hk
      simp only [hYt]
      obtain ⟨hmem, hint⟩ := S7FCW5_pair (hG t ht).1 (hG t ht).2 (μ t) h (hA t ht) (F (m n)) (F (m k))
      refine S7FCW5_eLp_of_sq _ hmem _ (by positivity) ?_
      refine lt_of_le_of_lt hint ?_
      have hy : (0 : ℝ) < ((1 / 2 : ℝ) ^ N) ^ 2 := by positivity
      have hq : (0 : ℝ) < K ^ 2 + 1 := by positivity
      have hb1 : ε (m n) ≤ ((1 / 2 : ℝ) ^ N) ^ 2 / (2 * (K ^ 2 + 1)) :=
        (hmε n).trans (div_le_div_of_nonneg_right (S7FCW5_half_pow_sq N n hn) (by positivity))
      have hb2 : ε (m k) ≤ ((1 / 2 : ℝ) ^ N) ^ 2 / (2 * (K ^ 2 + 1)) :=
        (hmε k).trans (div_le_div_of_nonneg_right (S7FCW5_half_pow_sq N k hk) (by positivity))
      have ht1 := htail t ht (m n)
      have ht2 := htail t ht (m k)
      calc K ^ 2 * (tailHS (wickCoeff (μ t) h) (F (m n)) + tailHS (wickCoeff (μ t) h) (F (m k)))
          ≤ K ^ 2 * (((1 / 2 : ℝ) ^ N) ^ 2 / (2 * (K ^ 2 + 1)) +
              ((1 / 2 : ℝ) ^ N) ^ 2 / (2 * (K ^ 2 + 1))) :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg K)
        _ = ((1 / 2 : ℝ) ^ N) ^ 2 * (K ^ 2 / (K ^ 2 + 1)) := by
          have hq0 : K ^ 2 + 1 ≠ 0 := ne_of_gt hq
          field_simp
          ring
        _ < ((1 / 2 : ℝ) ^ N) ^ 2 := mul_lt_of_lt_one_right hy ((div_lt_one hq).2 (by linarith))
    have hcau := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm (p := 2) (μ := P) (f := fun j ω => Ym j (t, ω))
      (fun j => ((hYmeas j).comp (hpt t)).aestronglyMeasurable)
      (by norm_num) (B := fun N : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ N)) hB hcs
    filter_upwards [hcau] with ω hω
    obtain ⟨l, hl⟩ := hω
    have hl' : Tendsto (fun j => Ym j (t, ω)) atTop (𝓝 l) := hl
    rw [hQp, hl'.limsup_eq, hl'.liminf_eq, if_pos rfl]
    exact hl'
  -- Step 4: the `IsHalfWick` bound for each finite section `S`
  have hbound : ∀ t : ℝ, 0 ≤ t → ∀ S : Finset (NonzeroLattice d),
      ∫⁻ ω, ‖Qp (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (K ^ 2 * tailHS (wickCoeff (μ t) h) S) := by
    intro t ht S
    have hWm : Measurable fun ω => wickSection P (X t) (μ t) h S ω := by
      have h3 : Measurable ((fun p : ℝ × Ω => wickSection P (X p.1) (μ p.1) h S p.2) ∘
          fun ω : Ω => ((t, ω) : ℝ × Ω)) := (S7FCW5_sec_meas P hXm μ h hcm S).comp (hpt t)
      exact h3
    have hYtm : ∀ j, Measurable fun ω => Ym j (t, ω) :=
      fun j => (hYmeas j).comp (hpt t)
    have hj : ∀ j, ∫⁻ ω, ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P ≤
        ENNReal.ofReal (K ^ 2 * (ε (m j) + tailHS (wickCoeff (μ t) h) S)) := by
      intro j
      obtain ⟨hmem, hint⟩ := S7FCW5_pair (hG t ht).1 (hG t ht).2 (μ t) h (hA t ht) (F (m j)) S
      have ht1 : tailHS (wickCoeff (μ t) h) (F (m j)) ≤ ε (m j) := htail t ht (m j)
      have hK2 : K ^ 2 * (tailHS (wickCoeff (μ t) h) (F (m j)) + tailHS (wickCoeff (μ t) h) S) ≤
          K ^ 2 * (ε (m j) + tailHS (wickCoeff (μ t) h) S) :=
        mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg K)
      calc ∫⁻ ω, ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P
          = ∫⁻ ω, ENNReal.ofReal ((wickSection P (X t) (μ t) h (F (m j)) ω -
              wickSection P (X t) (μ t) h S ω) ^ 2) ∂P :=
            lintegral_congr fun ω => by rw [hYt, S7FCW5_enorm_sq]
        _ = ENNReal.ofReal (∫ ω, (wickSection P (X t) (μ t) h (F (m j)) ω -
              wickSection P (X t) (μ t) h S ω) ^ 2 ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
              (Eventually.of_forall fun ω => sq_nonneg _)).symm
        _ ≤ ENNReal.ofReal (K ^ 2 * (ε (m j) + tailHS (wickCoeff (μ t) h) S)) :=
            ENNReal.ofReal_le_ofReal (hint.trans hK2)
    have hmeas_j : ∀ j, AEMeasurable (fun ω => ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2) P :=
      fun j => ((((hYtm j).sub hWm).enorm).pow_const 2).aemeasurable
    have hfat : ∫⁻ ω, ‖Qp (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P ≤
        Filter.liminf (fun j => ∫⁻ ω, ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P) atTop := by
      calc ∫⁻ ω, ‖Qp (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P
          = ∫⁻ ω, Filter.liminf (fun j => ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2) atTop ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hconv t ht] with ω hω
            have hT : Tendsto (fun j => ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2) atTop
                (𝓝 (‖Qp (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2)) :=
              (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto _).comp (hω.sub_const _)
            exact hT.liminf_eq.symm
        _ ≤ _ := lintegral_liminf_le' (f := fun j ω => ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2)
            hmeas_j
    calc ∫⁻ ω, ‖Qp (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P
        ≤ Filter.liminf (fun j => ∫⁻ ω, ‖Ym j (t, ω) - wickSection P (X t) (μ t) h S ω‖ₑ ^ 2 ∂P) atTop := hfat
      _ ≤ Filter.liminf (fun j => ENNReal.ofReal (K ^ 2 * (ε (m j) + tailHS (wickCoeff (μ t) h) S))) atTop :=
          Filter.liminf_le_liminf (Eventually.of_forall hj)
      _ = ENNReal.ofReal (K ^ 2 * tailHS (wickCoeff (μ t) h) S) := by
          apply Tendsto.liminf_eq
          apply ENNReal.tendsto_ofReal
          have h1 := ((hε.comp hm.tendsto_atTop).add_const (tailHS (wickCoeff (μ t) h) S)).const_mul (K ^ 2)
          simpa using h1
  -- Step 5: `tailHS → 0` along finite sets, and conclusion
  have hlim : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun S : Finset (NonzeroLattice d) => tailHS (wickCoeff (μ t) h) S) atTop (𝓝 0) := by
    intro t ht
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun S => lt_of_lt_of_le ha (S7FCW5_tail_nonneg _ _),
      fun a ha => ?_⟩
    obtain ⟨n, hn⟩ := (hε.eventually (gt_mem_nhds ha)).exists
    filter_upwards [eventually_ge_atTop (F n)] with S hS
    exact lt_of_le_of_lt ((S7FCW5_tail_anti (wickCoeff (μ t) h) (hA t ht) hS).trans (htail t ht n)) hn
  refine ⟨fun t ω => Qp (t, ω), hQm, fun t ht => ?_⟩
  have hL : Tendsto (fun S : Finset (NonzeroLattice d) =>
      ENNReal.ofReal (K ^ 2 * tailHS (wickCoeff (μ t) h) S)) atTop (𝓝 0) := by
    have h2 := (hlim t ht).const_mul (K ^ 2)
    rw [mul_zero] at h2
    have h3 := ENNReal.tendsto_ofReal h2
    rwa [ENNReal.ofReal_zero] at h3
  unfold IsHalfWick
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL (fun _ => by simp)
    (fun S => hbound t ht S)

end HRS.MC.Sec7.S7FCW5

end
