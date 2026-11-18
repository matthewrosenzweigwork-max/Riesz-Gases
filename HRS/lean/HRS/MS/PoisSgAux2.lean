import HRS.MS.PoisSgAux1

/-!
# POIS-SG, part 2: the semigroup `sg`, differentiation under the integral, derivative bounds

Definition `sg P W q B t h x = ∫ ω, h (flowMap q B (W · ω) t x) ∂P`.

Main results (helper lemmas carry the prefix `sg_`):
* `sg_iteratedFDeriv_integral`: a general differentiation-under-the-integral theorem
  (`∫ G ω x dμ` is `C^k` with `D^i ∫ = ∫ D^i`, for a finite measure, `G ω ∈ C^k` with uniformly
  bounded derivatives and the measurability of the derivatives).
* `sg_contDiff`: for `h ∈ C^k` with `‖D^i h‖ ≤ M` (`i ≤ k ≤ m`), `sg t h` is `C^k`, its derivatives are
  the integrals of the derivatives of `h ∘ flowMap`, and `‖D^j (sg t h)‖ ≤ C M` with `C` depending
  only on `(d, q, Mb, m, T)` (not on `P`, `W`, `B`, `h`, `t ∈ [0,T]`).
* `sg_fderiv_bound`: `‖D (sg t h)‖ ≤ e^{(q+Mb) t} ‖Dh‖`.
* `sg_second_moment`: `E‖flowMap t x‖² ≤ C (1 + ‖x‖²)` for a Brownian filtration, together with
  integrability of `‖flowMap t x‖²`.

Statement adjustments relative to the packet sketch: the bound `‖D^j sg‖ ≤ C_j(t) Σ_{i ≤ j} ‖D^i h‖`
is stated with a common bound `M` of `‖D^i h‖`, `i ≤ k` (equivalent up to the constant), and `C` is
uniform for `t ∈ [0,T]`; `Mb ≥ 0` is automatic from `HasCbBound` (so `e^{(q+Mb)t}` is the same as
`e^{(q+|Mb|)t}` of `FlowB`).  The noise is an arbitrary `SgNoise` family (it is satisfied by
`IsBrownianFiltration`, see `sgNoise_of_brownian`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow

noncomputable section

universe u

namespace HRS.MS.PoisSg

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-! ### Differentiation under the integral sign -/

theorem sg_hasFDerivAt_integral {μ : Measure Ω} [IsFiniteMeasure μ] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (H : Ω → Euc d → V) (hdiff : ∀ ω, Differentiable ℝ (H ω)) {M0 M1 : ℝ}
    (h0 : ∀ ω x, ‖H ω x‖ ≤ M0) (h1 : ∀ ω x, ‖fderiv ℝ (H ω) x‖ ≤ M1)
    (hm0 : ∀ x, AEStronglyMeasurable (fun ω => H ω x) μ)
    (hm1 : ∀ x, AEStronglyMeasurable (fun ω => fderiv ℝ (H ω) x) μ) (x : Euc d) :
    HasFDerivAt (fun x => ∫ ω, H ω x ∂μ) (∫ ω, fderiv ℝ (H ω) x ∂μ) x :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x ω => H ω x)
    (F' := fun x ω => fderiv ℝ (H ω) x) (s := Set.univ) (bound := fun _ => M1)
    Filter.univ_mem (Eventually.of_forall hm0)
    (Integrable.of_bound (hm0 x) M0 (Eventually.of_forall fun ω => h0 ω x)) (hm1 x)
    (Eventually.of_forall fun ω y _ => h1 ω y) (integrable_const _)
    (Eventually.of_forall fun ω y _ => (hdiff ω y).hasFDerivAt)

theorem sg_integral_curryLeft {μ : Measure Ω} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (i : ℕ)
    (f : Ω → E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F) :
    ∫ ω, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm (f ω) ∂μ =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm (∫ ω, f ω ∂μ) :=
by
  simpa using LinearIsometry.integral_comp_comm (𝕜 := ℝ)
    (E := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin (i + 1) => E) F) (μ := μ)
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm.toLinearIsometry f

theorem sg_iteratedFDeriv_integral {μ : Measure Ω} [IsFiniteMeasure μ] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : Ω → Euc d → F) (k : ℕ) (hG : ∀ ω, ContDiff ℝ (k : WithTop ℕ∞) (G ω))
    (hbd : ∀ i ≤ k, ∃ M : ℝ, ∀ ω x, ‖iteratedFDeriv ℝ i (G ω) x‖ ≤ M)
    (hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun ω => iteratedFDeriv ℝ i (G ω) x) μ) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∫ ω, G ω x ∂μ) ∧
      ∀ i ≤ k, ∀ x, iteratedFDeriv ℝ i (fun x => ∫ ω, G ω x ∂μ) x =
        ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ := by
  -- one differentiation step
  have step : ∀ i < k, ∀ x, HasFDerivAt (fun x => ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ)
      (∫ ω, fderiv ℝ (iteratedFDeriv ℝ i (G ω)) x ∂μ) x := by
    intro i hi x
    obtain ⟨M0, hM0⟩ := hbd i hi.le
    obtain ⟨M1, hM1⟩ := hbd (i + 1) hi
    refine sg_hasFDerivAt_integral (fun ω => iteratedFDeriv ℝ i (G ω))
      (fun ω => (hG ω).differentiable_iteratedFDeriv (by exact_mod_cast hi)) hM0 (M1 := M1) (fun ω y => ?_)
      (fun y => hmeas i hi.le y) (fun y => ?_) x
    · have e : fderiv ℝ (iteratedFDeriv ℝ i (G ω)) y =
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F
            (iteratedFDeriv ℝ (i + 1) (G ω) y) := by
        rw [iteratedFDeriv_succ_eq_comp_left]; simp
      rw [e, LinearIsometryEquiv.norm_map]; exact hM1 ω y
    · have e : (fun ω => fderiv ℝ (iteratedFDeriv ℝ i (G ω)) y) = fun ω =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F
            (iteratedFDeriv ℝ (i + 1) (G ω) y) := by
        funext ω; rw [iteratedFDeriv_succ_eq_comp_left]; simp
      rw [e]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F).continuous.comp_aestronglyMeasurable (hmeas (i + 1) hi y)
  have hS : ∀ i ≤ k, iteratedFDeriv ℝ i (fun x => ∫ ω, G ω x ∂μ) =
      fun x => ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ := by
    intro i
    induction i with
    | zero =>
      intro _
      funext x
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp]
      have : ∀ ω, iteratedFDeriv ℝ 0 (G ω) x =
          (continuousMultilinearCurryFin0 ℝ (Euc d) F).symm (G ω x) := fun ω => by
        rw [iteratedFDeriv_zero_eq_comp]; rfl
      simp_rw [this]
      exact ((continuousMultilinearCurryFin0 ℝ (Euc d) F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    | succ i ih =>
      intro hi
      funext x
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp, ih (Nat.le_of_succ_le hi),
        (step i hi x).fderiv]
      have : ∀ ω, iteratedFDeriv ℝ (i + 1) (G ω) x =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) F).symm
            (fderiv ℝ (iteratedFDeriv ℝ i (G ω)) x) := fun ω => by
        rw [iteratedFDeriv_succ_eq_comp_left]; rfl
      simp_rw [this]
      exact (sg_integral_curryLeft i _).symm
  refine ⟨?_, fun i hi x => by rw [hS i hi]⟩
  have hk : ∀ i ≤ k, Continuous fun x => ∫ ω, iteratedFDeriv ℝ i (G ω) x ∂μ := by
    intro i hi
    obtain ⟨M0, hM0⟩ := hbd i hi
    exact continuous_of_dominated (bound := fun _ => M0) (fun y => hmeas i hi y)
      (fun y => Eventually.of_forall fun ω => hM0 ω y) (integrable_const _)
      (Eventually.of_forall fun ω => (hG ω).continuous_iteratedFDeriv (by exact_mod_cast hi))
  have key : ContDiff ℝ ((k : ℕ∞) : WithTop ℕ∞) (fun x => ∫ ω, G ω x ∂μ) := by
    refine contDiff_iff_continuous_differentiable.2 ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi' : i ≤ k := by exact_mod_cast hi
      rw [hS i hi']; exact hk i hi'
    · have hi' : i < k := by exact_mod_cast hi
      rw [hS i hi'.le]
      exact fun x => (step i hi' x).differentiableAt
  exact_mod_cast key

/-! ### The semigroup and its derivatives -/

/-- `sg P W q B t h x = ∫ h (flowMap q B (W · ω) t x) dP(ω)`: the transition semigroup of the SDE
`dX = (-q X + B X) dt + √2 dW`, evaluated through the pathwise flow. -/
def sg (P : Measure Ω) (W : ℝ≥0 → Ω → Fin d → ℝ) (q : ℝ) (B : Euc d → Euc d) (t : ℝ)
    (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ ω, h (flowMap q B (fun s => W s ω) t x) ∂P

/-- Differentiation under the integral sign for `∫ h (φ ω x) dP`, with chain rule bounds
`‖D^j (h ∘ φ ω)‖ ≤ j! M D^j` (`D ≥ 1` a common bound of `‖D^i (φ ω)‖`, `1 ≤ i ≤ k`). -/
theorem sg_family {P : Measure Ω} [IsProbabilityMeasure P] {φ : Ω → Euc d → Euc d} {k : ℕ}
    (hφm : Measurable (fun p : Ω × Euc d => φ p.1 p.2))
    (hφ : ∀ ω, ContDiff ℝ (k : WithTop ℕ∞) (φ ω)) {h : Euc d → ℝ}
    (hh : ContDiff ℝ (k : WithTop ℕ∞) h) {M D : ℝ}
    (hM : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) (hD : 1 ≤ D)
    (hφD : ∀ ω x j, 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j (φ ω) x‖ ≤ D) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun x => ∫ ω, h (φ ω x) ∂P) ∧
      (∀ j ≤ k, ∀ x, iteratedFDeriv ℝ j (fun x => ∫ ω, h (φ ω x) ∂P) x =
        ∫ ω, iteratedFDeriv ℝ j (fun y => h (φ ω y)) x ∂P) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ∫ ω, h (φ ω x) ∂P) x‖ ≤
        (k.factorial : ℝ) * M * D ^ k := by
  set G : Ω → Euc d → ℝ := fun ω y => h (φ ω y) with hGdef
  have hGc : ∀ ω, ContDiff ℝ (k : WithTop ℕ∞) (G ω) := fun ω => hh.comp (hφ ω)
  have hGm : StronglyMeasurable (fun p : Ω × Euc d => G p.1 p.2) :=
    (hh.continuous.measurable.comp hφm).stronglyMeasurable
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hpt : ∀ ω x, ∀ j ≤ k, ‖iteratedFDeriv ℝ j (G ω) x‖ ≤ (k.factorial : ℝ) * M * D ^ k := by
    intro ω x j hj
    have h1 : ‖iteratedFDeriv ℝ j (h ∘ φ ω) x‖ ≤ (j.factorial : ℝ) * M * D ^ j :=
      norm_iteratedFDeriv_comp_le (N := (k : WithTop ℕ∞)) hh (hφ ω) (by exact_mod_cast hj) x
        (fun i hi => hM i (hi.trans hj) _)
        (fun i hi1 hi2 => (hφD ω x i hi1 (hi2.trans hj)).trans
          (le_self_pow₀ hD (by omega)))
    refine h1.trans ?_
    have hf1 : (j.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hj
    have hp1 : D ^ j ≤ D ^ k := pow_le_pow_right₀ hD hj
    have hp0 : 0 ≤ D ^ j := by positivity
    calc (j.factorial : ℝ) * M * D ^ j ≤ (k.factorial : ℝ) * M * D ^ j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf1 hM0) hp0
      _ ≤ (k.factorial : ℝ) * M * D ^ k :=
          mul_le_mul_of_nonneg_left hp1 (by positivity)
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun ω => iteratedFDeriv ℝ i (G ω) x) P := by
    intro i hi x
    have := sg_stronglyMeasurable_iteratedFDeriv G hGm i
      (fun ω => (hGc ω).of_le (by exact_mod_cast hi))
    exact (this.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  obtain ⟨hcd, hform⟩ := sg_iteratedFDeriv_integral (μ := P) G k hGc
    (fun i hi => ⟨_, fun ω x => hpt ω x i hi⟩) hmeas
  refine ⟨hcd, hform, fun j hj x => ?_⟩
  rw [hform j hj x]
  have := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => iteratedFDeriv ℝ j (G ω) x) (C := (k.factorial : ℝ) * M * D ^ k)
    (Eventually.of_forall fun ω => hpt ω x j hj)
  simpa using this

/-- **POIS-SG, smoothness.**  For `h ∈ C^k` with `‖D^i h‖ ≤ M` (`i ≤ k ≤ m`), `sg t h` is `C^k`, its
derivatives are the integrals of the derivatives of `h ∘ flowMap`, and they are bounded by `C M`,
`C` depending only on `(d, q, Mb, m, T)`, for all `t ∈ [0,T]`. -/
theorem sg_contDiff (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (T : ℝ) (hT : 0 ≤ T) (k : ℕ)
    (hk : k ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : ℝ≥0 → Ω → Fin d → ℝ), SgNoise W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ h : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) h → ∀ M : ℝ,
      (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) → ∀ t ∈ Icc (0 : ℝ) T,
        ContDiff ℝ (k : WithTop ℕ∞) (sg P W q B t h) ∧
        (∀ j ≤ k, ∀ x, iteratedFDeriv ℝ j (sg P W q B t h) x =
          ∫ ω, iteratedFDeriv ℝ j (fun y => h (flowMap q B (fun s => W s ω) t y)) x ∂P) ∧
        ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (sg P W q B t h) x‖ ≤ C * M := by
  obtain ⟨C0, hC0, hflow⟩ := pois_flow (d := d) q Mb hq m hm T hT
  set D : ℝ := max 1 C0 with hDdef
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨(m.factorial : ℝ) * D ^ m, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast m.factorial_pos
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ hD1)
  intro Ω _ P _ W hW B hB h hh M hM t ht
  have hfl := fun ω => hflow B hB (fun s => W s ω) (hW.cont ω) (hW.zero ω)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  obtain ⟨h1, h2, h3⟩ := sg_family (P := P) (k := k)
    (φ := fun ω => flowMap q B (fun s => W s ω) t)
    (sg_measurable_flowMap hW hq.le (by omega) hB ht.1)
    (fun ω => ((hfl ω).2 t ht).1.of_le (by exact_mod_cast hk)) hh hM hD1
    (fun ω x j hj1 hjk => (((hfl ω).2 t ht).2 j hj1 (hjk.trans hk) x).trans (le_max_right _ _))
  refine ⟨h1, h2, fun j hj x => (h3 j hj x).trans ?_⟩
  have hf : (k.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hk
  have hp : D ^ k ≤ D ^ m := pow_le_pow_right₀ hD1 hk
  calc (k.factorial : ℝ) * M * D ^ k ≤ (m.factorial : ℝ) * M * D ^ m :=
        mul_le_mul (mul_le_mul_of_nonneg_right hf hM0) hp (by positivity) (by positivity)
    _ = (m.factorial : ℝ) * D ^ m * M := by ring

/-- **POIS-SG, Lipschitz bound.**  `‖D (sg t h)‖ ≤ e^{(q+Mb) t} ‖Dh‖` for `h ∈ C^1` with bounded `h`
and `Dh`, `t ≥ 0`.  (`Mb ≥ 0` follows from `HasCbBound`.) -/
theorem sg_fderiv_bound (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → Fin d → ℝ)
    (hW : SgNoise W) (B : Euc d → Euc d) (hB : HasCbBound m Mb B) (h : Euc d → ℝ)
    (hh : ContDiff ℝ (1 : WithTop ℕ∞) h) (M0 M1 : ℝ) (hM0 : ∀ y, ‖h y‖ ≤ M0)
    (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1) (t : ℝ) (ht : 0 ≤ t) (x : Euc d) :
    ‖fderiv ℝ (sg P W q B t h) x‖ ≤ Real.exp ((q + Mb) * t) * M1 := by
  have hMb : 0 ≤ Mb := by
    have := hB.2 0 (Nat.zero_le _) 0
    exact (norm_nonneg _).trans this
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hΛ : 0 ≤ q + |Mb| := by positivity
  have hex : 1 ≤ Real.exp ((q + |Mb|) * t) := Real.one_le_exp (by positivity)
  have hHyp : ∀ ω, PfHyp q Mb (n + 1) B (fun s => W s ω) := fun ω =>
    ⟨hq.le, by omega, hB, hW.cont ω, hW.zero ω⟩
  have htT : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hfd : ∀ ω x, ‖fderiv ℝ (flowMap q B (fun s => W s ω) t) x‖ ≤
      Real.exp ((q + |Mb|) * t) := by
    intro ω x
    have hb := pf_isDriftBounds (hHyp ω) t
    have hΨ := pf_isNegDriftFlow (hHyp ω) ht
    have := FlowB.flow_fderiv_bound ht hb hΨ t htT x
    have e : flowMap q B (fun s => W s ω) t = fun x =>
        pfZ q B (fun s => W s ω) x t + Real.sqrt 2 • ouShift q (fun s => W s ω) t := rfl
    rw [e, fderiv_add_const]
    exact this
  have hfc : ∀ ω, ContDiff ℝ (1 : WithTop ℕ∞) (flowMap q B (fun s => W s ω) t) := fun ω => by
    have := FlowB.flow_contDiff ht (pf_isDriftBounds (hHyp ω) t) (pf_isNegDriftFlow (hHyp ω) ht)
      t htT
    have e : flowMap q B (fun s => W s ω) t = fun x =>
        pfZ q B (fun s => W s ω) x t + Real.sqrt 2 • ouShift q (fun s => W s ω) t := rfl
    rw [e]
    exact (this.add contDiff_const).of_le (by exact_mod_cast Nat.le_add_left 1 n)
  obtain ⟨h1, h2, _⟩ := sg_family (P := P) (k := 1) (M := max M0 M1)
    (φ := fun ω => flowMap q B (fun s => W s ω) t) (h := h)
    (sg_measurable_flowMap hW hq.le (by omega) hB ht) hfc hh
    (fun i hi y => by
      interval_cases i
      · rw [norm_iteratedFDeriv_zero]; exact (hM0 y).trans (le_max_left _ _)
      · rw [norm_iteratedFDeriv_one]; exact (hM1 y).trans (le_max_right _ _))
    hex (fun ω x j hj1 hj2 => by
      obtain rfl : j = 1 := le_antisymm hj2 hj1
      rw [norm_iteratedFDeriv_one]; exact hfd ω x)
  have hM1nn : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hpt : ∀ ω, ‖iteratedFDeriv ℝ 1 (fun y => h (flowMap q B (fun s => W s ω) t y)) x‖ ≤
      Real.exp ((q + |Mb|) * t) * M1 := by
    intro ω
    rw [norm_iteratedFDeriv_one]
    have hdh : DifferentiableAt ℝ h (flowMap q B (fun s => W s ω) t x) :=
      (hh.differentiable (by norm_num)) _
    have hdf : DifferentiableAt ℝ (flowMap q B (fun s => W s ω) t) x :=
      ((hfc ω).differentiable (by norm_num)) x
    have e : fderiv ℝ (fun y => h (flowMap q B (fun s => W s ω) t y)) x =
        (fderiv ℝ h (flowMap q B (fun s => W s ω) t x)).comp
          (fderiv ℝ (flowMap q B (fun s => W s ω) t) x) := fderiv_comp x hdh hdf
    rw [e]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [mul_comm]
    exact mul_le_mul (hfd ω x) (hM1 _) (norm_nonneg _) (Real.exp_pos _).le
  calc ‖fderiv ℝ (sg P W q B t h) x‖ = ‖iteratedFDeriv ℝ 1 (sg P W q B t h) x‖ :=
        (norm_iteratedFDeriv_one (𝕜 := ℝ) (f := sg P W q B t h) (x := x)).symm
    _ = ‖∫ ω, iteratedFDeriv ℝ 1 (fun y => h (flowMap q B (fun s => W s ω) t y)) x ∂P‖ := by
        exact congrArg norm (h2 1 le_rfl x)
    _ ≤ Real.exp ((q + |Mb|) * t) * M1 := by
        have := norm_integral_le_of_norm_le_const (μ := P)
          (f := fun ω => iteratedFDeriv ℝ 1 (fun y => h (flowMap q B (fun s => W s ω) t y)) x)
          (C := Real.exp ((q + |Mb|) * t) * M1) (Eventually.of_forall hpt)
        simpa using this
    _ = Real.exp ((q + Mb) * t) * M1 := by rw [abs_of_nonneg hMb]

/-! ### Second moment of the flow -/

/-- Cauchy-Schwarz on `[0,t]`: `(∫ f)² ≤ t ∫ f²` for continuous `f`. -/
theorem sg_cs {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, f s) ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  rcases ht.eq_or_lt with rfl | htp
  · simp
  set I := ∫ s in (0 : ℝ)..t, f s with hI
  set J := ∫ s in (0 : ℝ)..t, f s ^ 2 with hJ
  have hf1 : IntervalIntegrable f volume 0 t := hf.intervalIntegrable _ _
  have hf2 : IntervalIntegrable (fun s => f s ^ 2) volume 0 t :=
    (hf.pow 2).intervalIntegrable _ _
  have key : ∀ c : ℝ, 0 ≤ J - 2 * c * I + c ^ 2 * t := by
    intro c
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..t, (f s - c) ^ 2 :=
      intervalIntegral.integral_nonneg htp.le fun s _ => sq_nonneg _
    have e : (fun s => (f s - c) ^ 2) = fun s => f s ^ 2 - (2 * c) * f s + c ^ 2 := by
      funext s; ring
    rw [e, intervalIntegral.integral_add (hf2.sub (hf1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf1.const_mul _), intervalIntegral.integral_const_mul]
      at h0
    simpa [hI, hJ, mul_comm, mul_left_comm] using h0
  have := key (I / t)
  have h2 : I ^ 2 ≤ t * J := by
    have e : J - 2 * (I / t) * I + (I / t) ^ 2 * t = J - I ^ 2 / t := by
      field_simp; ring
    rw [e] at this
    have : I ^ 2 / t ≤ J := by linarith
    rwa [div_le_iff₀ htp, mul_comm] at this
  exact h2

/-- Pathwise bound `‖U_t‖² ≤ 2‖w_t‖² + 2 q² t ∫_0^t ‖w_s‖² ds` for the OU shift. -/
theorem sg_ou_sq_le {q : ℝ} (hq : 0 ≤ q) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖ouShift q w t‖ ^ 2 ≤ 2 * ‖pfPath w t‖ ^ 2 +
      2 * q ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖pfPath w s‖ ^ 2 := by
  have hP : Continuous (pfPath w) := pf_continuous_path hw
  have hPn : Continuous fun s => ‖pfPath w s‖ := hP.norm
  set a := ∫ s in (0 : ℝ)..t, ‖pfPath w s‖ with ha
  have hcont : Continuous fun s : ℝ => Real.exp (-q * (t - s)) • pfPath w s :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).smul hP
  have h1 : ‖∫ s in (0 : ℝ)..t, Real.exp (-q * (t - s)) • pfPath w s‖ ≤ a := by
    refine (intervalIntegral.norm_integral_le_integral_norm ht).trans ?_
    refine intervalIntegral.integral_mono_on ht (hcont.norm.intervalIntegrable _ _)
      (hPn.intervalIntegrable _ _) fun s hs => ?_
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have : Real.exp (-q * (t - s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hs.2, hq])
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have h2 : ‖ouShift q w t‖ ≤ ‖pfPath w t‖ + q * a := by
    unfold ouShift
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hq]
    exact add_le_add_right (mul_le_mul_of_nonneg_left h1 hq) _
  have h3 : a ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, ‖pfPath w s‖ ^ 2 := sg_cs hPn ht
  have h4 : ‖ouShift q w t‖ ^ 2 ≤ (‖pfPath w t‖ + q * a) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h5 : (‖pfPath w t‖ + q * a) ^ 2 ≤ 2 * ‖pfPath w t‖ ^ 2 + 2 * (q * a) ^ 2 := by
    nlinarith [sq_nonneg (‖pfPath w t‖ - q * a)]
  have h6 : 2 * (q * a) ^ 2 ≤ 2 * q ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖pfPath w s‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * q ^ 2)
    nlinarith [this]
  linarith

/-- Uniform (in the noise path) growth bound of the random ODE: `‖Z_t(x)‖ ≤ e^{qt}(‖x‖ + Mb/q)`. -/
theorem sg_Z_bound {q Mb : ℝ} {m : ℕ} {B : Euc d → Euc d} {w : ℝ≥0 → Fin d → ℝ}
    (H : PfHyp q Mb m B w) (hq : 0 < q) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    ‖pfZ q B w x t‖ ≤ Real.exp (q * t) * (‖x‖ + Mb / q) := by
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (H.hB.2 0 (Nat.zero_le _) 0)
  have hB0 : ∀ y, ‖B y‖ ≤ Mb := fun y => by
    have := H.hB.2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hder : ∀ τ ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt (pfZ q B w x) (pfDrift q B w τ (pfZ q B w x τ)) (Ici τ) τ := by
    intro τ hτ
    have h := pf_hasDerivWithinAt_of_integral (T := t)
      (F := fun s => pfDrift q B w s (pfZ q B w x s)) (pf_continuousOn_drift H x ht)
      (fun r hr => pf_Z_eq H x hr.1) τ ⟨hτ.1, hτ.2.le⟩
    refine h.mono_of_mem_nhdsWithin ?_
    exact mem_of_superset (Icc_mem_nhdsGE hτ.2) (Icc_subset_Icc_left hτ.1)
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := pfZ q B w x)
    (f' := fun s => pfDrift q B w s (pfZ q B w x s)) (δ := ‖x‖) (K := q) (ε := Mb)
    (a := 0) (b := t) (pf_Z_cont H x ht) hder (by rw [pf_Z_zero H x]) (fun s hs => by
      unfold pfDrift
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_neg, Real.norm_of_nonneg hq.le]
      linarith [hB0 (pfZ q B w x s + Real.sqrt 2 • ouShift q w s)]) t ⟨ht, le_rfl⟩
  simp only [gronwallBound, hq.ne', ite_false, sub_zero] at hG
  refine hG.trans ?_
  have : 0 ≤ Mb / q := div_nonneg hMb hq.le
  nlinarith [Real.exp_pos (q * t), mul_nonneg this (Real.exp_pos (q * t)).le]

/-! ### Brownian input -/

theorem sgNoise_of_brownian {P : Measure Ω} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W) : SgNoise W where
  meas := hW.measurable
  cont := hW.cont
  zero := hW.zero

/-- Squared norm of the noise at time `s`. -/
def sgN (W : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ) (ω : Ω) : ℝ := ‖pfPath (fun r => W r ω) s‖ ^ 2

theorem sg_N_eq (W : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ) (ω : Ω) :
    sgN W s ω = ∑ k, (W s.toNNReal ω k) ^ 2 := by
  simp [sgN, pfPath, EuclideanSpace.norm_sq_eq]

theorem sg_N_integral {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : IsBrownianFiltration P ℱ W) (s : ℝ) :
    Integrable (sgN W s) P ∧ ∫ ω, sgN W s ω ∂P = d * (s.toNNReal : ℝ) := by
  have hmem : ∀ k, MemLp (fun ω => W s.toNNReal ω k) 2 P := fun k =>
    hW.memLp_coord s.toNNReal k (by norm_num)
  have e : sgN W s = fun ω => ∑ k, (W s.toNNReal ω k) ^ 2 := funext (sg_N_eq W s)
  rw [e]
  refine ⟨integrable_finset_sum _ fun k _ => (hmem k).integrable_sq, ?_⟩
  rw [integral_finset_sum _ fun k _ => (hmem k).integrable_sq]
  have : ∀ k : Fin d, ∫ ω, (W s.toNNReal ω k) ^ 2 ∂P = (s.toNNReal : ℝ) := fun k => by
    have := (hW.hasLaw_coord s.toNNReal k).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [integral_sq_gaussianReal_zero] at this
    exact this
  simp [this]

theorem sg_Psi {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..t, sgN W s ω) P ∧
      ∫ ω, (∫ s in (0 : ℝ)..t, sgN W s ω) ∂P ≤ d * t ^ 2 := by
  have hn := sgNoise_of_brownian hW
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) t) with hν
  have hNm : Measurable (fun p : Ω × ℝ => sgN W p.2 p.1) :=
    (((sg_meas_pfPath hn).comp measurable_swap).norm).pow_const 2
  have hNc : ∀ ω, Continuous fun s => sgN W s ω := fun ω =>
    (pf_continuous_path (hn.cont ω)).norm.pow 2
  have hcoef : Continuous fun s : ℝ => (d : ℝ) * (s.toNNReal : ℝ) :=
    continuous_const.mul (NNReal.continuous_coe.comp continuous_real_toNNReal)
  have hint : Integrable (fun p : Ω × ℝ => sgN W p.2 p.1) (P.prod ν) := by
    rw [integrable_prod_iff' hNm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun s => (sg_N_integral hW s).1, ?_⟩
    have : (fun s : ℝ => ∫ ω, ‖sgN W s ω‖ ∂P) = fun s => (d : ℝ) * (s.toNNReal : ℝ) := by
      funext s
      rw [← (sg_N_integral hW s).2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [Real.norm_eq_abs]
        exact abs_of_nonneg (by unfold sgN; positivity))
    rw [this]
    exact hcoef.integrableOn_Ioc
  have hP1 : (fun ω => ∫ s in (0 : ℝ)..t, sgN W s ω) = fun ω => ∫ s, sgN W s ω ∂ν := by
    funext ω; rw [intervalIntegral.integral_of_le ht]
  rw [hP1]
  refine ⟨hint.integral_prod_left, ?_⟩
  have hswap := integral_integral_swap (μ := P) (ν := ν) (f := fun ω s => sgN W s ω) hint
  rw [hswap]
  have h1 : ∀ s, ∫ ω, sgN W s ω ∂P = (d : ℝ) * (s.toNNReal : ℝ) := fun s => (sg_N_integral hW s).2
  simp_rw [h1]
  calc ∫ s, (d : ℝ) * (s.toNNReal : ℝ) ∂ν ≤ ∫ s, (d : ℝ) * t ∂ν := by
        refine setIntegral_mono_on hcoef.integrableOn_Ioc (integrableOn_const (by simp))
          measurableSet_Ioc fun s hs => ?_
        have : (s.toNNReal : ℝ) ≤ t := by
          rw [Real.coe_toNNReal _ hs.1.le]; exact hs.2
        exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
    _ = (d : ℝ) * t ^ 2 := by
        rw [integral_const, hν]
        simp [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal ht]
        ring

/-- **POIS-SG, second moment.**  For a Brownian filtration, `‖flowMap t x‖²` is integrable and
`E ‖flowMap t x‖² ≤ C (1 + ‖x‖²)` for `t ∈ [0,T]`, with `C` depending only on `(d, q, Mb, T)`
(not on `m`, `B`, the probability space). -/
theorem sg_second_moment (q Mb : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ m : ℕ, 1 ≤ m → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Euc d,
        Integrable (fun ω => ‖flowMap q B (fun s => W s ω) t x‖ ^ 2) P ∧
        ∫ ω, ‖flowMap q B (fun s => W s ω) t x‖ ^ 2 ∂P ≤ C * (1 + ‖x‖ ^ 2) := by
  set c : ℝ := Mb / q with hc
  set A : ℝ := 4 * Real.exp (2 * q * T) * (1 + c ^ 2) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A + 8 * d * T + 8 * q ^ 2 * T * (d * T ^ 2) + 1, by positivity, ?_⟩
  intro Ω mΩ P _ ℱ W hW m hm B hB t ht x
  have hn := sgNoise_of_brownian hW
  have hH : ∀ ω, PfHyp q Mb m B (fun s => W s ω) := fun ω =>
    ⟨hq.le, hm, hB, hn.cont ω, hn.zero ω⟩
  set Ψ : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..t, sgN W s ω with hΨ
  have hΨnn : ∀ ω, 0 ≤ Ψ ω := fun ω =>
    intervalIntegral.integral_nonneg ht.1 fun s _ => by unfold sgN; positivity
  set g : Ω → ℝ := fun ω => 4 * Real.exp (2 * q * T) * (‖x‖ ^ 2 + c ^ 2) + 8 * sgN W t ω +
    8 * q ^ 2 * T * Ψ ω with hg
  have hpt : ∀ ω, ‖‖flowMap q B (fun s => W s ω) t x‖ ^ 2‖ ≤ g ω := by
    intro ω
    rw [Real.norm_of_nonneg (by positivity)]
    have hZ := sg_Z_bound (hH ω) hq x ht.1
    have hU := sg_ou_sq_le hq.le (hn.cont ω) ht.1
    have hZ0 : 0 ≤ ‖pfZ q B (fun s => W s ω) x t‖ := norm_nonneg _
    have hZsq : ‖pfZ q B (fun s => W s ω) x t‖ ^ 2 ≤
        Real.exp (2 * q * T) * (2 * ‖x‖ ^ 2 + 2 * c ^ 2) := by
      calc ‖pfZ q B (fun s => W s ω) x t‖ ^ 2
          ≤ (Real.exp (q * t) * (‖x‖ + c)) ^ 2 := pow_le_pow_left₀ hZ0 hZ 2
        _ = Real.exp (2 * q * t) * (‖x‖ + c) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
        _ ≤ Real.exp (2 * q * T) * (2 * ‖x‖ ^ 2 + 2 * c ^ 2) := by
          have h1 : Real.exp (2 * q * t) ≤ Real.exp (2 * q * T) :=
            Real.exp_le_exp.2 (by nlinarith [ht.2])
          have h2 : (‖x‖ + c) ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * c ^ 2 := by
            nlinarith [sq_nonneg (‖x‖ - c)]
          exact mul_le_mul h1 h2 (sq_nonneg _) (Real.exp_pos _).le
    have hUsq : ‖ouShift q (fun s => W s ω) t‖ ^ 2 ≤ 2 * sgN W t ω + 2 * q ^ 2 * T * Ψ ω := by
      refine hU.trans ?_
      have : 2 * q ^ 2 * t * ∫ s in (0 : ℝ)..t, ‖pfPath (fun r => W r ω) s‖ ^ 2 ≤
          2 * q ^ 2 * T * Ψ ω :=
        mul_le_mul_of_nonneg_right (by nlinarith [ht.2, sq_nonneg q]) (hΨnn ω)
      simp only [sgN]
      linarith
    have hsplit : ‖flowMap q B (fun s => W s ω) t x‖ ^ 2 ≤
        2 * ‖pfZ q B (fun s => W s ω) x t‖ ^ 2 +
          2 * ‖Real.sqrt 2 • ouShift q (fun s => W s ω) t‖ ^ 2 := by
      have := norm_add_le (pfZ q B (fun s => W s ω) x t)
        (Real.sqrt 2 • ouShift q (fun s => W s ω) t)
      have h0 : 0 ≤ ‖flowMap q B (fun s => W s ω) t x‖ := norm_nonneg _
      have h1 : ‖flowMap q B (fun s => W s ω) t x‖ ≤
          ‖pfZ q B (fun s => W s ω) x t‖ + ‖Real.sqrt 2 • ouShift q (fun s => W s ω) t‖ := this
      nlinarith [sq_nonneg (‖pfZ q B (fun s => W s ω) x t‖ -
        ‖Real.sqrt 2 • ouShift q (fun s => W s ω) t‖), pow_le_pow_left₀ h0 h1 2]
    have hsq : ‖Real.sqrt 2 • ouShift q (fun s => W s ω) t‖ ^ 2 =
        2 * ‖ouShift q (fun s => W s ω) t‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
    rw [hsq] at hsplit
    nlinarith [hZsq, hUsq, hsplit]
  have hmeas : Measurable fun ω => ‖flowMap q B (fun s => W s ω) t x‖ ^ 2 :=
    (((sg_measurable_flowMap hn hq.le hm hB ht.1).comp
      (measurable_id.prodMk measurable_const)).norm).pow_const 2
  obtain ⟨hNi, hNe⟩ := sg_N_integral hW t
  obtain ⟨hΨi, hΨe⟩ := sg_Psi hW ht.1
  have hgi : Integrable g P :=
    ((integrable_const _).add (hNi.const_mul 8)).add (hΨi.const_mul _)
  refine ⟨hgi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall hpt), ?_⟩
  have hint : ∫ ω, ‖flowMap q B (fun s => W s ω) t x‖ ^ 2 ∂P ≤ ∫ ω, g ω ∂P :=
    integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) hgi
      (Eventually.of_forall fun ω => by simpa [Real.norm_of_nonneg (sq_nonneg _)] using hpt ω)
  refine hint.trans ?_
  have e1 : ∫ ω, g ω ∂P = 4 * Real.exp (2 * q * T) * (‖x‖ ^ 2 + c ^ 2) +
      8 * ∫ ω, sgN W t ω ∂P + 8 * q ^ 2 * T * ∫ ω, Ψ ω ∂P := by
    have i0 : Integrable (fun ω : Ω => 8 * sgN W t ω) P := hNi.const_mul 8
    have i1 : Integrable (fun ω : Ω => 4 * Real.exp (2 * q * T) * (‖x‖ ^ 2 + c ^ 2) +
        8 * sgN W t ω) P := (integrable_const _).add i0
    have i2 : Integrable (fun ω : Ω => 8 * q ^ 2 * T * Ψ ω) P := hΨi.const_mul _
    simp only [hg]
    rw [integral_add i1 i2, integral_add (integrable_const _) i0]
    simp [integral_const_mul]
  rw [e1, hNe, Real.coe_toNNReal _ ht.1]
  have hΨ' : ∫ ω, Ψ ω ∂P ≤ d * T ^ 2 := hΨe.trans
    (mul_le_mul_of_nonneg_left (by nlinarith [ht.1, ht.2]) (Nat.cast_nonneg _))
  have hq2 : 0 ≤ 8 * q ^ 2 * T := by positivity
  have h1 : 8 * (d * t) ≤ 8 * d * T := by
    nlinarith [ht.2, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h2 := mul_le_mul_of_nonneg_left hΨ' hq2
  have hx : 4 * Real.exp (2 * q * T) * (‖x‖ ^ 2 + c ^ 2) ≤ A * (1 + ‖x‖ ^ 2) := by
    have : 0 ≤ Real.exp (2 * q * T) := (Real.exp_pos _).le
    simp only [hA]
    nlinarith [mul_nonneg this (sq_nonneg ‖x‖), mul_nonneg this (sq_nonneg c),
      mul_nonneg (mul_nonneg this (sq_nonneg c)) (sq_nonneg ‖x‖)]
  have hone : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hK : 0 ≤ 8 * (d : ℝ) * T + 8 * q ^ 2 * T * (d * T ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hone hK]

end HRS.MS.PoisSg
