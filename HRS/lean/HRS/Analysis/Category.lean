import Mathlib

/-!
# Real-analysis lemmas used in the sharpness statements

Sources (HRS periodic main paper):
* Lemma 4.20 `M:V:lem:response-category` (source lines 5386-5395): a Baire-category
  lemma for sequences of continuous functions with interval-averaged lower bounds.
* Lemma C.6 `M:B:lem:sqrt-lipschitz` (12311-12313): square roots of nonnegative `C^{1,1}`
  functions are Lipschitz, `‖∇√a‖_∞ ≤ (‖∇²a‖_∞/2)^{1/2}`.
* Proposition 3.10 `M:B:prop:hadamard` (1778-1786), the lattice-supremum identity
  `sup_k ⟨k⟩^{m'-m} e^{4π² c (2π|k|)^{s-d} (kᵀ S k) τ} = ∞`, isolated here as a pure
  analysis statement (`hadamard_sup_eq_top`); the connection with the zero-temperature
  adjoint equation is package ADJ-03.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace HRS

/-- Lemma 4.20 in the form that the manuscript's proof actually gives: a dense `G_δ` set `R ⊆ (a,b)`
of points `θ` with `f_N θ > q/2` for arbitrarily large `N` (so `limsup_N f_N θ ≥ q/2` in `EReal`).
This frequent form implies the `EReal` limsup statement `response_category` below. -/
theorem response_category_freq (a b : ℝ) (hab : a < b) (f : ℕ → ℝ → ℝ)
    (hcont : ∀ N, ContinuousOn (f N) (Set.Ioo a b))
    (hnonneg : ∀ N, ∀ θ ∈ Set.Ioo a b, 0 ≤ f N θ)
    (q : ℝ) (hq : 0 < q)
    (havg : ∀ c d, a < c → c < d → d < b →
      ((q : ℝ) : EReal) ≤ liminf (fun N => (((d - c)⁻¹ * ∫ θ in c..d, f N θ : ℝ) : EReal)) atTop) :
    ∃ R : Set ℝ, R ⊆ Set.Ioo a b ∧ IsGδ R ∧ Set.Ioo a b ⊆ closure R ∧
      ∀ θ ∈ R, ∀ L : ℕ, ∃ N, L ≤ N ∧ q / 2 < f N θ := by
  set O : ℕ → Set ℝ := fun L => ⋃ N ∈ {N : ℕ | L ≤ N}, (Set.Ioo a b ∩ f N ⁻¹' Set.Ioi (q / 2)) with hO
  have hOopen : ∀ L, IsOpen (O L) := by
    intro L
    refine isOpen_biUnion fun N _ => ?_
    exact (hcont N).isOpen_inter_preimage isOpen_Ioo isOpen_Ioi
  have hOsub : ∀ L, O L ⊆ Set.Ioo a b := by
    intro L θ hθ
    simp only [hO, Set.mem_iUnion] at hθ
    obtain ⟨N, _, h, _⟩ := hθ
    exact h
  -- density of O L in Ioo
  have hOdense : ∀ L, Set.Ioo a b ⊆ closure (O L) := by
    intro L θ hθ
    rw [mem_closure_iff]
    intro U hU hθU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.inter isOpen_Ioo) θ ⟨hθU, hθ⟩
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = θ - ε / 2 := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = θ + ε / 2 := ⟨_, rfl⟩
    have hsub : Set.Icc c d ⊆ U ∩ Set.Ioo a b := by
      intro x hx
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hac : a < c := (hsub (Set.left_mem_Icc.2 (by linarith))).2.1
    have hdb : d < b := (hsub (Set.right_mem_Icc.2 (by linarith))).2.2
    have hcd : c < d := by linarith
    have hint : ∀ N, IntervalIntegrable (f N) MeasureTheory.volume c d := fun N =>
      ((hcont N).mono (fun x hx => (hsub (Set.uIcc_of_le hcd.le ▸ hx)).2)).intervalIntegrable
    have hev : ∀ᶠ N in atTop, q / 2 < (d - c)⁻¹ * ∫ θ in c..d, f N θ := by
      have hlt : ((q / 2 : ℝ) : EReal) <
          liminf (fun N => (((d - c)⁻¹ * ∫ θ in c..d, f N θ : ℝ) : EReal)) atTop :=
        lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (half_lt_self hq)) (havg c d hac hcd hdb)
      filter_upwards [eventually_lt_of_lt_liminf hlt] with N hN
      exact EReal.coe_lt_coe_iff.1 hN
    obtain ⟨N, hN, hLN⟩ := (hev.and (eventually_ge_atTop L)).exists
    by_contra hnone
    have hle : ∀ x ∈ Set.Icc c d, f N x ≤ q / 2 := by
      intro x hx
      by_contra hlt
      push Not at hlt
      apply hnone
      refine ⟨x, (hsub hx).1, ?_⟩
      simp only [hO, Set.mem_iUnion]
      exact ⟨N, hLN, (hsub hx).2, hlt⟩
    have h1 : ∫ θ in c..d, f N θ ≤ ∫ θ in c..d, q / 2 :=
      intervalIntegral.integral_mono_on hcd.le (hint N) (by simp) hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have hdc : 0 < d - c := by linarith
    have : (d - c)⁻¹ * ∫ θ in c..d, f N θ ≤ q / 2 := by
      calc _ ≤ (d - c)⁻¹ * ((d - c) * (q / 2)) := by gcongr
        _ = q / 2 := by field_simp
    linarith
  refine ⟨⋂ L, O L, ?_, ?_, ?_, ?_⟩
  · exact (Set.iInter_subset _ 0).trans (hOsub 0)
  · exact IsGδ.iInter_of_isOpen hOopen
  · -- density
    set U : ℕ → Set ℝ := fun L => O L ∪ (Set.Icc a b)ᶜ with hU
    have hUopen : ∀ L, IsOpen (U L) := fun L => (hOopen L).union isClosed_Icc.isOpen_compl
    have hUdense : ∀ L, Dense (U L) := by
      intro L
      rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
      intro x
      by_cases hx : x ∈ Set.Icc a b
      · have : Set.Icc a b ⊆ closure (O L) := by
          calc Set.Icc a b ⊆ closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]
            _ ⊆ closure (closure (O L)) := closure_mono (hOdense L)
            _ = closure (O L) := closure_closure
        exact closure_mono Set.subset_union_left (this hx)
      · exact subset_closure (Or.inr hx)
    have hD := dense_iInter_of_isOpen_nat hUopen hUdense
    have h2 := hD.open_subset_closure_inter (isOpen_Ioo (a := a) (b := b))
    refine h2.trans (closure_mono ?_)
    intro x ⟨hx1, hx2⟩
    simp only [Set.mem_iInter] at hx2 ⊢
    intro L
    rcases hx2 L with h | h
    · exact h
    · exact absurd (Set.Ioo_subset_Icc_self hx1) h
  · intro θ hθ L
    have := Set.mem_iInter.1 hθ L
    simp only [hO, Set.mem_iUnion] at this
    obtain ⟨N, hN, _, h⟩ := this
    exact ⟨N, hN, h⟩

/-- Lemma 4.20 `M:V:lem:response-category` (lines 5386-5395): let `I = (a,b)` be an open bounded
interval and `f_N : I → [0,∞)` continuous. If some `q > 0` satisfies
`liminf_N |J|⁻¹ ∫_J f_N ≥ q` for every closed nondegenerate interval `J ⊂ I`, then a dense
`G_δ` subset of `I` consists of points where `limsup_N f_N ≥ q/2`.

The `liminf` and `limsup` are taken in `EReal`, as in the source (values in `[0,∞]`); the real
`liminf`/`limsup` of Mathlib take junk values on unbounded sequences and would change the
statement (docs/ISSUES.md, item on Lemma 4.20). "Dense in `I`" is `I ⊆ closure R` with `R ⊆ I`;
a `G_δ` subset of the open set `I` is the same as a `G_δ` subset of `ℝ` contained in `I`. -/
theorem response_category (a b : ℝ) (hab : a < b) (f : ℕ → ℝ → ℝ)
    (hcont : ∀ N, ContinuousOn (f N) (Set.Ioo a b))
    (hnonneg : ∀ N, ∀ θ ∈ Set.Ioo a b, 0 ≤ f N θ)
    (q : ℝ) (hq : 0 < q)
    (havg : ∀ c d, a < c → c < d → d < b →
      ((q : ℝ) : EReal) ≤ liminf (fun N => (((d - c)⁻¹ * ∫ θ in c..d, f N θ : ℝ) : EReal)) atTop) :
    ∃ R : Set ℝ, R ⊆ Set.Ioo a b ∧ IsGδ R ∧ Set.Ioo a b ⊆ closure R ∧
      ∀ θ ∈ R, ((q / 2 : ℝ) : EReal) ≤ limsup (fun N => ((f N θ : ℝ) : EReal)) atTop := by
  obtain ⟨R, h1, h2, h3, h4⟩ := response_category_freq a b hab f hcont hnonneg q hq havg
  refine ⟨R, h1, h2, h3, fun θ hθ => ?_⟩
  refine Filter.le_limsup_of_frequently_le ?_
  rw [Filter.frequently_atTop]
  intro L
  obtain ⟨N, hN, hlt⟩ := h4 θ hθ L
  exact ⟨N, hN, EReal.coe_le_coe_iff.2 hlt.le⟩

section Sqrt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma sqrtLip_taylor (a : E → ℝ) (ha : ContDiff ℝ 1 a) (L : ℝ) (hL : 0 ≤ L)
    (hlip : LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ a x)) (x h : E) :
    a (x + h) ≤ a x + fderiv ℝ a x h + L / 2 * ‖h‖ ^ 2 := by
  have hda : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => a (x + t • h)) (fderiv ℝ a (x + t • h) h) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    exact (hda (x + t • h)).hasFDerivAt.comp_hasDerivAt t h1
  set φ : ℝ → ℝ := fun t => a (x + t • h) - t * fderiv ℝ a x h - L / 2 * t ^ 2 * ‖h‖ ^ 2 with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ
      (fderiv ℝ a (x + t • h) h - fderiv ℝ a x h - L * t * ‖h‖ ^ 2) t := by
    intro t
    have := (((hd t).sub ((hasDerivAt_id t).mul_const (fderiv ℝ a x h))).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖h‖ ^ 2)))
    exact this.congr_deriv (by simp only [id, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, one_mul]; ring)
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hφd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hφd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφd t).deriv]
      have h0 : 0 ≤ t := ht.1.le
      have h1 : dist (fderiv ℝ a (x + t • h)) (fderiv ℝ a x) ≤ L * (t * ‖h‖) := by
        have := hlip.dist_le_mul (x + t • h) x
        simpa [Real.coe_toNNReal _ hL, dist_eq_norm, norm_smul, abs_of_nonneg h0] using this
      have h2 : fderiv ℝ a (x + t • h) h - fderiv ℝ a x h ≤ L * (t * ‖h‖) * ‖h‖ := by
        have := (fderiv ℝ a (x + t • h) - fderiv ℝ a x).le_opNorm h
        rw [dist_eq_norm] at h1
        have h3 : (fderiv ℝ a (x + t • h) - fderiv ℝ a x) h = fderiv ℝ a (x + t • h) h - fderiv ℝ a x h := rfl
        rw [h3] at this
        calc _ ≤ ‖fderiv ℝ a (x + t • h) h - fderiv ℝ a x h‖ := Real.le_norm_self _
          _ ≤ ‖fderiv ℝ a (x + t • h) - fderiv ℝ a x‖ * ‖h‖ := this
          _ ≤ _ := by gcongr
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [hφ] at this
  simp at this
  linarith

omit [FiniteDimensional ℝ E] in
lemma sqrtLip_grad (a : E → ℝ) (ha : ContDiff ℝ 1 a) (hnn : ∀ x, 0 ≤ a x) (L : ℝ) (hL : 0 ≤ L)
    (hlip : LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ a x)) (x h : E) :
    (fderiv ℝ a x h) ^ 2 ≤ 2 * L * a x * ‖h‖ ^ 2 := by
  have key : ∀ s : ℝ, 0 ≤ a x + s * fderiv ℝ a x h + L / 2 * s ^ 2 * ‖h‖ ^ 2 := by
    intro s
    have := sqrtLip_taylor a ha L hL hlip x (s • h)
    have h2 := hnn (x + s • h)
    simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at this
    nlinarith
  set D := fderiv ℝ a x h
  set H := ‖h‖ ^ 2 with hH
  have hH0 : 0 ≤ H := by positivity
  have hax := hnn x
  by_cases hLH : L * H = 0
  · have : D = 0 := by
      by_contra hD
      have := key (-(a x + 1) * D / D ^ 2)
      have hD2 : 0 < D ^ 2 := by positivity
      have e : L / 2 * (-(a x + 1) * D / D ^ 2) ^ 2 * H = 0 := by
        have : L / 2 * (-(a x + 1) * D / D ^ 2) ^ 2 * H = (-(a x + 1) * D / D ^ 2) ^ 2 / 2 * (L * H) := by ring
        rw [this, hLH]; ring
      rw [e] at this
      have : (-(a x + 1) * D / D ^ 2) * D = -(a x + 1) := by field_simp
      nlinarith
    rw [this]; simp; positivity
  · have hLH' : 0 < L * H := lt_of_le_of_ne (by positivity) (Ne.symm hLH)
    have := key (-D / (L * H))
    have e : a x + -D / (L * H) * D + L / 2 * (-D / (L * H)) ^ 2 * H = a x - D ^ 2 / (2 * (L * H)) := by
      field_simp; ring
    rw [e] at this
    have : D ^ 2 / (2 * (L * H)) ≤ a x := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith

/-- Lemma C.6 `M:B:lem:sqrt-lipschitz` (lines 12311-12313), on a finite-dimensional Euclidean
space (the torus case follows by periodic lifting): if `0 ≤ a ∈ C^{1,1}` with
`‖∇²a‖_∞ ≤ L`, then `√a` is Lipschitz with constant `(L/2)^{1/2}`. -/
theorem sqrt_lipschitz (a : E → ℝ) (ha : ContDiff ℝ 1 a) (hnn : ∀ x, 0 ≤ a x) (L : ℝ) (hL : 0 ≤ L)
    (hlip : LipschitzWith (Real.toNNReal L) (fun x => fderiv ℝ a x)) :
    LipschitzWith (Real.toNNReal (Real.sqrt (L / 2))) (fun x => Real.sqrt (a x)) := by
  have step : ∀ x y : E, Real.sqrt (a y) ≤ Real.sqrt (a x) + Real.sqrt (L / 2) * dist y x := by
    intro x y
    set h := y - x with hh
    have hy : y = x + h := by simp [hh]
    have hdist : dist y x = ‖h‖ := by rw [dist_eq_norm]
    rw [hdist]
    set M := Real.sqrt (L / 2)
    have hM : 0 ≤ M := Real.sqrt_nonneg _
    have hM2 : M ^ 2 = L / 2 := Real.sq_sqrt (by positivity)
    have hax := hnn x
    have hsa := Real.sq_sqrt hax
    have hsa0 := Real.sqrt_nonneg (a x)
    have hT := sqrtLip_taylor a ha L hL hlip x h
    have hG := sqrtLip_grad a ha hnn L hL hlip x h
    have hD : fderiv ℝ a x h ≤ 2 * Real.sqrt (a x) * M * ‖h‖ := by
      have h1 : (fderiv ℝ a x h) ^ 2 ≤ (2 * Real.sqrt (a x) * M * ‖h‖) ^ 2 := by
        calc _ ≤ 2 * L * a x * ‖h‖ ^ 2 := hG
          _ = _ := by
            have : (2 * Real.sqrt (a x) * M * ‖h‖) ^ 2 = 4 * (Real.sqrt (a x)) ^ 2 * M ^ 2 * ‖h‖ ^ 2 := by ring
            rw [this, hsa, hM2]; ring
      exact (le_abs_self _).trans (abs_le_of_sq_le_sq h1 (by positivity))
    have : a y ≤ (Real.sqrt (a x) + M * ‖h‖) ^ 2 := by
      rw [hy]
      nlinarith
    calc Real.sqrt (a y) ≤ Real.sqrt ((Real.sqrt (a x) + M * ‖h‖) ^ 2) := Real.sqrt_le_sqrt this
      _ = _ := Real.sqrt_sq (by positivity)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _), Real.dist_eq, abs_le]
  have h1 := step x y
  have h2 := step y x
  rw [dist_comm y x] at h1
  constructor <;> linarith


end Sqrt

section Hadamard

/-- The Hadamard growth factor of Proposition 3.10 for frequency `k`:
`⟨k⟩^{m'-m} exp(4π² c (2π|k|)^{s-d} (kᵀ S k) τ)` with `⟨k⟩ = (1+4π²|k|²)^{1/2}`. -/
def hadamardFactor (d : ℕ) (s c τ m m' : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (k : Fin d → ℤ) : ℝ :=
  let nk : ℝ := Real.sqrt (∑ i, ((k i : ℝ)) ^ 2)
  let kSk : ℝ := ∑ i, ∑ j, (k i : ℝ) * S i j * (k j : ℝ)
  (1 + 4 * Real.pi ^ 2 * nk ^ 2) ^ (m' / 2) / (1 + 4 * Real.pi ^ 2 * nk ^ 2) ^ (m / 2) *
    Real.exp (4 * Real.pi ^ 2 * c * (2 * Real.pi * nk) ^ (s - d) * kSk * τ)

/-- A nonzero lattice vector on which the quadratic form of `S` is positive. -/
lemma exists_lattice_pos (d : ℕ) (S : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∃ q : EuclideanSpace ℝ (Fin d), ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * S i j * q j) :
    ∃ k : Fin d → ℤ, k ≠ 0 ∧ 0 < ∑ i, ∑ j, (k i : ℝ) * S i j * (k j : ℝ) := by
  obtain ⟨q, hq1, hq2⟩ := hpos
  set Q : (Fin d → ℝ) → ℝ := fun u => ∑ i, ∑ j, u i * S i j * u j with hQ
  have hQc : Continuous Q := by
    simp only [hQ]; fun_prop
  have hqne : ∃ i, q i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : q = 0 := by ext i; exact hcon i
    simp [this] at hq1
  obtain ⟨i0, hi0⟩ := hqne
  -- rounding approximations
  let r : ℕ → (Fin d → ℤ) := fun N => fun i => round ((N : ℝ) * q i)
  have hconv : Tendsto (fun N : ℕ => fun i => ((r N i : ℤ) : ℝ) / (N : ℝ)) atTop (𝓝 (fun i => q i)) := by
    rw [tendsto_pi_nhds]
    intro i
    have hbd : ∀ N : ℕ, 1 ≤ N → |((r N i : ℤ) : ℝ) / (N : ℝ) - q i| ≤ 1 / (N : ℝ) := by
      intro N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 := abs_sub_round ((N : ℝ) * q i)
      have : ((r N i : ℤ) : ℝ) / (N : ℝ) - q i = (((r N i : ℤ) : ℝ) - (N : ℝ) * q i) / N := by
        field_simp
      rw [this, abs_div, abs_of_pos hNpos]
      rw [abs_sub_comm] at h1
      calc _ ≤ (1 / 2) / (N : ℝ) := by gcongr
        _ ≤ 1 / (N : ℝ) := by gcongr; norm_num
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Real.dist_eq]; exact hbd N hN
  have hev1 : ∀ᶠ N : ℕ in atTop, 0 < Q (fun i => ((r N i : ℤ) : ℝ) / (N : ℝ)) :=
    hconv.eventually ((hQc.tendsto _).eventually (lt_mem_nhds (show 0 < Q (fun i => q i) from hq2)))
  have hev2 : ∀ᶠ N : ℕ in atTop, ((r N i0 : ℤ) : ℝ) / (N : ℝ) ≠ 0 :=
    (tendsto_pi_nhds.1 hconv i0).eventually (isOpen_ne.mem_nhds hi0)
  obtain ⟨N, ⟨h1, h2⟩, h3⟩ := ((hev1.and hev2).and (eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h3
  refine ⟨r N, ?_, ?_⟩
  · intro h0
    apply h2
    have : r N i0 = 0 := congrFun h0 i0
    simp [this]
  · have hscale : Q (fun i => ((r N i : ℤ) : ℝ) / (N : ℝ)) =
        ((N : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, ((r N i : ℤ) : ℝ) * S i j * ((r N j : ℤ) : ℝ) := by
      simp only [hQ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hscale] at h1
    exact pos_of_mul_pos_right h1 (by positivity)


lemma exp_rpow_div_tendsto (K θ m : ℝ) (hK : 0 < K) (hθ : 0 < θ) :
    Tendsto (fun x : ℝ => Real.exp (K * x ^ θ) / x ^ m) atTop atTop := by
  have h1 := (tendsto_exp_mul_div_rpow_atTop (m / θ) K hK).comp (tendsto_rpow_atTop hθ)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx.le]
  congr 2
  field_simp

lemma hadamardFactor_smul (d : ℕ) (s c τ m m' : ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (q0 : Fin d → ℤ) (n : ℕ) :
    hadamardFactor d s c τ m m' S (fun i => (n : ℤ) * q0 i) =
      (1 + 4 * Real.pi ^ 2 * ((n : ℝ) * Real.sqrt (∑ i, ((q0 i : ℤ) : ℝ) ^ 2)) ^ 2) ^ (m' / 2) /
        (1 + 4 * Real.pi ^ 2 * ((n : ℝ) * Real.sqrt (∑ i, ((q0 i : ℤ) : ℝ) ^ 2)) ^ 2) ^ (m / 2) *
      Real.exp (4 * Real.pi ^ 2 * c *
        (2 * Real.pi * ((n : ℝ) * Real.sqrt (∑ i, ((q0 i : ℤ) : ℝ) ^ 2))) ^ (s - d) *
        ((n : ℝ) ^ 2 * ∑ i, ∑ j, ((q0 i : ℤ) : ℝ) * S i j * ((q0 j : ℤ) : ℝ)) * τ) := by
  have h1 : ∑ i, (((((n : ℤ) * q0 i : ℤ)) : ℝ)) ^ 2 = (n : ℝ) ^ 2 * ∑ i, ((q0 i : ℤ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring
  have h2 : ∑ i, ∑ j, (((((n : ℤ) * q0 i : ℤ)) : ℝ)) * S i j * (((((n : ℤ) * q0 j : ℤ)) : ℝ)) =
      (n : ℝ) ^ 2 * ∑ i, ∑ j, ((q0 i : ℤ) : ℝ) * S i j * ((q0 j : ℤ) : ℝ) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; push_cast; ring
  have h3 : Real.sqrt ((n : ℝ) ^ 2 * ∑ i, ((q0 i : ℤ) : ℝ) ^ 2) =
      (n : ℝ) * Real.sqrt (∑ i, ((q0 i : ℤ) : ℝ) ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg n)]
  simp only [hadamardFactor, h1, h2, h3]


/-- Proposition 3.10 `M:B:prop:hadamard` (lines 1778-1786), the supremum identity: for
`d - 2 < s < d`, `c > 0`, `τ > 0`, `m, m' ≥ 0`, and a symmetric `S` with `qᵀ S q > 0` for some
unit vector `q`, `sup_{k ≠ 0} hadamardFactor = ∞` (the factor is unbounded over `ℤ^d∖{0}`). -/
theorem hadamard_sup_eq_top (d : ℕ) (hd : 2 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s) (hs2 : s < d)
    (c : ℝ) (hc : 0 < c) (τ : ℝ) (hτ : 0 < τ) (m m' : ℝ) (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.IsSymm)
    (hpos : ∃ q : EuclideanSpace ℝ (Fin d), ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * S i j * q j) :
    ¬ BddAbove (Set.range fun k : {k : Fin d → ℤ // k ≠ 0} => hadamardFactor d s c τ m m' S k.1) := by
  obtain ⟨q0, hq0, hσ⟩ := exists_lattice_pos d S hpos
  set σ : ℝ := ∑ i, ∑ j, ((q0 i : ℤ) : ℝ) * S i j * ((q0 j : ℤ) : ℝ) with hσdef
  set T : ℝ := ∑ i, ((q0 i : ℤ) : ℝ) ^ 2 with hTdef
  have hT : 0 < T := by
    obtain ⟨i0, hi0⟩ : ∃ i, q0 i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq0 (funext hcon)
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨i0, Finset.mem_univ _, ?_⟩
    have : ((q0 i0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi0
    positivity
  set r : ℝ := Real.sqrt T with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hT
  set A : ℝ := 4 * Real.pi ^ 2 * r ^ 2 with hAdef
  have hA : 0 < A := by positivity
  set θ : ℝ := s - d + 2 with hθdef
  have hθ : 0 < θ := by linarith
  set K : ℝ := 4 * Real.pi ^ 2 * c * (2 * Real.pi * r) ^ (s - d) * σ * τ with hKdef
  have hK : 0 < K := by positivity
  have hlow : ∀ n : ℕ, 1 ≤ n →
      (1 + A) ^ (-(m / 2)) * (Real.exp (K * (n : ℝ) ^ θ) / (n : ℝ) ^ m) ≤
        hadamardFactor d s c τ m m' S (fun i => (n : ℤ) * q0 i) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hadamardFactor_smul]
    simp only [← hTdef, ← hσdef, ← hrdef]
    have hu : 4 * Real.pi ^ 2 * ((n : ℝ) * r) ^ 2 = A * (n : ℝ) ^ 2 := by rw [hAdef]; ring
    rw [hu]
    have hE : 4 * Real.pi ^ 2 * c * (2 * Real.pi * ((n : ℝ) * r)) ^ (s - d) *
        ((n : ℝ) ^ 2 * σ) * τ = K * (n : ℝ) ^ θ := by
      have e1 : (2 * Real.pi * ((n : ℝ) * r)) = (2 * Real.pi * r) * n := by ring
      rw [e1, Real.mul_rpow (by positivity) hnpos.le, hθdef, Real.rpow_add hnpos, Real.rpow_two,
        hKdef]
      ring
    rw [hE]
    set u : ℝ := 1 + A * (n : ℝ) ^ 2 with hudef
    have hu1 : 1 ≤ u := by rw [hudef]; nlinarith [sq_nonneg (n : ℝ)]
    have hu0 : 0 < u := by linarith
    have hup : 1 ≤ u ^ (m' / 2) := Real.one_le_rpow hu1 (by positivity)
    have hule : u ≤ (1 + A) * (n : ℝ) ^ 2 := by
      rw [hudef]; nlinarith [sq_nonneg (n : ℝ)]
    have hum : u ^ (m / 2) ≤ (1 + A) ^ (m / 2) * (n : ℝ) ^ m := by
      calc u ^ (m / 2) ≤ ((1 + A) * (n : ℝ) ^ 2) ^ (m / 2) :=
            Real.rpow_le_rpow hu0.le hule (by positivity)
        _ = (1 + A) ^ (m / 2) * (n : ℝ) ^ m := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (n : ℝ) 2,
              ← Real.rpow_mul hnpos.le]
            congr 2
            push_cast; ring
    have hpos1 : 0 < (1 + A) ^ (m / 2) * (n : ℝ) ^ m := by positivity
    have hexp : 0 < Real.exp (K * (n : ℝ) ^ θ) := Real.exp_pos _
    have hq : 1 / ((1 + A) ^ (m / 2) * (n : ℝ) ^ m) ≤ u ^ (m' / 2) / u ^ (m / 2) := by
      rw [div_le_div_iff₀ hpos1 (by positivity)]
      nlinarith [Real.rpow_pos_of_pos hu0 (m / 2)]
    calc (1 + A) ^ (-(m / 2)) * (Real.exp (K * (n : ℝ) ^ θ) / (n : ℝ) ^ m)
        = 1 / ((1 + A) ^ (m / 2) * (n : ℝ) ^ m) * Real.exp (K * (n : ℝ) ^ θ) := by
          rw [Real.rpow_neg (by positivity)]; field_simp
      _ ≤ _ := by gcongr
  rintro ⟨B, hB⟩
  have ht : Tendsto (fun n : ℕ => (1 + A) ^ (-(m / 2)) *
      (Real.exp (K * (n : ℝ) ^ θ) / (n : ℝ) ^ m)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((exp_rpow_div_tendsto K θ m hK hθ).comp tendsto_natCast_atTop_atTop)
  have hev := (ht.eventually_gt_atTop B).and (eventually_ge_atTop 1)
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  have hne : (fun i => (n : ℤ) * q0 i) ≠ 0 := by
    intro h0
    apply hq0
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply, mul_eq_zero] at this
    rcases this with h | h
    · omega
    · exact h
  have hmem : hadamardFactor d s c τ m m' S (fun i => (n : ℤ) * q0 i) ∈
      Set.range fun k : {k : Fin d → ℤ // k ≠ 0} => hadamardFactor d s c τ m m' S k.1 :=
    ⟨⟨_, hne⟩, rfl⟩
  have := hB hmem
  have := hlow n hn2
  linarith


end Hadamard

end HRS
