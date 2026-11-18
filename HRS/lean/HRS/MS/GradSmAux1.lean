import HRS.MS.PoisHighAux3

/-!
# S6.7 packet S67B: gradient smoothing of the one-body semigroup (`W:r2mov:gradient-smoothing`), part 1

TeX `S:W:r2mov:gradient-smoothing` (supplement L4456-4492):
`‖∇P_tF‖_{C_b^k} ≤ C_k (1+t^{-1/2}) e^{-λt} ‖F‖_{C_b^k}`, `P_t` the semigroup of `νΔ + b·∇`, `b = -qx + B(x)`.

## Plan (the cheapest route: the merged POIS lemmas already gain one derivative)

The brief of this packet says that the merged POIS lemmas gain no derivative; this is wrong for two of them:
* `PoisGrad.pois_gradsmooth`: `‖D P_t f‖ ≤ √(Mb+1) M_0 / √t`, `0 < t ≤ 1` (order `0 → 1`);
* `PoisHigh.pois_highsmooth`: `‖D^j P_t g‖ ≤ C_j t^{-1/2} ∑_{i=1}^{j-1} M_i`, `2 ≤ j ≤ m`, `0 < t ≤ 1` (order `j-1 → j`).
Together with `pois_shorttime` (`t ≤ 1`, no gain), `pois_longtime` (`t ≥ 1`, `C e^{-c0(t-1)} Lip`, the Lipschitz
contraction `pois_lipdecay` replaces Eberle) and `sg_markov_C2` the TeX estimate is an assembly:

* `s67b_short_one`: the `j = 1` bound for `C^m` data (mollification `pois_moll_data` and the closing lemma
  `pois_moll_close_data`, because `pois_gradsmooth` is stated for `C^∞` data).
* `s67b_short`: `0 < t ≤ 1`, `1 ≤ j ≤ k+1`: `‖D^j P_t F‖ ≤ C t^{-1/2} K`, `K = ∑_{i ≤ k} M_i`.
* `s67b_long`: `t ≥ 1`: `r = P_{1/2}F`, `P_t F = P_{t-1/2} r`, `‖D r‖ ≤ C M_0`; `pois_longtime` (`t ≥ 3/2`) and
  `pois_shorttime` (`1 ≤ t ≤ 3/2`): `‖D^j P_t F‖ ≤ C e^{-c0 t} K`.
* `s67b_gs_smooth`: both ranges, `‖D^j P_t F‖ ≤ C (1 + t^{-1/2}) e^{-c0 t} ∑_{i ≤ k} M_i`, `1 ≤ j ≤ k+1`, `c0 = pm_c0 q Mb`.

Normalisation: the POIS package is `Δ - q x·∇ + B·∇` (`ν = 1`); `ν > 0` is the time scaling `q' = q/ν`, `B' = B/ν`, `t' = νt`.
The time-dependent perturbation `-F_v·∇f_v` of the S6.7 adjoint is a SOURCE of the stationary Duhamel formula (TeX L4482-4492), so
the estimate is for the stationary semigroup and data in `C_b^k` including the zeroth order.
The qualitative hypothesis is `F ∈ C^m` (`m ≥ max 2 (k+1)`) with bounds `M i` for `i ≤ m`; only `M_0..M_k` enter.
Part 2 (`GradSmAux2`) closes it to `F ∈ C^{k+1}` with `m` free.

Files: `GradSmAux1` (this file, `C^m` data), `GradSmAux2` (`C^{k+1}` data, `ContDiff` and `cbNormVecE` forms), `GradSmAux3`
(Arzela-Ascoli and the compactness lemma `s67b_lim`), `GradSmAux4` (qualitative gain `F ∈ C^k ⇒ P_tF ∈ C^{k+1}`, `s67b_gs_gain`),
`GradSmTie` (headline `gradient_smoothing_cb`).  Truth/junk-value check: true and non-vacuous; `t > 0` (`t^{-1/2}`), `q > 0`,
`sg t F` is an integral of a bounded function (no Bochner junk) and all `iteratedFDeriv` statements are about `C^{k+1}` functions.
Not covered here (consumer side): the Duhamel integral `∇∫ P_{v-r}g_v dv` (differentiation under `dv`, needs measurability in `v`).

Helpers carry the prefix `s67b_`; namespace `HRS.MS.GradSm`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
  HRS.MS.PoisHigh

noncomputable section

universe u

namespace HRS.MS.GradSm

variable {d : ℕ}

theorem s67b_c0_pos (q Mb : ℝ) (hq : 0 < q) : 0 < pm_c0 q Mb := by
  unfold pm_c0 pm_kappa
  exact mul_pos (Real.exp_pos _) (lt_min one_pos (by positivity))

/-- the order `0 → 1` short-time bound for `C^m` data. -/
theorem s67b_short_one (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : IsBrownianFiltration P ℱ W)
    {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {F : Euc d → ℝ}
    (hF : ContDiff ℝ (m : WithTop ℕ∞) F) {M : ℕ → ℝ}
    (hM : ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (x : Euc d) :
    ‖fderiv ℝ (sg P W q B t F) x‖ ≤ Real.sqrt (Mb + 1) * M 0 / Real.sqrt t := by
  have hWs := sgNoise_of_brownian hW
  obtain ⟨hn, hnc, hnM, hnb, hn0, hnlim⟩ := pois_moll_data (k := m) hF (M := M) hM
  set M' : ℝ := ∑ i ∈ Finset.range (m + 1), |M i| with hM'def
  have hMM' : ∀ i ≤ m, M i ≤ M' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have key := pois_moll_close_data (P := P) q Mb hq m hm m le_rfl 1 (by omega) hB W hWs
    (hn := hn) (fun n => (hnc n).of_le (by exact_mod_cast le_top))
    (fun n => ⟨M', fun i hi y => (hnM n i hi y).trans (hMM' i hi)⟩) hF (M := M')
    (fun i hi y => (hM i hi y).trans (hMM' i hi)) hnlim (M0 := M 0) hn0 ht0.le
    (C := fun i => if i = 0 then M 0 else Real.sqrt (Mb + 1) * M 0 / Real.sqrt t)
    (fun n i hi y => ?_) 1 le_rfl x
  · rw [norm_iteratedFDeriv_one] at key
    simpa using key
  · interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      simpa using gs_sg_abs_le (P := P) (W := W) (q := q) (B := B) (hn0 n) t y
    · rw [norm_iteratedFDeriv_one]
      simpa using pois_gradsmooth hq hm hB hW (hnc n) (hn0 n)
        ⟨M', fun i hi y => (hnM n i (by omega) y).trans (hMM' i (by omega))⟩ ht0 ht1 y


/-- `0 < t ≤ 1`, orders `1 ≤ j ≤ k+1`: `‖D^j P_t F‖ ≤ C t^{-1/2} ∑_{i ≤ k} M_i`. -/
theorem s67b_short (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t F) x‖ ≤
        C * (Real.sqrt t)⁻¹ * ∑ i ∈ Finset.range (k + 1), M i := by
  have hj : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (2 ≤ j → j ≤ m → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ g : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M i) → ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t g) x‖ ≤
        C * (Real.sqrt t)⁻¹ * ∑ i ∈ Finset.Icc 1 (j - 1), M i) := by
    intro j
    by_cases h : 2 ≤ j ∧ j ≤ m
    · obtain ⟨C, hC0, hC⟩ := pois_highsmooth (d := d) q Mb hq hMb m hm j h.1 h.2
      exact ⟨C, hC0, fun _ _ => hC⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Cj hCj0 hCj using hj
  set CS : ℝ := Real.sqrt (Mb + 1) + ∑ j ∈ Finset.range (k + 2), Cj j with hCS
  have hCS0 : 0 ≤ CS := by
    have : 0 ≤ ∑ j ∈ Finset.range (k + 2), Cj j := Finset.sum_nonneg fun j _ => hCj0 j
    positivity
  refine ⟨CS, hCS0, fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht0 ht1 j hj1 hjk x => ?_⟩
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set K : ℝ := ∑ i ∈ Finset.range (k + 1), M i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i hi => hM0 i (by
    have := Finset.mem_range.1 hi; omega)
  have hsq : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht0)
  have hMK : ∀ i, i ≤ k → M i ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => M i) (fun i hi' => hM0 i (by
      have := Finset.mem_range.1 hi'; omega)) (Finset.mem_range.2 (by omega))
  rcases Nat.eq_or_lt_of_le hj1 with h1 | h2
  · subst h1
    rw [norm_iteratedFDeriv_one]
    have := s67b_short_one q Mb hq m hm P ℱ W hW hBm hF hM ht0 ht1 x
    refine this.trans ?_
    have e : Real.sqrt (Mb + 1) * M 0 / Real.sqrt t = Real.sqrt (Mb + 1) * (Real.sqrt t)⁻¹ * M 0 := by
      rw [div_eq_mul_inv]; ring
    rw [e]
    have hle : Real.sqrt (Mb + 1) ≤ CS := by
      have : 0 ≤ ∑ j ∈ Finset.range (k + 2), Cj j := Finset.sum_nonneg fun j _ => hCj0 j
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hle hsq.le) (hMK 0 (Nat.zero_le _))
      (hM0 0 (by omega)) (by positivity)
  · have h2' : 2 ≤ j := h2
    have hb := hCj j h2' (by omega) P ℱ W hW B hBm F hF M hM t ht0 ht1 x
    refine hb.trans ?_
    have hsub : ∑ i ∈ Finset.Icc 1 (j - 1), M i ≤ K := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) (fun i hi _ => ?_)
      · have := Finset.mem_Icc.1 hi; exact Finset.mem_range.2 (by omega)
      · exact hM0 i (by have := Finset.mem_range.1 ‹_›; omega)
    have hle : Cj j ≤ CS := by
      have h3 : Cj j ≤ ∑ j ∈ Finset.range (k + 2), Cj j :=
        Finset.single_le_sum (f := fun j => Cj j) (fun j _ => hCj0 j)
          (Finset.mem_range.2 (by omega))
      have := Real.sqrt_nonneg (Mb + 1)
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hle hsq.le) hsub
      (Finset.sum_nonneg fun i hi => hM0 i (by have := (Finset.mem_Icc.1 hi).2; omega))
      (by positivity)


theorem s67b_inv_sqrt_half : (Real.sqrt (1 / 2))⁻¹ ≤ 2 := by
  have h : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
  calc (Real.sqrt (1 / 2))⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 2 := by norm_num

theorem s67b_one_le_exp {c0 t : ℝ} (hc : 0 ≤ c0) (ht : t ≤ 3 / 2) :
    1 ≤ Real.exp (3 / 2 * c0) * Real.exp (-c0 * t) := by
  rw [← Real.exp_add]
  exact Real.one_le_exp (by nlinarith)

/-- `t ≥ 1`, orders `1 ≤ j ≤ k+1`: `‖D^j P_t F‖ ≤ C e^{-c0 t} ∑_{i ≤ k} M_i`. -/
theorem s67b_long (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 1 ≤ t →
      ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t F) x‖ ≤
        C * Real.exp (-(pm_c0 q Mb) * t) * ∑ i ∈ Finset.range (k + 1), M i := by
  obtain ⟨C1, hC10, hC1⟩ := s67b_short (d := d) q Mb hq hMb m hm k hk
  obtain ⟨Csg, hCsg1, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm (1 / 2) (by norm_num) m le_rfl
  have hst : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j → j ≤ m → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i r y‖ ≤ M i) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ C * ∑ i ∈ Finset.Icc 1 j, M i) := by
    intro j
    by_cases h : 1 ≤ j ∧ j ≤ m
    · obtain ⟨C, hC0, hC⟩ := pois_shorttime (d := d) q Mb hq m hm j h.1 h.2
      exact ⟨C, hC0, fun _ _ => hC⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hlt : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j → j ≤ m → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω}
      (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i r y‖ ≤ M i) → ∀ t : ℝ, 1 ≤ t → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤
        C * Real.exp (-(pm_c0 q Mb) * (t - 1)) * M 1) := by
    intro j
    by_cases h : 1 ≤ j ∧ j ≤ m
    · obtain ⟨C, hC0, hC⟩ := pois_longtime (d := d) q Mb hq hMb m hm j h.1 h.2
      exact ⟨C, hC0, fun _ _ => hC⟩
    · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Cst hCst0 hCst using hst
  choose Clt hClt0 hClt using hlt
  set A : ℝ := ∑ j ∈ Finset.range (k + 2), Cst j with hA
  set Bc : ℝ := ∑ j ∈ Finset.range (k + 2), Clt j with hBc
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => hCst0 j
  have hBc0 : 0 ≤ Bc := Finset.sum_nonneg fun j _ => hClt0 j
  set c0 : ℝ := pm_c0 q Mb with hc0
  have hc00 : 0 < c0 := s67b_c0_pos q Mb hq
  set C : ℝ := (A * ((k : ℝ) + 1) * (2 * C1) + Bc * (2 * C1)) * Real.exp (3 / 2 * c0) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht1 j hj1 hjk x => ?_⟩
  have hWs := sgNoise_of_brownian hW
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set K : ℝ := ∑ i ∈ Finset.range (k + 1), M i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i hi => hM0 i (by
    have := Finset.mem_range.1 hi; omega)
  set M' : ℝ := ∑ i ∈ Finset.range (m + 1), |M i| with hM'def
  have hMM' : ∀ i ≤ m, M i ≤ M' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hM'0 : 0 ≤ M' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨hrc, -, hrb⟩ := hCsg P W hWs B hBm F hF M' (fun i hi y => (hM i hi y).trans (hMM' i hi))
    (1 / 2) ⟨by norm_num, le_rfl⟩
  set r : Euc d → ℝ := sg P W q B (1 / 2) F with hr
  set R : ℝ := 2 * C1 * K with hR
  have hR0 : 0 ≤ R := by positivity
  have hrD : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ y, ‖iteratedFDeriv ℝ i r y‖ ≤ R := by
    intro i hi1 hik y
    have h1 := hC1 P ℱ W hW B hBm F hF M hM (1 / 2) (by norm_num) (by norm_num) i hi1 hik y
    refine h1.trans ?_
    have := s67b_inv_sqrt_half
    calc C1 * (Real.sqrt (1 / 2))⁻¹ * K ≤ C1 * 2 * K :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC10) hK0
      _ = R := by rw [hR]; ring
  have hmk : sg P W q B t F = sg P W q B (t - 1 / 2) r := by
    funext y
    have := sg_markov_C2 hW hq.le (by omega : 1 ≤ m) hBm (h := F)
      (hF.of_le (by exact_mod_cast (by omega : 2 ≤ m))) (M := M')
      (fun i hi y => (hM i (by omega) y).trans (hMM' i (by omega))) (t := t - 1 / 2)
      (s := 1 / 2) (by linarith) (by norm_num) y
    have e : t - 1 / 2 + 1 / 2 = t := by ring
    rw [e] at this
    exact this
  have hjm : j ≤ m := by omega
  rw [hmk]
  rcases le_or_gt t (3 / 2) with hle | hgt
  · have hb := hCst j hj1 hjm P ℱ W hW B hBm r hrc
      (fun i => if 1 ≤ i ∧ i ≤ k + 1 then R else Csg * M') (fun i hi y => ?_) (t - 1 / 2)
      (by linarith) (by linarith) x
    · refine hb.trans ?_
      have hsum : ∑ i ∈ Finset.Icc 1 j, (if 1 ≤ i ∧ i ≤ k + 1 then R else Csg * M') = j * R := by
        rw [Finset.sum_congr rfl (g := fun _ => R) (fun i hi => by
          have := Finset.mem_Icc.1 hi
          simp [this.1, show i ≤ k + 1 by omega])]
        simp
      rw [hsum]
      have hCj : Cst j ≤ A :=
        Finset.single_le_sum (f := fun j => Cst j) (fun j _ => hCst0 j)
          (Finset.mem_range.2 (by omega))
      have hjk' : (j : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hjk
      have h1 : Cst j * (j * R) ≤ A * ((k : ℝ) + 1) * R :=
        calc Cst j * (j * R) ≤ A * (((k : ℝ) + 1) * R) :=
              mul_le_mul hCj (mul_le_mul_of_nonneg_right hjk' hR0) (by positivity) hA0
          _ = _ := by ring
      have h2 := s67b_one_le_exp (c0 := c0) hc00.le hle
      calc Cst j * (j * R) ≤ A * ((k : ℝ) + 1) * R := h1
        _ ≤ A * ((k : ℝ) + 1) * R * (Real.exp (3 / 2 * c0) * Real.exp (-c0 * t)) :=
            le_mul_of_one_le_right (by positivity) h2
        _ ≤ C * Real.exp (-c0 * t) * K := by
            rw [hC, hR]
            have : 0 ≤ Real.exp (-c0 * t) := (Real.exp_pos _).le
            nlinarith [mul_nonneg (mul_nonneg hA0 (by positivity : (0:ℝ) ≤ (k:ℝ) + 1)) hC10,
              mul_nonneg (mul_nonneg hBc0 hC10) hK0,
              Real.exp_pos (3 / 2 * c0), mul_nonneg hK0 this]
    · by_cases hi' : 1 ≤ i ∧ i ≤ k + 1
      · simp only [hi', and_self, ite_true]
        exact hrD i hi'.1 hi'.2 y
      · simp only [hi', ite_false]
        exact hrb i hi y
  · have hb := hClt j hj1 hjm P ℱ W hW B hBm r hrc
      (fun i => if i = 1 then R else Csg * M') (fun i hi y => ?_) (t - 1 / 2) (by linarith) x
    · refine hb.trans ?_
      simp only [ite_true]
      have hCj : Clt j ≤ Bc :=
        Finset.single_le_sum (f := fun j => Clt j) (fun j _ => hClt0 j)
          (Finset.mem_range.2 (by omega))
      have e : Real.exp (-c0 * (t - 1 / 2 - 1)) = Real.exp (3 / 2 * c0) * Real.exp (-c0 * t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e, hC, hR]
      have : 0 ≤ Real.exp (-c0 * t) := (Real.exp_pos _).le
      have hE := Real.exp_pos (3 / 2 * c0)
      calc Clt j * (Real.exp (3 / 2 * c0) * Real.exp (-c0 * t)) * (2 * C1 * K)
          ≤ Bc * (Real.exp (3 / 2 * c0) * Real.exp (-c0 * t)) * (2 * C1 * K) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCj (by positivity))
              (by positivity)
        _ ≤ _ := by
            nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hBc0 hC10) hK0) (mul_nonneg hE.le this),
              mul_nonneg (mul_nonneg (mul_nonneg hA0 (by positivity : (0:ℝ) ≤ (k:ℝ) + 1) ) hC10)
                (mul_nonneg hK0 (mul_nonneg hE.le this))]
    · by_cases hi' : i = 1
      · subst hi'
        simp only [ite_true]
        exact hrD 1 le_rfl (by omega) y
      · simp only [hi', ite_false]
        exact hrb i hi y


/-- **Gradient smoothing, smooth data.**  For `B ∈ C_b^m` (`HasCbBound m Mb B`, `m ≥ max 2 (k+1)`), `F ∈ C^m` with
`‖D^i F‖ ≤ M i` (`i ≤ m`), every `t > 0` and every `1 ≤ j ≤ k+1`:
`‖D^j P_t F‖ ≤ C (1 + t^{-1/2}) e^{-c0 t} ∑_{i ≤ k} M i`, `c0 = pm_c0 q Mb > 0`;
that is `‖∇ P_t F‖_{C_b^k} ≲ (1 + t^{-1/2}) e^{-c0 t} ‖F‖_{C_b^k}` (the bounds `M i`, `k < i ≤ m`, are qualitative only). -/
theorem s67b_gs_smooth (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (k : ℕ)
    (hk : k + 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ F : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) F → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i F y‖ ≤ M i) → ∀ t : ℝ, 0 < t →
      ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t F) x‖ ≤
        C * (1 + (Real.sqrt t)⁻¹) * Real.exp (-(pm_c0 q Mb) * t) *
          ∑ i ∈ Finset.range (k + 1), M i := by
  obtain ⟨C1, hC10, hC1⟩ := s67b_short (d := d) q Mb hq hMb m hm k hk
  obtain ⟨C2, hC20, hC2⟩ := s67b_long (d := d) q Mb hq hMb m hm k hk
  set c0 : ℝ := pm_c0 q Mb with hc0
  have hc00 : 0 < c0 := s67b_c0_pos q Mb hq
  refine ⟨C1 * Real.exp c0 + C2, by positivity, fun {Ω} {mΩ} P _ ℱ W hW B hBm F hF M hM t ht0 j hj1 hjk x => ?_⟩
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set K : ℝ := ∑ i ∈ Finset.range (k + 1), M i with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i hi => hM0 i (by
    have := Finset.mem_range.1 hi; omega)
  have hsq : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht0)
  have hE : 0 < Real.exp (-c0 * t) := Real.exp_pos _
  rcases le_or_gt t 1 with h1 | h1
  · have hb := hC1 P ℱ W hW B hBm F hF M hM t ht0 h1 j hj1 hjk x
    refine hb.trans ?_
    have h2 : 1 ≤ Real.exp c0 * Real.exp (-c0 * t) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have h3 : C1 * (Real.sqrt t)⁻¹ * K ≤
        C1 * (Real.sqrt t)⁻¹ * K * (Real.exp c0 * Real.exp (-c0 * t)) :=
      le_mul_of_one_le_right (by positivity) h2
    refine h3.trans ?_
    have h4 : 0 ≤ C1 * (Real.exp c0 * (Real.sqrt t)⁻¹ * (Real.exp (-c0 * t) * K)) := by positivity
    have h5 : 0 ≤ C2 * (Real.exp (-c0 * t) * K) := by positivity
    have h6 : 0 ≤ C2 * ((Real.sqrt t)⁻¹ * (Real.exp (-c0 * t) * K)) := by positivity
    nlinarith
  · have hb := hC2 P ℱ W hW B hBm F hF M hM t h1.le j hj1 hjk x
    refine hb.trans ?_
    have h4 : 0 ≤ C1 * Real.exp c0 * (1 + (Real.sqrt t)⁻¹) * (Real.exp (-c0 * t) * K) := by positivity
    have h6 : 0 ≤ C2 * (Real.sqrt t)⁻¹ * (Real.exp (-c0 * t) * K) := by positivity
    nlinarith

end HRS.MS.GradSm
