import HRS.MS.PoisMollAux1

/-!
# POIS-MOLL, part 2: pathwise convergence of the flows, convergence of the semigroups, interfaces

Setting: `q > 0`, `B` with `HasCbBound m Mb B` (`m ≥ 1`), and drifts `B_n` with `HasCbBound m Mb (B_n)`
and `‖B_n - B‖_∞ ≤ δ_n → 0` (for the mollified drifts `B_n = B * η_n` of `PoisMollAux1`,
`δ_n = Mb/(n+1)` because `B` is `Mb`-Lipschitz).  Helper lemmas carry the prefix `moll_`.

* `moll_flow_diff` (pathwise Gronwall): for every noise path `w` (continuous, `w 0 = 0`), `t ≥ 0`,
  `x`: `‖flowMap q B' w t x - flowMap q B w t x‖ ≤ δ t e^{(q+Mb)t}` when `‖B' - B‖_∞ ≤ δ`; the bound is
  uniform in `x` and `w`.  The flow is `Z_t + √2 U_t` and the OU shift `U` is the same for both drifts.
* `moll_sg_tendsto`: `sg (B_n) t h x → sg B t h x` for continuous bounded `h` (dominated convergence);
  `moll_sg_tendsto_data`: `sg B t (h_n) x → sg B t h x` for `h_n → h` pointwise, uniformly bounded.
* `pois_moll_drift`: the approximating drifts: `C^∞`, `HasCbBound m Mb`, all derivatives bounded
  (`HasCbBound k M_k` for every `k`), `‖B_n - B‖ ≤ Mb/(n+1)`.
* `pois_moll_data`: the same for scalar data `h ∈ C^k` (bounds `‖D^j h_n‖ ≤ M j` for `j ≤ k`).
* `pois_moll_close_drift`, `pois_moll_close_data`: the closing lemmas: if `‖D^i sg^{B_n} t h‖ ≤ C i`
  for all `n` and `i ≤ j0` (`j0 ≤ k ≤ m`) then the same bound holds for `sg^B t h`; likewise in the
  data variable.
* `pois_moll`: packaging of `pois_moll_drift` and `pois_moll_close_drift` for a fixed `B`.

Note on the statements: the bound `‖B_n - B‖_∞ ≤ Mb/(n+1)` is global because `B` is `Mb`-Lipschitz; no
compactness is used.  `sg_contDiff` is applied with the *same* `(m, Mb)` for `B` and all `B_n`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg

set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace HRS.MS.PoisMoll

variable {d : ℕ}

/-! ### Pathwise Gronwall -/

theorem moll_flow_diff {q Mb : ℝ} (hq : 0 < q) {m : ℕ} {B B' : Euc d → Euc d}
    {w : ℝ≥0 → Fin d → ℝ} (H : PfHyp q Mb m B w) (H' : PfHyp q Mb m B' w) {δ : ℝ}
    (hδ : ∀ y, ‖B' y - B y‖ ≤ δ) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    ‖flowMap q B' w t x - flowMap q B w t x‖ ≤ δ * t * Real.exp ((q + Mb) * t) := by
  have hMb : 0 ≤ Mb := by
    have := H.hB.2 0 (Nat.zero_le _) 0
    exact (norm_nonneg _).trans this
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  set Z := pfZ q B w x with hZ
  set Z' := pfZ q B' w x with hZ'
  set f : ℝ → Euc d := fun s => Z' s - Z s with hf
  set f' : ℝ → Euc d := fun s => pfDrift q B' w s (Z' s) - pfDrift q B w s (Z s) with hf'
  have hd : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt Z (pfDrift q B w τ (Z τ)) (Icc 0 t) τ :=
    pf_hasDerivWithinAt_of_integral (pf_continuousOn_drift H x ht)
      (fun s hs => pf_Z_eq H x hs.1)
  have hd' : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt Z' (pfDrift q B' w τ (Z' τ)) (Icc 0 t) τ :=
    pf_hasDerivWithinAt_of_integral (pf_continuousOn_drift H' x ht)
      (fun s hs => pf_Z_eq H' x hs.1)
  have hcont : ContinuousOn f (Icc 0 t) := (pf_Z_cont H' x ht).sub (pf_Z_cont H x ht)
  have hderiv : ∀ s ∈ Ico (0 : ℝ) t, HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    have h1 := ((hd' s ⟨hs.1, hs.2.le⟩).sub (hd s ⟨hs.1, hs.2.le⟩))
    exact h1.mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc hs.1 le_rfl))
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖f' s‖ ≤ (q + Mb) * ‖f s‖ + δ := by
    intro s _
    set u : Euc d := Real.sqrt 2 • ouShift q w s
    have e : f' s = -q • (Z' s - Z s) + ((B' (Z' s + u) - B (Z' s + u)) +
        (B (Z' s + u) - B (Z s + u))) := by
      simp only [hf', pfDrift]; module
    rw [e]
    have h1 : ‖-q • (Z' s - Z s)‖ = q * ‖f s‖ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg hq.le]
    have h2 := pf_lip_of_cb H.hm H.hB (Z' s + u) (Z s + u)
    rw [add_sub_add_right_eq_sub] at h2
    calc _ ≤ ‖-q • (Z' s - Z s)‖ + (‖B' (Z' s + u) - B (Z' s + u)‖ +
          ‖B (Z' s + u) - B (Z s + u)‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ q * ‖f s‖ + (δ + Mb * ‖f s‖) := by
          rw [h1]; exact add_le_add le_rfl (add_le_add (hδ _) h2)
      _ = (q + Mb) * ‖f s‖ + δ := by ring
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) hcont hderiv
    (by simp [hf, Z, Z', pf_Z_zero H, pf_Z_zero H']) hbound t ⟨ht, le_rfl⟩
  have e : flowMap q B' w t x - flowMap q B w t x = f t := by
    simp only [flowMap, hf]; abel
  rw [e]
  have hK : q + Mb ≠ 0 := by positivity
  rw [sub_zero, gronwallBound_of_K_ne_0 hK] at hg
  refine hg.trans ?_
  have hK0 : 0 < q + Mb := by positivity
  have h3 : Real.exp ((q + Mb) * t) - 1 ≤ (q + Mb) * t * Real.exp ((q + Mb) * t) := by
    have := Real.add_one_le_exp (-((q + Mb) * t))
    have h4 : Real.exp (-((q + Mb) * t)) * Real.exp ((q + Mb) * t) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos ((q + Mb) * t)]
  calc 0 * Real.exp ((q + Mb) * t) + δ / (q + Mb) * (Real.exp ((q + Mb) * t) - 1)
      ≤ δ / (q + Mb) * ((q + Mb) * t * Real.exp ((q + Mb) * t)) := by
        rw [zero_mul, zero_add]
        exact mul_le_mul_of_nonneg_left h3 (div_nonneg hδ0 hK0.le)
    _ = δ * t * Real.exp ((q + Mb) * t) := by field_simp

/-! ### Convergence of the semigroups -/

section Sg

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem moll_meas_comp {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : SgNoise W) {q Mb : ℝ} (hq : 0 ≤ q)
    {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {t : ℝ} (ht : 0 ≤ t)
    {h : Euc d → ℝ} (hh : Continuous h) (x : Euc d) :
    AEStronglyMeasurable (fun a => h (flowMap q B (fun s => W s a) t x)) P :=
  (hh.measurable.comp ((sg_measurable_flowMap hW hq hm hB ht).comp
    (measurable_id.prodMk measurable_const))).aestronglyMeasurable

/-- `sg^{B_n} t h x → sg^B t h x` for continuous bounded `h` when `‖B_n - B‖_∞ → 0`
(dominated convergence on top of the pathwise Gronwall estimate). -/
theorem moll_sg_tendsto {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : SgNoise W) {q Mb : ℝ} (hq : 0 < q)
    {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {Bn : ℕ → Euc d → Euc d} (hBn : ∀ n, HasCbBound m Mb (Bn n)) {δ : ℕ → ℝ}
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hδ : ∀ n y, ‖Bn n y - B y‖ ≤ δ n) {h : Euc d → ℝ}
    (hh : Continuous h) {M0 : ℝ} (hM0 : ∀ y, ‖h y‖ ≤ M0) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    Tendsto (fun n => sg P W q (Bn n) t h x) atTop (𝓝 (sg P W q B t h x)) := by
  unfold sg
  refine tendsto_integral_of_dominated_convergence (fun _ => M0)
    (fun n => moll_meas_comp P hW hq.le hm (hBn n) ht hh x) (integrable_const _)
    (fun n => ae_of_all _ fun a => hM0 _) (ae_of_all _ fun a => ?_)
  have hflow : Tendsto (fun n => flowMap q (Bn n) (fun s => W s a) t x) atTop
      (𝓝 (flowMap q B (fun s => W s a) t x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => moll_flow_diff hq
      ⟨hq.le, hm, hB, hW.cont a, hW.zero a⟩ ⟨hq.le, hm, hBn n, hW.cont a, hW.zero a⟩ (hδ n) ht x) ?_
    simpa using (hδ0.mul_const t).mul_const (Real.exp ((q + Mb) * t))
  exact (hh.tendsto _).comp hflow

/-- `sg^B t h_n x → sg^B t h x` for uniformly bounded continuous `h_n → h` pointwise. -/
theorem moll_sg_tendsto_data {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : SgNoise W) {q Mb : ℝ} (hq : 0 ≤ q)
    {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {hn : ℕ → Euc d → ℝ} (hhn : ∀ n, Continuous (hn n)) {h : Euc d → ℝ}
    (hlim : ∀ y, Tendsto (fun n => hn n y) atTop (𝓝 (h y))) {M0 : ℝ}
    (hM0 : ∀ n y, ‖hn n y‖ ≤ M0) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    Tendsto (fun n => sg P W q B t (hn n) x) atTop (𝓝 (sg P W q B t h x)) := by
  unfold sg
  exact tendsto_integral_of_dominated_convergence (fun _ => M0)
    (fun n => moll_meas_comp P hW hq hm hB ht (hhn n) x) (integrable_const _)
    (fun n => ae_of_all _ fun a => hM0 _ _) (ae_of_all _ fun a => hlim _)

/-- **Closing lemma, drift variable.**  Let `B_n → B` uniformly, all with `HasCbBound m Mb`.  If
`‖D^i sg^{B_n} t h‖ ≤ C i` for all `n` and `i ≤ j0` (`j0 ≤ k ≤ m`, `h ∈ C^k` with bounded
derivatives), then `‖D^i sg^{B} t h‖ ≤ C i` for `i ≤ j0`. -/
theorem pois_moll_close_drift (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ m)
    (j0 : ℕ) (hj0 : j0 ≤ k) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {Bn : ℕ → Euc d → Euc d} (hBn : ∀ n, HasCbBound m Mb (Bn n)) {δ : ℕ → ℝ}
    (hδ0 : Tendsto δ atTop (𝓝 0)) (hδ : ∀ n y, ‖Bn n y - B y‖ ≤ δ n)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : SgNoise W) {h : Euc d → ℝ}
    (hh : ContDiff ℝ (k : WithTop ℕ∞) h) {M : ℝ}
    (hM : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) {C : ℕ → ℝ}
    (hC : ∀ n, ∀ i ≤ j0, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q (Bn n) t h) x‖ ≤ C i) :
    ∀ i ≤ j0, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q B t h) x‖ ≤ C i := by
  obtain ⟨C0, -, hsg⟩ := sg_contDiff (d := d) q Mb hq m hm t ht k hk
  have hcd : ∀ B' : Euc d → Euc d, HasCbBound m Mb B' →
      ContDiff ℝ (k : WithTop ℕ∞) (sg P W q B' t h) := fun B' hB' =>
    (hsg P W hW B' hB' h hh M hM t ⟨ht, le_rfl⟩).1
  have hM0 : ∀ y, ‖h y‖ ≤ M := fun y => by simpa using hM 0 (Nat.zero_le _) y
  exact moll_closing (j0 := j0) (fun n => (hcd _ (hBn n)).of_le (by exact_mod_cast hj0))
    ((hcd _ hB).of_le (by exact_mod_cast hj0))
    (fun x => moll_sg_tendsto P hW hq (by omega) hB hBn hδ0 hδ hh.continuous hM0 ht x) hC

/-- **Closing lemma, data variable.**  Let `h_n → h` pointwise, `h_n ∈ C^k` (each with some finite
derivative bounds), `‖h_n‖ ≤ M0`.  If `‖D^i sg^B t h_n‖ ≤ C i` for all `n`, `i ≤ j0 ≤ k ≤ m`, then
`‖D^i sg^B t h‖ ≤ C i` for `i ≤ j0` (`h ∈ C^k` with bounded derivatives). -/
theorem pois_moll_close_data (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ m)
    (j0 : ℕ) (hj0 : j0 ≤ k) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (hW : SgNoise W) {hn : ℕ → Euc d → ℝ}
    (hhn : ∀ n, ContDiff ℝ (k : WithTop ℕ∞) (hn n))
    (hMn : ∀ n, ∃ M : ℝ, ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i (hn n) y‖ ≤ M) {h : Euc d → ℝ}
    (hh : ContDiff ℝ (k : WithTop ℕ∞) h) {M : ℝ}
    (hM : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M)
    (hlim : ∀ y, Tendsto (fun n => hn n y) atTop (𝓝 (h y))) {M0 : ℝ}
    (hM0 : ∀ n y, ‖hn n y‖ ≤ M0) {t : ℝ} (ht : 0 ≤ t) {C : ℕ → ℝ}
    (hC : ∀ n, ∀ i ≤ j0, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q B t (hn n)) x‖ ≤ C i) :
    ∀ i ≤ j0, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q B t h) x‖ ≤ C i := by
  obtain ⟨C0, -, hsg⟩ := sg_contDiff (d := d) q Mb hq m hm t ht k hk
  refine moll_closing (j0 := j0) (fun n => ?_)
    ((hsg P W hW B hB h hh M hM t ⟨ht, le_rfl⟩).1.of_le (by exact_mod_cast hj0))
    (fun x => moll_sg_tendsto_data P hW hq.le (by omega) hB (fun n => (hhn n).continuous) hlim hM0
      ht x) hC
  obtain ⟨Mn, hMn'⟩ := hMn n
  exact (hsg P W hW B hB (hn n) (hhn n) Mn hMn' t ⟨ht, le_rfl⟩).1.of_le (by exact_mod_cast hj0)

end Sg

/-! ### The approximating sequences -/

/-- `HasCbBound k M` for a `C^∞` function with all derivatives bounded. -/
theorem moll_hasCbBound_of_bdd {B : Euc d → Euc d} (hB : ContDiff ℝ ∞ B)
    (hbd : ∀ k, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k B x‖ ≤ C) (k : ℕ) :
    ∃ M : ℝ, HasCbBound k M B := by
  choose Cj hCj using hbd
  refine ⟨∑ j ∈ Finset.range (k + 1), |Cj j|, hB.of_le (by exact_mod_cast le_top),
    fun j hj x => (hCj j x).trans ((le_abs_self _).trans ?_)⟩
  exact Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

/-- **POIS-MOLL, drift.**  For `B` with `HasCbBound m Mb B` (`m ≥ 1`) the mollifications
`B_n = B * η_n` are `C^∞`, satisfy `HasCbBound m Mb (B_n)` (same `Mb`: derivative bounds are
preserved), have all derivatives bounded (`HasCbBound k M_k (B_n)` for every `k`), and
`‖B_n - B‖_∞ ≤ Mb/(n+1)`. -/
theorem pois_moll_drift {m : ℕ} (hm : 1 ≤ m) {Mb : ℝ} {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) :
    ∃ Bn : ℕ → Euc d → Euc d, (∀ n, ContDiff ℝ ∞ (Bn n)) ∧ (∀ n, HasCbBound m Mb (Bn n)) ∧
      (∀ n k, ∃ M : ℝ, HasCbBound k M (Bn n)) ∧
      (∀ n y, ‖Bn n y - B y‖ ≤ Mb / ((n : ℝ) + 1)) := by
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  have hbd0 : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  refine ⟨fun n => mollify n B, fun n => moll_contDiff n hB.1.continuous, fun n => ⟨?_, ?_⟩,
    fun n k => moll_hasCbBound_of_bdd (moll_contDiff n hB.1.continuous)
      (fun k => moll_iter_bdd n hB.1.continuous hbd0 k) k, fun n y => ?_⟩
  · exact (moll_contDiff n hB.1.continuous).of_le (by exact_mod_cast le_top)
  · exact fun j hj x => moll_iter_le n hB.1 (M := fun _ => Mb) hB.2 j hj x
  · have := moll_approx n hMb (pf_lip_of_cb hm hB) y
    exact this

/-- **POIS-MOLL, data.**  A scalar `h ∈ C^k` with `‖D^j h‖ ≤ M j` (`j ≤ k`) is the pointwise limit of
`C^∞` functions `h_n` with the same bounds `‖D^j h_n‖ ≤ M j` (`j ≤ k`), all derivatives of every
`h_n` bounded, and `‖h_n‖ ≤ M 0`. -/
theorem pois_moll_data {k : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ (k : WithTop ℕ∞) h) {M : ℕ → ℝ}
    (hM : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j h y‖ ≤ M j) :
    ∃ hn : ℕ → Euc d → ℝ, (∀ n, ContDiff ℝ ∞ (hn n)) ∧
      (∀ n, ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j (hn n) y‖ ≤ M j) ∧
      (∀ n j, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (hn n) y‖ ≤ C) ∧ (∀ n y, ‖hn n y‖ ≤ M 0) ∧
      (∀ y, Tendsto (fun n => hn n y) atTop (𝓝 (h y))) := by
  have hb0 : ∀ y, ‖h y‖ ≤ M 0 := fun y => by simpa using hM 0 (Nat.zero_le _) y
  have hc : Continuous h := hh.continuous
  refine ⟨fun n => mollify n h, fun n => moll_contDiff n hc,
    fun n j hj y => moll_iter_le n hh hM j hj y,
    fun n j => moll_iter_bdd n hc hb0 j, fun n y => ?_, fun y => moll_tendsto hc y⟩
  simpa using moll_iter_le n hh hM 0 (Nat.zero_le _) y

/-- **Pathwise convergence of the flows.**  For every continuous noise path `w` with `w 0 = 0`, if
`B, B'` have `HasCbBound m Mb` and `‖B' - B‖_∞ ≤ δ`, then
`‖flowMap q B' w t x - flowMap q B w t x‖ ≤ δ t e^{(q+Mb) t}` for all `x` and `t ≥ 0`. -/
theorem pois_moll_flow (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 1 ≤ m) {B B' : Euc d → Euc d}
    (hB : HasCbBound m Mb B) (hB' : HasCbBound m Mb B') {δ : ℝ} (hδ : ∀ y, ‖B' y - B y‖ ≤ δ)
    {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (x : Euc d) :
    ‖flowMap q B' w t x - flowMap q B w t x‖ ≤ δ * t * Real.exp ((q + Mb) * t) :=
  moll_flow_diff hq ⟨hq.le, hm, hB, hw, hw0⟩ ⟨hq.le, hm, hB', hw, hw0⟩ hδ ht x

/-- **POIS-MOLL, interface for GRADSM/HIGHSM.**  For `B` with `HasCbBound m Mb B` there are drifts
`B_n` that are `C^∞`, satisfy `HasCbBound m Mb (B_n)`, have all derivatives bounded, converge
uniformly (`‖B_n - B‖ ≤ Mb/(n+1)`) and such that the following closing property holds for every
Brownian noise: if `‖D^i sg^{B_n} t h‖ ≤ C i` for all `n` and `i ≤ j0` (`j0 ≤ k ≤ m`, `h ∈ C^k`
bounded derivatives, `t ≥ 0`), then `‖D^i sg^{B} t h‖ ≤ C i` for `i ≤ j0`. -/
theorem pois_moll (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) :
    ∃ Bn : ℕ → Euc d → Euc d, (∀ n, ContDiff ℝ ∞ (Bn n)) ∧ (∀ n, HasCbBound m Mb (Bn n)) ∧
      (∀ n k, ∃ M : ℝ, HasCbBound k M (Bn n)) ∧
      (∀ n y, ‖Bn n y - B y‖ ≤ Mb / ((n : ℝ) + 1)) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : ℝ≥0 → Ω → Fin d → ℝ), SgNoise W → ∀ k, k ≤ m → ∀ j0, j0 ≤ k →
        ∀ h : Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) h → ∀ M : ℝ,
        (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) → ∀ t : ℝ, 0 ≤ t → ∀ C : ℕ → ℝ,
        (∀ n, ∀ i ≤ j0, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q (Bn n) t h) x‖ ≤ C i) →
        ∀ i ≤ j0, ∀ x, ‖iteratedFDeriv ℝ i (sg P W q B t h) x‖ ≤ C i := by
  obtain ⟨Bn, h1, h2, h3, h4⟩ := pois_moll_drift (by omega) hB
  refine ⟨Bn, h1, h2, h3, h4, fun {Ω} _ P _ W hW k hk j0 hj0 h hh M hM t ht C hC => ?_⟩
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  have hδ0 : Tendsto (fun n : ℕ => Mb / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Mb
  exact pois_moll_close_drift P q Mb hq m hm k hk j0 hj0 hB h2 hδ0 h4 W hW hh hM ht hC

end HRS.MS.PoisMoll
