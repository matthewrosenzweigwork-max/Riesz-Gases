import Mathlib
import HRS.MS.PoisHighAux2

/-!
# POIS-HIGHSM (part 3): closing lemmas, the induction, and the statements S2, S3

Helper lemmas carry the prefix `hs_`.  Summary of the route (see `PoisHighAux1`, `PoisHighAux2`):

* `hs_close_data`: the bound for compactly supported data passes to all data of the class `HsData`
  (cut-offs `χ(y/(n+1))`, whose derivatives are `O(1/(n+1))`, and `pois_moll_close_data`).
* `hs_smooth_bound`: for a smooth drift, by strong induction on `j` (`pois_gradsmooth` is the case `j = 1`,
  `hs_core` and `hs_close_data` give the step), `‖D^j P_t g‖ ≤ C_j K / √t` with `C_j` depending only on
  `(q, Mb, j)`.
* `pois_highsmooth` (S2): for `B` with `HasCbBound m Mb B` (mollified drifts, `pois_moll` closing) and data
  `g ∈ C^m` with `‖D^i g‖ ≤ M i`: `‖D^j P_t g‖ ≤ C_j t^{-1/2} Σ_{i=1}^{j-1} M i` for `2 ≤ j ≤ m`,
  `0 < t ≤ 1`.
* `pois_highsmooth_lip`: `‖D^j P_t g‖ ≤ C_j t^{-(j-1)/2} ‖Dg‖` (`P_t = P_{t/2} P_{t/2}` and induction).
* `pois_longtime` (S3): `‖D^j P_t r‖ ≤ C_j e^{-c0 (t-1)} Lip(r)` for `t ≥ 1`, and the short time bound
  `‖D^j P_t r‖ ≤ C_j Σ_{i=1}^j ‖D^i r‖` for `t ≤ 1`.

Statement adjustments relative to the packet sketch (documented, harmless): the sums `Σ ‖D^i g‖_∞` are
stated with arbitrary bounds `M i ≥ ‖D^i g‖_∞` (so `‖D^i g‖_∞` itself is allowed); data are bounded
(`‖g‖ ≤ M 0`, which does not enter the constants), as in `pois_lipdecay`; `Lip(g)` is a bound `M 1 ≥ ‖Dg‖`;
the noise is a Brownian filtration.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
  HRS.MS.PoisHigh
open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

noncomputable section

universe u

namespace HRS.MS.PoisHigh

variable {d : ℕ}

/-! ### Cut-offs with decaying derivatives -/

/-- the fixed bump `1` on the unit ball, supported in the ball of radius `2`. -/
def hsChi (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the cut-off `χ(y/(n+1))`. -/
def hsCut (n : ℕ) (y : Euc d) : ℝ := hsChi d (((n : ℝ) + 1)⁻¹ • y)

theorem hs_cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (hsCut (d := d) n) :=
  (hsChi d).contDiff.comp (show ContDiff ℝ ∞ (fun y : Euc d => ((n : ℝ) + 1)⁻¹ • y) from
    contDiff_id.const_smul _)

theorem hs_cut_support (n : ℕ) : HasCompactSupport (hsCut (d := d) n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * ((n : ℝ) + 1))) (fun y hy => ?_)
  rw [mem_closedBall_zero_iff, not_le] at hy
  unfold hsCut
  refine (hsChi d).zero_of_le_dist ?_
  show (2 : ℝ) ≤ dist (((n : ℝ) + 1)⁻¹ • y) 0
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hn]
  linarith

theorem hs_cut_eq_one (n : ℕ) {y : Euc d} (hy : ‖y‖ ≤ (n : ℝ) + 1) : hsCut n y = 1 := by
  unfold hsCut
  refine (hsChi d).one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  show ((n : ℝ) + 1)⁻¹ * ‖y‖ ≤ 1
  rw [inv_mul_le_iff₀ hn]
  linarith

theorem hs_cut_bounds (n : ℕ) (y : Euc d) : 0 ≤ hsCut n y ∧ hsCut n y ≤ 1 :=
  ⟨(hsChi d).nonneg, (hsChi d).le_one⟩

/-- derivatives of the cut-off decay like `1/(n+1)`. -/
theorem hs_cut_deriv (i : ℕ) (hi : 1 ≤ i) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i (hsCut n) y‖ ≤ c * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨c, hc0, hc⟩ := (hsChi d).hasCompactSupport.exists_bound_iteratedFDeriv (hsChi d).contDiff i
  refine ⟨c, hc0, fun n y => ?_⟩
  set L : Euc d →L[ℝ] Euc d := ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Euc d) with hL
  have hcomp : hsCut (d := d) n = ⇑(hsChi d) ∘ ⇑L := by
    funext z; simp [hsCut, hL]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hLn : ‖L‖ ≤ ((n : ℝ) + 1)⁻¹ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun z => ?_)
    simp only [hL, smul_apply, ContinuousLinearMap.id_apply]
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hn.le]
  have h1 := L.iteratedFDeriv_comp_right (hsChi d).contDiff y (i := i) (by exact_mod_cast le_top)
  rw [hcomp, h1]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hi0 : ‖iteratedFDeriv ℝ i (hsChi d) (L y)‖ ≤ c := hc i le_rfl _
  have hpow : ‖L‖ ^ i ≤ ((n : ℝ) + 1)⁻¹ := by
    have h1' : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    calc ‖L‖ ^ i ≤ ((n : ℝ) + 1)⁻¹ ^ i := pow_le_pow_left₀ (norm_nonneg _) hLn i
      _ ≤ ((n : ℝ) + 1)⁻¹ ^ 1 := pow_le_pow_of_le_one (by positivity) h1' hi
      _ = _ := pow_one _
  calc _ ≤ c * ‖L‖ ^ i := mul_le_mul hi0 le_rfl (by positivity) hc0
    _ ≤ c * ((n : ℝ) + 1)⁻¹ := mul_le_mul_of_nonneg_left hpow hc0

/-- product with the cut-off: derivatives change by `O(1/(n+1))`. -/
theorem hs_cut_prod (j : ℕ) (Mall : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (n : ℕ) (g : Euc d → ℝ), ContDiff ℝ ∞ g →
      (∀ l ≤ j, ∀ y, ‖iteratedFDeriv ℝ l g y‖ ≤ Mall) → ∀ i ≤ j, ∀ y,
      ‖iteratedFDeriv ℝ i (fun y => hsCut n y * g y) y‖ ≤ ‖iteratedFDeriv ℝ i g y‖ +
        E * ((n : ℝ) + 1)⁻¹ := by
  have key : ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (n : ℕ) (y : Euc d),
      1 ≤ k → ‖iteratedFDeriv ℝ k (hsCut n) y‖ ≤ c * ((n : ℝ) + 1)⁻¹ := by
    intro k
    by_cases hk : 1 ≤ k
    · obtain ⟨c, hc0, hc⟩ := hs_cut_deriv (d := d) k hk
      exact ⟨c, hc0, fun n y _ => hc n y⟩
    · exact ⟨0, le_rfl, fun n y h => absurd h hk⟩
  choose c hc0 hc using key
  refine ⟨|Mall| * ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.range i,
      ((i.choose (k + 1) : ℝ) * c (k + 1)), mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (hc0 _)), fun n g hg hM i hi y => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcut := hs_cut_contDiff (d := d) n
  have hi' : (i : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by generalize i = n; exact_mod_cast le_top
  have h1 := norm_iteratedFDeriv_mul_le (N := (∞ : WithTop ℕ∞)) hcut hg y hi' 
  refine h1.trans ?_
  rw [Finset.sum_range_succ']
  have h0 : (i.choose 0 : ℝ) * ‖iteratedFDeriv ℝ 0 (hsCut n) y‖ * ‖iteratedFDeriv ℝ (i - 0) g y‖ ≤
      ‖iteratedFDeriv ℝ i g y‖ := by
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [norm_iteratedFDeriv_zero]
    have := (hs_cut_bounds n y)
    rw [Real.norm_of_nonneg this.1]
    exact mul_le_of_le_one_left (norm_nonneg _) this.2
  have h2 : ∑ k ∈ Finset.range i, (i.choose (k + 1) : ℝ) * ‖iteratedFDeriv ℝ (k + 1) (hsCut n) y‖ *
      ‖iteratedFDeriv ℝ (i - (k + 1)) g y‖ ≤
      (|Mall| * ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.range i,
        ((i.choose (k + 1) : ℝ) * c (k + 1))) * ((n : ℝ) + 1)⁻¹ := by
    have hinner : ∑ k ∈ Finset.range i, (i.choose (k + 1) : ℝ) * ‖iteratedFDeriv ℝ (k + 1) (hsCut n) y‖ *
        ‖iteratedFDeriv ℝ (i - (k + 1)) g y‖ ≤
        ∑ k ∈ Finset.range i, (i.choose (k + 1) : ℝ) * c (k + 1) * ((n : ℝ) + 1)⁻¹ * |Mall| := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : k + 1 ≤ i := Finset.mem_range.1 hk
      have a1 := hc (k + 1) n y le_add_self
      have a2 : ‖iteratedFDeriv ℝ (i - (k + 1)) g y‖ ≤ |Mall| :=
        (hM (i - (k + 1)) (by omega) y).trans (le_abs_self _)
      have hcc : (0 : ℝ) ≤ i.choose (k + 1) := Nat.cast_nonneg _
      calc (i.choose (k + 1) : ℝ) * ‖iteratedFDeriv ℝ (k + 1) (hsCut n) y‖ *
            ‖iteratedFDeriv ℝ (i - (k + 1)) g y‖
          ≤ (i.choose (k + 1) : ℝ) * (c (k + 1) * ((n : ℝ) + 1)⁻¹) * |Mall| := by
            gcongr
            exact mul_nonneg hcc (mul_nonneg (hc0 _) (inv_nonneg.2 hn.le))
        _ = _ := by ring
    refine hinner.trans ?_
    have hsi : ∑ k ∈ Finset.range i, (i.choose (k + 1) : ℝ) * c (k + 1) * ((n : ℝ) + 1)⁻¹ * |Mall| =
        (|Mall| * ∑ k ∈ Finset.range i, ((i.choose (k + 1) : ℝ) * c (k + 1))) * ((n : ℝ) + 1)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hsi]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
    exact Finset.single_le_sum (f := fun i => ∑ k ∈ Finset.range i, ((i.choose (k + 1) : ℝ) * c (k + 1)))
      (fun i _ => Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (hc0 _))
      (Finset.mem_range.2 (by omega))
  linarith

/-! ### Closing in the data variable -/

section Close

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

set_option maxHeartbeats 2000000 in
/-- From compactly supported data to all data of the class (smooth drift). -/
theorem hs_close_data [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m) {B : Euc d → Euc d}
    (hBm : HasCbBound m Mb B) {C : ℝ} (hC0 : 0 ≤ C)
    (hCS : HsBound HasCompactSupport P W q B j C) : HsBound (fun _ => True) P W q B j C := by
  intro g hg _ K hK t ht0 ht1 x
  have hWs := sgNoise_of_brownian hW
  have hm2 : 2 ≤ m := by omega
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 1 (by omega) (Or.inl le_rfl) 0)
  choose Cg hCg using hg.2
  set Mall : ℝ := ∑ l ∈ Finset.range (j + 1), |Cg l| with hMall
  have hMallb : ∀ l ≤ j, ∀ y, ‖iteratedFDeriv ℝ l g y‖ ≤ Mall := fun l hl y =>
    (hCg l y).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun l => |Cg l|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
  obtain ⟨E, hE0, hE⟩ := hs_cut_prod (d := d) j Mall
  have hMall0 : 0 ≤ Mall := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨Csg, -, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm2 1 zero_le_one j hjm
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  -- the claim with an `ε` of room
  have key : ∀ ε : ℝ, 0 < ε → ‖iteratedFDeriv ℝ j (sg P W q B t g) x‖ ≤ C * (K + ε) / Real.sqrt t := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (E / ε)
    set hn : ℕ → Euc d → ℝ := fun n y => hsCut (n + N) y * g y with hhn
    have hEN : ∀ n : ℕ, E * ((((n + N : ℕ) : ℝ) + 1)⁻¹) ≤ ε := by
      intro n
      have h1 : E / ε < ((n + N : ℕ) : ℝ) + 1 := by
        have : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N n
        linarith
      rw [div_lt_iff₀ hε] at h1
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      linarith
    have hhnc : ∀ n, ContDiff ℝ ∞ (hn n) := fun n => (hs_cut_contDiff _).mul hg.1
    have hhns : ∀ n, HasCompactSupport (hn n) := fun n => (hs_cut_support _).mul_right
    have hhnD : ∀ n, HsData (hn n) := fun n => ⟨hhnc n, fun k => by
      obtain ⟨C', -, hC'⟩ := (hhns n).exists_bound_iteratedFDeriv (hhnc n) k
      exact ⟨C', hC' k le_rfl⟩⟩
    have hbd : ∀ n, ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i (hn n) y‖ ≤ ‖iteratedFDeriv ℝ i g y‖ + ε := by
      intro n i hi y
      have := hE (n + N) g hg.1 hMallb i hi y
      have h2 := hEN n
      exact this.trans (by linarith)
    have hbdM : ∀ n, ∀ i ≤ j, ∀ y, ‖iteratedFDeriv ℝ i (hn n) y‖ ≤ Mall + ε := by
      intro n i hi y
      exact (hbd n i hi y).trans (by linarith [hMallb i hi y])
    have hbdc : ∀ n t' (_ : 0 < t') (_ : t' ≤ 1) x', ‖iteratedFDeriv ℝ j (sg P W q B t' (hn n)) x'‖ ≤
        C * (K + ε) / Real.sqrt t' := fun n t' h0 h1 x' =>
      hCS (hn n) (hhnD n) (hhns n) (K + ε) (fun i hi hi' y =>
        (hbd n i hi.le y).trans (by linarith [hK i hi hi' y])) t' h0 h1 x'
    have hlow : ∀ n, ∀ i ≤ j, ∀ x', ‖iteratedFDeriv ℝ i (sg P W q B t (hn n)) x'‖ ≤
        Csg * (Mall + ε) := by
      intro n i hi x'
      obtain ⟨-, -, h3⟩ := hCsg P W hWs B hBm (hn n) ((hhnc n).of_le (by generalize j = k; exact_mod_cast le_top))
        (Mall + ε) (fun l hl y => hbdM n l hl y) t ⟨ht0.le, ht1⟩
      exact h3 i hi x'
    have hlim : ∀ y, Tendsto (fun n => hn n y) atTop (𝓝 (g y)) := by
      intro y
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖y‖⌉₊] with n hn'
      have h1 : ‖y‖ ≤ ((n + N : ℕ) : ℝ) + 1 := by
        have := Nat.le_ceil ‖y‖
        have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast hn'.trans (Nat.le_add_right n N)
        linarith
      show g y = hsCut (n + N) y * g y
      rw [hs_cut_eq_one _ h1, one_mul]
    have hM0 : ∀ n y, ‖hn n y‖ ≤ Mall + ε := fun n y => by
      have := hbdM n 0 (Nat.zero_le _) y
      rwa [norm_iteratedFDeriv_zero] at this
    have hclose := pois_moll_close_data (P := P) q Mb hq m hm2 j hjm j le_rfl hBm W hWs
      (hn := hn) (fun n => (hhnc n).of_le (by generalize j = k; exact_mod_cast le_top))
      (fun n => by
        obtain ⟨M', hM'⟩ := (hhnD n).2 0
        exact ⟨Mall + ε, fun i hi y => hbdM n i hi y⟩)
      (h := g) (hg.1.of_le (by generalize j = k; exact_mod_cast le_top)) (M := Mall) hMallb hlim hM0
      ht0.le (C := fun i => if i = j then C * (K + ε) / Real.sqrt t else Csg * (Mall + ε))
      (fun n i hi x' => by
        by_cases hij : i = j
        · subst hij; simp only [if_true]; exact hbdc n t ht0 ht1 x'
        · simp only [hij, ite_false]; exact hlow n i hi x')
    have := hclose j le_rfl x
    simpa using this
  -- let `ε → 0`
  set c : ℝ := C / Real.sqrt t with hc
  have hc0 : 0 ≤ c := by positivity
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  have h1 := key (δ / (c + 1)) (by positivity)
  refine h1.trans ?_
  have : C * (K + δ / (c + 1)) / Real.sqrt t = C * K / Real.sqrt t + c * (δ / (c + 1)) := by
    rw [hc]; ring
  rw [this]
  have h2 : c * (δ / (c + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

end Close

/-! ### The induction for smooth drifts and the statement S2 -/

theorem hs_data_bound {g : Euc d → ℝ} (hg : HsData g) (k : ℕ) :
    ∃ M : ℝ, ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M := by
  choose Cg hCg using hg.2
  refine ⟨∑ l ∈ Finset.range (k + 1), |Cg l|, fun i hi y => (hCg i y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun l => |Cg l|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))))⟩

/-- Smooth drift: `HsBound` at every order `1 ≤ j ≤ m`, with constants depending only on `(q, Mb, j)`. -/
theorem hs_smooth_bound (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) :
    ∀ j : ℕ, 1 ≤ j → j ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W →
        ∀ B : Euc d → Euc d, HasCbBound m Mb B → (∀ k, ∃ M : ℝ, HasCbBound k M B) →
        HsBound (fun _ => True) P W q B j C := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjm
    rcases Nat.eq_or_lt_of_le hj1 with hj | hj
    · subst hj
      refine ⟨Real.sqrt (Mb + 1), Real.sqrt_nonneg _, fun {Ω} {mΩ} P _ ℱ W hW B hBm hBall => ?_⟩
      intro g hg _ K hK t ht0 ht1 x
      have hK' : ∀ y, ‖g y‖ ≤ K := fun y => by
        have := hK 0 (by norm_num) (Or.inr rfl) y
        rwa [norm_iteratedFDeriv_zero] at this
      have hfM := hs_data_bound hg 2
      have := pois_gradsmooth hq hm hBm hW hg.1 hK' hfM ht0 ht1 x
      rw [norm_iteratedFDeriv_one]
      calc _ ≤ _ := this
        _ = Real.sqrt (Mb + 1) * K / Real.sqrt t := rfl
    · have hall : ∀ l : ℕ, ∃ C : ℝ, (1 ≤ l → l < j → 0 ≤ C ∧
          ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
            (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W →
            ∀ B : Euc d → Euc d, HasCbBound m Mb B → (∀ k, ∃ M : ℝ, HasCbBound k M B) →
            HsBound (fun _ => True) P W q B l C) := by
        intro l
        by_cases h : 1 ≤ l ∧ l < j
        · obtain ⟨C, hC⟩ := ih l h.2 h.1 (by omega)
          exact ⟨C, fun _ _ => hC⟩
        · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
      choose Cs hCs using hall
      have hj2 : 2 ≤ j := hj
      have hA0 : 0 ≤ hsA q Mb j Cs := by
        unfold hsA
        have : 0 ≤ ∑ l ∈ Finset.range j, |Cs l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have := Real.exp_pos (q + Mb)
        positivity
      have hC0 : 0 ≤ hsC q Mb j Cs := by unfold hsC; positivity
      refine ⟨hsC q Mb j Cs, hC0, fun {Ω} {mΩ} P _ ℱ W hW B hBm hBall => ?_⟩
      exact hs_close_data hW hq hj2 hjm hBm hC0
        (hs_core hW hq hj2 hjm hBm hBall Cs (fun l h1 h2 => (hCs l h1 h2).2 P ℱ W hW B hBm hBall))

set_option maxHeartbeats 2000000 in
/-- **POIS-HIGHSM, S2 (`pois_highsmooth`).**  For `q > 0`, `B` with `HasCbBound m Mb B` (`2 ≤ m`),
a Brownian filtration and `g ∈ C^m` with `‖D^i g‖ ≤ M i` (`i ≤ m`; `M 0` bounds `g` and does not enter),
for `2 ≤ j ≤ m` and `0 < t ≤ 1`:
`‖D^j P_t g‖ ≤ C_j t^{-1/2} ∑_{i=1}^{j-1} M i`, `C_j` depending only on `(q, Mb, j)`. -/
theorem pois_highsmooth (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (j : ℕ)
    (hj : 2 ≤ j) (hjm : j ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ g : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M i) → ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t g) x‖ ≤
        C * (Real.sqrt t)⁻¹ * ∑ i ∈ Finset.Icc 1 (j - 1), M i := by
  obtain ⟨C, hC0, hCb⟩ := hs_smooth_bound (d := d) q Mb hq hMb m hm j (by omega) hjm
  obtain ⟨Csg, -, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm 1 zero_le_one j hjm
  refine ⟨C, hC0, fun {Ω} {mΩ} P _ ℱ W hW B hBm g hg M hM t ht0 ht1 x => ?_⟩
  have hWs := sgNoise_of_brownian hW
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set K : ℝ := ∑ i ∈ Finset.Icc 1 (j - 1), M i with hKdef
  have hKM : ∀ i, 1 ≤ i → i ≤ j - 1 → M i ≤ K := fun i h1 h2 =>
    Finset.single_le_sum (f := fun i => M i) (fun i hi => hM0 i (by
      have := (Finset.mem_Icc.1 hi).2; omega)) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i hi => hM0 i (by
    have := (Finset.mem_Icc.1 hi).2; omega)
  set M' : ℝ := ∑ i ∈ Finset.range (m + 1), |M i| with hM'def
  have hMM' : ∀ i ≤ m, M i ≤ M' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  obtain ⟨Bn, -, hBnm, hBn3, -, hclose⟩ := pois_moll q Mb hq m hm hBm
  obtain ⟨hn, hnc, hnM, hnb, hn0, hnlim⟩ := pois_moll_data (k := m) hg (M := M) hM
  have hhnD : ∀ k, HsData (hn k) := fun k => ⟨hnc k, fun l => hnb k l⟩
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  -- the bound for the smooth drifts and the original data
  have hdata : ∀ n, ∀ i ≤ j, ∀ x', ‖iteratedFDeriv ℝ i (sg P W q (Bn n) t g) x'‖ ≤
      if i = j then C * K / Real.sqrt t else Csg * M' := by
    intro n i hi x'
    have hmain : ∀ k, ∀ x'', ‖iteratedFDeriv ℝ j (sg P W q (Bn n) t (hn k)) x''‖ ≤
        C * K / Real.sqrt t := fun k x'' =>
      hCb P ℱ W hW (Bn n) (hBnm n) (hBn3 n) (hn k) (hhnD k) trivial K
        (fun i' hi' hi'' y => (hnM k i' (by omega) y).trans ((hKM i' (by omega) (by omega))))
        t ht0 ht1 x''
    have hlow : ∀ k, ∀ i' ≤ j, ∀ x'', ‖iteratedFDeriv ℝ i' (sg P W q (Bn n) t (hn k)) x''‖ ≤
        Csg * M' := by
      intro k i' hi' x''
      obtain ⟨-, -, h3⟩ := hCsg P W hWs (Bn n) (hBnm n) (hn k)
        ((hnc k).of_le (by generalize j = k'; exact_mod_cast le_top)) M'
        (fun l hl y => (hnM k l (by omega) y).trans (hMM' l (by omega))) t ⟨ht0.le, ht1⟩
      exact h3 i' hi' x''
    have hcl := pois_moll_close_data (P := P) q Mb hq m hm j hjm j le_rfl (hBnm n) W hWs
      (hn := hn) (fun k => (hnc k).of_le (by generalize j = k'; exact_mod_cast le_top))
      (fun k => ⟨M', fun l hl y => (hnM k l (by omega) y).trans (hMM' l (by omega))⟩)
      (h := g) (hg.of_le (by exact_mod_cast hjm)) (M := M') (fun l hl y => (hM l (by omega) y).trans
        (hMM' l (by omega))) hnlim (M0 := M 0) hn0 ht0.le
      (C := fun i => if i = j then C * K / Real.sqrt t else Csg * M')
      (fun k i' hi' x'' => by
        by_cases hij : i' = j
        · subst hij; simp only [if_true]; exact hmain k x''
        · simp only [hij, ite_false]; exact hlow k i' hi' x'')
    exact hcl i hi x'
  have hfin := hclose P W hWs m le_rfl j hjm g hg M' (fun i hi y => (hM i hi y).trans (hMM' i hi)) t
    ht0.le (fun i => if i = j then C * K / Real.sqrt t else Csg * M') hdata j le_rfl x
  simp only [if_true] at hfin
  calc _ ≤ C * K / Real.sqrt t := hfin
    _ = C * (Real.sqrt t)⁻¹ * K := by rw [div_eq_mul_inv]; ring

/-- `‖D^j P_t g‖ ≤ C_j t^{-(j-1)/2} ‖Dg‖` (`1 ≤ j ≤ m`, `0 < t ≤ 1`), from S2 and `P_t = P_{t/2} P_{t/2}`. -/
theorem pois_highsmooth_lip (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) :
    ∀ j : ℕ, 1 ≤ j → j ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W →
        ∀ B : Euc d → Euc d, HasCbBound m Mb B →
        ∀ g : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g → ∀ M : ℕ → ℝ,
        (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M i) → ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
        ‖iteratedFDeriv ℝ j (sg P W q B t g) x‖ ≤ C * ((Real.sqrt t)⁻¹) ^ (j - 1) * M 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjm
    rcases Nat.eq_or_lt_of_le hj1 with hj | hj
    · subst hj
      refine ⟨Real.exp (q + Mb), (Real.exp_pos _).le, fun {Ω} {mΩ} P _ ℱ W hW B hBm g hg M hM t ht0
        ht1 x => ?_⟩
      have hWs := sgNoise_of_brownian hW
      have hM1 : 0 ≤ M 1 := (norm_nonneg _).trans (by
        have := hM 1 (by omega) 0; rwa [norm_iteratedFDeriv_one] at this)
      have hh : ContDiff ℝ (1 : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast (by omega : 1 ≤ m))
      have := sg_fderiv_bound q Mb hq m hm P W hWs B hBm g hh (M 0) (M 1)
        (fun y => by simpa using hM 0 (by omega) y)
        (fun y => by have := hM 1 (by omega) y; rwa [norm_iteratedFDeriv_one] at this) t ht0.le x
      rw [norm_iteratedFDeriv_one]
      calc _ ≤ _ := this
        _ ≤ Real.exp (q + Mb) * M 1 := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hM1
          nlinarith
        _ = Real.exp (q + Mb) * ((Real.sqrt t)⁻¹) ^ (1 - 1) * M 1 := by rw [Nat.sub_self, pow_zero, mul_one]
    · have hj2 : 2 ≤ j := hj
      have hall : ∀ l : ℕ, ∃ C : ℝ, (1 ≤ l → l < j → 0 ≤ C ∧
          ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
            (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ), IsBrownianFiltration P ℱ W →
            ∀ B : Euc d → Euc d, HasCbBound m Mb B →
            ∀ g : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g → ∀ M : ℕ → ℝ,
            (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M i) → ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
            ‖iteratedFDeriv ℝ l (sg P W q B t g) x‖ ≤ C * ((Real.sqrt t)⁻¹) ^ (l - 1) * M 1) := by
        intro l
        by_cases h : 1 ≤ l ∧ l < j
        · obtain ⟨C, hC⟩ := ih l h.2 h.1 (by omega)
          exact ⟨C, fun _ _ => hC⟩
        · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
      choose Cs hCs using hall
      obtain ⟨C2, hC20, hC2⟩ := pois_highsmooth (d := d) q Mb hq hMb m hm j hj2 hjm
      obtain ⟨Cm, -, hCm⟩ := sg_contDiff (d := d) q Mb hq m hm 1 zero_le_one m le_rfl
      set S : ℝ := ∑ i ∈ Finset.range j, |Cs i| with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
      refine ⟨C2 * S * 2 ^ (j - 1), by positivity, fun {Ω} {mΩ} P _ ℱ W hW B hBm g hg M hM t ht0
        ht1 x => ?_⟩
      have hWs := sgNoise_of_brownian hW
      have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
      set M' : ℝ := ∑ i ∈ Finset.range (m + 1), |M i| with hM'def
      have hMM' : ∀ i ≤ m, M i ≤ M' := fun i hi =>
        (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.2 (by omega)))
      have hM'0 : 0 ≤ M' := Finset.sum_nonneg fun _ _ => abs_nonneg _
      set s : ℝ := (Real.sqrt t)⁻¹ with hsdef
      have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
      have hs1 : 1 ≤ s := by
        rw [hsdef, one_le_inv₀ hsq]; exact Real.sqrt_le_one.2 ht1
      set τ : ℝ := t / 2 with hτ
      have hτ0 : 0 < τ := by positivity
      have hτ1 : τ ≤ 1 := by linarith
      have hr : (Real.sqrt τ)⁻¹ ≤ 2 * s := by
        have h1 : (Real.sqrt τ)⁻¹ = Real.sqrt 2 * s := by
          rw [hτ, Real.sqrt_div ht0.le, hsdef, inv_div, div_eq_mul_inv]
        have h2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        rw [h1]
        exact mul_le_mul_of_nonneg_right h2 (by linarith)
      have hr1 : 1 ≤ (Real.sqrt τ)⁻¹ := by
        rw [one_le_inv₀ (Real.sqrt_pos.2 hτ0)]; exact Real.sqrt_le_one.2 hτ1
      have hM1 : 0 ≤ M 1 := hM0 1 (by omega)
      -- the intermediate function
      obtain ⟨hcd, -, hbd⟩ := hCm P W hWs B hBm g hg M' (fun i hi y => (hM i hi y).trans (hMM' i hi))
        τ ⟨hτ0.le, hτ1⟩
      set h : Euc d → ℝ := sg P W q B τ g with hh
      -- bounds on the derivatives of `h`
      set Mh : ℕ → ℝ := fun i => if 1 ≤ i ∧ i < j then |Cs i| * (2 * s) ^ (j - 2) * M 1
        else Cm * M' with hMh
      have hlow : ∀ i, 1 ≤ i → i < j → ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ |Cs i| * (2 * s) ^ (j - 2) * M 1 := by
        intro i h1 h2 y
        have := ((hCs i h1 h2).2 P ℱ W hW B hBm g hg M hM τ hτ0 hτ1 y)
        refine this.trans ?_
        have hpow : ((Real.sqrt τ)⁻¹) ^ (i - 1) ≤ (2 * s) ^ (j - 2) :=
          (pow_le_pow_left₀ (by positivity) hr _).trans
            (pow_le_pow_right₀ (by linarith) (by omega))
        exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hpow (by positivity)
          (abs_nonneg _)) hM1
      have hMhb : ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ Mh i := by
        intro i hi y
        by_cases hc : 1 ≤ i ∧ i < j
        · simp only [hMh, hc, and_self, if_true]
          exact hlow i hc.1 hc.2 y
        · simp only [hMh, hc, if_false]
          exact hbd i hi y
      have hS2 := hC2 P ℱ W hW B hBm h hcd Mh hMhb τ hτ0 hτ1 x
      have hMhI : ∀ i ∈ Finset.Icc 1 (j - 1), Mh i = |Cs i| * (2 * s) ^ (j - 2) * M 1 := by
        intro i hi
        have hi' := Finset.mem_Icc.1 hi
        simp only [hMh, show 1 ≤ i ∧ i < j from ⟨hi'.1, by omega⟩, and_self, ite_true]
      have h2s0 : 0 ≤ (2 * s) ^ (j - 2) := pow_nonneg (by linarith) _
      have hsum : ∑ i ∈ Finset.Icc 1 (j - 1), Mh i ≤ S * (2 * s) ^ (j - 2) * M 1 := by
        rw [Finset.sum_congr rfl hMhI, ← Finset.sum_mul, ← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ h2s0) hM1
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
        intro i hi
        have hi' := Finset.mem_Icc.1 hi
        exact Finset.mem_range.2 (by omega)
      have hmk : sg P W q B t g = sg P W q B τ h := by
        funext y
        have := sg_markov_C2 hW hq.le (by omega : 1 ≤ m) hBm (h := g)
          (hg.of_le (by exact_mod_cast hm)) (M := M') (fun i hi y => (hM i (by omega) y).trans
            (hMM' i (by omega))) hτ0.le hτ0.le y
        rw [hh]
        have e : τ + τ = t := by rw [hτ]; ring
        rw [e] at this
        exact this
      rw [hmk]
      refine hS2.trans ?_
      have hpow : (2 * s) ^ (j - 1) = (2 * s) * (2 * s) ^ (j - 2) := by
        rw [← pow_succ']; congr 1; omega
      have h2s : 0 ≤ 2 * s := by positivity
      calc C2 * (Real.sqrt τ)⁻¹ * ∑ i ∈ Finset.Icc 1 (j - 1), Mh i
          ≤ C2 * (2 * s) * (S * (2 * s) ^ (j - 2) * M 1) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hr hC20) hsum
              (Finset.sum_nonneg fun i hi => ?_) (by positivity)
            rw [hMhI i hi]; exact mul_nonneg (mul_nonneg (abs_nonneg _) h2s0) hM1
        _ = C2 * S * 2 ^ (j - 1) * s ^ (j - 1) * M 1 := by
            have : (2 * s) * (2 * s) ^ (j - 2) = 2 ^ (j - 1) * s ^ (j - 1) := by
              rw [← hpow, mul_pow]
            calc C2 * (2 * s) * (S * (2 * s) ^ (j - 2) * M 1)
                = C2 * S * ((2 * s) * (2 * s) ^ (j - 2)) * M 1 := by ring
              _ = _ := by rw [this]; ring

/-! ### S3: short and long time bounds -/

/-- Chain rule bound using only the derivatives of order `≥ 1` of the outer function. -/
theorem hs_comp_deriv_only {g : Euc d → ℝ} {f : Euc d → Euc d} {n : ℕ} (hn : 1 ≤ n)
    (hg : ContDiff ℝ (n : WithTop ℕ∞) g) (hf : ContDiff ℝ (n : WithTop ℕ∞) f) (x : Euc d)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => g (f y)) x‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  set g' : Euc d → ℝ := fun z => g z - g (f x) with hg'
  have hgc : ContDiff ℝ (n : WithTop ℕ∞) g' := hg.sub contDiff_const
  have hcomp := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (N := (n : WithTop ℕ∞)) hgc hf le_rfl x
    (C := C) (D := D) (fun i hi => ?_) hD
  · have e1 : (fun y => g' (f y)) = (fun y => g (f y)) - fun _ => g (f x) := rfl
    have e2 : iteratedFDeriv ℝ n (fun y => g' (f y)) x = iteratedFDeriv ℝ n (fun y => g (f y)) x := by
      have hcf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun y => g (f y)) x := (hg.comp hf).contDiffAt
      rw [e1, iteratedFDeriv_sub_apply hcf contDiff_const.contDiffAt,
        iteratedFDeriv_const_of_ne (by omega)]
      simp
    have := hcomp
    simpa [Function.comp_def, e2] using this
  · rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      rw [norm_iteratedFDeriv_zero]
      simpa [hg'] using hC0
    · have e3 : iteratedFDeriv ℝ i g' (f x) = iteratedFDeriv ℝ i g (f x) := by
        have e1 : g' = g - fun _ => g (f x) := rfl
        rw [e1, iteratedFDeriv_sub_apply ((hg.of_le (by exact_mod_cast hi)).contDiffAt)
          contDiff_const.contDiffAt, iteratedFDeriv_const_of_ne (by omega)]
        simp
      rw [e3]
      exact hC i h0 hi

/-- **POIS-HIGHSM, S3, short time.**  `‖D^j P_t r‖ ≤ C_j ∑_{i=1}^j M i` for `0 ≤ t ≤ 1`
(only derivatives of `r` of order `≥ 1` enter). -/
theorem pois_shorttime (q Mb : ℝ) (hq : 0 < q) (m : ℕ) (hm : 2 ≤ m) (j : ℕ) (hj1 : 1 ≤ j)
    (hjm : j ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i r y‖ ≤ M i) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤ C * ∑ i ∈ Finset.Icc 1 j, M i := by
  obtain ⟨C0, hC0, hflow⟩ := pois_flow (d := d) q Mb hq m hm 1 zero_le_one
  set D : ℝ := max 1 C0 with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  obtain ⟨Csg, -, hCsg⟩ := sg_contDiff (d := d) q Mb hq m hm 1 zero_le_one j hjm
  refine ⟨(j.factorial : ℝ) * D ^ j, by positivity, fun {Ω} {mΩ} P _ ℱ W hW B hBm r hr M hM t ht0
    ht1 x => ?_⟩
  have hWs := sgNoise_of_brownian hW
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  set M' : ℝ := ∑ i ∈ Finset.range (m + 1), |M i| with hM'def
  have hMM' : ∀ i ≤ m, M i ≤ M' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  set Mc : ℝ := ∑ i ∈ Finset.Icc 1 j, M i with hMc
  have hMc0 : 0 ≤ Mc := Finset.sum_nonneg fun i hi => hM0 i (by
    have := (Finset.mem_Icc.1 hi).2; omega)
  have hMcb : ∀ i, 1 ≤ i → i ≤ j → M i ≤ Mc := fun i h1 h2 =>
    Finset.single_le_sum (f := fun i => M i) (fun i hi => hM0 i (by
      have := (Finset.mem_Icc.1 hi).2; omega)) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hjle : (j : WithTop ℕ∞) ≤ (m : WithTop ℕ∞) := by exact_mod_cast hjm
  obtain ⟨hcd, hform, -⟩ := hCsg P W hWs B hBm r (hr.of_le hjle) M'
    (fun i hi y => (hM i (by omega) y).trans (hMM' i (by omega))) t ⟨ht0, ht1⟩
  rw [hform j le_rfl x]
  have hpt : ∀ o, ‖iteratedFDeriv ℝ j (fun y => r (flowMap q B (fun s => W s o) t y)) x‖ ≤
      (j.factorial : ℝ) * Mc * D ^ j := by
    intro o
    have hfl := hflow B hBm (fun s => W s o) (hWs.cont o) (hWs.zero o)
    obtain ⟨hfc, hfb⟩ := hfl.2 t ⟨ht0, ht1⟩
    refine hs_comp_deriv_only hj1 (hr.of_le hjle) (hfc.of_le hjle) x hMc0
      (fun i h1 h2 => (hM i (by omega) _).trans (hMcb i h1 h2)) (fun i h1 h2 => ?_)
    exact (hfb i h1 (by omega) x).trans ((le_max_right _ _).trans (le_self_pow₀ hD1 (by omega)))
  have hb : ‖∫ o, iteratedFDeriv ℝ j (fun y => r (flowMap q B (fun s => W s o) t y)) x ∂P‖ ≤
      (j.factorial : ℝ) * Mc * D ^ j := by
    simpa using norm_integral_le_of_norm_le_const (μ := P)
      (f := fun o => iteratedFDeriv ℝ j (fun y => r (flowMap q B (fun s => W s o) t y)) x)
      (C := (j.factorial : ℝ) * Mc * D ^ j) (Eventually.of_forall hpt)
  refine hb.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 2000000 in
/-- **POIS-HIGHSM, S3, long time (`pois_longtime`).**  For `t ≥ 1`, `1 ≤ j ≤ m`, `r ∈ C^m` with
`‖D^i r‖ ≤ M i`: `‖D^j P_t r‖ ≤ C_j e^{-c0 (t-1)} M 1` (`c0 = pm_c0 q Mb`, `M 1 ≥ Lip r`). -/
theorem pois_longtime (q Mb : ℝ) (hq : 0 < q) (hMb : 0 ≤ Mb) (m : ℕ) (hm : 2 ≤ m) (j : ℕ)
    (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ),
      IsBrownianFiltration P ℱ W → ∀ B : Euc d → Euc d, HasCbBound m Mb B →
      ∀ r : Euc d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) r → ∀ M : ℕ → ℝ,
      (∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i r y‖ ≤ M i) → ∀ t : ℝ, 1 ≤ t → ∀ x,
      ‖iteratedFDeriv ℝ j (sg P W q B t r) x‖ ≤
        C * Real.exp (-(pm_c0 q Mb) * (t - 1)) * M 1 := by
  obtain ⟨C1, hC10, hC1⟩ := pois_highsmooth_lip (d := d) q Mb hq hMb m hm j hj1 hjm
  have hκ : 0 < pm_kappa q Mb := Real.exp_pos _
  refine ⟨C1 * (pm_kappa q Mb)⁻¹, by positivity, fun {Ω} {mΩ} P _ ℱ W hW B hBm r hr M hM t ht1 x => ?_⟩
  have hWs := sgNoise_of_brownian hW
  have hM0 : ∀ i ≤ m, 0 ≤ M i := fun i hi => (norm_nonneg _).trans (hM i hi 0)
  have hM1 : 0 ≤ M 1 := hM0 1 (by omega)
  set M' : ℝ := ∑ i ∈ Finset.range (m + 1), |M i| with hM'def
  have hMM' : ∀ i ≤ m, M i ≤ M' := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega)))
  have hM'0 : 0 ≤ M' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hs0 : 0 ≤ t - 1 := by linarith
  obtain ⟨CmT, hCmT1, hCmT⟩ := sg_contDiff (d := d) q Mb hq m hm (t - 1) hs0 m le_rfl
  obtain ⟨hcd, -, hbd⟩ := hCmT P W hWs B hBm r hr M' (fun i hi y => (hM i hi y).trans (hMM' i hi))
    (t - 1) ⟨hs0, le_rfl⟩
  set g : Euc d → ℝ := sg P W q B (t - 1) r with hg
  set L : ℝ := (pm_kappa q Mb)⁻¹ * Real.exp (-(pm_c0 q Mb) * (t - 1)) * M 1 with hL
  have hL0 : 0 ≤ L := by positivity
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by exact_mod_cast hm)
  have hlip : ∀ y z, |g y - g z| ≤ L * ‖y - z‖ := by
    intro y z
    have := HRS.MS.PoisLip.pois_lipdecay hq hm hBm hW hr2 (M0 := M 0) (M1 := M 1) (M2 := M 2)
      (fun y => by simpa using hM 0 (by omega) y)
      (fun y => by have := hM 1 (by omega) y; rwa [norm_iteratedFDeriv_one] at this)
      (fun y => hM 2 hm y) hs0 y z
    refine this.trans (le_of_eq ?_)
    rw [hL]
  have hDg : ∀ y, ‖fderiv ℝ g y‖ ≤ L := fun y =>
    norm_fderiv_le_of_lip' ℝ hL0 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hlip z y)
  -- apply the `t = 1` bound to `g`
  have hMg : ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ (fun i => if i = 1 then L else CmT * M') i := by
    intro i hi y
    by_cases h1 : i = 1
    · subst h1
      simp only [ite_true]
      rw [norm_iteratedFDeriv_one]; exact hDg y
    · simp only [h1, ite_false]
      exact hbd i hi y
  have h1 := hC1 P ℱ W hW B hBm g hcd (fun i => if i = 1 then L else CmT * M') hMg 1 one_pos
    le_rfl x
  have hmk : sg P W q B t r = sg P W q B 1 g := by
    funext y
    have := sg_markov_C2 hW hq.le (by omega : 1 ≤ m) hBm (h := r) hr2 (M := M')
      (fun i hi y => (hM i (by omega) y).trans (hMM' i (by omega))) zero_le_one hs0 y
    rw [hg]
    have e : (1 : ℝ) + (t - 1) = t := by ring
    rw [e] at this
    exact this
  rw [hmk]
  simp only [Real.sqrt_one, inv_one, one_pow, mul_one, ite_true] at h1
  refine h1.trans (le_of_eq ?_)
  rw [hL]; ring

end HRS.MS.PoisHigh
