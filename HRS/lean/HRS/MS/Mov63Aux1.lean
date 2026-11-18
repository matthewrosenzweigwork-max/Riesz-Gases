import HRS.MS.MovOpAux3
import HRS.MS.MovForceTie
import HRS.MS.MovBridgeAux7
import HRS.MS.MovOscAux5

/-!
# S6.3, packet N1 (part 1): `Σ^n ⊂ C_b^i` for non-Schwartz data

Namespace `HRS.MS.Mov63`, helper prefix `mn_`.  Infrastructure for S6.3 (`mov_nonlinear`); not manuscript rows.

* `mn_ae_eq_cont` : two continuous functions that agree a.e. agree everywhere.
* `mn_sobolev_emb_gen` : for `i + d/2 < n` every `f ∈ Σ^n` (`MemOsc n f`, NOT necessarily Schwartz) has a `C^i`
  representative `g` (`f =ᵐ g`) with `‖D^k g x‖ ≤ C ‖f‖_{Σ^n}` for all `k ≤ i`, `x`; the constant is independent of `f`.
  Proof: the Hermite partial sums are Schwartz and (along a fast subsequence) form a series of `C^i` functions
  with summable sup-bounds (`mo_sobolev_emb`, `mo_hsum_tail`); `contDiff_tsum`.
* Junk-value discipline: all statements carry the `MemOsc` guard (`oscNorm` is junk off `MemOsc`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

/-- Two continuous functions on `ℝ^d` that agree almost everywhere agree everywhere. -/
theorem mn_ae_eq_cont {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[(volume : Measure (Euc d))] g) : f = g :=
  (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hf hg).1 h

theorem mn_pSum_schwartz (f : Euc d → ℝ) (k : ℕ) :
    ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = mo_pSum f k :=
  mova3c_hspan_schwartz (mova3_comb_mem _ _)

theorem mn_diff_schwartz (f : Euc d → ℝ) (k l : ℕ) :
    ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = fun x => mo_pSum f k x - mo_pSum f l x := by
  obtain ⟨φ, hφ⟩ := mn_pSum_schwartz f k
  obtain ⟨ψ, hψ⟩ := mn_pSum_schwartz f l
  refine ⟨φ - ψ, ?_⟩
  funext x
  rw [SchwartzMap.sub_apply, congrFun hφ x, congrFun hψ x]

theorem mn_osc_diff_le (n : ℕ) {f : Euc d → ℝ} (hf : MemOsc (n : ℝ) f) (k l : ℕ) :
    oscNorm n (fun x => mo_pSum f k x - mo_pSum f l x) ≤
      oscNorm n (fun x => f x - mo_pSum f k x) + oscNorm n (fun x => f x - mo_pSum f l x) := by
  have hA := (mova2_sub_pSum (n : ℝ) hf l).1
  have hB := (mova2_sub_pSum (n : ℝ) hf k).1
  have h := (movc1_osc_lin (n : ℝ) 1 (-1) hA hB).2
  have e : (fun x => (1 : ℝ) * (f x - mo_pSum f l x) + (-1) * (f x - mo_pSum f k x)) =
      fun x => mo_pSum f k x - mo_pSum f l x := by funext x; ring
  rw [e] at h
  simp only [abs_one, abs_neg, one_mul] at h
  linarith

theorem mn_eLpNorm_eq {h : Euc d → ℝ} (hh : MemLp h 2 (volume : Measure (Euc d))) :
    eLpNorm h 2 (volume : Measure (Euc d)) = ENNReal.ofReal (oscNorm 0 h) := by
  rw [oscNorm_zero h hh, hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp [Real.rpow_two, sq_abs]


/-- A series of `C^i` functions with summable sup-bounds on the derivatives of order `≤ i`:
the partial sums `a N` converge pointwise to a `C^i` function `g`, and the derivative norms converge too. -/
theorem mn_series_limit (i : ℕ) (a u : ℕ → Euc d → ℝ) (v : ℕ → ℝ)
    (hu0 : u 0 = a 0) (huS : ∀ j, u (j + 1) = fun y => a (j + 1) y - a j y)
    (hcd : ∀ j, ContDiff ℝ (i : WithTop ℕ∞) (u j)) (hv : Summable v)
    (hbd : ∀ k ≤ i, ∀ j x, ‖iteratedFDeriv ℝ k (u j) x‖ ≤ v j) :
    ∃ g : Euc d → ℝ, ContDiff ℝ (i : WithTop ℕ∞) g ∧
      (∀ x, Tendsto (fun N => a N x) atTop (𝓝 (g x))) ∧
      ∀ k ≤ i, ∀ x, Tendsto (fun N => ‖iteratedFDeriv ℝ k (a N) x‖) atTop
        (𝓝 ‖iteratedFDeriv ℝ k g x‖) := by
  have hpart : ∀ N, a N = fun y => ∑ j ∈ Finset.range (N + 1), u j y := by
    intro N
    induction N with
    | zero => funext y; simp [hu0]
    | succ N ih =>
      funext y
      rw [Finset.sum_range_succ, ← congrFun ih y, huS N]
      ring
  have hcdN : ∀ j, ContDiff ℝ (i : WithTop ℕ∞) (u j) := hcd
  have hg : ContDiff ℝ (i : WithTop ℕ∞) fun x => ∑' j, u j x :=
    contDiff_tsum (v := fun _ => v) hcdN (fun _ _ => hv) (fun k j x hk => hbd k (by exact_mod_cast hk) j x)
  refine ⟨fun x => ∑' j, u j x, hg, ?_, ?_⟩
  · intro x
    have hs : Summable fun j => u j x := by
      refine Summable.of_norm_bounded hv fun j => ?_
      simpa [norm_iteratedFDeriv_zero] using hbd 0 (Nat.zero_le _) j x
    have := (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, hpart N]
  · intro k hk x
    have hs : Summable fun j => ‖iteratedFDeriv ℝ k (u j) x‖ := Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun j => hbd k hk j x) hv
    have hderiv := iteratedFDeriv_tsum_apply (𝕜 := ℝ) (N := (i : ℕ∞)) (f := u)
      (v := fun _ => v) (fun j => by exact_mod_cast hcdN j) (fun _ _ => hv) (fun k j x hk => hbd k (by exact_mod_cast hk) j x)
      (k := k) (by exact_mod_cast hk) x
    have hsum : HasSum (fun j => iteratedFDeriv ℝ k (u j) x)
        (iteratedFDeriv ℝ k (fun y => ∑' j, u j y) x) := by
      rw [hderiv]
      exact (hs.of_norm).hasSum
    have h1 := (hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).norm
    refine h1.congr fun N => ?_
    simp only [Function.comp_apply]
    congr 1
    rw [hpart N, iteratedFDeriv_fun_sum_apply]
    intro j _
    exact ((hcdN j).of_le (by exact_mod_cast hk)).contDiffAt

/-- `L²` convergence of `a N` to `f` and pointwise convergence to `g` give `f =ᵐ g`. -/
theorem mn_ae_of_tendsto {f g : Euc d → ℝ} (a : ℕ → Euc d → ℝ)
    (hconv : Tendsto (fun N => eLpNorm (fun x => f x - a N x) 2 (volume : Measure (Euc d))) atTop (𝓝 0))
    (hpt : ∀ x, Tendsto (fun N => a N x) atTop (𝓝 (g x))) :
    f =ᵐ[(volume : Measure (Euc d))] g := by
  have h1 : TendstoInMeasure (volume : Measure (Euc d)) a atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero ?_
    refine hconv.congr fun N => ?_
    rw [← eLpNorm_sub_comm]
    rfl
  obtain ⟨ns, hns, hae⟩ := h1.exists_seq_tendsto_ae
  filter_upwards [hae] with x hx
  exact tendsto_nhds_unique hx ((hpt x).comp hns.tendsto_atTop)


/-- The increments `a 0, a 1 - a 0, a 2 - a 1, ...` of a sequence of functions. -/
def mn_diffSeq (a : ℕ → Euc d → ℝ) : ℕ → Euc d → ℝ
  | 0 => a 0
  | j + 1 => fun y => a (j + 1) y - a j y

/-- **`mn_sobolev_emb_gen`.**  For `i + d/2 < n`, every `f ∈ Σ^n` (not nec. Schwartz) has a `C^i` representative `g`
(`f =ᵐ g`) whose derivatives of order `≤ i` are bounded by `C ‖f‖_{Σ^n}`; `C` is independent of `f`. -/
theorem mn_sobolev_emb_gen (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, MemOsc (n : ℝ) f →
      ∃ g : Euc d → ℝ, ContDiff ℝ (i : WithTop ℕ∞) g ∧ f =ᵐ[(volume : Measure (Euc d))] g ∧
        ∀ k ≤ i, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ C * oscNorm (n : ℝ) f := by
  have hemb : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ (k ≤ i → ∀ (φ : SchwartzMap (Euc d) ℝ) (x : Euc d),
      ‖iteratedFDeriv ℝ k φ x‖ ≤ Ck * oscNorm (n : ℝ) φ) := fun k => by
    by_cases hk : k ≤ i
    · obtain ⟨C, hC0, hC⟩ := mo_sobolev_emb (d := d) k n
        (by have : (k : ℝ) ≤ i := by exact_mod_cast hk
            linarith)
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hk⟩
  choose Ck hCk0 hCk using hemb
  set C : ℝ := ∑ k ∈ Finset.range (i + 1), Ck k with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun k _ => hCk0 k
  have hCle : ∀ k ≤ i, Ck k ≤ C := fun k hk =>
    Finset.single_le_sum (f := Ck) (fun k _ => hCk0 k) (Finset.mem_range.2 (by omega))
  have hschw : ∀ (φ : SchwartzMap (Euc d) ℝ), ∀ k ≤ i, ∀ x,
      ‖iteratedFDeriv ℝ k φ x‖ ≤ C * oscNorm (n : ℝ) φ := fun φ k hk x =>
    (hCk k hk φ x).trans (mul_le_mul_of_nonneg_right (hCle k hk) (Real.sqrt_nonneg _))
  refine ⟨C, hC0, fun f hf => ?_⟩
  have ht : Tendsto (fun N : ℕ => oscNorm (n : ℝ) (fun x => f x - mo_pSum f N x)) atTop (𝓝 0) :=
    mo_hsum_tail _ hf
  have hκ : ∀ j : ℕ, ∃ N : ℕ, oscNorm (n : ℝ) (fun x => f x - mo_pSum f N x) ≤ (1 / 2 : ℝ) ^ j :=
    fun j => (ht.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ j))).exists
  choose κ hκ using hκ
  set a : ℕ → Euc d → ℝ := fun N => mo_pSum f (κ N) with ha
  set w : ℕ → ℝ := fun j => if j = 0 then oscNorm (n : ℝ) f else 2 * (1 / 2 : ℝ) ^ (j - 1) with hw
  have hsch_u : ∀ j, ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = mn_diffSeq a j := by
    intro j
    cases j with
    | zero => exact mn_pSum_schwartz f (κ 0)
    | succ j => exact mn_diff_schwartz f (κ (j + 1)) (κ j)
  have hnorm_u : ∀ j, oscNorm (n : ℝ) (mn_diffSeq a j) ≤ w j := by
    intro j
    cases j with
    | zero =>
      simpa [hw, mn_diffSeq, ha] using (mo_pSum_oscNorm_le (n : ℝ) hf (κ 0)).2
    | succ j =>
      have h1 := mn_osc_diff_le n hf (κ (j + 1)) (κ j)
      have h2 := hκ (j + 1)
      have h3 := hκ j
      have h4 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ j :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ j)
      simp only [hw, mn_diffSeq, ha]
      simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      linarith
  have hcd : ∀ j, ContDiff ℝ (i : WithTop ℕ∞) (mn_diffSeq a j) := fun j => by
    obtain ⟨φ, hφ⟩ := hsch_u j
    rw [← hφ]; exact φ.smooth _
  have hwsum : Summable w := by
    rw [← summable_nat_add_iff 1]
    have : Summable fun j : ℕ => 2 * (1 / 2 : ℝ) ^ j := summable_geometric_two.mul_left 2
    refine this.congr fun j => ?_
    simp [hw]
  have hbd : ∀ k ≤ i, ∀ j x, ‖iteratedFDeriv ℝ k (mn_diffSeq a j) x‖ ≤ C * w j := by
    intro k hk j x
    obtain ⟨φ, hφ⟩ := hsch_u j
    rw [← hφ]
    exact (hschw φ k hk x).trans (mul_le_mul_of_nonneg_left (by rw [hφ]; exact hnorm_u j) hC0)
  obtain ⟨g, hg, hpt, hnormconv⟩ := mn_series_limit i a (mn_diffSeq a) (fun j => C * w j) rfl
    (fun j => rfl) hcd (hwsum.mul_left C) hbd
  refine ⟨g, hg, ?_, ?_⟩
  · refine mn_ae_of_tendsto a ?_ hpt
    have hle : ∀ N, eLpNorm (fun x => f x - a N x) 2 (volume : Measure (Euc d)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
      intro N
      have hmem := (mova2_sub_pSum (n : ℝ) hf (κ N)).1
      have hL : MemLp (fun x => f x - a N x) 2 (volume : Measure (Euc d)) :=
        hf.1.sub (mova2_hsum_memLp _ _)
      rw [mn_eLpNorm_eq hL]
      refine ENNReal.ofReal_le_ofReal ?_
      exact ((mo_mono (r := 0) (r' := (n : ℝ)) (Nat.cast_nonneg n) hmem).2).trans (hκ N)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hle
    simpa using ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  · intro k hk x
    refine le_of_tendsto (hnormconv k hk x) (Eventually.of_forall fun N => ?_)
    obtain ⟨φ, hφ⟩ := mn_pSum_schwartz f (κ N)
    have : a N = ⇑φ := hφ.symm
    rw [this]
    refine (hschw φ k hk x).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [hφ]
    exact (mo_pSum_oscNorm_le (n : ℝ) hf (κ N)).2

end HRS.MS.Mov63
