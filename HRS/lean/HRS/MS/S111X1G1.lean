import HRS.MS.S111X1F3
import HRS.MS.MovOscAux4
import HRS.MS.OrbFeatAux1
import HRS.MS.TransOpAux8

/-!
# S11.1 X1: bounded derivatives of oscillator test functions (Hermite series)

A smooth `ψ ∈ Σ^m` is the absolutely convergent Hermite series `∑ c_α h_α` in `C_b^K`, `m > K + 2d + 2`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- derivative bounds of the Hermite functions: `‖D^j h_α‖_∞ ≤ C λ_α^{n/2}` -/
theorem hermite_deriv_bound (j n : ℕ) (hn : (j : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : MultiIndex d) (x : Euc d),
      ‖iteratedFDeriv ℝ j (hermiteFunD α) x‖ ≤ C * oscEigenvalue d α ^ ((n : ℝ) / 2) := by
  obtain ⟨C, hC, h⟩ := HRS.MS.MovOsc.mo_sobolev_emb (d := d) j n hn
  refine ⟨C, hC, fun α x => ?_⟩
  obtain ⟨f, hf, hN⟩ := HRS.MS.S52B.s52b_phi (d := d) 0 α
  have e : (⇑f : Euc d → ℝ) = hermiteFunD α := by
    rw [hf]; funext y; simp [oscTestFun]
  have h1 := h f x
  have h2 := hN n
  rw [e] at h1 h2
  rw [h2] at h1
  simpa using h1

theorem hermite_series_summable {m : ℝ} {n : ℕ} (hmn : (d : ℝ) < m - n) {ψ : Euc d → ℝ} (hψ : MemOsc m ψ) :
    Summable fun α : MultiIndex d => |hermiteCoeff ψ α| * oscEigenvalue d α ^ ((n : ℝ) / 2) := by
  have hS := OscDual.summable_oscEv_neg_rpow (d := d) hmn
  have hT := hψ.2
  refine Summable.of_nonneg_of_le (fun α => mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (oscEv_pos α).le _)) (fun α => ?_) ((hT.add hS).div_const 2)
  have hl := oscEv_pos (d := d) α
  set l := oscEigenvalue d α with hlset
  set c := hermiteCoeff ψ α with hc
  have e1 : l ^ ((n : ℝ) / 2) = l ^ (m / 2) * l ^ (((n : ℝ) - m) / 2) := by
    rw [← Real.rpow_add hl]; congr 1; ring
  have e2 : l ^ m = (l ^ (m / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]; congr 1; ring
  have e3 : l ^ (-(m - (n : ℝ))) = (l ^ (((n : ℝ) - m) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]; congr 1; push_cast; ring
  rw [e1, show |c| * (l ^ (m / 2) * l ^ (((n : ℝ) - m) / 2)) =
    (|c| * l ^ (m / 2)) * l ^ (((n : ℝ) - m) / 2) by ring]
  have : l ^ m * c ^ 2 = (|c| * l ^ (m / 2)) ^ 2 := by rw [e2, mul_pow, sq_abs]; ring
  show _ ≤ (l ^ m * c ^ 2 + l ^ (-(m - (n : ℝ)))) / 2
  rw [this, e3]
  nlinarith [sq_nonneg (|c| * l ^ (m / 2) - l ^ (((n : ℝ) - m) / 2))]

/-- partial sums of the Hermite series -/
def hpart (ψ : Euc d → ℝ) (S : Finset (MultiIndex d)) (x : Euc d) : ℝ :=
  ∑ α ∈ S, hermiteCoeff ψ α * hermiteFunD α x

theorem hpart_memLp (ψ : Euc d → ℝ) (S : Finset (MultiIndex d)) :
    ∃ h : MemLp (hpart ψ S) 2 (volume : Measure (Euc d)),
      h.toLp (hpart ψ S) = ∑ α ∈ S, hermiteCoeff ψ α • (hermiteLpD α) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e0 : hpart ψ ∅ = 0 := by funext x; simp [hpart]
    rw [e0]
    exact ⟨MemLp.zero, by simp⟩
  | insert a S ha ih =>
    obtain ⟨h, hh⟩ := ih
    have hla : hermiteLpD a = (memLp_hermiteFunD a).toLp (hermiteFunD a) := by
      unfold hermiteLpD; exact dif_pos _
    have hm : MemLp (fun x => hermiteCoeff ψ a * hermiteFunD a x) 2 volume :=
      (memLp_hermiteFunD a).const_mul _
    have e : hpart ψ (insert a S) = fun x => hermiteCoeff ψ a * hermiteFunD a x + hpart ψ S x := by
      funext x; simp [hpart, Finset.sum_insert ha]
    have hmem : MemLp (hpart ψ (insert a S)) 2 volume := by rw [e]; exact hm.add h
    refine ⟨hmem, ?_⟩
    rw [Finset.sum_insert ha, ← hh, hla]
    have h1 := MemLp.toLp_add hm h
    have h2 := MemLp.toLp_const_smul (μ := (volume : Measure (Euc d))) (p := 2) (hermiteCoeff ψ a)
      (memLp_hermiteFunD a)
    rw [← h2]
    refine Eq.trans (MemLp.toLp_congr hmem (hm.add h) (Filter.Eventually.of_forall fun x => by rw [e]; rfl)) ?_
    exact h1

theorem hermite_series_eq {m : ℝ} {n : ℕ} (hn : (d : ℝ) / 2 < n) (hmn : (d : ℝ) < m - n)
    {ψ : Euc d → ℝ} (hψc : Continuous ψ) (hψ : MemOsc m ψ) :
    ∀ x, ψ x = ∑' α, hermiteCoeff ψ α * hermiteFunD α x := by
  classical
  obtain ⟨C, hC, hb⟩ := hermite_deriv_bound (d := d) 0 n (by simpa using hn)
  have hsum := (hermite_series_summable hmn hψ).mul_left C
  have hbd : ∀ α x, ‖hermiteCoeff ψ α * hermiteFunD α x‖ ≤
      C * (|hermiteCoeff ψ α| * oscEigenvalue d α ^ ((n : ℝ) / 2)) := by
    intro α x
    have := hb α x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, abs_mul]
    calc |hermiteCoeff ψ α| * |hermiteFunD α x| ≤ |hermiteCoeff ψ α| * (C * oscEigenvalue d α ^ ((n : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have hsumx : ∀ x, Summable fun α => hermiteCoeff ψ α * hermiteFunD α x := fun x =>
    Summable.of_norm_bounded hsum (fun α => hbd α x)
  set F : Euc d → ℝ := fun x => ∑' α, hermiteCoeff ψ α * hermiteFunD α x with hF
  have hFc : Continuous F := continuous_tsum (fun α => continuous_const.mul
    (contDiff_hermiteFunD α).continuous) hsum (fun α x => hbd α x)
  -- the Hilbert space expansion
  have hL := (HRS.MS.TransOp.s611_basis d).hasSum_repr (hψ.1.toLp ψ)
  have hrepr : ∀ α, ((HRS.MS.TransOp.s611_basis d).repr (hψ.1.toLp ψ)) α = hermiteCoeff ψ α := by
    intro α
    rw [HilbertBasis.repr_apply_apply, HRS.MS.TransOp.s611_basis_apply,
      OscSpace.inner_hermiteLpD_toLp ψ hψ.1 α]
  have hL' : HasSum (fun α => hermiteCoeff ψ α • hermiteLpD α) (hψ.1.toLp ψ) := by
    convert hL using 2 with α
    rw [hrepr α, HRS.MS.TransOp.s611_basis_apply]
  have hT : Tendsto (fun S : Finset (MultiIndex d) => ∑ α ∈ S, hermiteCoeff ψ α • hermiteLpD α) atTop
      (𝓝 (hψ.1.toLp ψ)) := hL'
  have hpm := fun S => hpart_memLp ψ S
  have hT' : Tendsto (fun S : Finset (MultiIndex d) => (hpm S).choose.toLp (hpart ψ S)) atTop
      (𝓝 (hψ.1.toLp ψ)) := by
    refine hT.congr fun S => ?_
    exact (hpm S).choose_spec.symm
  have hE := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (p := 2) (fi := atTop) (fun S => hpart ψ S)
    (fun S => (hpm S).choose) ψ hψ.1).1 hT'
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (μ := (volume : Measure (Euc d))) (p := 2)
    (by norm_num) hE
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae'
  have hpt : ∀ x, Tendsto (fun i => hpart ψ (ns i) x) atTop (𝓝 (F x)) := by
    intro x
    exact (hsumx x).hasSum.comp hns
  have hEq : ∀ᵐ x ∂(volume : Measure (Euc d)), ψ x = F x := by
    filter_upwards [hae] with x hx
    exact tendsto_nhds_unique hx (hpt x) |>.symm ▸ rfl
  have := (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hψc hFc).1 hEq
  intro x
  exact congrFun this x

theorem hermite_deriv_bound_le (K n : ℕ) (hn : (K : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ K, ∀ (α : MultiIndex d) (x : Euc d),
      ‖iteratedFDeriv ℝ j (hermiteFunD α) x‖ ≤ C * oscEigenvalue d α ^ ((n : ℝ) / 2) := by
  have h : ∀ j : Fin (K + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : MultiIndex d) (x : Euc d),
      ‖iteratedFDeriv ℝ (j : ℕ) (hermiteFunD α) x‖ ≤ C * oscEigenvalue d α ^ ((n : ℝ) / 2) := fun j =>
    hermite_deriv_bound (j : ℕ) n (by
      have : ((j : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 j.2
      linarith)
  choose C hC0 hC using h
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC0 j, fun j hj α x => ?_⟩
  have hl := Real.rpow_nonneg (oscEv_pos (d := d) α).le ((n : ℝ) / 2)
  refine (hC ⟨j, Nat.lt_succ_of_le hj⟩ α x).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_univ _)

theorem osc_deriv_bdd {m : ℝ} {n K : ℕ} (hn : (K : ℝ) + d / 2 < n) (hmn : (d : ℝ) < m - n)
    {ψ : Euc d → ℝ} (hψc : ContDiff ℝ ∞ ψ) (hψ : MemOsc m ψ) :
    ∃ A : ℝ, ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ A := by
  classical
  have hn0 : (d : ℝ) / 2 < n := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hser := hermite_series_eq hn0 hmn hψc.continuous hψ
  set F : Euc d → ℝ := fun x => ∑' α, hermiteCoeff ψ α * hermiteFunD α x with hF
  have hfun : ψ = F := funext hser
  obtain ⟨C, hC0, hC⟩ := hermite_deriv_bound_le K n hn
  have hsum := (hermite_series_summable hmn hψ).mul_left C
  have hcd : ∀ α, ContDiff ℝ (K : WithTop ℕ∞) (fun y => hermiteCoeff ψ α * hermiteFunD α y) := fun α =>
    contDiff_const.mul ((contDiff_hermiteFunD α).of_le (by exact_mod_cast le_top))
  have hbd : ∀ (k : ℕ) (α : MultiIndex d) (x : Euc d), (k : ℕ∞) ≤ K →
      ‖iteratedFDeriv ℝ k (fun y => hermiteCoeff ψ α * hermiteFunD α y) x‖ ≤
        C * (|hermiteCoeff ψ α| * oscEigenvalue d α ^ ((n : ℝ) / 2)) := by
    intro k α x hk
    have hkK : k ≤ K := by exact_mod_cast hk
    have e : iteratedFDeriv ℝ k (fun y => hermiteCoeff ψ α * hermiteFunD α y) x =
        hermiteCoeff ψ α • iteratedFDeriv ℝ k (hermiteFunD α) x :=
      iteratedFDeriv_const_smul_apply (a := hermiteCoeff ψ α) (i := k) (f := hermiteFunD α)
        (((contDiff_hermiteFunD α).of_le (by exact_mod_cast le_top)).contDiffAt)
    rw [e, norm_smul, Real.norm_eq_abs]
    calc |hermiteCoeff ψ α| * ‖iteratedFDeriv ℝ k (hermiteFunD α) x‖
        ≤ |hermiteCoeff ψ α| * (C * oscEigenvalue d α ^ ((n : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hC k hkK α x) (abs_nonneg _)
      _ = _ := by ring
  refine ⟨∑' α, C * (|hermiteCoeff ψ α| * oscEigenvalue d α ^ ((n : ℝ) / 2)), fun j hj x => ?_⟩
  have hit := iteratedFDeriv_tsum (𝕜 := ℝ) (N := (K : ℕ∞)) (f := fun α y => hermiteCoeff ψ α * hermiteFunD α y)
    (v := fun _ α => C * (|hermiteCoeff ψ α| * oscEigenvalue d α ^ ((n : ℝ) / 2))) hcd
    (fun k _ => hsum) hbd (k := j) (by exact_mod_cast hj)
  have hit' : iteratedFDeriv ℝ j F x =
      ∑' α, iteratedFDeriv ℝ j (fun y => hermiteCoeff ψ α * hermiteFunD α y) x := by
    rw [hF]; exact congrFun hit x
  have hj' : iteratedFDeriv ℝ j ψ x = iteratedFDeriv ℝ j F x := by rw [hfun]
  rw [hj', hit']
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => hbd j α x (by exact_mod_cast hj)) hsum
  · exact Summable.tsum_le_tsum (fun α => hbd j α x (by exact_mod_cast hj))
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => hbd j α x (by exact_mod_cast hj)) hsum) hsum

end HRS.MS.S111X1
