import HRS.MS.QsfOsc4
import HRS.MS.MovOscAux5
import HRS.Whole.Oscillator

/-!
# S8P: elements of `Σ^m` have `C^J` representatives for `m > J + 2d` (S8.7, packet E4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_osc_smooth`: if `MemOsc m ψ` and `J + 2d < m` (`d ≥ 1`) there is a `C^J`
function `ψ'` with bounded derivatives of order `≤ J` and `ψ' = ψ` a.e.: the Hermite series `∑ c_α h_α` converges in `C_b^J`
(`s45_cb_oscTest`, `summable_oscEigenvalue_rpow_iff`) and in `L²`, and the two limits agree a.e.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovOsc

variable {d : ℕ}

theorem s8p_iter_le_cbNorm {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ} (hj : j ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm k f := by
  have h0 : ‖iteratedFDeriv ℝ j f x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖ :=
    le_ciSup (hf.2 j hj) x
  refine h0.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun i _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem s8p_osc_smooth_conv (hd : 1 ≤ d) (J : ℕ) {m : ℝ} (hm : (J : ℝ) + 2 * d < m)
    {ψ : Euc d → ℝ} (hψ : MemOsc m ψ) :
    ∃ ψ' : Euc d → ℝ, ContDiff ℝ J ψ' ∧ (∀ k ≤ J, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ k ψ' x‖ ≤ B) ∧
      ψ' =ᵐ[volume] ψ ∧ ∀ k ≤ J, ∀ x : Euc d,
        Tendsto (fun n : ℕ => iteratedFDeriv ℝ k (mo_pSum ψ n) x) atTop (𝓝 (iteratedFDeriv ℝ k ψ' x)) := by
  classical
  obtain ⟨K, hK0, hK⟩ := S45.s45_cb_oscTest hd J m
  set c : MultiIndex d → ℝ := fun α => hermiteCoeff ψ α with hc
  set a : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ (m / 2) * c α with ha
  have ha2 : ∀ α, a α ^ 2 = oscEigenvalue d α ^ m * c α ^ 2 := by
    intro α
    rw [ha]; simp only
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (oscEv_pos α).le]
    congr 2; push_cast; ring
  have hasum : Summable fun α => a α ^ 2 := by
    refine hψ.2.congr fun α => ?_
    rw [ha2]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ α, |a α| ≤ B := by
    refine ⟨Real.sqrt (∑' α, a α ^ 2), Real.sqrt_nonneg _, fun α => ?_⟩
    have : a α ^ 2 ≤ ∑' α, a α ^ 2 := hasum.le_tsum α (fun _ _ => sq_nonneg _)
    calc |a α| = Real.sqrt (a α ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt this
  -- the terms
  set φ : MultiIndex d → Euc d → ℝ := fun α => oscTestFun m α with hφ
  have hterm : ∀ α x, a α * φ α x = c α * hermiteFunD α x := by
    intro α x
    simp only [ha, hφ, oscTestFun]
    have h1 : oscEigenvalue d α ^ (m / 2) * oscEigenvalue d α ^ (-(m / 2)) = 1 := by
      rw [← Real.rpow_add (oscEv_pos α)]; simp
    calc oscEigenvalue d α ^ (m / 2) * c α * (oscEigenvalue d α ^ (-(m / 2)) * hermiteFunD α x)
        = (oscEigenvalue d α ^ (m / 2) * oscEigenvalue d α ^ (-(m / 2))) * (c α * hermiteFunD α x) := by
          ring
      _ = _ := by rw [h1, one_mul]
  have hlt : (d : ℝ) < (m - J) / 2 := by linarith
  have hsumv : Summable fun α : MultiIndex d => B * (K * oscEigenvalue d α ^ (-((m - J) / 2))) :=
    ((summable_oscEigenvalue_rpow_iff hd ((m - J) / 2)).2 hlt).mul_left K |>.mul_left B
  have hbound : ∀ (k : ℕ) (α : MultiIndex d) (x : Euc d), k ≤ J →
      ‖iteratedFDeriv ℝ k (fun y => a α * φ α y) x‖ ≤ B * (K * oscEigenvalue d α ^ (-((m - J) / 2))) := by
    intro k α x hk
    have hsm : ContDiff ℝ k (φ α) := ((hK α).1.1).of_le (by exact_mod_cast hk)
    have e1' : iteratedFDeriv ℝ k (fun y => a α • φ α y) x = a α • iteratedFDeriv ℝ k (φ α) x :=
      iteratedFDeriv_const_smul_apply' (f := φ α) (hsm.contDiffAt)
    have e1 : iteratedFDeriv ℝ k (fun y => a α * φ α y) x = a α • iteratedFDeriv ℝ k (φ α) x := by
      simpa only [smul_eq_mul] using e1'
    rw [e1, norm_smul, Real.norm_eq_abs]
    calc |a α| * ‖iteratedFDeriv ℝ k (φ α) x‖ ≤ B * cbNorm J (φ α) :=
          mul_le_mul (hB.2 α) (s8p_iter_le_cbNorm (hK α).1 hk x) (norm_nonneg _) hB.1
      _ ≤ _ := mul_le_mul_of_nonneg_left (hK α).2 hB.1
  have hcd : ∀ α, ContDiff ℝ ((J : ℕ∞) : WithTop ℕ∞) (fun y => a α * φ α y) := fun α => by
    have := ((hK α).1.1).const_smul (a α)
    simpa [smul_eq_mul] using this
  set ψ' : Euc d → ℝ := fun x => ∑' α, a α * φ α x with hψ'
  have hdiff : ContDiff ℝ ((J : ℕ∞) : WithTop ℕ∞) ψ' :=
    contDiff_tsum (v := fun _ α => B * (K * oscEigenvalue d α ^ (-((m - J) / 2)))) hcd
      (fun _ _ => hsumv) (fun k α x hk => hbound k α x (by exact_mod_cast hk))
  refine ⟨ψ', by exact_mod_cast hdiff, fun k hk => ?_, ?_, ?_⟩
  · refine ⟨∑' α, B * (K * oscEigenvalue d α ^ (-((m - J) / 2))), fun x => ?_⟩
    have h1 := iteratedFDeriv_tsum_apply (v := fun _ α => B * (K * oscEigenvalue d α ^ (-((m - J) / 2))))
      hcd (fun _ _ => hsumv) (fun k α x hk => hbound k α x (by exact_mod_cast hk))
      (k := k) (by exact_mod_cast hk) x
    show ‖iteratedFDeriv ℝ k (fun y => ∑' α, a α * φ α y) x‖ ≤ _
    rw [h1]
    have hsn : Summable fun α => ‖iteratedFDeriv ℝ k (fun y => a α * φ α y) x‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => hbound k α x hk) hsumv
    exact (norm_tsum_le_tsum_norm hsn).trans
      (Summable.tsum_le_tsum (fun α => hbound k α x hk) hsn hsumv)
  · -- a.e. equality with ψ
    obtain ⟨e⟩ := S45.s45_exists_enum hd
    obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
    have hL : HasSum (fun α => c α • hermiteLpD α) (hψ.1.toLp ψ) := by
      have := b.hasSum_repr (hψ.1.toLp ψ)
      convert this using 2 with α
      rw [HilbertBasis.repr_apply_apply, hb α, OscSpace.inner_hermiteLpD_toLp]
    have hLn : Tendsto (fun n => ∑ i ∈ Finset.range n, c (e i) • hermiteLpD (e i)) atTop
        (𝓝 (hψ.1.toLp ψ)) := (e.hasSum_iff.2 hL).tendsto_sum_nat
    set P : ℕ → Lp ℝ 2 (volume : Measure (Euc d)) :=
      fun n => ∑ i ∈ Finset.range n, c (e i) • hermiteLpD (e i) with hP
    set Sn : ℕ → Euc d → ℝ := fun n x => ∑ i ∈ Finset.range n, c (e i) * hermiteFunD (e i) x with hSn
    have hh : ∀ α, (hermiteLpD α : Euc d → ℝ) =ᵐ[volume] hermiteFunD α := by
      intro α
      have h1 : hermiteLpD α = (memLp_hermiteFunD α).toLp (hermiteFunD α) := by
        unfold hermiteLpD; exact dif_pos _
      rw [h1]; exact (memLp_hermiteFunD α).coeFn_toLp
    have hPae : ∀ n, (P n : Euc d → ℝ) =ᵐ[volume] Sn n := by
      intro n
      induction n with
      | zero => simp only [hP, hSn, Finset.range_zero, Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
      | succ n ih =>
        have e1 : P (n + 1) = P n + c (e n) • hermiteLpD (e n) := by
          simp only [hP]; rw [Finset.sum_range_succ]
        rw [e1]
        filter_upwards [Lp.coeFn_add (P n) (c (e n) • hermiteLpD (e n)),
          Lp.coeFn_smul (c (e n)) (hermiteLpD (e n)), hh (e n), ih] with x h1 h2 h3 h4
        simp only [hSn, Finset.sum_range_succ] at h4 ⊢
        rw [h1]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h2 ⊢
        rw [h2, h3, h4]
    have hall : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ n, (P n : Euc d → ℝ) x = Sn n x :=
      ae_all_iff.2 hPae
    have hmeas : TendstoInMeasure volume (fun n => (P n : Euc d → ℝ)) atTop ψ := by
      refine tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞)) (by norm_num) ?_
      exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm P ψ hψ.1).1 hLn
    obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hall, hae] with x hx1 hx2
    -- pointwise convergence of `Sn n x` to `ψ' x`
    have hpt : Summable fun α => a α * φ α x :=
      Summable.of_norm_bounded (g := fun α => B * (K * oscEigenvalue d α ^ (-((m - J) / 2)))) hsumv
        (fun α => by simpa using hbound 0 α x (Nat.zero_le _))
    have hfun : (fun α => a α * φ α x) = fun α => c α * hermiteFunD α x :=
      funext fun α => hterm α x
    have hpt' : HasSum (fun α => c α * hermiteFunD α x) (ψ' x) := by
      rw [← hfun]; exact hpt.hasSum
    have hsum : HasSum (fun i => c (e i) * hermiteFunD (e i) x) (ψ' x) :=
      (e.hasSum_iff (f := fun α => c α * hermiteFunD α x)).2 hpt'
    have hlim1 : Tendsto (fun n => Sn n x) atTop (𝓝 (ψ' x)) := hsum.tendsto_sum_nat
    have hlim2 : Tendsto (fun i => Sn (ns i) x) atTop (𝓝 (ψ x)) := by
      simpa [hx1] using hx2
    exact tendsto_nhds_unique (hlim1.comp hns.tendsto_atTop) hlim2
  · intro k hk x
    have h1 := iteratedFDeriv_tsum_apply (v := fun _ α => B * (K * oscEigenvalue d α ^ (-((m - J) / 2))))
      hcd (fun _ _ => hsumv) (fun k α x hk => hbound k α x (by exact_mod_cast hk))
      (k := k) (by exact_mod_cast hk) x
    have hsn : Summable fun α => ‖iteratedFDeriv ℝ k (fun y => a α * φ α y) x‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => hbound k α x hk) hsumv
    have hsm : Summable fun α => iteratedFDeriv ℝ k (fun y => a α * φ α y) x := hsn.of_norm
    have hT : Tendsto (fun n : ℕ => ∑ α ∈ mova2_S d n, iteratedFDeriv ℝ k (fun y => a α * φ α y) x)
        atTop (𝓝 (∑' α, iteratedFDeriv ℝ k (fun y => a α * φ α y) x)) :=
      hsm.hasSum.comp (tendsto_atTop_finset_of_monotone mova2_S_mono mova2_S_exh)
    have hψ'k : iteratedFDeriv ℝ k ψ' x = ∑' α, iteratedFDeriv ℝ k (fun y => a α * φ α y) x := by
      show iteratedFDeriv ℝ k (fun y => ∑' α, a α * φ α y) x = _
      exact h1
    rw [hψ'k]
    refine hT.congr fun n => ?_
    have hps : mo_pSum ψ n = fun y => ∑ α ∈ mova2_S d n, a α * φ α y := by
      funext y
      unfold mo_pSum mo_hsum
      exact Finset.sum_congr rfl fun α _ => (hterm α y).symm
    rw [hps]
    have hcdk : ∀ α ∈ mova2_S d n, ContDiffAt ℝ k (fun y => a α * φ α y) x := fun α _ =>
      ((hcd α).of_le (by exact_mod_cast hk)).contDiffAt
    exact (iteratedFDeriv_fun_sum_apply hcdk).symm

theorem s8p_osc_smooth (hd : 1 ≤ d) (J : ℕ) {m : ℝ} (hm : (J : ℝ) + 2 * d < m)
    {ψ : Euc d → ℝ} (hψ : MemOsc m ψ) :
    ∃ ψ' : Euc d → ℝ, ContDiff ℝ J ψ' ∧ (∀ k ≤ J, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ k ψ' x‖ ≤ B) ∧
      ψ' =ᵐ[volume] ψ := by
  obtain ⟨ψ', h1, h2, h3, -⟩ := s8p_osc_smooth_conv hd J hm hψ
  exact ⟨ψ', h1, h2, h3⟩

end HRS.MS.Spec
