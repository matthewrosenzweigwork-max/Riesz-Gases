import HRS.MS.WadAux107

/-!
# S8.3, packet S8F-8: weighted derivative bounds of the classical solution from the iterated-difference bounds

`s8f_cl_deriv`: for `φ ∈ C_c^∞` with `‖D^iφ(y)‖ ≤ Nφ ⟨y⟩^M` (`i ≤ N`) and the classical solution `f` of terminal datum `φ` on `[0,t]`, `0 < t ≤ T`:
every partial derivative of `f_0` of order `k ≤ N` is bounded by `K Nφ ⟨x⟩^M`, and every one of order `k + 1 ≤ N + 1` by `K Nφ e^{lam T} t^{-3/4} ⟨x⟩^M`
(difference quotients in coordinate directions, `s8f_partial_le_of_dp`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S85 HRS.MS.S52B

variable {d : ℕ}

theorem s8f_dp_clm_apply (η : List (Euc d)) (G : Euc d → (Euc d →L[ℝ] ℝ)) (e : Euc d) (y : Euc d) :
    s8f_dp η (fun y => G y e) y = (s8f_dp η G y) e := by
  induction η generalizing y with
  | nil => rfl
  | cons e' η ih =>
    show s8f_dp η (fun y => G y e) (y + e') - s8f_dp η (fun y => G y e) y =
      (s8f_dp η G (y + e') - s8f_dp η G y) e
    rw [ih, ih, ContinuousLinearMap.sub_apply]

theorem s8f_partial_succ {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ (k + 1) f) (idx : Fin (k + 1) → Fin d)
    (x : Euc d) :
    partialDeriv idx f x = partialDeriv (fun l : Fin k => idx l.castSucc)
      (fun y => fderiv ℝ f y (EuclideanSpace.single (idx (Fin.last k)) (1 : ℝ))) x := by
  have hDf : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  have e1 : (fun y => fderiv ℝ f y (EuclideanSpace.single (idx (Fin.last k)) (1 : ℝ))) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (idx (Fin.last k)) (1 : ℝ) : Euc d)) ∘
        fderiv ℝ f := rfl
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_right, e1,
    ContinuousLinearMap.iteratedFDeriv_comp_left _ hDf.contDiffAt le_rfl]
  rfl

theorem s8f_small_ofFn {N k : ℕ} (hk : k ≤ N) (m : Fin k → Euc d) {h : ℝ} (hh : ∀ l, ‖m l‖ = h)
    (hhs : (N : ℝ) * h ≤ 1 / 8) (hh0 : 0 ≤ h) :
    s8f_small N (List.ofFn m).reverse ∧
      (((List.ofFn m).reverse).map (fun e => ‖e‖)).prod = h ^ k := by
  have hmap : ((List.ofFn m).reverse).map (fun e => ‖e‖) = List.replicate k h := by
    rw [List.map_reverse, List.map_ofFn]
    have : (fun e : Euc d => ‖e‖) ∘ m = fun _ : Fin k => h := funext hh
    rw [this]
    simp [List.ofFn_const]
  refine ⟨⟨by simpa using hk, ?_⟩, ?_⟩
  · rw [hmap, List.sum_replicate, nsmul_eq_mul]
    have : (k : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith
  · rw [hmap, List.prod_replicate]

theorem s8f_Dif_zero (a : ℝ) (ξs : List (Euc d)) (f : ℝ → Euc d → ℝ) :
    s8f_Dif a ξs f 0 = s8f_dp ξs (f 0) := by
  rw [s8f_Dif_eq_dp]
  have : ξs.map (fun ξ => s8e_zs a ξ 0) = ξs := by
    conv_rhs => rw [← List.map_id ξs]
    exact List.map_congr_left fun ξ _ => by simp [s8e_zs]
  rw [this]

theorem s8f_cl_deriv (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (N : ℕ) :
    ∃ lam K : ℝ, 0 ≤ lam ∧ 0 ≤ K ∧ ∀ {t Nφ : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      S85Cc φ → IsClassicalAdjointW (critCoeff d a β ρβ) t φ f → 0 ≤ Nφ →
      (∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Nφ * jbracket y ^ M) →
      (∀ k ≤ N, ∀ idx : Fin k → Fin d, ∀ x, |partialDeriv idx (f 0) x| ≤ K * Nφ * jbracket x ^ M) ∧
      (∀ k ≤ N, ∀ idx : Fin (k + 1) → Fin d, ∀ x, |partialDeriv idx (f 0) x| ≤
        K * Nφ * (Real.exp (lam * T) * t ^ (-(3 / 4 : ℝ))) * jbracket x ^ M) := by
  obtain ⟨lam, Kc, hlam, hKc, hcl⟩ := s8f_jets hd ha hβ hT hM hρ N
  have h3 : 0 ≤ (3 : ℝ) ^ M := Real.rpow_nonneg (by norm_num) _
  refine ⟨lam, Kc * (3 ^ M) ^ N, hlam, by positivity, ?_⟩
  intro t Nφ φ f ht htT hφ hf hNφ hb
  have hφN : ContDiff ℝ N φ := contDiff_infty.1 hφ.1 N
  have hdat := s8f_hdat hM ha.le ht.le N hf.terminal hφN hb
  set Φ : ℝ := Nφ * (3 ^ M) ^ N with hΦdef
  have hΦ : 0 ≤ Φ := by positivity
  have hcl' := hcl ht htT hf hΦ hdat
  have hsm : ∀ j : ℕ, ContDiff ℝ j (f 0) := fun j =>
    s8f_cl_smooth_cc hd ha hβ hρ hT.le hφ ⟨ht.le, htT⟩ j hf
  have hf0 : Differentiable ℝ (f 0) := (hsm 1).differentiable (by norm_num)
  set h0 : ℝ := 1 / (8 * ((N : ℝ) + 1)) with hh0def
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hh0 : 0 < h0 := by positivity
  have hhs : ∀ h : ℝ, h ≤ h0 → (N : ℝ) * h ≤ 1 / 8 := by
    intro h hh
    have : ((N : ℝ) + 1) * h0 = 1 / 8 := by rw [hh0def]; field_simp
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hnorm : ∀ {k : ℕ} (idx : Fin k → Fin d) {h : ℝ}, 0 < h →
      ∀ l, ‖(fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)) l‖ = h := by
    intro k idx h hh l
    simp [norm_smul, abs_of_pos hh]
  refine ⟨fun k hk idx x => ?_, fun k hk idx x => ?_⟩
  · refine s8f_partial_le_of_dp (hsm k) idx x (B := Kc * (3 ^ M) ^ N * Nφ * jbracket x ^ M) hh0 ?_
    intro h hh hhle
    obtain ⟨hsmall, hprod⟩ := s8f_small_ofFn hk _ (hnorm idx hh) (hhs h hhle) hh.le
    obtain ⟨-, hsup⟩ := hcl' _ hsmall (by rw [List.length_reverse, List.length_ofFn]; omega)
    have := hsup 0 ⟨le_rfl, ht.le⟩ x
    rw [s8f_Dif_zero, s8f_dp_ofFn, hprod] at this
    refine this.trans (le_of_eq ?_)
    rw [hΦdef]; ring
  · set e : Euc d := EuclideanSpace.single (idx (Fin.last k)) (1 : ℝ) with hedef
    set idx0 : Fin k → Fin d := fun l => idx l.castSucc with hidx0
    set g : Euc d → ℝ := fun y => fderiv ℝ (f 0) y e with hgdef
    have hg : ContDiff ℝ k g :=
      ((hsm (k + 1)).fderiv_right (by norm_cast)).clm_apply contDiff_const
    rw [s8f_partial_succ (hsm (k + 1)) idx x]
    refine s8f_partial_le_of_dp hg idx0 x
      (B := Kc * (3 ^ M) ^ N * Nφ * (Real.exp (lam * T) * t ^ (-(3 / 4 : ℝ))) * jbracket x ^ M) hh0 ?_
    intro h hh hhle
    obtain ⟨hsmall, hprod⟩ := s8f_small_ofFn hk
      (fun l => h • (EuclideanSpace.single (idx0 l) (1 : ℝ) : Euc d)) (hnorm idx0 hh) (hhs h hhle) hh.le
    obtain ⟨hadm, -⟩ := hcl' _ hsmall (by rw [List.length_reverse, List.length_ofFn]; omega)
    have hx := (hadm 0 ⟨le_rfl, ht⟩).1 x
    rw [s8f_Dif_zero, s8f_dp_fderiv _ hf0, hprod] at hx
    rw [← s8f_dp_ofFn]
    have e1 : s8f_dp (List.ofFn fun l : Fin k => h • (EuclideanSpace.single (idx0 l) (1 : ℝ) : Euc d)).reverse g x =
        (s8f_dp (List.ofFn fun l : Fin k => h • (EuclideanSpace.single (idx0 l) (1 : ℝ) : Euc d)).reverse
          (fderiv ℝ (f 0)) x) e := s8f_dp_clm_apply _ (fderiv ℝ (f 0)) e x
    rw [e1]
    have hen : ‖e‖ = 1 := by simp [hedef]
    have hw0 : s84_wt lam t 0 ≤ Real.exp (lam * T) * t ^ (-(3 / 4 : ℝ)) := by
      unfold s84_wt
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT hlam))
        (Real.rpow_nonneg ht.le _)
    have hj : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
    have hΘ : 0 ≤ Kc * Φ * h ^ k := by positivity
    calc |(s8f_dp (List.ofFn fun l : Fin k => h • (EuclideanSpace.single (idx0 l) (1 : ℝ) : Euc d)).reverse
          (fderiv ℝ (f 0)) x) e|
        ≤ ‖(s8f_dp (List.ofFn fun l : Fin k => h • (EuclideanSpace.single (idx0 l) (1 : ℝ) : Euc d)).reverse
          (fderiv ℝ (f 0)) x)‖ * ‖e‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Kc * Φ * h ^ k * s84_wt lam t 0 * jbracket x ^ M) * 1 := by
          rw [hen]
          exact mul_le_mul_of_nonneg_right hx zero_le_one
      _ ≤ (Kc * Φ * h ^ k * (Real.exp (lam * T) * t ^ (-(3 / 4 : ℝ))) * jbracket x ^ M) * 1 := by
          gcongr
      _ = _ := by rw [hΦdef]; ring

end HRS.MS.Wad
