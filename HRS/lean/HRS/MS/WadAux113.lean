import HRS.MS.WadAux112

/-!
# S8.3, packet S8F-13: extension of the jet bounds from `C_c^∞` to `C_M^k` data

`s8f_Ulim_cc_decay`: for `ψ ∈ C_c^∞`, `D^i U_t ψ / ⟨·⟩^M → 0` at infinity (bound at the weight `M/2`).
`s8f_extend`: if the output bound `‖D^i U_t ψ‖ ≤ K' ν ⟨y⟩^M` (`i ≤ n`) holds for `ψ ∈ C_c^∞` with `‖D^jψ‖ ≤ ν⟨y⟩^M` (`j ≤ k`), then for
`f ∈ C_M^k` with `‖D^j f‖ ≤ ν⟨y⟩^M` one has `U_t f ∈ C_M^n` and `‖D^i U_t f‖ ≤ K' ν ⟨y⟩^M` (`i ≤ n`).
Proof: `C_c^∞` approximants in the jet norm (`s8f_jet_approx`); the images are Cauchy in the output jet norm (linearity of `U_t`);
`s8f_closure`; decay of the limit by `s8d_decay_of_approx`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_cc_jet_bound {ψ : Euc d → ℝ} (hψ : S85Cc ψ) (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ ν : ℝ, 0 ≤ ν ∧ ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ ν * jbracket y ^ M := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i ψ x‖ ≤ C := fun i =>
    (hψ.1.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hψ.2.iteratedFDeriv i)
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (N + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i hi y => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i ψ y‖ ≤ ∑ j ∈ Finset.range (N + 1), |C j| :=
    (hC i y).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|)
      (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
  have hJ : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have h0 : 0 ≤ ∑ j ∈ Finset.range (N + 1), |C j| := Finset.sum_nonneg fun i _ => abs_nonneg _
  nlinarith

theorem s8f_Ulim_cc_decay {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) (N : ℕ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) {ψ : Euc d → ℝ} (hψ : S85Cc ψ) :
    ∀ i ≤ N, Tendsto (fun x => ‖iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t ψ) x‖ / jbracket x ^ M)
      (cocompact (Euc d)) (𝓝 0) := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  have H' : S85Hyp d a β T (M / 2) ρβ := ⟨hd, ha, hβ, hT, by positivity, hρ⟩
  obtain ⟨K, hK0, hK⟩ := s8f_Ulim_cc_bounds H' N
  obtain ⟨ν, hν0, hν⟩ := s8f_cc_jet_bound hψ N (M := M / 2) (by positivity)
  have hU := (hK ht htT hψ hν0 hν).2.1
  have heq : s85_Ulim a β ρβ M t ψ = s85_Ulim a β ρβ (M / 2) t ψ := funext fun x => by
    rw [s85_Ulim_cc H ht.le htT hψ x, s85_Ulim_cc H' ht.le htT hψ x]
  intro i hi
  rw [heq]
  have hlim : Tendsto (fun x : Euc d => K * ν * jbracket x ^ (-(M / 2))) (cocompact (Euc d)) (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < M / 2 by positivity)).comp (s83_jb_tendsto_atTop (d := d))
    simpa using this.const_mul (K * ν)
  refine squeeze_zero (fun x => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (s83_jb_pos x).le _))
    (fun x => ?_) hlim
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  rw [div_le_iff₀ hp]
  refine (hU i hi x).trans (le_of_eq ?_)
  have : jbracket x ^ (-(M / 2)) * jbracket x ^ M = jbracket x ^ (M / 2) := by
    rw [← Real.rpow_add (s83_jb_pos x)]; congr 1; ring
  rw [mul_assoc (K * ν) _ _, this]

theorem s8f_extend {a β T M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β T M ρβ) (hMpos : 0 < M) {t : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (k n : ℕ) {K' : ℝ} (hK' : 0 ≤ K')
    (hbound : ∀ {ν : ℝ} {ψ : Euc d → ℝ}, S85Cc ψ → 0 ≤ ν →
      (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ ν * jbracket y ^ M) →
      ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t ψ) y‖ ≤ K' * ν * jbracket y ^ M)
    (hsmooth : ∀ {ψ : Euc d → ℝ}, S85Cc ψ → ∀ j : ℕ, ContDiff ℝ j (s85_Ulim a β ρβ M t ψ))
    {f : Euc d → ℝ} (hfM : MemCM M f) (hfk : ContDiff ℝ k f)
    (hdec : ∀ i ≤ k, Tendsto (fun x => ‖iteratedFDeriv ℝ i f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0))
    {ν : ℝ} (hν : 0 ≤ ν) (hfν : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ ν * jbracket y ^ M) :
    MemCMj M n (s85_Ulim a β ρβ M t f) ∧
      ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t f) y‖ ≤ K' * ν * jbracket y ^ M := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨Kb, hKb0, hKb⟩ := s85_Ulim_bound H
  set e : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with he
  have he0 : ∀ m, 0 ≤ e m := fun m => by positivity
  have hea : Antitone e := fun m l hml => by
    simp only [he]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hml 1)
  have het : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex : ∀ m : ℕ, ∃ φ : Euc d → ℝ, S85Cc φ ∧ ∀ i ≤ k, ∀ y,
      ‖iteratedFDeriv ℝ i (fun x => φ x - f x) y‖ ≤ e m * jbracket y ^ M :=
    fun m => s8f_jet_approx hM hfk hdec (by positivity : 0 < e m)
  choose φ hφc hφe using hex
  set u : ℕ → Euc d → ℝ := fun m => s85_Ulim a β ρβ M t (φ m) with hu
  set U : Euc d → ℝ := s85_Ulim a β ρβ M t f with hU
  have hφi : ∀ m, ContDiff ℝ k (φ m) := fun m => (hφc m).1.of_le (by exact_mod_cast le_top)
  -- jet bounds of the approximants
  have hφν : ∀ m, ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i (φ m) y‖ ≤ (ν + e m) * jbracket y ^ M := by
    intro m i hi y
    have e1 : iteratedFDeriv ℝ i (φ m) y = iteratedFDeriv ℝ i (fun x => φ m x - f x) y + iteratedFDeriv ℝ i f y := by
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := y) (i := i) (f := φ m) (g := f)
        (hφi m |>.of_le (by exact_mod_cast hi)).contDiffAt (hfk.of_le (by exact_mod_cast hi)).contDiffAt
      simp only [Pi.sub_def] at this ⊢
      rw [this]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have := hφe m i hi y
    have := hfν i hi y
    nlinarith
  -- pointwise convergence
  have hpt : ∀ x, Tendsto (fun m => u m x) atTop (𝓝 (U x)) := by
    intro x
    have hb : ∀ m, ‖u m x - U x‖ ≤ Kb * e m * jbracket x ^ M := by
      intro m
      have hw : Wt M (e m) (fun y => φ m y - f y) := fun y => by
        have := hφe m 0 (Nat.zero_le _) y
        rwa [norm_iteratedFDeriv_zero] at this
      have := hKb ht.le htT (s85_Cc_memCM M (hφc m)) hfM hw x
      rwa [Real.norm_eq_abs]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) hb ?_
    simpa using (het.const_mul Kb).mul_const (jbracket x ^ M)
  -- the images are Cauchy in the jet norm
  have hdiff : ∀ m l, ∃ ψ : Euc d → ℝ, S85Cc ψ ∧ (∀ x, u m x - u l x = s85_Ulim a β ρβ M t ψ x) ∧
      (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ (e m + e l) * jbracket y ^ M) := by
    intro m l
    refine ⟨fun y => (-1 : ℝ) * φ l y + φ m y, s85_Cc_lin (hφc l) (hφc m), fun x => ?_, fun i hi y => ?_⟩
    · rw [s85_Ulim_lin H ht.le htT (s85_Cc_memCM M (hφc l)) (s85_Cc_memCM M (hφc m)) (-1) x]
      simp only [hu]; ring
    · have e1 : (fun y => (-1 : ℝ) * φ l y + φ m y) =
          fun y => (φ m y - f y) - (φ l y - f y) := by funext y; ring
      rw [e1]
      have hi' : (i : WithTop ℕ∞) ≤ k := by exact_mod_cast hi
      have hA : ContDiff ℝ i (fun y => φ m y - f y) := ((hφi m).sub hfk).of_le hi'
      have hB : ContDiff ℝ i (fun y => φ l y - f y) := ((hφi l).sub hfk).of_le hi'
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := y) (i := i) hA.contDiffAt hB.contDiffAt
      simp only [Pi.sub_def] at this ⊢
      rw [this]
      refine (norm_sub_le _ _).trans ?_
      have h1 := hφe m i hi y
      have h2 := hφe l i hi y
      linarith
  have hcau : ∀ m l, ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (u m) y - iteratedFDeriv ℝ i (u l) y‖ ≤
      (e m + e l) * K' * jbracket y ^ M := by
    intro m l i hi y
    obtain ⟨ψ, hψc, hψeq, hψb⟩ := hdiff m l
    have hum := hsmooth (hφc m) i
    have hul := hsmooth (hφc l) i
    have e1 : iteratedFDeriv ℝ i (u m) y - iteratedFDeriv ℝ i (u l) y =
        iteratedFDeriv ℝ i (s85_Ulim a β ρβ M t ψ) y := by
      have h1 := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := y) (i := i) hum.contDiffAt hul.contDiffAt
      have h2 : (fun x => u m x - u l x) = s85_Ulim a β ρβ M t ψ := funext hψeq
      simp only [Pi.sub_def] at h1
      rw [← h1, h2]
    rw [e1]
    have := hbound hψc (add_nonneg (he0 m) (he0 l)) hψb i hi y
    linarith
  obtain ⟨hUc, hUb⟩ := s8f_closure hM hK' he0 hea het n (F := ℝ) (u := u) (U := U)
    (fun m => hsmooth (hφc m) n) hpt hcau
  -- the bound for `U`
  have hbU : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i U y‖ ≤ K' * ν * jbracket y ^ M := by
    intro i hi y
    have hj : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
    have hm : ∀ m, ‖iteratedFDeriv ℝ i U y‖ ≤ K' * ν * jbracket y ^ M + 2 * e m * (K' * jbracket y ^ M) := by
      intro m
      have h1 := hbound (hφc m) (add_nonneg hν (he0 m)) (hφν m) i hi y
      have h2 := hUb m i hi y
      have h3 : ‖iteratedFDeriv ℝ i U y‖ ≤ ‖iteratedFDeriv ℝ i U y - iteratedFDeriv ℝ i (u m) y‖ +
          ‖iteratedFDeriv ℝ i (u m) y‖ := by
        have := norm_add_le (iteratedFDeriv ℝ i U y - iteratedFDeriv ℝ i (u m) y) (iteratedFDeriv ℝ i (u m) y)
        simpa using this
      have h4 : K' * (ν + e m) * jbracket y ^ M = K' * ν * jbracket y ^ M + e m * (K' * jbracket y ^ M) := by ring
      nlinarith
    have hlim : Tendsto (fun m => K' * ν * jbracket y ^ M + 2 * e m * (K' * jbracket y ^ M)) atTop
        (𝓝 (K' * ν * jbracket y ^ M + 2 * 0 * (K' * jbracket y ^ M))) :=
      tendsto_const_nhds.add ((het.const_mul 2).mul_const _)
    have := ge_of_tendsto hlim (Eventually.of_forall hm)
    simpa using this
  refine ⟨⟨hUc, fun i hi idx => ?_⟩, hbU⟩
  have hpd : ∀ m x, |partialDeriv idx U x - partialDeriv idx (u m) x| ≤ e m * K' * jbracket x ^ M := by
    intro m x
    have hum := hsmooth (hφc m) i
    have hUi : ContDiff ℝ i U := hUc.of_le (by exact_mod_cast hi)
    have e1 : partialDeriv idx U x - partialDeriv idx (u m) x =
        partialDeriv idx (fun y => U y - u m y) x := by
      unfold partialDeriv
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) (i := i) hUi.contDiffAt hum.contDiffAt
      simp only [Pi.sub_def] at this ⊢
      rw [this]; rfl
    rw [e1]
    refine (s83_abs_partial_le i idx _ x).trans ?_
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) (i := i) (hUc.of_le (by exact_mod_cast hi)).contDiffAt
      (hsmooth (hφc m) i).contDiffAt
    simp only [Pi.sub_def] at this
    rw [this]
    exact hUb m i hi x
  refine s8d_decay_of_approx (c := K') (g := fun m => partialDeriv idx (u m)) (e := e) he0 het
    (fun m => ?_) (fun m x => hpd m x) hK'
  have hdm := s8f_Ulim_cc_decay H hMpos n ht htT (hφc m) i hi
  refine squeeze_zero_norm (fun x => ?_) hdm
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  rw [norm_div, Real.norm_of_nonneg hp.le]
  exact div_le_div_of_nonneg_right (by simpa [Real.norm_eq_abs] using s83_abs_partial_le i idx (u m) x) hp.le

end HRS.MS.Wad
