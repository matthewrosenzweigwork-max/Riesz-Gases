import HRS.MH.DualityRdB1
import HRS.MS.UniqC2c
import HRS.MS.AdjFarAux1
import HRS.MS.SuppU4Aux1
import HRS.MP.RdInit
import HRS.Whole.Orbits

/-!
# S5.5, commutator part 1: the setup gives `AdjointDecayHyp` (infrastructure, not a manuscript row)

For `b : WholeBounds d`, `S : WholeSetup b` and `b.s ≤ d - 2` the hypothesis block `AdjointDecayHyp`
(S4.12/S4.14) holds for `(ν, ρ) = (S.invβ N, S.ρ N)`.  Only the field `drift_cont` (joint continuity of
`(t,x) ↦ (∇g*ρ_t)(x)`) is not read off the setup: `WholeSetup.dens` is a statement at each fixed time.  It is
derived here from the weak mean-field identity `S.mf` (through the merged `mf_weak_integrable_proof`, which
shows that the generator in the weak form is integrable, so the weak identity is a genuine one: `t ↦ ∫ ψ ρ_t`
is Lipschitz on `[0,T]` for `ψ ∈ C_b²`), the uniform weighted bounds `S.dens`, and the approximate-identity
argument of `HRS.MS.UniqC2` (`c2_joint`, `c2_rgT_cont`), repeated here with smooth test functions (the weak
identity is for `C_b²` tests, `UniqC2` asks continuity for continuous compactly supported tests).
Helper names carry the prefix `s55_`; namespace `HRS.MS.Go`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd

variable {d : ℕ}

/-! ### Weighted sup norms -/

lemma s55_dse_bound {k : ℕ} {w : ℕ → ℝ} {Λ : ℝ} {f : Euc d → ℝ} (h : derivSupE k w f ≤ ENNReal.ofReal Λ)
    {j : ℕ} (hj : j ≤ k) (i : Fin j → Fin d) (x : Euc d) :
    jbracket x ^ w j * |partialDeriv i f x| ≤ max Λ 0 := by
  have h1 : ENNReal.ofReal (jbracket x ^ w j * |partialDeriv i f x|) ≤ derivSupE k w f := by
    unfold derivSupE
    exact le_iSup_of_le (⟨j, by omega⟩ : Fin (k + 1)) (le_iSup_of_le i (le_iSup_of_le x le_rfl))
  have h2 := h1.trans h
  have h3 : ENNReal.ofReal (jbracket x ^ w j * |partialDeriv i f x|) ≤ ENNReal.ofReal (max Λ 0) :=
    h2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h3

lemma s55_dse_le {k : ℕ} {w : ℕ → ℝ} {Λ : ℝ} {f : Euc d → ℝ}
    (h : ∀ j ≤ k, ∀ (i : Fin j → Fin d) (x : Euc d), jbracket x ^ w j * |partialDeriv i f x| ≤ Λ) :
    derivSupE k w f ≤ ENNReal.ofReal Λ := by
  unfold derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
  exact h j.1 (by omega) i x

lemma s55_dse_mono_order {k n : ℕ} (hkn : k ≤ n) (w : ℕ → ℝ) (f : Euc d → ℝ) :
    derivSupE k w f ≤ derivSupE n w f := by
  unfold derivSupE
  refine iSup_le fun j => ?_
  exact le_iSup_of_le (⟨j.1, by omega⟩ : Fin (n + 1)) le_rfl

lemma s55_jb_pos (x : Euc d) : 0 < jbracket x :=
  lt_of_lt_of_le one_pos (HRS.MS.Adj.ad1_one_le_jb x)

/-! ### The quadratic potential -/

lemma s55_vhyp_quadV {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm) (c : Euc d) :
    ∃ ΛV G₀ : ℝ, VHypRd 2 ΛV G₀ (quadV Q c) := by
  set Qc : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin Q).toContinuousLinearMap with hQc
  set V : Euc d → ℝ := quadV Q c with hV
  have hVs : ContDiff ℝ ∞ V := by
    have h1 : ContDiff ℝ ∞ (fun x : Euc d => (1 / 2 : ℝ) * inner ℝ x (Qc x)) :=
      contDiff_const.mul (contDiff_id.inner ℝ Qc.contDiff)
    have h2 : ContDiff ℝ ∞ (fun x : Euc d => inner ℝ c x) :=
      contDiff_const.inner ℝ contDiff_id
    exact h1.add h2
  have hgrad : ∀ x, gradient V x = Qc x + c := fun x => HRS.MS.Adj.ad_gradient_quadV hQ c x
  have hF : fderiv ℝ V = fun x => (InnerProductSpace.toDual ℝ (Euc d)) (Qc x + c) := by
    funext x
    have := hgrad x
    unfold gradient at this
    rw [← this]
    simp
  have hd2 : ∀ y, ‖fderiv ℝ (fderiv ℝ V) y‖ ≤ ‖Qc‖ := by
    intro y
    rw [hF]
    have hd : HasFDerivAt (fun x => (InnerProductSpace.toDual ℝ (Euc d)) (Qc x + c))
        ((InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.toContinuousLinearMap.comp Qc) y :=
      ((InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.hasFDerivAt).comp y
        (Qc.hasFDerivAt.add_const c)
    rw [hd.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have : ‖(InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simp
    nlinarith [norm_nonneg Qc]
  refine ⟨‖Qc‖, ‖gradient V 0‖, hVs, fun j hj2 hj x => ?_, le_rfl⟩
  have hj' : j = 2 := le_antisymm hj hj2
  subst hj'
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := V) (x := x) (n := 1)
  rw [norm_iteratedFDeriv_one] at h1
  rw [← h1]
  exact hd2 x


/-! ### Regularity slice and the `MFData` of the setup -/

lemma s55_card_sum_le (j : ℕ) {K : ℝ} (f : (Fin j → Fin d) → ℝ) (hf : ∀ i, f i ≤ K) :
    ∑ i, f i ≤ (d : ℝ) ^ j * K := by
  calc ∑ i, f i ≤ ∑ _i : Fin j → Fin d, K := Finset.sum_le_sum fun i _ => hf i
    _ = (d : ℝ) ^ j * K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

lemma s55_regular_slice {n : ℕ} (hn : 3 ≤ n) {L Λ : ℝ} (hL : (d : ℝ) + 3 ≤ L) {f : Euc d → ℝ}
    (hf : ContDiff ℝ n f) (hw : weightedSupE n L f ≤ ENNReal.ofReal Λ) :
    MemCb 3 f ∧ weightedSupE 3 ((d : ℝ) + 3) f < ⊤ ∧
      HRS.cbNorm 3 f + (weightedSupE 3 ((d : ℝ) + 3) f).toReal ≤
        (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max Λ 0 := by
  have hL0 : 0 ≤ L := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hΛ0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hp : ∀ j ≤ 3, ∀ (i : Fin j → Fin d) (x : Euc d), |partialDeriv i f x| ≤ max Λ 0 := by
    intro j hj i x
    have h1 := s55_dse_bound (w := fun _ => L) hw (j := j) (by omega) i x
    have h2 : 1 ≤ jbracket x ^ L := Real.one_le_rpow (HRS.MS.Adj.ad1_one_le_jb x) hL0
    nlinarith [abs_nonneg (partialDeriv i f x)]
  have hnorm : ∀ j ≤ 3, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ j * max Λ 0 := by
    intro j hj x
    exact (HRS.MP.RdInit.mri_norm_iter_le j f x).trans
      (s55_card_sum_le j _ fun i => hp j hj i x)
  have hmem : MemCb 3 f :=
    ⟨hf.of_le (by exact_mod_cast hn), fun j hj => ⟨(d : ℝ) ^ j * max Λ 0, by
      rintro _ ⟨x, rfl⟩; exact hnorm j hj x⟩⟩
  have hcb : HRS.cbNorm 3 f ≤ ∑ j ∈ Finset.range 4, (d : ℝ) ^ j * max Λ 0 := by
    unfold HRS.cbNorm
    refine Finset.sum_le_sum fun j hj => ?_
    exact ciSup_le fun x => hnorm j (by have := Finset.mem_range.1 hj; omega) x
  have hwse : weightedSupE 3 ((d : ℝ) + 3) f ≤ ENNReal.ofReal (max Λ 0) := by
    refine s55_dse_le fun j hj i x => ?_
    have h1 := s55_dse_bound (w := fun _ => L) hw (j := j) (by omega) i x
    have h2 : jbracket x ^ ((d : ℝ) + 3) ≤ jbracket x ^ L :=
      Real.rpow_le_rpow_of_exponent_le (HRS.MS.Adj.ad1_one_le_jb x) hL
    exact (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)).trans h1
  refine ⟨hmem, lt_of_le_of_lt hwse ENNReal.ofReal_lt_top, ?_⟩
  have h3 : (weightedSupE 3 ((d : ℝ) + 3) f).toReal ≤ max Λ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hwse
    rwa [ENNReal.toReal_ofReal hΛ0] at this
  calc HRS.cbNorm 3 f + (weightedSupE 3 ((d : ℝ) + 3) f).toReal
      ≤ ∑ j ∈ Finset.range 4, (d : ℝ) ^ j * max Λ 0 + max Λ 0 := add_le_add hcb h3
    _ = (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max Λ 0 := by
        rw [add_mul, one_mul, Finset.sum_mul]

/-- The mean-field data of the setup (for `s < d - 1`, so that the fractional-force clause of
`IsRegularMFRd` is vacuous). -/
theorem s55_mfdata {s T ν Λ L : ℝ} {n : ℕ} (hn : 3 ≤ n) (hL : (d : ℝ) + 3 ≤ L)
    (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 1) (M Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) (c : Euc d)
    (hν : 0 ≤ ν) {ρ : ℝ → Euc d → ℝ}
    (hmf : IsWholeMeanFieldSolution (⟨s, M, quadV Q c, ν⟩ : WholeDyn d) T ρ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ n (ρ t) ∧ weightedSupE n L (ρ t) ≤ ENNReal.ofReal Λ) :
    ∃ Λ'' ΛV G₀ : ℝ, MFData s Λ'' T ΛV G₀ (⟨s, M, quadV Q c, ν⟩ : WholeDyn d) ρ := by
  obtain ⟨ΛV, G₀, hV⟩ := s55_vhyp_quadV hQ c
  refine ⟨(∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max Λ 0, ΛV, G₀, rfl, hs0, ?_, hν, hV, hmf, ?_, ?_⟩
  · linarith
  · intro t ht
    exact s55_regular_slice hn hL (hdens t ht).1 (hdens t ht).2
  · intro h; exfalso; linarith

/-! ### Weak continuity -/

theorem s55_weak_cont {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ}
    (h : MFData s Λ T ΛV G₀ D ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Set.Icc (0 : ℝ) T) := by
  obtain ⟨-, ⟨K, hK⟩, hweak⟩ := mf_weak_integrable_proof h hψ
  have hP : ∀ t ∈ Set.Icc (0 : ℝ) T, (∫ x, ψ x * ρ t x) = Whole.pair (Whole.withDensityReal (ρ t)) ψ := by
    intro t ht
    rw [Whole.Q09A.pair_withDensityReal (h.hρ.density t ht)]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hlip : ∀ a ∈ Set.Icc (0 : ℝ) T, ∀ b ∈ Set.Icc (0 : ℝ) T, a ≤ b →
      |(∫ x, ψ x * ρ b x) - ∫ x, ψ x * ρ a x| ≤ max K 0 * |b - a| := by
    intro a ha b hb hab
    rw [hP a ha, hP b hb, hweak a b ha.1 hab hb.2, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := max K 0) fun r hr => ?_).trans ?_
    · rw [Set.uIoc_of_le hab] at hr
      rw [Real.norm_eq_abs]
      exact (hK r ⟨ha.1.trans hr.1.le, hr.2.trans hb.2⟩).trans (le_max_left _ _)
    · rw [abs_of_nonneg (sub_nonneg.2 hab)]
  have : LipschitzOnWith (Real.toNNReal (max K 0)) (fun t => ∫ x, ψ x * ρ t x) (Set.Icc (0 : ℝ) T) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_max_right _ _)]
    rcases le_total a b with hab | hab
    · rw [abs_sub_comm, abs_sub_comm a b]; exact hlip a ha b hb hab
    · exact hlip b hb a ha hab
  exact this.continuousOn

/-! ### Joint continuity (the approximate-identity argument of `UniqC2`, smooth test functions) -/

/-- Existence of the approximate identity (`ContDiffBump`). -/
lemma s55_bump (y : Euc d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ w, 0 ≤ ψ w) ∧ ∫ w, ψ w = 1 ∧
      ∀ w, ψ w ≠ 0 → ‖w - y‖ < δ := by
  let f : ContDiffBump y := ⟨δ / 2, δ, by positivity, by linarith⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, f.nonneg_normed,
    f.integral_normed, fun w hw => ?_⟩
  have : w ∈ Function.support (f.normed volume) := hw
  rw [f.support_normed_eq] at this
  simpa [dist_eq_norm] using this

/-- **Pointwise continuity from weak continuity and a uniform Lipschitz bound.** -/
lemma s55_pointwise {S : Set ℝ} {g : ℝ → Euc d → ℝ} {b1 : ℝ} (hb1 : 0 ≤ b1)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) S)
    (hdiff : ∀ r ∈ S, Differentiable ℝ (g r)) (hlip : ∀ r ∈ S, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1)
    (y : Euc d) : ContinuousOn (fun r => g r y) S := by
  rw [Metric.continuousOn_iff]
  intro r₀ hr₀ ε hε
  set δ : ℝ := ε / (3 * (b1 + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hbδ : b1 * δ < ε / 3 := by
    have : b1 * δ = ε / 3 * (b1 / (b1 + 1)) := by rw [hδdef]; field_simp
    rw [this]
    have h1 : b1 / (b1 + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have : 0 < ε / 3 := by positivity
    nlinarith
  obtain ⟨ψ, hψc, hψk, hψn, hψ1, hψs⟩ := s55_bump y hδ
  obtain ⟨η, hη, hηr⟩ := Metric.continuousOn_iff.1 (hweak ψ hψc hψk) r₀ hr₀ (ε / 3) (by positivity)
  refine ⟨η, hη, fun r hr hrd => ?_⟩
  have h1 := HRS.MS.UniqC2.c2_approx (hdiff r hr) (hlip r hr) hb1 y hδ ψ hψc.continuous hψk hψn hψ1 hψs
  have h2 := HRS.MS.UniqC2.c2_approx (hdiff r₀ hr₀) (hlip r₀ hr₀) hb1 y hδ ψ hψc.continuous hψk hψn hψ1 hψs
  have h3 := hηr r hr hrd
  rw [Real.dist_eq] at h3 ⊢
  have e : g r y - g r₀ y = (g r y - ∫ w, ψ w * g r w) - (g r₀ y - ∫ w, ψ w * g r₀ w) +
      ((∫ w, ψ w * g r w) - ∫ w, ψ w * g r₀ w) := by ring
  rw [e]
  calc _ ≤ |(g r y - ∫ w, ψ w * g r w) - (g r₀ y - ∫ w, ψ w * g r₀ w)| +
        |(∫ w, ψ w * g r w) - ∫ w, ψ w * g r₀ w| := abs_add_le _ _
    _ ≤ (|g r y - ∫ w, ψ w * g r w| + |g r₀ y - ∫ w, ψ w * g r₀ w|) +
        |(∫ w, ψ w * g r w) - ∫ w, ψ w * g r₀ w| := by
          gcongr; exact abs_sub _ _
    _ < ε := by linarith

/-- **Joint continuity** of `(r,x) ↦ g r x` on `S × ℝ^d`. -/
lemma s55_joint {S : Set ℝ} {g : ℝ → Euc d → ℝ} {b1 : ℝ} (hb1 : 0 ≤ b1)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) S)
    (hdiff : ∀ r ∈ S, Differentiable ℝ (g r)) (hlip : ∀ r ∈ S, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1) :
    ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (S ×ˢ Set.univ) := by
  intro p₀ hp₀
  obtain ⟨r₀, x₀⟩ := p₀
  have hr₀ : r₀ ∈ S := hp₀.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, hηr⟩ := Metric.continuousOn_iff.1
    (s55_pointwise hb1 hweak hdiff hlip x₀) r₀ hr₀ (ε / 2) (by positivity)
  set δ : ℝ := min η (ε / (2 * (b1 + 1))) with hδdef
  have hδ : 0 < δ := lt_min hη (by positivity)
  refine ⟨δ, hδ, fun ⟨r, x⟩ hp hd => ?_⟩
  have hr : r ∈ S := hp.1
  rw [Prod.dist_eq] at hd
  simp only at hd
  have hd1 : dist r r₀ < η := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hd) (min_le_left _ _)
  have hd2 : dist x x₀ < ε / (2 * (b1 + 1)) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hd) (min_le_right _ _)
  have h1 := hηr r hr hd1
  have h2 := HRS.MS.UniqC2.c2_lip (hdiff r hr) (hlip r hr) x x₀
  have h3 : b1 * ‖x - x₀‖ < ε / 2 := by
    rw [← dist_eq_norm]
    have : b1 * dist x x₀ ≤ (b1 + 1) * dist x x₀ := by
      nlinarith [dist_nonneg (x := x) (y := x₀)]
    have h4 : (b1 + 1) * dist x x₀ < ε / 2 := by
      calc (b1 + 1) * dist x x₀ < (b1 + 1) * (ε / (2 * (b1 + 1))) :=
            mul_lt_mul_of_pos_left hd2 (by linarith)
        _ = ε / 2 := by field_simp
    linarith
  rw [Real.dist_eq] at h1 ⊢
  have e : g r x - g r₀ x₀ = (g r x - g r x₀) + (g r x₀ - g r₀ x₀) := by ring
  rw [e]
  calc _ ≤ |g r x - g r x₀| + |g r x₀ - g r₀ x₀| := abs_add_le _ _
    _ < ε := by linarith


theorem s55_force_cont (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ)
    {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) T, MemCb 3 (ρ t) ∧ weightedSupE 3 ((d : ℝ) + 3) (ρ t) < ⊤ ∧
      HRS.cbNorm 3 (ρ t) + (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun p : ℝ × Euc d => convGradConvW (rieszKernelGrad d s) (ρ p.1) p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  set A : ℝ := (d : ℝ) ^ 3 * max Λ 0 * 2 ^ ((d : ℝ) + 3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hdec : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.MP.RdGen.RgDecay 3 (fun _ => A) (ρ r) := by
    intro r hr
    have hcb := hreg r hr
    have hcb0 : 0 ≤ HRS.cbNorm 3 (ρ r) :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    exact HRS.MP.RdGen.rg_rho_decay hd (r := 3) (Λ := max Λ 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ 0])
  have hparts := fun r hr => HRS.MP.RdGen.rg_decay_parts (n := 3) (by omega) (a := fun _ => A)
    (fun _ => hA) (hdec r hr)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) T, Differentiable ℝ (ρ r) := fun r hr =>
    ((hparts r hr).1).differentiable (by norm_num)
  have h0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖ρ r y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) :=
    fun r hr => (hparts r hr).2.1
  have h1' : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ A := fun r hr y =>
    ((hparts r hr).2.2.1 y).trans (by
      calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 := mul_le_mul_of_nonneg_left (hw y) hA
        _ = A := mul_one _)
  have hjoint := s55_joint hA hweak hdiff h1'
  apply HRS.MS.UniqC2.c2_vec_contOn
  intro i
  have hcomp := HRS.MS.UniqC2.c2_rgT_cont hd hs0 hsd (HRS.MP.RdGen.rgKerComp_ok (d := d) hs0 i) hA hA hdiff h0 h1' hjoint
  refine hcomp.congr fun p hp => ?_
  exact HRS.MP.RdGen.rg_force_comp hd hs0 hsd (hdiff p.1 hp.1) hA hA (h0 p.1 hp.1) (h1' p.1 hp.1) p.2 i


/-! ### `AdjointDecayHyp` from the setup -/

/-- For `b.s ≤ d - 2` the hypothesis block of S4.12/S4.14 holds for `(ν, ρ) = (S.invβ N, S.ρ N)`. -/
theorem s55_adjointDecayHyp (b : WholeBounds d) (hb : b.Valid) (hsub : b.s ≤ (d : ℝ) - 2)
    (S : WholeSetup b) (N : ℕ) :
    AdjointDecayHyp b.θ b.s b.M b.Q b.c b.T b.νstar b.k b.L b.Λ b.K (S.invβ N) (S.ρ N) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hs0 := hb.hs0
  have hL := hb.hL
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hn : 3 ≤ b.k + 6 + ⌈(d : ℝ) / 2⌉₊ := by omega
  have hsd1 : b.s < (d : ℝ) - 1 := by linarith
  obtain ⟨Λ'', ΛV, G₀, hMF⟩ := s55_mfdata hn hdL hb.hs0 hsd1 b.M b.Q hb.hQ b.c (S.hinvβ N).1
    (S.mf N) (S.dens N)
  refine ⟨⟨hb.hs0, hsub⟩, S.hinvβ N, hb.hQ, by linarith, ?_, S.adjoint N, ?_⟩
  · intro t ht
    refine ⟨(S.mf N).density t ht, ((S.dens N t ht).1).of_le (by exact_mod_cast (by omega)), ?_⟩
    exact (s55_dse_mono_order (by omega) _ _).trans (S.dens N t ht).2
  · refine s55_force_cont hd1 hb.hs0 hb.hsd ((∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max b.Λ 0) (fun t ht => ?_) (fun ψ hψ hcs => ?_)
    · exact s55_regular_slice hn hdL (S.dens N t ht).1 (S.dens N t ht).2
    · exact s55_weak_cont hMF (HRS.Whole.u4_memCb 2 ⟨hψ, hcs⟩)

end HRS.MS.Go
