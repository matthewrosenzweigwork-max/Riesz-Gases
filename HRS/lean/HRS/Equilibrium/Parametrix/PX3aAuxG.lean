import HRS.Equilibrium.Parametrix.PX3aAuxF
import HRS.Equilibrium.Parametrix.PX1AuxExtApply
import HRS.Equilibrium.Parametrix.PX2AuxE

/-!
# Packet PX3a auxiliaries G: the chart-level source class
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Chart-level source class: `g(X, w)` supported in `‖w‖ ≤ 1/16`, `C^m` for `w ≠ 0`, with the
conormal bounds of order `σ` (log power `b`, constant `A`). -/
structure SrcCls (d : ℕ) (σ : ℝ) (b m : ℕ) (A : ℝ) (g : Euc d × Euc d → ℝ) : Prop where
  smooth : ContDiffOn ℝ (m : WithTop ℕ∞) g {p | p.2 ≠ 0}
  supp : ∀ X w : Euc d, 1 / 16 < ‖w‖ → g (X, w) = 0
  bound : ∀ a c : ℕ, a + c ≤ m → ∀ X w : Euc d, w ≠ 0 →
    ‖mixedDeriv a c g X w‖ ≤ A * (1 + ‖w‖ ^ (-(σ + c)) * (1 + |Real.log ‖w‖|) ^ b)

/-- The Newton potential of a chart source. -/
def newtonPot (d : ℕ) (g : Euc d × Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  ∫ w, Efund d (p.2 - w) * g (p.1, w)

lemma isOpen_ne_snd : IsOpen {p : Euc d × Euc d | p.2 ≠ 0} :=
  isOpen_ne_fun continuous_snd continuous_const

namespace SrcCls

variable {σ : ℝ} {b m : ℕ} {A : ℝ} {g : Euc d × Euc d → ℝ}

lemma slice_bound (h : SrcCls d σ b m A g) {j : ℕ} (hj : j ≤ m) (X w : Euc d) (hw : w ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun X' => g (X', w)) X‖ ≤ A * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b) := by
  have := h.bound j 0 (by omega) X w hw
  rw [norm_mixedDeriv_zero] at this
  simpa using this

lemma slice_zero (h : SrcCls d σ b m A g) (j : ℕ) {w : Euc d} (hw : 1 / 16 < ‖w‖) (X : Euc d) :
    iteratedFDeriv ℝ j (fun X' => g (X', w)) X = 0 := by
  have : (fun X' => g (X', w)) = fun _ => (0 : ℝ) := by funext X'; exact h.supp X' w hw
  rw [this]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [iteratedFDeriv_zero_eq_comp]
  · have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) (by omega : j ≠ 0) (0 : ℝ)
    exact congrFun this X


lemma slice_continuousOn (h : SrcCls d σ b m A g) (X : Euc d) :
    ContinuousOn (fun w => g (X, w)) {w | w ≠ 0} := by
  have h1 : ContinuousOn g {p : Euc d × Euc d | p.2 ≠ 0} := h.smooth.continuousOn
  exact h1.comp (by fun_prop : Continuous fun w : Euc d => ((X, w) : Euc d × Euc d)).continuousOn
    (fun w hw => hw)

lemma slice_aesm (hd : 1 ≤ d) (h : SrcCls d σ b m A g) (X : Euc d) :
    AEStronglyMeasurable (fun w => g (X, w)) (volume : Measure (Euc d)) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have := (h.slice_continuousOn X).aestronglyMeasurable (isOpen_ne.measurableSet) (μ := volume)
  rwa [show {w : Euc d | w ≠ 0} = ({0}ᶜ : Set (Euc d)) from rfl, restrict_compl_singleton] at this

lemma slice_integrable (hd : 1 ≤ d) (hσ : σ < d) (h : SrcCls d σ b m A g) (X : Euc d) :
    Integrable (fun w => g (X, w)) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hsupp : Function.support (fun w => g (X, w)) ⊆ Metric.ball (0 : Euc d) (1 / 8) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hh
    exact hw (h.supp X w (by linarith [not_lt.mp hh]))
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hg : IntegrableOn (fun w : Euc d => A * (1 + ‖w‖ ^ (-σ) * (1 + |Real.log ‖w‖|) ^ b))
      (Metric.ball (0 : Euc d) (1 / 8)) := by
    refine Integrable.const_mul ?_ A
    exact (integrableOn_const (measure_ball_lt_top.ne)).add (integrableOn_rpow_log hd hσ b (by norm_num))
  refine Integrable.mono' hg (h.slice_aesm hd X).restrict ?_
  have hae : ∀ᵐ w : Euc d, w ≠ 0 := by
    have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
    filter_upwards [this] with w hw using by simpa using hw
  refine (ae_restrict_iff' measurableSet_ball).mpr ?_
  filter_upwards [hae] with w hw0 _
  have := h.slice_bound (Nat.zero_le m) X w hw0
  simpa [iteratedFDeriv_zero_eq_comp] using this


lemma full_bound (h : SrcCls d σ b m A g) (hA : 0 ≤ A) {k : ℕ} (hk : k ≤ m) {ρ0 : ℝ} (hρ0 : 0 < ρ0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q : Euc d × Euc d, ρ0 ≤ ‖q.2‖ → ‖iteratedFDeriv ℝ k g q‖ ≤ M := by
  set Wc : ℕ → ℝ := fun c => A * (1 + (ρ0 ^ (-(σ + c)) + (1 / 16 : ℝ) ^ (-(σ + c))) * lw ρ0 ^ b) with hWc
  have hWc0 : ∀ c, 0 ≤ Wc c := fun c => by
    have := lw_pos ρ0
    simp only [hWc]; positivity
  set S : ℝ := ∑ c ∈ Finset.range (k + 1), Wc c with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => hWc0 c
  have hWS : ∀ c ≤ k, Wc c ≤ S := fun c hc =>
    Finset.single_le_sum (f := Wc) (fun i _ => hWc0 i) (Finset.mem_range.mpr (by omega))
  refine ⟨2 ^ k * S, by positivity, fun q hq => ?_⟩
  by_cases hbig : 1 / 16 < ‖q.2‖
  · have : g =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds hbig]
        with p hp using h.supp p.1 p.2 hp
    rw [(this.iteratedFDeriv ℝ k).eq_of_nhds]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [iteratedFDeriv_zero_eq_comp]
      positivity
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp; positivity
  · have ht1 : ‖q.2‖ ≤ 1 / 16 := not_lt.mp hbig
    have hq0 : q.2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hρ0 hq)
    have hqU : q ∈ {p : Euc d × Euc d | p.2 ≠ 0} := hq0
    have hT : ∀ a c, a + c = k → TB g q a c S := by
      intro a c hac
      refine tb_of_norm_le isOpen_ne_snd ?_ hqU ?_
      · exact h.smooth.of_le (by exact_mod_cast (by omega : a + c ≤ m))
      · refine (h.bound a c (by omega) q.1 q.2 hq0).trans ?_
        refine le_trans ?_ (hWS c (by omega))
        simp only [hWc]
        have hpos : 0 < ‖q.2‖ := lt_of_lt_of_le hρ0 hq
        have h1 : ‖q.2‖ ^ (-(σ + c)) ≤ ρ0 ^ (-(σ + c)) + (1 / 16 : ℝ) ^ (-(σ + c)) :=
          rpow_le_of_mem _ hρ0 hq ht1
        have h2 : (1 + |Real.log ‖q.2‖|) ^ b ≤ lw ρ0 ^ b :=
          pow_le_pow_left₀ (lw_pos _).le (lw_anti hρ0 hq (by linarith)) b
        have h3 : 0 ≤ ‖q.2‖ ^ (-(σ + c)) := by positivity
        gcongr
    have hfull := full_of_tb k g S hS0 (h.smooth.contDiffAt (isOpen_ne_snd.mem_nhds hqU) |>.of_le
      (by exact_mod_cast hk)) hT
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
    have := hfull w
    rw [Real.norm_eq_abs]
    calc |iteratedFDeriv ℝ k g q w| ≤ 2 ^ k * S * ∏ i, ‖w i‖ := this
      _ = _ := rfl

end SrcCls

section Prodpat

variable {φ ψ : Euc d → ℝ}

lemma hasFDerivAt_prod_pair (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (q : Euc d × Euc d) :
    HasFDerivAt (fun q : Euc d × Euc d => φ q.2 * ψ q.1)
      (φ q.2 • ((fderiv ℝ ψ q.1).comp (ContinuousLinearMap.fst ℝ (Euc d) (Euc d))) +
        ψ q.1 • ((fderiv ℝ φ q.2).comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)))) q := by
  have h1 : HasFDerivAt (fun q : Euc d × Euc d => φ q.2)
      ((fderiv ℝ φ q.2).comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d))) q :=
    (hφ q.2).hasFDerivAt.comp q hasFDerivAt_snd
  have h2 : HasFDerivAt (fun q : Euc d × Euc d => ψ q.1)
      ((fderiv ℝ ψ q.1).comp (ContinuousLinearMap.fst ℝ (Euc d) (Euc d))) q :=
    (hψ q.1).hasFDerivAt.comp q hasFDerivAt_fst
  exact h1.mul h2

lemma dirD_prod_snd (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (h : Euc d) :
    dirD ((0 : Euc d), h) (fun q : Euc d × Euc d => φ q.2 * ψ q.1) =
      fun q => dirD h φ q.2 * ψ q.1 := by
  funext q
  simp only [dirD]
  rw [(hasFDerivAt_prod_pair hφ hψ q).fderiv]
  simp [mul_comm]

lemma dirD_prod_fst (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (h : Euc d) :
    dirD (h, (0 : Euc d)) (fun q : Euc d × Euc d => φ q.2 * ψ q.1) =
      fun q => φ q.2 * dirD h ψ q.1 := by
  funext q
  simp only [dirD]
  rw [(hasFDerivAt_prod_pair hφ hψ q).fderiv]
  simp


lemma iteratedFDeriv_prodpat : ∀ (n a c : ℕ), a + c = n → ∀ (φ ψ : Euc d → ℝ),
    ContDiff ℝ (n : WithTop ℕ∞) φ → ContDiff ℝ (n : WithTop ℕ∞) ψ →
    ∀ (p : Euc d × Euc d) (u : Fin a → Euc d) (v : Fin c → Euc d),
      iteratedFDeriv ℝ (a + c) (fun q : Euc d × Euc d => φ q.2 * ψ q.1) p (pat u v) =
        iteratedFDeriv ℝ c φ p.2 v * iteratedFDeriv ℝ a ψ p.1 u := by
  intro n
  induction n with
  | zero =>
    intro a c hac φ ψ hφ hψ p u v
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro a c hac φ ψ hφ hψ p u v
    have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
    have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have hΦ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun q : Euc d × Euc d => φ q.2 * ψ q.1) :=
      (hφ.comp contDiff_snd).mul (hψ.comp contDiff_fst)
    rcases c with _ | c'
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨n, by omega⟩
      obtain rfl : a' = n := by omega
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      subst hv
      set h := u (Fin.last a') with hh
      set u' := Fin.init u with hu'
      have hpat : pat u (Fin.elim0 : Fin 0 → Euc d) =
          (Fin.snoc (pat u' (Fin.elim0 : Fin 0 → Euc d)) (h, (0 : Euc d)) : Fin (a' + 0 + 1) → Euc d × Euc d) := by
        have := pat_snoc_left u' h
        rw [hu', hh, Fin.snoc_init_self] at this
        exact this
      rw [hpat, ← iteratedFDeriv_dirD hΦ.contDiffAt (h, (0 : Euc d)) (pat u' Fin.elim0)]
      rw [dirD_prod_fst hdφ hdψ h]
      have hψ' : ContDiff ℝ (a' : WithTop ℕ∞) (dirD h ψ) := by
        have := hψ.fderiv_right (m := a') (by norm_cast)
        exact this.clm_apply contDiff_const
      have e := ih a' 0 (by omega) φ (dirD h ψ) (hφ.of_le (by exact_mod_cast Nat.le_succ a')) hψ' p u' Fin.elim0
      simp only [Nat.add_zero] at e
      rw [e]
      rw [iteratedFDeriv_dirD hψ.contDiffAt h u', Fin.snoc_init_self]
    · obtain rfl : n = a + c' := by omega
      have hv : v = Fin.snoc (Fin.init v) (v (Fin.last c')) := (Fin.snoc_init_self v).symm
      set h := v (Fin.last c') with hh
      set v' := Fin.init v with hv'
      have hpat : pat u v = (Fin.snoc (pat (a := a) (c := c') u v') ((0 : Euc d), h) : Fin (a + c' + 1) → Euc d × Euc d) := by
        rw [hv]; exact pat_snoc_right u v' h
      rw [hpat]
      refine Eq.trans (iteratedFDeriv_dirD hΦ.contDiffAt ((0 : Euc d), h) (pat (a := a) (c := c') u v')).symm ?_
      rw [dirD_prod_snd hdφ hdψ h]
      have hφ' : ContDiff ℝ ((a + c' : ℕ) : WithTop ℕ∞) (dirD h φ) := by
        have := hφ.fderiv_right (m := a + c') (by norm_cast)
        exact this.clm_apply contDiff_const
      rw [ih a c' (by omega) (dirD h φ) ψ hφ' (hψ.of_le (by exact_mod_cast Nat.le_succ (a + c'))) p u v']
      rw [iteratedFDeriv_dirD (hφ.of_le (by exact_mod_cast (by omega : c' + 1 ≤ a + c' + 1))).contDiffAt h v', ← hv]

end Prodpat

end HRS.Parx

end
