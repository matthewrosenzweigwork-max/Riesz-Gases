import HRS.MS.S104eC3H

/-!
# S104E route C, packet C3, file I: the limit of the Picard iterates
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ} {j : ℕ} {η H : ℝ} {P A : ℝ → (Euc d → ℝ) → Euc d → ℝ}

theorem s104c3_geom_tail (a : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => a * (1 / 2 : ℝ) ^ (k + n + 1)) (a * (1 / 2) ^ n) := by
  have h := (hasSum_geometric_two).mul_left (a * (1 / 2) ^ (n + 1))
  convert h using 1
  · funext k; ring
  · ring

theorem s104c3_unif_series {X G : Type*} [NormedAddCommGroup G] [CompleteSpace G] (c : X → G)
    (F : ℕ → X → G) (a : ℝ) (hF : ∀ k x, ‖F k x‖ ≤ a * (1 / 2 : ℝ) ^ (k + 1)) :
    TendstoUniformly (fun n x => c x + ∑ k ∈ Finset.range n, F k x) (fun x => c x + ∑' k, F k x) atTop ∧
    ∀ n x, ‖(∑' k, F k x) - ∑ k ∈ Finset.range n, F k x‖ ≤ a * (1 / 2) ^ n := by
  have hsum : Summable (fun k : ℕ => a * (1 / 2 : ℝ) ^ (k + 1)) := by
    have := (s104c3_geom_tail a 0).summable
    simpa using this
  constructor
  · have h := tendstoUniformly_tsum_nat hsum hF
    rw [Metric.tendstoUniformly_iff] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with n hn x
    simpa [dist_add_left] using hn x
  · intro n x
    have hs : Summable (fun k => F k x) := Summable.of_norm_bounded hsum (fun k => hF k x)
    have := hs.sum_add_tsum_nat_add n
    have e : (∑' k, F k x) - ∑ k ∈ Finset.range n, F k x = ∑' k, F (k + n) x := by
      rw [← this]; abel
    rw [e]
    exact tsum_of_norm_bounded (s104c3_geom_tail a n) (fun k => hF (k + n) x)

theorem s104c3_HolB_zero {j : ℕ} {η B : ℝ} (hB : 0 ≤ B) : HolB j η B (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨(Bd.zero (j + 1)).mono_A hB, fun x z => ?_⟩
  have h0 : iteratedFDeriv ℝ (j + 1) (fun _ : Euc d => (0 : ℝ)) (x + z) -
      iteratedFDeriv ℝ (j + 1) (fun _ : Euc d => (0 : ℝ)) x = 0 := by
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]; simp
  rw [h0, norm_zero]
  exact mul_nonneg hB (Real.rpow_nonneg (norm_nonneg _) _)

/-- The limit of the Picard iterates. -/
theorem s104c3_limit (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {lam : ℝ} (hlam : 0 ≤ lam) (hθ : s104c3_theta hyp lam ≤ 1 / 2) {B : ℝ}
    {ψ : Euc d → ℝ} (hψ : HolB j η B ψ) (hψv : VanB (j + 1) ψ) :
    ∃ w : ℝ → Euc d → ℝ,
      (∀ r ∈ Icc 0 t, HolB j η (2 * hyp.CP * B * Real.exp (lam * (t - r))) (w r)) ∧
      (∀ r ∈ Icc 0 t, ∀ n : ℕ, HolB j η (hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r)))
        (fun x => w r x - s104c3_seq P A t ψ n r x)) ∧
      s104c3_TC t (j + 1) w ∧ (∀ r ∈ Icc 0 t, VanB (j + 1) (w r)) ∧
      ∀ r ∈ Icc 0 t, ∀ x, Tendsto (fun n => s104c3_seq P A t ψ n r x) atTop (𝓝 (w r x)) := by
  have hCP : 0 < hyp.CP := by linarith [hyp.CP1]
  have hB : 0 ≤ B := s104c3_HolB_nonneg hψ
  have props := s104c3_seq_props hyp hη0 hη1 ht hlam hθ hψ hψv
  set S := s104c3_seq P A t ψ with hS
  have hE0 : ∀ r : ℝ, 0 < Real.exp (lam * (t - r)) := fun r => Real.exp_pos _
  have hseqcd : ∀ n, ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (S n r) :=
    fun n r hr => ((props n).1 r hr).1.1
  have hddcd : ∀ n, ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
      (fun x => S (n + 1) r x - S n r x) := fun n r hr => ((props n).2.2.2 r hr).1.1
  -- telescoping of jets
  have htel : ∀ n, ∀ r ∈ Icc 0 t, ∀ m ≤ j + 1, ∀ x, iteratedFDeriv ℝ m (S n r) x =
      iteratedFDeriv ℝ m (S 0 r) x +
        ∑ k ∈ Finset.range n, iteratedFDeriv ℝ m (fun y => S (k + 1) r y - S k r y) x := by
    intro n r hr m hm x
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      have e : S (n + 1) r = fun y => 1 * S n r y + (S (n + 1) r y - S n r y) := by
        funext y; ring
      conv_lhs => rw [e]
      rw [s104c3_jets_lin_apply 1 (hseqcd n r hr) (hddcd n r hr) hm x, one_smul]
  have htel0 : ∀ n, ∀ r : ℝ, ∀ x, S n r x = S 0 r x + ∑ k ∈ Finset.range n, (S (k + 1) r x - S k r x) := by
    intro n r x
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih]; ring
  -- the limit
  set w : ℝ → Euc d → ℝ := fun r x => S 0 r x + ∑' k, (S (k + 1) r x - S k r x) with hw
  have hbd : ∀ k, ∀ r ∈ Icc 0 t, ∀ m ≤ j + 1, ∀ x,
      ‖iteratedFDeriv ℝ m (fun y => S (k + 1) r y - S k r y) x‖ ≤
        hyp.CP * B * Real.exp (lam * (t - r)) * (1 / 2) ^ (k + 1) := by
    intro k r hr m hm x
    have := ((props k).2.2.2 r hr).1.2 m hm x
    refine this.trans (le_of_eq ?_)
    ring
  have hper : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (w r) ∧
      (∀ m ≤ j + 1, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ m (S n r) x) atTop
        (𝓝 (iteratedFDeriv ℝ m (w r) x))) ∧
      (∀ x, Tendsto (fun n => S n r x) atTop (𝓝 (w r x))) := by
    intro r hr
    have hlimval := (s104c3_unif_series (G := ℝ) (S 0 r)
      (fun k x => S (k + 1) r x - S k r x) (hyp.CP * B * Real.exp (lam * (t - r))) (fun k x => by
        have := hbd k r hr 0 (Nat.zero_le _) x
        rwa [norm_iteratedFDeriv_zero] at this)).1
    have hval : ∀ x, Tendsto (fun n => S n r x) atTop (𝓝 (w r x)) := by
      intro x
      have := hlimval.tendsto_at x
      refine this.congr fun n => ?_
      exact (htel0 n r x).symm
    have hlimj : ∀ m ≤ j + 1, TendstoUniformly (fun n x => iteratedFDeriv ℝ m (S n r) x)
        (fun x => iteratedFDeriv ℝ m (S 0 r) x +
          ∑' k, iteratedFDeriv ℝ m (fun y => S (k + 1) r y - S k r y) x) atTop := by
      intro m hm
      have h := (s104c3_unif_series (G := Euc d [×m]→L[ℝ] ℝ) (fun x => iteratedFDeriv ℝ m (S 0 r) x)
        (fun k x => iteratedFDeriv ℝ m (fun y => S (k + 1) r y - S k r y) x)
        (hyp.CP * B * Real.exp (lam * (t - r))) (fun k x => hbd k r hr m hm x)).1
      have e : (fun n x => iteratedFDeriv ℝ m (S n r) x) = fun n x => iteratedFDeriv ℝ m (S 0 r) x +
          ∑ k ∈ Finset.range n, iteratedFDeriv ℝ m (fun y => S (k + 1) r y - S k r y) x := by
        funext n x; exact htel n r hr m hm x
      rw [e]; exact h
    have hj := s104c3_jets_limit (N := j + 1) (fn := fun n => S n r) (f := w r)
      (q := fun m x => iteratedFDeriv ℝ m (S 0 r) x +
          ∑' k, iteratedFDeriv ℝ m (fun y => S (k + 1) r y - S k r y) x)
      (fun n => hseqcd n r hr) hlimj hval
    refine ⟨hj.1, fun m hm x => ?_, hval⟩
    rw [hj.2 m hm x]
    exact (hlimj m hm).tendsto_at x
  have hwcd : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (w r) := fun r hr => (hper r hr).1
  -- the differences `S (K+n) - S n` are in `HolB`
  have hV : ∀ n, ∀ r ∈ Icc 0 t, ∀ K : ℕ, HolB j η
      (hyp.CP * B * ((1 / 2) ^ n - (1 / 2) ^ (K + n)) * Real.exp (lam * (t - r)))
      (fun x => S (K + n) r x - S n r x) := by
    intro n r hr K
    induction K with
    | zero =>
      have : (fun x => S (0 + n) r x - S n r x) = fun _ => (0 : ℝ) := by
        funext x; simp
      rw [this]
      exact s104c3_HolB_zero (by simp)
    | succ K ih =>
      have h := s104c3_HolB_add ih (((props (K + n)).2.2.2 r hr))
      have e : (fun x => (S (K + n + 1) r x - S (K + n) r x) + (S (K + n) r x - S n r x)) =
          fun x => S (K + 1 + n) r x - S n r x := by
        funext x
        have : K + 1 + n = K + n + 1 := by omega
        rw [this]; ring
      rw [e] at h
      refine h.mono_B (le_of_eq ?_) hη0.le
      have : K + 1 + n = K + n + 1 := by omega
      rw [this]; ring
  -- the limit differences
  have hdiff : ∀ r ∈ Icc 0 t, ∀ n : ℕ, HolB j η
      (hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r))) (fun x => w r x - S n r x) := by
    intro r hr n
    refine s104c3_HolB_of_tendsto (fK := fun K x => S (K + n) r x - S n r x) ?_ ?_ ?_
    · exact (hwcd r hr).sub (hseqcd n r hr)
    · intro m hm x
      have h1 : Tendsto (fun K => iteratedFDeriv ℝ m (S (K + n) r) x) atTop
          (𝓝 (iteratedFDeriv ℝ m (w r) x)) :=
        ((hper r hr).2.1 m hm x).comp (tendsto_add_atTop_nat n)
      have hlin : ∀ (g : Euc d → ℝ), ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g →
          iteratedFDeriv ℝ m (fun y => g y - S n r y) x =
            (-1 : ℝ) • iteratedFDeriv ℝ m (S n r) x + iteratedFDeriv ℝ m g x := by
        intro g hg
        have e : (fun y => g y - S n r y) = fun y => -1 * S n r y + g y := by funext y; ring
        rw [e]; exact s104c3_jets_lin_apply (-1) (hseqcd n r hr) hg hm x
      have h2 : ∀ K, iteratedFDeriv ℝ m (fun y => S (K + n) r y - S n r y) x =
          (-1 : ℝ) • iteratedFDeriv ℝ m (S n r) x + iteratedFDeriv ℝ m (S (K + n) r) x :=
        fun K => hlin _ (hseqcd _ r hr)
      simp only [h2, hlin (w r) (hwcd r hr)]
      exact tendsto_const_nhds.add h1
    · intro K
      refine (hV n r hr K).mono_B ?_ hη0.le
      have h0 : 0 ≤ hyp.CP * B * Real.exp (lam * (t - r)) :=
        mul_nonneg (mul_nonneg hCP.le hB) (hE0 r).le
      have : (0 : ℝ) ≤ (1 / 2) ^ (K + n) := by positivity
      nlinarith
  -- bound for the limit
  have hbound : ∀ r ∈ Icc 0 t, HolB j η (2 * hyp.CP * B * Real.exp (lam * (t - r))) (w r) := by
    intro r hr
    refine s104c3_HolB_of_tendsto (fK := fun K => S K r) (hwcd r hr)
      (fun m hm x => (hper r hr).2.1 m hm x) (fun K => ?_)
    refine ((props K).1 r hr).mono_B ?_ hη0.le
    have h0 : 0 ≤ hyp.CP * B * Real.exp (lam * (t - r)) :=
      mul_nonneg (mul_nonneg hCP.le hB) (hE0 r).le
    have : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
    nlinarith
  -- jets of the difference
  have hjetdiff : ∀ r ∈ Icc 0 t, ∀ n : ℕ, ∀ i ≤ j + 1, ∀ x,
      ‖iteratedFDeriv ℝ i (w r) x - iteratedFDeriv ℝ i (S n r) x‖ ≤
        hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r)) := by
    intro r hr n i hi x
    have h := (hdiff r hr n).1.2 i hi x
    have e : (fun y => w r y - S n r y) = fun y => -1 * S n r y + w r y := by funext y; ring
    rw [e, s104c3_jets_lin_apply (-1) (hseqcd n r hr) (hwcd r hr) hi x] at h
    have e2 : (-1 : ℝ) • iteratedFDeriv ℝ i (S n r) x + iteratedFDeriv ℝ i (w r) x =
        iteratedFDeriv ℝ i (w r) x - iteratedFDeriv ℝ i (S n r) x := by
      rw [neg_one_smul]; abel
    rwa [e2] at h
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ r ∈ Icc 0 t,
      hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r)) ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := ε / (hyp.CP * B * Real.exp (lam * t) + 1))
      (y := (1 / 2 : ℝ)) (by positivity) (by norm_num)
    refine ⟨n, fun r hr => ?_⟩
    have hex : Real.exp (lam * (t - r)) ≤ Real.exp (lam * t) :=
      Real.exp_le_exp.2 (by nlinarith [hr.1])
    have h0 : 0 ≤ hyp.CP * B := mul_nonneg hCP.le hB
    have h1 : hyp.CP * B * (1 / 2) ^ n * Real.exp (lam * (t - r)) ≤
        (1 / 2) ^ n * (hyp.CP * B * Real.exp (lam * t)) := by
      have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
      nlinarith [mul_nonneg h0 this]
    refine h1.trans ?_
    have hpos : 0 < hyp.CP * B * Real.exp (lam * t) + 1 := by positivity
    rw [lt_div_iff₀ hpos] at hn
    have : 0 ≤ hyp.CP * B * Real.exp (lam * t) := mul_nonneg h0 (Real.exp_pos _).le
    nlinarith
  refine ⟨w, hbound, hdiff, ?_, ?_, fun r hr x => (hper r hr).2.2 x⟩
  · refine s104c3_TC_of_unif (fn := S) (fun n => (props n).2.1) ?_
    intro i hi ε hε
    obtain ⟨n, hn⟩ := hsmall ε hε
    exact ⟨n, fun r hr x => (hjetdiff r hr n i hi x).trans (hn r hr)⟩
  · intro r hr
    refine s104c3_VanB_of_unif (fn := fun n => S n r) (fun n => (props n).2.2.1 r hr) ?_
    intro i hi ε hε
    obtain ⟨n, hn⟩ := hsmall ε hε
    exact ⟨n, fun x => (hjetdiff r hr n i hi x).trans (hn r hr)⟩

end HRS.MS.S104e.C
