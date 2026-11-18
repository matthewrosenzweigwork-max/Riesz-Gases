import HRS.MS.S104eC3G

/-!
# S104E route C, packet C3, file H: the Picard iterates and their uniform bounds

`seq 0 r = P_{t-r} ψ`, `seq (n+1) r = P_{t-r} ψ + Φ(seq n) r`.  With `θ(λ) ≤ 1/2` we prove by induction
`seq n r ∈ HolB (CP B (2 - 2^{-n}) e^{λ(t-r)})`, `seq (n+1) - seq n ∈ HolB (CP B 2^{-(n+1)} e^{λ(t-r)})`,
vanishing of jets at infinity and uniform time continuity.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ} {j : ℕ} {η H : ℝ} {P A : ℝ → (Euc d → ℝ) → Euc d → ℝ}

/-- The Picard iterates. -/
def s104c3_seq (P A : ℝ → (Euc d → ℝ) → Euc d → ℝ) (t : ℝ) (ψ : Euc d → ℝ) : ℕ → ℝ → Euc d → ℝ
  | 0 => fun r x => P (t - r) ψ x
  | n + 1 => fun r x => P (t - r) ψ x + s104c3_Phi P A t (s104c3_seq P A t ψ n) r x

theorem s104c3_seq_zero (t : ℝ) (ψ : Euc d → ℝ) : s104c3_seq P A t ψ 0 = fun r x => P (t - r) ψ x := rfl

theorem s104c3_seq_succ (t : ℝ) (ψ : Euc d → ℝ) (n : ℕ) :
    s104c3_seq P A t ψ (n + 1) =
      fun r x => P (t - r) ψ x + s104c3_Phi P A t (s104c3_seq P A t ψ n) r x := rfl

/-- Linearity of the Duhamel operator (on differences of admissible families). -/
theorem s104c3_phi_sub (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {N N' lam : ℝ} (hlam : 0 ≤ lam) {u u' : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    (hu' : ∀ v ∈ Icc 0 t, HolB j η (N' * Real.exp (lam * (t - v))) (u' v))
    (huc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2)
      (Icc 0 t ×ˢ univ))
    (huc' : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u' p.1) p.2)
      (Icc 0 t ×ˢ univ)) {r : ℝ} (hr : r ∈ Icc 0 t) (x : Euc d) :
    s104c3_Phi P A t (fun v y => u' v y - u v y) r x =
      s104c3_Phi P A t u' r x - s104c3_Phi P A t u r x := by
  have h1 := (s104c3_duhamel hyp hη0 hη1 ht hlam hu huc r hr).1 x
  have h2 := (s104c3_duhamel hyp hη0 hη1 ht hlam hu' huc' r hr).1 x
  unfold s104c3_Phi
  rw [← intervalIntegral.integral_sub h2 h1]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le hr.2] at hv
  have hvt : v ∈ Icc 0 t := ⟨hr.1.trans hv.1, hv.2⟩
  exact hyp.PA_sub (f := u v) (g := u' v) ⟨hvt.1, hvt.2.trans ht.2⟩ (by linarith [hv.1])
    (hu v hvt) (hu' v hvt) x

/-- One Picard step halves the bound. -/
theorem s104c3_halve (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {lam : ℝ} (hlam : 0 ≤ lam) (hθ : s104c3_theta hyp lam ≤ 1 / 2) {N : ℝ}
    (hN : 0 ≤ N) {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc 0 t, HolB j η (N * Real.exp (lam * (t - v))) (u v))
    (huc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2)
      (Icc 0 t ×ˢ univ)) :
    ∀ r ∈ Icc 0 t, HolB j η (1 / 2 * N * Real.exp (lam * (t - r))) (s104c3_Phi P A t u r) := by
  intro r hr
  have h := (s104c3_duhamel hyp hη0 hη1 ht hlam hu huc r hr).2.2.2
  refine h.mono_B ?_ hη0.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθ hN) (Real.exp_pos _).le

/-- The free term `r ↦ P_{t-r} ψ`. -/
theorem s104c3_base (hyp : VolHyp d j η H P A) {t : ℝ} (ht : t ∈ Icc 0 H) {B : ℝ} {ψ : Euc d → ℝ}
    (hψ : HolB j η B ψ) (hψv : VanB (j + 1) ψ) :
    (∀ r ∈ Icc 0 t, HolB j η (hyp.CP * B) (P (t - r) ψ)) ∧
    (∀ r ∈ Icc 0 t, VanB (j + 1) (P (t - r) ψ)) ∧
    s104c3_TC t (j + 1) (fun r => P (t - r) ψ) := by
  refine ⟨fun r hr => hyp.P_stab (t - r) (by linarith [hr.2]) (by linarith [hr.1, ht.2]) _ _ hψ,
    fun r hr => hyp.P_van (t - r) (by linarith [hr.2]) (by linarith [hr.1, ht.2]) _ _ hψ hψv, ?_⟩
  intro i hi ε hε
  obtain ⟨δ, hδ, h⟩ := hyp.P_strong B ψ hψ hψv ε hε
  refine ⟨δ, hδ, fun r hr r' hr' hrr x => ?_⟩
  exact h (t - r) ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩ (t - r')
    ⟨by linarith [hr'.2], by linarith [hr'.1, ht.2]⟩
    (by rw [show t - r - (t - r') = -(r - r') by ring, abs_neg]; exact hrr) i hi x

theorem s104c3_TC_add {t : ℝ} {N : ℕ} {u u' : ℝ → Euc d → ℝ}
    (hu : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u r))
    (hu' : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u' r))
    (h : s104c3_TC t N u) (h' : s104c3_TC t N u') : s104c3_TC t N (fun r x => u r x + u' r x) := by
  have := s104c3_TC_lin 1 hu hu' h h'
  simpa using this

theorem s104c3_VanB_add {N : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ (N : WithTop ℕ∞) f)
    (hg : ContDiff ℝ (N : WithTop ℕ∞) g) (h1 : VanB N f) (h2 : VanB N g) :
    VanB N (fun x => f x + g x) := by
  have := s104c3_VanB_lin 1 hf hg h1 h2
  simpa using this

/-- Inductive properties of the iterates. -/
theorem s104c3_seq_props (hyp : VolHyp d j η H P A) (hη0 : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 H) {lam : ℝ} (hlam : 0 ≤ lam) (hθ : s104c3_theta hyp lam ≤ 1 / 2) {B : ℝ}
    {ψ : Euc d → ℝ} (hψ : HolB j η B ψ) (hψv : VanB (j + 1) ψ) :
    ∀ n : ℕ,
      (∀ r ∈ Icc 0 t, HolB j η (hyp.CP * B * (2 - (1 / 2) ^ n) * Real.exp (lam * (t - r)))
        (s104c3_seq P A t ψ n r)) ∧
      s104c3_TC t (j + 1) (s104c3_seq P A t ψ n) ∧
      (∀ r ∈ Icc 0 t, VanB (j + 1) (s104c3_seq P A t ψ n r)) ∧
      (∀ r ∈ Icc 0 t, HolB j η (hyp.CP * B * (1 / 2) ^ (n + 1) * Real.exp (lam * (t - r)))
        (fun x => s104c3_seq P A t ψ (n + 1) r x - s104c3_seq P A t ψ n r x)) := by
  have hCP : 0 < hyp.CP := by linarith [hyp.CP1]
  have hB : 0 ≤ B := s104c3_HolB_nonneg hψ
  have hbase := s104c3_base hyp ht hψ hψv
  have hE1 : ∀ r ∈ Icc 0 t, 1 ≤ Real.exp (lam * (t - r)) := fun r hr =>
    Real.one_le_exp (mul_nonneg hlam (by linarith [hr.2]))
  have hE0 : ∀ r, 0 < Real.exp (lam * (t - r)) := fun r => Real.exp_pos _
  -- uniform form of the hypothesis for the Duhamel estimate
  have hu2 : ∀ n : ℕ, (∀ r ∈ Icc 0 t, HolB j η (hyp.CP * B * (2 - (1 / 2) ^ n) * Real.exp (lam * (t - r)))
        (s104c3_seq P A t ψ n r)) → ∀ r ∈ Icc 0 t,
        HolB j η ((2 * (hyp.CP * B)) * Real.exp (lam * (t - r))) (s104c3_seq P A t ψ n r) := by
    intro n h r hr
    refine (h r hr).mono_B ?_ hη0.le
    have : (1 / 2 : ℝ) ^ n ≥ 0 := by positivity
    have h0 : 0 ≤ hyp.CP * B := mul_nonneg hCP.le hB
    nlinarith [hE0 r, mul_nonneg h0 this, mul_nonneg (mul_nonneg h0 this) (hE0 r).le]
  intro n
  induction n with
  | zero =>
    have hQ : ∀ r ∈ Icc 0 t, HolB j η (hyp.CP * B * (2 - (1 / 2) ^ 0) * Real.exp (lam * (t - r)))
        (s104c3_seq P A t ψ 0 r) := by
      intro r hr
      refine (hbase.1 r hr).mono_B ?_ hη0.le
      have h0 : 0 ≤ hyp.CP * B := mul_nonneg hCP.le hB
      have := hE1 r hr
      norm_num
      nlinarith
    have hTC : s104c3_TC t (j + 1) (s104c3_seq P A t ψ 0) := hbase.2.2
    have hV : ∀ r ∈ Icc 0 t, VanB (j + 1) (s104c3_seq P A t ψ 0 r) := hbase.2.1
    refine ⟨hQ, hTC, hV, ?_⟩
    have hcd : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s104c3_seq P A t ψ 0 r) :=
      fun r hr => (hQ r hr).1.1
    have huc := s104c3_jets_cont_of_TC hTC hcd
    have hu : ∀ v ∈ Icc 0 t, HolB j η ((hyp.CP * B) * Real.exp (lam * (t - v))) (s104c3_seq P A t ψ 0 v) := by
      intro v hv
      refine (hQ v hv).mono_B ?_ hη0.le
      norm_num
    have := s104c3_halve hyp hη0 hη1 ht hlam hθ (mul_nonneg hCP.le hB) hu huc
    intro r hr
    have e : (fun x => s104c3_seq P A t ψ (0 + 1) r x - s104c3_seq P A t ψ 0 r x) =
        s104c3_Phi P A t (s104c3_seq P A t ψ 0) r := by
      funext x; simp [s104c3_seq]
    rw [e]
    refine (this r hr).mono_B (le_of_eq ?_) hη0.le
    ring
  | succ n ih =>
    obtain ⟨hQ, hTC, hV, hR⟩ := ih
    have hcd : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s104c3_seq P A t ψ n r) :=
      fun r hr => (hQ r hr).1.1
    have huc := s104c3_jets_cont_of_TC hTC hcd
    have hu := hu2 n hQ
    have hN2 : 0 ≤ 2 * (hyp.CP * B) := by positivity
    have hD := fun r hr => s104c3_duhamel hyp hη0 hη1 ht hlam hu huc r hr
    -- TC, vanishing of the next iterate
    have hcdP : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (P (t - r) ψ) :=
      fun r hr => (hbase.1 r hr).1.1
    have hcdΦ : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
        (s104c3_Phi P A t (s104c3_seq P A t ψ n) r) := fun r hr => (hD r hr).2.1
    have hTC' : s104c3_TC t (j + 1) (s104c3_seq P A t ψ (n + 1)) :=
      s104c3_TC_add hcdP hcdΦ hbase.2.2 (s104c3_phi_TC hyp hη0 hη1 ht hlam hu huc hTC)
    have hV' : ∀ r ∈ Icc 0 t, VanB (j + 1) (s104c3_seq P A t ψ (n + 1) r) := fun r hr =>
      s104c3_VanB_add (hcdP r hr) (hcdΦ r hr) (hbase.2.1 r hr)
        (s104c3_phi_van hyp hη0 hη1 ht hlam hu huc hV r hr)
    have hQ' : ∀ r ∈ Icc 0 t, HolB j η (hyp.CP * B * (2 - (1 / 2) ^ (n + 1)) * Real.exp (lam * (t - r)))
        (s104c3_seq P A t ψ (n + 1) r) := by
      intro r hr
      have h := s104c3_HolB_add (hQ r hr) (hR r hr)
      have e : (fun x => s104c3_seq P A t ψ (n + 1) r x - s104c3_seq P A t ψ n r x +
          s104c3_seq P A t ψ n r x) = s104c3_seq P A t ψ (n + 1) r := by funext x; ring
      rw [e] at h
      refine h.mono_B (le_of_eq ?_) hη0.le
      ring
    refine ⟨hQ', hTC', hV', ?_⟩
    -- the next difference is `Φ` of the previous one
    have hcd' : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s104c3_seq P A t ψ (n + 1) r) :=
      fun r hr => (hQ' r hr).1.1
    have huc' := s104c3_jets_cont_of_TC hTC' hcd'
    have hu' := hu2 (n + 1) hQ'
    have hdcd : ∀ r ∈ Icc 0 t, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
        (fun x => s104c3_seq P A t ψ (n + 1) r x - s104c3_seq P A t ψ n r x) := fun r hr => (hR r hr).1.1
    have hTCd : s104c3_TC t (j + 1) (fun r x => s104c3_seq P A t ψ (n + 1) r x - s104c3_seq P A t ψ n r x) := by
      have e : (fun r x => s104c3_seq P A t ψ (n + 1) r x - s104c3_seq P A t ψ n r x) =
          fun r x => -1 * s104c3_seq P A t ψ n r x + s104c3_seq P A t ψ (n + 1) r x := by
        funext r x; ring
      rw [e]
      exact s104c3_TC_lin (-1) hcd hcd' hTC hTC'
    have hdc := s104c3_jets_cont_of_TC hTCd hdcd
    have hN3 : 0 ≤ hyp.CP * B * (1 / 2) ^ (n + 1) := by positivity
    have hhalf := s104c3_halve hyp hη0 hη1 ht hlam hθ hN3 hR hdc
    intro r hr
    have e : (fun x => s104c3_seq P A t ψ (n + 1 + 1) r x - s104c3_seq P A t ψ (n + 1) r x) =
        s104c3_Phi P A t (fun v y => s104c3_seq P A t ψ (n + 1) v y - s104c3_seq P A t ψ n v y) r := by
      funext x
      rw [s104c3_phi_sub hyp hη0 hη1 ht hlam hu hu' huc huc' hr x]
      simp [s104c3_seq]
    rw [e]
    refine (hhalf r hr).mono_B (le_of_eq ?_) hη0.le
    ring

end HRS.MS.S104e.C
