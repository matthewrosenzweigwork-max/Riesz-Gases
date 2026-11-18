import HRS.MS.S104eC3B

/-!
# S104E route C, packet C3, file C: the structure `VolHyp`, the Duhamel operator, linearity lemmas

`VolHyp` extends the skeleton structure (see the changelog in `HANDOFF_S104C3.md`):
* `P_cont` is now jet-valued (all `i ≤ j+1`), `A_cont` is replaced by the family version `A_jc`; new `P_jc`;
* vanishing at infinity: `P_van`, `P_vgain`, `A_van`; strong continuity `P_strong`; time continuity of the
  perturbation `A_tc` (these are the interface items requested by the orchestrator for C5).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Interval

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL

variable {d : ℕ}

/-- Uniform (in `x`) time continuity of the jets of order `≤ N` of a family `u r` on `[0,t]`. -/
def s104c3_TC (t : ℝ) (N : ℕ) (u : ℝ → Euc d → ℝ) : Prop :=
  ∀ i ≤ N, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc 0 t, ∀ r' ∈ Icc 0 t, |r - r'| < δ →
    ∀ x : Euc d, ‖iteratedFDeriv ℝ i (u r) x - iteratedFDeriv ℝ i (u r') x‖ ≤ ε

/-- Abstract hypotheses on the semigroup part `P h` and the perturbation `A v` (instantiated in C5 by the OU semigroup and
`s103bQ`). -/
structure VolHyp (d : ℕ) (j : ℕ) (η H : ℝ) (P : ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (A : ℝ → (Euc d → ℝ) → Euc d → ℝ) where
  CP : ℝ
  CA : ℝ
  CP1 : 1 ≤ CP
  CA0 : 0 ≤ CA
  P_zero : ∀ f, P 0 f = f
  P_lin : ∀ h, 0 ≤ h → ∀ (c B B' : ℝ) (f g : Euc d → ℝ), Bd 0 B f → Bd 0 B' g →
    P h (fun x => c * f x + g x) = fun x => c * P h f x + P h g x
  A_lin : ∀ v, v ∈ Icc 0 H → ∀ (c B B' : ℝ) (f g : Euc d → ℝ), HolB j η B f → HolB j η B' g →
    A v (fun x => c * f x + g x) = fun x => c * A v f x + A v g x
  P_stab : ∀ h, 0 ≤ h → h ≤ H → ∀ B f, HolB j η B f → HolB j η (CP * B) (P h f)
  P_gain : ∀ h, 0 < h → h ≤ H → ∀ B f, Bd j B f → HolB j η (CP * (1 + h ^ (-((1 + η) / 2))) * B) (P h f)
  A_bd : ∀ v, v ∈ Icc 0 H → ∀ B f, HolB j η B f → Bd j (CA * B) (A v f)
  /-- jointly continuous jets of `(h,x) ↦ P_h f` for `f ∈ HolB` (`h = 0` included). -/
  P_cont : ∀ B f, HolB j η B f → ∀ i ≤ j + 1,
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (P p.1 f) p.2) (Icc 0 H ×ˢ univ)
  /-- joint continuity of `(h, v, x) ↦ D^i (P_h g_v)(x)` for `h > 0`, for a continuous bounded family `g_v ∈ Bd j`. -/
  P_jc : ∀ t ∈ Icc 0 H, ∀ (B : ℝ) (G : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, Bd j B (G v)) →
    (∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) →
    ∀ i ≤ j + 1, ContinuousOn
      (fun q : ℝ × ℝ × Euc d => iteratedFDeriv ℝ i (P q.1 (G q.2.1)) q.2.2) (Ioc 0 H ×ˢ Icc 0 t ×ˢ univ)
  /-- joint continuity of the jets (`≤ j`) of `(v,x) ↦ A_v f_v (x)` for a family `f_v` with jointly continuous jets (`≤ j+1`). -/
  A_jc : ∀ t ∈ Icc 0 H, ∀ (B : ℝ) (G : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, HolB j η B (G v)) →
    (∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) →
    ∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (A p.1 (G p.1)) p.2) (Icc 0 t ×ˢ univ)
  /-- `P_h` preserves vanishing of the `j+1` jets of a `HolB` function. -/
  P_van : ∀ h, 0 ≤ h → h ≤ H → ∀ B f, HolB j η B f → VanB (j + 1) f → VanB (j + 1) (P h f)
  /-- smoothing preserves vanishing: `h > 0`, `g ∈ Bd j`, jets `≤ j` vanishing give vanishing jets `≤ j+1`. -/
  P_vgain : ∀ h, 0 < h → h ≤ H → ∀ B f, Bd j B f → VanB j f → VanB (j + 1) (P h f)
  /-- uniform strong continuity in `h` of the jets (`≤ j+1`) for data in `HolB ∩ VanB (j+1)`. -/
  P_strong : ∀ B f, HolB j η B f → VanB (j + 1) f → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ h ∈ Icc 0 H, ∀ h' ∈ Icc 0 H, |h - h'| < δ → ∀ i ≤ j + 1, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (P h f) x - iteratedFDeriv ℝ i (P h' f) x‖ ≤ ε
  A_van : ∀ v, v ∈ Icc 0 H → ∀ B f, HolB j η B f → VanB (j + 1) f → VanB j (A v f)
  /-- time continuity of `v ↦ A_v u_v` in the sup norm of the jets `≤ j`, from that of `u_v` in the jets `≤ j+1`. -/
  A_tc : ∀ t ∈ Icc 0 H, ∀ (B : ℝ) (u : ℝ → Euc d → ℝ), (∀ v ∈ Icc 0 t, HolB j η B (u v)) →
    s104c3_TC t (j + 1) u → s104c3_TC t j (fun v => A v (u v))

variable {j : ℕ} {η H : ℝ} {P A : ℝ → (Euc d → ℝ) → Euc d → ℝ}

/-- The Duhamel operator `Φ u (r) (x) = ∫_r^t P_{v-r} A_v u_v (x) dv`. -/
def s104c3_Phi (P A : ℝ → (Euc d → ℝ) → Euc d → ℝ) (t : ℝ) (u : ℝ → Euc d → ℝ) (r : ℝ) (x : Euc d) : ℝ :=
  ∫ v in r..t, P (v - r) (A v (u v)) x

/-- The contraction constant. -/
def s104c3_theta (hyp : VolHyp d j η H P A) (lam : ℝ) : ℝ :=
  hyp.CP * hyp.CA * ∫ h in (0 : ℝ)..H, s104c3_k η h * Real.exp (-lam * h)

theorem s104c3_theta_nonneg (hyp : VolHyp d j η H P A) (hH : 0 ≤ H) (hη1 : η < 1) (hη0 : 0 < η) (lam : ℝ) :
    0 ≤ s104c3_theta hyp lam := by
  have hCP : 0 ≤ hyp.CP := by linarith [hyp.CP1]
  refine mul_nonneg (mul_nonneg hCP hyp.CA0) (intervalIntegral.integral_nonneg hH fun h hh => ?_)
  exact mul_nonneg (s104c3_k_nonneg η hh.1) (Real.exp_pos _).le

/-- Linearity of `h ↦ P h (A v ·)` on differences. -/
theorem VolHyp.PA_sub (hyp : VolHyp d j η H P A) {v h : ℝ} (hv : v ∈ Icc 0 H) (hh : 0 ≤ h) {B B' : ℝ}
    {f g : Euc d → ℝ} (hf : HolB j η B f) (hg : HolB j η B' g) (x : Euc d) :
    P h (A v (fun y => g y - f y)) x = P h (A v g) x - P h (A v f) x := by
  have hA := hyp.A_lin v hv (-1) B B' f g hf hg
  have e : (fun y => g y - f y) = fun y => -1 * f y + g y := by funext y; ring
  rw [e, hA]
  have hP := hyp.P_lin h hh (-1) _ _ (A v f) (A v g) (s104c3_Bd_zero_of (hyp.A_bd v hv _ _ hf))
    (s104c3_Bd_zero_of (hyp.A_bd v hv _ _ hg))
  rw [hP]
  ring

/-- Linearity of `h ↦ P h (A v ·)` on sums with coefficient. -/
theorem VolHyp.PA_lin (hyp : VolHyp d j η H P A) {v h : ℝ} (hv : v ∈ Icc 0 H) (hh : 0 ≤ h) {B B' : ℝ}
    {f g : Euc d → ℝ} (hf : HolB j η B f) (hg : HolB j η B' g) (c : ℝ) (x : Euc d) :
    P h (A v (fun y => c * f y + g y)) x = c * P h (A v f) x + P h (A v g) x := by
  have hA := hyp.A_lin v hv c B B' f g hf hg
  rw [hA]
  have hP := hyp.P_lin h hh c _ _ (A v f) (A v g) (s104c3_Bd_zero_of (hyp.A_bd v hv _ _ hf))
    (s104c3_Bd_zero_of (hyp.A_bd v hv _ _ hg))
  rw [hP]

/-! ## Jets of linear combinations of families -/

theorem s104c3_jets_lin {t : ℝ} {N : ℕ} {u u' : ℝ → Euc d → ℝ} (c : ℝ)
    (hu : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u r))
    (hu' : ∀ r ∈ Icc 0 t, ContDiff ℝ (N : WithTop ℕ∞) (u' r))
    (huc : ∀ i ≤ N, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u p.1) p.2) (Icc 0 t ×ˢ univ))
    (huc' : ∀ i ≤ N, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (u' p.1) p.2) (Icc 0 t ×ˢ univ)) :
    ∀ i ≤ N, ContinuousOn
      (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (fun x => c * u p.1 x + u' p.1 x) p.2) (Icc 0 t ×ˢ univ) := by
  intro i hi
  have h := ((huc i hi).const_smul c).add (huc' i hi)
  refine h.congr fun p hp => ?_
  rw [s104c3_jets_lin_apply c (hu p.1 hp.1) (hu' p.1 hp.1) hi p.2]
  rfl

end HRS.MS.S104e.C
