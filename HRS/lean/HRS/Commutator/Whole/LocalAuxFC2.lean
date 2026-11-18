import HRS.Commutator.Whole.LocalAuxFC
import HRS.Commutator.Whole.ApproxAux

/-!
# CMX-FC auxiliary: smoothness and bounded derivatives of `ψ * K`

For a kernel `K : ℝ^d → ℝ^d` that is locally integrable and bounded away from the origin
(`cmxFB_KerOK`) and a Schwartz function `φ`, the map `x ↦ ∫ B(φ(x-y))(K y) dy` is smooth with all
derivatives bounded (differentiation under the integral sign, by induction on the order).
Names prefixed `cmxFB_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- Hypotheses on the kernel: measurable, integrable on the open unit ball, bounded outside. -/
structure cmxFB_KerOK (K : Euc d → Euc d) : Prop where
  meas : AEStronglyMeasurable K volume
  loc : IntegrableOn K (ball (0 : Euc d) 1)
  far : ∃ M : ℝ, ∀ y : Euc d, 1 ≤ ‖y‖ → ‖K y‖ ≤ M

/-- The weight `(1+|z|)^{-(d+1)}`. -/
def cmxFB_a (d : ℕ) (z : Euc d) : ℝ := ((1 + ‖z‖) ^ (d + 1))⁻¹

theorem cmxFB_a_pos (z : Euc d) : 0 < cmxFB_a d z := by unfold cmxFB_a; positivity

theorem cmxFB_a_le_one (z : Euc d) : cmxFB_a d z ≤ 1 := by
  unfold cmxFB_a
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg z])

theorem cmxFB_a_integrable : Integrable (cmxFB_a d) :=
  cmxFB_integrable_inv_pow (d := d) (d + 1) (by omega)

theorem cmxFB_a_shift (x x0 y : Euc d) (h : ‖x - x0‖ ≤ 1) :
    cmxFB_a d (x - y) ≤ 2 ^ (d + 1) * cmxFB_a d (x0 - y) := by
  unfold cmxFB_a
  have h1 : 1 + ‖x0 - y‖ ≤ 2 * (1 + ‖x - y‖) := by
    have : ‖x0 - y‖ ≤ ‖x0 - x‖ + ‖x - y‖ := by
      calc ‖x0 - y‖ = ‖(x0 - x) + (x - y)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖x0 - x‖ ≤ 1 := by rw [norm_sub_rev]; exact h
    nlinarith [norm_nonneg (x - y)]
  have hP : 0 < (1 + ‖x - y‖) ^ (d + 1) := by positivity
  have hQ : 0 < (1 + ‖x0 - y‖) ^ (d + 1) := by positivity
  have h3 : (1 + ‖x0 - y‖) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + ‖x - y‖) ^ (d + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hP hQ]
  linarith

theorem cmxFB_decay_gen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : SchwartzMap (Euc d) V) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d, (1 + ‖x‖) ^ N * ‖φ x‖ ≤ C := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ,
    mul_nonneg (by positivity) (apply_nonneg _ _), fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0)
    le_rfl le_rfl φ x
  simpa using this

theorem cmxFB_schwartz_a {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : SchwartzMap (Euc d) V) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, ‖φ z‖ ≤ C * cmxFB_a d z := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_decay_gen φ (d + 1)
  refine ⟨C, hC0, fun z => ?_⟩
  unfold cmxFB_a
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [hC z]

/-- The dominating function. -/
def cmxFB_bd (K : Euc d → Euc d) (C c2 : ℝ) (x0 y : Euc d) : ℝ :=
  C * (ball (0 : Euc d) 1).indicator (fun y => ‖K y‖) y + c2 * cmxFB_a d (x0 - y)

theorem cmxFB_bd_integrable {K : Euc d → Euc d} (hK : cmxFB_KerOK K) (C c2 : ℝ) (x0 : Euc d) :
    Integrable (cmxFB_bd K C c2 x0) := by
  unfold cmxFB_bd
  refine Integrable.add (Integrable.const_mul ?_ C) (Integrable.const_mul ?_ c2)
  · exact (integrable_indicator_iff measurableSet_ball).2 hK.loc.norm
  · exact cmxFB_a_integrable.comp_sub_left x0

theorem cmxFB_bd_integral {K : Euc d → Euc d} (hK : cmxFB_KerOK K) (C c2 : ℝ) (x0 : Euc d) :
    ∫ y, cmxFB_bd K C c2 x0 y =
      C * (∫ y in ball (0 : Euc d) 1, ‖K y‖) + c2 * (∫ y, cmxFB_a d y) := by
  unfold cmxFB_bd
  rw [integral_add (Integrable.const_mul ((integrable_indicator_iff measurableSet_ball).2
      hK.loc.norm) C) (Integrable.const_mul (cmxFB_a_integrable.comp_sub_left x0) c2),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_ball]
  rw [integral_sub_left_eq_self (cmxFB_a d) volume x0]

theorem cmxFB_dom {K : Euc d → Euc d} (hK : cmxFB_KerOK K) {V : Type} [NormedAddCommGroup V]
    (h : Euc d → V) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ z, ‖h z‖ ≤ C * cmxFB_a d z) :
    ∃ c2 : ℝ, ∀ x x0 : Euc d, ‖x - x0‖ ≤ 1 → ∀ y : Euc d,
      ‖h (x - y)‖ * ‖K y‖ ≤ cmxFB_bd K C c2 x0 y := by
  obtain ⟨M, hM⟩ := hK.far
  refine ⟨C * max M 0 * 2 ^ (d + 1), fun x x0 hx y => ?_⟩
  unfold cmxFB_bd
  have ha0 := cmxFB_a_pos (d := d) (x0 - y)
  have hc2 : 0 ≤ C * max M 0 * 2 ^ (d + 1) := by positivity
  by_cases hy : y ∈ ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hy]
    have h1 : ‖h (x - y)‖ ≤ C := by
      calc ‖h (x - y)‖ ≤ C * cmxFB_a d (x - y) := hh _
        _ ≤ C * 1 := by gcongr; exact cmxFB_a_le_one _
        _ = C := mul_one C
    have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (K y))
    nlinarith [mul_nonneg hc2 ha0.le]
  · rw [Set.indicator_of_notMem hy]
    have hy1 : 1 ≤ ‖y‖ := by
      simpa [mem_ball_zero_iff] using hy
    have hKy : ‖K y‖ ≤ max M 0 := (hM y hy1).trans (le_max_left _ _)
    have h1 : ‖h (x - y)‖ ≤ C * (2 ^ (d + 1) * cmxFB_a d (x0 - y)) :=
      (hh _).trans (mul_le_mul_of_nonneg_left (cmxFB_a_shift x x0 y hx) hC)
    calc ‖h (x - y)‖ * ‖K y‖ ≤ (C * (2 ^ (d + 1) * cmxFB_a d (x0 - y))) * max M 0 :=
          mul_le_mul h1 hKy (norm_nonneg _) (by positivity)
      _ = 0 + C * max M 0 * 2 ^ (d + 1) * cmxFB_a d (x0 - y) := by ring
      _ ≤ _ := by simp

/-! ### The convolution operator -/

section Phi

variable (K : Euc d → Euc d) {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- `Φ_{B,φ}(x) = ∫ B(φ(x-y))(K y) dy`. -/
def cmxFB_Phi (B : G →L[ℝ] Euc d →L[ℝ] H) (φ : SchwartzMap (Euc d) G) (x : Euc d) : H :=
  ∫ y, B (φ (x - y)) (K y)

/-- The bilinear map for the derivative: `B'(A)(w) = B(A ·)(w)`. -/
def cmxFB_B' (B : G →L[ℝ] Euc d →L[ℝ] H) : (Euc d →L[ℝ] G) →L[ℝ] Euc d →L[ℝ] (Euc d →L[ℝ] H) :=
  ((ContinuousLinearMap.compL ℝ (Euc d) G H).comp B.flip).flip

theorem cmxFB_B'_apply (B : G →L[ℝ] Euc d →L[ℝ] H) (A : Euc d →L[ℝ] G) (w : Euc d) :
    cmxFB_B' B A w = (B.flip w).comp A := rfl

theorem cmxFB_B'_norm_le (B : G →L[ℝ] Euc d →L[ℝ] H) (A : Euc d →L[ℝ] G) (w : Euc d) :
    ‖cmxFB_B' B A w‖ ≤ ‖B‖ * ‖A‖ * ‖w‖ := by
  rw [cmxFB_B'_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  calc ‖((B.flip w).comp A) h‖ = ‖B (A h) w‖ := rfl
    _ ≤ ‖B‖ * ‖A h‖ * ‖w‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (‖A‖ * ‖h‖) * ‖w‖ := by gcongr; exact A.le_opNorm h
    _ = ‖B‖ * ‖A‖ * ‖w‖ * ‖h‖ := by ring

variable {K}

theorem cmxFB_Phi_meas (hK : cmxFB_KerOK K) (B : G →L[ℝ] Euc d →L[ℝ] H)
    (φ : SchwartzMap (Euc d) G) (x : Euc d) :
    AEStronglyMeasurable (fun y => B (φ (x - y)) (K y)) volume := by
  have h1 : Continuous fun y : Euc d => φ (x - y) :=
    φ.continuous.comp (continuous_const.sub continuous_id)
  exact B.aestronglyMeasurable_comp₂ h1.aestronglyMeasurable hK.meas

theorem cmxFB_Phi_bound (hK : cmxFB_KerOK K) (B : G →L[ℝ] Euc d →L[ℝ] H)
    (φ : SchwartzMap (Euc d) G) :
    ∃ c2 C : ℝ, 0 ≤ C ∧ ∀ x x0 : Euc d, ‖x - x0‖ ≤ 1 → ∀ y : Euc d,
      ‖B (φ (x - y)) (K y)‖ ≤ ‖B‖ * cmxFB_bd K C c2 x0 y := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_schwartz_a φ
  obtain ⟨c2, hc2⟩ := cmxFB_dom hK (fun z => φ z) C hC0 hC
  refine ⟨c2, C, hC0, fun x x0 hx y => ?_⟩
  calc ‖B (φ (x - y)) (K y)‖ ≤ ‖B‖ * ‖φ (x - y)‖ * ‖K y‖ := B.le_opNorm₂ _ _
    _ = ‖B‖ * (‖φ (x - y)‖ * ‖K y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hc2 x x0 hx y) (by positivity)

theorem cmxFB_Phi_integrable (hK : cmxFB_KerOK K) (B : G →L[ℝ] Euc d →L[ℝ] H)
    (φ : SchwartzMap (Euc d) G) (x : Euc d) :
    Integrable (fun y => B (φ (x - y)) (K y)) := by
  obtain ⟨c2, C, hC0, hb⟩ := cmxFB_Phi_bound hK B φ
  refine ((cmxFB_bd_integrable hK C c2 x).const_mul ‖B‖).mono' (cmxFB_Phi_meas hK B φ x)
    (Eventually.of_forall fun y => hb x x (by simp) y)

theorem cmxFB_Phi_bdd [CompleteSpace H] (hK : cmxFB_KerOK K) (B : G →L[ℝ] Euc d →L[ℝ] H)
    (φ : SchwartzMap (Euc d) G) : ∃ C : ℝ, ∀ x, ‖cmxFB_Phi K B φ x‖ ≤ C := by
  obtain ⟨c2, C, hC0, hb⟩ := cmxFB_Phi_bound hK B φ
  refine ⟨‖B‖ * (C * (∫ y in ball (0 : Euc d) 1, ‖K y‖) + c2 * (∫ y, cmxFB_a d y)),
    fun x => ?_⟩
  unfold cmxFB_Phi
  calc ‖∫ y, B (φ (x - y)) (K y)‖ ≤ ∫ y, ‖B‖ * cmxFB_bd K C c2 x y :=
        norm_integral_le_of_norm_le ((cmxFB_bd_integrable hK C c2 x).const_mul ‖B‖)
          (Eventually.of_forall fun y => hb x x (by simp) y)
    _ = _ := by rw [integral_const_mul, cmxFB_bd_integral hK]

theorem cmxFB_Phi_hasFDerivAt [CompleteSpace H] (hK : cmxFB_KerOK K) (B : G →L[ℝ] Euc d →L[ℝ] H)
    (φ : SchwartzMap (Euc d) G) (x0 : Euc d) :
    HasFDerivAt (cmxFB_Phi K B φ)
      (cmxFB_Phi K (cmxFB_B' B) (SchwartzMap.fderivCLM ℝ (Euc d) G φ) x0) x0 := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_schwartz_a (SchwartzMap.fderivCLM ℝ (Euc d) G φ)
  obtain ⟨c2, hc2⟩ := cmxFB_dom hK (fun z => SchwartzMap.fderivCLM ℝ (Euc d) G φ z) C hC0 hC
  have hmem : ball x0 1 ∈ 𝓝 x0 := ball_mem_nhds _ one_pos
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y => B (φ (x - y)) (K y))
    (F' := fun x y => cmxFB_B' B (SchwartzMap.fderivCLM ℝ (Euc d) G φ (x - y)) (K y))
    (bound := fun y => ‖B‖ * cmxFB_bd K C c2 x0 y) hmem
    (Eventually.of_forall fun x => cmxFB_Phi_meas hK B φ x)
    (cmxFB_Phi_integrable hK B φ x0)
    (cmxFB_Phi_meas hK (cmxFB_B' B) (SchwartzMap.fderivCLM ℝ (Euc d) G φ) x0)
    (Eventually.of_forall fun y x hx => ?_)
    ((cmxFB_bd_integrable hK C c2 x0).const_mul _)
    (Eventually.of_forall fun y x hx => ?_)
  · have hx' : ‖x - x0‖ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hx; exact hx.le
    calc ‖cmxFB_B' B (SchwartzMap.fderivCLM ℝ (Euc d) G φ (x - y)) (K y)‖
        ≤ ‖B‖ * ‖SchwartzMap.fderivCLM ℝ (Euc d) G φ (x - y)‖ * ‖K y‖ :=
          cmxFB_B'_norm_le B _ _
      _ = ‖B‖ * (‖SchwartzMap.fderivCLM ℝ (Euc d) G φ (x - y)‖ * ‖K y‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hc2 x x0 hx' y) (by positivity)
  · have h1 : HasFDerivAt (fun x : Euc d => φ (x - y)) (fderiv ℝ φ (x - y)) x := by
      have := (φ.differentiableAt (x := x - y)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)
      exact this
    exact (B.flip (K y)).hasFDerivAt.comp x h1

end Phi

section Induct

variable {K : Euc d → Euc d}

theorem cmxFB_Phi_fderiv {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (hK : cmxFB_KerOK K)
    (B : G →L[ℝ] Euc d →L[ℝ] H) (φ : SchwartzMap (Euc d) G) :
    fderiv ℝ (cmxFB_Phi K B φ) =
      cmxFB_Phi K (cmxFB_B' B) (SchwartzMap.fderivCLM ℝ (Euc d) G φ) :=
  funext fun x => (cmxFB_Phi_hasFDerivAt hK B φ x).fderiv

theorem cmxFB_Phi_contDiff (hK : cmxFB_KerOK K) (n : ℕ) :
    ∀ {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
      [NormedSpace ℝ H] [CompleteSpace H] (B : G →L[ℝ] Euc d →L[ℝ] H)
      (φ : SchwartzMap (Euc d) G), ContDiff ℝ n (cmxFB_Phi K B φ) := by
  induction n with
  | zero =>
    intro G H _ _ _ _ _ B φ
    rw [Nat.cast_zero, contDiff_zero]
    have hd : Differentiable ℝ (cmxFB_Phi K B φ) := fun x =>
      (cmxFB_Phi_hasFDerivAt hK B φ x).differentiableAt
    exact hd.continuous
  | succ n ih =>
    intro G H _ _ _ _ _ B φ
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (cmxFB_Phi_hasFDerivAt hK B φ x).differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [cmxFB_Phi_fderiv hK]
      exact ih _ _

theorem cmxFB_Phi_iter_bdd (hK : cmxFB_KerOK K) (k : ℕ) :
    ∀ {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H]
      [NormedSpace ℝ H] [CompleteSpace H] (B : G →L[ℝ] Euc d →L[ℝ] H)
      (φ : SchwartzMap (Euc d) G), ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (cmxFB_Phi K B φ) x‖ ≤ C := by
  induction k with
  | zero =>
    intro G H _ _ _ _ _ B φ
    obtain ⟨C, hC⟩ := cmxFB_Phi_bdd hK B φ
    exact ⟨C, fun x => by simpa [norm_iteratedFDeriv_zero] using hC x⟩
  | succ k ih =>
    intro G H _ _ _ _ _ B φ
    obtain ⟨C, hC⟩ := ih (cmxFB_B' B) (SchwartzMap.fderivCLM ℝ (Euc d) G φ)
    refine ⟨C, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, cmxFB_Phi_fderiv hK]
    exact hC x

end Induct

/-! ### The kernel `∇g` and `∇g_{≤1}` -/

section Force

variable {s : ℝ}

theorem cmxFB_kernGrad_norm (x : Euc d) (hx : x ≠ 0) :
    ‖kernGrad s x‖ = ‖x‖ ^ (-(s + 1)) := by
  unfold kernGrad
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  rw [show -(s + 1) = -(s + 2) + 1 by ring, Real.rpow_add hn, Real.rpow_one]

theorem cmxFB_kernGrad_norm_le (hs0 : 0 ≤ s) (x : Euc d) :
    ‖kernGrad s x‖ ≤ ‖x‖ ^ (-(s + 1)) := by
  by_cases hx : x = 0
  · subst hx
    simp [kernGrad]
    exact Real.rpow_nonneg le_rfl _
  · exact (cmxFB_kernGrad_norm x hx).le

theorem cmxFB_kernGrad_neg (x : Euc d) : kernGrad s (-x) = -kernGrad s x := by
  unfold kernGrad
  simp

theorem cmxFB_kerOK (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    cmxFB_KerOK (kernGrad s : Euc d → Euc d) := by
  refine ⟨(cmxSA_kernGrad_measurable s).aestronglyMeasurable, ?_, 1, fun y hy => ?_⟩
  · refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := s + 1) ?_ ?_ ?_
      (cmxSA_kernGrad_measurable s).aestronglyMeasurable
    · rw [cmxSA_finrank]; omega
    · rw [cmxSA_finrank]; linarith
    · exact Filter.Eventually.of_forall fun z => by
        rw [one_mul]; exact cmxFB_kernGrad_norm_le hs0 z
  · refine (cmxFB_kernGrad_norm_le hs0 y).trans ?_
    exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)

/-- `B z e = Re z • e`. -/
def cmxFB_B0 (d : ℕ) : ℂ →L[ℝ] Euc d →L[ℝ] Euc d :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp Complex.reCLM

theorem cmxFB_B0_apply (z : ℂ) (e : Euc d) : cmxFB_B0 d z e = z.re • e := rfl

theorem cmxFB_gloForce_eq :
    (gloForce s : Euc d → Euc d) =
      cmxFB_Phi (kernGrad s) (cmxFB_B0 d) (cmxFB_Om (d := d) 1 one_pos) := by
  funext x
  unfold gloForce Pleq cmxFB_Phi
  have := integral_sub_left_eq_self (fun y => psiL 1 y • kernGrad s (x - y)) volume x
  simp only [sub_sub_cancel] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [cmxFB_B0_apply, cmxFB_Om_apply]

theorem cmxFB_gloForce_neg (x : Euc d) : gloForce s (-x) = -gloForce s x := by
  unfold gloForce Pleq
  have h1 := integral_neg_eq_self (fun y => psiL 1 y • kernGrad s (-x - y)) volume
  rw [← h1]
  have h2 : ∀ y : Euc d, psiL 1 (-y) • kernGrad s (-x - -y) = -(psiL 1 y • kernGrad s (x - y)) := by
    intro y
    rw [cmxFB_psiL_neg, show -x - -y = -(x - y) by abel, cmxFB_kernGrad_neg, smul_neg]
  simp_rw [h2]
  exact integral_neg _

end Force

end HRS.Commutator.Whole
