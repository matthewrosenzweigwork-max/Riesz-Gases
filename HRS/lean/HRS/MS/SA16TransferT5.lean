import HRS.MS.SA16TransferEnergyAux

/-!
# S.A.16 T5: `mild_energy_by_splitting`

Time splitting of the mild solution at a uniform mesh: the one-step estimate
`sa16x_step` (energy of `x + ∫ A x`), the exact bound for `S`, the defect
`∫ (S(τ,r) - S(τ,s)) g(r) dr` (which sums to zero by dominated convergence), and a discrete Gronwall.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16Evolution

/-- the bundled hypotheses of `mild_energy_by_splitting` -/
structure sa16x_Data {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (p T K C₀ C₁ : ℝ) (N : X → ℝ) (S : ℝ → ℝ → X →L[ℝ] X) (A : ℝ → X →L[ℝ] X)
    (f u : ℝ → X) (x₀ : X) : Prop where
  hp : 2 ≤ p
  hT : 0 ≤ T
  hK : 0 ≤ K
  hN : IsSmoothNorm p N
  hdiag : ∀ r ∈ Icc (0 : ℝ) T, S r r = ContinuousLinearMap.id ℝ X
  hcomp : ∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T → (S t s).comp (S s r) = S t r
  hcont : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
    {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}
  hSbound : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ∀ x, N (S t r x) ≤ Real.exp (C₀ * (t - r)) * N x
  hA : ∀ x, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Icc (0 : ℝ) T))
  hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K
  hdiss : ∀ r ∈ Icc (0 : ℝ) T, ∀ x,
    fderiv ℝ (fun y => (N y) ^ p) x (A r x) ≤ p * C₁ * (N x) ^ p
  hf : IntegrableOn f (Icc (0 : ℝ) T)
  hu : ContinuousOn u (Icc (0 : ℝ) T)
  hmild : ∀ t ∈ Icc (0 : ℝ) T,
    u t = S t 0 x₀ + ∫ r in Icc (0 : ℝ) t, S t r (A r (u r) + f r)

section T5
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {p T K C₀ C₁ : ℝ} {N : X → ℝ} {S : ℝ → ℝ → X →L[ℝ] X} {A : ℝ → X →L[ℝ] X} {f u : ℝ → X}
  {x₀ : X}

/-- the integrand `A u + f` -/
def sa16x_g (A : ℝ → X →L[ℝ] X) (u f : ℝ → X) : ℝ → X := fun r => A r (u r) + f r

/-- uniform operator bound for the propagator -/
lemma sa16x_M (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ‖S t r‖ ≤ M := by
  obtain ⟨c, C, hc, hC, hcC⟩ := H.hN.equivalent
  refine ⟨Real.exp (|C₀| * T) * C / c, by positivity, fun r t hr hrt htT => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  have h1 := (hcC (S t r x)).1
  have h2 := H.hSbound r t hr hrt htT x
  have h3 := (hcC x).2
  have h4 : Real.exp (C₀ * (t - r)) ≤ Real.exp (|C₀| * T) :=
    Real.exp_le_exp.2 (by
      nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self C₀)) (sub_nonneg.2 hrt),
        mul_nonneg (abs_nonneg C₀) (show 0 ≤ T - (t - r) by linarith)])
  have h5 : N x ≤ C * ‖x‖ := h3
  have h6 : Real.exp (C₀ * (t - r)) * N x ≤ Real.exp (|C₀| * T) * (C * ‖x‖) :=
    mul_le_mul h4 h5 (H.hN.nonneg x) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

lemma sa16x_g_aesm (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) :
    AEStronglyMeasurable (sa16x_g A u f) (volume.restrict (Icc (0 : ℝ) T)) :=
  (sa16e_aesm_apply A H.hA (H.hu.aestronglyMeasurable measurableSet_Icc)).add
    H.hf.aestronglyMeasurable

lemma sa16x_u_bdd (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ Icc (0 : ℝ) T, ‖u r‖ ≤ R := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn H.hu
  exact ⟨max R 0, le_max_right _ _, fun r hr => (hR r hr).trans (le_max_left _ _)⟩

lemma sa16x_g_int (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) :
    IntegrableOn (sa16x_g A u f) (Icc (0 : ℝ) T) := by
  obtain ⟨R, hR0, hR⟩ := sa16x_u_bdd H
  have h1 : IntegrableOn (fun r => K * R + ‖f r‖) (Icc (0 : ℝ) T) :=
    (integrable_const _).add H.hf.norm
  refine Integrable.mono' h1 (sa16x_g_aesm H) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  calc ‖sa16x_g A u f r‖ ≤ ‖A r (u r)‖ + ‖f r‖ := norm_add_le _ _
    _ ≤ K * R + ‖f r‖ := by
      refine add_le_add ?_ le_rfl
      exact ((A r).le_opNorm _).trans (mul_le_mul (H.hAb r hr) (hR r hr) (norm_nonneg _) H.hK)

/-- the propagator applied to `g` is integrable on `[0,t]` -/
lemma sa16x_Sg_int (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (fun r => S t r (sa16x_g A u f r)) (volume.restrict (Icc (0 : ℝ) t)) := by
  obtain ⟨M, hM0, hM⟩ := sa16x_M H
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
  have hgi : IntegrableOn (sa16x_g A u f) (Icc (0 : ℝ) t) := (sa16x_g_int H).mono_set hsub
  refine Integrable.mono' (hgi.norm.const_mul M)
    (sa16e_S_aesm S H.hcont ht.2 hgi.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  exact ((S t r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM r t hr.1 hr.2 ht.2)
    (norm_nonneg _))

/-- splitting of the mild formula at an intermediate time -/
lemma sa16x_split (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s ≤ τ)
    (hτ : τ ≤ T) :
    u τ = S τ s (u s) + ∫ r in Ioc s τ, S τ r (sa16x_g A u f r) := by
  have hsT : s ≤ T := hsτ.trans hτ
  have hmτ : u τ = S τ 0 x₀ + ∫ r in Icc (0 : ℝ) τ, S τ r (sa16x_g A u f r) :=
    H.hmild τ ⟨hs.trans hsτ, hτ⟩
  have hms : u s = S s 0 x₀ + ∫ r in Icc (0 : ℝ) s, S s r (sa16x_g A u f r) :=
    H.hmild s ⟨hs, hsT⟩
  have hint : Integrable (fun r => S τ r (sa16x_g A u f r)) (volume.restrict (Icc (0 : ℝ) τ)) :=
    sa16x_Sg_int H ⟨hs.trans hsτ, hτ⟩
  rw [integral_Icc_eq_integral_Ioc] at hmτ hms
  have hint' : IntegrableOn (fun r => S τ r (sa16x_g A u f r)) (Ioc (0 : ℝ) τ) :=
    (IntegrableOn.mono_set hint Ioc_subset_Icc_self)
  have hunion : Ioc (0 : ℝ) τ = Ioc 0 s ∪ Ioc s τ := (Ioc_union_Ioc_eq_Ioc hs hsτ).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) s) (Ioc s τ) := Ioc_disjoint_Ioc_of_le le_rfl
  have hsplit : (∫ r in Ioc (0 : ℝ) τ, S τ r (sa16x_g A u f r)) =
      (∫ r in Ioc (0 : ℝ) s, S τ r (sa16x_g A u f r)) + ∫ r in Ioc s τ, S τ r (sa16x_g A u f r) := by
    rw [hunion]
    exact setIntegral_union hdisj measurableSet_Ioc (hint'.mono_set (hunion ▸ subset_union_left))
      (hint'.mono_set (hunion ▸ subset_union_right))
  have hint_s : IntegrableOn (fun r => S s r (sa16x_g A u f r)) (Ioc (0 : ℝ) s) :=
    IntegrableOn.mono_set (sa16x_Sg_int H ⟨hs, hsT⟩) Ioc_subset_Icc_self
  have hcomm : (∫ r in Ioc (0 : ℝ) s, S τ r (sa16x_g A u f r)) =
      S τ s (∫ r in Ioc (0 : ℝ) s, S s r (sa16x_g A u f r)) := by
    rw [← ContinuousLinearMap.integral_comp_comm (S τ s) hint_s]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [← H.hcomp r s τ hr.1.le hr.2 hsτ hτ]
    rfl
  have h0 : S τ 0 x₀ = S τ s (S s 0 x₀) := by
    rw [← H.hcomp 0 s τ le_rfl hs hsτ hτ]
    rfl
  rw [hmτ, hsplit, hcomm, hms, h0, map_add]
  abel


lemma sa16x_int_Ac (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) (y : X) :
    IntegrableOn (fun r => A r y) (Icc (0 : ℝ) T) := by
  refine Integrable.mono' (integrable_const (K * ‖y‖)) (H.hA y) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  exact ((A r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (H.hAb r hr) (norm_nonneg _))

lemma sa16x_int_Au (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) (y : X) :
    IntegrableOn (fun r => A r (u r - y)) (Icc (0 : ℝ) T) := by
  obtain ⟨R, hR0, hR⟩ := sa16x_u_bdd H
  refine Integrable.mono' (integrable_const (K * (R + ‖y‖)))
    (sa16e_aesm_apply A H.hA ((H.hu.aestronglyMeasurable measurableSet_Icc).sub
      aestronglyMeasurable_const)) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  refine ((A r).le_opNorm _).trans (mul_le_mul (H.hAb r hr) ?_ (norm_nonneg _) H.hK)
  exact (norm_sub_le _ _).trans (add_le_add (hR r hr) le_rfl)

lemma sa16x_Ioc_sub {s τ : ℝ} (hs : 0 ≤ s) (hτ : τ ≤ T) : Ioc s τ ⊆ Icc (0 : ℝ) T :=
  fun r hr => ⟨hs.trans hr.1.le, hr.2.trans hτ⟩

/-- the exact one-step decomposition -/
lemma sa16x_decomp (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {s τ : ℝ} (hs : 0 ≤ s)
    (hsτ : s ≤ τ) (hτ : τ ≤ T) :
    u τ = S τ s (u s + ((∫ r in Ioc s τ, A r (u s)) + (∫ r in Ioc s τ, A r (u r - u s)) +
        ∫ r in Ioc s τ, f r)) +
      ∫ r in Ioc s τ, (S τ r (sa16x_g A u f r) - S τ s (sa16x_g A u f r)) := by
  have hsub := sa16x_Ioc_sub (T := T) hs hτ
  have hz : IntegrableOn (fun r => A r (u s)) (Ioc s τ) := (sa16x_int_Ac H _).mono_set hsub
  have hw : IntegrableOn (fun r => A r (u r - u s)) (Ioc s τ) := (sa16x_int_Au H _).mono_set hsub
  have hφ : IntegrableOn f (Ioc s τ) := H.hf.mono_set hsub
  have hg : IntegrableOn (sa16x_g A u f) (Ioc s τ) := (sa16x_g_int H).mono_set hsub
  have hSg : IntegrableOn (fun r => S τ r (sa16x_g A u f r)) (Ioc s τ) :=
    IntegrableOn.mono_set (sa16x_Sg_int H ⟨hs.trans hsτ, hτ⟩) (Ioc_subset_Icc_self.trans
      (Icc_subset_Icc hs le_rfl))
  have hSg' : IntegrableOn (fun r => S τ s (sa16x_g A u f r)) (Ioc s τ) :=
    (S τ s).integrable_comp hg
  have hgsum : (∫ r in Ioc s τ, sa16x_g A u f r) =
      (∫ r in Ioc s τ, A r (u s)) + (∫ r in Ioc s τ, A r (u r - u s)) + ∫ r in Ioc s τ, f r := by
    calc (∫ r in Ioc s τ, sa16x_g A u f r)
        = ∫ r in Ioc s τ, ((A r (u s) + A r (u r - u s)) + f r) := by
          refine integral_congr_ae (Eventually.of_forall fun r => ?_)
          simp only [sa16x_g, ← map_add, add_sub_cancel]
      _ = (∫ r in Ioc s τ, (A r (u s) + A r (u r - u s))) + ∫ r in Ioc s τ, f r :=
          integral_add (hz.add hw) hφ
      _ = _ := by rw [integral_add hz hw]
  have hE := integral_sub hSg hSg'
  have hcm : (∫ r in Ioc s τ, S τ s (sa16x_g A u f r)) =
      S τ s (∫ r in Ioc s τ, sa16x_g A u f r) :=
    ContinuousLinearMap.integral_comp_comm (S τ s) hg
  rw [← hgsum, map_add, ← hcm, hE, sa16x_split H hs hsτ hτ]
  abel

instance sa16x_fin_Ioc (a b : ℝ) : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
  ⟨by rw [Measure.restrict_apply_univ]; simp⟩

lemma sa16x_z_bound (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {s τ : ℝ} (hs : 0 ≤ s)
    (hsτ : s ≤ τ) (hτ : τ ≤ T) :
    ‖∫ r in Ioc s τ, A r (u s)‖ ≤ K * (τ - s) * ‖u s‖ ∧
    fderiv ℝ (fun y => (N y) ^ p) (u s) (∫ r in Ioc s τ, A r (u s)) ≤
      (τ - s) * (p * C₁ * (N (u s)) ^ p) := by
  have hsub := sa16x_Ioc_sub (T := T) hs hτ
  have hz : IntegrableOn (fun r => A r (u s)) (Ioc s τ) := (sa16x_int_Ac H _).mono_set hsub
  have hfin : volume (Ioc s τ) < (⊤ : ℝ≥0∞) := by simp
  refine ⟨?_, ?_⟩
  · have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc s τ)
      (f := fun r => A r (u s)) (C := K * ‖u s‖) hfin (fun r hr =>
        ((A r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (H.hAb r (hsub hr)) (norm_nonneg _)))
    rw [Real.volume_real_Ioc_of_le hsτ] at this
    linarith
  · rw [← ContinuousLinearMap.integral_comp_comm _ hz]
    have hc : IntegrableOn (fun _ : ℝ => p * C₁ * (N (u s)) ^ p) (Ioc s τ) :=
      integrableOn_const (by simp)
    have := setIntegral_mono_on (μ := volume) (s := Ioc s τ)
      (f := fun r => fderiv ℝ (fun y => (N y) ^ p) (u s) (A r (u s)))
      (g := fun _ => p * C₁ * (N (u s)) ^ p)
      ((fderiv ℝ (fun y => (N y) ^ p) (u s)).integrable_comp hz) hc measurableSet_Ioc
      (fun r hr => H.hdiss r (hsub hr) (u s))
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hsτ, smul_eq_mul] at this
    exact this

lemma sa16x_w_bound (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {s τ ε : ℝ} (hs : 0 ≤ s)
    (hsτ : s ≤ τ) (hτ : τ ≤ T) (hε : ∀ r ∈ Ioc s τ, ‖u r - u s‖ ≤ ε) :
    ‖∫ r in Ioc s τ, A r (u r - u s)‖ ≤ K * ε * (τ - s) := by
  have hsub := sa16x_Ioc_sub (T := T) hs hτ
  have hfin : volume (Ioc s τ) < (⊤ : ℝ≥0∞) := by simp
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc s τ)
    (f := fun r => A r (u r - u s)) (C := K * ε) hfin (fun r hr =>
      ((A r).le_opNorm _).trans (mul_le_mul (H.hAb r (hsub hr)) (hε r hr) (norm_nonneg _) H.hK))
  rw [Real.volume_real_Ioc_of_le hsτ] at this
  exact this

lemma sa16x_phi_bound (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {s τ : ℝ} (hs : 0 ≤ s)
    (hτ : τ ≤ T) :
    N (∫ r in Ioc s τ, f r) ≤ ∫ r in Ioc s τ, N (f r) :=
  sa16x_N_integral_le H.hN (H.hf.mono_set (sa16x_Ioc_sub (T := T) hs hτ))

/-- the one-step energy inequality, with the splitting defect isolated -/
lemma sa16x_onestep (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ θ : ℝ, 0 < θ → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ s τ : ℝ, 0 ≤ s → s < τ → τ ≤ T → τ - s ≤ h₀ →
      N (u τ) ≤ Real.exp (C₀ * (τ - s)) * (N (u s) * (1 + C₁ * (τ - s)) + θ * (τ - s) +
          ∫ r in Ioc s τ, N (f r)) +
        Cn * ‖∫ r in Ioc s τ, (S τ r (sa16x_g A u f r) - S τ s (sa16x_g A u f r))‖ := by
  obtain ⟨c, Cn, hc, hCn, hcC⟩ := H.hN.equivalent
  refine ⟨Cn, hCn, fun θ hθ => ?_⟩
  have hQ : IsCompact (u '' Icc (0 : ℝ) T) := isCompact_Icc.image_of_continuousOn H.hu
  obtain ⟨h₁, hh₁, hstep⟩ := sa16x_step H.hN H.hp K C₁ H.hK hQ (θ := θ / 2) (by positivity)
  have huc : UniformContinuousOn u (Icc (0 : ℝ) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous H.hu
  have hCK : 0 < Cn * K + 1 := by have := H.hK; positivity
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc (θ / (2 * (Cn * K + 1)))
    (by positivity)
  refine ⟨min h₁ (δ / 2), by positivity, fun s τ hs hsτ hτ hh => ?_⟩
  have hh1 : τ - s ≤ h₁ := hh.trans (min_le_left _ _)
  have hh2 : τ - s ≤ δ / 2 := hh.trans (min_le_right _ _)
  have hhpos : 0 < τ - s := sub_pos.2 hsτ
  have hsT : s ≤ T := hsτ.le.trans hτ
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs, hsT⟩
  have hεr : ∀ r ∈ Ioc s τ, ‖u r - u s‖ ≤ θ / (2 * (Cn * K + 1)) := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) T := ⟨hs.trans hr.1.le, hr.2.trans hτ⟩
    have := hδu r hrI s hsI (by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hr.1])]
      linarith [hr.2])
    rw [dist_eq_norm] at this
    exact this.le
  obtain ⟨hzn, hzd⟩ := sa16x_z_bound H hs hsτ.le hτ
  have hwn := sa16x_w_bound H hs hsτ.le hτ hεr
  have hφ := sa16x_phi_bound H hs hτ
  set z : X := ∫ r in Ioc s τ, A r (u s) with hz
  set w : X := ∫ r in Ioc s τ, A r (u r - u s) with hw
  set φ : X := ∫ r in Ioc s τ, f r with hφdef
  set E : X := ∫ r in Ioc s τ, (S τ r (sa16x_g A u f r) - S τ s (sa16x_g A u f r)) with hE
  have h1 := hstep (τ - s) hhpos hh1 (u s) ⟨s, hsI, rfl⟩ z hzn hzd
  have hwN : N w ≤ θ / 2 * (τ - s) := by
    have h2 : N w ≤ Cn * ‖w‖ := (hcC w).2
    have h3 : Cn * ‖w‖ ≤ Cn * (K * (θ / (2 * (Cn * K + 1))) * (τ - s)) :=
      mul_le_mul_of_nonneg_left hwn hCn.le
    have h4 : Cn * (K * (θ / (2 * (Cn * K + 1))) * (τ - s)) =
        θ / 2 * (τ - s) * ((Cn * K) / (Cn * K + 1)) := by field_simp
    have h5 : (Cn * K) / (Cn * K + 1) ≤ 1 := by rw [div_le_one hCK]; linarith
    have h6 : θ / 2 * (τ - s) * ((Cn * K) / (Cn * K + 1)) ≤ θ / 2 * (τ - s) * 1 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  have hdec := sa16x_decomp H hs hsτ.le hτ
  have hY : N (u s + (z + w + φ)) ≤ N (u s + z) + N w + N φ := by
    have e : u s + (z + w + φ) = ((u s + z) + w) + φ := by abel
    rw [e]
    have a1 := H.hN.add ((u s + z) + w) φ
    have a2 := H.hN.add (u s + z) w
    linarith
  have hSn := H.hSbound s τ hs hsτ.le hτ (u s + (z + w + φ))
  have hexp := Real.exp_pos (C₀ * (τ - s))
  have hmain : N (u τ) ≤ N (S τ s (u s + (z + w + φ))) + N E := by
    conv_lhs => rw [hdec]
    exact H.hN.add _ _
  have hEn : N E ≤ Cn * ‖E‖ := (hcC E).2
  have hbr : N (u s + (z + w + φ)) ≤ N (u s) * (1 + C₁ * (τ - s)) + θ * (τ - s) +
      ∫ r in Ioc s τ, N (f r) := by nlinarith
  calc N (u τ) ≤ N (S τ s (u s + (z + w + φ))) + N E := hmain
    _ ≤ Real.exp (C₀ * (τ - s)) * N (u s + (z + w + φ)) + Cn * ‖E‖ := add_le_add hSn hEn
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hbr hexp.le
      linarith

/-- uniform mesh points `i t/(n+1)` -/
def sa16x_pt (t : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * (t / ((n : ℝ) + 1))

lemma sa16x_pt_succ (t : ℝ) (n i : ℕ) : sa16x_pt t n (i + 1) = sa16x_pt t n i + t / ((n : ℝ) + 1) := by
  unfold sa16x_pt; push_cast; ring

lemma sa16x_pt_nonneg {t : ℝ} (ht : 0 ≤ t) (n i : ℕ) : 0 ≤ sa16x_pt t n i := by
  unfold sa16x_pt; positivity

lemma sa16x_pt_le {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {i : ℕ} (hi : i ≤ n + 1) : sa16x_pt t n i ≤ t := by
  unfold sa16x_pt
  have h1 : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hi
  have h2 : 0 < (n : ℝ) + 1 := by positivity
  calc (i : ℝ) * (t / ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * (t / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = t := by field_simp

/-- every point of `(0,t]` lies in exactly one mesh cell -/
lemma sa16x_active {t : ℝ} (ht : 0 < t) (n : ℕ) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) t) :
    ∃ i, i < n + 1 ∧ r ∈ Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)) ∧
      ∀ j, j ≠ i → r ∉ Ioc (sa16x_pt t n j) (sa16x_pt t n (j + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set h : ℝ := t / ((n : ℝ) + 1) with hh
  have hh0 : 0 < h := by positivity
  have hrh : 0 < r / h := div_pos hr.1 hh0
  have hrt : r / h ≤ (n : ℝ) + 1 := by
    rw [div_le_iff₀ hh0, hh]
    calc r ≤ t := hr.2
      _ = ((n : ℝ) + 1) * (t / ((n : ℝ) + 1)) := by field_simp
  set m : ℕ := ⌈r / h⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.ceil_pos.2 hrh
  have hm2 : m ≤ n + 1 := by
    rw [hm, Nat.ceil_le]
    exact_mod_cast hrt
  have hm3 : r / h ≤ m := Nat.le_ceil _
  have hm4 : (m : ℝ) < r / h + 1 := Nat.ceil_lt_add_one hrh.le
  obtain ⟨i, hi⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  have hi' : (i : ℝ) + 1 = m := by exact_mod_cast hi.symm
  have hI : r ∈ Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)) := by
    unfold sa16x_pt
    constructor
    · rw [← hh]
      have : (i : ℝ) < r / h := by linarith
      rw [lt_div_iff₀ hh0] at this
      exact this
    · rw [← hh]
      push_cast
      have := hm3
      rw [div_le_iff₀ hh0] at this
      rw [hi']
      exact this
  refine ⟨i, by omega, hI, fun j hj hJ => ?_⟩
  unfold sa16x_pt at hI hJ
  rw [← hh] at hI hJ
  push_cast at hI hJ
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · have h1 : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
    have := hJ.2
    have := hI.1
    nlinarith
  · have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hgt
    have := hI.2
    have := hJ.1
    nlinarith

lemma sa16x_tri_compact (T : ℝ) : IsCompact {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} := by
  have hcl : IsClosed {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} := by
    refine IsClosed.inter (isClosed_le continuous_const continuous_snd) (IsClosed.inter
      (isClosed_le continuous_snd continuous_fst) (isClosed_le continuous_fst continuous_const))
  refine (isCompact_Icc (a := ((0 : ℝ), (0 : ℝ))) (b := (T, T))).of_isClosed_subset hcl ?_
  intro q hq
  exact ⟨⟨hq.2.1.trans' hq.1 |>.trans' le_rfl |>.trans' (by simpa using hq.1), hq.1⟩,
    ⟨hq.2.2, hq.2.1.trans hq.2.2⟩⟩

/-- the splitting defect tends to zero along uniform meshes -/
lemma sa16x_defect (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
      ‖∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)),
        (S (sa16x_pt t n (i + 1)) r (sa16x_g A u f r) -
          S (sa16x_pt t n (i + 1)) (sa16x_pt t n i) (sa16x_g A u f r))‖) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := sa16x_M H
  set g : ℝ → X := sa16x_g A u f with hg
  have hgI : IntegrableOn g (Icc (0 : ℝ) T) := sa16x_g_int H
  have hgM : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) T)) := sa16x_g_aesm H
  have ht0' : 0 ≤ t := ht0.le
  -- the cell integrands
  let Δ : ℕ → ℕ → ℝ → ℝ := fun n i r =>
    ‖S (sa16x_pt t n (i + 1)) r (g r) - S (sa16x_pt t n (i + 1)) (sa16x_pt t n i) (g r)‖
  let F : ℕ → ℝ → ℝ := fun n r => ∑ i ∈ Finset.range (n + 1),
    (Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1))).indicator (Δ n i) r
  have hcell : ∀ n, ∀ i ∈ Finset.range (n + 1), Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)) ⊆
      Icc (0 : ℝ) (sa16x_pt t n (i + 1)) := by
    intro n i _ r hr
    exact ⟨(sa16x_pt_nonneg ht0' n i).trans hr.1.le, hr.2⟩
  have hτT : ∀ n, ∀ i ∈ Finset.range (n + 1), sa16x_pt t n (i + 1) ≤ T := by
    intro n i hi
    exact (sa16x_pt_le ht0' n (by have := Finset.mem_range.1 hi; omega)).trans htT
  have hτmem : ∀ n, ∀ i ∈ Finset.range (n + 1), sa16x_pt t n (i + 1) ∈ Icc (0 : ℝ) T :=
    fun n i hi => ⟨sa16x_pt_nonneg ht0' n _, hτT n i hi⟩
  have hΔm : ∀ n, ∀ i ∈ Finset.range (n + 1),
      AEStronglyMeasurable (Δ n i) (volume.restrict (Icc (0 : ℝ) (sa16x_pt t n (i + 1)))) := by
    intro n i hi
    have hsub : Icc (0 : ℝ) (sa16x_pt t n (i + 1)) ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc le_rfl (hτT n i hi)
    have hgm : AEStronglyMeasurable g
        (volume.restrict (Icc (0 : ℝ) (sa16x_pt t n (i + 1)))) :=
      hgM.mono_measure (Measure.restrict_mono hsub le_rfl)
    exact ((sa16e_S_aesm S H.hcont (hτT n i hi) hgm).sub
      ((S (sa16x_pt t n (i + 1)) (sa16x_pt t n i)).continuous.comp_aestronglyMeasurable hgm)).norm
  have hΔb : ∀ n, ∀ i ∈ Finset.range (n + 1), ∀ r ∈ Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)),
      Δ n i r ≤ 2 * M * ‖g r‖ := by
    intro n i hi r hr
    have hi1 : i ≤ n + 1 := by have := Finset.mem_range.1 hi; omega
    have h1 := hM r (sa16x_pt t n (i + 1)) (by linarith [hr.1, sa16x_pt_nonneg ht0' n i]) hr.2
      (hτT n i hi)
    have h2 := hM (sa16x_pt t n i) (sa16x_pt t n (i + 1)) (sa16x_pt_nonneg ht0' n i)
      (by rw [sa16x_pt_succ]; have : 0 ≤ t / ((n : ℝ) + 1) := by positivity
          linarith) (hτT n i hi)
    calc Δ n i r ≤ ‖S (sa16x_pt t n (i + 1)) r (g r)‖ +
          ‖S (sa16x_pt t n (i + 1)) (sa16x_pt t n i) (g r)‖ := norm_sub_le _ _
      _ ≤ M * ‖g r‖ + M * ‖g r‖ := add_le_add
          (((S _ r).le_opNorm _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
          (((S _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))
      _ = 2 * M * ‖g r‖ := by ring
  have hΔint : ∀ n, ∀ i ∈ Finset.range (n + 1),
      Integrable ((Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1))).indicator (Δ n i)) volume := by
    intro n i hi
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hsub : Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)) ⊆ Icc (0 : ℝ) T :=
      (hcell n i hi).trans (Icc_subset_Icc le_rfl (hτT n i hi))
    have hgi : IntegrableOn g (Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1))) := hgI.mono_set hsub
    refine Integrable.mono' (hgi.norm.const_mul (2 * M)) ?_ ?_
    · exact (hΔm n i hi).mono_measure (Measure.restrict_mono (hcell n i hi) le_rfl)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hΔb n i hi r hr
  have hcellt : ∀ n, ∀ i ∈ Finset.range (n + 1), Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)) ⊆
      Ioc (0 : ℝ) t := by
    intro n i hi r hr
    have hi1 : i + 1 ≤ n + 1 := by have := Finset.mem_range.1 hi; omega
    refine ⟨lt_of_le_of_lt (sa16x_pt_nonneg ht0' n i) hr.1, hr.2.trans (sa16x_pt_le ht0' n hi1)⟩
  -- on `(0,t]` only the active cell contributes
  have hFact : ∀ n, ∀ r ∈ Ioc (0 : ℝ) t, ∃ i, i < n + 1 ∧
      r ∈ Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)) ∧ F n r = Δ n i r := by
    intro n r hr
    obtain ⟨i, hi, hri, huniq⟩ := sa16x_active ht0 n hr
    refine ⟨i, hi, hri, ?_⟩
    simp only [F]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hri _
    · intro j _ hj
      exact Set.indicator_of_notMem (huniq j hj) _
    · intro hno
      exact absurd (Finset.mem_range.2 hi) hno
  have hFout : ∀ n, ∀ r ∉ Ioc (0 : ℝ) t, F n r = 0 := by
    intro n r hr
    simp only [F]
    refine Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (fun hmem => hr (hcellt n i hi hmem)) _
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    have h := Finset.aestronglyMeasurable_sum (μ := volume) (Finset.range (n + 1))
      (f := fun i => (Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1))).indicator (Δ n i))
      (fun i hi => (hΔint n i hi).aestronglyMeasurable)
    refine h.congr (Eventually.of_forall fun r => ?_)
    simp [F, Finset.sum_apply]
  have hbd_int : Integrable ((Ioc (0 : ℝ) t).indicator (fun r => 2 * M * ‖g r‖)) volume := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (hgI.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl htT))).norm.const_mul
      (2 * M)
  have hFbound : ∀ n, ∀ᵐ r ∂volume,
      ‖F n r‖ ≤ (Ioc (0 : ℝ) t).indicator (fun r => 2 * M * ‖g r‖) r := by
    intro n
    refine Eventually.of_forall fun r => ?_
    by_cases hr : r ∈ Ioc (0 : ℝ) t
    · obtain ⟨i, hi, hri, hFi⟩ := hFact n r hr
      rw [hFi, Set.indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hΔb n i (Finset.mem_range.2 hi) r hri
    · rw [hFout n r hr, Set.indicator_of_notMem hr]
      simp
  have hFlim : ∀ᵐ r ∂volume, Tendsto (fun n => F n r) atTop (𝓝 0) := by
    refine Eventually.of_forall fun r => ?_
    by_cases hr : r ∈ Ioc (0 : ℝ) t
    · -- uniform continuity of the propagator applied to `g r` on the compact triangle
      have huc : UniformContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 (g r))
          {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} :=
        (sa16x_tri_compact T).uniformContinuousOn_of_continuous (H.hcont (g r))
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
      obtain ⟨N0, hN0⟩ := exists_nat_gt (t / δ)
      refine ⟨N0, fun n hn => ?_⟩
      obtain ⟨i, hi, hri, hFi⟩ := hFact n r hr
      have hi' : i ∈ Finset.range (n + 1) := Finset.mem_range.2 hi
      have hh : t / ((n : ℝ) + 1) < δ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hN0
        have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      have hτ := hτT n i hi'
      have hpt := sa16x_pt_nonneg ht0' n i
      have hpt1 : sa16x_pt t n i ≤ sa16x_pt t n (i + 1) := by
        rw [sa16x_pt_succ]; have : 0 ≤ t / ((n : ℝ) + 1) := by positivity
        linarith
      have := hδu (sa16x_pt t n (i + 1), r) ⟨hr.1.le, hri.2, hτ⟩
        (sa16x_pt t n (i + 1), sa16x_pt t n i) ⟨hpt, hpt1, hτ⟩ (by
          rw [Prod.dist_eq]
          simp only [dist_self, Real.dist_eq]
          refine max_lt hδ ?_
          rw [abs_of_nonneg (by linarith [hri.1])]
          rw [sa16x_pt_succ] at hri
          linarith [hri.2])
      rw [Real.dist_eq, hFi, sub_zero, abs_of_nonneg (norm_nonneg _)]
      simpa [Δ, dist_eq_norm] using this
    · simp only [hFout _ r hr]
      exact tendsto_const_nhds
  have hlim := tendsto_integral_of_dominated_convergence _ hFmeas hbd_int hFbound hFlim
  simp only [integral_zero] at hlim
  refine squeeze_zero (fun n => Finset.sum_nonneg fun i _ => norm_nonneg _) (fun n => ?_) hlim
  simp only [F]
  rw [integral_finsetSum _ (fun i hi => hΔint n i hi)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [integral_indicator measurableSet_Ioc]
  exact norm_integral_le_integral_norm _

/-- discrete Gronwall -/
lemma sa16x_gronwall (a β : ℕ → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ m : ℕ, (∀ i < m, a (i + 1) ≤ lam * a i + β i) →
      a m ≤ lam ^ m * a 0 + ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * β i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h m (by omega)
    rw [Finset.sum_range_succ]
    have h3 : lam * (lam ^ m * a 0 + ∑ i ∈ Finset.range m, lam ^ (m - 1 - i) * β i) =
        lam ^ (m + 1) * a 0 + ∑ i ∈ Finset.range m, lam ^ (m + 1 - 1 - i) * β i := by
      rw [mul_add, ← mul_assoc, ← pow_succ', Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have : m + 1 - 1 - i = (m - 1 - i) + 1 := by have := Finset.mem_range.1 hi; omega
      rw [this, pow_succ']; ring
    have h4 : lam ^ (m + 1 - 1 - m) * β m = β m := by simp
    have h5 := mul_le_mul_of_nonneg_left h1 hlam
    linarith

lemma sa16x_pt_last {t : ℝ} (n : ℕ) : sa16x_pt t n (n + 1) = t := by
  unfold sa16x_pt
  push_cast
  field_simp

lemma sa16x_pt_zero (t : ℝ) (n : ℕ) : sa16x_pt t n 0 = 0 := by
  unfold sa16x_pt; simp

/-- the forcing terms of the discrete scheme are bounded by the continuous convolution -/
lemma sa16x_forcing_sum {ν : ℝ → ℝ} (hν0 : ∀ r, 0 ≤ ν r) {t : ℝ} (ht0 : 0 < t)
    (hνI : IntegrableOn ν (Ioc (0 : ℝ) t)) (c C₀ : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Real.exp (c * (t / ((n : ℝ) + 1))) ^ (n - i) *
        Real.exp (C₀ * (t / ((n : ℝ) + 1))) *
        ∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)), ν r ≤
      Real.exp ((|c| + |C₀|) * (t / ((n : ℝ) + 1))) *
        ∫ r in Ioc (0 : ℝ) t, Real.exp (c * (t - r)) * ν r := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set h : ℝ := t / ((n : ℝ) + 1) with hh
  have hh0 : 0 < h := by positivity
  have hth : t = ((n : ℝ) + 1) * h := by rw [hh]; field_simp
  set G : ℝ → ℝ := fun r => Real.exp (c * (t - r)) * ν r with hG
  have hGI : IntegrableOn G (Ioc (0 : ℝ) t) := by
    refine Integrable.mono' (hνI.const_mul (Real.exp (|c| * t)))
      ((by fun_prop : Continuous fun r : ℝ => Real.exp (c * (t - r))).aestronglyMeasurable.mul
        hνI.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr => ?_)
    rw [hG, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hν0 r))]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hν0 r)
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self c)) (sub_nonneg.2 hr.2),
      mul_nonneg (abs_nonneg c) (show 0 ≤ t - (t - r) by linarith [hr.1]),
      mul_nonneg (abs_nonneg c) hr.1.le, mul_nonneg (abs_nonneg c) (show 0 ≤ t - r by linarith [hr.2])]
  have hcellI : ∀ i ∈ Finset.range (n + 1),
      IntegrableOn G (Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1))) := by
    intro i hi
    refine hGI.mono_set (fun r hr => ⟨lt_of_le_of_lt (sa16x_pt_nonneg ht0.le n i) hr.1, ?_⟩)
    exact hr.2.trans (sa16x_pt_le ht0.le n (by have := Finset.mem_range.1 hi; omega))
  have hterm : ∀ i ∈ Finset.range (n + 1), Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) *
      (∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)), ν r) ≤
      Real.exp ((|c| + |C₀|) * h) *
        ∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)), G r := by
    intro i hi
    have hi' : i ≤ n := by have := Finset.mem_range.1 hi; omega
    set κ : ℝ := Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) with hκ
    have hκe : κ = Real.exp (c * (t - sa16x_pt t n (i + 1)) + C₀ * h) := by
      have hpt : sa16x_pt t n (i + 1) = ((i : ℝ) + 1) * h := by
        unfold sa16x_pt; push_cast; rfl
      have hsub : t - sa16x_pt t n (i + 1) = ((n : ℝ) - i) * h := by
        rw [hpt]; linear_combination hth
      rw [hκ, ← Real.exp_nat_mul, ← Real.exp_add, hsub, Nat.cast_sub hi']
      congr 1
      ring
    have hνcell : IntegrableOn ν (Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1))) :=
      hνI.mono_set (fun r hr => ⟨lt_of_le_of_lt (sa16x_pt_nonneg ht0.le n i) hr.1,
        hr.2.trans (sa16x_pt_le ht0.le n (by omega))⟩)
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_on (hνcell.const_mul κ) ((hcellI i hi).const_mul _) measurableSet_Ioc
      (fun r hr => ?_)
    rw [hG, ← mul_assoc, hκe, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (hν0 r)
    have hd0 : 0 ≤ sa16x_pt t n (i + 1) - r := by linarith [hr.2]
    have hd1 : sa16x_pt t n (i + 1) - r ≤ h := by
      rw [sa16x_pt_succ] at hd0 ⊢
      linarith [hr.1, sa16x_pt_succ t n i]
    have e1 : -c * (sa16x_pt t n (i + 1) - r) ≤ |c| * (sa16x_pt t n (i + 1) - r) :=
      mul_le_mul_of_nonneg_right (neg_le_abs c) hd0
    have e2 : |c| * (sa16x_pt t n (i + 1) - r) ≤ |c| * h :=
      mul_le_mul_of_nonneg_left hd1 (abs_nonneg c)
    have e3 : C₀ * h ≤ |C₀| * h := mul_le_mul_of_nonneg_right (le_abs_self C₀) hh0.le
    nlinarith
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), Real.exp ((|c| + |C₀|) * h) *
          ∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)), G r := Finset.sum_le_sum hterm
    _ = Real.exp ((|c| + |C₀|) * h) * ∫ r in Ioc (0 : ℝ) t, G r := by
      rw [← Finset.mul_sum]
      congr 1
      have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := G)
        (a := sa16x_pt t n) (n := n + 1) (fun k hk => by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by
            rw [sa16x_pt_succ]; linarith)]
          exact hcellI k (Finset.mem_range.2 hk))
      rw [sa16x_pt_zero, sa16x_pt_last, intervalIntegral.integral_of_le ht0.le] at hsum
      rw [← hsum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [intervalIntegral.integral_of_le (by rw [sa16x_pt_succ]; linarith)]

lemma sa16x_u_zero (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) : u 0 = x₀ := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, H.hT⟩
  have := H.hmild 0 h0
  rw [Icc_self, setIntegral_measure_zero _ (by simp), add_zero, H.hdiag 0 h0] at this
  simpa using this

/-- the energy bound along a fixed fine mesh -/
lemma sa16x_scheme (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    {Cn θ h₀ : ℝ} (hθ : 0 < θ) (hCn : 0 < Cn)
    (hstep : ∀ s τ : ℝ, 0 ≤ s → s < τ → τ ≤ T → τ - s ≤ h₀ →
      N (u τ) ≤ Real.exp (C₀ * (τ - s)) * (N (u s) * (1 + C₁ * (τ - s)) + θ * (τ - s) +
          ∫ r in Ioc s τ, N (f r)) +
        Cn * ‖∫ r in Ioc s τ, (S τ r (sa16x_g A u f r) - S τ s (sa16x_g A u f r))‖)
    (n : ℕ) (hn : t / ((n : ℝ) + 1) ≤ h₀) :
    N (u t) ≤ Real.exp ((C₀ + C₁) * t) * N x₀ +
      Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) * (θ * t) +
      Real.exp ((|C₀ + C₁| + |C₀|) * (t / ((n : ℝ) + 1))) *
        (∫ r in Ioc (0 : ℝ) t, Real.exp ((C₀ + C₁) * (t - r)) * N (f r)) +
      Real.exp (|C₀ + C₁| * t) * (Cn * ∑ i ∈ Finset.range (n + 1),
        ‖∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)),
          (S (sa16x_pt t n (i + 1)) r (sa16x_g A u f r) -
            S (sa16x_pt t n (i + 1)) (sa16x_pt t n i) (sa16x_g A u f r))‖) := by
  have ht0' : 0 ≤ t := ht0.le
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfI : IntegrableOn (fun r => N (f r)) (Ioc (0 : ℝ) t) :=
    sa16x_N_comp_int H.hN (IntegrableOn.mono_set H.hf
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl htT)))
  have hforce := sa16x_forcing_sum (ν := fun r => N (f r)) (fun r => H.hN.nonneg _) ht0 hfI
    (C₀ + C₁) C₀ n
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = t / ((n : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hh] at hforce hn ⊢
  have hh0 : 0 < h := by rw [hh]; positivity
  have hth : t = ((n : ℝ) + 1) * h := by rw [hh]; field_simp
  have hpts : ∀ i : ℕ, sa16x_pt t n (i + 1) = sa16x_pt t n i + h := fun i => by
    rw [sa16x_pt_succ, hh]
  set c : ℝ := C₀ + C₁ with hc
  set a : ℕ → ℝ := fun i => N (u (sa16x_pt t n i)) with ha
  set F : ℕ → ℝ := fun i => ∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)), N (f r) with hF
  set E : ℕ → ℝ := fun i => ‖∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)),
    (S (sa16x_pt t n (i + 1)) r (sa16x_g A u f r) -
      S (sa16x_pt t n (i + 1)) (sa16x_pt t n i) (sa16x_g A u f r))‖ with hE
  set β : ℕ → ℝ := fun i => Real.exp (C₀ * h) * (θ * h + F i) + Cn * E i with hβ
  have hstep' : ∀ i < n + 1, a (i + 1) ≤ Real.exp (c * h) * a i + β i := by
    intro i hi
    have hi1 : i + 1 ≤ n + 1 := hi
    have hd : sa16x_pt t n (i + 1) - sa16x_pt t n i = h := by rw [hpts]; ring
    have h1 := hstep (sa16x_pt t n i) (sa16x_pt t n (i + 1)) (sa16x_pt_nonneg ht0' n i)
      (by rw [hpts]; linarith) ((sa16x_pt_le ht0' n hi1).trans htT) (by rw [hd]; exact hn)
    rw [hd] at h1
    have h2 : Real.exp (C₀ * h) * (a i * (1 + C₁ * h)) ≤ Real.exp (c * h) * a i := by
      have h3 : 1 + C₁ * h ≤ Real.exp (C₁ * h) := by linarith [Real.add_one_le_exp (C₁ * h)]
      have h4 : Real.exp (c * h) = Real.exp (C₀ * h) * Real.exp (C₁ * h) := by
        rw [← Real.exp_add, hc]; ring_nf
      have h5 : 0 ≤ a i := H.hN.nonneg _
      rw [h4]
      calc Real.exp (C₀ * h) * (a i * (1 + C₁ * h))
          ≤ Real.exp (C₀ * h) * (a i * Real.exp (C₁ * h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 h5) (Real.exp_pos _).le
        _ = Real.exp (C₀ * h) * Real.exp (C₁ * h) * a i := by ring
    have h6 : a (i + 1) ≤ Real.exp (C₀ * h) * (a i * (1 + C₁ * h) + θ * h + F i) + Cn * E i := h1
    have h7 : Real.exp (C₀ * h) * (a i * (1 + C₁ * h) + θ * h + F i) =
        Real.exp (C₀ * h) * (a i * (1 + C₁ * h)) + Real.exp (C₀ * h) * (θ * h + F i) := by ring
    simp only [hβ]
    linarith
  have hG := sa16x_gronwall a β (Real.exp_pos (c * h)).le (n + 1) hstep'
  have ha_last : a (n + 1) = N (u t) := by simp only [ha, sa16x_pt_last]
  have ha_zero : a 0 = N x₀ := by simp only [ha, sa16x_pt_zero, sa16x_u_zero H]
  have hpow : Real.exp (c * h) ^ (n + 1) = Real.exp (c * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [hth]; ring
  have hlam : ∀ k : ℕ, k ≤ n + 1 → Real.exp (c * h) ^ k ≤ Real.exp (|c| * t) := by
    intro k hk
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hk' : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk
    calc (k : ℝ) * (c * h) ≤ k * (|c| * h) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self c) hh0.le)
            (Nat.cast_nonneg _)
      _ ≤ ((n : ℝ) + 1) * (|c| * h) := mul_le_mul_of_nonneg_right hk' (by positivity)
      _ = |c| * t := by rw [hth]; ring
  have hexp0 : Real.exp (C₀ * h) ≤ Real.exp (|C₀| * t) := by
    refine Real.exp_le_exp.2 ?_
    have hht : h ≤ t := by
      rw [hth]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc C₀ * h ≤ |C₀| * h := mul_le_mul_of_nonneg_right (le_abs_self C₀) hh0.le
      _ ≤ |C₀| * t := mul_le_mul_of_nonneg_left hht (abs_nonneg _)
  set K0 : ℝ := Real.exp (|c| * t) * Real.exp (|C₀| * t) with hK0
  have hterm : ∀ i ∈ Finset.range (n + 1), Real.exp (c * h) ^ (n + 1 - 1 - i) * β i ≤
      K0 * (θ * h) + Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) * F i +
        Real.exp (|c| * t) * (Cn * E i) := by
    intro i hi
    have hk : n + 1 - 1 - i = n - i := by simp
    rw [hk]
    have hl := hlam (n - i) (by omega)
    have hl0 : 0 ≤ Real.exp (c * h) ^ (n - i) := (pow_pos (Real.exp_pos _) _).le
    have hE0 : 0 ≤ E i := norm_nonneg _
    have h1 : Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) ≤ K0 :=
      mul_le_mul hl hexp0 (Real.exp_pos _).le (Real.exp_pos _).le
    have h2 : Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) * (θ * h) ≤ K0 * (θ * h) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : Real.exp (c * h) ^ (n - i) * (Cn * E i) ≤ Real.exp (|c| * t) * (Cn * E i) :=
      mul_le_mul_of_nonneg_right hl (by positivity)
    have e : Real.exp (c * h) ^ (n - i) * β i =
        Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) * (θ * h) +
        Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) * F i +
        Real.exp (c * h) ^ (n - i) * (Cn * E i) := by
      simp only [hβ]; ring
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hsum
  have hconst : K0 * (((n + 1 : ℕ) : ℝ) * (θ * h)) = K0 * (θ * t) := by
    push_cast; rw [hth]; ring
  have hEsum : ∑ x ∈ Finset.range (n + 1), Real.exp (|c| * t) * (Cn * E x) =
      Real.exp (|c| * t) * (Cn * ∑ x ∈ Finset.range (n + 1), E x) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hforce' : ∑ i ∈ Finset.range (n + 1), Real.exp (c * h) ^ (n - i) * Real.exp (C₀ * h) * F i ≤
      Real.exp ((|c| + |C₀|) * h) * (∫ r in Ioc (0 : ℝ) t, Real.exp (c * (t - r)) * N (f r)) :=
    hforce
  rw [hpow, ha_last, ha_zero] at hG
  have hEs : ∑ i ∈ Finset.range (n + 1), E i = ∑ i ∈ Finset.range (n + 1),
      ‖∫ r in Ioc (sa16x_pt t n i) (sa16x_pt t n (i + 1)),
        (S (sa16x_pt t n (i + 1)) r (sa16x_g A u f r) -
          S (sa16x_pt t n (i + 1)) (sa16x_pt t n i) (sa16x_g A u f r))‖ := rfl
  rw [← hEs]
  have h1 := hG.trans (add_le_add le_rfl hsum)
  rw [hconst, hEsum] at h1
  refine h1.trans ?_
  have h3 : Real.exp (c * t) * N x₀ + (K0 * (θ * t) +
      ∑ x ∈ Finset.range (n + 1), Real.exp (c * h) ^ (n - x) * Real.exp (C₀ * h) * F x +
        Real.exp (|c| * t) * (Cn * ∑ x ∈ Finset.range (n + 1), E x)) ≤
      Real.exp (c * t) * N x₀ + (K0 * (θ * t) +
      Real.exp ((|c| + |C₀|) * h) * (∫ r in Ioc (0 : ℝ) t, Real.exp (c * (t - r)) * N (f r)) +
        Real.exp (|c| * t) * (Cn * ∑ x ∈ Finset.range (n + 1), E x)) := by
    exact add_le_add le_rfl (add_le_add (add_le_add le_rfl hforce') le_rfl)
  refine h3.trans (le_of_eq ?_)
  ring

lemma sa16x_main_pos (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) {t : ℝ} (ht0 : 0 < t)
    (htT : t ≤ T) :
    N (u t) ≤ Real.exp ((C₀ + C₁) * t) * N x₀ +
      ∫ r in Ioc (0 : ℝ) t, Real.exp ((C₀ + C₁) * (t - r)) * N (f r) := by
  obtain ⟨Cn, hCn, hone⟩ := sa16x_onestep H
  have hD := sa16x_defect H ht0 htT
  have hmesh : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul t
    simpa [div_eq_mul_inv] using this
  have key : ∀ θ : ℝ, 0 < θ → N (u t) ≤ Real.exp ((C₀ + C₁) * t) * N x₀ +
      Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) * (θ * t) +
      ∫ r in Ioc (0 : ℝ) t, Real.exp ((C₀ + C₁) * (t - r)) * N (f r) := by
    intro θ hθ
    obtain ⟨h₀, hh₀, hstep⟩ := hone θ hθ
    have hev : ∀ᶠ n : ℕ in atTop, t / ((n : ℝ) + 1) ≤ h₀ :=
      (hmesh.eventually (Iic_mem_nhds hh₀))
    have hg : Tendsto (fun n : ℕ => Real.exp ((|C₀ + C₁| + |C₀|) * (t / ((n : ℝ) + 1)))) atTop
        (𝓝 (Real.exp ((|C₀ + C₁| + |C₀|) * 0))) :=
      (Real.continuous_exp.tendsto _).comp (hmesh.const_mul _)
    have hlim := ((tendsto_const_nhds (x := Real.exp ((C₀ + C₁) * t) * N x₀ +
      Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) * (θ * t))).add
      (hg.mul_const (∫ r in Ioc (0 : ℝ) t, Real.exp ((C₀ + C₁) * (t - r)) * N (f r)))).add
      (tendsto_const_nhds (x := Real.exp (|C₀ + C₁| * t)).mul (hD.const_mul Cn))
    have := ge_of_tendsto hlim (hev.mono fun n hn => sa16x_scheme H ht0 htT hθ hCn hstep n hn)
    simpa using this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hK0 : 0 ≤ Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) * t := by positivity
  have := key (ε / (Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) * t + 1)) (by positivity)
  refine this.trans ?_
  have h2 : Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) *
      (ε / (Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t) * t + 1) * t) ≤ ε := by
    set K0 := Real.exp (|C₀ + C₁| * t) * Real.exp (|C₀| * t)
    have hpos : 0 < K0 * t + 1 := by linarith
    have : K0 * (ε / (K0 * t + 1) * t) = ε * (K0 * t) / (K0 * t + 1) := by field_simp
    rw [this, div_le_iff₀ hpos]
    nlinarith
  linarith

theorem sa16x_main (H : sa16x_Data p T K C₀ C₁ N S A f u x₀) :
    ∀ t ∈ Icc (0 : ℝ) T, N (u t) ≤ Real.exp ((C₀ + C₁) * t) * N x₀ +
      ∫ r in Icc (0 : ℝ) t, Real.exp ((C₀ + C₁) * (t - r)) * N (f r) := by
  intro t ht
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [sa16x_u_zero H, Icc_self, setIntegral_measure_zero _ (by simp)]
    simp
  · rw [integral_Icc_eq_integral_Ioc]
    exact sa16x_main_pos H hpos ht.2

end T5


/-- (skeleton defect fixed: the binder list of `hcomp` ended in `t ≤ T,` instead of `t ≤ T →`) -/
theorem mild_energy_by_splitting
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (p T K C₀ C₁ : ℝ) (hp : 2 ≤ p) (hT : 0 ≤ T) (hK : 0 ≤ K)
    (N : X → ℝ) (hN : IsSmoothNorm p N)
    (S : ℝ → ℝ → X →L[ℝ] X)
    (hdiag : ∀ r ∈ Icc (0 : ℝ) T, S r r=ContinuousLinearMap.id ℝ X)
    (hcomp : ∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T → (S t s).comp (S s r)=S t r)
    (hcont : ∀ x, ContinuousOn (fun q : ℝ × ℝ => S q.1 q.2 x)
      {q | 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T})
    (hSbound : ∀ r t, 0 ≤ r → r ≤ t → t ≤ T → ∀ x,
      N (S t r x) ≤ Real.exp (C₀*(t-r))*N x)
    (A : ℝ → X →L[ℝ] X)
    (hA : ∀ x, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Icc (0 : ℝ) T)))
    (hAb : ∀ r ∈ Icc (0 : ℝ) T, ‖A r‖ ≤ K)
    (hdiss : ∀ r ∈ Icc (0 : ℝ) T, ∀ x,
      fderiv ℝ (fun y => (N y)^p) x (A r x) ≤ p*C₁*(N x)^p)
    (f : ℝ → X) (hf : IntegrableOn f (Icc (0 : ℝ) T)) (x₀ : X)
    (u : ℝ → X) (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hmild : ∀ t ∈ Icc (0 : ℝ) T,
      u t=S t 0 x₀+∫ r in Icc (0 : ℝ) t, S t r (A r (u r)+f r)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      N (u t) ≤ Real.exp ((C₀+C₁)*t)*N x₀+
        ∫ r in Icc (0 : ℝ) t, Real.exp ((C₀+C₁)*(t-r))*N (f r) :=
  sa16x_main ⟨hp, hT, hK, hN, hdiag, hcomp, hcont, hSbound, hA, hAb, hdiss, hf, hu, hmild⟩

end HRS.Whole.AppendixA.Phase2SA16Transfer
