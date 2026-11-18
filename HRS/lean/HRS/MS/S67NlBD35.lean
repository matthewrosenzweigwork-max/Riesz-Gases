import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63DAux1
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD34

/-!
# S6.7 nonlinear breakdown, packet 35: integrable higher-space majorant for a gain below two

`s67bd_lift_integrable`.  Short times: `HsOK`; longer times up to `T`: level-`p` propagation by short steps
and one gain step, giving `‖T†(τ) w‖_q ≤ K₀ (1 + τ^{-(q-p)/2}) ‖w‖_p` on `(0, T]`.  The majorant is
integrated with `mnd_beta_int` (`θ = 1 - (q-p)/2 > 0`).  The `L²_0`-valued path is strongly measurable
because its Hermite coordinates (an orthonormal basis of `L²`) are continuous on `(r, T]`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Level-`p` propagation of `T†(t)`, `0 < t ≤ m + 1`, with constant `M^(m+1)`. -/
theorem s67bd_prop_level (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) (p : ℝ) (hp : 0 ≤ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ m : ℕ, ∀ t ∈ Ioc (0 : ℝ) ((m : ℝ) + 1), ∀ w : MovL2Zero ρ₀,
      MemOsc p (movFun w) →
      MemOsc p (movFun (s67bd_Tdag H g hg t w)) ∧
        oscNorm p (movFun (s67bd_Tdag H g hg t w)) ≤ M ^ (m + 1) * oscNorm p (movFun w) := by
  obtain ⟨hsemi, -, hOK, -⟩ := s67bd_semigroup_data H g hg
  obtain ⟨C, hC0, hC⟩ := hOK p p hp le_rfl
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  have hshort : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ w : MovL2Zero ρ₀, MemOsc p (movFun w) →
      MemOsc p (movFun (s67bd_Tdag H g hg t w)) ∧
        oscNorm p (movFun (s67bd_Tdag H g hg t w)) ≤ max 1 C * oscNorm p (movFun w) := by
    intro t ht w hw
    obtain ⟨h1, h2⟩ := hC t ht w hw
    refine ⟨h1, h2.trans ?_⟩
    simp only [sub_self, zero_div, neg_zero, Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  intro m
  induction m with
  | zero =>
    intro t ht w hw
    have := hshort t (by simpa using ht) w hw
    simpa using this
  | succ m ih =>
    intro t ht w hw
    by_cases h1 : t ≤ 1
    · obtain ⟨a, b⟩ := hshort t ⟨ht.1, h1⟩ w hw
      refine ⟨a, b.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))⟩
      calc max 1 C = (max 1 C) ^ 1 := (pow_one _).symm
        _ ≤ (max 1 C) ^ (m + 1 + 1) :=
          pow_le_pow_right₀ (le_max_left _ _) (by omega)
    · replace h1 := not_le.1 h1
      have ht' : t - 1 ∈ Ioc (0 : ℝ) ((m : ℝ) + 1) := by
        refine ⟨by linarith, ?_⟩
        have := ht.2
        push_cast at this
        linarith
      obtain ⟨a1, b1⟩ := ih (t - 1) ht' w hw
      obtain ⟨a2, b2⟩ := hshort 1 ⟨one_pos, le_rfl⟩ _ a1
      rw [s67bd_Tdag_law H g hg hsemi t h1.le w]
      refine ⟨a2, b2.trans ?_⟩
      calc max 1 C * oscNorm p (movFun (s67bd_Tdag H g hg (t - 1) w))
          ≤ max 1 C * ((max 1 C) ^ (m + 1) * oscNorm p (movFun w)) :=
            mul_le_mul_of_nonneg_left b1 (le_trans zero_le_one (le_max_left _ _))
        _ = (max 1 C) ^ (m + 1 + 1) * oscNorm p (movFun w) := by ring

/-- The gain bound on `(0, T]`: `‖T†(τ) w‖_q ≤ K₀ (1 + τ^{-(q-p)/2}) ‖w‖_p`. -/
theorem s67bd_gain_bound (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) (p qlev T : ℝ) (hp : 0 ≤ p)
    (hpq : p ≤ qlev) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ τ ∈ Ioc (0 : ℝ) T, ∀ w : MovL2Zero ρ₀, MemOsc p (movFun w) →
      MemOsc qlev (movFun (s67bd_Tdag H g hg τ w)) ∧
        oscNorm qlev (movFun (s67bd_Tdag H g hg τ w)) ≤
          K0 * (1 + τ ^ (-((qlev - p) / 2))) * oscNorm p (movFun w) := by
  obtain ⟨hsemi, -, hOK, -⟩ := s67bd_semigroup_data H g hg
  obtain ⟨Cpq, hCpq0, hCpq⟩ := hOK p qlev hp hpq
  obtain ⟨M, hM1, hM⟩ := s67bd_prop_level H g hg p hp
  set m : ℕ := ⌈T⌉₊ with hm
  have hMm : 1 ≤ M ^ (m + 1) := one_le_pow₀ hM1
  refine ⟨Cpq * M ^ (m + 1), mul_nonneg hCpq0 (by linarith), fun τ hτ w hw => ?_⟩
  have hn0 : 0 ≤ oscNorm p (movFun w) := Real.sqrt_nonneg _
  have hτpow : 0 ≤ τ ^ (-((qlev - p) / 2)) := Real.rpow_nonneg hτ.1.le _
  by_cases h1 : τ ≤ 1
  · obtain ⟨a, b⟩ := hCpq τ ⟨hτ.1, h1⟩ w hw
    refine ⟨a, b.trans ?_⟩
    have : Cpq * τ ^ (-((qlev - p) / 2)) ≤ Cpq * M ^ (m + 1) * (1 + τ ^ (-((qlev - p) / 2))) := by
      nlinarith [mul_nonneg hCpq0 hτpow, mul_nonneg hCpq0 (by linarith : (0:ℝ) ≤ M ^ (m + 1) - 1),
        mul_nonneg (mul_nonneg hCpq0 (by linarith : (0:ℝ) ≤ M ^ (m + 1) - 1)) hτpow]
    exact mul_le_mul_of_nonneg_right this hn0
  · replace h1 := not_le.1 h1
    have ht' : τ - 1 ∈ Ioc (0 : ℝ) ((m : ℝ) + 1) := by
      refine ⟨by linarith, ?_⟩
      have h2 : T ≤ (m : ℝ) := Nat.le_ceil T
      linarith [hτ.2]
    obtain ⟨a1, b1⟩ := hM m (τ - 1) ht' w hw
    obtain ⟨a2, b2⟩ := hCpq 1 ⟨one_pos, le_rfl⟩ _ a1
    rw [s67bd_Tdag_law H g hg hsemi τ h1.le w]
    refine ⟨a2, b2.trans ?_⟩
    rw [Real.one_rpow, mul_one]
    calc Cpq * oscNorm p (movFun (s67bd_Tdag H g hg (τ - 1) w))
        ≤ Cpq * (M ^ (m + 1) * oscNorm p (movFun w)) := mul_le_mul_of_nonneg_left b1 hCpq0
      _ = Cpq * M ^ (m + 1) * oscNorm p (movFun w) := by ring
      _ ≤ Cpq * M ^ (m + 1) * (1 + τ ^ (-((qlev - p) / 2))) * oscNorm p (movFun w) := by
          refine mul_le_mul_of_nonneg_right ?_ hn0
          have h0 : 0 ≤ Cpq * M ^ (m + 1) := mul_nonneg hCpq0 (by linarith)
          nlinarith [mul_nonneg h0 hτpow]

/-- `‖u‖_{L²_0} = ‖u‖_{Σ^0}`. -/
theorem s67bd_norm_eq_osc_zero (u : MovL2Zero ρ₀) : ‖u‖ = oscNorm 0 (movFun u) := by
  have hmem : MemLp (movFun u) 2 (volume : Measure (Euc d)) :=
    Lp.memLp (u : Lp ℝ 2 (volume : Measure (Euc d)))
  rw [oscNorm_zero _ hmem]
  have h1 : ‖u‖ = ‖(u : Lp ℝ 2 (volume : Measure (Euc d)))‖ := (Submodule.norm_coe u).symm
  rw [h1]
  have h2 : ‖(u : Lp ℝ 2 (volume : Measure (Euc d)))‖ ^ 2 = ∫ x, movFun u x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    simp [sq]
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

/-- Strong measurability of an `L²_0`-valued path from continuity of its Hermite coordinates. -/
theorem s67bd_measurable_K {S : Set ℝ} (hS : MeasurableSet S) (k : ℝ → MovL2Zero ρ₀)
    (hcoef : ∀ α : MultiIndex d, ContinuousOn (fun v => hermiteCoeff (movFun (k v)) α) S) :
    AEStronglyMeasurable k (volume.restrict S) := by
  classical
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  set F : ℕ → ℝ → Lp ℝ 2 (volume : Measure (Euc d)) := fun n v =>
    ∑ α ∈ mova2_S d n, hermiteCoeff (movFun (k v)) α • b α with hF
  have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict S) := fun n =>
    Finset.aestronglyMeasurable_fun_sum _ fun α _ =>
      ((hcoef α).aestronglyMeasurable hS).smul_const (b α)
  have hlim : ∀ᵐ v ∂(volume.restrict S), Tendsto (fun n => F n v) atTop
      (𝓝 ((k v : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d)))) := by
    refine Eventually.of_forall fun v => ?_
    have hsum := b.hasSum_repr ((k v : MovL2Zero ρ₀) : Lp ℝ 2 (volume : Measure (Euc d)))
    have hT' := hsum.comp (tendsto_atTop_finset_of_monotone (mova2_S_mono (d := d)) mova2_S_exh)
    refine hT'.congr fun n => ?_
    simp only [Function.comp_apply, hF]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [HilbertBasis.repr_apply_apply, s67bd_coeff_eq_inner, hb α]
  have hm := aestronglyMeasurable_of_tendsto_ae atTop hFm hlim
  exact (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).1 hm

/-- Continuity of the Hermite coordinates of `v ↦ T†(v - r) h_v` on `(r, T]`. -/
theorem s67bd_coeff_cont_Tdag (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) (T r : ℝ) (hr0 : 0 ≤ r)
    (h : ℝ → MovL2Zero ρ₀) (hc : ContinuousOn h (Icc (0 : ℝ) T)) (α : MultiIndex d) :
    ContinuousOn (fun v => hermiteCoeff (movFun (s67bd_Tdag H g hg (v - r) (h v))) α) (Ioc r T) := by
  obtain ⟨hsemi, -, -, -⟩ := s67bd_semigroup_data H g hg
  simp_rw [s67bd_coeff_Tdag]
  set e : MovL2Zero ρ₀ := (MovL2Zero ρ₀).orthogonalProjectionOnto (hermiteLpD α) with he
  have h1 : ContinuousOn (fun v : ℝ => mov2d_T H g hg (v - r) e) (Ioc r T) := by
    refine (hsemi.cont e).comp (continuousOn_id.sub continuousOn_const) ?_
    intro v hv
    simp only [mem_Ici, sub_nonneg]
    exact hv.1.le
  have h2 : ContinuousOn h (Ioc r T) :=
    hc.mono fun v hv => ⟨hr0.trans hv.1.le, hv.2⟩
  exact h1.inner h2

set_option maxHeartbeats 1600000 in
theorem s67bd_lift_integrable (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (p qlev T : ℝ) (hp : 0 ≤ p) (hpq : p ≤ qlev) (hgain : qlev - p < 2)
    (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 ≤ B → ∀ h : ℝ → MovL2Zero ρ₀,
      ContinuousOn h (Icc (0 : ℝ) T) →
      (∀ v ∈ Icc (0 : ℝ) T, MemOsc p (movFun (h v)) ∧ oscNorm p (movFun (h v)) ≤ B) →
      ∀ r ∈ Icc (0 : ℝ) T,
        IntegrableOn (s67bd_lift H g hg qlev r h) (Icc r T) volume ∧
        (∫ v in Icc r T, ‖s67bd_lift H g hg qlev r h v‖) ≤ C * B ∧
        IntegrableOn (fun v => s67bd_Tdag H g hg (v - r) (h v)) (Icc r T) volume := by
  obtain ⟨K0, hK0, hgainb⟩ := s67bd_gain_bound H g hg p qlev T hp hpq
  set θ : ℝ := 1 - (qlev - p) / 2 with hθdef
  have hθ : 0 < θ := by rw [hθdef]; linarith
  have hexp : θ - 1 = -((qlev - p) / 2) := by rw [hθdef]; ring
  refine ⟨K0 * Real.exp T * mndBeta θ 1, mul_nonneg (mul_nonneg hK0 (Real.exp_pos _).le)
    (mnd_beta_nonneg θ 1), fun B hB h hc hmB r hr => ?_⟩
  have hm : ∀ v ∈ Icc (0 : ℝ) T, MemOsc p (movFun (h v)) := fun v hv => (hmB v hv).1
  obtain ⟨hmem, hmeas⟩ := s67bd_lift_measurable H g hg p qlev T hp hpq hgain hT h hc hm r hr
  have hrT : r ≤ T := hr.2
  set G : ℝ → ℝ := fun τ => (1 + τ ^ (θ - 1)) * Real.exp (-(1 * τ)) with hG
  set c0 : ℝ := B * (K0 * Real.exp T) with hc0
  have hc00 : 0 ≤ c0 := mul_nonneg hB (mul_nonneg hK0 (Real.exp_pos _).le)
  set ψ : ℝ → ℝ := fun v => c0 * G (v - r) with hψ
  have hGint : IntegrableOn (fun v => G (v - r)) (Icc r T) := by
    have h1 : IntervalIntegrable (fun v => G (v - r)) volume r T := by
      have h0 := (mnd_beta_intervalIntegrable hθ one_pos (sub_nonneg.2 hrT)).comp_sub_right r
      rw [zero_add, sub_add_cancel] at h0
      exact h0
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hrT).1 h1
  have hψIcc : IntegrableOn ψ (Icc r T) := hGint.const_mul c0
  have hψint : IntegrableOn ψ (Ioc r T) := hψIcc.mono_set Ioc_subset_Icc_self
  -- pointwise bounds on `(r, T]`
  have hbd : ∀ v ∈ Ioc r T, ‖s67bd_lift H g hg qlev r h v‖ ≤ ψ v ∧
      ‖s67bd_Tdag H g hg (v - r) (h v)‖ ≤ ψ v := by
    intro v hv
    have hτ : v - r ∈ Ioc (0 : ℝ) T := ⟨sub_pos.2 hv.1, by linarith [hr.1, hv.2]⟩
    have hv' : v ∈ Icc (0 : ℝ) T := ⟨hr.1.trans hv.1.le, hv.2⟩
    obtain ⟨hmem', hnorm⟩ := hgainb (v - r) hτ (h v) (hm v hv')
    have hB' : oscNorm p (movFun (h v)) ≤ B := (hmB v hv').2
    have hτpow : 0 ≤ (v - r) ^ (-((qlev - p) / 2)) := Real.rpow_nonneg hτ.1.le _
    have hmain : oscNorm qlev (movFun (s67bd_Tdag H g hg (v - r) (h v))) ≤ ψ v := by
      refine hnorm.trans ?_
      have h1 : K0 * (1 + (v - r) ^ (-((qlev - p) / 2))) * oscNorm p (movFun (h v)) ≤
          K0 * (1 + (v - r) ^ (-((qlev - p) / 2))) * B :=
        mul_le_mul_of_nonneg_left hB' (mul_nonneg hK0 (by linarith))
      refine h1.trans ?_
      have hE : 1 ≤ Real.exp T * Real.exp (-(1 * (v - r))) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith [hτ.2])
      have hpos : 0 ≤ K0 * (1 + (v - r) ^ (-((qlev - p) / 2))) * B :=
        mul_nonneg (mul_nonneg hK0 (by linarith)) hB
      calc K0 * (1 + (v - r) ^ (-((qlev - p) / 2))) * B
          ≤ K0 * (1 + (v - r) ^ (-((qlev - p) / 2))) * B *
              (Real.exp T * Real.exp (-(1 * (v - r)))) := le_mul_of_one_le_right hpos hE
        _ = ψ v := by rw [hψ, hG, hc0, hexp]; ring
    refine ⟨?_, ?_⟩
    · have hl : s67bd_lift H g hg qlev r h v =
          OscSpace.ofFun qlev (movFun (s67bd_Tdag H g hg (v - r) (h v))) := by
        simp only [s67bd_lift, hv.1, ↓reduceIte]
      rw [hl, OscSpace.norm_ofFun _ (hmem v hv)]
      exact hmain
    · rw [s67bd_norm_eq_osc_zero]
      exact ((mo_mono (hp.trans hpq) (hmem v hv)).2).trans hmain
  have hae : ∀ᵐ v ∂(volume.restrict (Ioc r T)), ‖s67bd_lift H g hg qlev r h v‖ ≤ ψ v :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => (hbd v hv).1)
  have hmeasI : AEStronglyMeasurable (s67bd_lift H g hg qlev r h) (volume.restrict (Ioc r T)) :=
    hmeas.mono_set Ioc_subset_Icc_self
  refine ⟨?_, ?_, ?_⟩
  · have hI : IntegrableOn (s67bd_lift H g hg qlev r h) (Ioc r T) := Integrable.mono' hψint hmeasI hae
    exact hI.congr_set_ae Ioc_ae_eq_Icc.symm
  · rw [integral_Icc_eq_integral_Ioc]
    have h1 : (∫ v in Ioc r T, ‖s67bd_lift H g hg qlev r h v‖) ≤ ∫ v in Ioc r T, ψ v :=
      integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) hψint hae
    refine h1.trans ?_
    have h2 : ∫ v in Ioc r T, ψ v = c0 * ∫ v in r..T, G (v - r) := by
      rw [intervalIntegral.integral_of_le hrT, ← integral_const_mul]
    have h3 : ∫ v in r..T, G (v - r) = ∫ τ in (0 : ℝ)..(T - r), G τ := by
      rw [intervalIntegral.integral_comp_sub_right (fun τ => G τ) r, sub_self]
    have h4 : ∫ τ in (0 : ℝ)..(T - r), G τ ≤ mndBeta θ 1 :=
      mnd_beta_le hθ one_pos (sub_nonneg.2 hrT)
    rw [h2, h3]
    calc c0 * ∫ τ in (0 : ℝ)..(T - r), G τ ≤ c0 * mndBeta θ 1 :=
          mul_le_mul_of_nonneg_left h4 hc00
      _ = K0 * Real.exp T * mndBeta θ 1 * B := by rw [hc0]; ring
  · have hkm : AEStronglyMeasurable (fun v => s67bd_Tdag H g hg (v - r) (h v))
        (volume.restrict (Ioc r T)) :=
      s67bd_measurable_K measurableSet_Ioc _ (s67bd_coeff_cont_Tdag H g hg T r hr.1 h hc)
    have hI : IntegrableOn (fun v => s67bd_Tdag H g hg (v - r) (h v)) (Ioc r T) :=
      Integrable.mono' hψint hkm
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => (hbd v hv).2))
    exact hI.congr_set_ae Ioc_ae_eq_Icc.symm

end HRS.MS.BreakdownS67
