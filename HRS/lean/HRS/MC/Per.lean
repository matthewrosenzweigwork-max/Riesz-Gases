import HRS.Appendix.FDL

/-!
# Packet PER: periodization of the scaled profile `φ_t` and its decay for large `t`

Relocated helper statements for Lemma D.3 (torus half): `per_fcoef`, `per_decay_const`, `per_decay_deriv`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped FourierTransform ENNReal

namespace HRS.MC.Per

open HRS

variable {d : ℕ}

/-! ### Analytic facts about the profile -/

lemma per_hasCompactSupport {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : HasCompactSupport ψ := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Euc d) (1 / 2)) (isClosed_tsupport _) ?_
  exact hψ.support.trans Metric.ball_subset_closedBall

lemma per_contDiff {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := hψ.smooth

lemma per_integrable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Integrable ψ :=
  (hψ.smooth.continuous).integrable_of_hasCompactSupport (per_hasCompactSupport hψ)

lemma per_psi_neg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (x : Euc d) : ψ (-x) = ψ x :=
  hψ.radial _ _ (norm_neg x)

/-- The complex-valued profile. -/
def perPsiC (ψ : Euc d → ℝ) : Euc d → ℂ := fun x => (ψ x : ℂ)

lemma per_psiC_integrable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Integrable (perPsiC ψ) :=
  (per_integrable hψ).ofReal

/-- The Schwartz function `ψ`. -/
def perSchwartz {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : SchwartzMap (Euc d) ℂ :=
  HasCompactSupport.toSchwartzMap (f := perPsiC ψ)
    ((per_hasCompactSupport hψ).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp (per_contDiff hψ))

lemma per_schwartz_coe {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    (perSchwartz hψ : Euc d → ℂ) = perPsiC ψ := rfl

/-- `ψ̂` as the (complex) Fourier transform of `ψ`: it is real and equal to the cosine transform. -/
lemma per_fourier_psiC {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (ξ : Euc d) :
    𝓕 (perPsiC ψ) ξ = ((fdlPsiHat ψ ξ : ℝ) : ℂ) := by
  rw [Real.fourier_eq]
  set F : Euc d → ℂ := fun v => 𝐞 (-inner ℝ v ξ) • perPsiC ψ v with hF
  have hint : Integrable F := by
    refine (per_psiC_integrable hψ).norm.mono' ?_ (Eventually.of_forall fun v => ?_)
    · have hc : Continuous (perPsiC ψ) := Complex.continuous_ofReal.comp hψ.smooth.continuous
      exact (Real.continuous_fourierChar.comp (by fun_prop) |>.aestronglyMeasurable.smul
        hc.aestronglyMeasurable)
    · simp [hF]
  have h1 : ∫ v, F (-v) = ∫ v, F v := integral_neg_eq_self F volume
  have h2 : ∀ v, F v + F (-v) = (2 * (ψ v * Real.cos (2 * Real.pi * inner ℝ ξ v) : ℝ) : ℂ) := by
    intro v
    simp only [hF, perPsiC, per_psi_neg hψ, inner_neg_left, Circle.smul_def, Real.fourierChar_apply,
      real_inner_comm ξ v, smul_eq_mul]
    push_cast
    rw [Complex.cos]
    ring_nf
  have h3 : ∫ v, (F v + F (-v)) = 2 * ∫ v, F v := by
    rw [integral_add hint (hint.comp_neg), h1]
    ring
  have h4 : ∫ v, (F v + F (-v)) = 2 * ((∫ v, ψ v * Real.cos (2 * Real.pi * inner ℝ ξ v) : ℝ) : ℂ) := by
    simp_rw [h2]
    rw [integral_const_mul]
    congr 1
    exact integral_ofReal
  unfold fdlPsiHat
  have h5 : (2 : ℂ) * ∫ v, F v = 2 * ((∫ v, ψ v * Real.cos (2 * Real.pi * inner ℝ ξ v) : ℝ) : ℂ) :=
    h3.symm.trans h4
  exact mul_left_cancel₀ (two_ne_zero) h5


/-- Schwartz decay of the cosine transform. -/
lemma per_psiHat_decay {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Euc d, ‖ξ‖ ^ q * |fdlPsiHat ψ ξ| ≤ C := by
  refine ⟨SchwartzMap.seminorm ℝ q 0 (𝓕 (perSchwartz hψ)), apply_nonneg _ _, fun ξ => ?_⟩
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 (perSchwartz hψ)) q ξ
  have h2 : (𝓕 (perSchwartz hψ)) ξ = ((fdlPsiHat ψ ξ : ℝ) : ℂ) := by
    rw [← per_fourier_psiC hψ ξ]
    exact congrFun (SchwartzMap.fourier_coe (perSchwartz hψ)) ξ
  rw [h2, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

lemma per_phiC (ψ : Euc d → ℝ) (x : Euc d) :
    ((fdlPhi ψ x : ℝ) : ℂ) =
      convolution (perPsiC ψ) (perPsiC ψ) (ContinuousLinearMap.mul ℂ ℂ) volume x := by
  unfold fdlPhi
  simp only [convolution_def, ContinuousLinearMap.mul_apply', perPsiC]
  have := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure (Euc d)))
    (f := fun t => ψ t * ψ (x - t))
  push_cast at this
  exact this.symm

lemma per_fourier_phiC {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (ξ : Euc d) :
    𝓕 (fun x => ((fdlPhi ψ x : ℝ) : ℂ)) ξ = ((fdlPsiHat ψ ξ : ℝ) : ℂ) ^ 2 := by
  have h : (fun x => ((fdlPhi ψ x : ℝ) : ℂ)) =
      convolution (perPsiC ψ) (perPsiC ψ) (ContinuousLinearMap.mul ℂ ℂ) volume :=
    funext (per_phiC ψ)
  rw [h, Real.fourier_mul_convolution_eq (per_psiC_integrable hψ) (per_psiC_integrable hψ),
    per_fourier_psiC hψ, sq]

lemma per_fourier_scale {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (k : Euc d) :
    ∫ y : Euc d, 𝐞 (-inner ℝ y k) • ((fdlPhiScale ψ t y : ℝ) : ℂ)
      = ((fdlPsiHat ψ (t • k) : ℝ) : ℂ) ^ 2 := by
  rw [← per_fourier_phiC hψ (t • k), Real.fourier_eq]
  set h : Euc d → ℂ := fun u => 𝐞 (-inner ℝ u (t • k)) • ((fdlPhi ψ u : ℝ) : ℂ) with hh
  have h1 : ∀ y : Euc d, 𝐞 (-inner ℝ y k) • ((fdlPhiScale ψ t y : ℝ) : ℂ)
      = (((t ^ d)⁻¹ : ℝ) : ℂ) • h (t⁻¹ • y) := by
    intro y
    simp only [hh, fdlPhiScale]
    have : inner ℝ (t⁻¹ • y) (t • k) = inner ℝ y k := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
    rw [this]
    simp only [Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  simp_rw [h1]
  rw [integral_smul, Measure.integral_comp_inv_smul volume h t, finrank_euclideanSpace_fin,
    abs_of_pos (pow_pos ht d), Complex.real_smul, smul_eq_mul, ← mul_assoc]
  have hne : ((t ^ d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos ht d).ne'
  push_cast
  rw [inv_mul_cancel₀ (by exact_mod_cast hne), one_mul]


/-! ### Support and smoothness of `φ` and `φ_t` -/

lemma per_psi_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {x : Euc d} (hx : 1 / 2 ≤ ‖x‖) :
    ψ x = 0 := by
  by_contra h
  have : x ∈ tsupport ψ := subset_tsupport _ (Function.mem_support.mpr h)
  have := hψ.support this
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

lemma per_phi_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {x : Euc d} (hx : 1 ≤ ‖x‖) :
    fdlPhi ψ x = 0 := by
  by_contra h
  have h1 := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) (μ := volume)
    (Function.mem_support.mpr h)
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  have ha' : ‖a‖ < 1 / 2 := by
    by_contra hh
    exact ha (per_psi_zero hψ (not_lt.mp hh))
  have hb' : ‖b‖ < 1 / 2 := by
    by_contra hh
    exact hb (per_psi_zero hψ (not_lt.mp hh))
  have := norm_add_le a b
  linarith

lemma per_phi_contDiff {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlPhi ψ) := by
  unfold fdlPhi
  exact (per_hasCompactSupport hψ).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    (per_contDiff hψ) ((per_contDiff hψ).continuous.locallyIntegrable)

lemma per_phiScale_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) {x : Euc d}
    (hx : t ≤ ‖x‖) : fdlPhiScale ψ t x = 0 := by
  unfold fdlPhiScale
  rw [per_phi_zero hψ, mul_zero]
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht]
  rw [le_inv_mul_iff₀ ht]
  linarith

lemma per_phiScale_contDiff {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (t : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlPhiScale ψ t) := by
  unfold fdlPhiScale
  exact contDiff_const.mul ((per_phi_contDiff hψ).comp (contDiff_const_smul _))

/-! ### Periodization of a compactly supported smooth function -/

lemma per_finite_lattice (B : ℝ) : {n : Lattice d | ‖Lattice.toEuc n‖ ≤ B}.Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -⌈B⌉) (fun _ => ⌈B⌉)).subset ?_
  intro n hn
  have h : ∀ i, |(n i : ℝ)| ≤ B := fun i => by
    have h1 := PiLp.norm_apply_le (Lattice.toEuc n) i
    have e : ‖(Lattice.toEuc n) i‖ = |(n i : ℝ)| := by simp [Lattice.toEuc]
    rw [e] at h1
    exact h1.trans hn
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.mp (h i)).1
    have h2 : (-⌈B⌉ : ℝ) ≤ n i := by
      have := Int.le_ceil B
      linarith
    exact_mod_cast h2
  · have := (abs_le.mp (h i)).2
    have h2 : (n i : ℝ) ≤ ⌈B⌉ := this.trans (Int.le_ceil B)
    exact_mod_cast h2

lemma per_fdlPer_mk (f : Euc d → ℝ) (y : Euc d) :
    fdlPer f (Torus.mk y) = ∑' n : Lattice d, f (y + Lattice.toEuc n) := by
  obtain ⟨m, hm⟩ := Torus.rep_mk y
  unfold fdlPer
  rw [hm]
  have := (Equiv.addRight m).tsum_eq (fun n : Lattice d => f (y + Lattice.toEuc n))
  rw [← this]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addRight]
  congr 1
  have : Lattice.toEuc (n + m) = Lattice.toEuc n + Lattice.toEuc m := by
    ext i; simp [Lattice.toEuc]
  rw [this]
  abel

lemma per_term_ne_zero {f : Euc d → ℝ} {R r : ℝ} (hR : ∀ x, R < ‖x‖ → f x = 0) {y : Euc d}
    (hy : ‖y‖ ≤ r) {n : Lattice d} (hn : f (y + Lattice.toEuc n) ≠ 0) :
    ‖Lattice.toEuc n‖ ≤ R + r := by
  by_contra h
  apply hn
  apply hR
  have := norm_sub_le (Lattice.toEuc n) (-y)
  have h2 : ‖Lattice.toEuc n‖ ≤ ‖y + Lattice.toEuc n‖ + ‖y‖ := by
    have := norm_sub_le (y + Lattice.toEuc n) y
    simpa using this
  linarith [not_le.mp h]

lemma per_G_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {R : ℝ}
    (hR : ∀ x, R < ‖x‖ → f x = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => ∑' n : Lattice d, f (y + Lattice.toEuc n)) := by
  rw [contDiff_iff_contDiffAt]
  intro y0
  set S : Finset (Lattice d) := (per_finite_lattice (d := d) (R + ‖y0‖ + 1)).toFinset with hS
  have hev : (fun y : Euc d => ∑' n : Lattice d, f (y + Lattice.toEuc n)) =ᶠ[𝓝 y0]
      fun y => ∑ n ∈ S, f (y + Lattice.toEuc n) := by
    filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
    refine tsum_eq_sum fun n hn => ?_
    by_contra hne
    apply hn
    rw [hS, Set.Finite.mem_toFinset]
    have := per_term_ne_zero hR (r := ‖y‖) le_rfl hne
    have h3 : ‖y‖ ≤ ‖y0‖ + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      have := norm_le_norm_add_norm_sub' y y0
      linarith
    show ‖Lattice.toEuc n‖ ≤ R + ‖y0‖ + 1
    linarith
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun n _ => hf.comp (contDiff_id.add contDiff_const)).contDiffAt

lemma per_lift_fdlPer (f : Euc d → ℝ) :
    Torus.lift (fdlPer f) = fun y : Euc d => ∑' n : Lattice d, f (y + Lattice.toEuc n) := by
  funext y
  exact per_fdlPer_mk f y


/-! ### Unfolding the periodization: Fourier coefficients -/

/-- The unit box `(0,1]^d`. -/
def perBox (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc (0 : ℝ) 1}

lemma per_measurableSet_box : MeasurableSet (perBox d) := by
  have : perBox d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) 1) := by
    ext w; simp [perBox]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

lemma per_mk_mp :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (perBox d)) volume := by
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1)))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => UnitAddCircle.measurePreserving_mk 0)
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) (0 + 1))
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc)
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (0 : ℝ) (0 + 1)) = perBox d := by
    ext w; simp [perBox]
  rw [hc] at h2
  exact h1.comp h2

lemma per_norm_le_of_mem_box {w : Euc d} (hw : w ∈ perBox d) : ‖w‖ ≤ d + 1 := by
  have h1 : ‖w‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hw i
          rw [Real.norm_eq_abs, abs_of_pos this.1, sq]
          nlinarith [this.1, this.2]
      _ = d := by simp
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  by_contra h
  push Not at h
  nlinarith [norm_nonneg w]

/-- The additive homomorphism `ℤ^d → ℝ^d`. -/
def perHom (d : ℕ) : Lattice d →+ Euc d where
  toFun := Lattice.toEuc
  map_zero' := by ext i; simp [Lattice.toEuc]
  map_add' := fun a b => by ext i; simp [Lattice.toEuc]

/-- The translation action of `ℤ^d` on `ℝ^d`. -/
@[instance_reducible]
def perAct (d : ℕ) : AddAction (Lattice d) (Euc d) := AddAction.compHom (Euc d) (perHom d)

section FundDom

attribute [local instance] perAct

lemma per_vadd_def (g : Lattice d) (x : Euc d) : g +ᵥ x = Lattice.toEuc g + x := rfl

local instance perMeasConst : MeasurableConstVAdd (Lattice d) (Euc d) :=
  ⟨fun g => by
    have : (fun x : Euc d => g +ᵥ x) = fun x => Lattice.toEuc g + x := rfl
    rw [this]; exact measurable_const_add _⟩

local instance perInv : VAddInvariantMeasure (Lattice d) (Euc d) volume :=
  ⟨fun g s hs => by
    have : (fun x : Euc d => g +ᵥ x) = fun x => Lattice.toEuc g + x := rfl
    show volume ((fun x : Euc d => g +ᵥ x) ⁻¹' s) = volume s
    rw [this]
    exact measure_preimage_add _ _ _⟩

lemma per_isFundamentalDomain : IsAddFundamentalDomain (Lattice d) (perBox d) volume := by
  refine IsAddFundamentalDomain.mk' per_measurableSet_box.nullMeasurableSet fun x => ?_
  have key : ∀ a : ℝ, ∃! n : ℤ, a + n ∈ Ioc (0 : ℝ) 1 := by
    intro a
    refine ⟨⌊-a⌋ + 1, ?_, ?_⟩
    · have h1 := Int.lt_floor_add_one (-a)
      have h2 := Int.floor_le (-a)
      push_cast
      constructor <;> linarith
    · intro n hn
      have h1 := Int.lt_floor_add_one (-a)
      have h2 := Int.floor_le (-a)
      have h3 : (⌊-a⌋ : ℝ) < n := by linarith [hn.1]
      have h4 : (n : ℝ) < ⌊-a⌋ + 1 + 1 := by linarith [hn.2]
      have h5 : ⌊-a⌋ < n := by exact_mod_cast h3
      have h6 : n < ⌊-a⌋ + 1 + 1 := by exact_mod_cast h4
      omega
  choose n hn hu using fun i => key (x i)
  refine ⟨n, fun i => ?_, fun m hm => ?_⟩
  · simpa [per_vadd_def, Lattice.toEuc, add_comm] using hn i
  · funext i
    refine hu i (m i) ?_
    simpa [per_vadd_def, Lattice.toEuc, add_comm] using hm i


lemma per_fcoef_unfold {f : Euc d → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {R : ℝ}
    (hR : ∀ x, R < ‖x‖ → f x = 0) (k : Lattice d) :
    Torus.fcoef (fdlPer f) k = ∫ y : Euc d, Torus.mode (-k) (Torus.mk y) * (f y : ℂ) := by
  have hfc : Continuous f := hf.continuous
  have hcs : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) R)
    (fun x hx => hR x (by simpa using hx))
  set e : Euc d → ℂ := fun y => Torus.mode (-k) (Torus.mk y) with he
  have hec : Continuous e := (Torus.continuous_mode _).comp Torus.continuous_mk
  have hperE : ∀ y n, e (y + Lattice.toEuc n) = e y :=
    fun y n => Torus.lift_periodic (Torus.mode (-k)) y n
  set H : Euc d → ℂ := fun y => e y * (f y : ℂ) with hH
  have hHc : Continuous H := hec.mul (Complex.continuous_ofReal.comp hfc)
  have hHint : Integrable H :=
    hHc.integrable_of_hasCompactSupport ((hcs.comp_left Complex.ofReal_zero).mul_left)
  have hFc : Continuous (fdlPer f) := Torus.continuous_of_continuous_lift (by
    rw [per_lift_fdlPer]; exact (per_G_contDiff hf hR).continuous)
  have hm := per_mk_mp (d := d)
  have step1 : Torus.fcoef (fdlPer f) k
      = ∫ w in perBox d, e w * ((∑' n : Lattice d, f (w + Lattice.toEuc n) : ℝ) : ℂ) := by
    unfold Torus.fcoef
    have hcont : Continuous (fun x : Torus d => Torus.mode (-k) x * (fdlPer f x : ℂ)) :=
      (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp hFc)
    have := integral_map (μ := volume.restrict (perBox d)) (φ := Torus.mk)
      hm.measurable.aemeasurable
      (f := fun x : Torus d => Torus.mode (-k) x * (fdlPer f x : ℂ))
      (by rw [hm.map_eq]; exact hcont.aestronglyMeasurable)
    rw [hm.map_eq] at this
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [he, per_fdlPer_mk]
  have step2 : ∀ w : Euc d, e w * ((∑' n : Lattice d, f (w + Lattice.toEuc n) : ℝ) : ℂ)
      = ∑' n : Lattice d, H (w + Lattice.toEuc n) := by
    intro w
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hH, hperE]
  set S : Set (Lattice d) := {n | ‖Lattice.toEuc n‖ ≤ R + (d + 1)} with hS
  have hSfin : S.Finite := per_finite_lattice _
  have hHn : ∀ n : Lattice d, Integrable (fun w => H (w + Lattice.toEuc n)) :=
    fun n => hHint.comp_add_right _
  have hsum : Summable fun n : Lattice d =>
      ∫ w, ‖H (w + Lattice.toEuc n)‖ ∂(volume.restrict (perBox d)) := by
    refine summable_of_hasFiniteSupport (hSfin.subset ?_)
    intro n hn
    by_contra hnS
    apply hn
    refine setIntegral_eq_zero_of_forall_eq_zero fun w hw => ?_
    have : H (w + Lattice.toEuc n) = 0 := by
      by_cases hz : f (w + Lattice.toEuc n) = 0
      · simp [hH, hz]
      · exact absurd (per_term_ne_zero hR (r := d + 1) (per_norm_le_of_mem_box hw) hz) hnS
    simp [this]
  rw [step1]
  simp_rw [step2]
  rw [← integral_tsum_of_summable_integral_norm (fun n => (hHn n).restrict) hsum]
  have h5 := (per_isFundamentalDomain (d := d)).integral_eq_tsum' H hHint
  rw [h5, ← (Equiv.neg (Lattice d)).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.neg_apply]
  refine setIntegral_congr_fun per_measurableSet_box fun w _ => ?_
  simp only [per_vadd_def, add_comm]

end FundDom


/-! ### The three statements -/

theorem per_fcoef (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (k : Lattice d) :
    Torus.fcoef (fdlPer (fdlPhiScale ψ t)) k = ((fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) := by
  rw [per_fcoef_unfold (per_phiScale_contDiff hψ t) (R := t)
    (fun x hx => per_phiScale_zero hψ ht hx.le) k]
  have h := per_fourier_scale hψ ht (Lattice.toEuc k)
  push_cast
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Torus.mode_mk, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  rw [Torus.dot_eq_inner, Torus.toEuc_neg, inner_neg_left, real_inner_comm]


/-! ### The subtracted periodization and its Fourier coefficients -/

lemma per_integral_phi {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∫ y, fdlPhi ψ y = fdlPsiHat ψ 0 ^ 2 := by
  have h := per_fourier_phiC hψ 0
  rw [Real.fourier_eq] at h
  simp only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul] at h
  have h2 : (((∫ y, fdlPhi ψ y : ℝ)) : ℂ) = ((fdlPsiHat ψ 0 ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    exact integral_ofReal.symm
  exact_mod_cast h2

/-- `P φ_t - ∫ φ` as a function on the torus. -/
def perQ (ψ : Euc d → ℝ) (t : ℝ) : Torus d → ℝ :=
  fun x => fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y

lemma per_fdlPer_continuous {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    Continuous (fdlPer (fdlPhiScale ψ t)) :=
  Torus.continuous_of_continuous_lift (by
    rw [per_lift_fdlPer]
    exact (per_G_contDiff (per_phiScale_contDiff hψ t)
      (fun x hx => per_phiScale_zero hψ ht hx.le)).continuous)

lemma per_fcoef_sub_const {g : Torus d → ℝ} (hg : Continuous g) (c : ℝ) (k : Lattice d) :
    Torus.fcoef (fun x => g x - c) k = Torus.fcoef g k - (if k = 0 then (c : ℂ) else 0) := by
  unfold Torus.fcoef
  have hi1 : Integrable (fun x : Torus d => Torus.mode (-k) x * (g x : ℂ)) :=
    ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x : Torus d => (c : ℂ) * Torus.mode (-k) x) :=
    (Torus.integrable_mode (-k)).const_mul _
  have : ∀ x : Torus d, Torus.mode (-k) x * ((g x - c : ℝ) : ℂ)
      = Torus.mode (-k) x * (g x : ℂ) - (c : ℂ) * Torus.mode (-k) x := by
    intro x; push_cast; ring
  simp_rw [this]
  rw [integral_sub hi1 hi2, integral_const_mul, Torus.integral_mode]
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

lemma per_fcoef_Q {ψ : Euc d → ℝ} (hd : 1 ≤ d) (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (k : Lattice d) :
    Torus.fcoef (perQ ψ t) k = if k = 0 then 0 else ((fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) := by
  unfold perQ
  rw [per_fcoef_sub_const (per_fdlPer_continuous hψ ht), per_fcoef hd hψ ht k]
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    simp [per_integral_phi hψ, h0]
  · simp [hk]


/-! ### The lattice-sum bound -/

lemma per_series_bound {ψ : Euc d → ℝ} (hd : 1 ≤ d) (hψ : IsFDLProfile ψ) (j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      Summable (fun k : Lattice d => Lattice.jp k ^ j * ‖Torus.fcoef (perQ ψ t) k‖) ∧
      ∑' k : Lattice d, Lattice.jp k ^ j * ‖Torus.fcoef (perQ ψ t) k‖ ≤ C * t ^ (-(N : ℝ)) := by
  set q : ℕ := N + j + d + 1 with hq
  obtain ⟨C0, hC0, hdec⟩ := per_psiHat_decay hψ q
  set A : ℝ := 1 + 2 * Real.pi with hA
  have hApos : 0 < A := by positivity
  set m : ℝ := ((2 * q : ℕ) - (j : ℝ)) / 2 with hm
  have hm2 : (d : ℝ) < 2 * m := by
    have h2m : 2 * m = ((2 * q : ℕ) : ℝ) - j := by rw [hm]; ring
    rw [h2m, hq]
    push_cast
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hbs := summable_jp_rpow (d := d) m hm2
  set B : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun k => by unfold Lattice.jp; positivity
  set K : ℝ := C0 ^ 2 * A ^ (2 * q) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * B, mul_nonneg hK0 hB0, fun t ht1 => ?_⟩
  have ht : 0 < t := lt_of_lt_of_le one_pos ht1
  -- pointwise bound
  have hpt : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ j * ‖Torus.fcoef (perQ ψ t) k.1‖
      ≤ K * (t ^ (2 * q))⁻¹ * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k
    have hjp1 : 1 ≤ Lattice.jp k.1 := Torus.jp_ge_one k.1
    have hjp : 0 < Lattice.jp k.1 := lt_of_lt_of_le one_pos hjp1
    have hje : Lattice.jp k.1 ≤ A * Lattice.enorm k.1 := jp_le_enorm k
    have he : 0 < Lattice.enorm k.1 := by
      by_contra h
      have : Lattice.enorm k.1 ≤ 0 := not_lt.mp h
      nlinarith
    have hfc : ‖Torus.fcoef (perQ ψ t) k.1‖ = fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 := by
      rw [per_fcoef_Q hd hψ ht, if_neg k.2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hfc]
    set X : ℝ := fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 with hX
    have hnorm : ‖t • Lattice.toEuc k.1‖ = t * Lattice.enorm k.1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; rfl
    have hd1 := hdec (t • Lattice.toEuc k.1)
    rw [hnorm] at hd1
    have hd2 : X * (t * Lattice.enorm k.1) ^ (2 * q) ≤ C0 ^ 2 := by
      have h3 : ((t * Lattice.enorm k.1) ^ q * |fdlPsiHat ψ (t • Lattice.toEuc k.1)|) ^ 2 ≤ C0 ^ 2 :=
        pow_le_pow_left₀ (by positivity) hd1 2
      have e1 : ((t * Lattice.enorm k.1) ^ q * |fdlPsiHat ψ (t • Lattice.toEuc k.1)|) ^ 2
          = (t * Lattice.enorm k.1) ^ (2 * q) * fdlPsiHat ψ (t • Lattice.toEuc k.1) ^ 2 := by
        rw [mul_pow, sq_abs, ← pow_mul, mul_comm q 2]
      calc X * (t * Lattice.enorm k.1) ^ (2 * q)
          = ((t * Lattice.enorm k.1) ^ q * |fdlPsiHat ψ (t • Lattice.toEuc k.1)|) ^ 2 := by
            rw [e1, hX]; ring
        _ ≤ C0 ^ 2 := h3
    have hjq : Lattice.jp k.1 ^ (2 * q) ≤ A ^ (2 * q) * Lattice.enorm k.1 ^ (2 * q) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hjp.le hje _
    have hXP : X * (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q)) ≤ K := by
      calc X * (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q))
          ≤ X * (t ^ (2 * q) * (A ^ (2 * q) * Lattice.enorm k.1 ^ (2 * q))) := by
            gcongr
        _ = A ^ (2 * q) * (X * (t * Lattice.enorm k.1) ^ (2 * q)) := by rw [mul_pow]; ring
        _ ≤ A ^ (2 * q) * C0 ^ 2 := by gcongr
        _ = K := by rw [hK]; ring
    have hrpow : Lattice.jp k.1 ^ (-(2 * m)) = Lattice.jp k.1 ^ j / Lattice.jp k.1 ^ (2 * q) := by
      have : -(2 * m) = (j : ℝ) - ((2 * q : ℕ) : ℝ) := by rw [hm]; ring
      rw [this, Real.rpow_sub hjp, Real.rpow_natCast, Real.rpow_natCast]
    rw [hrpow]
    have hP : 0 < t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q) := by positivity
    have hXle : X ≤ K / (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q)) := by
      rw [le_div_iff₀ hP]; exact hXP
    calc Lattice.jp k.1 ^ j * X ≤ Lattice.jp k.1 ^ j * (K / (t ^ (2 * q) * Lattice.jp k.1 ^ (2 * q))) :=
          mul_le_mul_of_nonneg_left hXle (by positivity)
      _ = K * (t ^ (2 * q))⁻¹ * (Lattice.jp k.1 ^ j / Lattice.jp k.1 ^ (2 * q)) := by
          field_simp
  have hsum0 : Summable fun k : NonzeroLattice d =>
      K * (t ^ (2 * q))⁻¹ * Lattice.jp k.1 ^ (-(2 * m)) := hbs.mul_left _
  have hsumNZ : Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ j * ‖Torus.fcoef (perQ ψ t) k.1‖ :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (le_trans zero_le_one (Torus.jp_ge_one k.1)) j) (norm_nonneg _)) hpt hsum0
  have hsum : Summable (fun k : Lattice d => Lattice.jp k ^ j * ‖Torus.fcoef (perQ ψ t) k‖) :=
    (Torus.summable_lattice_iff _).mpr hsumNZ
  refine ⟨hsum, ?_⟩
  rw [Torus.tsum_lattice _ hsum]
  have h0 : Lattice.jp (0 : Lattice d) ^ j * ‖Torus.fcoef (perQ ψ t) 0‖ = 0 := by
    rw [per_fcoef_Q hd hψ ht, if_pos rfl]; simp
  rw [h0, zero_add]
  calc ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ j * ‖Torus.fcoef (perQ ψ t) k.1‖
      ≤ ∑' k : NonzeroLattice d, K * (t ^ (2 * q))⁻¹ * Lattice.jp k.1 ^ (-(2 * m)) :=
        hsumNZ.tsum_le_tsum hpt hsum0
    _ = K * (t ^ (2 * q))⁻¹ * B := by rw [tsum_mul_left]
    _ ≤ K * B * t ^ (-(N : ℝ)) := by
        have h1 : (t ^ (2 * q))⁻¹ ≤ t ^ (-(N : ℝ)) := by
          rw [Real.rpow_neg ht.le, Real.rpow_natCast]
          exact inv_anti₀ (pow_pos ht N) (pow_le_pow_right₀ ht1 (by omega))
        calc K * (t ^ (2 * q))⁻¹ * B = K * B * (t ^ (2 * q))⁻¹ := by ring
          _ ≤ K * B * t ^ (-(N : ℝ)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK0 hB0)



theorem per_decay_const (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (N : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ x : Torus d,
      |fdlPer (fdlPhiScale ψ t) x - ∫ y, fdlPhi ψ y| ≤ C * t ^ (-(N : ℝ)) := by
  obtain ⟨C, -, hC⟩ := per_series_bound hd hψ 0 N
  refine ⟨C, fun t ht x => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  obtain ⟨hs, hle⟩ := hC t ht
  simp only [pow_zero, one_mul] at hs hle
  have hcont : Continuous (perQ ψ t) :=
    (per_fdlPer_continuous hψ ht0).sub continuous_const
  exact (Torus.abs_le_tsum_fcoef hcont hs x).trans hle

theorem per_decay_deriv (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (j : ℕ) (hj : 1 ≤ j)
    (N : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (fdlPer (fdlPhiScale ψ t))) y‖ ≤ C * t ^ (-(N : ℝ)) := by
  obtain ⟨C, -, hC⟩ := per_series_bound hd hψ j N
  refine ⟨C, fun t ht y => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  obtain ⟨hs, hle⟩ := hC t ht
  set c : ℝ := ∫ y, fdlPhi ψ y with hc
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (fdlPer (fdlPhiScale ψ t))) := by
    rw [per_lift_fdlPer]
    exact per_G_contDiff (per_phiScale_contDiff hψ t) (fun x hx => per_phiScale_zero hψ ht0 hx.le)
  have hlift : Torus.lift (perQ ψ t) = fun z => Torus.lift (fdlPer (fdlPhiScale ψ t)) z - c := rfl
  have hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (perQ ψ t)) := by
    rw [hlift]; exact hG.sub contDiff_const
  have hQj : ContDiff ℝ (j : WithTop ℕ∞) (Torus.lift (perQ ψ t)) :=
    hQ.of_le (by exact_mod_cast le_top)
  have heq : Torus.lift (fdlPer (fdlPhiScale ψ t))
      = Torus.lift (perQ ψ t) + fun _ => c := by
    funext z; simp [hlift]
  have hderiv : iteratedFDeriv ℝ j (Torus.lift (fdlPer (fdlPhiScale ψ t))) y
      = iteratedFDeriv ℝ j (Torus.lift (perQ ψ t)) y := by
    rw [heq, iteratedFDeriv_add_apply (hQj.contDiffAt) contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero]
  rw [hderiv]
  exact (Torus.norm_iteratedFDeriv_le_tsum hQj le_rfl hs y).trans hle

end HRS.MC.Per
