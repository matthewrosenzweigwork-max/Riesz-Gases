import Mathlib

/-!
# S8.2 observed-time layer, packet T8A.C06: positive resolvent domination from a discrete density recursion

Let `R = limsup_k r_k` (bounded, measurable).  Passing to the limit in the recursion (monotonicity of the positive operator
`T`, dominated convergence along the decreasing envelopes `R_N = sup_{k ≥ N} r_k`) gives `R ≤ b + T R` a.e.;
iterating, `R ≤ ∑_{j<m} T^j b + T^m R ≤ ∑_{j<m} T^j b + θ^m B`, and `v ≤ R`.  Only bounded measurable functions are used.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

section general
variable {E : Type*} [MeasurableSpace E] (mu : Measure E) [IsProbabilityMeasure mu] (K : E → E → ℝ)

/-- bounded measurable functions -/
def r26t8a_c06_good (f : E → ℝ) : Prop := Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C

theorem r26t8a_c06_int {hKm : Measurable (Function.uncurry K)}
    (hKrow : ∀ x, Integrable (K x) mu) {f : E → ℝ} (hf : r26t8a_c06_good f) (x : E) :
    Integrable (fun y => K x y * f y) mu := by
  obtain ⟨hfm, C, hC⟩ := hf
  have := (hKrow x).bdd_mul (c := C) hfm.aestronglyMeasurable (Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hC y)
  exact this.congr (Eventually.of_forall fun y => by simp [mul_comm])

end general

theorem r26t8a_positive_resolvent {E : Type*} [MeasurableSpace E]
    (mu : Measure E) [IsProbabilityMeasure mu] (K : E → E → ℝ)
    (hKm : Measurable (Function.uncurry K)) (hK0 : ∀ x y, 0 ≤ K x y)
    (b v : E → ℝ) (r : ℕ → E → ℝ) (eta theta B B0 : ℝ)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hB : 0 ≤ B) (hB0 : 0 ≤ B0) (hb : Measurable b) (hv : Measurable v)
    (hbb : ∀ x, 0 ≤ b x ∧ b x ≤ B0) (hrm : ∀ k, Measurable (r k))
    (hr : ∀ k x, 0 ≤ r k x ∧ r k x ≤ B)
    (hKrow : ∀ x, Integrable (K x) mu ∧ ∫ y, K x y ∂mu ≤ theta)
    (hrec : ∀ k, ∀ᵐ x ∂mu, r (k+1) x ≤ (1-eta)*r k x +
      eta*(b x + ∫ y, K x y*r k y ∂mu)) (hvr : ∀ k, v ≤ᵐ[mu] r k) :
    let T := fun f x => ∫ y, K x y*f y ∂mu
    (∀ x, Summable (fun j : ℕ => (T^[j]) b x)) ∧
    v ≤ᵐ[mu] (fun x => ∑' j : ℕ, (T^[j]) b x) := by
  intro T
  classical
  have hKi : ∀ x, Integrable (K x) mu := fun x => (hKrow x).1
  have hint : ∀ {f : E → ℝ}, r26t8a_c06_good f → ∀ x, Integrable (fun y => K x y * f y) mu :=
    fun {f} hf x => r26t8a_c06_int mu K (hKm := hKm) hKi hf x
  have hTgood : ∀ {f : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good (T f) := by
    intro f hf
    obtain ⟨hfm, C, hC⟩ := hf
    refine ⟨?_, |C| * theta, fun x => ?_⟩
    · have hmeas : Measurable fun p : E × E => K p.1 p.2 * f p.2 :=
        hKm.mul (hfm.comp measurable_snd)
      exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := mu)).measurable
    · have h1 : ‖∫ y, K x y * f y ∂mu‖ ≤ ∫ y, |C| * K x y ∂mu :=
        norm_integral_le_of_norm_le ((hKi x).const_mul |C|) (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 x y)]
          calc K x y * |f y| ≤ K x y * |C| :=
                mul_le_mul_of_nonneg_left ((hC y).trans (le_abs_self C)) (hK0 x y)
            _ = |C| * K x y := mul_comm _ _)
      rw [integral_const_mul] at h1
      have := mul_le_mul_of_nonneg_left (hKrow x).2 (abs_nonneg C)
      show |∫ y, K x y * f y ∂mu| ≤ |C| * theta
      rw [← Real.norm_eq_abs]; linarith
  have hTmono_ae : ∀ {f g : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good g → f ≤ᵐ[mu] g →
      ∀ x, T f x ≤ T g x := fun hf hg h x =>
    integral_mono_ae (hint hf x) (hint hg x)
      (h.mono fun y hy => mul_le_mul_of_nonneg_left hy (hK0 x y))
  have hTadd : ∀ {f g : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good g → ∀ x,
      T (fun y => f y + g y) x = T f x + T g x := fun {f g} hf hg x => by
    show ∫ y, K x y * (f y + g y) ∂mu = (∫ y, K x y * f y ∂mu) + ∫ y, K x y * g y ∂mu
    rw [← integral_add (hint hf x) (hint hg x)]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have hTb : ∀ {f : E → ℝ} (c : ℝ), r26t8a_c06_good f → (∀ y, f y ≤ c) → 0 ≤ c →
      ∀ x, T f x ≤ theta * c := by
    intro f c hf hfc hc x
    have h1 : T f x ≤ ∫ y, K x y * c ∂mu :=
      integral_mono (hint hf x) ((hKi x).mul_const c)
        (fun y => mul_le_mul_of_nonneg_left (hfc y) (hK0 x y))
    rw [integral_mul_const] at h1
    have := mul_le_mul_of_nonneg_right (hKrow x).2 hc
    linarith
  have hit_good : ∀ (j : ℕ) {f : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good ((T^[j]) f) := by
    intro j
    induction j with
    | zero => intro f hf; exact hf
    | succ j ih => intro f hf; rw [Function.iterate_succ']; exact hTgood (ih hf)
  have hit_bound : ∀ (j : ℕ) {f : E → ℝ} (c : ℝ), r26t8a_c06_good f → (∀ y, 0 ≤ f y) →
      (∀ y, f y ≤ c) → 0 ≤ c → ∀ x, 0 ≤ (T^[j]) f x ∧ (T^[j]) f x ≤ theta ^ j * c := by
    intro j
    induction j with
    | zero => intro f c hf h0 hc hc0 x; exact ⟨h0 x, by simpa using hc x⟩
    | succ j ih =>
      intro f c hf h0 hc hc0 x
      rw [Function.iterate_succ']
      show 0 ≤ T ((T^[j]) f) x ∧ T ((T^[j]) f) x ≤ theta ^ (j + 1) * c
      refine ⟨integral_nonneg fun y => mul_nonneg (hK0 x y) (ih c hf h0 hc hc0 y).1, ?_⟩
      have := hTb (theta ^ j * c) (hit_good j hf) (fun y => (ih c hf h0 hc hc0 y).2)
        (by positivity) x
      rw [pow_succ]; linarith
  have hiter_mono : ∀ (m : ℕ) {f g : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good g → f ≤ᵐ[mu] g →
      (T^[m]) f ≤ᵐ[mu] (T^[m]) g := by
    intro m
    induction m with
    | zero => intro f g _ _ h; exact h
    | succ m ih =>
      intro f g hf hg h
      rw [Function.iterate_succ]
      exact ih (hTgood hf) (hTgood hg) (Eventually.of_forall (hTmono_ae hf hg h))
  have hiter_add : ∀ (m : ℕ) {f g : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good g → ∀ x,
      (T^[m]) (fun y => f y + g y) x = (T^[m]) f x + (T^[m]) g x := by
    intro m
    induction m with
    | zero => intro f g _ _ x; rfl
    | succ m ih =>
      intro f g hf hg x
      rw [Function.iterate_succ]
      simp only [Function.comp]
      have : T (fun y => f y + g y) = fun x => T f x + T g x := funext (hTadd hf hg)
      rw [this]
      exact ih (hTgood hf) (hTgood hg) x
  have hbgood : r26t8a_c06_good b := ⟨hb, B0, fun x => by rw [abs_of_nonneg (hbb x).1]; exact (hbb x).2⟩
  -- summability
  have hsumm : ∀ x, Summable (fun j : ℕ => (T^[j]) b x) := by
    intro x
    refine Summable.of_nonneg_of_le (fun j => (hit_bound j B0 hbgood (fun y => (hbb y).1)
      (fun y => (hbb y).2) hB0 x).1) (fun j => (hit_bound j B0 hbgood (fun y => (hbb y).1)
      (fun y => (hbb y).2) hB0 x).2) ?_
    exact (summable_geometric_of_lt_one htheta htheta1).mul_right B0
  refine ⟨hsumm, ?_⟩
  -- the envelopes
  have hbdd : ∀ (N : ℕ) (x : E), BddAbove (Set.range fun k : ℕ => r (N + k) x) := fun N x =>
    ⟨B, by rintro _ ⟨k, rfl⟩; exact (hr _ x).2⟩
  set RN : ℕ → E → ℝ := fun N x => ⨆ k : ℕ, r (N + k) x with hRN
  have le_RN : ∀ N k x, r (N + k) x ≤ RN N x := fun N k x => le_ciSup (hbdd N x) k
  have RN_le : ∀ N x, RN N x ≤ B := fun N x => ciSup_le fun k => (hr _ x).2
  have RN_nn : ∀ N x, 0 ≤ RN N x := fun N x => (hr (N + 0) x).1.trans (le_RN N 0 x)
  have RN_meas : ∀ N, Measurable (RN N) := fun N => Measurable.iSup fun k => hrm (N + k)
  have RN_anti : ∀ N x, RN (N + 1) x ≤ RN N x := fun N x => ciSup_le fun k => by
    have := le_RN N (k + 1) x
    rwa [show N + (k + 1) = N + 1 + k by omega] at this
  set R : E → ℝ := fun x => ⨅ N : ℕ, RN N x with hR
  have hRbdd : ∀ x, BddBelow (Set.range fun N : ℕ => RN N x) := fun x => ⟨0, by
    rintro _ ⟨N, rfl⟩; exact RN_nn N x⟩
  have R_le : ∀ N x, R x ≤ RN N x := fun N x => ciInf_le (hRbdd x) N
  have R_nn : ∀ x, 0 ≤ R x := fun x => le_ciInf fun N => RN_nn N x
  have R_meas : Measurable R := Measurable.iInf RN_meas
  have hRN_tend : ∀ x, Tendsto (fun N => RN N x) atTop (𝓝 (R x)) := fun x =>
    tendsto_atTop_ciInf (antitone_nat_of_succ_le fun N => RN_anti N x) (hRbdd x)
  have hrgood : ∀ k, r26t8a_c06_good (r k) := fun k =>
    ⟨hrm k, B, fun x => by rw [abs_of_nonneg (hr k x).1]; exact (hr k x).2⟩
  have hRNgood : ∀ N, r26t8a_c06_good (RN N) := fun N =>
    ⟨RN_meas N, B, fun x => by rw [abs_of_nonneg (RN_nn N x)]; exact RN_le N x⟩
  have hRgood : r26t8a_c06_good R :=
    ⟨R_meas, B, fun x => by rw [abs_of_nonneg (R_nn x)]; exact (R_le 0 x).trans (RN_le 0 x)⟩
  have hrec_all : ∀ᵐ x ∂mu, ∀ k, r (k+1) x ≤ (1-eta)*r k x + eta*(b x + ∫ y, K x y*r k y ∂mu) :=
    ae_all_iff.2 hrec
  have hTmono : ∀ {f g : E → ℝ}, r26t8a_c06_good f → r26t8a_c06_good g → (∀ y, f y ≤ g y) →
      ∀ x, T f x ≤ T g x := fun hf hg h x => hTmono_ae hf hg (Eventually.of_forall h) x
  have hRineq : ∀ᵐ x ∂mu, R x ≤ b x + T R x := by
    filter_upwards [hrec_all] with x hx
    have hEnv : ∀ N, RN (N + 1) x ≤ (1 - eta) * RN N x + eta * (b x + T (RN N) x) := by
      intro N
      refine ciSup_le fun k => ?_
      have h1 := hx (N + k)
      have e : N + 1 + k = N + k + 1 := by omega
      show r (N + 1 + k) x ≤ _
      rw [e]
      have h2 : T (r (N + k)) x ≤ T (RN N) x := hTmono (hrgood _) (hRNgood N) (fun y => le_RN N k y) x
      have h3 : (1 - eta) * r (N + k) x ≤ (1 - eta) * RN N x :=
        mul_le_mul_of_nonneg_left (le_RN N k x) (by linarith)
      have h4 : eta * (b x + T (r (N + k)) x) ≤ eta * (b x + T (RN N) x) :=
        mul_le_mul_of_nonneg_left (by linarith) heta.le
      have h5 : (∫ y, K x y * r (N + k) y ∂mu) = T (r (N + k)) x := rfl
      rw [h5] at h1
      linarith
    have hTlim : Tendsto (fun N => T (RN N) x) atTop (𝓝 (T R x)) := by
      refine tendsto_integral_of_dominated_convergence (fun y => K x y * B) ?_ ?_ ?_ ?_
      · intro N
        exact ((hKm.comp (measurable_const.prodMk measurable_id)).mul (RN_meas N)).aestronglyMeasurable
      · exact (hKi x).mul_const B
      · intro N
        exact Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK0 x y) (RN_nn N y))]
          exact mul_le_mul_of_nonneg_left (RN_le N y) (hK0 x y)
      · exact Eventually.of_forall fun y => (hRN_tend y).const_mul (K x y)
    have hL : Tendsto (fun N => RN (N + 1) x) atTop (𝓝 (R x)) :=
      (hRN_tend x).comp (tendsto_add_atTop_nat 1)
    have hRr : Tendsto (fun N => (1 - eta) * RN N x + eta * (b x + T (RN N) x)) atTop
        (𝓝 ((1 - eta) * R x + eta * (b x + T R x))) :=
      ((hRN_tend x).const_mul (1 - eta)).add ((hTlim.const_add (b x)).const_mul eta)
    have hle := le_of_tendsto_of_tendsto' hL hRr hEnv
    have : eta * R x ≤ eta * (b x + T R x) := by linarith
    exact le_of_mul_le_mul_left this heta
  -- iteration
  have hiter : ∀ m : ℕ, ∀ᵐ x ∂mu, R x ≤ (∑ j ∈ Finset.range m, (T^[j]) b x) + (T^[m]) R x := by
    intro m
    induction m with
    | zero => exact Eventually.of_forall fun x => by simp
    | succ m ih =>
      have hg : r26t8a_c06_good (fun y => b y + T R y) := by
        obtain ⟨hm1, C1, hC1⟩ := hbgood
        obtain ⟨hm2, C2, hC2⟩ := hTgood hRgood
        exact ⟨hm1.add hm2, C1 + C2, fun x => (abs_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))⟩
      have hmono := hiter_mono m hRgood hg hRineq
      filter_upwards [ih, hmono] with x hx1 hx2
      have hadd := hiter_add m hbgood (hTgood hRgood) x
      have hsucc : (T^[m + 1]) R x = (T^[m]) (T R) x := by rw [Function.iterate_succ]; rfl
      rw [Finset.sum_range_succ, hsucc]
      have : (T^[m]) (fun y => b y + T R y) x = (T^[m]) b x + (T^[m]) (T R) x := hadd
      linarith
  -- v ≤ R
  have hvR : ∀ᵐ x ∂mu, v x ≤ R x := by
    have : ∀ᵐ x ∂mu, ∀ N, v x ≤ r N x := ae_all_iff.2 hvr
    filter_upwards [this] with x hx
    exact le_ciInf fun N => (hx N).trans ((le_RN N 0 x))
  have hall : ∀ᵐ x ∂mu, ∀ m : ℕ, v x ≤ (∑ j ∈ Finset.range m, (T^[j]) b x) + theta ^ m * B := by
    have := ae_all_iff.2 hiter
    filter_upwards [hvR, this] with x hx1 hx2 m
    have hb2 := (hit_bound m B hRgood (fun y => R_nn y) (fun y => (R_le 0 y).trans (RN_le 0 y)) hB x).2
    linarith [hx2 m]
  filter_upwards [hall] with x hx
  have hpart : ∀ m : ℕ, v x ≤ (∑' j : ℕ, (T^[j]) b x) + theta ^ m * B := fun m => by
    refine (hx m).trans ?_
    have := (hsumm x).sum_le_tsum (Finset.range m) (fun j _ => (hit_bound j B0 hbgood (fun y => (hbb y).1)
      (fun y => (hbb y).2) hB0 x).1)
    linarith
  have hlim : Tendsto (fun m : ℕ => (∑' j : ℕ, (T^[j]) b x) + theta ^ m * B) atTop
      (𝓝 ((∑' j : ℕ, (T^[j]) b x) + 0 * B)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one htheta htheta1).mul_const B)
  have := ge_of_tendsto' hlim hpart
  simpa using this

end HRS.MS.R26T8A
