import HRS.MS.Mov63EAux4

/-!
# S6.3, packet N6 (part 5): the pointwise Duhamel formula

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.

* `mne_weak_test`: `∫ ψ (h_t - h_0) = ∫_0^t ∫ ψ div Y_s ds` for `ψ ∈ C_c^∞` (`mne_weak_lin` with `φ = √ρ ψ` and `mne_pair_e`).
* `mne_fubini`, **`mne_pointwise`**: `h_t(x) - h_0(x) = ∫_0^t div Y_s(x) ds` for all `x`, `t ≥ 0` (testing against `C_c^∞`,
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`, continuity in `x` of both sides).  `mneEc` is the clamped, globally continuous version of `(s,x) ↦ div Y_{v_s}(x)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Duhamel

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m)

/-- The clamped flux divergence `Ê(s,x) = e_{v(max s 0)}(x)`. -/
def mneEc (d : ℕ) (s q β : ℝ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (v : ℝ → OscSpace d (m : ℝ))
    (p : ℝ × Euc d) : ℝ :=
  movDiv (mneY d s q β ρ hm (v (max p.1 0))) p.2

variable (H : Mov2dTh d s β q ρ) {v : ℝ → OscSpace d (m : ℝ)}

lemma mne_Ec_cont (hmild : MneMild H hm v) : Continuous (mneEc d s q β ρ hm v) := by
  have h := mne_e_joint hm H hmild.cont
  have hc : Continuous fun p : ℝ × Euc d => (max p.1 0, p.2) :=
    (continuous_fst.max continuous_const).prodMk continuous_snd
  have h2 := h.comp_continuous hc (fun p => Set.mk_mem_prod (show (0 : ℝ) ≤ max p.1 0 from le_max_right _ _) (mem_univ _))
  exact h2


/-- Continuity in `x` of the primitive `∫_0^t e_s(x) ds`. -/
lemma mne_prim_cont (hmild : MneMild H hm v) (t : ℝ) :
    Continuous fun x : Euc d => ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) := by
  have hc := mne_Ec_cont hm H hmild
  have h2 : Continuous (Function.uncurry fun (x : Euc d) (τ : ℝ) => mneEc d s q β ρ hm v (τ, x)) :=
    hc.comp (continuous_snd.prodMk continuous_fst)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : Euc d) (τ : ℝ) => mneEc d s q β ρ hm v (τ, x)) h2 0 t

lemma mneEc_eq {s' : ℝ} (hs : 0 ≤ s') (x : Euc d) :
    mneEc d s q β ρ hm v (s', x) = movDiv (mneY d s q β ρ hm (v s')) x := by
  simp only [mneEc, max_eq_left hs]

/-- **The tested Duhamel identity**: `∫ ψ (h_t - h_0) = ∫_0^t ∫ ψ e_s ds`. -/
theorem mne_weak_test (hmild : MneMild H hm v) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ψ x * (mnc_hu ρ (mne_hn hm) (v t) x - mnc_hu ρ (mne_hn hm) (v 0) x) =
      ∫ τ in (0 : ℝ)..t, ∫ x, ψ x * mneEc d s q β ρ hm v (τ, x) := by
  have hρsm := mnc_rho_smooth H
  have hpos := (mnb_rhoData H).pos
  set φ' : Euc d → ℝ := fun y => Real.sqrt (ρ y) * ψ y with hφ'
  have hsq : ContDiff ℝ ∞ (fun y => Real.sqrt (ρ y)) := (mnb_rhoData H).sqrt_smooth
  have hφ'sm : ContDiff ℝ ∞ φ' := hsq.mul hψ
  have hφ'c : HasCompactSupport φ' := hψc.mul_left
  have hφ2 : MemLp φ' 2 (volume : Measure (Euc d)) := hφ'sm.continuous.memLp_of_hasCompactSupport hφ'c
  have e1 : ∀ τ : ℝ, mnc_ipL φ' (Nat.cast_nonneg m) (v τ) = ∫ x, ψ x * mnc_hu ρ (mne_hn hm) (v τ) x := by
    intro τ
    have := mnc_ipL_ofFun hφ2 (Nat.cast_nonneg m) (mneV_memOsc hm (v τ))
    rw [mneV_ofFun hm (v τ)] at this
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hφ', mnc_hu]
    ring
  have hψint : ∀ τ : ℝ, Integrable (fun x => ψ x * mnc_hu ρ (mne_hn hm) (v τ) x) := by
    intro τ
    exact (hψ.continuous.mul (mne_hu_cd hm H (v τ)).continuous).integrable_of_hasCompactSupport hψc.mul_right
  have hweak := mne_weak_lin hmild hφ'sm hφ'c ht
  have e2 : ∀ x : ℝ, 0 ≤ x → (-(mnc_ipL (mov_S0 d β q φ') (Nat.cast_nonneg m) (v x)) +
        mnc_ipL φ' (mnb_sub_a_nonneg H hm) (mneF H hm v x)) = ∫ y, ψ y * mneEc d s q β ρ hm v (x, y) := by
    intro x hx
    have := mne_pair_e hm H hφ'sm hφ'c (v x)
    have e : (fun y => φ' y / Real.sqrt (ρ y) * movDiv (mneY d s q β ρ hm (v x)) y) =
        fun y => ψ y * mneEc d s q β ρ hm v (x, y) := by
      funext y
      have hs : 0 < Real.sqrt (ρ y) := Real.sqrt_pos.2 (hpos y)
      rw [mneEc_eq hm hx y]
      simp only [hφ']
      field_simp
    rw [← e]
    exact this.symm
  rw [e1 t, e1 0] at hweak
  rw [← integral_sub (hψint t) (hψint 0)] at hweak
  have e3 : ∀ x, ψ x * (mnc_hu ρ (mne_hn hm) (v t) x - mnc_hu ρ (mne_hn hm) (v 0) x) =
      ψ x * mnc_hu ρ (mne_hn hm) (v t) x - ψ x * mnc_hu ρ (mne_hn hm) (v 0) x := fun x => by ring
  simp_rw [e3]
  rw [hweak, intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
  exact e2 x hx.1.le


/-- Fubini for the tested primitive. -/
lemma mne_fubini (hmild : MneMild H hm v) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) =
      ∫ τ in (0 : ℝ)..t, ∫ x, ψ x * mneEc d s q β ρ hm v (τ, x) := by
  have hc := mne_Ec_cont hm H hmild
  set F : ℝ × Euc d → ℝ := fun p => ψ p.2 * mneEc d s q β ρ hm v p with hF
  have hFc : Continuous F := (hψ.continuous.comp continuous_snd).mul hc
  have hK : IsCompact (Icc (0 : ℝ) t ×ˢ tsupport ψ) := isCompact_Icc.prod hψc
  have hA : IntegrableOn F (Ioc (0 : ℝ) t ×ˢ tsupport ψ) :=
    (hFc.continuousOn.integrableOn_compact hK).mono_set (prod_mono Ioc_subset_Icc_self subset_rfl)
  have hB : IntegrableOn F (Ioc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) := by
    refine hA.of_forall_diff_eq_zero (measurableSet_Ioc.prod MeasurableSet.univ) (fun p hp => ?_)
    have : p.2 ∉ tsupport ψ := fun h => hp.2 ⟨hp.1.1, h⟩
    simp only [hF, image_eq_zero_of_notMem_tsupport this, zero_mul]
  have hint : Integrable (Function.uncurry fun (τ : ℝ) (x : Euc d) => ψ x * mneEc d s q β ρ hm v (τ, x))
      ((volume.restrict (uIoc (0 : ℝ) t)).prod (volume : Measure (Euc d))) := by
    rw [uIoc_of_le ht]
    have := hB
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at this
    exact this
  have e : ∀ x : Euc d, ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) =
      ∫ τ in (0 : ℝ)..t, ψ x * mneEc d s q β ρ hm v (τ, x) := fun x => by
    rw [intervalIntegral.integral_const_mul]
  simp_rw [e]
  exact (intervalIntegral_integral_swap hint).symm

/-- **Pointwise Duhamel** for `h_s = √ρ V_s`: `h_t(x) - h_0(x) = ∫_0^t e_s(x) ds`, `e_s = div Y_s`. -/
theorem mne_pointwise (hmild : MneMild H hm v) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    mnc_hu ρ (mne_hn hm) (v t) x - mnc_hu ρ (mne_hn hm) (v 0) x =
      ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) := by
  set Dfun : Euc d → ℝ := fun x => mnc_hu ρ (mne_hn hm) (v t) x - mnc_hu ρ (mne_hn hm) (v 0) x -
    ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) with hD
  have hDc : Continuous Dfun :=
    (((mne_hu_cd hm H (v t)).continuous.sub (mne_hu_cd hm H (v 0)).continuous)).sub (mne_prim_cont hm H hmild t)
  have hzero : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∫ x, ψ x • Dfun x ∂volume = 0 := by
    intro ψ hψ hψc
    have h1 := mne_weak_test hm H hmild hψ hψc ht
    have h2 := mne_fubini hm H hmild hψ hψc ht
    have i1 : Integrable (fun x => ψ x * (mnc_hu ρ (mne_hn hm) (v t) x - mnc_hu ρ (mne_hn hm) (v 0) x)) :=
      (hψ.continuous.mul ((mne_hu_cd hm H (v t)).continuous.sub (mne_hu_cd hm H (v 0)).continuous)).integrable_of_hasCompactSupport
        hψc.mul_right
    have i2 : Integrable (fun x => ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x)) :=
      (hψ.continuous.mul (mne_prim_cont hm H hmild t)).integrable_of_hasCompactSupport hψc.mul_right
    have e : ∀ x, ψ x • Dfun x = ψ x * (mnc_hu ρ (mne_hn hm) (v t) x - mnc_hu ρ (mne_hn hm) (v 0) x) -
        ψ x * ∫ τ in (0 : ℝ)..t, mneEc d s q β ρ hm v (τ, x) := fun x => by
      simp only [hD, smul_eq_mul]; ring
    simp_rw [e]
    rw [integral_sub i1 i2, h1, h2]
    ring
  have hlocal : LocallyIntegrable Dfun volume := hDc.locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal hzero
  have h0 : Dfun = 0 := by
    have := (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hDc continuous_const (g := fun _ => (0 : ℝ))).1
      (by filter_upwards [hae] with y hy; exact hy)
    exact this
  have := congrFun h0 x
  simp only [hD, Pi.zero_apply] at this
  linarith

end Duhamel

end HRS.MS.Mov63

end
