import HRS.MS.CritWholeW2Shift
import HRS.Stochastic.Integral
import HRS.Stochastic.Simple

/-!
# S8.1 (worker S81S): time shift of the scalar Itô integral

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

`s81s_ito_shift`: for a Brownian filtration `(ℱ, W)`, a progressive `L²` integrand `Φ` and the shifted data
`(ℱ_h = ℱ_{h+·}, W_h = W_{h+·} - W_h, Φ_h = Φ(h+·))`, the integral of `Φ_h` against `W_h` is the increment of the integral of `Φ`:
`∫_0^v Φ_h dW_h = ∫_0^{h+v} Φ dW - ∫_0^h Φ dW` (a.s., simultaneously for all `v ≥ 0`).  (Pro R26-T2.J00, `scalar_ito_shift`.)

Proof: a simple integrand for `ℱ_h` is shifted forward to a simple integrand for `ℱ` with the same elementary integral, and the
`L²`-approximation property of the Itô integral of `1_{(h,h+N]} Φ` identifies the increment as the integral of `1_{(0,N]} Φ_h`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS

namespace HRS.Whole.S81S

open HRS.Whole.BreakdownS81 HRS.MD.EQLawPath

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {ι : Type*}

/-- Forward shift of a simple integrand for the shifted filtration. -/
def s81s_shiftSimple (h : ℝ≥0) (Ψ : SimpleIntegrand (s81b_shiftFil ℱ h) ι) : SimpleIntegrand ℱ ι where
  n := Ψ.n
  t := fun i => Ψ.t i + h
  mono := fun i j hij => by
    have := Ψ.mono hij
    show Ψ.t i + (h : ℝ) ≤ Ψ.t j + (h : ℝ)
    linarith
  nonneg := add_nonneg Ψ.nonneg h.2
  ξ := Ψ.ξ
  meas := fun i => by
    have hnn : 0 ≤ Ψ.t i.castSucc := Ψ.nonneg.trans (Ψ.mono (Fin.zero_le _))
    have e : (s81b_shiftFil ℱ h) (Ψ.t i.castSucc) = ℱ (Ψ.t i.castSucc + h) := by
      simp only [s81b_shiftFil, max_eq_left hnn, add_comm]
    have := Ψ.meas i
    rw [e] at this
    exact this
  bdd := Ψ.bdd

theorem s81s_shiftSimple_toFun [Fintype ι] (h : ℝ≥0) (Ψ : SimpleIntegrand (s81b_shiftFil ℱ h) ι) (s : ℝ)
    (ω : Ω) (k : ι) : (s81s_shiftSimple h Ψ).toFun s ω k = Ψ.toFun (s - h) ω k := by
  rw [SimpleIntegrand.toFun_apply (s81s_shiftSimple h Ψ), SimpleIntegrand.toFun_apply Ψ]
  change (∑ i : Fin Ψ.n, Set.indicator (Set.Ioc (Ψ.t i.castSucc + h) (Ψ.t i.succ + h))
      (fun _ => Ψ.ξ i ω k) s) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Set.indicator, Set.mem_Ioc]
  have : (Ψ.t i.castSucc + h < s ∧ s ≤ Ψ.t i.succ + h) ↔ (Ψ.t i.castSucc < s - h ∧ s - h ≤ Ψ.t i.succ) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  simp only [this]

theorem s81s_shiftSimple_elem [Fintype ι] (h : ℝ≥0) (Ψ : SimpleIntegrand (s81b_shiftFil ℱ h) ι)
    (W : ℝ≥0 → Ω → ι → ℝ) {v : ℝ} (hv : 0 ≤ v) (ω : Ω) :
    (s81s_shiftSimple h Ψ).elemIntegral W (h + v) ω = Ψ.elemIntegral (shiftProc W h) v ω := by
  have hnn : ∀ j : Fin (Ψ.n + 1), 0 ≤ Ψ.t j := fun j => Ψ.nonneg.trans (Ψ.mono (Fin.zero_le _))
  have key : ∀ j : Fin (Ψ.n + 1), Real.toNNReal (min (Ψ.t j + h) ((h : ℝ) + v)) =
      h + Real.toNNReal (min (Ψ.t j) v) := by
    intro j
    have e1 : min (Ψ.t j + h) ((h : ℝ) + v) = (h : ℝ) + min (Ψ.t j) v := by
      rw [add_comm (Ψ.t j) (h : ℝ), min_add_add_left]
    rw [e1, Real.toNNReal_add h.coe_nonneg (le_min (hnn j) hv), Real.toNNReal_coe]
  show (∑ i : Fin Ψ.n, ∑ k, Ψ.ξ i ω k * (W (Real.toNNReal (min (Ψ.t i.succ + h) ((h : ℝ) + v))) ω k -
      W (Real.toNNReal (min (Ψ.t i.castSucc + h) ((h : ℝ) + v))) ω k)) = _
  unfold SimpleIntegrand.elemIntegral
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [key, shiftProc, Pi.sub_apply]
  ring

section Main

variable [Fintype ι]

theorem s81s_integrand_shift (h : ℝ≥0) {Φ Φh : ℝ → Ω → ι → ℝ} (v₀ : ℝ)
    (hrel : ∀ r : ℝ, 0 < r → ∀ ω k, Φh r ω k = Φ (h + r) ω k)
    (Ψ : SimpleIntegrand (s81b_shiftFil ℱ h) ι) (s : ℝ) (ω : Ω) (k : ι) :
    (s81s_shiftSimple h Ψ).toFun s ω k - restrictFun Φ h (h + v₀) Set.univ s ω k =
      Ψ.toFun (s - h) ω k - restrictFun Φh 0 v₀ Set.univ (s - h) ω k := by
  rw [s81s_shiftSimple_toFun]
  congr 1
  unfold restrictFun
  by_cases hs : s ∈ Set.Ioc (h : ℝ) (h + v₀)
  · have hs' : s - h ∈ Set.Ioc (0 : ℝ) v₀ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simp only [Set.mem_univ, true_and, hs, hs', if_true]
    have := hrel (s - h) (by linarith [hs.1]) ω k
    rw [this]
    congr 1
    ring
  · have hs' : s - h ∉ Set.Ioc (0 : ℝ) v₀ := fun hh => hs ⟨by linarith [hh.1], by linarith [hh.2]⟩
    simp [hs, hs']

theorem s81s_simple_zero (h : ℝ≥0) (Ψ : SimpleIntegrand (s81b_shiftFil ℱ h) ι) {r : ℝ} (hr : r ≤ 0)
    (ω : Ω) (k : ι) : Ψ.toFun r ω k = 0 := by
  rw [SimpleIntegrand.toFun_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hnn : 0 ≤ Ψ.t i.castSucc := Ψ.nonneg.trans (Ψ.mono (Fin.zero_le _))
  simp only [Set.indicator, Set.mem_Ioc]
  rw [if_neg]
  intro hh
  linarith [hh.1]

theorem s81s_sq_shift {P : Measure Ω} (h : ℝ≥0) {Φ Φh : ℝ → Ω → ι → ℝ} (v₀ : ℝ)
    (hrel : ∀ r : ℝ, 0 < r → ∀ ω k, Φh r ω k = Φ (h + r) ω k)
    (Ψ : SimpleIntegrand (s81b_shiftFil ℱ h) ι) (t : ℝ) :
    sqIntegralOn P (fun s ω => (s81s_shiftSimple h Ψ).toFun s ω - restrictFun Φ h (h + v₀) Set.univ s ω)
        (h + t) =
      sqIntegralOn P (fun r ω => Ψ.toFun r ω - restrictFun Φh 0 v₀ Set.univ r ω) t := by
  unfold sqIntegralOn
  refine lintegral_congr fun ω => ?_
  set g : ℝ → ℝ≥0∞ := fun r => ∑ k, ‖(Ψ.toFun r ω - restrictFun Φh 0 v₀ Set.univ r ω) k‖ₑ ^ 2 with hg
  have hg0 : ∀ r, r ≤ 0 → g r = 0 := by
    intro r hr
    simp only [hg]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 := s81s_simple_zero h Ψ hr ω k
    have h2 : restrictFun Φh 0 v₀ Set.univ r ω k = 0 := by
      have hr' : r ∉ Set.Ioc (0 : ℝ) v₀ := fun hh => by linarith [hh.1]
      simp [restrictFun, hr']
    simp [Pi.sub_apply, h1, h2]
  have e1 : ∀ s : ℝ, (∑ k, ‖((s81s_shiftSimple h Ψ).toFun s ω - restrictFun Φ h (h + v₀) Set.univ s ω) k‖ₑ ^ 2) =
      g (s - h) := by
    intro s
    simp only [hg, Pi.sub_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [s81s_integrand_shift h v₀ hrel Ψ s ω k]
  simp only [Pi.sub_apply] at e1 ⊢
  simp_rw [e1]
  rw [← lintegral_indicator measurableSet_Icc, ← lintegral_indicator measurableSet_Icc]
  have e2 : (Set.Icc (0 : ℝ) (h + t)).indicator (fun s => g (s - h)) =
      fun s => (Set.Icc (0 : ℝ) t).indicator g (s - h) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) (h + t)
    · by_cases hs2 : 0 ≤ s - h
      · have : s - h ∈ Set.Icc (0 : ℝ) t := ⟨hs2, by linarith [hs.2]⟩
        simp [Set.indicator, hs, this]
      · have : g (s - h) = 0 := hg0 _ (by linarith)
        simp [Set.indicator, hs, this]
    · have : s - h ∉ Set.Icc (0 : ℝ) t := fun hh => hs ⟨by linarith [hh.1, h.coe_nonneg], by linarith [hh.2]⟩
      simp [Set.indicator, hs, this]
  rw [e2]
  exact lintegral_sub_right_eq_self ((Set.Icc (0 : ℝ) t).indicator g) (h : ℝ)

end Main


section Shift

variable [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ι → ℝ}

theorem s81s_restrict_ito (hW : IsBrownianFiltration P ℱ W) {Φ : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressiveL2 P ℱ Φ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (restrictFun Φ a b Set.univ) t ω =
      itoIntegral P ℱ W Φ (min t b) ω - itoIntegral P ℱ W Φ (min t a) ω := by
  have h1 := itoIntegral_indicator_Ioc hW hΦ ha hab
  have e : (fun s ω => Set.indicator (Set.Ioc a b) (fun _ => Φ s ω) s) = restrictFun Φ a b Set.univ := by
    funext s ω; simp [restrictFun, Set.indicator]
  rw [e] at h1
  exact h1

/-- **Time shift of the Itô integral.** -/
theorem s81s_ito_shift (hW : IsBrownianFiltration P ℱ W) (h : ℝ≥0) {Φ Φh : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressiveL2 P ℱ Φ) (hΦh : IsProgressiveL2 P (s81b_shiftFil ℱ h) Φh)
    (hrel : ∀ r : ℝ, 0 < r → ∀ ω k, Φh r ω k = Φ (h + r) ω k) :
    ∀ᵐ ω ∂P, ∀ v : ℝ, 0 ≤ v →
      itoIntegral P (s81b_shiftFil ℱ h) (shiftProc W h) Φh v ω =
        itoIntegral P ℱ W Φ (h + v) ω - itoIntegral P ℱ W Φ h ω := by
  have hWh := s81b_isBrownianFiltration_shift hW h
  have key : ∀ N : ℕ, ∀ᵐ ω ∂P, ∀ v : ℝ, 0 ≤ v → v ≤ N →
      itoIntegral P (s81b_shiftFil ℱ h) (shiftProc W h) Φh v ω =
        itoIntegral P ℱ W Φ (h + v) ω - itoIntegral P ℱ W Φ h ω := by
    intro N
    have hv₀ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    set v₀ : ℝ := (N : ℝ) with hv₀def
    have hΦ₀ : IsProgressiveL2 P ℱ (restrictFun Φ h (h + v₀) Set.univ) :=
      hΦ.restrictFun (MeasurableSet.univ : MeasurableSet[ℱ h] Set.univ)
    have hΦh₀ : IsProgressiveL2 P (s81b_shiftFil ℱ h) (restrictFun Φh 0 v₀ Set.univ) :=
      hΦh.restrictFun (MeasurableSet.univ : MeasurableSet[(s81b_shiftFil ℱ h) 0] Set.univ)
    have hM₀ := s81s_restrict_ito hW hΦ (a := h) (b := h + v₀) h.coe_nonneg (by linarith)
    have hNh := s81s_restrict_ito hWh hΦh (a := 0) (b := v₀) le_rfl hv₀
    have hM₀h : ∀ᵐ ω ∂P, itoIntegral P ℱ W (restrictFun Φ h (h + v₀) Set.univ) h ω = 0 := by
      filter_upwards [hM₀] with ω hω
      rw [hω h, min_eq_left (by linarith), min_self, sub_self]
    set Mh : ℝ → Ω → ℝ := fun v ω =>
      itoIntegral P ℱ W (restrictFun Φ h (h + v₀) Set.univ) (h + max v 0) ω -
        itoIntegral P ℱ W (restrictFun Φ h (h + v₀) Set.univ) h ω with hMh
    have hIto : IsItoIntegral P (s81b_shiftFil ℱ h) (shiftProc W h) (restrictFun Φh 0 v₀ Set.univ) Mh := by
      refine isItoIntegral_of_exists_seq hWh hΦh₀ (fun ω => ?_) (fun v => ?_) (fun v hv ω => ?_)
        (fun t ht => ?_)
      · exact ((continuous_itoIntegral P ℱ W _ ω).comp
          (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
      · have h1 : Measurable[ℱ ((h : ℝ) + max v 0)]
            (itoIntegral P ℱ W (restrictFun Φ h (h + v₀) Set.univ) (h + max v 0)) :=
          adapted_itoIntegral P ℱ W _ _
        have h2 : Measurable[ℱ ((h : ℝ) + max v 0)]
            (itoIntegral P ℱ W (restrictFun Φ h (h + v₀) Set.univ) h) :=
          (adapted_itoIntegral P ℱ W _ _).mono (ℱ.mono (by linarith [le_max_right v 0])) le_rfl
        exact h1.sub h2
      · simp only [hMh, max_eq_right hv, add_zero, sub_self]
      · obtain ⟨Ξ, hΞ⟩ := exists_simple_approx P (s81b_shiftFil ℱ h) _ hΦh₀.prog t (hΦh₀.sq t)
        refine ⟨Ξ, hΞ, ?_⟩
        have hΞ' : IsApprox P (restrictFun Φ h (h + v₀) Set.univ) (fun n => s81s_shiftSimple h (Ξ n))
            (h + t) := by
          unfold IsApprox
          have : ∀ n, sqIntegralOn P (fun s ω => (s81s_shiftSimple h (Ξ n)).toFun s ω -
              restrictFun Φ h (h + v₀) Set.univ s ω) (h + t) =
              sqIntegralOn P (fun r ω => (Ξ n).toFun r ω - restrictFun Φh 0 v₀ Set.univ r ω) t :=
            fun n => s81s_sq_shift h v₀ hrel (Ξ n) t
          simpa only [this] using hΞ
        have h1 := (isItoIntegral_itoIntegral hW hΦ₀).approx (h + t)
          (add_nonneg h.coe_nonneg ht) (fun n => s81s_shiftSimple h (Ξ n)) hΞ'
        refine h1.congr fun n => ?_
        refine lintegral_congr_ae ?_
        filter_upwards [hM₀h] with ω hω
        rw [s81s_shiftSimple_elem h (Ξ n) W ht ω]
        simp only [hMh, max_eq_left ht, hω, sub_zero]
    have huniq := hIto.ae_eq_forall hWh (isItoIntegral_itoIntegral hWh hΦh₀) hΦh₀
    filter_upwards [hM₀, hNh, huniq, hM₀h] with ω h1 h2 h3 h4 v hv hvN
    have e1 := h3 v
    have e2 := h2 v
    have e3 : itoIntegral P (s81b_shiftFil ℱ h) (shiftProc W h) Φh (min v v₀) ω = itoIntegral P (s81b_shiftFil ℱ h) (shiftProc W h) Φh v ω := by
      rw [min_eq_left hvN]
    have e4 : itoIntegral P (s81b_shiftFil ℱ h) (shiftProc W h) Φh (min v 0) ω = 0 := by
      rw [min_eq_right hv]
      exact itoIntegral_of_nonpos P (s81b_shiftFil ℱ h) (shiftProc W h) Φh le_rfl ω
    rw [e3, e4, sub_zero] at e2
    rw [← e2, ← e1]
    simp only [hMh, max_eq_left hv, h4, sub_zero]
    rw [h1 (h + v), min_eq_left (by linarith), min_eq_right (by linarith)]
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω v hv
  obtain ⟨N, hN⟩ := exists_nat_ge v
  exact hω N v hv hN

end Shift


end HRS.Whole.S81S
