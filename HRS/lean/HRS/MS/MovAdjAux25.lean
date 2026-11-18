import HRS.MS.MovAdjAux24

/-!
# S6.7 (packet P5, part 2): the derivative bound for `f_r` (core of the stationary row)

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_core`: for `r < t` the classical adjoint solution satisfies the Duhamel formula
`f_r = sg_τ φ + ∫_0^τ sg_{τ-s}(β J f_{t-βs}) ds`, `τ = (t-r)/β`, hence
`‖D^k f_r‖ ≤ (C_1 ∑ Y_i + C_2 β K_J C_sp N) e^{-(μ/2) τ}` for `1 ≤ k ≤ j+1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg HRS.MS.PoisFlow
  HRS.MS.PoisMax

universe w

variable {d : ℕ}

/-- Continuity of `s ↦ sg_{τ-s}(S_s)(x)` on `[0,τ]` from `S67DuhData`. -/
theorem s67_Gc {Ω : Type w} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hBm : HasCbBound m Mb B)
    {T : ℝ} (hT0 : 0 ≤ T) {u a S : ℝ → Euc d → ℝ} (h : S67DuhData q B T u a S) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) (x : Euc d) :
    ContinuousOn (fun s => sg P W q B (τ - s) (S s) x) (Icc 0 τ) := by
  obtain ⟨KS, hKS⟩ := h.Sbd
  have hSc := s67_comp_clamp hT0 h.Scont
  have := s67_cont_sg_comp hW hq hm hBm hT0 (g := fun r y => S (clampT T r) y) hSc (K := |KS|)
    (fun r y => (hKS _ (clampT_mem hT0 r) y).trans (le_abs_self _)) hτ x
  refine this.congr (fun s hs => ?_)
  simp only [clampT_of_mem (⟨hs.1, hs.2.trans hτ.2⟩ : s ∈ Icc (0 : ℝ) T)]

theorem s67_cast_le {a b : ℕ} (h : a ≤ b) : ((a : ℕ) : WithTop ℕ∞) ≤ ((b : ℕ) : WithTop ℕ∞) := by
  exact_mod_cast h

set_option maxHeartbeats 3200000 in
theorem s67_core {s q β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) {B : Euc d → Euc d}
    (hgrad : ∀ x, gradient (fun y => Real.log (ρ y)) x = (-(β * q)) • x + B x)
    (j M : ℕ) {mp : ℕ} {Mb : ℝ} (hmp : mp = max 2 (j + 1))
    (hBm : HasCbBound mp Mb B) (hMb : 0 ≤ Mb)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {cs Csp KJ : ℝ} (hcs : 0 < cs) (hCsp0 : 0 ≤ Csp) (hKJ0 : 0 ≤ KJ)
    (hKJ : ∀ u : Euc d → ℝ, MemCb 2 u → MemOsc (M : ℝ) (s67psi ρ u) →
      ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) u ∧ ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (s67J d s ρ u) ∧
      ∀ i ≤ j + 2, ∀ x, ‖iteratedFDeriv ℝ i (s67J d s ρ u) x‖ ≤ KJ * oscNorm (M : ℝ) (s67psi ρ u))
    (hspec : ∀ (t : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ t →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f →
      MemOsc (M : ℝ) (s67psi ρ φ) → ∀ r ∈ Icc (0 : ℝ) t,
        MemOsc (M : ℝ) (s67psi ρ (f r)) ∧
          oscNorm (M : ℝ) (s67psi ρ (f r)) ≤ Csp * Real.exp (-cs * (t - r)) * oscNorm (M : ℝ) (s67psi ρ φ)) :
    ∃ Csg Cd : ℝ, 0 ≤ Csg ∧ 0 ≤ Cd ∧ ∀ (t : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 < t →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) t φ f →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ → MemOsc (M : ℝ) (s67psi ρ φ) →
      ∀ r ∈ Icc (0 : ℝ) t, r < t → ∀ Y : ℕ → ℝ, (∀ i, 0 ≤ Y i) →
      (∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ (i + 1) φ x‖ ≤ Y i) →
        ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (f r) ∧
        ∀ k, 1 ≤ k → k ≤ j + 1 → ∀ x, ‖iteratedFDeriv ℝ k (f r) x‖ ≤
          (Csg * ∑ i ∈ Finset.range (j + 1), Y i +
            Cd * (β * KJ * Csp * oscNorm (M : ℝ) (s67psi ρ φ))) *
          Real.exp (-(min (pm_c0 (β * q) Mb) (cs * β) / 2) * ((t - r) / β)) := by
  have hq' : 0 < β * q := mul_pos hβ hq
  have hmp2 : 2 ≤ mp := by rw [hmp]; exact le_max_left _ _
  have hmpj : j + 1 ≤ mp := by rw [hmp]; exact le_max_right _ _
  have hmpj2 : mp ≤ j + 2 := by rw [hmp]; exact max_le (by omega) (by omega)
  obtain ⟨Csg, hCsg0, hCsg⟩ := s67_sg_decay.{0} (d := d) (β * q) Mb hq' hMb mp hmp2
  obtain ⟨Cd, hCd0, hCd⟩ := s67_duh_bound.{0} (d := d) (β * q) Mb hq' hMb mp hmp2 (j + 1) (by omega) hmpj
    (b := cs * β) (mul_pos hcs hβ)
  refine ⟨Csg, Cd, hCsg0, hCd0, ?_⟩
  intro t φ f ht hf hφ hosc r hr hrt Y hY0 hYφ
  have hBc : Continuous B := hBm.1.continuous
  have ht0 : 0 ≤ t := ht.le
  set N := oscNorm (M : ℝ) (s67psi ρ φ) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hspecT := hspec t φ f ht0 hf hosc
  have hJ : ∀ v ∈ Icc (0 : ℝ) t, ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (f v) ∧
      ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) (s67J d s ρ (f v)) ∧
      ∀ i ≤ j + 2, ∀ x, ‖iteratedFDeriv ℝ i (s67J d s ρ (f v)) x‖ ≤
        KJ * (Csp * Real.exp (-cs * (t - v)) * N) := by
    intro v hv
    obtain ⟨h1, h2, h3⟩ := hKJ (f v) (hf.isC12TestRd.memCb hv) (hspecT v hv).1
    exact ⟨h1, h2, fun i hi x => (h3 i hi x).trans
      (mul_le_mul_of_nonneg_left (hspecT v hv).2 hKJ0)⟩
  have hSb : ∃ KS : ℝ, ∀ v ∈ Icc (0 : ℝ) t, ∀ y, |s67J d s ρ (f v) y| ≤ KS := by
    refine ⟨KJ * (Csp * N), fun v hv y => ?_⟩
    have h1 := (hJ v hv).2.2 0 (Nat.zero_le _) y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hKJ0)
    have he : Real.exp (-cs * (t - v)) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ t - v := sub_nonneg.2 hv.2
      nlinarith
    calc Csp * Real.exp (-cs * (t - v)) * N ≤ Csp * 1 * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hCsp0) hN0
      _ = Csp * N := by ring
  have hDuh := s67_duhData hd hs0 hsd hq hβ hρ hBc hgrad hf hSb
  have hT : 0 < t / β := div_pos ht hβ
  have hτ0 : 0 ≤ (t - r) / β := div_nonneg (sub_nonneg.2 hr.2) hβ.le
  set τ := (t - r) / β with hτdef
  have hτ : τ ∈ Icc (0 : ℝ) (t / β) :=
    ⟨hτ0, div_le_div_of_nonneg_right (by linarith [hr.1]) hβ.le⟩
  have hτr : t - β * τ = r := by rw [hτdef]; field_simp; ring
  have hduh : ∀ x, f r x = sg P W (β * q) B τ φ x +
      ∫ σ in (0 : ℝ)..τ, sg P W (β * q) B (τ - σ) (fun y => β * s67J d s ρ (f (t - β * σ)) y) x := by
    intro x
    have := s67_duhamel_abs hW (Mb := Mb) hq' hmp2 hBm hDuh hT hτ x
    simp only [mul_zero, sub_zero, hf.terminal, hτr] at this
    exact this
  -- the derivative bounds of `φ`
  obtain ⟨Bφ, hBφ⟩ : ∃ Bφ : ℝ, ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Bφ := by
    obtain ⟨b0, hb0⟩ := hf.bdd 0 (by norm_num)
    obtain ⟨b1, hb1⟩ := hf.bdd 1 (by norm_num)
    obtain ⟨b2, hb2⟩ := hf.bdd 2 (by norm_num)
    have htm : t ∈ Icc (0 : ℝ) t := ⟨ht0, le_rfl⟩
    refine ⟨max (max b0 b1) b2, fun i hi y => ?_⟩
    interval_cases i
    · have := hb0 t htm y; rw [hf.terminal] at this
      exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have := hb1 t htm y; rw [hf.terminal] at this
      exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
    · have := hb2 t htm y; rw [hf.terminal] at this
      exact this.trans (le_max_right _ _)
  have hφmp : ContDiff ℝ (mp : WithTop ℕ∞) φ := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have : mp = 2 := by rw [hmp]; rfl
      rw [this]
      have := hf.c2 t ⟨ht0, le_rfl⟩
      rwa [hf.terminal] at this
    · have : mp = j + 1 := by rw [hmp]; exact max_eq_right (by omega)
      rw [this]; exact hφ
  set Mf : ℕ → ℝ := fun i => if 1 ≤ i ∧ i ≤ j + 1 then Y (i - 1) else Bφ with hMf
  have hMfb : ∀ i ≤ mp, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Mf i := by
    intro i hi y
    by_cases h : 1 ≤ i ∧ i ≤ j + 1
    · simp only [hMf, h, and_self, if_true]
      have := hYφ (i - 1) (by omega) y
      have e : i - 1 + 1 = i := by omega
      rwa [e] at this
    · simp only [hMf, h, if_false]
      refine hBφ i ?_ y
      have : i ≤ max 2 (j + 1) := by rw [← hmp]; exact hi
      by_contra hcon
      push Not at hcon
      apply h
      constructor <;> [omega; (rcases le_max_iff.1 this with h2 | h2 <;> omega)]
  -- `f r` is `C^{j+4}`, `sg φ` is `C^{j+1}`
  have hfr : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (f r) := (hJ r hr).1
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (j + 1), Y i := Finset.sum_nonneg fun i _ => hY0 i
  have hBm' : ∀ i ≤ j + 1, ∀ y, ‖iteratedFDeriv ℝ i φ y‖ ≤ Bφ + ∑ i ∈ Finset.range (j + 1), Y i := by
    intro i hi y
    have h0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0 (by norm_num) 0)
    by_cases h : 1 ≤ i
    · have := hYφ (i - 1) (by omega) y
      have e : i - 1 + 1 = i := by omega
      rw [e] at this
      have h2 : Y (i - 1) ≤ ∑ i ∈ Finset.range (j + 1), Y i :=
        Finset.single_le_sum (f := Y) (fun i _ => hY0 i) (Finset.mem_range.2 (by omega))
      linarith
    · have hi0 : i = 0 := by omega
      subst hi0
      have := hBφ 0 (by norm_num) y
      linarith
  obtain ⟨Cc, -, hCc⟩ := sg_contDiff (d := d) (β * q) Mb hq' mp hmp2 τ hτ0 (j + 1) hmpj
  have hsg : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (sg P W (β * q) B τ φ) :=
    (hCc P W (sgNoise_of_brownian hW) B hBm φ hφ _ hBm' τ ⟨hτ0, le_rfl⟩).1
  set Φ : Euc d → ℝ := fun x => ∫ σ in (0 : ℝ)..τ,
    sg P W (β * q) B (τ - σ) (fun y => β * s67J d s ρ (f (t - β * σ)) y) x with hΦdef
  have hfe : f r = fun x => sg P W (β * q) B τ φ x + Φ x := funext hduh
  have hΦ_eq : Φ = fun x => f r x - sg P W (β * q) B τ φ x := by
    funext x; rw [hduh x]; ring
  have hΦK : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) Φ := by
    rw [hΦ_eq]
    exact (hfr.of_le (s67_cast_le (by omega : j + 1 ≤ j + 4))).sub hsg
  -- the integral term
  have hSdiff : ∀ σ ∈ Icc (0 : ℝ) τ, ContDiff ℝ (mp : WithTop ℕ∞)
      (fun y => β * s67J d s ρ (f (t - β * σ)) y) := by
    intro σ hs
    have hv : t - β * σ ∈ Icc (0 : ℝ) t := s67_hmem hβ ⟨hs.1, hs.2.trans hτ.2⟩
    exact contDiff_const.mul (((hJ _ hv).2.1).of_le (s67_cast_le hmpj2))
  have hSbd : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ i ≤ mp, ∀ y,
      ‖iteratedFDeriv ℝ i (fun y => β * s67J d s ρ (f (t - β * σ)) y) y‖ ≤
        (β * KJ * Csp * N) * Real.exp (-(cs * β) * σ) := by
    intro σ hs i hi y
    have hv : t - β * σ ∈ Icc (0 : ℝ) t := s67_hmem hβ ⟨hs.1, hs.2.trans hτ.2⟩
    have hJd := (hJ _ hv).2.1
    have hi2 : i ≤ j + 2 := hi.trans hmpj2
    have hJi : ContDiffAt ℝ (i : WithTop ℕ∞) (s67J d s ρ (f (t - β * σ))) y :=
      (hJd.of_le (s67_cast_le hi2)).contDiffAt
    have e1 := iteratedFDeriv_const_smul_apply' (a := β) hJi
    have e2 : iteratedFDeriv ℝ i (fun y => β * s67J d s ρ (f (t - β * σ)) y) y =
        β • iteratedFDeriv ℝ i (s67J d s ρ (f (t - β * σ))) y := e1
    rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    have h3 := (hJ _ hv).2.2 i hi2 y
    have e3 : -cs * (t - (t - β * σ)) = -(cs * β) * σ := by ring
    rw [e3] at h3
    calc β * ‖iteratedFDeriv ℝ i (s67J d s ρ (f (t - β * σ))) y‖
        ≤ β * (KJ * (Csp * Real.exp (-(cs * β) * σ) * N)) := mul_le_mul_of_nonneg_left h3 hβ.le
      _ = (β * KJ * Csp * N) * Real.exp (-(cs * β) * σ) := by ring
  have hA0 : 0 ≤ β * KJ * Csp * N := mul_nonneg (mul_nonneg (mul_nonneg hβ.le hKJ0) hCsp0) hN0
  have hΦb := hCd P ℱ W hW B hBm (β * KJ * Csp * N) hA0 τ hτ0
    (fun σ y => β * s67J d s ρ (f (t - β * σ)) y) hSdiff hSbd
    (fun x => s67_Gc hW hq' hmp2 hBm hT.le hDuh hτ x) Φ (fun x => rfl) hΦK
  refine ⟨hfr, fun k hk1 hkK x => ?_⟩
  have hk_mp : k ≤ mp := hkK.trans hmpj
  have hsum : iteratedFDeriv ℝ k (f r) x = iteratedFDeriv ℝ k (sg P W (β * q) B τ φ) x +
      iteratedFDeriv ℝ k Φ x := by
    rw [hfe]
    exact iteratedFDeriv_add_apply (hsg.of_le (s67_cast_le hkK)).contDiffAt (hΦK.of_le (s67_cast_le hkK)).contDiffAt
  have hs1 := hCsg k hk1 hk_mp P ℱ W hW B hBm φ hφmp Mf hMfb τ hτ0 x
  have hSle : ∑ i ∈ Finset.Icc 1 k, Mf i ≤ ∑ i ∈ Finset.range (j + 1), Y i :=
    s67_sum_shift hkK Y hY0 Bφ
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0 (by norm_num) 0)
  have hS1 : 0 ≤ ∑ i ∈ Finset.Icc 1 k, Mf i :=
    Finset.sum_nonneg fun i _ => by
      simp only [hMf]; split_ifs
      · exact hY0 _
      · exact hBφ0
  have hc0 : 0 ≤ pm_c0 (β * q) Mb := s67_pm_c0_nonneg _ _ hq'
  have hμc : min (pm_c0 (β * q) Mb) (cs * β) ≤ pm_c0 (β * q) Mb := min_le_left _ _
  have hμ0 : 0 ≤ min (pm_c0 (β * q) Mb) (cs * β) := le_min hc0 (mul_pos hcs hβ).le
  have hexp : Real.exp (-pm_c0 (β * q) Mb * τ) ≤
      Real.exp (-(min (pm_c0 (β * q) Mb) (cs * β) / 2) * τ) := by
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hτ0 (sub_nonneg.2 hμc), mul_nonneg hτ0 hμ0]
  have hsgb : ‖iteratedFDeriv ℝ k (sg P W (β * q) B τ φ) x‖ ≤
      Csg * Real.exp (-(min (pm_c0 (β * q) Mb) (cs * β) / 2) * τ) * ∑ i ∈ Finset.range (j + 1), Y i := by
    refine hs1.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hexp hCsg0) hSle hS1
      (mul_nonneg hCsg0 (Real.exp_pos _).le)
  calc ‖iteratedFDeriv ℝ k (f r) x‖
      = ‖iteratedFDeriv ℝ k (sg P W (β * q) B τ φ) x + iteratedFDeriv ℝ k Φ x‖ := by rw [hsum]
    _ ≤ ‖iteratedFDeriv ℝ k (sg P W (β * q) B τ φ) x‖ + ‖iteratedFDeriv ℝ k Φ x‖ := norm_add_le _ _
    _ ≤ Csg * Real.exp (-(min (pm_c0 (β * q) Mb) (cs * β) / 2) * τ) * ∑ i ∈ Finset.range (j + 1), Y i +
        Cd * Real.exp (-(min (pm_c0 (β * q) Mb) (cs * β) / 2) * τ) * (β * KJ * Csp * N) :=
        add_le_add hsgb (hΦb k hk1 hkK x)
    _ = _ := by ring

end HRS.MS.MovAdj
