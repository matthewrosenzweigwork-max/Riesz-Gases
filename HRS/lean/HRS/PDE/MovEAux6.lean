import HRS.PDE.MovAFinal
import HRS.PDE.MovCAux1
import HRS.PDE.MovSpec2

/-!
# MOVE Aux6: `movT_source_exp_scaled_uniform` (scaled exponential bound, `L`-uniform), for `0 < T`

The scaled version of `movsx_source_exp_uniform_of`: the commutator kernel is divided by `2 L(r)` (a Lipschitz bound of
`u^M` once the one-body remainder `Cι ‖g - g_M‖_{L¹} ≤ ℓ`), the pressure estimate is applied to the divided kernel (its
constants `θ₀, C₁` depend only on `d, s, βm, βp, Λ₂`), and the one-body remainder is `≤ 1` for `M ≥ M₀(ℓ, N)`.
The statement is FALSE for `T = 0` (`ρt 0` arbitrary since `IsC12Test.time_deriv` is vacuous on `Ioo 0 0`, while the
constants are uniform in `ρt`); `0 < T` is added.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem move_gReg_L1_small (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → 0 ≤ M →
      ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s M z| ≤ ε := by
  by_contra hcon
  push Not at hcon
  choose f hf using hcon
  have hM : Tendsto (fun n : ℕ => f n) atTop atTop :=
    tendsto_atTop_mono (fun n => (hf n).1) tendsto_natCast_atTop_atTop
  have h := movc_gReg_L1_tendsto hd hs0 hsd hM (fun n => (hf n).2.1)
  have := (h.eventually (gt_mem_nhds hε)).exists
  obtain ⟨n, hn⟩ := this
  exact absurd (hf n).2.2 (not_lt.2 hn.le)

set_option maxHeartbeats 1600000 in
theorem move_source_exp_scaled_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (c₀ : ℝ) (hc₀ : 0 < c₀) (Λ₂ : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}, MovTraj D T ρ →
      IsC12Test T ρ ρt → 0 < T → D.s = s → D.invβ⁻¹ ∈ Set.Icc βm βp →
      (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) → (∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) →
      ∀ {ℓ : ℝ} (L : ℝ → ℝ), 0 < ℓ →
        (∀ r ∈ Set.Icc 0 T, ℓ ≤ L r ∧ IsLipschitzVF (L r) (mfeTransport D (ρ r))) →
        ∀ N : ℕ, 2 ≤ N → MovSrcScaled D N ρ ρt T c (C * N * deltaN d s N) L := by
  obtain ⟨cstar, A, hA, hw, h0, hdomk⟩ := movsx_hdom hd hs0 hsd
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = periodicRiesz d s 0 := ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = max cstar (1 - g0) := ⟨_, rfl⟩
  have hcs : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have : 1 - g0 ≤ cs := by rw [hcsdef]; exact le_max_right _ _
      linarith
    · have := hw z hz; have : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
      linarith
  have hcstar : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
  obtain ⟨Bg0, hBg0⟩ := periodicRiesz_ge_of_one_le (d := d) (s := s) hd hs0 hsd
  obtain ⟨Bg, hBgdef⟩ : ∃ Bg : ℝ, Bg = |Bg0| := ⟨_, rfl⟩
  have hBg : 0 ≤ Bg := by rw [hBgdef]; exact abs_nonneg _
  have hBgl : ∀ z : Torus d, -Bg ≤ periodicRiesz d s z := fun z => by
    have := hBg0 z; have := le_abs_self Bg0; rw [hBgdef]; linarith
  obtain ⟨E₀, hE₀, hspl⟩ := uniformSplit hd hs0 hsd cs hcs
  obtain ⟨Λ0, hΛ0def⟩ : ∃ Λ0 : ℝ, Λ0 = max Λ₂ 0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ0 := by rw [hΛ0def]; exact le_max_right _ _
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 + |cs| + Bg := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by rw [hκdef]; positivity
  obtain ⟨ε₀, hε₀, hε₀1, hP⟩ := movsx_pressure_param hd s hs0 hsd cs hcs βm βp hβm Λ0 hΛ0 E₀ A κ hE₀ hA hκ
  obtain ⟨Λf, af, q₀, cc, haf, hq₀m, hq₀0, hq₀ev, hq₀int, hq₀ε, hcc, hsplit₀, hq₀env⟩ := hspl ε₀ hε₀ hε₀1
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ, Sa = ∑ k ∈ Λf, af k := ⟨_, rfl⟩
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg haf
  obtain ⟨D', hD'def⟩ : ∃ D' : ℝ, D' = A * (Sa + 1 + |cs|) := ⟨_, rfl⟩
  have hD'0 : 0 ≤ D' := by rw [hD'def]; positivity
  obtain ⟨θ₀, C₁, hθ₀, hC₁, hP2⟩ := hP Λf af q₀ cc D' haf hq₀m hq₀0 hq₀int hq₀ε hcc hD'0 hq₀env
  obtain ⟨cS, hcSdef⟩ : ∃ cS : ℝ, cS = βm * θ₀ / (2 * (|βp| + 1)) := ⟨_, rfl⟩
  have hcS : 0 < cS := by rw [hcSdef]; positivity
  have hcS2 : cS * (2 * (|βp| + 1)) = βm * θ₀ := by rw [hcSdef]; field_simp
  refine ⟨cS, 2 * (2 * C₁ + 1) + 1, hcS, ?_⟩
  intro D T ρ ρt htr hρt hT hDs hβI hc0 hΛ ℓ L hℓ hL N hN
  subst hDs
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = D.invβ⁻¹ := ⟨_, rfl⟩
  have hβ' : β ∈ Set.Icc βm βp := hβdef ▸ hβI
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ'.1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨Cι, hCι, hdecM⟩ := movT_srcReg_decomp_proof_pos hN htr hρt hT
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = ℓ / ((Cι + 1) * (cS + 1) * (N + 1)) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁key : ε₁ * ((Cι + 1) * (cS + 1) * (N + 1)) = ℓ := by rw [hε₁def]; field_simp
  obtain ⟨M₁, hM₁⟩ := move_gReg_L1_small hd hs0 hsd hε₁
  unfold MovSrcScaled
  refine ⟨max (max Sa 0) M₁, ?_⟩
  intro M hM r hr
  have hM0 : 0 ≤ M := (le_max_right Sa 0).trans ((le_max_left _ _).trans hM)
  have hSaM : Sa ≤ M := (le_max_left Sa 0).trans ((le_max_left _ _).trans hM)
  have hM1 : M₁ ≤ M := (le_max_right _ _).trans hM
  obtain ⟨IM, hIMdef⟩ : ∃ IM : ℝ, IM = ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z| :=
    ⟨_, rfl⟩
  have hIM0 : 0 ≤ IM := by rw [hIMdef]; exact integral_nonneg fun z => abs_nonneg _
  have hIM : IM ≤ ε₁ := by rw [hIMdef]; exact hM₁ M hM1 hM0
  have hLr := hL r hr
  have hLpos : 0 < L r := hℓ.trans_le hLr.1
  have hCIl : Cι * IM ≤ ℓ := by
    have h1 : Cι * IM ≤ Cι * ε₁ := mul_le_mul_of_nonneg_left hIM hCι
    have h2 : Cι * ε₁ ≤ (Cι + 1) * (cS + 1) * (N + 1) * ε₁ := by
      refine mul_le_mul_of_nonneg_right ?_ hε₁.le
      nlinarith [mul_nonneg hCι hcS.le, mul_nonneg hCι hN0, mul_nonneg hcS.le hN0,
        mul_nonneg (mul_nonneg hCι hcS.le) hN0]
    nlinarith [hε₁key]
  have hCcl : cS * (Cι * N * IM) ≤ ℓ := by
    have h1 : cS * (Cι * N * IM) ≤ cS * (Cι * N * ε₁) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIM (by positivity)) hcS.le
    have h2 : cS * (Cι * N * ε₁) ≤ (Cι + 1) * (cS + 1) * (N + 1) * ε₁ := by
      calc cS * (Cι * N * ε₁) = (cS * Cι * N) * ε₁ := by ring
        _ ≤ (Cι + 1) * (cS + 1) * (N + 1) * ε₁ := by
          refine mul_le_mul_of_nonneg_right ?_ hε₁.le
          nlinarith [mul_nonneg hCι hcS.le, mul_nonneg hCι hN0, mul_nonneg hcS.le hN0,
            mul_nonneg (mul_nonneg hCι hcS.le) hN0]
    nlinarith [hε₁key]
  obtain ⟨L', hL'def⟩ : ∃ L' : ℝ, L' = 2 * L r := ⟨_, rfl⟩
  have hL' : 0 < L' := by rw [hL'def]; positivity
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = cS / L r := ⟨_, rfl⟩
  have hl : 0 < l := by rw [hldef]; positivity
  have hlL : l * L' = 2 * cS := by rw [hldef, hL'def]; field_simp
  obtain ⟨hqm, hq0, hqle, hqev, hsplitM⟩ :=
    movsx_qM_props hd hs0 hsd haf hSa hq₀0 hcc hsplit₀ hSaM (M := M)
  set qM := movsx_qM d D.s M cc Λf af with hqMdef
  have hρprob : IsProbDensity (ρ r) := htr.mf.density r hr
  haveI hμprob : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal hρprob
  have hρΛ : ∀ x, ρ r x ≤ Λ0 := fun x =>
    ((movsx_le_cbNorm_two (htr.ck r hr) x).trans (hΛ r hr)).trans (hΛ0def ▸ le_max_left _ _)
  -- Lipschitz bound of the regularised transport field
  obtain ⟨hdecr, hlipr⟩ := hdecM M hM0 r hr
  have hLipM : IsLipschitzVF L' (movT_uReg D M (ρ r)) := by
    refine movsx_lip_mono (hlipr (L r) hLr.2) ?_
    rw [hL'def, ← hIMdef]
    linarith [hLr.1, hCIl]
  set v := movT_uReg D M (ρ r) with hvdef
  have hv : Continuous v := Commutator.IsLipschitzVF.continuous hL'.le hLipM
  have hk := hdomk L' v hL'.le hLipM
  obtain ⟨h, hhdef⟩ : ∃ h : Torus d → Torus d → ℝ, h = fun x y =>
      L'⁻¹ * (movsx_lam d D.s M (x - y) * commKernel (periodicRieszGrad d D.s) v x y) := ⟨_, rfl⟩
  have hhm : Measurable (Function.uncurry h) := by
    rw [hhdef]
    exact measurable_const.mul ((((movsx_lam_measurable hd hs0 hsd M).comp
      (measurable_fst.sub measurable_snd))).mul (Q40b.q40b_commKernel_meas hsd hv))
  have hsym : ∀ x y, h x y = h y x := by
    intro x y
    rw [hhdef]; simp only
    rw [Q40b.q40b_commKernel_symm hsd v x y, ← neg_sub x y, movsx_lam_neg]
  have hhdom0 : ∀ x y, |h x y| ≤ A * (periodicRiesz d D.s (x - y) + cstar) := by
    intro x y
    rw [hhdef]; simp only
    rw [abs_mul, abs_of_pos (inv_pos.2 hL'), abs_mul, abs_of_nonneg (movsx_lam_nonneg D.s M _)]
    have hl1 := movsx_lam_le_one (d := d) D.s M (x - y)
    have hl0 := movsx_lam_nonneg (d := d) D.s M (x - y)
    calc L'⁻¹ * (movsx_lam d D.s M (x - y) * |commKernel (periodicRieszGrad d D.s) v x y|)
        ≤ L'⁻¹ * (1 * ((A * L') * (periodicRiesz d D.s (x - y) + cstar))) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hL').le
          exact mul_le_mul hl1 (hk x y) (abs_nonneg _) zero_le_one
      _ = A * (periodicRiesz d D.s (x - y) + cstar) := by field_simp
  have hhdom : ∀ x y, |h x y| ≤ A * (periodicRiesz d D.s (x - y) + cs) := fun x y =>
    (hhdom0 x y).trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  have hhnn : ∀ x y, 0 ≤ A * qM (x - y) + D' := fun x y => by
    have := hq0 (x - y); positivity
  have henv : ∀ x y, |h x y| ≤ A * qM (x - y) + D' := by
    intro x y
    by_cases hxy : x = y
    · have : h x y = 0 := by rw [hhdef]; simp [hxy, commKernel]
      rw [this, abs_zero]; exact hhnn x y
    · have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
      by_cases hbig : M + 1 ≤ periodicRiesz d D.s (x - y)
      · have : h x y = 0 := by rw [hhdef]; simp [movsx_lam_eq_zero D.s M hbig]
        rw [this, abs_zero]; exact hhnn x y
      · push Not at hbig
        have h1 := hhdom0 x y
        have hmin := b15c_min_le_trunc M (periodicRiesz d D.s (x - y))
        rw [← b15c_gReg_of_ne D.s M hz] at hmin
        have hgl : periodicRiesz d D.s (x - y) ≤ b15c_gReg d D.s M (x - y) + 1 := by
          rcases le_total (periodicRiesz d D.s (x - y)) M with hh | hh
          · rw [min_eq_left hh] at hmin; linarith
          · rw [min_eq_right hh] at hmin; linarith
        have hsp := hsplitM (x - y) hz
        have hcosle : ∑ k ∈ Λf, af k * Torus.cosMode k (x - y) ≤ Sa := by
          refine (le_abs_self _).trans ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [hSa]
          refine Finset.sum_le_sum fun k hk => ?_
          rw [abs_mul, abs_of_nonneg (haf k hk)]
          exact mul_le_of_le_one_right (haf k hk) (abs_cosMode_le k _)
        have h2 : periodicRiesz d D.s (x - y) + cstar ≤ qM (x - y) + (Sa + 1 + |cs|) := by
          have := le_abs_self cs
          have hq00 := hq0 (x - y)
          linarith
        calc |h x y| ≤ A * (periodicRiesz d D.s (x - y) + cstar) := h1
          _ ≤ A * (qM (x - y) + (Sa + 1 + |cs|)) := mul_le_mul_of_nonneg_left h2 hA
          _ = A * qM (x - y) + D' := by rw [hD'def]; ring
  have hGdom : ∀ z : Torus d, z ≠ 0 →
      |b15c_gReg d D.s M z| ≤ κ * (periodicRiesz d D.s z + cs) := by
    intro z hz
    have h1 := hcs z
    have hle := b15c_gReg_le (d := d) D.s M hz
    have hge := b15c_gReg_ge D.s hBg hM0 hBgl z
    have h2 : |periodicRiesz d D.s z| ≤ (periodicRiesz d D.s z + cs) + |cs| := by
      have := le_abs_self cs
      have := neg_abs_le cs
      rw [abs_le]; constructor <;> linarith [neg_abs_le (periodicRiesz d D.s z), le_abs_self (periodicRiesz d D.s z)]
    have h3 : |b15c_gReg d D.s M z| ≤ |periodicRiesz d D.s z| + Bg := by
      rw [abs_le]; constructor
      · linarith [abs_nonneg (periodicRiesz d D.s z)]
      · linarith [le_abs_self (periodicRiesz d D.s z)]
    rw [hκdef]
    nlinarith [abs_nonneg cs]
  have hPM := hP2 (b15c_gReg d D.s M) qM (movsx_gReg_continuous hd hs0 hsd M).measurable hqm hq0 hqle hqev
    hGdom hsplitM (ρ r) hρprob hρΛ h hhm hsym hhdom henv N hN β hβ'
  -- row bounds and the moment bound
  have hgi : Integrable (periodicRiesz d D.s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  have hwi : Integrable (fun z => periodicRiesz d D.s z + cs) := hgi.add (integrable_const cs)
  have hhR : RowOK (withDensityReal (ρ r)) h :=
    (rowOK_of_dom hΛ0 hρΛ (hwi.const_mul A) hhm hhdom).1
  obtain ⟨Kg, hKg⟩ := b15_bounded_of_continuous (movsx_gReg_continuous hd hs0 hsd M)
  have hgR : RowOK (withDensityReal (ρ r)) (fun x y => b15c_gReg d D.s M (x - y)) :=
    (rowOK_of_dom hΛ0 hρΛ (integrable_const Kg)
      (show Measurable (Function.uncurry fun x y : Torus d => b15c_gReg d D.s M (x - y)) from
        (movsx_gReg_continuous hd hs0 hsd M).measurable.comp (measurable_fst.sub measurable_snd))
      (fun x y => hKg _)).1
  have hδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN hs0 N (by omega)
  obtain ⟨hE, -⟩ := moments_of_pressure (N := N) (μ := withDensityReal (ρ r)) (g := b15c_gReg d D.s M)
    (h := h) hgR hhR (δ := deltaN d D.s N) (C := C₁) (θ₀ := θ₀) (βm := βm) (β := β) hδ hC₁ hθ₀ hβm hβ'.1 hPM
  have hΦm : Measurable (fun X : Config d N => modulatedEnergy h X (withDensityReal (ρ r))) :=
    measurable_modulatedEnergy hhR
  have hQprob : IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) :=
    movT_QReg_isProb D htr M hr
  have hQdef : movT_Q (b15c_gReg d D.s M) D N ρ r =
      modulatedGibbs (b15c_gReg d D.s M) N β (withDensityReal (ρ r)) := by
    rw [hβdef]; rfl
  rw [← hQdef] at hE
  have htpos : 0 < βm * θ₀ * N := by positivity
  have ha0 : 0 ≤ l * L' * β * N := by positivity
  have hβle : β ≤ |βp| + 1 := hβ'.2.trans ((le_abs_self βp).trans (by linarith))
  have hat : l * L' * β * N ≤ βm * θ₀ * N := by
    calc l * L' * β * N = (2 * cS) * β * N := by rw [hlL]
      _ ≤ (2 * cS) * (|βp| + 1) * N := by gcongr
      _ = βm * θ₀ * N := by rw [← hcS2]; ring
  obtain ⟨-, hcen⟩ := movsx_center_exp (movT_Q (b15c_gReg d D.s M) D N ρ r) hΦm htpos ha0 hat
    (K := (2 * C₁ + 1) * N * deltaN d D.s N) hE
  -- `C^M = L' Φ`
  have hCΦ : ∀ X : Config d N, movT_commReg D N M (ρ r) X =
      L' * modulatedEnergy h X (withDensityReal (ρ r)) := by
    intro X
    unfold movT_commReg
    have : commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M (ρ r)) =
        fun x y => L' * h x y := by
      funext x y
      rw [movsx_commKernel_gReg hd hs0 hsd M v x y, hhdef]
      simp only
      rw [mul_inv_cancel_left₀ hL'.ne']
    rw [this, modulatedEnergy_smul]
    exact hhR
  have hpt : ∀ X : Config d N, l * |movT_srcReg D N M ρ ρt r X| ≤
      (l * L' * β * N) * |modulatedEnergy h X (withDensityReal (ρ r)) -
        ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)| +
        l * Cι * N * IM := by
    intro X
    have h1 := hdecr X
    have hcm : (fun Y => movT_commReg D N M (ρ r) Y) =
        fun Y => L' * modulatedEnergy h Y (withDensityReal (ρ r)) := funext hCΦ
    rw [hcm, integral_const_mul, hCΦ X, ← hβdef] at h1
    set Φx := modulatedEnergy h X (withDensityReal (ρ r))
    set m := ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)
    have h2 : |movT_srcReg D N M ρ ρt r X| ≤ β * N * L' * |Φx - m| + Cι * N * IM := by
      have h3 : |-(β * N) * (L' * Φx - L' * m)| = β * N * L' * |Φx - m| := by
        rw [show -(β * N) * (L' * Φx - L' * m) = -(β * N * L') * (Φx - m) by ring, abs_mul, abs_neg,
          abs_of_nonneg (by positivity)]
      have h4 : Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z| ≤ Cι * N * IM := by
        rw [← hIMdef]
      have h5 := abs_sub_abs_le_abs_sub (movT_srcReg D N M ρ ρt r X) (-(β * N) * (L' * Φx - L' * m))
      linarith
    calc l * |movT_srcReg D N M ρ ρt r X| ≤ l * (β * N * L' * |Φx - m| + Cι * N * IM) :=
          mul_le_mul_of_nonneg_left h2 hl.le
      _ = (l * L' * β * N) * |Φx - m| + l * Cι * N * IM := by ring
  have hmain : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
      ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤
      ENNReal.ofReal (Real.exp (2 * ((2 * C₁ + 1) * N * deltaN d D.s N))) *
        ENNReal.ofReal (Real.exp (l * Cι * N * IM)) := by
    calc ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)
        ≤ ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l * L' * β * N) *
            |modulatedEnergy h X (withDensityReal (ρ r)) -
              ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)|))
            * ENNReal.ofReal (Real.exp (l * Cι * N * IM)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := by
          refine lintegral_mono fun X => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hpt X]))
      _ = (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l * L' * β * N) *
            |modulatedEnergy h X (withDensityReal (ρ r)) -
              ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)|))
            ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) * ENNReal.ofReal (Real.exp (l * Cι * N * IM)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hlC : l * Cι * N * IM ≤ 1 := by
    have e : l * Cι * N * IM = (cS * (Cι * N * IM)) / L r := by rw [hldef]; field_simp
    rw [e, div_le_one hLpos]; exact hCcl.trans hLr.1
  have hfin : ENNReal.ofReal (Real.exp (2 * ((2 * C₁ + 1) * N * deltaN d D.s N))) *
      ENNReal.ofReal (Real.exp (l * Cι * N * IM)) ≤
      ENNReal.ofReal (Real.exp ((2 * (2 * C₁ + 1) + 1) * N * deltaN d D.s N)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith [hδ, hlC]
  have hrw : ∀ X : Config d N, cS * |movT_srcReg D N M ρ ρt r X| / L r =
      l * |movT_srcReg D N M ρ ρt r X| := fun X => by rw [hldef]; ring
  refine (le_of_eq (lintegral_congr fun X => ?_)).trans (hmain.trans hfin)
  rw [hrw]

end HRS

end
