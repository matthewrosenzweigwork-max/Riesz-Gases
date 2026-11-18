import HRS.PDE.MovSXAux6

/-!
# MOVSX Aux7: `movT_source_exp_uniform` (gap (2) of ISSUES "MOV", route (i)), conditional on packets 2 and 7

`movsx_source_exp_uniform_of`: the `ε`-uniform exponential bound for `S^M`, from
* the MOV-A decomposition (`movT_srcReg_decomp`, hypothesis `hdec`) and the uniform Lipschitz bound of `u^r`
  (`movT_traj_bounds`, hypothesis `hbd`), and
* the pressure bound for the regularised kernel `g_M = g_L + q^M - c_0` (`movsx_pressure_param`, `movsx_qM_props`),
  `N:lem:weak-pressure` unchanged, `moments_of_pressure` and `movsx_center_exp`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

set_option maxHeartbeats 1600000 in
theorem movsx_source_exp_uniform_of (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ)
    (hdec : ∃ Cι : ℝ, 0 ≤ Cι ∧ ∀ M : ℝ, 0 ≤ M → ∀ r ∈ Set.Icc 0 T,
      (∀ X : Config d N, |movT_srcReg D N M ρ ρt r X -
          (-(D.invβ⁻¹ * N) * (movT_commReg D N M (ρ r) X -
            ∫ Y, movT_commReg D N M (ρ r) Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)))| ≤
        Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|) ∧
      ∀ L : ℝ, IsLipschitzVF L (mfeTransport D (ρ r)) →
        IsLipschitzVF (L + Cι * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z|)
          (movT_uReg D M (ρ r)))
    (hbd : ∃ c₀ Lu : ℝ, 0 < c₀ ∧ 0 < Lu ∧ (∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x) ∧
      ∀ r ∈ Set.Icc 0 T, IsLipschitzVF Lu (mfeTransport D (ρ r))) :
    ∃ l C M₀ : ℝ, 0 < l ∧ ∀ M : ℝ, M₀ ≤ M → ∀ r ∈ Set.Icc 0 T,
      ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
        ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤ ENNReal.ofReal (Real.exp C) := by
  obtain ⟨Cι, hCι, hdecM⟩ := hdec
  obtain ⟨c₀', Lu, -, hLu, -, hLip⟩ := hbd
  have hd : 1 ≤ d := b15_one_le_d D
  have hs0 := D.hs0
  have hsd := D.hsd
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = D.invβ⁻¹ := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; exact inv_pos.2 htr.pos_temp
  obtain ⟨Λ₂, hΛ₂⟩ := htr.bounds
  obtain ⟨I₀, hI₀def⟩ : ∃ I₀ : ℝ, I₀ = ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s 0 z| :=
    ⟨_, rfl⟩
  have hI₀ : 0 ≤ I₀ := by rw [hI₀def]; exact integral_nonneg fun z => abs_nonneg _
  obtain ⟨L', hL'def⟩ : ∃ L' : ℝ, L' = Lu + Cι * I₀ := ⟨_, rfl⟩
  have hL' : 0 < L' := by rw [hL'def]; have := mul_nonneg hCι hI₀; linarith
  obtain ⟨cstar, A, hA, hw, h0, hdomk⟩ := movsx_hdom hd hs0 hsd
  obtain ⟨g0, hg0⟩ : ∃ g0 : ℝ, g0 = periodicRiesz d D.s 0 := ⟨_, rfl⟩
  obtain ⟨cs, hcsdef⟩ : ∃ cs : ℝ, cs = max cstar (1 - g0) := ⟨_, rfl⟩
  have hcs : ∀ z : Torus d, 1 ≤ periodicRiesz d D.s z + cs := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have : 1 - g0 ≤ cs := by rw [hcsdef]; exact le_max_right _ _
      linarith
    · have := hw z hz; have : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
      linarith
  have hcstar : cstar ≤ cs := by rw [hcsdef]; exact le_max_left _ _
  obtain ⟨Bg0, hBg0⟩ := periodicRiesz_ge_of_one_le (d := d) (s := D.s) hd hs0 hsd
  obtain ⟨Bg, hBgdef⟩ : ∃ Bg : ℝ, Bg = |Bg0| := ⟨_, rfl⟩
  have hBg : 0 ≤ Bg := by rw [hBgdef]; exact abs_nonneg _
  have hBgl : ∀ z : Torus d, -Bg ≤ periodicRiesz d D.s z := fun z => by
    have := hBg0 z; have := le_abs_self Bg0; rw [hBgdef]; linarith
  obtain ⟨E₀, hE₀, hspl⟩ := uniformSplit hd hs0 hsd cs hcs
  obtain ⟨Λ0, hΛ0def⟩ : ∃ Λ0 : ℝ, Λ0 = max Λ₂ 0 := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ0 := by rw [hΛ0def]; exact le_max_right _ _
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 + |cs| + Bg := ⟨_, rfl⟩
  have hκ : 0 ≤ κ := by rw [hκdef]; positivity
  obtain ⟨ε₀, hε₀, hε₀1, hP⟩ := movsx_pressure_param hd D.s hs0 hsd cs hcs β β hβ Λ0 hΛ0 E₀ A κ hE₀ hA hκ
  obtain ⟨Λf, af, q₀, cc, haf, hq₀m, hq₀0, hq₀ev, hq₀int, hq₀ε, hcc, hsplit₀, hq₀env⟩ := hspl ε₀ hε₀ hε₀1
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ, Sa = ∑ k ∈ Λf, af k := ⟨_, rfl⟩
  have hSa0 : 0 ≤ Sa := by rw [hSa]; exact Finset.sum_nonneg haf
  obtain ⟨D', hD'def⟩ : ∃ D' : ℝ, D' = A * (Sa + 1 + |cs|) := ⟨_, rfl⟩
  have hD'0 : 0 ≤ D' := by rw [hD'def]; positivity
  obtain ⟨θ₀, C₁, hθ₀, hC₁, hP2⟩ := hP Λf af q₀ cc D' haf hq₀m hq₀0 hq₀int hq₀ε hcc hD'0 hq₀env
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = θ₀ / (2 * L') := ⟨_, rfl⟩
  have hl : 0 < l := by rw [hldef]; positivity
  have hlL : l * L' = θ₀ / 2 := by rw [hldef]; field_simp
  refine ⟨l, 2 * ((2 * C₁ + 1) * N * deltaN d D.s N) + l * Cι * N * I₀, max Sa 0, hl, ?_⟩
  intro M hM r hr
  have hM0 : 0 ≤ M := (le_max_right _ _).trans hM
  have hSaM : Sa ≤ M := (le_max_left _ _).trans hM
  obtain ⟨hqm, hq0, hqle, hqev, hsplitM⟩ :=
    movsx_qM_props hd hs0 hsd haf hSa hq₀0 hcc hsplit₀ hSaM (M := M)
  set qM := movsx_qM d D.s M cc Λf af with hqMdef
  have hρprob : IsProbDensity (ρ r) := htr.mf.density r hr
  haveI hμprob : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal hρprob
  have hρΛ : ∀ x, ρ r x ≤ Λ0 := fun x =>
    ((movsx_le_cbNorm_two (htr.ck r hr) x).trans (hΛ₂ r hr)).trans (hΛ0def ▸ le_max_left _ _)
  -- Lipschitz bound of the regularised transport field
  obtain ⟨hdecr, hlipr⟩ := hdecM M hM0 r hr
  obtain ⟨hL1i, hL1⟩ := movsx_gReg_L1_le hd hs0 hsd hM0
  have hLipM : IsLipschitzVF L' (movT_uReg D M (ρ r)) := by
    refine movsx_lip_mono (hlipr Lu (hLip r hr)) ?_
    rw [hL'def, ← hI₀def] at *
    have := mul_le_mul_of_nonneg_left hL1 hCι
    linarith
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
    hGdom hsplitM (ρ r) hρprob hρΛ h hhm hsym hhdom henv N hN β ⟨le_rfl, le_rfl⟩
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
    (h := h) hgR hhR (δ := deltaN d D.s N) (C := C₁) (θ₀ := θ₀) (βm := β) (β := β) hδ hC₁ hθ₀ hβ le_rfl hPM
  have hΦm : Measurable (fun X : Config d N => modulatedEnergy h X (withDensityReal (ρ r))) :=
    measurable_modulatedEnergy hhR
  have hQprob : IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r) :=
    movT_QReg_isProb D htr M hr
  have hQdef : movT_Q (b15c_gReg d D.s M) D N ρ r =
      modulatedGibbs (b15c_gReg d D.s M) N β (withDensityReal (ρ r)) := by
    rw [hβdef]; rfl
  rw [← hQdef] at hE
  have htpos : 0 < β * θ₀ * N := by positivity
  have ha0 : 0 ≤ l * L' * β * N := by positivity
  have hat : l * L' * β * N ≤ β * θ₀ * N := by
    rw [hlL]; nlinarith [mul_pos hβ hθ₀, (Nat.cast_nonneg N : (0:ℝ) ≤ N)]
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
  have hIM : ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z| ≤ I₀ := by
    rw [hI₀def]; exact hL1
  have hpt : ∀ X : Config d N, l * |movT_srcReg D N M ρ ρt r X| ≤
      (l * L' * β * N) * |modulatedEnergy h X (withDensityReal (ρ r)) -
        ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)| +
        l * Cι * N * I₀ := by
    intro X
    have h1 := hdecr X
    have hcm : (fun Y => movT_commReg D N M (ρ r) Y) =
        fun Y => L' * modulatedEnergy h Y (withDensityReal (ρ r)) := funext hCΦ
    rw [hcm, integral_const_mul, hCΦ X, ← hβdef] at h1
    set Φx := modulatedEnergy h X (withDensityReal (ρ r))
    set m := ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)
    have h2 : |movT_srcReg D N M ρ ρt r X| ≤ β * N * L' * |Φx - m| + Cι * N * I₀ := by
      have h3 : |-(β * N) * (L' * Φx - L' * m)| = β * N * L' * |Φx - m| := by
        rw [show -(β * N) * (L' * Φx - L' * m) = -(β * N * L') * (Φx - m) by ring, abs_mul, abs_neg,
          abs_of_nonneg (by positivity)]
      have h4 : Cι * N * ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z| ≤ Cι * N * I₀ :=
        mul_le_mul_of_nonneg_left hIM (by positivity)
      have h5 := abs_sub_abs_le_abs_sub (movT_srcReg D N M ρ ρt r X) (-(β * N) * (L' * Φx - L' * m))
      linarith
    calc l * |movT_srcReg D N M ρ ρt r X| ≤ l * (β * N * L' * |Φx - m| + Cι * N * I₀) :=
          mul_le_mul_of_nonneg_left h2 hl.le
      _ = (l * L' * β * N) * |Φx - m| + l * Cι * N * I₀ := by ring
  have hmain : ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
      ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) ≤
      ENNReal.ofReal (Real.exp (2 * ((2 * C₁ + 1) * N * deltaN d D.s N))) *
        ENNReal.ofReal (Real.exp (l * Cι * N * I₀)) := by
    calc ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N M ρ ρt r X|))
          ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)
        ≤ ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l * L' * β * N) *
            |modulatedEnergy h X (withDensityReal (ρ r)) -
              ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)|))
            * ENNReal.ofReal (Real.exp (l * Cι * N * I₀)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := by
          refine lintegral_mono fun X => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hpt X]))
      _ = (∫⁻ X : Config d N, ENNReal.ofReal (Real.exp ((l * L' * β * N) *
            |modulatedEnergy h X (withDensityReal (ρ r)) -
              ∫ X', modulatedEnergy h X' (withDensityReal (ρ r)) ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)|))
            ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) * ENNReal.ofReal (Real.exp (l * Cι * N * I₀)) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  refine hmain.trans ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

end HRS

end
