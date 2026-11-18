import HRS.MS.UniqE3f

/-!
# E3 of `UniqPlan.md`, part 7: the commutator remainder bound and mass lemmas

* `e3_rem_i_bound`: `|∫ u · transRem i|` in terms of `M = ∫_S (η_ε*|u|)²`, `∫_S P²`, `∫_S (∂_i P)²`.
* `e3_moll_sq_set_le`: `∫_S (η_ε * w)² ≤ N B²` for `S ⊆ ball e r`, `LocMass B w`.
* `e3_grad_sq_set_le`: `∫_S |∇(η_ε * u)|² ≤ N B²` for `S ⊆ ball e r`, `ulocNormE 1 χ u ≤ B`.
* `e3_integral_le_cellEnergy`, `e3_ball_le_cellEnergy`: real forms of the energy conversion.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

theorem e3_rem_i_bound {b : Euc d → Euc d} {Cb : ℝ} (hdrift : DriftFacts b Cb) (hCb : 0 ≤ Cb)
    {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u) {P : Euc d → ℝ}
    (hP : ContDiff ℝ 1 P) {S : Set (Euc d)} (hS : IsCompact S) (hPS : ∀ x, x ∉ S → P x = 0)
    (i : Fin d) (hDPS : ∀ x, x ∉ S → D1 i P x = 0) :
    |∫ x, u x * transRem d ε b P i x| ≤
      (ε * Cb * ((1 / 2) * (∫ x in S, moll d ε (fun y => ‖u y‖) x ^ 2) +
          (1 / 2) * ∫ x in S, P x ^ 2)) +
        ε * Cb * ((1 / 2) * (∫ x in S, moll d ε (fun y => ‖u y‖) x ^ 2) +
          (1 / 2) * ∫ x in S, D1 i P x ^ 2) := by
  have hPc : HasCompactSupport P := e3_hasCompactSupport_of_zero hS hPS
  have hDP : Continuous (D1 i P) := e3_continuous_D1 hP i
  have hDPc : HasCompactSupport (D1 i P) := e3_hasCompactSupport_of_zero hS hDPS
  have hb1 : ∀ i, ContDiff ℝ 1 (fun y => b y i) := fun i => (hdrift.smooth i).of_le (by norm_num)
  have hli := hu.locallyIntegrable
  have hDb : Continuous (D1 i (fun y => b y i)) := e3_continuous_D1 (hb1 i) i
  have c1 := e3_comm_continuous hε hDb hP.continuous
  have c2 := e3_comm_continuous hε (hb1 i).continuous hDP
  have s1 := e3_comm_hasCompactSupport hε (a := D1 i (fun y => b y i)) hPc
  have s2 := e3_comm_hasCompactSupport hε (a := fun y => b y i) hDPc
  have hsplit : ∫ x, u x * transRem d ε b P i x =
      (∫ x, u x * comm d ε (D1 i (fun y => b y i)) P x) +
        ∫ x, u x * comm d ε (fun y => b y i) (D1 i P) x := by
    unfold transRem
    simp_rw [mul_add]
    exact integral_add (e3_integrable_mul hli c1 s1) (e3_integrable_mul hli c2 s2)
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact e3_comm_integral_bound hε hu hCb (hdrift.lip1 i) hP.continuous hS hPS
  · exact e3_comm_integral_bound hε hu hCb (hdrift.lip0 i) hDP hS hDPS

theorem e3_moll_sq_set_le (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (B : ℝ) (w : Euc d → ℝ), LocMass B w →
      ∀ (e : Euc d) (S : Set (Euc d)), S ⊆ ball e r →
        ∫ x in S, moll d ε w x ^ 2 ≤ N * B ^ 2 := by
  obtain ⟨N, hN⟩ := moll_mass_le_const d r
  refine ⟨N, fun ε hε hε1 B w hw e S hS => ?_⟩
  refine e3_real_sq_le (e3_moll_continuous hε hw.locallyIntegrable) (by positivity) ?_
  rw [← e3_nat_mul_ofReal N]
  exact (lintegral_mono_set hS).trans (hN ε hε hε1 B w hw e)

theorem e3_grad_sq_set_le (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ {χ : Euc d → ℝ}, IsUlocCutoff χ → ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B →
      ulocNormE 1 χ u ≤ ENNReal.ofReal B → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ (e : Euc d) (S : Set (Euc d)), S ⊆ ball e r →
          ∫ x in S, ‖fderiv ℝ (moll d ε u) x‖ ^ 2 ≤ N * B ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := moll_grad_of_ulocNormE d
  obtain ⟨N₁, hN₁⟩ := e3_ball_of_unit d r
  refine ⟨N₁ * N₀, fun {χ} hχ u B hB hu ε hε hε1 e S hS => ?_⟩
  obtain ⟨v, -, -, hv⟩ := hN₀ hχ u B hB hu
  have hlu : LocallyIntegrable u volume := (locMass_of_ulocNormE hχ hB hu).locallyIntegrable
  have hcont : Continuous (fun x => ‖fderiv ℝ (moll d ε u) x‖) :=
    ((moll_contDiff hε hlu).continuous_fderiv (by simp)).norm
  refine e3_real_sq_le hcont (by positivity) ?_
  have h1 := hN₁ (fun x => ‖fderiv ℝ (moll d ε u) x‖ₑ ^ 2)
    ((N₀ : ℝ≥0∞) * ENNReal.ofReal (B ^ 2)) (fun c => (hv ε hε hε1).2 c) e
  have h2 : ∫⁻ x in S, ‖‖fderiv ℝ (moll d ε u) x‖‖ₑ ^ 2 ≤
      (N₁ : ℝ≥0∞) * ((N₀ : ℝ≥0∞) * ENNReal.ofReal (B ^ 2)) := by
    simp only [enorm_norm]
    exact (lintegral_mono_set hS).trans h1
  refine h2.trans (le_of_eq ?_)
  rw [← mul_assoc, ← Nat.cast_mul, e3_nat_mul_ofReal]

theorem e3_integral_le_cellEnergy {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) {w : Euc d → ℝ} (hw : Continuous w)
    (hE : cellEnergy χ Ψ σ w ≠ ⊤) (c : Euc d) :
    ∫ x, varsigma χ Ψ σ c x * w x ^ 2 ≤ (cellEnergy χ Ψ σ w).toReal := by
  have h0 : ∀ x, 0 ≤ varsigma χ Ψ σ c x * w x ^ 2 := fun x =>
    mul_nonneg (hF.range σ hσ c x).1 (sq_nonneg _)
  have hςc : Continuous (varsigma χ Ψ σ c) := (hF.contDiff σ hσ c).continuous
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0)
    (hςc.mul (hw.pow 2)).aestronglyMeasurable]
  exact ENNReal.toReal_mono hE (e3_le_cellEnergy χ Ψ σ w c)

theorem e3_ball_le_cellEnergy {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) t) {r : ℝ} (hr : 0 ≤ r) {w : Euc d → ℝ} (hw : Continuous w)
    (hE : cellEnergy χ Ψ σ w ≠ ⊤) (e : Euc d) :
    ∫ x in closedBall e r, w x ^ 2 ≤ (coverN d Cb t r : ℝ) * (cellEnergy χ Ψ σ w).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
    (hw.pow 2).aestronglyMeasurable]
  have h := e3_cover_ball hF hσ hr hw e
  have hne : (coverN d Cb t r : ℝ≥0∞) * cellEnergy χ Ψ σ w ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hE
  have := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this

end HRS.MS.UniqE3
