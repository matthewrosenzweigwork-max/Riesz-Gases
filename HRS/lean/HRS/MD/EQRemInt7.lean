import HRS.MD.EQRemInt6

/-!
# EQ-REM (b), part 7: the integrand `Γ^{t,k}(r, x) = 𝓡_{stat}(U^{r,t} e_k)(x)` is jointly measurable and its `E_M`-energy
is controlled by that of `(𝓡(e_j))_j`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ} {s : ℝ}

/-- The integrand of `statForcingCoord` (set to `0` outside `(0,t)`). -/
def Gam (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ} (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (t : ℝ) (k : NonzeroLattice d) (r : ℝ) (x : Config d N) : ℝ :=
  if r ∈ Set.Ioo 0 t then
    statRemainder d s V β ρβ (N := N) (propagator D ρ r t (Torus.realMode k)) x else 0

theorem eqrem_prop_dual {M : ℝ} (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M) (hdual : Uniform.IsDualEvolution D ρ M Vev)
    {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (k : NonzeroLattice d) (Y : NegSobolev d M) :
    NegSobolev.fourierCoeff (Vev t u Y) k = NegSobolev.eval Y (propagator D ρ u t (Torus.realMode k)) := by
  rw [← eqrem_eval_realMode (Vev t u Y) k]
  exact hdual u t hu hut Y _ (eqrem_isSmooth_realMode k)

section Gam

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) {M : ℝ} (hM : (d : ℝ) / 2 + 2 < M)
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M)
    (hdual : Uniform.IsDualEvolution D ρ M Vev) {K c : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u)))

include hd hs0 hsd hV hβ hρ hN hM hdual hK hdec

/-- Joint measurability of the integrand. -/
theorem eqrem_Gam_meas (t : ℝ) (k : NonzeroLattice d) :
    Measurable (Function.uncurry (Gam d s V β ρβ (N := N) D ρ t k)) := by
  classical
  obtain ⟨f, hfp, hfc, hft⟩ := eqrem_prop_data D ρ t (Torus.realMode k)
  have hRm : ∀ j : NonzeroLattice d, Measurable (statRemainder d s V β ρβ (N := N) (Torus.realMode j)) :=
    fun j => eqrem_statRemainder_meas hd hs0 hsd V hV hβ hρ hN (by
      have := Uniform.Q54c.isCk_realMode j 2
      exact_mod_cast this)
  have hcoef := fun j => eqrem_coeff_meas t f hfc hft j
  -- partial sums
  set S : Finset (NonzeroLattice d) → ℝ × Config d N → ℝ := fun F p =>
    ∑ j ∈ F, (if p.1 ∈ Set.Ioo 0 t then Torus.funRealCoeff (f p.1) j else 0) *
      statRemainder d s V β ρβ (N := N) (Torus.realMode j) p.2 with hS
  have hSm : ∀ F, Measurable (S F) := by
    intro F
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hcoef j).comp measurable_fst).mul ((hRm j).comp measurable_snd)
  have hlim : Tendsto S atTop (𝓝 (Function.uncurry (Gam d s V β ρβ (N := N) D ρ t k))) := by
    rw [tendsto_pi_nhds]
    rintro ⟨r, x⟩
    by_cases hr : r ∈ Set.Ioo 0 t
    · have hSr : ∀ F, S F (r, x) = ∑ j ∈ F, Torus.funRealCoeff (f r) j *
          statRemainder d s V β ρβ (N := N) (Torus.realMode j) x := by
        intro F; simp only [hS, if_pos hr]
      simp_rw [hSr]
      have hκ := hdec r t hr.1.le hr.2.le
      obtain ⟨hsob, -⟩ := eqrem_dual_sobolev (Vev t r) hκ (propagator D ρ r t (Torus.realMode k)) k
        (fun Y => eqrem_prop_dual D ρ Vev hdual hr.1.le hr.2.le k Y)
      rw [hfp r] at hsob
      have := eqrem_stat_expansion hd hs0 hsd V hV hβ hρ hN hM x (hfc r ⟨hr.1.le, hr.2.le⟩) hsob
      have hG : Function.uncurry (Gam d s V β ρβ (N := N) D ρ t k) (r, x) =
          statRemainder d s V β ρβ (N := N) (f r) x := by
        simp only [Function.uncurry, Gam, if_pos hr, hfp r]
      rw [hG]
      exact this
    · have hSr : ∀ F, S F (r, x) = 0 := by
        intro F; simp only [hS, if_neg hr, zero_mul, Finset.sum_const_zero]
      have hG : Function.uncurry (Gam d s V β ρβ (N := N) D ρ t k) (r, x) = 0 := by
        simp [Function.uncurry, Gam, hr]
      simp_rw [hSr]
      rw [hG]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable' atTop hSm hlim

/-- Energy of the integrand: `∑_k ⟨k⟩^{-2M} Γ^{t,k}(r,x)² ≤ ((K+1) e^{-c(t-r)})² ∑_j ⟨j⟩^{-2M} 𝓡(e_j)(x)²`. -/
theorem eqrem_Gam_energy (t r : ℝ) (x : Config d N) :
    coordEnergy M (fun k => Gam d s V β ρβ (N := N) D ρ t k r x) ≤
      ENNReal.ofReal (((K + 1) * Real.exp (-c * (t - r))) ^ 2) *
        coordEnergy M (fun j => statRemainder d s V β ρβ (N := N) (Torus.realMode j) x) := by
  by_cases hr : r ∈ Set.Ioo 0 t
  · have hκ : ‖Vev t r‖ ≤ (K + 1) * Real.exp (-c * (t - r)) :=
      (hdec r t hr.1.le hr.2.le).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
    have hκpos : 0 < (K + 1) * Real.exp (-c * (t - r)) := mul_pos (by linarith) (Real.exp_pos _)
    have hck : ∀ k, Torus.IsCk 2 (propagator D ρ r t (Torus.realMode k)) := by
      intro k
      obtain ⟨f, hfp, hfc, -⟩ := eqrem_prop_data D ρ t (Torus.realMode k)
      rw [hfp r]; exact hfc r ⟨hr.1.le, hr.2.le⟩
    have := eqrem_energy_transfer hd hs0 hsd V hV hβ hρ hN hM (Vev t r) hκ hκpos
      (fun k => propagator D ρ r t (Torus.realMode k)) hck
      (fun k Y => eqrem_prop_dual D ρ Vev hdual hr.1.le hr.2.le k Y) x
    simpa [Gam, hr] using this
  · have h0 : (fun k => Gam d s V β ρβ (N := N) D ρ t k r x) = fun _ => 0 := by
      funext k; simp [Gam, hr]
    rw [h0]
    have : coordEnergy M (fun _ : NonzeroLattice d => (0 : ℝ)) = 0 := by
      unfold coordEnergy; simp
    rw [this]
    exact bot_le

end Gam

end HRS.MD.EQRem

end
