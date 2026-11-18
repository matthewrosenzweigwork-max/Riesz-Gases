import HRS.MS.S104eC4B

/-!
# S104E route C, packet C4 part C: the right derivative of the Duhamel remainder and of `P_τψ + Dd g τ τ`

`c4_R_deriv`: `h ↦ Dd (g(·+τ)) h h x` has right derivative `g τ x` at `h = 0`.
`c4_right`: if `W τ = P_τ ψ + Dd g τ τ` (`ψ` bounded continuous) and `W τ ∈ C²` with bounded jets, then `τ' ↦ W τ' x` has right derivative
`ul5A Q ν (W τ) x + g τ x` at every `τ ∈ [0,T)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

theorem c4_R_deriv (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) {τ : ℝ} (hτ : τ ∈ Ico 0 T) (x : Euc d) :
    HasDerivWithinAt (fun h => Dd Q ν (fun σ => g (σ + τ)) h h x) (g τ x) (Ici 0) 0 := by
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ < T := hτ.2
  have hG' : GFam (T - τ) K (fun σ => g (σ + τ)) :=
    GFam.shift (by rwa [sub_add_cancel]) hτ0
  have hmemτ : τ ∈ Icc (0 : ℝ) T := ⟨hτ0, hτT.le⟩
  have hI : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext y; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hI, Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨δ1, hδ1, hg⟩ := hG.cont τ hmemτ (ε / 4) hε4
  have hgT := ul4_ouSg_cont_time Q hν (hG.c2 τ hmemτ) (M := K) (hG.bd τ hmemτ) x
  have hR0 : Dd Q ν (fun σ => g (σ + τ)) 0 0 x = 0 := by simp [Dd]
  have hg0 := hgT 0 (mem_Ici.2 le_rfl)
  rw [ContinuousWithinAt, ouSg_zero Q hν.le, Metric.tendsto_nhdsWithin_nhds] at hg0
  obtain ⟨δ2, hδ2, hs2⟩ := hg0 (ε / 4) hε4
  have hδ : 0 < min (min δ1 δ2) (T - τ) := lt_min (lt_min hδ1 hδ2) (sub_pos.2 hτT)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  have hh0 : 0 < h := hh.1
  have hhδ1 : h < δ1 := hh.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hhδ2 : h < δ2 := hh.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hhT : h < T - τ := hh.2.trans_le (min_le_right _ _)
  set f : ℝ → ℝ := fun σ => ouSg Q ν (h - σ) (g (σ + τ)) x with hf
  have hfc : ContinuousOn f (Icc 0 h) := c4_phi_cont Q hν hG' x (τ := h) (t0 := h) hhT.le le_rfl
  have hfi : IntervalIntegrable f volume 0 h := hfc.intervalIntegrable_of_Icc hh0.le
  have hbd : ∀ σ ∈ Icc (0 : ℝ) h, ‖f σ - g τ x‖ ≤ ε / 2 := by
    intro σ hσ
    have hσT : σ + τ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hσδ : |σ + τ - τ| < δ1 := by
      rw [add_sub_cancel_right, abs_of_nonneg hσ.1]; linarith [hσ.2]
    have h1 := hg (σ + τ) hσT hσδ
    have hsub : ouSg Q ν (h - σ) (fun y => g (σ + τ) y - g τ y) x =
        ouSg Q ν (h - σ) (g (σ + τ)) x - ouSg Q ν (h - σ) (g τ) x :=
      congrFun (ul3C_sub_lin Q ν (h - σ) (hG.c2 _ hσT).continuous.measurable
        (hG.c2 τ hmemτ).continuous.measurable (fun y => hG.abs hσT y) (fun y => hG.abs hmemτ y)) x
    have hab : |ouSg Q ν (h - σ) (fun y => g (σ + τ) y - g τ y) x| ≤ ε / 4 :=
      ul4_ouSg_abs_le Q ν _ (fun y => h1 y) x
    have hs2' := hs2 (show h - σ ∈ Ici (0 : ℝ) from mem_Ici.2 (by linarith [hσ.2])) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith [hσ.2])]; linarith [hσ.1])
    rw [Real.dist_eq] at hs2'
    rw [Real.norm_eq_abs]
    have : f σ - g τ x = (ouSg Q ν (h - σ) (fun y => g (σ + τ) y - g τ y) x) +
        (ouSg Q ν (h - σ) (g τ) x - g τ x) := by
      rw [hsub]; simp only [hf]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith [hs2']
  have hint : ∫ σ in (0 : ℝ)..h, (f σ - g τ x) =
      Dd Q ν (fun σ => g (σ + τ)) h h x - h * g τ x := by
    rw [intervalIntegral.integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const]
    simp [Dd, hf]
  have hnorm : ‖∫ σ in (0 : ℝ)..h, (f σ - g τ x)‖ ≤ ε / 2 * |h - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [uIoc_of_le hh0.le] at hσ
    exact hbd σ ⟨hσ.1.le, hσ.2⟩
  rw [hint, sub_zero, abs_of_pos hh0] at hnorm
  have hslope : slope (fun h => Dd Q ν (fun σ => g (σ + τ)) h h x) 0 h =
      (Dd Q ν (fun σ => g (σ + τ)) h h x) / h := by
    rw [slope_def_field]; simp [hR0]
  rw [hslope, dist_eq_norm, Real.norm_eq_abs]
  have e : (Dd Q ν (fun σ => g (σ + τ)) h h x) / h - g τ x =
      (Dd Q ν (fun σ => g (σ + τ)) h h x - h * g τ x) / h := by
    field_simp
  rw [e, abs_div, abs_of_pos hh0, div_lt_iff₀ hh0]
  rw [Real.norm_eq_abs] at hnorm
  nlinarith

theorem c4_ouSg_add (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {f g : Euc d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {Bf Bg : ℝ} (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    ouSg Q ν τ (fun x => f x + g x) = fun x => ouSg Q ν τ f x + ouSg Q ν τ g x := by
  funext x
  have hi : ∀ (u : Euc d → ℝ), Measurable u → ∀ B : ℝ, (∀ x, |u x| ≤ B) →
      Integrable (fun y => u (ouExp Q τ x + y)) (ouLaw Q ν τ) := fun u hu B hB =>
    Integrable.of_bound (hu.comp (measurable_const.add measurable_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB _)
  exact integral_add (hi f hf Bf hBf) (hi g hg Bg hBg)

/-- the right derivative of `W τ = P_τ ψ + Dd g τ τ` -/
theorem c4_right (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) {ψ : Euc d → ℝ} (hψc : Continuous ψ) {Bψ : ℝ} (hψb : ∀ y, |ψ y| ≤ Bψ)
    {W : ℝ → Euc d → ℝ} (hW : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, W τ x = ouSg Q ν τ ψ x + Dd Q ν g τ τ x)
    {BW : ℝ} (hW2 : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (W τ) ∧ ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i (W τ) y‖ ≤ BW)
    {τ : ℝ} (hτ : τ ∈ Ico 0 T) (x : Euc d) :
    HasDerivWithinAt (fun τ' => W τ' x) (ul5A Q ν (W τ) x + g τ x) (Ici τ) τ := by
  have hmem : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.le⟩
  have hΦ : HasDerivWithinAt (fun h => ouSg Q ν h (W τ) x) (ul5A Q ν (W τ) x) (Ici 0) 0 :=
    ul5_gen_right Q hν (hW2 τ hmem).1 (M := BW) (hW2 τ hmem).2 x
  have hR := c4_R_deriv Q hν hG hτ x
  have hsum := hΦ.add hR
  have hWb : ∀ y, |W τ y| ≤ BW := fun y => by
    have := (hW2 τ hmem).2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hψm : Measurable (ouSg Q ν τ ψ) := ul4_ouSg_measurable Q ν τ hψc
  have hψτb : ∀ y, |ouSg Q ν τ ψ y| ≤ Bψ := fun y => ul4_ouSg_abs_le Q ν τ hψb y
  have hDeq : (fun y => Dd Q ν g τ τ y) = fun y => W τ y - ouSg Q ν τ ψ y := by
    funext y; rw [hW τ hmem y]; ring
  have hDm : Measurable (fun y => Dd Q ν g τ τ y) := by
    rw [hDeq]; exact (hW2 τ hmem).1.continuous.measurable.sub hψm
  have hDb : ∀ y, |Dd Q ν g τ τ y| ≤ BW + Bψ := fun y => by
    have e : Dd Q ν g τ τ y = W τ y - ouSg Q ν τ ψ y := by rw [hW τ hmem y]; ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (hWb y) (hψτb y))
  have hWτ : W τ = fun y => ouSg Q ν τ ψ y + Dd Q ν g τ τ y := funext fun y => hW τ hmem y
  have key : ∀ h : ℝ, 0 ≤ h → τ + h ≤ T → W (τ + h) x =
      ouSg Q ν h (W τ) x + Dd Q ν (fun σ => g (σ + τ)) h h x := by
    intro h hh hτh
    have hmh : τ + h ∈ Icc (0 : ℝ) T := ⟨by linarith [hτ.1], hτh⟩
    rw [hW _ hmh x]
    have e : ouSg Q ν h (W τ) x = ouSg Q ν (τ + h) ψ x + ouSg Q ν h (fun y => Dd Q ν g τ τ y) x := by
      rw [hWτ, congrFun (c4_ouSg_add Q ν h hψm hDm hψτb hDb) x]
      have := ul4_semigroup Q hν.le hh hτ.1 hψc hψb x
      rw [add_comm τ h, this]
    rw [e, c4_decomp Q hν hG hτ.1 hh hτh x]
    ring
  have hev : (fun h => W (τ + h) x) =ᶠ[𝓝[Ici 0] 0]
      fun h => ouSg Q ν h (W τ) x + Dd Q ν (fun σ => g (σ + τ)) h h x := by
    filter_upwards [Icc_mem_nhdsGE (sub_pos.2 hτ.2)] with h hh
    exact key h hh.1 (by linarith [hh.2])
  have h0 : W (τ + 0) x = ouSg Q ν 0 (W τ) x + Dd Q ν (fun σ => g (σ + τ)) 0 0 x := by
    have := key 0 le_rfl (by linarith [hτ.2])
    simpa using this
  have hV := hsum.congr_of_eventuallyEq hev h0
  have hsub : HasDerivWithinAt (fun τ' : ℝ => τ' - τ) 1 (Ici τ) τ :=
    (hasDerivWithinAt_id τ _).sub_const τ
  have hcomp := HasDerivWithinAt.scomp (g₁ := fun h => W (τ + h) x) τ
    (by simpa using hV) hsub (fun y hy => by simpa using sub_nonneg.2 (mem_Ici.1 hy))
  refine (hcomp.congr_deriv (by simp)).congr (fun y _ => ?_) ?_
  · simp
  · simp

end HRS.MS.S104e.C
