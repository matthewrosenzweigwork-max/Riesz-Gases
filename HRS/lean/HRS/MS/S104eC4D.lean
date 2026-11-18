import HRS.MS.S104eC4C

/-!
# S104E route C, packet C4 part D: two-sided derivative of `τ ↦ W τ x` (FTC trick of `ul5_V_hasDerivAt`)

`c4_hasDerivAt`: under the hypotheses of `c4_right` and joint continuity of the jets `i ≤ 2` of `(τ,x) ↦ W τ x`, `τ ↦ W τ x` has the derivative
`ul5A Q ν (W τ) x + g τ x` at every `τ ∈ (0,T)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

theorem c4_val_cont {T : ℝ} {W : ℝ → Euc d → ℝ}
    (h0 : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 0 (W p.1) p.2) (Icc 0 T ×ˢ univ)) (x : Euc d) :
    ContinuousOn (fun τ => W τ x) (Icc 0 T) := by
  have hA := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun _ => 0)).continuous.comp_continuousOn h0
  have hB : ContinuousOn (fun τ : ℝ => (τ, x)) (Icc 0 T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  refine (hA.comp hB (fun τ hτ => ⟨hτ, mem_univ _⟩)).congr fun τ _ => ?_
  simp [iteratedFDeriv_zero_apply]

theorem c4_gen_cont (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {T : ℝ} {W : ℝ → Euc d → ℝ}
    (h1 : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 1 (W p.1) p.2) (Icc 0 T ×ˢ univ))
    (h2 : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 2 (W p.1) p.2) (Icc 0 T ×ˢ univ)) (x : Euc d) :
    ContinuousOn (fun τ => ul5A Q ν (W τ) x) (Icc 0 T) := by
  have hB : ContinuousOn (fun τ : ℝ => (τ, x)) (Icc 0 T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hm : MapsTo (fun τ : ℝ => (τ, x)) (Icc 0 T) (Icc 0 T ×ˢ univ) := fun τ hτ => ⟨hτ, mem_univ _⟩
  have hp := ((h1.comp hB hm).prodMk (h2.comp hB hm))
  have hG := (ul5G_cont2 Q ν).comp_continuousOn ((continuousOn_const : ContinuousOn (fun _ : ℝ => x) (Icc 0 T)).prodMk hp)
  refine hG.congr fun τ _ => ?_
  simp only [Function.comp]
  exact ul5_A_eq Q ν _ _

theorem c4_hasDerivAt (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {T K : ℝ} {g : ℝ → Euc d → ℝ}
    (hG : GFam T K g) {ψ : Euc d → ℝ} (hψc : Continuous ψ) {Bψ : ℝ} (hψb : ∀ y, |ψ y| ≤ Bψ)
    {W : ℝ → Euc d → ℝ} (hW : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, W τ x = ouSg Q ν τ ψ x + Dd Q ν g τ τ x)
    {BW : ℝ} (hW2 : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (W τ) ∧ ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i (W τ) y‖ ≤ BW)
    (hWc : ∀ i ≤ 2, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (W p.1) p.2) (Icc 0 T ×ˢ univ))
    {τ : ℝ} (hτ : τ ∈ Ioo 0 T) (x : Euc d) :
    HasDerivAt (fun τ' => W τ' x) (ul5A Q ν (W τ) x + g τ x) τ := by
  set Vx : ℝ → ℝ := fun τ' => W τ' x with hVx
  set F : ℝ → ℝ := fun τ' => ul5A Q ν (W τ') x + g τ' x with hF
  have hVc : ContinuousOn Vx (Icc 0 T) := c4_val_cont (hWc 0 (Nat.zero_le _)) x
  have hgc : ContinuousOn (fun τ' => g τ' x) (Icc 0 T) := by
    intro σ₀ hσ₀
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hG.cont σ₀ hσ₀ (ε / 2) (by positivity)
    refine ⟨δ, hδ, fun σ hσ hd => ?_⟩
    rw [Real.dist_eq]
    have := h σ hσ (by rwa [← Real.dist_eq]) x
    linarith
  have hFc : ContinuousOn F (Icc 0 T) :=
    (c4_gen_cont Q ν (hWc 1 (by norm_num)) (hWc 2 le_rfl) x).add hgc
  have hint : ∀ b ∈ Icc (0 : ℝ) T, Vx b = Vx 0 + ∫ t in (0 : ℝ)..b, F t := by
    intro b hb
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := Vx) (f' := F) hb.1
      (hVc.mono (Icc_subset_Icc le_rfl hb.2))
      (fun t ht => (c4_right Q hν hG hψc hψb hW hW2 ⟨ht.1.le, ht.2.trans_le hb.2⟩ x).mono
        Ioi_subset_Ici_self)
      ((hFc.mono (Icc_subset_Icc le_rfl hb.2)).intervalIntegrable_of_Icc hb.1)
    linarith
  have hFt : ContinuousAt F τ := hFc.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
  have hmeas : StronglyMeasurableAtFilter F (𝓝 τ) :=
    (hFc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo τ hτ
  have hfi : IntervalIntegrable F volume 0 τ :=
    (hFc.mono (Icc_subset_Icc le_rfl hτ.2.le)).intervalIntegrable_of_Icc hτ.1.le
  have hder := (intervalIntegral.integral_hasDerivAt_right hfi hmeas hFt).const_add (Vx 0)
  refine hder.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with b hb
  exact hint b ⟨hb.1.le, hb.2.le⟩

end HRS.MS.S104e.C
