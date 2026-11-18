import HRS.MS.R2MtAux3

/-!
# S11.4 items (2), (3): family version of the tail key estimate of S9.2

`s11_tail_key_fam` is `HRS.MS.R2Mt.s92_tail_key` for a family `(ρ k, D k, P k)` indexed by `k` (kernel parameter × time):
the constants are uniform in `ρ`, and the only `ρ`-dependent input, `‖D k j‖²_{L²(μ_k×μ_k)}`, is controlled by a common
sequence `τ j → 0`.  Then the plain/centred tails `R2ActualFTail`, `R2ActualFTailFam` follow as in `s92_tail`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole HRS.MS.Wr HRS.External HRS.MS.R2Mt

variable {d : ℕ}

theorem s11_tail_key_fam {κ : Type*} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L b p K B r C₁ : ℝ) (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r)
    {ρ : κ → Euc d → ℝ} (hρ : ∀ k, IsRound2Density d s M L (ρ k))
    {P : κ → ∀ N, Measure (EucConfig d N)}
    (hP : ∀ k N, 2 ≤ N → HasR2ActualDensity s b p K (HRS.Whole.withDensityReal (ρ k)) (P k N))
    {D : κ → ℕ → Euc d → Euc d → ℝ} (hD : ∀ k j, IsBoundedPairKernel s (C₁ * B + B) (D k j))
    {τ : ℕ → ℝ≥0∞} (hτ : Tendsto τ atTop (𝓝 0))
    (hτb : ∀ k j, (eLpNorm (fun q : Euc d × Euc d => D k j q.1 q.2) (ENNReal.ofReal 2)
      ((HRS.Whole.withDensityReal (ρ k)).prod (HRS.Whole.withDensityReal (ρ k)))) ^ 2 ≤ τ j)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ j in atTop, ∀ (k : κ) (N : ℕ), 2 ≤ N →
      eLpNorm (fun X : EucConfig d N => (N : ℝ) *
        pairEnergy (D k j) X (HRS.Whole.withDensityReal (ρ k))) (ENNReal.ofReal r) (P k N) ≤
        ENNReal.ofReal θ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hd1 : 1 ≤ d := by omega
  have hcp : 1 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp).symm.lt
  set t : ℝ := r * Real.conjExponent p with ht
  have ht0 : 0 < t := mul_pos (by linarith) (by linarith)
  set m : ℕ := ⌈t⌉₊ with hm
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := lt_of_lt_of_le ht0 (Nat.le_ceil t)
    exact_mod_cast this
  obtain ⟨C2, hC2nn, hC2⟩ := s92_moment_Q hd hs0 hs M L b (C₁ * B + B) hb (2 * m)
  obtain ⟨C0, hC0, hnorm⟩ := s92_normalizer_bounds hd hs0 hs M L b (2 * b) hb (by linarith)
  set K' : ℝ := max K 0 with hK'
  set θ' : ℝ := θ / (K' ^ (1 / r) + 1) with hθ'
  have hθ'0 : 0 < θ' := by positivity
  set ε : ℝ := θ' / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hfT : Tendsto (fun j => 100 * τ j) atTop (𝓝 0) := by
    have h0 : (100 : ℝ≥0∞) * 0 = 0 := by simp
    have := ((ENNReal.continuous_const_mul (by simp : (100 : ℝ≥0∞) ≠ ⊤)).tendsto 0).comp hτ
    rw [h0] at this
    exact this
  have hGT := s92_G_tendsto (c1 := (ENNReal.ofReal C2) ^ (1 / (2 : ℝ))) (c2 := ENNReal.ofReal (Real.exp (3 * C0 / 2)))
    (c3 := ENNReal.ofReal (ε ^ (-2 : ℤ)))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top hfT
  have hcpos : (0 : ℝ≥0∞) < ENNReal.ofReal (θ' ^ m / 2) := ENNReal.ofReal_pos.2 (by positivity)
  filter_upwards [(tendsto_order.1 hGT).2 _ hcpos] with j hj'
  intro k N hN
  haveI hμ := s92_isProb_mu (hρ k).prob
  set μ := HRS.Whole.withDensityReal (ρ k) with hμdef
  have hN0 : 0 < N := by omega
  have hk := hD k j
  obtain ⟨hsec, hint, hHint⟩ := s92_kernel_integrable hd1 hs0 hsd M (hρ k).prob (hρ k).bdd hk
  have hW := (hnorm (ρ k) (hρ k) N hN b ⟨le_rfl, by linarith⟩).1
  have hW2 := (hnorm (ρ k) (hρ k) N hN (2 * b) ⟨by linarith, le_rfl⟩).1
  have hl1 := (hnorm (ρ k) (hρ k) N hN b ⟨le_rfl, by linarith⟩).2
  have hl2 := (hnorm (ρ k) (hρ k) N hN (2 * b) ⟨by linarith, le_rfl⟩).2
  haveI hQprob := s92_isProb_Q (N := N) hW
  haveI hPprob : IsProbabilityMeasure (P k N) := (hP k N hN).1
  have hXm : Measurable (fun X : EucConfig d N => (N : ℝ) * pairEnergy (D k j) X μ) :=
    measurable_const.mul (wr9_measurable_pairEnergy hk.measurable)
  -- second moment under the product measure
  have h2 := s92_second_moment (N := N) hk.measurable hk.symm hsec hint hHint hN0
  rw [s92_S2_eq hk.measurable] at h2
  have h2' := h2.trans (mul_le_mul_right (hτb k j) (100 : ℝ≥0∞))
  -- Q-level pieces
  have hQeq : HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ =
      pairGibbs (fun x y => rieszKernel d s (x - y)) N b μ := rfl
  have hGm := wr9_rieszKernel_pair_meas (d := d) s
  have hψm := s92_dens_meas (μ := μ) (N := N) hGm b
  have hdens := s92_pairGibbs_eq (N := N) hGm hW
  have hmom := hC2 (ρ k) (hρ k) _ hk N hN
  rw [hQeq, hdens] at hmom
  have hA := s92_psi_L2 hW hW2 hl1 hl2
  haveI : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => μ).withDensity (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) := by
    rw [← hdens]; exact hQprob
  have htail := s92_tail_Q (Measure.pi fun _ : Fin N => μ) hψm hXm m hε0 hmom hA
    (s := 100 * τ j) h2'
  have hQmom : ∫⁻ X, ‖(N : ℝ) * pairEnergy (D k j) X μ‖ₑ ^ m
      ∂((Measure.pi fun _ : Fin N => μ).withDensity (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) ≤ ENNReal.ofReal (θ' ^ m) := by
    have hε1 : ε ^ m ≤ θ' ^ m / 2 := by
      rw [hε, div_pow]
      have h2m : (2 : ℝ) ≤ 2 ^ m := le_self_pow₀ (by norm_num) (by omega)
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h2m
    calc _ ≤ _ := htail
      _ ≤ ENNReal.ofReal (θ' ^ m / 2) + ENNReal.ofReal (θ' ^ m / 2) := by
          refine add_le_add ?_ hj'.le
          rw [← ENNReal.ofReal_pow hε0.le]
          exact ENNReal.ofReal_le_ofReal hε1
      _ = ENNReal.ofReal (θ' ^ m) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  have hQb0 := s92_eLpNorm_le_of_moment ((Measure.pi fun _ : Fin N => μ).withDensity (s92_dens (fun x y => rieszKernel d s (x - y)) N b μ)) hXm ht0 m
    (Nat.le_ceil t) (by positivity) hQmom
  have hroot : (θ' ^ m) ^ (1 / (m : ℝ)) = θ' := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hθ'0.le (by omega)
  rw [hroot, ← hdens, ← hQeq] at hQb0
  have hdensP : eLpNorm (fun X => ((P k N).rnDeriv (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) X).toReal)
      (ENNReal.ofReal p) (HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ) ≤ ENNReal.ofReal K' :=
    (hP k N hN).2.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hPb := s92_transfer _ (P k N) (hP k N hN).2.1 hp (le_max_right _ _) hdensP hXm (by linarith : 0 < r) hQb0
  refine hPb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hκ : 0 ≤ K' ^ (1 / r) := by positivity
  rw [hθ', ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

/-- The plain and centred tails, uniformly over a kernel parameter `θ` and the family index `i` (time). -/
theorem s11_tailFam {ι Θ : Type*} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (M L b p K B r C₁ : ℝ) (hb : 0 < b) (hp : 1 < p) (hr : 1 ≤ r)
    {ρ : ι → Euc d → ℝ} (hρ : ∀ i, IsRound2Density d s M L (ρ i))
    {P : ι → ∀ N, Measure (EucConfig d N)}
    (hP : ∀ i N, 2 ≤ N → HasR2ActualDensity s b p K (HRS.Whole.withDensityReal (ρ i)) (P i N))
    {h : Θ → Euc d → Euc d → ℝ} {hj : Θ → ℕ → Euc d → Euc d → ℝ}
    (hD : ∀ θ j, IsBoundedPairKernel s (C₁ * B + B) (fun x y => hj θ j x y - h θ x y))
    {τ : ℕ → ℝ≥0∞} (hτ : Tendsto τ atTop (𝓝 0))
    (hτb : ∀ θ i j, (eLpNorm (fun q : Euc d × Euc d => hj θ j q.1 q.2 - h θ q.1 q.2) (ENNReal.ofReal 2)
      ((HRS.Whole.withDensityReal (ρ i)).prod (HRS.Whole.withDensityReal (ρ i)))) ^ 2 ≤ τ j) :
    Tendsto (fun j => ⨆ (θ : Θ) (i : ι) (N : {N : ℕ // 2 ≤ N}),
      eLpNorm (fun X => ((N : ℕ) : ℝ) * pairEnergy (fun x y => hj θ j x y - h θ x y) X
        (HRS.Whole.withDensityReal (ρ i))) (ENNReal.ofReal r) (P i N)) atTop (𝓝 0) ∧
    Tendsto (fun j => ⨆ (θ : Θ) (i : ι) (N : {N : ℕ // 2 ≤ N}),
      eLpNorm (fun X => ((N : ℕ) : ℝ) * (pairEnergy (fun x y => hj θ j x y - h θ x y) X
        (HRS.Whole.withDensityReal (ρ i)) -
        ∫ Y, pairEnergy (fun x y => hj θ j x y - h θ x y) Y (HRS.Whole.withDensityReal (ρ i)) ∂(P i N)))
        (ENNReal.ofReal r) (P i N)) atTop (𝓝 0) := by
  have hmain := fun θ' (hθ : 0 < θ') => s11_tail_key_fam (κ := Θ × ι) hd hs0 hs M L b p K B r C₁ hb hp hr
    (ρ := fun q => ρ q.2) (fun q => hρ q.2) (P := fun q => P q.2) (fun q N hN => hP q.2 N hN)
    (D := fun q j x y => hj q.1 j x y - h q.1 x y) (fun q j => hD q.1 j) hτ
    (fun q j => hτb q.1 q.2 j) hθ
  have hpe : ∀ (θ : Θ) (i : ι) (j : ℕ) (N : ℕ), 2 ≤ N → Measurable (fun X : EucConfig d N =>
      (N : ℝ) * pairEnergy (fun x y => hj θ j x y - h θ x y) X (HRS.Whole.withDensityReal (ρ i))) :=
    fun θ i j N _ => by
      haveI := s92_isProb_mu (hρ i).prob
      exact measurable_const.mul (wr9_measurable_pairEnergy (hD θ j).measurable)
  constructor
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨θ, hθ, hθε⟩ := s92_exists_real_le hε
    filter_upwards [hmain θ hθ] with j hj'
    exact iSup_le fun θ' => iSup_le fun i => iSup_le fun N => (hj' (θ', i) N.1 N.2).trans hθε
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨θ, hθ, hθε⟩ := s92_exists_real_le hε
    filter_upwards [hmain (θ / 2) (by positivity)] with j hj'
    refine iSup_le fun θ' => iSup_le fun i => iSup_le fun N => ?_
    have hN := N.2
    haveI : IsProbabilityMeasure (P i N.1) := (hP i N.1 hN).1
    have hc := s92_centered_le (P i N.1) (hpe θ' i j N.1 hN) hr (by positivity : (0 : ℝ) ≤ θ / 2)
      (hj' (θ', i) N.1 hN)
    have e : (fun X : EucConfig d N.1 => (N.1 : ℝ) *
        (pairEnergy (fun x y => hj θ' j x y - h θ' x y) X (HRS.Whole.withDensityReal (ρ i)) -
          ∫ Y, pairEnergy (fun x y => hj θ' j x y - h θ' x y) Y (HRS.Whole.withDensityReal (ρ i)) ∂(P i N.1))) =
        fun X => (N.1 : ℝ) * pairEnergy (fun x y => hj θ' j x y - h θ' x y) X (HRS.Whole.withDensityReal (ρ i)) -
          ∫ Y, (N.1 : ℝ) * pairEnergy (fun x y => hj θ' j x y - h θ' x y) Y (HRS.Whole.withDensityReal (ρ i)) ∂(P i N.1) := by
      funext X
      rw [integral_const_mul, mul_sub]
    show eLpNorm (fun X : EucConfig d N.1 => (N.1 : ℝ) *
        (pairEnergy (fun x y => hj θ' j x y - h θ' x y) X (HRS.Whole.withDensityReal (ρ i)) -
          ∫ Y, pairEnergy (fun x y => hj θ' j x y - h θ' x y) Y (HRS.Whole.withDensityReal (ρ i)) ∂(P i N.1)))
        (ENNReal.ofReal r) (P i N.1) ≤ ε
    rw [e]
    refine hc.trans ((le_of_eq ?_).trans hθε)
    congr 1; ring

end HRS.MS.R2S11
