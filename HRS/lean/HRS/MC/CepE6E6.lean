import HRS.MC.CepE6E4
import HRS.MC.CepE6E5

/-!
# Packet CEPE6E, file 6: the deterministic final estimate (S7, pathwise part)

* `cepe6e_det_final`: given the Itô identities `∫⟨v_ε(Zs_i), b_i⟩ = boundary terms + M_i` with `|M_i| ≤ B`, the singular part
  `R_T = A(T) - ∫_0^T ∇Φ(Zl)` satisfies
  `½‖R_T‖ ≤ N² ε + |∫⟨v_ε(Zl),F(Zl)⟩| + σ'² |∫ Σ χ''_ε| + B + ∫ |⟨v_ε(Zl), ∇Φ(Zl)⟩|`.
* `cepe6e_Dterms_tendsto`: the explicit terms tend to `0` as `ε → 0` (dominated convergence; this is where
  `∫ ds/m_p < ∞` kills the local time).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {N : ℕ}

theorem gg_continuous (ε : ℝ) : Continuous (gg (N := N) ε) := (gg_contDiff ε).continuous

theorem vv_continuous (ε : ℝ) : Continuous (vv (N := N) ε) := (vv_contDiff ε).continuous

theorem cepe6e_det_final {a : ℝ} {J : ℝ → Ch N → Ch N} {T : ℝ} {nn : ℕ → ℝ} {Zs : ℕ → ℝ → Ch N}
    {Zl : ℝ → Ch N} (D : Det a J T nn Zs Zl) (hN : 1 ≤ N) {A : ℝ → Ch N}
    (hA : TendstoUniformlyOn (fun i t => ∫ s in (0 : ℝ)..t, bF J nn Zs i s) A atTop (Icc 0 T))
    {K : ℝ} (hK : ∀ᶠ i in atTop, ∫ s in (0 : ℝ)..T, ‖bF J nn Zs i s‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) {σ' : ℝ} {z0 : Ch N} (hz0 : z0 ∈ cep_Alcove N)
    {F : Ch N → Ch N} (hF : Continuous F) {M : ℕ → ℝ} {B : ℝ} (hM : ∀ᶠ i in atTop, |M i| ≤ B)
    (hIto : ∀ i, ∫ s in (0 : ℝ)..T, ⟪vv ε (Zs i s), bF J nn Zs i s⟫ =
      gg ε z0 - gg ε (Zs i T) + (∫ s in (0 : ℝ)..T, ⟪vv ε (Zs i s), F (Zs i s)⟫) +
        σ' ^ 2 * (∫ s in (0 : ℝ)..T, lap2 ε (Zs i s)) + M i) :
    (1 / 2) * ‖A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s)‖ ≤
      (N : ℝ) ^ 2 * ε + |∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), F (Zl s)⟫| +
        σ' ^ 2 * |∫ s in (0 : ℝ)..T, lap2 ε (Zl s)| + B +
        ∫ s in (0 : ℝ)..T, |⟪vv ε (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫| := by
  have hT := D.hT
  set R : Ch N := A T - ∫ s in (0 : ℝ)..T, gradient (cep_chamberPot a N) (Zl s) with hR
  -- the right-hand side is nonnegative except possibly `B`; handle `R = 0` separately
  have hnn1 : 0 ≤ |∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), F (Zl s)⟫| := abs_nonneg _
  have hnn2 : 0 ≤ σ' ^ 2 * |∫ s in (0 : ℝ)..T, lap2 ε (Zl s)| := by positivity
  have hnn3 : 0 ≤ ∫ s in (0 : ℝ)..T, |⟪vv ε (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫| :=
    intervalIntegral.integral_nonneg hT fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ B := by
    obtain ⟨i, hi⟩ := hM.exists
    exact (abs_nonneg _).trans hi
  have hNε : 0 ≤ (N : ℝ) ^ 2 * ε := by positivity
  by_cases hR0 : R = 0
  · rw [hR0, norm_zero]; linarith
  have hRpos : 0 < ‖R‖ := norm_pos_iff.2 hR0
  set u : Ch N := (1 / (2 * ‖R‖)) • R with hu
  have hunorm : ‖u‖ = 1 / 2 := by
    rw [hu, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  obtain ⟨L, hL, hineq⟩ := cepe6e_det_main D hN hA hK hε hε1 (u := u) (by rw [hunorm])
  have huR : ⟪u, R⟫ = (1 / 2) * ‖R‖ := by
    rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hineq2 : ⟪u, R⟫ ≤ -L + ∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫ :=
    hineq
  rw [huR] at hineq2
  -- the convergence of the boundary terms
  have hcl : Zl T ∈ closure (cep_Alcove N) := D.hcl T ⟨hT, le_rfl⟩
  have hggc : Continuous (gg (N := N) ε) := gg_continuous ε
  have hS1 : Tendsto (fun i => gg ε (Zs i T)) atTop (𝓝 (gg ε (Zl T))) := by
    have := (cepe6e_tuo_comp hggc isCompact_Icc D.hZl.continuousOn D.hunif).tendsto_at
      (x := T) ⟨hT, le_rfl⟩
    exact this
  have hHc : Continuous fun z : Ch N => ⟪vv (N := N) ε z, F z⟫ :=
    (vv_continuous ε).inner hF
  have hS2 : Tendsto (fun i => ∫ s in (0 : ℝ)..T, ⟪vv ε (Zs i s), F (Zs i s)⟫) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), F (Zl s)⟫)) := by
    refine cepe6e_integral_tuo hT (fun i => (hHc.comp (D.hZs i)).continuousOn)
      (hHc.comp D.hZl).continuousOn ?_
    exact cepe6e_tuo_comp hHc isCompact_Icc D.hZl.continuousOn D.hunif
  have hS3 : Tendsto (fun i => ∫ s in (0 : ℝ)..T, lap2 ε (Zs i s)) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, lap2 ε (Zl s))) := by
    refine cepe6e_integral_tuo hT (fun i => ((lap2_continuous ε).comp (D.hZs i)).continuousOn)
      ((lap2_continuous ε).comp D.hZl).continuousOn ?_
    exact cepe6e_tuo_comp (lap2_continuous ε) isCompact_Icc D.hZl.continuousOn D.hunif
  set Sinf : ℝ := gg ε z0 - gg ε (Zl T) + (∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), F (Zl s)⟫) +
    σ' ^ 2 * (∫ s in (0 : ℝ)..T, lap2 ε (Zl s)) with hSinf
  have hSlim : Tendsto (fun i => gg ε z0 - gg ε (Zs i T) + (∫ s in (0 : ℝ)..T, ⟪vv ε (Zs i s), F (Zs i s)⟫) +
      σ' ^ 2 * (∫ s in (0 : ℝ)..T, lap2 ε (Zs i s))) atTop (𝓝 Sinf) :=
    (((tendsto_const_nhds.sub hS1).add hS2).add (hS3.const_mul _))
  have hMlim : Tendsto M atTop (𝓝 (L - Sinf)) := by
    have := hL.sub hSlim
    refine this.congr fun i => ?_
    rw [hIto i]; ring
  have hMB : |L - Sinf| ≤ B := by
    have := (hMlim.abs)
    exact le_of_tendsto this hM
  -- the size of the boundary terms
  have hz0b := gg_bounds ε hε z0 (fun k l hkl => ⟨by linarith [hz0.1 k l hkl], by linarith [hz0.2 k l]⟩)
  have hcl' : Zl T ∈ ClAlc N := closure_Alc_subset hcl
  have hzTb := gg_bounds ε hε (Zl T)
    (fun k l hkl => ⟨by linarith [hcl'.1 k l hkl], by linarith [hcl'.2 k l]⟩)
  have hX : |gg ε z0 - gg ε (Zl T)| ≤ (N : ℝ) ^ 2 * ε := by
    rw [abs_le]
    constructor <;> nlinarith [hz0b.1, hz0b.2, hzTb.1, hzTb.2]
  set I1 := ∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), F (Zl s)⟫ with hI1
  set I2 := ∫ s in (0 : ℝ)..T, lap2 ε (Zl s) with hI2
  have habs : |Sinf| ≤ (N : ℝ) ^ 2 * ε + |I1| + σ' ^ 2 * |I2| := by
    have e : Sinf = (gg ε z0 - gg ε (Zl T)) + I1 + σ' ^ 2 * I2 := rfl
    rw [e]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg σ')]
    linarith
  have hI3 : ∫ s in (0 : ℝ)..T, ⟪vv ε (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫ ≤
      ∫ s in (0 : ℝ)..T, |⟪vv ε (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫| :=
    (le_abs_self _).trans (intervalIntegral.abs_integral_le_integral_abs hT)
  have hL' : -L ≤ |Sinf| + B := by
    have h1 : L = Sinf + (L - Sinf) := by ring
    have h2 : -L ≤ |L| := neg_le_abs L
    have h3 : |L| ≤ |Sinf| + |L - Sinf| := by
      calc |L| = |Sinf + (L - Sinf)| := by rw [← h1]
        _ ≤ |Sinf| + |L - Sinf| := abs_add_le _ _
    linarith
  linarith

/-- Pointwise: at a point of the open alcove, `v_ε` and the Laplacian term vanish for small `ε`. -/
theorem cepe6e_eventually_zero {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → vv ε z = 0 ∧ lap2 ε z = 0 := by
  have hd : ∀ k l : Fin N, k < l → 0 < min (z l - z k) (1 - (z l - z k)) := by
    intro k l hkl
    exact lt_min (by linarith [hz.1 k l hkl]) (by linarith [hz.2 k l])
  -- a uniform lower bound for the finitely many pairs
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ k l : Fin N, k < l → m ≤ min (z l - z k) (1 - (z l - z k)) := by
    classical
    let f : Fin N × Fin N → ℝ := fun p => if p.1 < p.2 then min (z p.2 - z p.1) (1 - (z p.2 - z p.1)) else 1
    have hfpos : ∀ p, 0 < f p := by
      intro p; by_cases h : p.1 < p.2
      · simp only [f, h, if_true]; exact hd _ _ h
      · simp only [f, h, if_false]; exact one_pos
    by_cases hne : (Finset.univ : Finset (Fin N × Fin N)).Nonempty
    · refine ⟨(Finset.univ : Finset (Fin N × Fin N)).inf' hne f, ?_, ?_⟩
      · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_inf' hne f
        rw [hp]; exact hfpos p
      · intro k l hkl
        have h1 := Finset.inf'_le f (Finset.mem_univ (k, l))
        have h2 : f (k, l) = min (z l - z k) (1 - (z l - z k)) := by simp [f, hkl]
        rw [← h2]; exact h1
    · refine ⟨1, one_pos, fun k l _ => ?_⟩
      exact absurd ⟨(k, l), Finset.mem_univ _⟩ hne
  refine ⟨m, hm0, fun ε hε hεm => ⟨?_, ?_⟩⟩
  · refine vv_eq_zero ε hε z fun k l hkl => ?_
    linarith [hm k l hkl]
  · unfold lap2
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      have := le_min_iff.1 ((show ε / 2 ≤ m by linarith).trans (hm k l hkl))
      exact chi2_eq_zero hε this.1 this.2
    · simp [hkl]

/-- Dominated convergence to `0` on `[0,T]`. -/
theorem cepe6e_dct_zero {T : ℝ} (hT : 0 ≤ T) {g : ℕ → ℝ → ℝ} {bound : ℝ → ℝ}
    (hmeas : ∀ l, AEStronglyMeasurable (g l) (volume.restrict (Ioc 0 T)))
    (hb : ∀ l, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) T → ‖g l s‖ ≤ bound s)
    (hbi : IntervalIntegrable bound volume 0 T)
    (hlim : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) T → Tendsto (fun l => g l s) atTop (𝓝 0)) :
    Tendsto (fun l => ∫ s in (0 : ℝ)..T, g l s) atTop (𝓝 0) := by
  have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := atTop) (a := 0) (b := T) (F := g) (f := fun _ => (0 : ℝ)) bound
    (Eventually.of_forall fun l => by rw [uIoc_of_le hT]; exact hmeas l)
    (Eventually.of_forall fun l => by
      filter_upwards [hb l] with s hs hsI
      rw [uIoc_of_le hT] at hsI
      exact hs hsI)
    hbi (by
      filter_upwards [hlim] with s hs hsI
      rw [uIoc_of_le hT] at hsI
      exact hs hsI)
  simpa using this

theorem cepe6e_ae_mem {T : ℝ} {Zl : ℝ → Ch N}
    (hnull : volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ∉ cep_Alcove N} = 0) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) T → Zl s ∈ cep_Alcove N := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with s hs hsI
  by_contra hz
  exact hs ⟨⟨hsI.1.le, hsI.2⟩, hz⟩

theorem cepe6e_Dterms_tendsto {a : ℝ} {T : ℝ} (hT : 0 ≤ T) {Zl : ℝ → Ch N} (hZl : Continuous Zl)
    {F : Ch N → Ch N} (hF : Continuous F) (σ' : ℝ)
    (hnull : volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ∉ cep_Alcove N} = 0)
    (hint : IntegrableOn (fun s => ‖gradient (cep_chamberPot a N) (Zl s)‖) (Icc 0 T))
    (hinv : IntegrableOn (fun s => ∑ k : Fin N, ∑ l : Fin N,
      (if k < l then 1 / min (Zl s l - Zl s k) (1 - (Zl s l - Zl s k)) else 0)) (Icc 0 T))
    {ε : ℕ → ℝ} (hε0 : ∀ l, 0 < ε l) (hε1 : ∀ l, ε l ≤ 1 / 8) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun l => (N : ℝ) ^ 2 * ε l + |∫ s in (0 : ℝ)..T, ⟪vv (ε l) (Zl s), F (Zl s)⟫| +
        σ' ^ 2 * |∫ s in (0 : ℝ)..T, lap2 (ε l) (Zl s)| +
        ∫ s in (0 : ℝ)..T, |⟪vv (ε l) (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫|) atTop (𝓝 0) := by
  have hae := cepe6e_ae_mem hnull
  -- pointwise eventual vanishing
  have hev : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc (0 : ℝ) T →
      ∀ᶠ l in atTop, vv (ε l) (Zl s) = 0 ∧ lap2 (ε l) (Zl s) = 0 := by
    filter_upwards [hae] with s hs hsI
    obtain ⟨ε₀, hε₀, h⟩ := cepe6e_eventually_zero (hs hsI)
    have : ∀ᶠ l in atTop, ε l ≤ ε₀ := hεlim.eventually (ge_mem_nhds hε₀)
    filter_upwards [this] with l hl
    exact h (ε l) (hε0 l) hl
  have hCz : 0 < Cz := lt_of_lt_of_le one_pos one_le_Cz
  have hGm : Measurable fun s => gradient (cep_chamberPot a N) (Zl s) :=
    (HRS.MC.CepE6A.e6a_gradient_measurable a).comp hZl.measurable
  have hvvZ : ∀ l, Continuous fun s => vv (N := N) (ε l) (Zl s) := fun l => (vv_continuous _).comp hZl
  -- T4
  have hT4 : Tendsto (fun l => ∫ s in (0 : ℝ)..T,
      |⟪vv (ε l) (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫|) atTop (𝓝 0) := by
    refine cepe6e_dct_zero hT (bound := fun s => (N : ℝ) ^ 2 * ‖gradient (cep_chamberPot a N) (Zl s)‖) ?_ ?_ ?_ ?_
    · intro l
      have hm : AEStronglyMeasurable (fun s => ⟪vv (ε l) (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫)
          (volume.restrict (Ioc 0 T)) :=
        (hvvZ l).aestronglyMeasurable.inner hGm.aestronglyMeasurable
      simpa [Real.norm_eq_abs] using hm.norm
    · intro l
      refine Eventually.of_forall fun s _ => ?_
      rw [Real.norm_eq_abs, abs_abs]
      calc |⟪vv (ε l) (Zl s), gradient (cep_chamberPot a N) (Zl s)⟫|
          ≤ ‖vv (ε l) (Zl s)‖ * ‖gradient (cep_chamberPot a N) (Zl s)‖ := abs_real_inner_le_norm _ _
        _ ≤ (N : ℝ) ^ 2 * ‖gradient (cep_chamberPot a N) (Zl s)‖ :=
            mul_le_mul_of_nonneg_right (norm_vv_le _ _) (norm_nonneg _)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
      exact hint.const_mul _
    · filter_upwards [hev] with s hs hsI
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hs hsI] with l hl
      simp [hl.1]
  -- T2
  obtain ⟨CF0, hCF0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn (hF.comp hZl).continuousOn
  have hT2 : Tendsto (fun l => ∫ s in (0 : ℝ)..T, |⟪vv (ε l) (Zl s), F (Zl s)⟫|) atTop (𝓝 0) := by
    refine cepe6e_dct_zero hT (bound := fun _ => (N : ℝ) ^ 2 * |CF0|) ?_ ?_ ?_ ?_
    · intro l
      exact (((hvvZ l).inner (hF.comp hZl)).abs).aestronglyMeasurable
    · intro l
      refine Eventually.of_forall fun s hs => ?_
      rw [Real.norm_eq_abs, abs_abs]
      have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
      calc |⟪vv (ε l) (Zl s), F (Zl s)⟫| ≤ ‖vv (ε l) (Zl s)‖ * ‖F (Zl s)‖ := abs_real_inner_le_norm _ _
        _ ≤ (N : ℝ) ^ 2 * |CF0| :=
            mul_le_mul (norm_vv_le _ _) ((hCF0 s hsI).trans (le_abs_self _)) (norm_nonneg _) (by positivity)
    · exact intervalIntegrable_const
    · filter_upwards [hev] with s hs hsI
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hs hsI] with l hl
      simp [hl.1]
  -- T3
  have hT3 : Tendsto (fun l => ∫ s in (0 : ℝ)..T, |lap2 (ε l) (Zl s)|) atTop (𝓝 0) := by
    refine cepe6e_dct_zero hT (bound := fun s => (Cz / 2) * ∑ k : Fin N, ∑ l : Fin N,
      (if k < l then 1 / min (Zl s l - Zl s k) (1 - (Zl s l - Zl s k)) else 0)) ?_ ?_ ?_ ?_
    · intro l
      exact (((lap2_continuous (ε l)).comp hZl).abs).aestronglyMeasurable
    · intro l
      filter_upwards [hae] with s hs hsI
      have hz := hs hsI
      rw [Real.norm_eq_abs, abs_abs]
      unfold lap2
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      by_cases hkm : k < m
      · simp only [hkm, if_true]
        have hμ : 0 < min (Zl s m - Zl s k) (1 - (Zl s m - Zl s k)) :=
          lt_min (by linarith [hz.1 k m hkm]) (by linarith [hz.2 k m])
        have h1 := abs_chi2_le_indicator (ε := ε l) (Zl s m - Zl s k) (hε0 l) (hε1 l)
        refine h1.trans ?_
        split_ifs with hlt
        · calc Cz / ε l ≤ Cz / (2 * min (Zl s m - Zl s k) (1 - (Zl s m - Zl s k))) :=
                div_le_div_of_nonneg_left hCz.le (by positivity) (by linarith)
            _ = Cz / 2 * (1 / min (Zl s m - Zl s k) (1 - (Zl s m - Zl s k))) := by
                field_simp
        · positivity
      · simp [hkm]
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
      exact hinv.const_mul _
    · filter_upwards [hev] with s hs hsI
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hs hsI] with l hl
      simp [hl.2]
  -- assemble
  have hT2' : Tendsto (fun l => |∫ s in (0 : ℝ)..T, ⟪vv (ε l) (Zl s), F (Zl s)⟫|) atTop (𝓝 0) :=
    squeeze_zero (fun l => abs_nonneg _) (fun l => intervalIntegral.abs_integral_le_integral_abs hT) hT2
  have hT3' : Tendsto (fun l => |∫ s in (0 : ℝ)..T, lap2 (ε l) (Zl s)|) atTop (𝓝 0) :=
    squeeze_zero (fun l => abs_nonneg _) (fun l => intervalIntegral.abs_integral_le_integral_abs hT) hT3
  have hT1 : Tendsto (fun l => (N : ℝ) ^ 2 * ε l) atTop (𝓝 0) := by
    simpa using hεlim.const_mul ((N : ℝ) ^ 2)
  have := ((hT1.add hT2').add (hT3'.const_mul (σ' ^ 2))).add hT4
  simpa using this

end HRS.MC.CepE6E
