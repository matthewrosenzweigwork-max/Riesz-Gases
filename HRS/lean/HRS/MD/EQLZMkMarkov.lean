import HRS.MD.EQLZMkIto
import HRS.MD.EQLZVocab

/-!
# EQ-LZ packet MK-1: the Markov property of the level-`lev` flow (`eqlz_mk_markov`), proof

Route: a classical backward solution `f` on `[0, t]` with terminal datum `φ` (`d1_backward_classical`), `f r = P_{t-r} φ`
(`d1_P_eq`).  Its transported lift `d1_cl (f r)` is a `C^{1,2}` function whose Itô drift along the level flow vanishes
(`d1_itoGen_eq_configGen_proof`, `b15d_pushField_eq_gradDrift`), so `f(r, Y_r) = f(0, Y_0) + M_r` with `M` a martingale
(`lzmk_ito_martingale`); conditioning on `ℱ_s` gives `E[φ(Z_t) | ℱ_s] = f(s, Y_s) = P_{t-s}φ(Z_s)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ

namespace HRS.MD.EQLZMk

variable {d N n : ℕ}

/-- Boundedness (by periodicity) of the transported `C^{1,2}` function and of its derivatives on `[0, τ]`. -/
theorem lzmk_bounds {τ : ℝ} (g : ℝ → Torus (N * d) → ℝ) (hf : IsC12On τ Set.univ (fun r => d1_cl (g r))) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc 0 τ, ∀ y, |d1_cl (g s) y| ≤ C ∧ ‖fderiv ℝ (d1_cl (g s)) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (d1_cl (g s))) y‖ ≤ C ∧
        |derivWithin (fun r => d1_cl (g r) y) (Set.Icc 0 τ) s| ≤ C := by
  set fn : ℝ → (Fin N → Euc d) → ℝ := fun r => d1_cl (g r) with hfn
  have hper1 : ∀ s (Y : Fin N → Euc d) (v : Fin N → Euc d), IsLatticeVec v → fn s (Y + v) = fn s Y := by
    intro s Y v hv
    simp only [hfn, d1_cl]
    rw [mk_add_lattice_vec hv Y]
  have hper2 : ∀ s (Y v : Fin N → Euc d), IsLatticeVec v →
      fderiv ℝ (fn s) (Y + v) = fderiv ℝ (fn s) Y :=
    fun s Y v hv => fderiv_periodic_add (fun x => hper1 s x v hv) Y
  have hper3 : ∀ s (Y v : Fin N → Euc d), IsLatticeVec v →
      fderiv ℝ (fderiv ℝ (fn s)) (Y + v) = fderiv ℝ (fderiv ℝ (fn s)) Y :=
    fun s Y v hv => fderiv_periodic_add (fun x => hper2 s x v hv) Y
  have hper4 : ∀ s (Y v : Fin N → Euc d), IsLatticeVec v →
      derivWithin (fun r => fn r (Y + v)) (Set.Icc 0 τ) s = derivWithin (fun r => fn r Y) (Set.Icc 0 τ) s := by
    intro s Y v hv
    have e : (fun r => fn r (Y + v)) = (fun r => fn r Y) := funext fun r => hper1 r Y v hv
    rw [e]
  obtain ⟨C1, h1⟩ := bounded_of_periodic (T := τ) (fun s y => fn s y) hf.cont
    (fun s Y v hv => hper1 s Y v hv)
  obtain ⟨C2, h2⟩ := bounded_of_periodic (T := τ) (fun s y => ‖fderiv ℝ (fn s) y‖)
    hf.cont_fderiv.norm (fun s Y v hv => by simp only [hper2 s Y v hv])
  have hc3 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => ‖fderiv ℝ (fderiv ℝ (fn p.1)) p.2‖)
      (Set.Icc 0 τ ×ˢ (Set.univ : Set (Fin N → Euc d))) :=
    ContinuousOn.norm (f := fun p : ℝ × (Fin N → Euc d) => fderiv ℝ (fderiv ℝ (fn p.1)) p.2)
      hf.cont_fderiv₂
  obtain ⟨C3, h3⟩ := bounded_of_periodic (T := τ) (fun s y => ‖fderiv ℝ (fderiv ℝ (fn s)) y‖)
    hc3 (fun s Y v hv => by simp only [hper3 s Y v hv])
  obtain ⟨C4, h4⟩ := bounded_of_periodic (T := τ)
    (fun s y => |derivWithin (fun r => fn r y) (Set.Icc 0 τ) s|)
    (continuous_abs.comp_continuousOn hf.cont_deriv) (fun s Y v hv => by simp only [hper4 s Y v hv])
  refine ⟨max (max C1 C2) (max C3 C4), fun s hs y => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := h1 s hs y
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_of_le_left (le_max_left _ _))
  · have := h2 s hs y
    rw [norm_norm] at this
    exact this.trans (le_max_of_le_left (le_max_right _ _))
  · have := h3 s hs y
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
  · have := h4 s hs y
    rw [Real.norm_eq_abs, abs_abs] at this
    exact this.trans (le_max_of_le_right (le_max_right _ _))

/-- A continuous function of a measurable map into the (compact) torus is integrable. -/
theorem lzmk_integrable_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Torus n → ℝ} (hg : Continuous g) {Z : Ω → Torus n} (hZ : Measurable Z) :
    Integrable (fun ω => g (Z ω)) P := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound (hg.measurable.comp hZ).aestronglyMeasurable C
    (ae_of_all _ fun ω => hC _ (Set.mem_univ _))

/-- `levelProc Y r` is `ℱ_r`-measurable. -/
theorem lzmk_levelProc_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {Y : ℝ → Ω → Fin N → Euc d} (hY : ∀ r, Measurable[ℱ r] (Y r)) (r : ℝ) :
    Measurable[ℱ r] (levelProc Y r) := by
  have hc : Continuous (fun Z : Fin N → Euc d => d1_configEquiv d N (fun i => Torus.mk (Z i))) :=
    (d1_configEquiv_continuous d N).comp (continuous_pi fun i => Torus.continuous_mk.comp (continuous_apply i))
  exact hc.measurable.comp (hY r)

/-- (MK-1, `eqlz_mk_markov`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_mk_markov`. -/
theorem eqlz_mk_markov_proof (hNd : 1 ≤ N * d) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsSmooth D.V) (hβ : 0 < D.invβ) (lev : ℝ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Y₀ : Ω → Fin N → Euc d)
    (Y : ℝ → Ω → Fin N → Euc d) (hY : IsLevelFlow D lev P ℱ W' Y₀ Y)
    {φ : Torus (N * d) → ℝ} (hφ : Torus.IsSmooth φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[fun ω => φ (levelProc Y t ω) | ℱ s] =ᵐ[P]
      fun ω => d1_P hNd hβ (b15d_U_isSmooth_proof (N := N) D hV lev) (t - s) φ (levelProc Y s ω) := by
  have hV2 : Torus.IsCk 2 D.V :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.V) from hV).of_le
      (by first | exact WithTop.coe_le_coe.2 le_top | (norm_cast; exact le_top) | simp)
  have hU := b15d_U_isSmooth_proof (N := N) D hV lev
  have hbC := b15d_liftedDriftReg_continuous_proof (N := N) D hV2 lev
  have hY' : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift (b15d_configDriftReg D lev))
      (d1_noise d N D.invβ) Y₀ (fun _ => ⊤) Y := hY.sol
  have hZm : ∀ r, Measurable[ℱ r] (levelProc Y r) := fun r => lzmk_levelProc_meas hY'.adapted r
  have hφc : Continuous φ := StaticLimitAux.continuous_of_smooth hφ
  rcases hst.eq_or_lt with hse | hlt
  · -- `s = t`
    subst hse
    have h0 : d1_P hNd hβ hU (s - s) φ = φ := by
      rw [sub_self]
      funext x
      unfold d1_P
      simp
    have hsm : StronglyMeasurable[ℱ s] (fun ω => φ (levelProc Y s ω)) :=
      (hφc.measurable.comp (hZm s)).stronglyMeasurable
    have hint : Integrable (fun ω => φ (levelProc Y s ω)) P :=
      lzmk_integrable_comp hφc ((hZm s).mono (ℱ.le s) le_rfl)
    rw [condExp_of_stronglyMeasurable (ℱ.le s) hsm hint, h0]
  · have ht0 : 0 < t := lt_of_le_of_lt hs hlt
    obtain ⟨fs, hfs⟩ := d1_backward_classical hNd hβ hU ht0 hφ
    set fn : ℝ → (Fin N → Euc d) → ℝ := fun r => d1_cl (fs r) with hfn
    have hΦ : IsC12Test t (fun r => (fun X => fs r (d1_configEquiv d N X)) ∘ (d1_configEquiv d N).symm)
        (fun r => (fun X => -(d1_gen D.invβ (d1_gradDrift (b15d_U (N := N) D lev)) (fs r)
          (d1_configEquiv d N X))) ∘ (d1_configEquiv d N).symm) := by
      have e1 : (fun r => (fun X => fs r (d1_configEquiv d N X)) ∘ (d1_configEquiv d N).symm) = fs := by
        funext r x
        simp
      have e2 : (fun r => (fun X => -(d1_gen D.invβ (d1_gradDrift (b15d_U (N := N) D lev)) (fs r)
          (d1_configEquiv d N X))) ∘ (d1_configEquiv d N).symm) =
          fun r x => -(d1_gen D.invβ (d1_gradDrift (b15d_U (N := N) D lev)) (fs r) x) := by
        funext r x
        simp
      rw [e1, e2]
      exact hfs.isC12Test
    have hf : IsC12On t Set.univ fn := (d1_isC12On_of_isC12Test_proof ht0 hfs.isC12Test).1
    obtain ⟨C, hC⟩ := lzmk_bounds (τ := t) fs hf
    -- the Ito drift of `fn` vanishes
    have hdrift : ∀ r ∈ Set.Icc 0 t, ∀ y : Fin N → Euc d,
        d1_itoGen D.invβ (b15d_configDriftReg D lev) t fn r y = 0 := by
      intro r hr y
      have h1 := d1_itoGen_eq_configGen_proof (N := N) (d := d) (bC := b15d_configDriftReg D lev) hβ.le ht0
        (Φ := fun r X => fs r (d1_configEquiv d N X))
        (Φt := fun r X => -(d1_gen D.invβ (d1_gradDrift (b15d_U (N := N) D lev)) (fs r)
          (d1_configEquiv d N X))) hΦ hr y
      have e1 : (fun r => d1_cl ((fun X => fs r (d1_configEquiv d N X)) ∘ (d1_configEquiv d N).symm)) = fn := by
        funext r Z
        simp [hfn, d1_cl]
      rw [e1] at h1
      rw [h1]
      have h2 := d1_gen_config D.invβ (b15d_configDriftReg (N := N) D lev) (fs r)
        (fun i => Torus.mk (y i))
      have hpf : d1_pushField (b15d_configDriftReg (N := N) D lev) =
          d1_gradDrift (b15d_U (N := N) D lev) := funext (b15d_pushField_eq_gradDrift D hM hV2 lev)
      rw [hpf] at h2
      have h2' : d1_gen D.invβ (d1_gradDrift (b15d_U (N := N) D lev)) (fs r)
          (d1_configEquiv d N fun i => Torus.mk (y i)) =
          d1_configGen D.invβ (b15d_configDriftReg D lev) (fun X => fs r (d1_configEquiv d N X))
            fun i => Torus.mk (y i) := h2
      linarith
    obtain ⟨Mp, hMp, hIto⟩ := lzmk_ito_martingale hY.brownian hβ.le hbC hY.init_adapted hY' ht0.le hf ⟨C, hC⟩
    have hIto' : ∀ r ∈ Set.Icc 0 t, ∀ᵐ ω ∂P, fn r (Y r ω) = fn 0 (Y 0 ω) + Mp r ω := by
      intro r hr
      filter_upwards [hIto r hr] with ω hω
      rw [hω, setIntegral_congr_fun measurableSet_Icc
        (fun u hu => hdrift u ⟨hu.1, hu.2.trans hr.2⟩ (Y u ω))]
      simp
    -- `fn 0` is continuous
    have hcont0 : Continuous (fn 0) :=
      ContinuousOn.comp_continuous (f := fun y : Fin N → Euc d => ((0 : ℝ), y)) hf.cont
        (continuous_const.prodMk continuous_id) (fun y => ⟨⟨le_rfl, ht0.le⟩, Set.mem_univ y⟩)
    have hY0 : Y 0 = Y₀ := funext hY'.init
    have hF0meas : StronglyMeasurable[ℱ s] (fun ω => fn 0 (Y 0 ω)) := by
      rw [hY0]
      exact (hcont0.measurable.comp (hY.init_adapted s)).stronglyMeasurable
    have hF0int : Integrable (fun ω => fn 0 (Y 0 ω)) P := by
      refine Integrable.of_bound ?_ C (ae_of_all _ fun ω => ?_)
      · rw [hY0]
        exact (hcont0.measurable.comp ((hY.init_adapted 0).mono (ℱ.le 0) le_rfl)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        exact (hC 0 ⟨le_rfl, ht0.le⟩ _).1
    have hst' : s ∈ Set.Icc (0 : ℝ) t := ⟨hs, hlt.le⟩
    have htt : t ∈ Set.Icc (0 : ℝ) t := ⟨ht0.le, le_rfl⟩
    -- identify both sides with `fn`
    have hL : (fun ω => φ (levelProc Y t ω)) = fun ω => fn t (Y t ω) := by
      funext ω
      simp only [hfn, d1_cl, hfs.terminal]
      rfl
    have hR : (fun ω => d1_P hNd hβ hU (t - s) φ (levelProc Y s ω)) = fun ω => fn s (Y s ω) := by
      funext ω
      rw [d1_P_eq hNd hβ hU ht0 hφ hfs ⟨by linarith, by linarith⟩ (levelProc Y s ω)]
      rw [show t - (t - s) = s by ring]
      rfl
    rw [hL, hR]
    have hc1 : P[fun ω => fn t (Y t ω) | ℱ s] =ᵐ[P] P[fun ω => fn 0 (Y 0 ω) + Mp t ω | ℱ s] :=
      condExp_congr_ae (hIto' t htt)
    have hc2 : P[fun ω => fn 0 (Y 0 ω) + Mp t ω | ℱ s] =ᵐ[P]
        P[fun ω => fn 0 (Y 0 ω) | ℱ s] + P[Mp t | ℱ s] :=
      condExp_add hF0int (hMp.integrable t) (ℱ s)
    have hc3 : P[fun ω => fn 0 (Y 0 ω) | ℱ s] = fun ω => fn 0 (Y 0 ω) :=
      condExp_of_stronglyMeasurable (ℱ.le s) hF0meas hF0int
    have hc4 : P[Mp t | ℱ s] =ᵐ[P] Mp s := hMp.condExp_ae_eq hlt.le
    filter_upwards [hc1, hc2, hc4, hIto' s hst'] with ω h1 h2 h4 h5
    rw [h1, h2, Pi.add_apply, hc3, h4, h5]

end HRS.MD.EQLZMk

end
