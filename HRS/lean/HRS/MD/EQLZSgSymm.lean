import HRS.MD.EQLZSgSemigroup
import HRS.PDE.TorusFPEntropyClassicalAux1
import HRS.PDE.TorusFPCompareAux2

/-!
# EQ-LZ packet SG-3: `L²(π)`-symmetry of `P_t` on smooth data (`eqlz_sg_symm`), proof

For classical backward solutions `f` (terminal datum `φ`) and `g` (terminal datum `ψ`) on `[0,t]`, the function
`J(s) = ∫ f_s · g_{t-s} dπ` is continuous on `[0,t]` and has derivative
`∫ (-L f_s) g_{t-s} + f_s (L g_{t-s}) dπ = 0` on `(0,t)` by `d3a_selfadj`; hence `J(0) = J(t)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS

namespace HRS.MD.EQLZSgSymm

variable {n : ℕ}

section Facts

variable {κ : ℝ} {U : Torus n → ℝ} {t : ℝ} {ψ : Torus n → ℝ} {f : ℝ → Torus n → ℝ}

theorem eqlzsg_joint (hf : D1BackwardSolution κ (d1_gradDrift U) t ψ f) :
    ContinuousOn (fun p : ℝ × Torus n => f p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ) :=
  continuousOn_Icc_prod_of_subtype hf.continuous_joint

theorem eqlzsg_bound (hf : D1BackwardSolution κ (d1_gradDrift U) t ψ f) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖f s x‖ ≤ C := by
  have hI : IsCompact (Set.Icc 0 t ×ˢ (Set.univ : Set (Torus n))) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hI.exists_bound_of_continuousOn (eqlzsg_joint hf)
  exact ⟨C, fun s hs x => hC (s, x) (Set.mk_mem_prod hs (Set.mem_univ x))⟩

theorem eqlzsg_bound_gen (hf : D1BackwardSolution κ (d1_gradDrift U) t ψ f) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖d1_gen κ (d1_gradDrift U) (f s) x‖ ≤ C := by
  have hI : IsCompact (Set.Icc 0 t ×ˢ (Set.univ : Set (Torus n))) :=
    isCompact_Icc.prod isCompact_univ
  have hgen : ContinuousOn (fun p : ℝ × Torus n => d1_gen κ (d1_gradDrift U) (f p.1) p.2)
      (Set.Icc 0 t ×ˢ Set.univ) :=
    continuousOn_Icc_prod_of_subtype hf.cont_time_deriv
  obtain ⟨C, hC⟩ := hI.exists_bound_of_continuousOn hgen
  exact ⟨C, fun s hs x => hC (s, x) (Set.mk_mem_prod hs (Set.mem_univ x))⟩

theorem eqlzsg_cont_time (hf : D1BackwardSolution κ (d1_gradDrift U) t ψ f) (x : Torus n) :
    ContinuousOn (fun s => f s x) (Set.Icc 0 t) :=
  (eqlzsg_joint hf).comp (continuous_id.prodMk continuous_const).continuousOn
    (fun s hs => ⟨hs, Set.mem_univ _⟩)

end Facts

/-- (SG-3, `eqlz_sg_symm`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_sg_symm`. -/
theorem eqlz_sg_symm_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {t : ℝ}
    (ht : 0 ≤ t) {φ ψ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    ∫ x, ψ x * d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) =
      ∫ x, φ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [HRS.MD.EQLZSgSemigroup.eqlzsg_P_zero hn hκ hU, HRS.MD.EQLZSgSemigroup.eqlzsg_P_zero hn hκ hU]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  · haveI := d3a_gibbs_isProb (κ := κ) hU
    obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU hpos hφ
    obtain ⟨g, hg⟩ := d1_backward_classical hn hκ hU hpos hψ
    set P := d1_gibbsMeasure κ U with hP
    set L := d1_gen κ (d1_gradDrift U) with hL
    have hint_c : ∀ h : Torus n → ℝ, Continuous h → Integrable h P := fun h hh =>
      hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hPf : ∀ x, d1_P hn hκ hU t φ x = f 0 x := by
      intro x
      rw [d1_P_eq hn hκ hU hpos hφ hf ⟨hpos.le, le_rfl⟩ x]; simp
    have hPg : ∀ x, d1_P hn hκ hU t ψ x = g 0 x := by
      intro x
      rw [d1_P_eq hn hκ hU hpos hψ hg ⟨hpos.le, le_rfl⟩ x]; simp
    obtain ⟨Cf, hCf⟩ := eqlzsg_bound hf
    obtain ⟨Cg, hCg⟩ := eqlzsg_bound hg
    obtain ⟨Df, hDf⟩ := eqlzsg_bound_gen hf
    obtain ⟨Dg, hDg⟩ := eqlzsg_bound_gen hg
    have hcf : ∀ s ∈ Set.Icc (0 : ℝ) t, Continuous (f s) := fun s hs =>
      d1_continuous_of_isCk2 (hf.c2 s hs)
    have hcg : ∀ s ∈ Set.Icc (0 : ℝ) t, Continuous (g s) := fun s hs =>
      d1_continuous_of_isCk2 (hg.c2 s hs)
    have hmem : ∀ s ∈ Set.Icc (0 : ℝ) t, t - s ∈ Set.Icc (0 : ℝ) t := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hgenf : ∀ s ∈ Set.Icc (0 : ℝ) t, Continuous (fun x => L (f s) x) := fun s hs =>
      d1_gen_continuous (d1_gradDrift_continuous hU) (hf.c2 s hs)
    have hgeng : ∀ s ∈ Set.Icc (0 : ℝ) t, Continuous (fun x => L (g s) x) := fun s hs =>
      d1_gen_continuous (d1_gradDrift_continuous hU) (hg.c2 s hs)
    -- continuity of J on [0,t]
    have hJcont : ContinuousOn (fun s => ∫ x, f s x * g (t - s) x ∂P) (Set.Icc 0 t) := by
      refine continuousOn_of_dominated (bound := fun _ => Cf * Cg)
        (fun s hs => ((hcf s hs).mul (hcg _ (hmem s hs))).aestronglyMeasurable)
        (fun s hs => ae_of_all _ (fun x => ?_)) (integrable_const _)
        (ae_of_all _ fun x => ?_)
      · rw [norm_mul]
        exact mul_le_mul (hCf s hs x) (hCg _ (hmem s hs) x) (norm_nonneg _)
          ((norm_nonneg _).trans (hCf s hs x))
      · refine (eqlzsg_cont_time hf x).mul ?_
        have : ContinuousOn (fun s : ℝ => t - s) (Set.Icc 0 t) := (continuous_const.sub continuous_id).continuousOn
        exact (eqlzsg_cont_time hg x).comp this (fun s hs => hmem s hs)
    -- derivative of J
    have hJderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt (fun s => ∫ x, f s x * g (t - s) x ∂P)
        (∫ x, ((-(L (f s) x)) * g (t - s) x + f s x * L (g (t - s)) x) ∂P) s := by
      intro s hs
      have hsI : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.le⟩
      have hts : ∀ s' ∈ Set.Ioo (0 : ℝ) t, t - s' ∈ Set.Ioo (0 : ℝ) t := fun s' hs' =>
        ⟨by linarith [hs'.2], by linarith [hs'.1]⟩
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
        (F := fun s' x => f s' x * g (t - s') x)
        (F' := fun s' x => (-(L (f s') x)) * g (t - s') x + f s' x * L (g (t - s')) x)
        (x₀ := s) (s := Set.Ioo 0 t) (bound := fun _ => Df * Cg + Cf * Dg)
        (Ioo_mem_nhds hs.1 hs.2) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
      · exact Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun s' hs' =>
          ((hcf s' ⟨hs'.1.le, hs'.2.le⟩).mul
            (hcg _ (hmem s' ⟨hs'.1.le, hs'.2.le⟩))).aestronglyMeasurable
      · exact hint_c _ ((hcf s hsI).mul (hcg _ (hmem s hsI)))
      · exact ((((hgenf s hsI).neg).mul (hcg _ (hmem s hsI))).add
          ((hcf s hsI).mul (hgeng _ (hmem s hsI)))).aestronglyMeasurable
      · refine ae_of_all _ fun a s' hs' => ?_
        have hs'I : s' ∈ Set.Icc (0 : ℝ) t := ⟨hs'.1.le, hs'.2.le⟩
        have hts' := hmem s' hs'I
        have e1 : ‖L (f s') a‖ ≤ Df := hDf s' hs'I a
        have e2 : ‖g (t - s') a‖ ≤ Cg := hCg _ hts' a
        have e3 : ‖f s' a‖ ≤ Cf := hCf s' hs'I a
        have e4 : ‖L (g (t - s')) a‖ ≤ Dg := hDg _ hts' a
        calc ‖(-(L (f s') a)) * g (t - s') a + f s' a * L (g (t - s')) a‖
            ≤ ‖(-(L (f s') a)) * g (t - s') a‖ + ‖f s' a * L (g (t - s')) a‖ := norm_add_le _ _
          _ ≤ Df * Cg + Cf * Dg := by
            rw [norm_mul, norm_mul, norm_neg]
            exact add_le_add (mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1))
              (mul_le_mul e3 e4 (norm_nonneg _) ((norm_nonneg _).trans e3))
      · refine ae_of_all _ fun a s' hs' => ?_
        have h1 := hf.time_deriv a s' hs'
        have h2 := (hg.time_deriv a (t - s') (hts s' hs')).comp_const_sub t s'
        have h3 := h1.mul h2
        convert h3 using 1
        ring
    have hzero : ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ∫ x, ((-(L (f s) x)) * g (t - s) x + f s x * L (g (t - s)) x) ∂P = 0 := by
      intro s hs
      have hsI : s ∈ Set.Icc (0 : ℝ) t := ⟨hs.1.le, hs.2.le⟩
      have hts := hmem s hsI
      have i1 : Integrable (fun x => (-(L (f s) x)) * g (t - s) x) P :=
        hint_c _ ((hgenf s hsI).neg.mul (hcg _ hts))
      have i2 : Integrable (fun x => f s x * L (g (t - s)) x) P :=
        hint_c _ ((hcf s hsI).mul (hgeng _ hts))
      rw [integral_add i1 i2]
      have hself := d3a_selfadj hκ hU (f := g (t - s)) (w := f s) (hg.c2 _ hts) (hf.c2 s hsI)
      have e1 : ∫ x, (-(L (f s) x)) * g (t - s) x ∂P = -∫ x, L (f s) x * g (t - s) x ∂P := by
        simp_rw [neg_mul]; rw [integral_neg]
      have e2 : ∫ x, f s x * L (g (t - s)) x ∂P = ∫ x, L (g (t - s)) x * f s x ∂P := by
        simp_rw [mul_comm (f s _)]
      rw [e1, e2, ← hself]
      ring
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
      (fun s => ∫ x, f s x * g (t - s) x ∂P)
      (fun s => ∫ x, ((-(L (f s) x)) * g (t - s) x + f s x * L (g (t - s)) x) ∂P)
      hpos hJcont hJderiv
    have hc0 := hzero c hc
    simp only [hc0] at hceq
    have hdiff : (∫ x, f t x * g (t - t) x ∂P) - ∫ x, f 0 x * g (t - 0) x ∂P = 0 := by
      rcases div_eq_zero_iff.1 hceq.symm with h | h
      · exact h
      · exfalso
        linarith
    have hfin : (∫ x, f t x * g (t - t) x ∂P) = ∫ x, f 0 x * g (t - 0) x ∂P := by linarith
    simp only [sub_self, sub_zero, hf.terminal, hg.terminal] at hfin
    simp_rw [hPf, hPg]
    calc ∫ x, ψ x * f 0 x ∂P = ∫ x, f 0 x * ψ x ∂P :=
          integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
      _ = ∫ x, φ x * g 0 x ∂P := hfin.symm

end HRS.MD.EQLZSgSymm

end
