import HRS.MS.UlClassAux1

/-!
# UL-5 (S5.1 infrastructure), part 2: the Duhamel integral is a classical solution

Not a manuscript row.  For `H : UlHyp s M ρ c ν k θ` and a uniformly strongly continuous family
`w : [0,T] → UlClosure k θ`, let `V τ = ulD Q ν s M ρ c w τ τ = ∫_0^τ P_{τ-σ} ulPert (w σ) dσ`.
Then (`ul5_V_hasDerivAt`, the source form of the OU equation `∂_τ V = L_0 V + ulPert (w τ)`,
`V 0 = 0`): for `τ ∈ (0,T)` and every `x`, `τ' ↦ V τ' x` has the derivative
`ul5A Q ν (V τ) x + ulPert s M ρ c (w τ) x` at `τ`.

The proof is by the semigroup splitting `V (τ+h) = P_h (V τ) + R_τ(h)` (`ul5_decomp`, Fubini + the
semigroup law), the right derivative of `h ↦ P_h φ x` at `0` for `φ = V τ ∈ C_b^2` (`ul5_gen_right`),
`R_τ(h)/h → ulPert (w τ) x` (`ul5_R_deriv`), and the fundamental theorem of calculus for the continuous
right derivative (`ul5_V_hasDerivAt`).  Regularity of `V τ` (closure membership, hence `C_b^4`) is the
admissibility `ul4b_adm` of the merged packet UL-4, so no differentiation under the `σ`-integral is
needed.  Helper lemmas carry the prefix `ul5_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

section Duh
variable {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {c : Euc d → Euc d} {ν : ℝ} {k : ℕ}
  {θ : Euc d → ℝ}

theorem ul5_ouSg_cont (Q : Matrix (Fin d) (Fin d) ℝ) (ν s' : ℝ) {g : Euc d → ℝ} (hg : MemCb 2 g) :
    Continuous (ouSg Q ν s' g) := by
  have := (ul3C_smooth Q ν s' 2 (h := g) (by exact_mod_cast hg.1) (M := cbNorm 2 g)
    (fun i hi y => ul3_cb_apply hg hi y)).1
  exact this.continuous

/-- uniform `C_b^2` bounds on the perturbation along a strongly continuous family -/
theorem ul5_pert_bdd (H : UlHyp s M ρ c ν k θ) {T : ℝ} {w : ℝ → Euc d → ℝ} (hw : UlReg k θ T w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc (0 : ℝ) T, MemCb 2 (ulPert s M ρ c (w σ)) ∧
      ∀ y, |ulPert s M ρ c (w σ) y| ≤ K := by
  obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd H.hθ hw (j := 4) H.hk
  obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
  refine ⟨Cp * B, by positivity, fun σ hσ => ?_⟩
  obtain ⟨hm, hn⟩ := hB σ hσ
  obtain ⟨h2, h3⟩ := hpcb _ hm
  exact ⟨h2, fun y => (h3 y).trans (mul_le_mul_of_nonneg_left hn hCp0)⟩

/-- **The semigroup shift of the Duhamel integral**:
`∫_0^τ P_{τ+h-σ} ulPert (w σ) dσ = P_h (∫_0^τ P_{τ-σ} ulPert (w σ) dσ)`. -/
theorem ul5_shift (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlReg k θ T w) {τ h : ℝ} (hτ : 0 ≤ τ) (hh : 0 ≤ h) (hτh : τ + h ≤ T)
    (x : Euc d) :
    ulD Q ν s M ρ c w τ (τ + h) x = ouSg Q ν h (fun y => ulD Q ν s M ρ c w τ τ y) x := by
  have hwτ : UlReg k θ τ w := ul4_reg_mono (by linarith) hw
  obtain ⟨K, hK0, hK⟩ := ul5_pert_bdd H hwτ
  set F : ℝ → Euc d → ℝ := fun σ z =>
    ouSg Q ν (τ - ul4bCl τ σ) (ulPert s M ρ c (w (ul4bCl τ σ))) z with hF
  have hFeq : ∀ σ ∈ Icc (0 : ℝ) τ, F σ = fun z =>
      ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) z := by
    intro σ hσ; funext z; simp only [hF, ul4bCl_eq hσ]
  have hFb : ∀ σ z, |F σ z| ≤ K := fun σ z =>
    ul4_ouSg_abs_le Q ν _ (hK _ (ul4bCl_mem hτ σ)).2 z
  have hFc : ∀ σ, Continuous (F σ) := fun σ =>
    ul5_ouSg_cont Q ν _ (hK _ (ul4bCl_mem hτ σ)).1
  have hFm : Measurable (Function.uncurry F) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun z => ?_)
      (fun σ => (hFc σ).measurable)
    have hΦ := ul4_Phi_cont H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ (le_refl τ) hwτ z
    exact hΦ.comp_continuous (ul4bCl_cont τ) (fun σ => ul4bCl_mem hτ σ)
  have hint : Integrable (Function.uncurry fun σ y => F σ (ouExp Q h x + y))
      ((volume.restrict (Ioc (0 : ℝ) τ)).prod (ouLaw Q ν h)) := by
    refine Integrable.of_bound (C := K) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (hFm.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))).aestronglyMeasurable
    · show ‖F p.1 (ouExp Q h x + p.2)‖ ≤ K
      rw [Real.norm_eq_abs]; exact hFb _ _
  have e1 : ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ + h - σ) (ulPert s M ρ c (w σ)) x =
      ∫ σ in (0 : ℝ)..τ, (∫ y, F σ (ouExp Q h x + y) ∂(ouLaw Q ν h)) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hτ] at hσ
    have := congrFun (ul4b_sg_split H Q (hwτ.mem σ hσ) hh (sub_nonneg.2 hσ.2)) x
    rw [show τ + h - σ = h + (τ - σ) by ring, this, hFeq σ hσ]
    rfl
  have e2 : ouSg Q ν h (fun y => ∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) y) x =
      ∫ y, (∫ σ in (0 : ℝ)..τ, F σ (ouExp Q h x + y)) ∂(ouLaw Q ν h) := by
    show ∫ y, (∫ σ in (0 : ℝ)..τ, ouSg Q ν (τ - σ) (ulPert s M ρ c (w σ)) (ouExp Q h x + y))
      ∂(ouLaw Q ν h) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hτ] at hσ
    rw [hFeq σ hσ]
  have e3 : ∫ σ in (0 : ℝ)..τ, (∫ y, F σ (ouExp Q h x + y) ∂(ouLaw Q ν h)) =
      ∫ y, (∫ σ in (0 : ℝ)..τ, F σ (ouExp Q h x + y)) ∂(ouLaw Q ν h) := by
    simp_rw [intervalIntegral.integral_of_le hτ]
    exact integral_integral_swap hint
  unfold ulD
  rw [e1, e3, e2]

/-- decomposition `V (τ+h) = P_h (V τ) + R_τ(h)` of the Duhamel integral -/
theorem ul5_decomp (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlReg k θ T w) {τ h : ℝ} (hτ : 0 ≤ τ) (hh : 0 ≤ h) (hτh : τ + h ≤ T)
    (x : Euc d) :
    ulD Q ν s M ρ c w (τ + h) (τ + h) x = ouSg Q ν h (fun y => ulD Q ν s M ρ c w τ τ y) x +
      ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x := by
  rw [ul4b_tail H Q hτ hh (ul4_reg_mono hτh hw) x, ul5_shift H Q hw hτ hh hτh x]

/-- the remainder `R_τ(h) = ∫_0^h P_{h-σ} ulPert (w (σ+τ)) dσ` has right derivative
`ulPert (w τ) x` at `h = 0` -/
theorem ul5_R_deriv (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlReg k θ T w) {τ : ℝ} (hτ : τ ∈ Ico 0 T) (x : Euc d) :
    HasDerivWithinAt (fun h => ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x)
      (ulPert s M ρ c (w τ) x) (Ici 0) 0 := by
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ < T := hτ.2
  have hw' : UlReg k θ (T - τ) (fun σ y => w (σ + τ) y) :=
    ul4b_reg_shift (a := T - τ) hτ0 (by rwa [sub_add_cancel])
  have hI : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext y; simp [lt_iff_le_and_ne, eq_comm]
  rw [hasDerivWithinAt_iff_tendsto_slope, hI, Metric.tendsto_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨K, hK0, hK⟩ := ul5_pert_bdd H hw
  have hmemτ : τ ∈ Icc (0 : ℝ) T := ⟨hτ0, hτT.le⟩
  have hgτ : MemCb 2 (ulPert s M ρ c (w τ)) := (hK τ hmemτ).1
  obtain ⟨δ1, hδ1, hg⟩ := ul4_g_cont H.hs0 H.hsd M ρ H.hρ H.hc H.hk H.hθ hw hmemτ hε4
  have hgT : ContinuousOn (fun s' => ouSg Q ν s' (ulPert s M ρ c (w τ)) x) (Ici 0) :=
    ul4_ouSg_cont_time Q H.hν hgτ.1 (M := cbNorm 2 (ulPert s M ρ c (w τ)))
      (fun i hi y => ul3_cb_apply hgτ hi y) x
  have hR0 : ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) 0 0 x = 0 := by simp [ulD]
  have hg0 := hgT 0 (mem_Ici.2 le_rfl)
  rw [ContinuousWithinAt, ouSg_zero Q H.hν.le, Metric.tendsto_nhdsWithin_nhds] at hg0
  obtain ⟨δ2, hδ2, hs2⟩ := hg0 (ε / 4) hε4
  have hδ : 0 < min (min δ1 δ2) (T - τ) := lt_min (lt_min hδ1 hδ2) (sub_pos.2 hτT)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  have hh0 : 0 < h := hh.1
  have hhδ1 : h < δ1 := hh.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hhδ2 : h < δ2 := hh.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hhT : h < T - τ := hh.2.trans_le (min_le_right _ _)
  have hwh : UlReg k θ h (fun σ y => w (σ + τ) y) := ul4_reg_mono hhT.le hw'
  -- the integrand
  set f : ℝ → ℝ := fun σ => ouSg Q ν (h - σ) (ulPert s M ρ c (w (σ + τ))) x with hf
  have hfc : ContinuousOn f (Icc 0 h) :=
    ul4_Phi_cont H.hs0 H.hsd M ρ H.hρ H.hc Q H.hν H.hk H.hθ (le_refl h) hwh x
  have hfi : IntervalIntegrable f volume 0 h := hfc.intervalIntegrable_of_Icc hh0.le
  have hbd : ∀ σ ∈ Icc (0 : ℝ) h, ‖f σ - ulPert s M ρ c (w τ) x‖ ≤ ε / 2 := by
    intro σ hσ
    have hσT : σ + τ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hσδ : |σ + τ - τ| < δ1 := by
      rw [add_sub_cancel_right, abs_of_nonneg hσ.1]; linarith [hσ.2]
    have h1 := hg (σ + τ) hσT hσδ
    obtain ⟨ha, haK⟩ := hK (σ + τ) hσT
    have hmeas_a : Measurable (ulPert s M ρ c (w (σ + τ))) := ha.1.continuous.measurable
    have hmeas_b : Measurable (ulPert s M ρ c (w τ)) := hgτ.1.continuous.measurable
    have hsub : ouSg Q ν (h - σ) (fun y => ulPert s M ρ c (w (σ + τ)) y - ulPert s M ρ c (w τ) y) x =
        ouSg Q ν (h - σ) (ulPert s M ρ c (w (σ + τ))) x - ouSg Q ν (h - σ) (ulPert s M ρ c (w τ)) x :=
      congrFun (ul3C_sub_lin Q ν (h - σ) hmeas_a hmeas_b haK (hK τ hmemτ).2) x
    have hab : |ouSg Q ν (h - σ) (fun y => ulPert s M ρ c (w (σ + τ)) y -
        ulPert s M ρ c (w τ) y) x| ≤ ε / 4 :=
      ul4_ouSg_abs_le Q ν _ (fun y => h1 y) x
    have hs2' := hs2 (show h - σ ∈ Ici (0 : ℝ) from mem_Ici.2 (by linarith [hσ.2])) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith [hσ.2])]; linarith [hσ.1])
    rw [Real.dist_eq] at hs2'
    rw [Real.norm_eq_abs]
    have : f σ - ulPert s M ρ c (w τ) x =
        (ouSg Q ν (h - σ) (fun y => ulPert s M ρ c (w (σ + τ)) y - ulPert s M ρ c (w τ) y) x) +
        (ouSg Q ν (h - σ) (ulPert s M ρ c (w τ)) x - ulPert s M ρ c (w τ) x) := by
      rw [hsub]; simp only [hf]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith [hs2']
  have hint : ∫ σ in (0 : ℝ)..h, (f σ - ulPert s M ρ c (w τ) x) =
      ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x - h * ulPert s M ρ c (w τ) x := by
    rw [intervalIntegral.integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const]
    simp [ulD, hf]
  have hnorm : ‖∫ σ in (0 : ℝ)..h, (f σ - ulPert s M ρ c (w τ) x)‖ ≤ ε / 2 * |h - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [uIoc_of_le hh0.le] at hσ
    exact hbd σ ⟨hσ.1.le, hσ.2⟩
  rw [hint, sub_zero, abs_of_pos hh0] at hnorm
  have hslope : slope (fun h => ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x) 0 h =
      (ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x) / h := by
    rw [slope_def_field]; simp [hR0]
  rw [hslope, dist_eq_norm, Real.norm_eq_abs]
  have e : (ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x) / h - ulPert s M ρ c (w τ) x =
      (ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x - h * ulPert s M ρ c (w τ) x) / h := by
    field_simp
  rw [e, abs_div, abs_of_pos hh0, div_lt_iff₀ hh0]
  rw [Real.norm_eq_abs] at hnorm
  nlinarith

/-- **Right derivative of the Duhamel integral**. -/
theorem ul5_V_right (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) {τ : ℝ} (hτ : τ ∈ Ico 0 T) (x : Euc d) :
    HasDerivWithinAt (fun τ' => ulD Q ν s M ρ c w τ' τ' x)
      (ul5A Q ν (fun y => ulD Q ν s M ρ c w τ τ y) x + ulPert s M ρ c (w τ) x) (Ici τ) τ := by
  have hwr := hw.toReg
  have hmem : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.le⟩
  have hφ : UlClosure k θ (fun y => ulD Q ν s M ρ c w τ τ y) := (ul4b_adm H Q T w hw).mem τ hmem
  obtain ⟨C, hC, hcb⟩ := ulClosure_cb k 2 H.hk2 θ H.hθ
  obtain ⟨hφcb, -⟩ := hcb _ hφ
  have hΦ : HasDerivWithinAt (fun h => ouSg Q ν h (fun y => ulD Q ν s M ρ c w τ τ y) x)
      (ul5A Q ν (fun y => ulD Q ν s M ρ c w τ τ y) x) (Ici 0) 0 :=
    ul5_gen_right Q H.hν hφcb.1 (M := cbNorm 2 (fun y => ulD Q ν s M ρ c w τ τ y))
      (fun i hi y => ul3_cb_apply hφcb hi y) x
  have hR := ul5_R_deriv H Q hwr hτ x
  have hsum := hΦ.add hR
  have hev : (fun h => ulD Q ν s M ρ c w (τ + h) (τ + h) x) =ᶠ[𝓝[Ici 0] 0]
      fun h => ouSg Q ν h (fun y => ulD Q ν s M ρ c w τ τ y) x +
        ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) h h x := by
    filter_upwards [Icc_mem_nhdsGE (sub_pos.2 hτ.2)] with h hh
    exact ul5_decomp H Q hwr hτ.1 hh.1 (by linarith [hh.2]) x
  have h0 : ulD Q ν s M ρ c w (τ + 0) (τ + 0) x =
      ouSg Q ν 0 (fun y => ulD Q ν s M ρ c w τ τ y) x +
        ulD Q ν s M ρ c (fun σ y => w (σ + τ) y) 0 0 x :=
    ul5_decomp H Q hwr hτ.1 le_rfl (by linarith [hτ.2]) x
  have hV := hsum.congr_of_eventuallyEq hev h0
  have hsub : HasDerivWithinAt (fun τ' : ℝ => τ' - τ) 1 (Ici τ) τ :=
    (hasDerivWithinAt_id τ _).sub_const τ
  have hcomp := HasDerivWithinAt.scomp (g₁ := fun h => ulD Q ν s M ρ c w (τ + h) (τ + h) x) τ
    (by simpa using hV) hsub (fun y hy => by simpa using sub_nonneg.2 (mem_Ici.1 hy))
  refine (hcomp.congr_deriv (by simp)).congr (fun y _ => ?_) ?_
  · simp
  · simp

/-- a continuous function on `Icc 0 T × ℝ^d` is continuous in the first variable at fixed `x` -/
theorem ul5_contOn_of_joint {T : ℝ} {F : ℝ → Euc d → ℝ}
    (hF : Continuous (fun p : Icc (0 : ℝ) T × Euc d => F p.1 p.2)) (x : Euc d) :
    ContinuousOn (fun τ => F τ x) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact hF.comp (Continuous.prodMk continuous_id continuous_const)

theorem ul5_ureg_val {T : ℝ} {a : ℝ → Euc d → ℝ} (hθ : IsUlCutoff θ) (ha : UlUReg k θ T a)
    (hk : (d : ℝ) / 2 < k) :
    Continuous (fun p : Icc (0 : ℝ) T × Euc d => a p.1 p.2) := by
  obtain ⟨C, hC, hcb⟩ := ulClosure_cb k 0 (by simpa using hk) θ hθ
  refine ul5_joint_cont (E := ℝ) (U := fun σ x => a σ x) (fun σ hσ => (ha.mem σ hσ).1.continuous) (fun ε hε => ?_)
  obtain ⟨δ, hδ, hu⟩ := ha.unif (ε / C) (by positivity)
  refine ⟨δ, hδ, fun σ hσ σ' hσ' hd x => ?_⟩
  have hcl := ul4_closure_sub hθ (ha.mem σ hσ) (ha.mem σ' hσ')
  obtain ⟨hmem, hnorm⟩ := hcb _ hcl
  have h1 := ul3_cb_apply hmem (Nat.zero_le 0) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs]
  refine h1.trans (hnorm.trans ?_)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hu σ hσ σ' hσ' hd)
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  calc C * (ulNormE k θ (fun y => a σ y - a σ' y)).toReal ≤ C * (ε / C) :=
        mul_le_mul_of_nonneg_left this hC.le
    _ = ε := by field_simp

/-- joint continuity of the base generator along a uniformly strongly continuous family -/
theorem ul5_A_joint (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (hθ : IsUlCutoff θ) {T : ℝ}
    {a : ℝ → Euc d → ℝ} (ha : UlUReg k θ T a) (hk2 : (2 : ℝ) + (d : ℝ) / 2 < k) :
    Continuous (fun p : Icc (0 : ℝ) T × Euc d => ul5A Q ν (a p.1) p.2) := by
  have hk2' : ((2 : ℕ) : ℝ) + (d : ℝ) / 2 < k := by exact_mod_cast hk2
  have h1 := ul5_ureg_joint hθ ha (j := 2) hk2' (i := 1) (by norm_num)
  have h2 := ul5_ureg_joint hθ ha (j := 2) hk2' (i := 2) le_rfl
  have hG := (ul5G_cont2 Q ν).comp (continuous_snd.prodMk (h1.prodMk h2))
  have e : (fun p : Icc (0 : ℝ) T × Euc d => ul5A Q ν (a p.1) p.2) =
      (fun q : Euc d × (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Euc d) ℝ ×
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Euc d) ℝ) => ul5G Q ν q.1 q.2) ∘
      (fun p : Icc (0 : ℝ) T × Euc d => (p.2, (iteratedFDeriv ℝ 1 (a p.1) p.2,
        iteratedFDeriv ℝ 2 (a p.1) p.2))) := by
    funext p; exact ul5_A_eq Q ν _ _
  rw [e]; exact hG

/-- joint continuity of the perturbation along a uniformly strongly continuous family -/
theorem ul5_pert_joint (H : UlHyp s M ρ c ν k θ) {T : ℝ} {a : ℝ → Euc d → ℝ}
    (ha : UlUReg k θ T a) :
    Continuous (fun p : Icc (0 : ℝ) T × Euc d => ulPert s M ρ c (a p.1) p.2) := by
  refine ul5_joint_cont (E := ℝ) (U := fun σ x => ulPert s M ρ c (a σ) x) (fun σ hσ => ?_) (fun ε hε => ?_)
  · obtain ⟨Cp, hCp0, hpcb⟩ := ul4_pert_cb H.hs0 H.hsd M ρ H.hρ H.hc
    obtain ⟨Ccb, hCcb, hcb⟩ := ulClosure_cb k 4 H.hk θ H.hθ
    exact (hpcb _ (hcb _ (ha.mem σ hσ)).1).1.1.continuous
  · obtain ⟨δ, hδ, h⟩ := ul5_pert_unif H ha hε
    exact ⟨δ, hδ, fun σ hσ σ' hσ' hd z => by
      rw [Real.norm_eq_abs]; exact h σ hσ σ' hσ' hd z⟩

/-- uniform sup bound along a strongly continuous family -/
theorem ul5_val_bdd {T : ℝ} {a : ℝ → Euc d → ℝ} (hθ : IsUlCutoff θ) (ha : UlReg k θ T a)
    (hk : (d : ℝ) / 2 < k) : ∃ B : ℝ, ∀ σ ∈ Icc (0 : ℝ) T, ∀ x, |a σ x| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := ul5_ureg_bdd hθ ha (j := 0) (by simpa using hk)
  refine ⟨B, fun σ hσ x => ?_⟩
  obtain ⟨hm, hn⟩ := hB σ hσ
  have h1 := ul3_cb_apply hm (Nat.zero_le 0) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  exact h1.trans hn

/-- continuity of the data of the derivative formula along the Duhamel family -/
theorem ul5_V_contOn (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) (x : Euc d) :
    ContinuousOn (fun τ' => ulD Q ν s M ρ c w τ' τ' x) (Icc 0 T) ∧
    ContinuousOn (fun τ' => ul5A Q ν (fun y => ulD Q ν s M ρ c w τ' τ' y) x +
      ulPert s M ρ c (w τ') x) (Icc 0 T) := by
  have hV : UlUReg k θ T (fun τ y => ulD Q ν s M ρ c w τ τ y) := ul4b_adm H Q T w hw
  exact ⟨ul5_contOn_of_joint (ul5_ureg_val H.hθ hV H.hk0) x,
    (ul5_contOn_of_joint (ul5_A_joint Q ν H.hθ hV H.hk2) x).add
      (ul5_contOn_of_joint (ul5_pert_joint H hw) x)⟩

/-- **`ul5_V_hasDerivAt`: the Duhamel integral is a classical solution of `∂_τ V = L_0 V + S`.** -/
theorem ul5_V_hasDerivAt (H : UlHyp s M ρ c ν k θ) (Q : Matrix (Fin d) (Fin d) ℝ) {T : ℝ}
    {w : ℝ → Euc d → ℝ} (hw : UlUReg k θ T w) {τ : ℝ} (hτ : τ ∈ Ioo 0 T) (x : Euc d) :
    HasDerivAt (fun τ' => ulD Q ν s M ρ c w τ' τ' x)
      (ul5A Q ν (fun y => ulD Q ν s M ρ c w τ τ y) x + ulPert s M ρ c (w τ) x) τ := by
  set Vx : ℝ → ℝ := fun τ' => ulD Q ν s M ρ c w τ' τ' x with hVx
  set F : ℝ → ℝ := fun τ' => ul5A Q ν (fun y => ulD Q ν s M ρ c w τ' τ' y) x +
    ulPert s M ρ c (w τ') x with hF
  obtain ⟨hVc, hFc⟩ := ul5_V_contOn H Q hw x
  have hint : ∀ b ∈ Icc (0 : ℝ) T, Vx b = Vx 0 + ∫ t in (0 : ℝ)..b, F t := by
    intro b hb
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := Vx) (f' := F) hb.1
      (hVc.mono (Icc_subset_Icc le_rfl hb.2))
      (fun t ht => (ul5_V_right H Q hw ⟨ht.1.le, ht.2.trans_le hb.2⟩ x).mono Ioi_subset_Ici_self)
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

end Duh

end HRS.MS.Ul
