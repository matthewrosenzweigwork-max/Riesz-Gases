import HRS.MC.CepP5Aux6

/-!
# Packet P5: the density solves the classical forward equation
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem continuousOn_Fwd {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O) {c : ℝ}
    {b : ℝ × (Fin N → Euc d) → Fin N → Euc d} (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b O)
    {g : ℝ × (Fin N → Euc d) → ℝ} (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g O) :
    ContinuousOn (Fwd c b g) O := by
  unfold Fwd
  refine (continuousOn_const.mul (continuousOn_finset_sum _ fun k _ => ?_)).sub
    (continuousOn_finset_sum _ fun k _ => ?_)
  · exact (contDiffOn_fderiv2_apply hO hg _ _).continuousOn
  · exact (contDiffOn_fderiv_apply hO ((contDiffOn_bk hb k).mul hg) _).continuousOn

/-- The forward equation under the additional (necessary) hypothesis `f ≥ 0`.  Without `hf0` the statement of the spec
`cep_P5_forward_equation` is not provable: `hρ` only involves `ENNReal.ofReal f`, so `f` may be altered by any
smooth negative function on an open component of `(0,T) × Ω_N` that carries no mass of `ρ`. -/
theorem cep_P5_forward_equation_core [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {f : ℝ → Config d N → ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N)))) :
    ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, HasDerivAt (fun r' => f r' x) (fkeForward D f r x) r := by
  classical
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  set O : Set (ℝ × (Fin N → Euc d)) := Ioo 0 T ×ˢ liftedFree d N with hOdef
  have hO : IsOpen O := isOpen_Ioo.prod (isOpen_liftedFree d N)
  set g : ℝ × (Fin N → Euc d) → ℝ := fun p => f p.1 (mkC p.2) with hgdef
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g O := hfs
  have hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bC (N := N) D) O := contDiffOn_bC D hV
  have hgm : Measurable (ghat f T) := measurable_ghat hfs
  -- the weak equation for `g`
  have hweak : ∀ F, CK O F → ∫ p, (Fwd D.invβ (bC D) g p - fderiv ℝ g p (1, 0)) * F p = 0 := by
    intro F hFk
    rw [← ibp_Lop hO hg hb D.invβ hFk]
    have h := weak_ghat hN hV hT hX hF hgm hf0 hρ hFk.smooth hFk.compact hFk.sub
    have hcongr : ∫ p, g p * HRS.MC.CepP3.Lop D.invβ (bC D) F p =
        ∫ p, ghat f T p * HRS.MC.CepP3.Lop D.invβ (bC D) F p := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      show g p * _ = ghat f T p * _
      by_cases hp : p ∈ O
      · rw [ghat_of_mem hp]
      · rw [Lop_eq_zero_off _ _ (fun h => hp (hFk.sub h)), mul_zero, mul_zero]
    exact hcongr.trans h
  -- the defect
  set E : ℝ × (Fin N → Euc d) → ℝ := fun p => fderiv ℝ g p (1, 0) - Fwd D.invβ (bC D) g p with hE
  have hEc : ContinuousOn E O :=
    (contDiffOn_fderiv_apply hO hg _).continuousOn.sub (continuousOn_Fwd hO hb hg)
  have hae := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (f := E)
    (hEc.locallyIntegrableOn hO.measurableSet) (by
      intro F hFs hFc hFO
      have := hweak F ⟨hFs, hFc, hFO⟩
      rw [← neg_eq_zero, ← integral_neg] at this
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [smul_eq_mul, hE]
      ring)
  have hEq : Set.EqOn E 0 O := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hO hEc continuousOn_const
    exact (ae_restrict_iff' hO.measurableSet).2 (hae.mono fun p hp hpO => hp hpO)
  intro r hr x hx
  have hpO : (r, repC x) ∈ O := by
    refine ⟨hr, ?_⟩
    show (fun i => Torus.mk (repC x i)) ∉ collisionSet d N
    rw [show (fun i => Torus.mk (repC x i)) = x from mk_repC x]
    exact hx
  have h0 : E (r, repC x) = 0 := hEq hpO
  have hfw : fkeForward D f r x = fderiv ℝ g (r, repC x) (1, 0) := by
    rw [fkeForward_eq hO hg hb hpO]
    have : fderiv ℝ g (r, repC x) (1, 0) - Fwd D.invβ (bC D) g (r, repC x) = 0 := h0
    linarith
  rw [hfw]
  have hgd : DifferentiableAt ℝ g (r, repC x) :=
    (hg.contDiffAt (hO.mem_nhds hpO)).differentiableAt (by simp)
  have hfun : (fun r' => f r' x) = fun r' => g (r', repC x) := by
    funext r'
    show f r' x = f r' (mkC (repC x))
    rw [show mkC (repC x) = x from mk_repC x]
  rw [hfun]
  exact hgd.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r (repC x)))

end HRS.MC.CepP5
