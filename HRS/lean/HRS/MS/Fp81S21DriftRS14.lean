import HRS.MS.Fp81S21DriftRS13
import HRS.MS.R2InterpAux48

/-! Identification of the cylindrical drift RS value on subintervals. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.R2Interp
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- Any specified RS value for the physical drift cumulative equals the
unsigned cylindrical drift integral on the same admissible subinterval. -/
theorem fp81s21_cylindrical_drift_rs_value
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {k : ℕ}
    {c : MultiIndex d → ℝ} {Pw : ℝ}
    {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m H k c)
    (hlin : S102Lin C m H) (hb : S102Drift C m H k Pw b Mb) (hH : 0 < H)
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ u ∈ Icc (0 : ℝ) H, IsR2FutureGaussian C m H u (γ u))
    {n : ℕ} (τ : Fin n → Icc (0 : ℝ) H) (α : Fin n → MultiIndex d)
    (hcov : ∀ i j, ContinuousOn (fun u => s102_obsCov C m τ α u i j) (Icc 0 H))
    (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : MemCb 2 G)
    (Y F : ℝ → OscPath d m H) (hY : ContinuousOn Y (Icc 0 H))
    (hF : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H → F v - F u = r2DriftInc C m H b u v)
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H) (I : ℝ)
    (hI : fp81s21_IsRSOn q r (fun t u v =>
      fderiv ℝ (r2HeatFn γ (fun w => G (s102_obs τ α w)) t) (Y t) (F v - F u)) I) :
    IntegrableOn (fun u => ∑ i,
      fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α (Y u))
        (EuclideanSpace.single i 1) * s102_hh C m τ α b i u) (Ioc q r) ∧
    I = ∫ u in Ioc q r, ∑ i,
      fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α (Y u))
        (EuclideanSpace.single i 1) * s102_hh C m τ α b i u := by
  let g : Fin n → ℝ → ℝ := fun i t => fderiv ℝ
    (gaussHeat (s102_obsCov C m τ α) G t) (s102_obs τ α (Y t))
      (EuclideanSpace.single i 1)
  let h : Fin n → ℝ → ℝ := fun i => s102_hh C m τ α b i
  have hcont := HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof H _ hcov
    (fun u hu => (s102_obs_law C (hγ u hu) τ α).1) G 2 hG 1 (by norm_num)
  have hg : ∀ i, ContinuousOn (g i) (Icc 0 H) := by
    intro i
    have h1 : ContinuousOn (fun t : ℝ => (t, s102_obs τ α (Y t))) (Icc 0 H) :=
      continuousOn_id.prodMk ((s102_obs τ α).continuous.comp_continuousOn hY)
    have h2 := hcont.comp h1 (fun t ht => ⟨ht, mem_univ _⟩)
    have h3 := ((HRS.MC.Sec7.S7PIL.S7PIL_ev (fun _ : Fin 1 =>
      (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n)))).continuous.comp_continuousOn h2)
    refine h3.congr fun t ht => ?_
    simp [g, HRS.MC.Sec7.S7PIL.S7PIL_ev_apply, iteratedFDeriv_one_apply]
  have hh : ∀ i, IntegrableOn (h i) (Icc 0 H) :=
    fun i => s102_hh_integrableOn hP hD hb τ α i
  have hsub : Icc q r ⊆ Icc (0 : ℝ) H := Icc_subset_Icc hq hr
  have hint : IntegrableOn (fun t => ∑ i, g i t * h i t) (Ioc q r) := by
    apply IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
    exact integrable_finsetSum _ fun i _ =>
      IntegrableOn.continuousOn_mul ((hg i).mono hsub) ((hh i).mono_set hsub) isCompact_Icc
  refine ⟨hint, ?_⟩
  by_cases hlt : q < r
  · have hd := fp81s21_isRSOn_density q r hlt g h
      (fun i => (hg i).mono hsub) (fun i => (hh i).mono_set hsub)
    have hd' : fp81s21_IsRSOn q r (fun t u v =>
        fderiv ℝ (r2HeatFn γ (fun w => G (s102_obs τ α w)) t) (Y t) (F v - F u))
        (∫ t in Ioc q r, ∑ i, g i t * h i t) := by
      apply (s102_isR2RS_iff _ _ _).2
      apply HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr ((s102_isR2RS_iff _ _ _).1 hd)
      intro t u v ht hu huv hv
      have htH : q + t ∈ Icc (0 : ℝ) H := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hu0 : 0 ≤ q + u := by linarith
      have huv' : q + u ≤ q + v := by linarith
      have hvH : q + v ≤ H := by linarith
      dsimp only
      rw [hF (q + u) (q + v) hu0 huv' hvH,
        s102_heat_fderiv_apply γ hγ τ α hG htH]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [s102_obs_driftInc hP hD hlin hb hH τ α hu0 (by linarith) i,
        s102_hh_integral]
    exact fp81s21_isRSOn_unique hlt hI hd'
  · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    simpa using fp81s21_isRSOn_zero_forces hI

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_cylindrical_drift_rs_value
