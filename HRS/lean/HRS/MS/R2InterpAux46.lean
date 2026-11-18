import HRS.MS.R2InterpAux45
import HRS.MC.S7PIS3Heat

/-!
# S10.2 (worker S102), part 46 (packet F8, deterministic pieces): the observation of a drift increment, continuity of the covariance and of the heat derivatives
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
  {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}

/-- `obs_i(𝒟_b((a,a'])) = ∫_{(a, a'∧τ_i]} b^u(U^{u,τ_i}φ_{α_i}) du`. -/
theorem s102_obs_driftInc (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 < T) {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (i : Fin q) :
    s102_obs τ α (r2DriftInc C m T b a a') i =
      ∫ u in Ioc a (min a' (τ i : ℝ)), b u (propagatorW C u (τ i) (oscTestFun m (α i))) := by
  have ht : (τ i : ℝ) ∈ Icc (0 : ℝ) T := (τ i).2
  have h1 : s102_obs τ α (r2DriftInc C m T b a a') i =
      s102_coordCLM (m := m) (α i) (r2PathAt (r2DriftInc C m T b a a') (τ i)) := by
    rw [s102_r2PathAt_of_mem _ ht, s102_obs_apply]
    rfl
  rw [h1, s102_driftInc_at hP hD hlin hb hT.le ha ha' ht]
  unfold s102_g
  have hs : Ioc a (min a' (τ i : ℝ)) ⊆ Icc 0 (τ i : ℝ) := fun u hu =>
    ⟨ha.trans hu.1.le, hu.2.trans (min_le_right _ _)⟩
  have hint := s102_w_integrableOn hP hD hlin hb ht hs measurableSet_Ioc
  rw [← ContinuousLinearMap.integral_comp_comm _ hint]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have huT : u ∈ Icc (0 : ℝ) T := ⟨ha.trans hu.1.le, (hu.2.trans (min_le_right _ _)).trans ht.2⟩
  have := s102_Vprop_coord hP hD (hb.hZ u huT) hlin huT (t := τ i) ⟨hu.2.trans (min_le_right _ _), ht.2⟩ (α i)
  exact this

/-- The covariance entries along the grid are continuous in `u ∈ [0,T]`. -/
theorem s102_obsCov_cont (hT : 0 < T) (L : ℕ)
    (hG : S102GramInt C m hT L) (k k' : Fin (s102_q d L)) :
    ContinuousOn (fun u => s102_obsCov C m (s102_tauk hT L) (s102_alk L) u k k') (Icc 0 T) := by
  have hI := s102_rateM_integrableOn (C := C) (m := m) hT L hG k k'
  have hH := s102_H_continuousOn (T := T) hT.le hI
  refine (continuousOn_const (c := s102_obsCov C m (s102_tauk hT L) (s102_alk L) 0 k k')).sub hH |>.congr ?_
  intro u hu
  have h := s102_obsCov_eq_rate hT L hG (le_refl 0) hu.1 hu.2 k k'
  rw [s102_setIntegral_Mb (le_refl 0) hu.1 hu.2 hI] at h
  have h0 : s102_H (fun ρ => s102_rateM C m hT L ρ k k') 0 = 0 := by simp [s102_H]
  rw [h0, sub_zero] at h
  rw [Pi.sub_apply]
  linarith

/-- Continuity of the derivatives of the heat function of the observation Gaussian. -/
theorem s102_heatDeriv_cont (hT : 0 < T) (L : ℕ)
    (hG : S102GramInt C m hT L)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} {k : ℕ} (hGk : MemCb k G) {j : ℕ} (hj : j ≤ k) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (s102_q d L)) =>
      iteratedFDeriv ℝ j (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
  HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof T _ (fun k k' => s102_obsCov_cont hT L hG k k')
    (fun u hu => (s102_obs_law C (hγ u hu) (s102_tauk hT L) (s102_alk L)).1) G k hGk j hj

end HRS.MS.R2Interp

end
