import HRS.MS.Fp81S21CovRS6
import HRS.MS.Fp81S21DriftRS15
import HRS.MS.R2InterpAux50

/-! Identification of a specified covariance RS value on an arbitrary interval. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.R2Interp
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- The specified projective covariance RS value equals the cylindrical
covariance time integral whenever the coordinate `hh2` densities are
integrable. The factor `2 * C.ν` occurs exactly once, as in `IsR2JValue`. -/
theorem fp81s21_cylindrical_covariance_rs_value
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {n : ℕ}
    (hH : 0 < H)
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ u ∈ Icc (0 : ℝ) H, IsR2FutureGaussian C m H u (γ u))
    (τ : Fin n → Icc (0 : ℝ) H) (α : Fin n → MultiIndex d)
    (hcov : ∀ i j, ContinuousOn (fun u => s102_obsCov C m τ α u i j) (Icc 0 H))
    (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : MemCb 2 G)
    (Y : ℝ → OscPath d m H) (hY : ContinuousOn Y (Icc 0 H))
    (z : ℝ → (Euc d → ℝ) → ℝ)
    (F : ℝ → projTensor (OscPath d m H) 2)
    (hF : ∀ u v, 0 ≤ u → u ≤ v → v ≤ H →
      IsR2JValue C m H z (Ioc u v)
        (((F v - F u : projTensor (OscPath d m H) 2) : TensorDual (OscPath d m H) 2)))
    (hzi : ∀ i j, IntegrableOn (s102_hh2 C m τ α z i j) (Icc 0 H))
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H) (I : ℝ)
    (hI : fp81s21_IsRSOn q r (fun t u v =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn γ
          (fun w => G (s102_obs τ α w)) t) (Y t)) (F v - F u)) I) :
    IntegrableOn (fun u => ∑ i, ∑ j,
      iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u)
        (s102_obs τ α (Y u))
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
      (2 * C.ν * s102_hh2 C m τ α z i j u)) (Ioc q r) ∧
    I = ∫ u in Ioc q r, ∑ i, ∑ j,
      iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u)
        (s102_obs τ α (Y u))
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
      (2 * C.ν * s102_hh2 C m τ α z i j u) := by
  let g : Fin n × Fin n → ℝ → ℝ := fun p t =>
    iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G t)
      (s102_obs τ α (Y t)) ![EuclideanSpace.single p.1 1, EuclideanSpace.single p.2 1]
  let h : Fin n × Fin n → ℝ → ℝ := fun p u =>
    2 * C.ν * s102_hh2 C m τ α z p.1 p.2 u
  have hcont := HRS.MC.Sec7.S7PIS3.s7_PIH_heat_cont_proof H _ hcov
    (fun u hu => (s102_obs_law C (hγ u hu) τ α).1) G 2 hG 2 le_rfl
  have hg : ∀ p, ContinuousOn (g p) (Icc 0 H) := by
    intro p
    have h1 : ContinuousOn (fun t : ℝ => (t, s102_obs τ α (Y t))) (Icc 0 H) :=
      continuousOn_id.prodMk ((s102_obs τ α).continuous.comp_continuousOn hY)
    have h2 := hcont.comp h1 (fun t ht => ⟨ht, mem_univ _⟩)
    exact (HRS.MC.Sec7.S7PIL.S7PIL_ev
      (![EuclideanSpace.single p.1 (1 : ℝ), EuclideanSpace.single p.2 1] :
        Fin 2 → EuclideanSpace ℝ (Fin n))).continuous.comp_continuousOn h2
  have hsub : Icc q r ⊆ Icc (0 : ℝ) H := Icc_subset_Icc hq hr
  have hh : ∀ p, IntegrableOn (h p) (Icc q r) := by
    intro p
    exact ((hzi p.1 p.2).mono_set hsub).const_mul _
  have hint : IntegrableOn (fun t => ∑ p : Fin n × Fin n, g p t * h p t) (Ioc q r) := by
    apply IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
    exact integrable_finsetSum _ fun p _ =>
      IntegrableOn.continuousOn_mul ((hg p).mono hsub) (hh p) isCompact_Icc
  have hint' : IntegrableOn (fun t => ∑ i, ∑ j,
      iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G t)
        (s102_obs τ α (Y t)) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
      (2 * C.ν * s102_hh2 C m τ α z i j t)) (Ioc q r) := by
    simpa only [Fintype.sum_prod_type, g, h] using hint
  have hd : fp81s21_IsRSOn q r (fun t u v =>
      ∑ p : Fin n × Fin n, g p t * ∫ x in Ioc u v, h p x)
      (∫ x in Ioc q r, ∑ p : Fin n × Fin n, g p x * h p x) := by
    by_cases hlt : q < r
    · exact fp81s21_isRSOn_density q r hlt g h
        (fun p => (hg p).mono hsub) hh
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      simpa using fp81s21_isRSOn_zero q
        (fun t u v => ∑ p : Fin n × Fin n, g p t * ∫ x in Ioc u v, h p x)
  have hd' : fp81s21_IsRSOn q r (fun t u v =>
      fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn γ
          (fun w => G (s102_obs τ α w)) t) (Y t)) (F v - F u))
      (∫ x in Ioc q r, ∑ p : Fin n × Fin n, g p x * h p x) := by
    apply (s102_isR2RS_iff _ _ _).2
    apply HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr ((s102_isR2RS_iff _ _ _).1 hd)
    intro t u v ht hu huv hv
    dsimp only
    have htH : q + t ∈ Icc (0 : ℝ) H :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hu0 : 0 ≤ q + u := by linarith
    have huv' : q + u ≤ q + v := by linarith
    have hvH : q + v ≤ H := by linarith
    have hJ := hF (q + u) (q + v) hu0 huv' hvH
    have hcoords : fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn γ
          (fun w => G (s102_obs τ α w)) (q + t)) (Y (q + t)))
        (F (q + v) - F (q + u)) =
        ∑ i, ∑ j, g (i, j) (q + t) *
          (2 * C.ν * ∫ x in Ioc (q + u) (q + v) ∩
            Icc (0 : ℝ) (min (τ i : ℝ) (τ j : ℝ)),
              z x (fun y => inner ℝ
                (gradient (propagatorW C x (τ i) (oscTestFun m (α i))) y)
                (gradient (propagatorW C x (τ j) (oscTestFun m (α j))) y))) := by
      change ((F (q + v) - F (q + u) : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) _ = _
      rw [(s102_heat_obs_deriv C γ hγ τ α G hG (q + t) htH (Y (q + t))).2,
        s102_cyl_expand τ α _ _]
      simp only [ContinuousMultilinearMap.sum_apply,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul,
        map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [s102_J_gen (hJ) τ α i j]
    have hentry : ∀ i j : Fin n,
        (∫ x in Ioc (q + u) (q + v), h (i, j) x) =
          2 * C.ν * ∫ x in Ioc (q + u) (q + v) ∩
            Icc (0 : ℝ) (min (τ i : ℝ) (τ j : ℝ)),
              z x (fun y => inner ℝ
                (gradient (propagatorW C x (τ i) (oscTestFun m (α i))) y)
                (gradient (propagatorW C x (τ j) (oscTestFun m (α j))) y)) := by
      intro i j
      calc
        _ = 2 * C.ν * ∫ x in Ioc (q + u) (q + v),
            s102_hh2 C m τ α z i j x := by
              rw [integral_const_mul]
        _ = _ := by
              rw [s102_hh2_integral C m τ α z i j hu0]
              
    have htarget : (∑ p : Fin n × Fin n, g p (q + t) *
          ∫ x in Ioc (q + u) (q + v), h p x) =
        ∑ i, ∑ j, g (i, j) (q + t) *
          (2 * C.ν * ∫ x in Ioc (q + u) (q + v) ∩
            Icc (0 : ℝ) (min (τ i : ℝ) (τ j : ℝ)),
              z x (fun y => inner ℝ
                (gradient (propagatorW C x (τ i) (oscTestFun m (α i))) y)
                (gradient (propagatorW C x (τ j) (oscTestFun m (α j))) y))) := by
      calc
        _ = ∑ p : Fin n × Fin n, g p (q + t) *
              (2 * C.ν * ∫ x in Ioc (q + u) (q + v) ∩
                Icc (0 : ℝ) (min (τ p.1 : ℝ) (τ p.2 : ℝ)),
                  z x (fun y => inner ℝ
                    (gradient (propagatorW C x (τ p.1) (oscTestFun m (α p.1))) y)
                    (gradient (propagatorW C x (τ p.2) (oscTestFun m (α p.2))) y))) := by
                apply Finset.sum_congr rfl
                rintro ⟨i, j⟩ _
                rw [hentry i j]
        _ = _ := by
              simp only [Fintype.sum_prod_type]
    rw [htarget, hcoords]
  refine ⟨hint', ?_⟩
  by_cases hlt : q < r
  · have hval := fp81s21_isRSOn_unique hlt hI hd'
    calc
      I = ∫ x in Ioc q r, ∑ p : Fin n × Fin n, g p x * h p x := hval
      _ = ∫ x in Ioc q r, ∑ i, ∑ j,
            iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G x)
              (s102_obs τ α (Y x))
              ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
            (2 * C.ν * s102_hh2 C m τ α z i j x) := by
              congr 1
              funext x
              simp only [Fintype.sum_prod_type, g, h]
  · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    simpa using fp81s21_isRSOn_zero_forces hI

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_cylindrical_covariance_rs_value
end
