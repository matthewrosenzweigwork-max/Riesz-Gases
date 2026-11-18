import HRS.MS.S111K2B04j
import HRS.MS.CovMeasAux22

/-!
# S11.1 continuation, B04 (part 11): the coordinates and the evaluation formula for `Dfun`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.R2WinErr HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {S T u Pw : ℝ}
  {z : ℝ → (Euc d → ℝ) → ℝ}

/-- The `α`-th coordinate as a continuous linear functional. -/
def s111k2_coordCLM (d : ℕ) (m : ℝ) (α : MultiIndex d) : OscDual d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => OscDual.coord u α
      map_add' := fun u v => OscDual.coord_add u v α
      map_smul' := fun c u => OscDual.coord_smul c u α } 1 (fun u => by
    have h := lp.norm_apply_le_norm (p := 2) (E := fun _ : MultiIndex d => ℝ) (by simp)
      (show lp (fun _ : MultiIndex d => ℝ) 2 from u) α
    have hn : ‖u‖ = ‖(show lp (fun _ : MultiIndex d => ℝ) 2 from u)‖ := rfl
    rw [one_mul, hn]
    exact h)

lemma s111k2_coordCLM_apply (α : MultiIndex d) (u : OscDual d m) :
    s111k2_coordCLM d m α u = OscDual.coord u α := rfl

/-! ### Bounded smooth functions are weighted tests; closure properties -/

def S111k2Bdd (r : ℕ) (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ r f ∧ ∃ B : ℝ, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B

lemma S111k2Bdd.test {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {f : Euc d → ℝ} (hf : S111k2Bdd r f) :
    IsR2WeightedTest r P f := by
  obtain ⟨hc, B, hB⟩ := hf
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  exact ⟨hc, lt_of_le_of_lt (s57p_E_le_cb hP hB0 hB) ENNReal.ofReal_lt_top⟩

lemma S111k2Bdd.add {r : ℕ} {f g : Euc d → ℝ} (hf : S111k2Bdd r f) (hg : S111k2Bdd r g) :
    S111k2Bdd r (f + g) := by
  obtain ⟨hf1, B1, hB1⟩ := hf
  obtain ⟨hg1, B2, hB2⟩ := hg
  refine ⟨hf1.add hg1, B1 + B2, fun j hj x => ?_⟩
  rw [iteratedFDeriv_add_apply (hf1.of_le (by exact_mod_cast hj)).contDiffAt
    (hg1.of_le (by exact_mod_cast hj)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hB1 j hj x) (hB2 j hj x))

lemma S111k2Bdd.smul {r : ℕ} {f : Euc d → ℝ} (hf : S111k2Bdd r f) (c : ℝ) :
    S111k2Bdd r (c • f) := by
  obtain ⟨hf1, B1, hB1⟩ := hf
  refine ⟨hf1.const_smul c, |c| * B1, fun j hj x => ?_⟩
  have := iteratedFDeriv_const_smul_apply (a := c) (x := x) (hf1.of_le (by exact_mod_cast hj)).contDiffAt
  rw [this, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB1 j hj x) (abs_nonneg _)

lemma S111k2Bdd.zero (r : ℕ) : S111k2Bdd (d := d) r (fun _ => (0 : ℝ)) := by
  refine ⟨contDiff_const, 0, fun j hj x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

/-! ### Linearity of the propagator and of `z^v` on finite combinations -/

lemma s111k2_prop_combo {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}
    (hW : S111k2WindowOrbitInput C m c0 r b) {v s : ℝ} (hv : 0 ≤ v) (hvs : v ≤ s)
    (S0 : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    propagatorW C v s (fun x => ∑ α ∈ S0, c α * oscTestFun m α x) =
      fun x => ∑ α ∈ S0, c α * propagatorW C v s (oscTestFun m α) x := by
  classical
  induction S0 using Finset.induction_on with
  | empty =>
    have h0 : IsR2DualCombo m (fun _ : Euc d => (0 : ℝ)) := ⟨∅, fun _ => 0, by simp⟩
    have := hW.linear v s hv hvs (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 1 h0 h0
    have e : ((fun _ : Euc d => (0 : ℝ)) + (1 : ℝ) • (fun _ : Euc d => (0 : ℝ))) = fun _ => 0 := by
      funext x; simp
    rw [e] at this
    funext x
    have hx := congrFun this x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] at hx
    simp only [Finset.sum_empty]
    linarith
  | insert β S0 hβ ih =>
    have hphi : IsR2DualCombo m (fun x => ∑ α ∈ S0, c α * oscTestFun m α x) := ⟨S0, c, rfl⟩
    have hpsi : IsR2DualCombo m (oscTestFun m β) := s111k2_dualCombo_single m β
    have := hW.linear v s hv hvs _ _ (c β) hphi hpsi
    have e : (fun x => ∑ α ∈ insert β S0, c α * oscTestFun m α x) =
        (fun x => ∑ α ∈ S0, c α * oscTestFun m α x) + (c β) • oscTestFun m β := by
      funext x; simp [Finset.sum_insert hβ, add_comm]
    rw [e, this, ih]
    funext x
    simp [Finset.sum_insert hβ, add_comm]

lemma s111k2_z_combo (h : S111k2Drift C m c0 r b S T u Pw z) {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (u + T))
    {s : ℝ} (hvs : v ≤ s) (S0 : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    z v (propagatorW C v s (fun x => ∑ α ∈ S0, c α * oscTestFun m α x)) =
      ∑ α ∈ S0, c α * z v (propagatorW C v s (oscTestFun m α)) := by
  classical
  have hP' : (d : ℝ) < 2 * Pw := by linarith [h.hP]
  rw [s111k2_prop_combo h.hW hv.1 hvs]
  have hbdd : ∀ α, S111k2Bdd r (propagatorW C v s (oscTestFun m α)) := by
    intro α
    obtain ⟨h1, h2, B0, h3⟩ := s111k2_orbit_data h.hW α hv.1 hvs
    refine ⟨h1.of_le (by exact_mod_cast Nat.le_succ r), max B0 (b α * Real.exp (-c0 * (s - v))), fun j hj x => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact (h3 x).trans (le_max_left _ _)
    · exact (h2 j hj0 (by omega) x).trans (le_max_right _ _)
  have hone := h.hone v hv
  have hlin := h.hz.1 v hv
  -- induction
  have key : ∀ S1 : Finset (MultiIndex d),
      S111k2Bdd r (fun x => ∑ α ∈ S1, c α * propagatorW C v s (oscTestFun m α) x) ∧
      z v (fun x => ∑ α ∈ S1, c α * propagatorW C v s (oscTestFun m α) x) =
        ∑ α ∈ S1, c α * z v (propagatorW C v s (oscTestFun m α)) := by
    intro S1
    induction S1 using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      refine ⟨S111k2Bdd.zero (d := d) r, ?_⟩
      have h0 := hlin.2.1 0 (fun _ : Euc d => (1 : ℝ))
        ⟨contDiff_const, by
          refine lt_of_le_of_lt (s57p_E_le_cb hP' (B := 1) zero_le_one (fun j hj x => ?_)) ENNReal.ofReal_lt_top
          rcases Nat.eq_zero_or_pos j with rfl | hj0
          · simp
          · rw [iteratedFDeriv_const_of_ne (by omega)]; simp⟩
      have e : ((0 : ℝ) • fun _ : Euc d => (1 : ℝ)) = fun _ => 0 := by funext x; simp
      rw [e, hone] at h0
      simpa using h0
    | insert β S1 hβ ih =>
      have e : (fun x => ∑ α ∈ insert β S1, c α * propagatorW C v s (oscTestFun m α) x) =
          (c β • propagatorW C v s (oscTestFun m β)) +
            (fun x => ∑ α ∈ S1, c α * propagatorW C v s (oscTestFun m α) x) := by
        funext x; simp [Finset.sum_insert hβ]
      rw [e]
      refine ⟨(S111k2Bdd.smul (hbdd β) (c β)).add ih.1, ?_⟩
      have t1 := S111k2Bdd.test hP' (S111k2Bdd.smul (hbdd β) (c β))
      have t2 := S111k2Bdd.test hP' ih.1
      have t0 := S111k2Bdd.test hP' (hbdd β)
      rw [hlin.1 _ _ t1 t2, hlin.2.1 (c β) _ t0, ih.2, Finset.sum_insert hβ]
  exact (key S0).2

lemma s111k2_coord_W (h : S111k2Drift C m c0 r b S T u Pw z) {v τ : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) (u + T)) (α : MultiIndex d) :
    OscDual.coord (s111k2_W C m z u v τ) α =
      if v ≤ u + τ then z v (propagatorW C v (u + τ) (oscTestFun m α)) else 0 := by
  by_cases hvτ : v ≤ u + τ
  · rw [if_pos hvτ]
    have e : s111k2_W C m z u v τ = s111k2_Y C m z v (u + τ) := by unfold s111k2_W; rw [if_pos hvτ]
    rw [e]
    unfold s111k2_Y
    exact s57p_coord_ellVec (s111k2_Ycoord_memell h.hW h.hbs h.hP h.hz hv (h.hone v hv) (h.dual_lt hv) hvτ) α
  · rw [if_neg hvτ]
    have e : s111k2_W C m z u v τ = 0 := by unfold s111k2_W; rw [if_neg hvτ]
    rw [e]; rfl

lemma s111k2_Dfun_eval (h : S111k2Drift C m c0 r b S T u Pw z) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) {φ : Euc d → ℝ} (hφ : IsR2DualCombo m φ) :
    OscDual.eval (s111k2_Dfun C m z u a b' τ) φ =
      ∫ v in Set.Ioc a b' ∩ Set.Icc 0 (u + τ), z v (propagatorW C v (u + τ) φ) := by
  classical
  obtain ⟨S0, c, rfl⟩ := hφ
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  have hI := s111k2_W_integrable h hτ ha hab hb
  have hcoord : ∀ α, IntegrableOn (fun v => OscDual.coord (s111k2_W C m z u v τ) α) (Set.Ioc a b') :=
    fun α => (s111k2_coordCLM d m α).integrable_comp hI
  rw [s101_eval_combo]
  have e1 : ∀ α, OscDual.coord (s111k2_Dfun C m z u a b' τ) α =
      ∫ v in Set.Ioc a b', OscDual.coord (s111k2_W C m z u v τ) α := fun α => by
    unfold s111k2_Dfun
    exact (ContinuousLinearMap.integral_comp_comm (s111k2_coordCLM d m α) hI).symm
  simp_rw [e1]
  have e2 : ∑ α ∈ S0, c α * ∫ v in Set.Ioc a b', OscDual.coord (s111k2_W C m z u v τ) α =
      ∫ v in Set.Ioc a b', ∑ α ∈ S0, c α * OscDual.coord (s111k2_W C m z u v τ) α := by
    rw [integral_finset_sum _ (fun α _ => (hcoord α).const_mul (c α))]
    exact Finset.sum_congr rfl fun α _ => (integral_const_mul _ _).symm
  have e3 : ∫ v in Set.Ioc a b' ∩ Set.Icc 0 (u + τ),
        z v (propagatorW C v (u + τ) (fun x => ∑ α ∈ S0, c α * oscTestFun m α x)) =
      ∫ v in Set.Ioc a b', (Set.Iic (u + τ)).indicator
        (fun v => z v (propagatorW C v (u + τ) (fun x => ∑ α ∈ S0, c α * oscTestFun m α x))) v := by
    have hset : Set.Ioc a b' ∩ Set.Icc 0 (u + τ) = Set.Ioc a b' ∩ Set.Iic (u + τ) := by
      ext v
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, ha.trans h1.1.le, h2⟩
    rw [setIntegral_indicator measurableSet_Iic, hset]
  rw [e2, e3]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  simp only [s111k2_coord_W h (hsub hv)]
  by_cases hvτ : v ≤ u + τ
  · simp only [if_pos hvτ, Set.indicator_of_mem (Set.mem_Iic.2 hvτ)]
    exact (s111k2_z_combo h (hsub hv) hvτ S0 c).symm
  · simp only [if_neg hvτ, Set.indicator_of_notMem (fun hh => hvτ (Set.mem_Iic.1 hh))]
    simp

end HRS.MS.S111K2
