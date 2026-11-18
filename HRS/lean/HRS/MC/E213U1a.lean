import HRS.MC.E213Defs
import HRS.Equilibrium.Parametrix.PX1AuxDeriv

/-!
# Packet e213u1 (part a): Riemann--Stieltjes uniqueness/comparison, symmetry of `D³Φ`, `Kinit0_mem`

Relocations (`_proof`) of `isRS_unique`, `isRS_sub_le`, `iteratedFDeriv_three_symm`, `Kinit0_mem` of `HRS.MC.E213Plan`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U1

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- The uniform partition of `[0,T]` into `n` pieces. -/
def u1_unif (T : ℝ) (n : ℕ) : Fin (n + 1) → ℝ := fun i => (i : ℕ) * T / n

theorem u1_unif_strictMono {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) : StrictMono (u1_unif T n) := by
  intro i j hij
  unfold u1_unif
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  rw [div_lt_div_iff_of_pos_right hn']
  exact mul_lt_mul_of_pos_right this hT

theorem u1_unif_zero (T : ℝ) (n : ℕ) : u1_unif T n 0 = 0 := by simp [u1_unif]

theorem u1_unif_last {T : ℝ} (n : ℕ) (hn : 0 < n) : u1_unif T n (Fin.last n) = T := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [u1_unif]
  field_simp

theorem u1_unif_succ_sub {T : ℝ} {n : ℕ} (hn : 0 < n) (i : Fin n) :
    u1_unif T n i.succ - u1_unif T n i.castSucc = T / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [u1_unif, Fin.val_succ, Fin.val_castSucc]
  push_cast
  field_simp
  ring

theorem u1_unif_nonneg {T : ℝ} (hT : 0 < T) {n : ℕ} (i : Fin (n + 1)) : 0 ≤ u1_unif T n i := by
  unfold u1_unif
  positivity

theorem u1_unif_le {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) : u1_unif T n i ≤ T := by
  have := (u1_unif_strictMono hT hn).monotone (Fin.le_last i)
  rwa [u1_unif_last n hn] at this

/-- For every `δ > 0` there is a uniform partition with left tags and mesh `< δ`. -/
theorem u1_exists_partition {T : ℝ} (hT : 0 < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ (∀ i : Fin n, u1_unif T n i.succ - u1_unif T n i.castSucc < δ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  refine ⟨n, hn0, fun i => ?_⟩
  rw [u1_unif_succ_sub hn0]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hn']
  rw [div_lt_iff₀ hδ] at hn
  linarith

theorem isRS_unique_proof {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I I' : ℝ} (h : IsRS T S I) (h' : IsRS T S I') :
    I = I' := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := h (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, H₂⟩ := h' (ε / 2) (by linarith)
  obtain ⟨n, hn, hmesh⟩ := u1_exists_partition hT (lt_min hδ₁ hδ₂)
  have hsm := u1_unif_strictMono hT hn
  have htag : ∀ i : Fin n, u1_unif T n i.castSucc ≤ u1_unif T n i.castSucc ∧
      u1_unif T n i.castSucc ≤ u1_unif T n i.succ := fun i => ⟨le_rfl, (hsm (Fin.castSucc_lt_succ)).le⟩
  have e₁ := H₁ n (u1_unif T n) (fun i => u1_unif T n i.castSucc) hsm (u1_unif_zero T n)
    (u1_unif_last n hn) htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_left _ _))
  have e₂ := H₂ n (u1_unif T n) (fun i => u1_unif T n i.castSucc) hsm (u1_unif_zero T n)
    (u1_unif_last n hn) htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_right _ _))
  rw [Real.dist_eq]
  calc |I - I'| = |(∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) - I') -
        (∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) - I)| := by
        congr 1; ring
    _ ≤ |∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) - I'| +
        |∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) - I| := abs_sub _ _
    _ ≤ ε := by linarith

/-- Telescoping of a finite measure along the uniform partition. -/
theorem u1_sum_measure {T : ℝ} (hT : 0 < T) (ν : Measure ℝ) [IsFiniteMeasure ν] {n : ℕ} (hn : 0 < n) :
    ∑ i : Fin n, (ν (Set.Ioc (u1_unif T n i.castSucc) (u1_unif T n i.succ))).toReal =
      (ν (Set.Ioc 0 T)).toReal := by
  have hsm := u1_unif_strictMono hT hn
  have key : ∀ a b : ℝ, a ≤ b → (ν (Set.Ioc a b)).toReal = (ν (Set.Iic b)).toReal - (ν (Set.Iic a)).toReal := by
    intro a b hab
    have : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
      ext x; simp [and_comm]
    rw [this, measure_sdiff (Set.Iic_subset_Iic.2 hab) measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono (Set.Iic_subset_Iic.2 hab)) (measure_ne_top _ _)]
  have step : ∀ i : Fin n, (ν (Set.Ioc (u1_unif T n i.castSucc) (u1_unif T n i.succ))).toReal =
      (ν (Set.Iic (u1_unif T n i.succ))).toReal - (ν (Set.Iic (u1_unif T n i.castSucc))).toReal :=
    fun i => key _ _ (hsm (Fin.castSucc_lt_succ)).le
  simp_rw [step]
  set G : ℕ → ℝ := fun k => (ν (Set.Iic ((k : ℝ) * T / n))).toReal with hG
  have h1 : ∀ i : Fin n, (ν (Set.Iic (u1_unif T n i.succ))).toReal -
      (ν (Set.Iic (u1_unif T n i.castSucc))).toReal = G ((i : ℕ) + 1) - G (i : ℕ) := by
    intro i
    simp [u1_unif, hG]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => G (i + 1) - G i) n, Finset.sum_range_sub]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hGn : G n = (ν (Set.Iic T)).toReal := by simp [hG]; field_simp
  rw [hGn, key 0 T hT.le]
  simp [hG]

theorem isRS_sub_le_proof {T : ℝ} (hT : 0 < T) {S S' : ℝ → ℝ → ℝ → ℝ} {I I' : ℝ}
    (hS : IsRS T S I) (hS' : IsRS T S' I') (ν : Measure ℝ) [IsFiniteMeasure ν] (κ : ℝ)
    (h : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ T →
      |S τ u u' - S' τ u u'| ≤ κ * (ν (Set.Ioc u u')).toReal) :
    |I - I'| ≤ κ * (ν (Set.Ioc 0 T)).toReal := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := hS (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, H₂⟩ := hS' (ε / 2) (by linarith)
  obtain ⟨n, hn, hmesh⟩ := u1_exists_partition hT (lt_min hδ₁ hδ₂)
  have hsm := u1_unif_strictMono hT hn
  have htag : ∀ i : Fin n, u1_unif T n i.castSucc ≤ u1_unif T n i.castSucc ∧
      u1_unif T n i.castSucc ≤ u1_unif T n i.succ := fun i => ⟨le_rfl, (hsm (Fin.castSucc_lt_succ)).le⟩
  have e₁ := H₁ n (u1_unif T n) (fun i => u1_unif T n i.castSucc) hsm (u1_unif_zero T n)
    (u1_unif_last n hn) htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_left _ _))
  have e₂ := H₂ n (u1_unif T n) (fun i => u1_unif T n i.castSucc) hsm (u1_unif_zero T n)
    (u1_unif_last n hn) htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_right _ _))
  have hsum : |∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) -
      ∑ i : Fin n, S' (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ)| ≤
      κ * (ν (Set.Ioc 0 T)).toReal := by
    rw [← u1_sum_measure hT ν hn, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact h _ _ _ (u1_unif_nonneg hT _) le_rfl (hsm (Fin.castSucc_lt_succ)).le (u1_unif_le hT hn _)
  calc |I - I'| = |(I - ∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ)) +
        (∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) -
          ∑ i : Fin n, S' (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ)) +
        (∑ i : Fin n, S' (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) - I')| := by
        congr 1; ring
    _ ≤ |I - ∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ)| +
        |∑ i : Fin n, S (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) -
          ∑ i : Fin n, S' (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ)| +
        |∑ i : Fin n, S' (u1_unif T n i.castSucc) (u1_unif T n i.castSucc) (u1_unif T n i.succ) - I'| :=
        (abs_add_three _ _ _)
    _ ≤ κ * (ν (Set.Ioc 0 T)).toReal + ε := by
        rw [abs_sub_comm I] at *
        linarith

/-- The `n`-th derivative of a `C^3` function is symmetric (relocation of `iteratedFDeriv_three_symm`). -/
theorem iteratedFDeriv_three_symm_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Φ : B → ℝ} {x : B}
    (hΦ : ContDiffAt ℝ 3 Φ x) (σ : Equiv.Perm (Fin 3)) :
    (iteratedFDeriv ℝ 3 Φ x).domDomCongr σ = iteratedFDeriv ℝ 3 Φ x := by
  ext v
  exact HRS.Parx.iteratedFDeriv_perm hΦ σ v

set_option maxSynthPendingDepth 3 in
/-- `K_{β₀,μ°} ∈ projTensor` (no analysis of `ℓ_x` is needed: the Bochner integral of a function with values in the closed
submodule `projTensor` lies in it, being `0` in the non-integrable case). -/
theorem Kinit0_mem_proof (S : PreparedData d) (β₀ : ℝ) :
    Kinit0 S β₀ ∈ projTensor (NegSobolev d (rLvl d)) 3 := by
  have := μ0_isProb S
  unfold Kinit0 bochTensor3
  by_cases hf : Integrable (fun x => (elemTensor ![ellVec S β₀ x, ellVec S β₀ x, ellVec S β₀ x] :
      TensorDual (NegSobolev d (rLvl d)) 3)) S.μ0
  · exact HRS.MC.E213T.e213t_integral_mem _ (Submodule.isClosed_topologicalClosure _) hf
      (ae_of_all _ fun ω => HRS.MC.E213T.elemTensor3_mem _ _ _)
  · rw [integral_undef hf]
    exact Submodule.zero_mem _

end HRS.MC.E213U1

end
