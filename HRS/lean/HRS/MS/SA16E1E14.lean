import HRS.MS.SA16E1E14b

/-!
# S.A.16 E14: `coefficient_time_regular`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Coeff

variable {d : ℕ}

theorem e14_base {S : Set ℝ} {g : ℝ → Euc d → ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hint : ∀ r ∈ S, Integrable (g r)) (hnn : ∀ r ∈ S, ∀ x, 0 ≤ g r x)
    (hone : ∀ r ∈ S, ∫ x, g r x = 1) (hgc : ∀ r ∈ S, Continuous (g r))
    (hlip : ∀ r ∈ S, ∀ x y, |g r x - g r y| ≤ Λ * ‖x - y‖)
    (hw : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) S) :
    ContinuousOn (fun q : ℝ × Euc d => g q.1 q.2) (S ×ˢ univ) := by
  have hunif : TendstoUniformlyOn (fun n => e14M n g) (fun q : ℝ × Euc d => g q.1 q.2) atTop
      (S ×ˢ univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (Λ / ε)
    filter_upwards [eventually_ge_atTop N] with n hn q hq
    have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have := e14_unif_approx hΛ (hint q.1 hq.1) (hgc q.1 hq.1) (hlip q.1 hq.1) n q.2
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt (by simpa using this) ?_
    rw [div_lt_iff₀ hn1]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  exact hunif.continuousOn ((Eventually.of_forall fun n => e14_M_cont hint hnn hone hw n).frequently)

theorem e14_bnd {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hμ : CoeffHypRd s m Λ T μ) {r : ℝ}
    (hr : r ∈ Icc (0:ℝ) T) {j : ℕ} (hj : j ≤ m + 3) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (μ r) x‖ ≤ Λ := by
  obtain ⟨hmem, -, hsum⟩ := hμ.regular.1 r hr
  have h1 : ‖iteratedFDeriv ℝ j (μ r) x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (μ r) z‖ :=
    le_ciSup (hmem.2 j hj) x
  have h2 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ j (μ r) z‖) ≤ cbNorm (m + 3) (μ r) := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j (μ r) z‖)
      (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have h3 : 0 ≤ (weightedSupE (m + 3) ((d : ℝ) + 3) (μ r)).toReal := ENNReal.toReal_nonneg
  linarith

theorem e14_step {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hT : 0 ≤ T) (hμ : CoeffHypRd s m Λ T μ)
    {j : ℕ} (hj : j + 1 ≤ m + 2)
    (hprev : ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (μ q.1) q.2)
      (Icc (0:ℝ) T ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ (j + 1) (μ q.1) q.2)
      (Icc (0:ℝ) T ×ˢ univ) := by
  have hΛ : 0 ≤ Λ :=
    (norm_nonneg _).trans (e14_bnd hμ (r := 0) ⟨le_rfl, hT⟩ (j := 0) (by omega) 0)
  have hcd : ∀ r ∈ Icc (0:ℝ) T, ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (μ r) :=
    fun r hr => (hμ.regular.1 r hr).1.1
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) ℝ with he
  have hkey : ∀ r (z : Euc d), fderiv ℝ (iteratedFDeriv ℝ j (μ r)) z =
      e (iteratedFDeriv ℝ (j + 1) (μ r) z) := by
    intro r z
    rw [iteratedFDeriv_succ_eq_comp_left]
    simp [he]
  have hcont : ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (iteratedFDeriv ℝ j (μ q.1)) q.2)
      (Icc (0:ℝ) T ×ˢ univ) := by
    refine e14_deriv_continuousOn hΛ (S := Icc (0:ℝ) T)
      (g := fun r => iteratedFDeriv ℝ j (μ r)) (fun r hr => ?_) (fun r hr x y => ?_) hprev
    · exact (hcd r hr).differentiable_iteratedFDeriv (by exact_mod_cast (by omega : j < m + 3))
    · rw [hkey, hkey, ← e.map_sub, e.norm_map]
      have hd : Differentiable ℝ (iteratedFDeriv ℝ (j + 1) (μ r)) :=
        (hcd r hr).differentiable_iteratedFDeriv (by exact_mod_cast (by omega : j + 1 < m + 3))
      have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
        (f := iteratedFDeriv ℝ (j + 1) (μ r)) (C := Λ) (fun z _ => hd z)
        (fun z _ => by
          rw [norm_fderiv_iteratedFDeriv]
          exact e14_bnd hμ hr (by omega) z) (mem_univ y) (mem_univ x)
      exact this
  have hfin : ContinuousOn (fun q : ℝ × Euc d => e.symm (fderiv ℝ (iteratedFDeriv ℝ j (μ q.1)) q.2))
      (Icc (0:ℝ) T ×ˢ univ) := e.symm.continuous.comp_continuousOn hcont
  refine hfin.congr (fun q _ => ?_)
  rw [iteratedFDeriv_succ_eq_comp_left]
  rfl

theorem e14_cont {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hT : 0 ≤ T)
    (hμ : CoeffHypRd s m Λ T μ) : ∀ j ≤ m + 2,
    ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (μ q.1) q.2) (Icc (0:ℝ) T ×ˢ univ) := by
  have hΛ : 0 ≤ Λ :=
    (norm_nonneg _).trans (e14_bnd hμ (r := 0) ⟨le_rfl, hT⟩ (j := 0) (by omega) 0)
  have hcd : ∀ r ∈ Icc (0:ℝ) T, ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (μ r) :=
    fun r hr => (hμ.regular.1 r hr).1.1
  have hbase : ContinuousOn (fun q : ℝ × Euc d => μ q.1 q.2) (Icc (0:ℝ) T ×ˢ univ) := by
    refine e14_base (S := Icc (0:ℝ) T) (g := μ) hΛ (fun r hr => ?_)
      (fun r hr => (hμ.prob r hr).nonneg) (fun r hr => (hμ.prob r hr).integral_one)
      (fun r hr => (hcd r hr).continuous) (fun r hr x y => ?_) hμ.cont
    · exact Integrable.of_integral_ne_zero (by rw [(hμ.prob r hr).integral_one]; exact one_ne_zero)
    · have hd : Differentiable ℝ (μ r) := (hcd r hr).differentiable (by exact_mod_cast (by omega : m + 3 ≠ 0))
      have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
        (f := μ r) (C := Λ) (fun z _ => hd z)
        (fun z _ => by
          rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
          exact e14_bnd hμ hr (by omega) z) (mem_univ y) (mem_univ x)
      simpa [Real.norm_eq_abs] using this
  intro j
  induction j with
  | zero =>
    intro _
    have : (fun q : ℝ × Euc d => iteratedFDeriv ℝ 0 (μ q.1) q.2) =
        fun q => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (μ q.1 q.2) := by
      funext q; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp_continuousOn hbase
  | succ j ih =>
    intro hj
    exact e14_step hT hμ hj (ih (by omega))

end Coeff

set_option maxHeartbeats 1600000 in
theorem e14_slab_cont {d : ℕ} {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hT : 0 ≤ T)
    (hμ : CoeffHypRd s m Λ T μ) :
    Continuous (fun p : Icc (0:ℝ) T × Euc d => iteratedFDeriv ℝ (m + 2) (μ p.1.1) p.2) := by
  have h := e14_cont hT hμ (m + 2) le_rfl
  have hc : Continuous (fun p : Icc (0:ℝ) T × Euc d => (p.1.1, p.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmaps : ∀ p : Icc (0:ℝ) T × Euc d, (p.1.1, p.2) ∈ Icc (0:ℝ) T ×ˢ (univ : Set (Euc d)) :=
    fun p => ⟨p.1.2, trivial⟩
  exact ContinuousOn.comp_continuous (g := fun q : ℝ × Euc d => iteratedFDeriv ℝ (m + 2) (μ q.1) q.2)
    (f := fun p : Icc (0:ℝ) T × Euc d => (p.1.1, p.2)) h hc hmaps

set_option maxHeartbeats 800000 in
theorem e14_meas {d : ℕ} {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hT : 0 ≤ T)
    (hμ : CoeffHypRd s m Λ T μ) (v : Fin (m + 3) → Euc d) :
    Measurable (fun q : Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ (m + 3) (μ q.1) q.2 v) := by
  letI : MeasurableSpace (Euc d [×(m + 3)]→L[ℝ] ℝ) := borel _
  haveI : BorelSpace (Euc d [×(m + 3)]→L[ℝ] ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (Euc d [×(m + 2)]→L[ℝ] ℝ) := borel _
  haveI : BorelSpace (Euc d [×(m + 2)]→L[ℝ] ℝ) := ⟨rfl⟩
  have hf0 := e14_slab_cont hT hμ
  have hm := measurable_fderiv_with_param ℝ
    (f := fun r : Icc (0:ℝ) T => iteratedFDeriv ℝ (m + 2) (μ r.1)) hf0
  have h2 : Measurable (fun q : Icc (0 : ℝ) T × Euc d => iteratedFDeriv ℝ (m + 3) (μ q.1) q.2) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 3) => Euc d) ℝ).symm.continuous.measurable.comp hm
  exact (continuous_eval_const v).measurable.comp h2

/-- E14 (corrected contract): weak probability continuity plus one unused spatial derivative
gives joint continuity below the top order. At the top only measurability is claimed.
The skeleton's `Measurable` for the multilinear-map-valued top derivative has no `MeasurableSpace`
instance on `Euc d [×(m+3)]→L[ℝ] ℝ`; the minimal fix is measurability of every evaluation
`iteratedFDeriv ℝ (m+3) (μ q.1) q.2 v`. -/
theorem coefficient_time_regular (d m : ℕ) (hd : 1 ≤ d) (s Λ T : ℝ)
    (hT : 0 ≤ T) (μ : ℝ → Euc d → ℝ) (hμ : CoeffHypRd s m Λ T μ) :
    (∀ j ≤ m+2, ContinuousOn (fun q : ℝ × Euc d =>
      iteratedFDeriv ℝ j (μ q.1) q.2) (Icc (0 : ℝ) T ×ˢ univ)) ∧
    ∀ v : Fin (m + 3) → Euc d, Measurable (fun q : Icc (0 : ℝ) T × Euc d =>
      iteratedFDeriv ℝ (m+3) (μ q.1) q.2 v) :=
  ⟨e14_cont hT hμ, e14_meas hT hμ⟩

end HRS.Whole.AppendixA.Phase2SA16Evolution
