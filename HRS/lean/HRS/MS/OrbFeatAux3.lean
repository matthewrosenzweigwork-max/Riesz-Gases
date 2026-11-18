import HRS.MS.OrbFeatAux2
import HRS.MS.MovOscAux4

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S52B

open HRS HRS.Whole HRS.MS.Go HRS.MP.RdGen HRS.MS.Ul

variable {d : ℕ}

/-- **Features from coordinate bounds** (generalisation of `s55f_features_of_meas` to an arbitrary coefficient `C`
and an arbitrary summable majorant `c`). -/
theorem s52b_features_of_data {n : ℕ} {m T : ℝ} (hd1 : 1 ≤ d) (C : WholeCoeff d) (c : MultiIndex d → ℝ)
    (hc0 : ∀ α, 0 ≤ c α) (hcs : Summable c)
    (hbase : ∀ (a : Fin d) (α : MultiIndex d),
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (oscTestFun m α) x) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤ c α)
    (horb : ∀ (a : Fin d) (α : MultiIndex d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T →
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) x) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => gradComp a (propagatorW C r t (generatorW C t (oscTestFun m α))) x) x‖ ≤ c α)
    (hmeas : ∀ (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ (α : MultiIndex d) (x : Euc d),
      AEStronglyMeasurable (fun t => gradComp a (propagatorW C r t
        (generatorW C t (oscTestFun m α))) x) (volume.restrict (Set.Ioc r T))) :
    ∃ Cf : ℝ, ∀ (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) T,
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradFeature C m T a r x) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => gradFeature C m T a r y) x‖ ≤ Cf := by
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set Bs : ℝ := ∑' α, c α with hBs
  have hBs0 : 0 ≤ Bs := tsum_nonneg hc0
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  refine ⟨2 * Bs + (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)), fun a r hr => ?_⟩
  set CC := C with hCC
  -- the base part
  have hbaseE := s55f_ell_contDiff (E := Euc d) (m := m) (k := n)
    (fun α x => gradComp a (oscTestFun m α) x) (fun α => (hbase a α).1) c hcs (fun α j hj x =>
      (hbase a α).2 j hj x)
  -- the orbit part
  set v' : MultiIndex d → ℝ → Euc d → ℝ := fun α t x =>
    if r < t ∧ t ≤ T then gradComp a (propagatorW CC r t (generatorW CC t (oscTestFun m α))) x else 0
    with hv'
  have hv'smooth : ∀ α t, ContDiff ℝ (n : WithTop ℕ∞) (v' α t) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (v' α t) x‖ ≤ c α := by
    intro α t
    by_cases ht : r < t ∧ t ≤ T
    · have e : v' α t = fun x => gradComp a
          (propagatorW CC r t (generatorW CC t (oscTestFun m α))) x := by
        funext x; simp [hv', ht]
      rw [e]
      obtain ⟨h1, h2⟩ := horb a α r t hr.1 ht.1.le ht.2
      exact ⟨h1, fun j hj x => h2 j hj x⟩
    · have e : v' α t = fun _ => (0 : ℝ) := by funext x; simp [hv', ht]
      rw [e]
      exact ⟨contDiff_const, fun j hj x => by rw [s55f_iter_zero]; exact hc0 α⟩
  set Fv : ℝ → Euc d → OscDual d m := fun t x => ellVec (d := d) m (fun α => v' α t x) with hFv
  have hFsm : ∀ t, ContDiff ℝ (n : WithTop ℕ∞) (Fv t) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (Fv t) x‖ ≤ Bs := fun t =>
    s55f_ell_contDiff (E := Euc d) (m := m) (k := n) (fun α x => v' α t x)
      (fun α => (hv'smooth α t).1) c hcs (fun α j hj x => (hv'smooth α t).2 j hj x)
  have hv'meas : ∀ x α, AEStronglyMeasurable (fun t => v' α t x) μ := by
    intro x α
    have e : (fun t => v' α t x) = (Set.Ioc r T).indicator (fun t => gradComp a
        (propagatorW CC r t (generatorW CC t (oscTestFun m α))) x) := by
      funext t
      by_cases ht : r < t ∧ t ≤ T
      · simp [hv', ht, Set.indicator_of_mem (show t ∈ Set.Ioc r T from ht)]
      · simp [hv', ht, Set.indicator_of_notMem (show t ∉ Set.Ioc r T from ht)]
    rw [e, aestronglyMeasurable_indicator_iff measurableSet_Ioc]
    have hsub : Set.Ioc r T ⊆ Set.Icc (0 : ℝ) T := fun t ht => ⟨hr.1.trans ht.1.le, ht.2⟩
    have : μ.restrict (Set.Ioc r T) = volume.restrict (Set.Ioc r T) := by
      rw [hμ, Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.2 hsub]
    rw [this]
    exact hmeas a r hr α x
  have hv'bd : ∀ x α t, |v' α t x| ≤ c α := by
    intro x α t
    have := (hv'smooth α t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hmeasF : ∀ x, AEStronglyMeasurable (fun t => Fv t x) μ := fun x =>
    s55f_aesm_ellVec (m := m) (fun α t => v' α t x) (hv'meas x) (fun t =>
      Summable.of_norm_bounded hcs fun α => by simpa [Real.norm_eq_abs] using hv'bd x α t)
  have hFb0 : ∀ t x, ‖Fv t x‖ ≤ Bs := fun t x => by
    have := (hFsm t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hmem : ∀ x, MemLp (fun t => Fv t x) 2 μ := fun x =>
    s55f_memLp_of_bound μ (hmeasF x) (B := Bs) (fun t => hFb0 t x)
  obtain ⟨hWc, hWb⟩ := s55f_L2_contDiff μ hd1 n Fv Bs (fun t => (hFsm t).1)
    (fun t j hj x => (hFsm t).2 j hj x) hmeasF hmem
  -- identification
  have hid : ∀ x, gradFeature CC m T a r x =
      s55fΦ₁ m T (ellVec (d := d) m (fun α => gradComp a (oscTestFun m α) x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun t => Fv t x)) := by
    intro x
    have hfF : (fun t => if r < t then ellVec (d := d) m (fun α => gradComp a
        (propagatorW CC r t (generatorW CC t (oscTestFun m α))) x) else 0) =ᵐ[μ]
        fun t => Fv t x := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
      by_cases hrt : r < t
      · have hc : r < t ∧ t ≤ T := ⟨hrt, ht.2⟩
        simp only [hrt, if_true, hFv, hv', hc, and_self]
      · simp only [hrt, if_false, hFv, hv', false_and, if_false]
        exact (s55f_ellVec_zero m).symm
    have hmf := (hmem x).ae_eq hfF.symm
    rw [← s55f_mk_eq]
    unfold gradFeature orbitFeature
    dsimp only
    congr 1
    exact (dif_pos hmf).trans (MemLp.toLp_congr hmf (hmem x) hfF)
  have hfun : (fun x => gradFeature CC m T a r x) = fun x =>
      s55fΦ₁ m T (ellVec (d := d) m (fun α => gradComp a (oscTestFun m α) x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun t => Fv t x)) := funext hid
  rw [hfun]
  refine ⟨((s55fΦ₁ m T).contDiff.comp hbaseE.1).add ((s55fΦ₂ m T).contDiff.comp hWc), ?_⟩
  intro j hj x
  have hjk : (j : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hj
  have hadd := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j)
    (((s55fΦ₁ m T).contDiff.comp hbaseE.1).of_le hjk).contDiffAt
    (((s55fΦ₂ m T).contDiff.comp hWc).of_le hjk).contDiffAt (x := x)
  have e1 := (s55fΦ₁ m T).norm_iteratedFDeriv_comp_left hbaseE.1.contDiffAt (x := x) (n := j) hjk
  have e2 := (s55fΦ₂ m T).norm_iteratedFDeriv_comp_left hWc.contDiffAt (x := x) (n := j) hjk
  show ‖iteratedFDeriv ℝ j ((s55fΦ₁ m T ∘ _) + (s55fΦ₂ m T ∘ _)) x‖ ≤ _
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have hb1 := hbaseE.2 j hj x
  have hb2 := hWb j hj x
  have hn1 := s55fΦ₁_norm (d := d) m T
  have hn2 := s55fΦ₂_norm (d := d) m T
  have hdj : (d : ℝ) ^ j ≤ (d : ℝ) ^ n := pow_le_pow_right₀ hd1' hj
  have hX : 0 ≤ Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by positivity
  calc _ ≤ ‖s55fΦ₁ m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m
          (fun α => gradComp a (oscTestFun m α) x)) x‖ +
        ‖s55fΦ₂ m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => Fv t x)) x‖ :=
        add_le_add e1 e2
    _ ≤ 2 * Bs + (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
        have h1 : ‖s55fΦ₁ m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m
            (fun α => gradComp a (oscTestFun m α) x)) x‖ ≤ 2 * Bs :=
          mul_le_mul hn1 hb1 (norm_nonneg _) (by norm_num)
        have h2 : ‖s55fΦ₂ m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => Fv t x)) x‖ ≤
            (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
          calc _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
                mul_le_mul hn2 hb2 (norm_nonneg _) (by norm_num)
            _ ≤ (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
                rw [one_mul]; exact mul_le_mul_of_nonneg_right hdj hX
        linarith


/-- the base coordinates `∂_a φ_α` -/
theorem s52b_base_data (n : ℕ) (m : ℝ) {J : ℕ} (hJ : s52bK d n ≤ J) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (a : Fin d) (α : MultiIndex d),
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a (oscTestFun m α) x) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun m α) x) x‖ ≤
        Cb * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := by
  have hj : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j ≤ n → ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ C * oscNorm ((s52bK d n : ℕ) : ℝ) f) := by
    intro j
    by_cases hjn : j ≤ n
    · have hlt : ((j + 1 : ℕ) : ℝ) + (d : ℝ) / 2 < (s52bK d n : ℕ) :=
        lt_of_le_of_lt (by have : ((j + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hjn
                           linarith) (s52bK_gt n)
      obtain ⟨C, hC0, hC⟩ := HRS.MS.MovOsc.mo_sobolev_emb (d := d) (j + 1) _ (by exact_mod_cast hlt)
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hjn⟩
  choose C hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (n + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun a α => ?_⟩
  obtain ⟨f, hf, hfN⟩ := s52b_phi (d := d) m α
  have hfs : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (oscTestFun m α) := by
    rw [← hf]; exact f.smooth _ |>.of_le (by exact_mod_cast le_top)
  obtain ⟨hc', hbd⟩ := s55f_gradComp (n := n) hfs a
  refine ⟨hc', fun j hj x => (hbd j hj x).trans ?_⟩
  have h1 := hC j hj f x
  have hosc : oscNorm ((s52bK d n : ℕ) : ℝ) f ≤ oscNorm (J : ℝ) f := ul6_osc_mono hJ f
  rw [hfN, hfN] at hosc
  have hpow : 0 ≤ oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := Real.rpow_nonneg (oscEv_pos α).le _
  have hjm : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hCj : C j ≤ ∑ j ∈ Finset.range (n + 1), C j :=
    Finset.single_le_sum (f := C) (fun _ _ => hC0 _) hjm
  rw [hfN] at h1
  rw [← hf]
  calc ‖iteratedFDeriv ℝ (j + 1) (⇑f) x‖ ≤ C j * oscEigenvalue d α ^ ((((s52bK d n : ℕ) : ℝ) - m) / 2) := h1
    _ ≤ C j * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := mul_le_mul_of_nonneg_left hosc (hC0 j)
    _ ≤ _ := mul_le_mul_of_nonneg_right hCj hpow

end HRS.MS.S52B
