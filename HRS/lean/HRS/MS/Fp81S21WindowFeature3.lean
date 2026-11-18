import HRS.MS.Fp81S21WindowFeature2
import HRS.MS.R2WinErrAux10

/-!
# HRS S2.1 packet 15c: regularity and a qualitative bound for the window feature

The FULL-history feature is `s101Gamma C m T v x : KSpace d m T`, whose three
coordinates are the same diagonal orbit value in slots `A₀` and `B`, and the
`L²([0,T]; OscDual)` class of `s101Fl C m T v s x` in slot `A'`.  In
`r2_covariance_measure_proof`, `s101_D_data` inserts this feature into
`s101Fm Γ Bil = Σ_k Bil (∂ₖΓ) (∂ₖΓ)`; `s101_Fm_Rk_eq_inner` identifies that
rank-one test with the covariance test.  `s56_reconCLM` (or
`reconstructPath`) reconstructs a path coordinate from the initial `A₀`
coordinate, the integral of `A'` up to the observation time, and the
increment `B(t)-B(0)`.

The observation-window feature keeps the `KSpace d m H` horizon fixed while
using physical orbit time `a+t` in its middle slot.  Its `A₀` and `B` slots
are different for noise times after the window start.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.Go HRS.MS.R2WinErr

variable {d : ℕ}

/-- The qualitative feature radius obtained from a common S101 coefficient
family.  Its dependence on the observation length is only through the
restricted-time measure. -/
def fp81s21_window_Bfull (d r : ℕ) (m H : ℝ) (c : MultiIndex d → ℝ) : ℝ :=
  2 * Real.sqrt (∑' α : MultiIndex d, c α ^ 2) +
    (d : ℝ) ^ (r + 1) *
      (Real.sqrt (∑' α : MultiIndex d, c α ^ 2) *
        ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ))

/-- Smoothness and a qualitative full derivative bound for the window feature.
The coefficient family `c` is fixed before `a` and `v`; the terminal
diagonal identity is made explicit because `S101Data` does not itself assert
it. -/
theorem fp81s21_window_feature_contDiff_full_of_data
    (hd : 1 ≤ d) {C : WholeCoeff d} {m H : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hH : 0 < H) :
    ∀ a : ℝ, 0 ≤ a → ∀ v : ℝ, v ∈ Icc (0 : ℝ) (a + H) →
      ∀ hD : S101Data C m (a + H) r c,
      (∀ α : MultiIndex d, ∀ x : Euc d,
        propagatorW C v v (oscTestFun m α) x = oscTestFun m α x) →
      ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞)
        (fp81s21_window_feature C m H a v) ∧
      ∀ j ≤ r + 1, ∀ x,
        ‖iteratedFDeriv ℝ j (fp81s21_window_feature C m H a v) x‖ ≤
          fp81s21_window_Bfull d r m H c := by
  intro a ha v hv hD hterminal
  let k : ℕ := r + 1
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  let Bs : ℝ := Real.sqrt (∑' α : MultiIndex d, c α ^ 2)
  let gA : MultiIndex d → Euc d → ℝ := fun α x =>
    if v ≤ a then propagatorW C v a (oscTestFun m α) x else oscTestFun m α x
  let gB : MultiIndex d → Euc d → ℝ := fun α x =>
    if a < v then oscTestFun m α x else 0
  let raw : ℝ → Euc d → OscDual d m :=
    fun t x => fp81s21_window_feature_Aprime C m H a v t x
  let Fv : ℝ → Euc d → OscDual d m := fun t x =>
    if t ∈ Icc (0 : ℝ) H then raw t x else 0
  have hA : ContDiff ℝ k (fun x => ellVec (d := d) m (fun α => gA α x)) ∧
      ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ ≤ Bs := by
    have hcoord := s101_ell2_contDiff (d := d) (m := m) k gA c hD.summable
      (fun α => by
        by_cases hva : v ≤ a
        · have haT : a ∈ Icc v (a + H) := by constructor <;> linarith
          simpa only [gA, if_pos hva, k] using hD.smoothU α v hv a haT
        · have hdiag := hD.smoothU α v hv v ⟨le_rfl, hv.2⟩
          have heq : (fun x => oscTestFun m α x) =
              propagatorW C v v (oscTestFun m α) := by
            funext x
            exact (hterminal α x).symm
          simp only [gA, if_neg hva]
          rw [heq]
          simpa only [k] using hdiag)
      (fun α j hj x => by
        by_cases hva : v ≤ a
        · have haT : a ∈ Icc v (a + H) := by constructor <;> linarith
          simpa only [gA, if_pos hva] using hD.bddU α v hv a haT j hj x
        · have hdiag := hD.bddU α v hv v ⟨le_rfl, hv.2⟩ j hj x
          have heq : (fun x => oscTestFun m α x) =
              propagatorW C v v (oscTestFun m α) := by
            funext y
            exact (hterminal α y).symm
          simp only [gA, if_neg hva]
          rw [heq]
          exact hdiag)
    simpa [k, Bs] using hcoord
  have hB : ContDiff ℝ k (fun x => ellVec (d := d) m (fun α => gB α x)) ∧
      ∀ j ≤ k, ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ ≤ Bs := by
    have hcoord := s101_ell2_contDiff (d := d) (m := m) k gB c hD.summable
      (fun α => by
        by_cases hav : a < v
        · have hdiag := hD.smoothU α v hv v ⟨le_rfl, hv.2⟩
          have heq : (fun x => oscTestFun m α x) =
              propagatorW C v v (oscTestFun m α) := by
            funext x
            exact (hterminal α x).symm
          simp only [gB, if_pos hav]
          rw [heq]
          simpa only [k] using hdiag
        · simp only [gB, if_neg hav]
          exact contDiff_const)
      (fun α j hj x => by
        by_cases hav : a < v
        · have hdiag := hD.bddU α v hv v ⟨le_rfl, hv.2⟩ j hj x
          have heq : (fun x => oscTestFun m α x) =
              propagatorW C v v (oscTestFun m α) := by
            funext y
            exact (hterminal α y).symm
          simp only [gB, if_pos hav]
          rw [heq]
          exact hdiag
        · simp only [gB, if_neg hav]
          rw [s55f_iter_zero]
          exact hD.nonneg α)
    simpa [k, Bs] using hcoord
  have hFsm : ∀ t, ContDiff ℝ k (Fv t) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (Fv t) x‖ ≤ Bs := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) H
    · have hsmooth : ∀ α, ContDiff ℝ k (fun x =>
          if v < a + t then s101Dt C m (a + H) v (a + t) α x else 0) := by
        intro α
        by_cases hvt : v < a + t
        · have htime : a + t ∈ Icc v (a + H) := by
            constructor
            · exact hvt.le
            · linarith [ht.2]
          have hvT : v ∈ Icc (0 : ℝ) (a + H) := hv
          have hsm := hD.smoothD α v hvT (a + t) htime
          simpa only [if_pos hvt, k] using hsm
        · simpa [hvt] using contDiff_const
      have hbound : ∀ α, ∀ j ≤ k, ∀ x,
          ‖iteratedFDeriv ℝ j
            (fun x => if v < a + t then s101Dt C m (a + H) v (a + t) α x else 0) x‖ ≤ c α := by
        intro α j hj x
        by_cases hvt : v < a + t
        · have htime : a + t ∈ Icc v (a + H) := by
            constructor
            · exact hvt.le
            · linarith [ht.2]
          have hvT : v ∈ Icc (0 : ℝ) (a + H) := hv
          simpa only [if_pos hvt] using hD.bddD α v hvT (a + t) htime j hj x
        · simp only [if_neg hvt]
          rw [s55f_iter_zero]
          exact hD.nonneg α
      have hEll := s101_ell2_contDiff (d := d) (m := m) k
        (fun α x => if v < a + t then s101Dt C m (a + H) v (a + t) α x else 0)
        c hD.summable hsmooth hbound
      have hFv : Fv t = fun x =>
          ellVec (d := d) m (fun α =>
            if v < a + t then s101Dt C m (a + H) v (a + t) α x else 0) := by
        funext x
        change (if t ∈ Icc (0 : ℝ) H then
          fp81s21_window_feature_Aprime C m H a v t x else 0) = _
        rw [if_pos ht]
        rfl
      rw [hFv]
      simpa [k, Bs] using hEll
    · have hzero : Fv t = fun _ : Euc d => (0 : OscDual d m) := by
        funext x
        change (if t ∈ Icc (0 : ℝ) H then raw t x else 0) = 0
        rw [if_neg ht]
      rw [hzero]
      refine ⟨contDiff_const, ?_⟩
      intro j hj x
      have hnorm : ‖iteratedFDeriv ℝ j
          (fun _ : Euc d => (0 : OscDual d m)) x‖ = 0 := by
        cases j with
        | zero => simp [norm_iteratedFDeriv_zero]
        | succ j => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)]; simp
      rw [hnorm]
      exact Real.sqrt_nonneg _
  have hrawMem : ∀ x,
      MemLp (fun t : ℝ => raw t x) 2 μ := by
    intro x
    dsimp [raw, μ]
    exact fp81s21_window_feature_Aprime_memLp hD ha hH.le hv hterminal
  have hFmeas : ∀ x, AEStronglyMeasurable (fun t => Fv t x) μ := by
    intro x
    have hEq : (fun t => raw t x) =ᵐ[μ] fun t => Fv t x := by
      filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := H))]
        with t ht
      simp only [Fv, if_pos ht]
    exact (hrawMem x).aestronglyMeasurable.congr hEq
  have hFmem : ∀ x, MemLp (fun t => Fv t x) 2 μ := by
    intro x
    have hEq : (fun t => raw t x) =ᵐ[μ] fun t => Fv t x := by
      filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := H))]
        with t ht
      simp only [Fv, if_pos ht]
    exact (memLp_congr_ae hEq).1 (hrawMem x)
  have hW := s55f_L2_contDiff (μ := μ) (d := d) (G := OscDual d m) hd k Fv Bs
    (fun t => (hFsm t).1) (fun t j hj x => (hFsm t).2 j hj x) hFmeas hFmem
  have hclipEq : ∀ x, (hrawMem x).toLp (fun t => raw t x) =
      (hFmem x).toLp (fun t => Fv t x) := by
    intro x
    apply Lp.ext
    have hEq : (fun t => raw t x) =ᵐ[μ] fun t => Fv t x := by
      filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := H))]
        with t ht
      simp only [Fv, if_pos ht]
    filter_upwards [(hrawMem x).coeFn_toLp, (hFmem x).coeFn_toLp, hEq] with t hr hf he
    rw [hr, hf, he]
  have hid : ∀ x,
      fp81s21_window_feature C m H a v x =
        s104ΦA m H (ellVec (d := d) m (fun α => gA α x)) +
          s55fΦ₂ m H ((hFmem x).toLp (fun t => Fv t x)) +
          s104ΦB m H (ellVec (d := d) m (fun α => gB α x)) := by
    intro x
    have hbase : fp81s21_window_feature C m H a v x =
        KSpace.mk (ellVec (d := d) m (fun α => gA α x))
          ((hrawMem x).toLp (fun t => raw t x))
          (ellVec (d := d) m (fun α => gB α x)) := by
      have hrawMem' : MemLp
          (fun t : ℝ => fp81s21_window_feature_Aprime C m H a v t x) 2
          (volume.restrict (Icc (0 : ℝ) H)) := by
        simpa [raw, μ] using hrawMem x
      unfold fp81s21_window_feature fp81s21_window_feature_A0
        fp81s21_window_feature_B gA gB raw
      rw [dif_pos hrawMem']
    rw [hbase, hclipEq x, s104_mk_eq]
  have hfun : (fun x => fp81s21_window_feature C m H a v x) = fun x =>
      s104ΦA m H (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m H ((hFmem x).toLp (fun t => Fv t x)) +
        s104ΦB m H (ellVec (d := d) m (fun α => gB α x)) := funext hid
  have hfun' : fp81s21_window_feature C m H a v =
      (fun x => s104ΦA m H (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m H ((hFmem x).toLp (fun t => Fv t x)) +
        s104ΦB m H (ellVec (d := d) m (fun α => gB α x))) := by
    exact hfun
  rw [hfun']
  have hcdA := (s104ΦA m H).contDiff.comp hA.1
  have hcdV := (s55fΦ₂ m H).contDiff.comp hW.1
  have hcdB := (s104ΦB m H).contDiff.comp hB.1
  refine ⟨(hcdA.add hcdV).add hcdB, ?_⟩
  intro j hj x
  have hjk : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hj
  have hadd₁ := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j)
    (hcdA.of_le hjk).contDiffAt (hcdV.of_le hjk).contDiffAt (x := x)
  have hadd₂ := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j)
    ((hcdA.add hcdV).of_le hjk).contDiffAt (hcdB.of_le hjk).contDiffAt (x := x)
  have eA := (s104ΦA m H).norm_iteratedFDeriv_comp_left hA.1.contDiffAt
    (x := x) (n := j) hjk
  have eV := (s55fΦ₂ m H).norm_iteratedFDeriv_comp_left hW.1.contDiffAt
    (x := x) (n := j) hjk
  have eB := (s104ΦB m H).norm_iteratedFDeriv_comp_left hB.1.contDiffAt
    (x := x) (n := j) hjk
  have hF1 : iteratedFDeriv ℝ j
      (fun x => s104ΦA m H (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m H ((hFmem x).toLp (fun t => Fv t x))) x =
      iteratedFDeriv ℝ j
        (s104ΦA m H ∘ fun x => ellVec (d := d) m (fun α => gA α x)) x +
      iteratedFDeriv ℝ j
        (s55fΦ₂ m H ∘ fun x => (hFmem x).toLp (fun t => Fv t x)) x := hadd₁
  have hF2 : iteratedFDeriv ℝ j
      (fun x => s104ΦA m H (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m H ((hFmem x).toLp (fun t => Fv t x)) +
        s104ΦB m H (ellVec (d := d) m (fun α => gB α x))) x =
      iteratedFDeriv ℝ j
        (fun x => s104ΦA m H (ellVec (d := d) m (fun α => gA α x)) +
          s55fΦ₂ m H ((hFmem x).toLp (fun t => Fv t x))) x +
      iteratedFDeriv ℝ j
        (s104ΦB m H ∘ fun x => ellVec (d := d) m (fun α => gB α x)) x := hadd₂
  rw [hF2, hF1]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  have hnA := s104ΦA_norm (d := d) m H
  have hnV := s55fΦ₂_norm (d := d) m H
  have hnB := s104ΦB_norm (d := d) m H
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdj : (d : ℝ) ^ j ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd1' hj
  have hX : 0 ≤ Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by positivity
  have hbA := hA.2 j hj x
  have hbV := hW.2 j hj x
  have hbB := hB.2 j hj x
  have h₁ : ‖s104ΦA (d := d) m H‖ *
      ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ ≤ Bs := by
    calc
      _ ≤ 1 * Bs := mul_le_mul hnA hbA (norm_nonneg _) (by norm_num)
      _ = Bs := one_mul _
  have h₂ : ‖s55fΦ₂ (d := d) m H‖ *
      ‖iteratedFDeriv ℝ j (fun x => (hFmem x).toLp (fun t => Fv t x)) x‖ ≤
        (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
    calc
      _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
        mul_le_mul hnV hbV (norm_nonneg _) (by norm_num)
      _ ≤ (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right hdj hX
  have h₃ : ‖s104ΦB (d := d) m H‖ *
      ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ ≤ Bs := by
    calc
      _ ≤ 1 * Bs := mul_le_mul hnB hbB (norm_nonneg _) (by norm_num)
      _ = Bs := one_mul _
  have hmass : (μ Set.univ).toReal ^ (1 / 2 : ℝ) =
      ((volume.restrict (Icc (0 : ℝ) H)) Set.univ).toReal ^ (1 / 2 : ℝ) := rfl
  calc
    _ ≤ ‖s104ΦA (d := d) m H‖ *
          ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ +
        ‖s55fΦ₂ (d := d) m H‖ *
          ‖iteratedFDeriv ℝ j (fun x => (hFmem x).toLp (fun t => Fv t x)) x‖ +
        ‖s104ΦB (d := d) m H‖ *
          ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ :=
      add_le_add (add_le_add eA eV) eB
    _ ≤ Bs + (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) + Bs :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = fp81s21_window_Bfull d r m H c := by
      dsimp [fp81s21_window_Bfull, Bs, μ, k]
      rw [hmass]
      ring

#print axioms fp81s21_window_feature_contDiff_full_of_data

end HRS.Fp81.S21

end
