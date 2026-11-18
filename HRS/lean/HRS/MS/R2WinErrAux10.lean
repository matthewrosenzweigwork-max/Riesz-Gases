import HRS.MS.R2WinErrAux9
import HRS.MS.GoFeatTie

/-!
# S10.4 packet E1a: smoothness and bounds of a `𝒦`-valued feature built from `ℓ²`-summable coordinates

`s104_K_features`: let `gA, gB : α ↦ (x ↦ ℝ)` and `v : α ↦ u ↦ (x ↦ ℝ)` be `C^k` with derivative bounds `≤ cA α, cB α, cV α`
(summable) and `u`-measurable at each `x`.  Then
`Γ(x) = (ℓ²-vector of (gA α x), L²_t-class of (u ↦ ℓ²-vector of (v α u x)), ℓ²-vector of (gB α x))` is a `C^k` map `ℝ^d → 𝒦_T` with
`‖D^jΓ‖ ≤ Σ cA + d^k (Σ cV) |[0,T]|^{1/2} + Σ cB`.  This is the assembly of `s55f_features_of_meas` (`HRS.MS.Go`) with independent
base and end slots, as needed for the window feature `r2WindowFeature` (first slot `∂_aU(r,max{b,r})φ_α`, third slot `1_{b≤r}∂_aφ_α`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

/-- `b ↦ (a, 0, 0)` and `b ↦ (0, 0, b)` as continuous linear maps into `𝒦`. -/
def s104ΦA (m T : ℝ) : OscDual d m →L[ℝ] KSpace d m T :=
  (s55fE (d := d) m T).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.prod 0 0))

def s104ΦB (m T : ℝ) : OscDual d m →L[ℝ] KSpace d m T :=
  (s55fE (d := d) m T).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.prod 0 (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ _)))

lemma s104ΦA_apply (m T : ℝ) (a : OscDual d m) : s104ΦA (d := d) m T a = KSpace.mk a 0 0 := rfl

lemma s104ΦB_apply (m T : ℝ) (b : OscDual d m) : s104ΦB (d := d) m T b = KSpace.mk 0 0 b := rfl

lemma s104ΦA_norm (m T : ℝ) : ‖(s104ΦA (d := d) m T)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun a => ?_
  rw [s104ΦA_apply]
  have := s55f_norm_mk_le (d := d) (m := m) (T := T) a 0 0
  simp only [norm_zero, add_zero] at this
  linarith

lemma s104ΦB_norm (m T : ℝ) : ‖(s104ΦB (d := d) m T)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun a => ?_
  rw [s104ΦB_apply]
  have := s55f_norm_mk_le (d := d) (m := m) (T := T) 0 0 a
  simp only [norm_zero, zero_add] at this
  linarith

lemma s104_mk_eq {m T : ℝ} (a : OscDual d m) (a' : L2Path d m T) (b : OscDual d m) :
    (KSpace.mk a a' b : KSpace d m T) = s104ΦA m T a + s55fΦ₂ m T a' + s104ΦB m T b := by
  rw [s104ΦA_apply, s55fΦ₂_apply, s104ΦB_apply]
  simp only [← s55fE_symm_apply]
  rw [← map_add, ← map_add]
  simp

theorem s104_K_features (hd1 : 1 ≤ d) (k : ℕ) (m T : ℝ)
    (cA cV cB : MultiIndex d → ℝ) (hcA : Summable cA) (hcV : Summable cV) (hcB : Summable cB)
    (gA gB : MultiIndex d → Euc d → ℝ) (v : MultiIndex d → ℝ → Euc d → ℝ)
    (hgA : ∀ α, ContDiff ℝ k (gA α))
    (hbA : ∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (gA α) x‖ ≤ cA α)
    (hgB : ∀ α, ContDiff ℝ k (gB α))
    (hbB : ∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (gB α) x‖ ≤ cB α)
    (hv : ∀ α u, ContDiff ℝ k (v α u))
    (hbv : ∀ α u, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (v α u) x‖ ≤ cV α)
    (hmeas : ∀ x α, AEStronglyMeasurable (fun u => v α u x) (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ContDiff ℝ k (fun x : Euc d => (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)
      (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T)) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x : Euc d => (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2
        (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)
      (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T)) x‖ ≤
      ∑' α, cA α + (d : ℝ) ^ k * ((∑' α, cV α) * ((volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ).toReal ^ (1 / 2 : ℝ))
        + ∑' α, cB α := by
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hbaseA := s55f_ell_contDiff (E := Euc d) (m := m) (k := k) gA hgA cA hcA hbA
  have hbaseB := s55f_ell_contDiff (E := Euc d) (m := m) (k := k) gB hgB cB hcB hbB
  set Bs : ℝ := ∑' α, cV α with hBs
  set Fv : ℝ → Euc d → OscDual d m := fun u x => ellVec (d := d) m (fun α => v α u x) with hFv
  have hFsm : ∀ u, ContDiff ℝ k (Fv u) ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (Fv u) x‖ ≤ Bs := fun u =>
    s55f_ell_contDiff (E := Euc d) (m := m) (k := k) (fun α x => v α u x) (fun α => hv α u) cV hcV
      (fun α j hj x => hbv α u j hj x)
  have hv0 : ∀ x α u, |v α u x| ≤ cV α := by
    intro x α u
    have := hbv α u 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hmeasF : ∀ x, AEStronglyMeasurable (fun u => Fv u x) μ := fun x =>
    s55f_aesm_ellVec (m := m) (fun α u => v α u x) (hmeas x) (fun u =>
      Summable.of_norm_bounded hcV fun α => by simpa [Real.norm_eq_abs] using hv0 x α u)
  have hFb0 : ∀ u x, ‖Fv u x‖ ≤ Bs := fun u x => by
    have := (hFsm u).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hmem : ∀ x, MemLp (fun u => Fv u x) 2 μ := fun x =>
    s55f_memLp_of_bound μ (hmeasF x) (B := Bs) (fun u => hFb0 u x)
  have hBs0 : 0 ≤ Bs := tsum_nonneg fun α => (abs_nonneg _).trans (hv0 0 α 0)
  obtain ⟨hWc, hWb⟩ := s55f_L2_contDiff μ hd1 k Fv Bs (fun u => (hFsm u).1)
    (fun u j hj x => (hFsm u).2 j hj x) hmeasF hmem
  have hid : ∀ x, (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2 μ then
        h.toLp _ else 0) (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T) =
      s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x)) +
        s104ΦB m T (ellVec (d := d) m (fun α => gB α x)) := by
    intro x
    rw [← s104_mk_eq]
    congr 1
    exact dif_pos (hmem x)
  have hfun : (fun x : Euc d => (KSpace.mk (ellVec (d := d) m (fun α => gA α x))
      (open Classical in if h : MemLp (fun u : ℝ => ellVec (d := d) m (fun α => v α u x)) 2 μ then
        h.toLp _ else 0) (ellVec (d := d) m (fun α => gB α x)) : KSpace d m T)) = fun x =>
      s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x)) +
        s104ΦB m T (ellVec (d := d) m (fun α => gB α x)) := funext hid
  rw [hfun]
  have cdA := (s104ΦA m T).contDiff.comp hbaseA.1
  have cdW := (s55fΦ₂ m T).contDiff.comp hWc
  have cdB := (s104ΦB m T).contDiff.comp hbaseB.1
  refine ⟨(cdA.add cdW).add cdB, fun j hj x => ?_⟩
  have hjk : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hj
  have hadd1 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) (cdA.of_le hjk).contDiffAt
    (cdW.of_le hjk).contDiffAt (x := x)
  have hadd2 := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) ((cdA.add cdW).of_le hjk).contDiffAt
    (cdB.of_le hjk).contDiffAt (x := x)
  have e1 := (s104ΦA m T).norm_iteratedFDeriv_comp_left hbaseA.1.contDiffAt (x := x) (n := j) hjk
  have e2 := (s55fΦ₂ m T).norm_iteratedFDeriv_comp_left hWc.contDiffAt (x := x) (n := j) hjk
  have e3 := (s104ΦB m T).norm_iteratedFDeriv_comp_left hbaseB.1.contDiffAt (x := x) (n := j) hjk
  have hF1 : iteratedFDeriv ℝ j (fun x => s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x))) x =
      iteratedFDeriv ℝ j (s104ΦA m T ∘ fun x => ellVec (d := d) m (fun α => gA α x)) x +
        iteratedFDeriv ℝ j (s55fΦ₂ m T ∘ fun x => (hmem x).toLp (fun u => Fv u x)) x := hadd1
  have hF2 : iteratedFDeriv ℝ j (fun x => s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x)) +
        s104ΦB m T (ellVec (d := d) m (fun α => gB α x))) x =
      iteratedFDeriv ℝ j (fun x => s104ΦA m T (ellVec (d := d) m (fun α => gA α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun u => Fv u x))) x +
        iteratedFDeriv ℝ j (s104ΦB m T ∘ fun x => ellVec (d := d) m (fun α => gB α x)) x := hadd2
  rw [hF2, hF1]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  have hb1 := hbaseA.2 j hj x
  have hb2 := hWb j hj x
  have hb3 := hbaseB.2 j hj x
  have hn1 := s104ΦA_norm (d := d) m T
  have hn2 := s55fΦ₂_norm (d := d) m T
  have hn3 := s104ΦB_norm (d := d) m T
  have hdj : (d : ℝ) ^ j ≤ (d : ℝ) ^ k := pow_le_pow_right₀ hd1' hj
  have hX : 0 ≤ Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by positivity
  have h1 : ‖s104ΦA (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ ≤
      ∑' α, cA α := by
    calc _ ≤ 1 * ∑' α, cA α := mul_le_mul hn1 hb1 (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have h3 : ‖s104ΦB (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ ≤
      ∑' α, cB α := by
    calc _ ≤ 1 * ∑' α, cB α := mul_le_mul hn3 hb3 (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have h2 : ‖s55fΦ₂ (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun u => Fv u x)) x‖ ≤
      (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
    calc _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
          mul_le_mul hn2 hb2 (norm_nonneg _) (by norm_num)
      _ ≤ (d : ℝ) ^ k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hdj hX
  calc _ ≤ ‖s104ΦA (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gA α x)) x‖ +
        ‖s55fΦ₂ (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun u => Fv u x)) x‖ +
        ‖s104ΦB (d := d) m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => gB α x)) x‖ :=
        add_le_add (add_le_add e1 e2) e3
    _ ≤ _ := by linarith

end HRS.MS.R2WinErr
