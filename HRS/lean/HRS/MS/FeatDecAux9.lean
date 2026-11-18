import HRS.MS.FeatDecAux8
import HRS.MS.OrbFeatAux3

/-!
# S8.5 `feature_decay`, part 9 (S85 packet): the `𝒦`-valued assembly `Θ(b, o)`

`s85Th m T b o x = Φ₁(ellVec (b_α(x))_α) + Φ₂([t ↦ ellVec (o_α(t,x))_α])` (junk `0` if the time slice is not `L²`).
* `s85_Th_props`: abstract assembly (copy of `s52b_features_of_data` for abstract coordinate families): `L²` slices, `C^n`, bounds;
* `s85_Th_smul`: `Θ(w b, w o)(x) = w(x) • Θ(b, o)(x)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

open Classical in
def s85Th (m T : ℝ) (b : MultiIndex d → Euc d → ℝ) (o : MultiIndex d → ℝ → Euc d → ℝ)
    (x : Euc d) : KSpace d m T :=
  s55fΦ₁ m T (ellVec (d := d) m (fun α => b α x)) +
    s55fΦ₂ m T (if h : MemLp (fun t => ellVec (d := d) m (fun α => o α t x)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) then h.toLp _ else 0)

theorem s85_Th_props {n : ℕ} {m T : ℝ} (hd1 : 1 ≤ d) (b : MultiIndex d → Euc d → ℝ)
    (o : MultiIndex d → ℝ → Euc d → ℝ) (c : MultiIndex d → ℝ) (hc0 : ∀ α, 0 ≤ c α)
    (hcs : Summable c)
    (hb : ∀ α, ContDiff ℝ (n : WithTop ℕ∞) (b α) ∧ ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (b α) x‖ ≤ c α)
    (ho : ∀ α t, ContDiff ℝ (n : WithTop ℕ∞) (o α t) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (o α t) x‖ ≤ c α)
    (hm : ∀ x α, AEStronglyMeasurable (fun t => o α t x) (volume.restrict (Set.Icc (0 : ℝ) T))) :
    (∀ x, MemLp (fun t => ellVec (d := d) m (fun α => o α t x)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
    ContDiff ℝ (n : WithTop ℕ∞) (s85Th m T b o) ∧
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (s85Th m T b o) x‖ ≤
      2 * (∑' α, c α) + (d : ℝ) ^ n * ((∑' α, c α) *
        ((volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ).toReal ^ (1 / 2 : ℝ)) := by
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  set Bs : ℝ := ∑' α, c α with hBs
  have hBs0 : 0 ≤ Bs := tsum_nonneg hc0
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hbaseE := s55f_ell_contDiff (E := Euc d) (m := m) (k := n) b (fun α => (hb α).1) c hcs
    (fun α j hj x => (hb α).2 j hj x)
  set Fv : ℝ → Euc d → OscDual d m := fun t x => ellVec (d := d) m (fun α => o α t x) with hFv
  have hFsm : ∀ t, ContDiff ℝ (n : WithTop ℕ∞) (Fv t) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (Fv t) x‖ ≤ Bs := fun t =>
    s55f_ell_contDiff (E := Euc d) (m := m) (k := n) (fun α x => o α t x)
      (fun α => (ho α t).1) c hcs (fun α j hj x => (ho α t).2 j hj x)
  have hobd : ∀ x α t, |o α t x| ≤ c α := by
    intro x α t
    have := (ho α t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hmeasF : ∀ x, AEStronglyMeasurable (fun t => Fv t x) μ := fun x =>
    s55f_aesm_ellVec (m := m) (fun α t => o α t x) (hm x) (fun t =>
      Summable.of_norm_bounded hcs fun α => by simpa [Real.norm_eq_abs] using hobd x α t)
  have hFb0 : ∀ t x, ‖Fv t x‖ ≤ Bs := fun t x => by
    have := (hFsm t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hmem : ∀ x, MemLp (fun t => Fv t x) 2 μ := fun x =>
    s55f_memLp_of_bound μ (hmeasF x) (B := Bs) (fun t => hFb0 t x)
  obtain ⟨hWc, hWb⟩ := s55f_L2_contDiff μ hd1 n Fv Bs (fun t => (hFsm t).1)
    (fun t j hj x => (hFsm t).2 j hj x) hmeasF hmem
  have hfun : s85Th m T b o = fun x =>
      s55fΦ₁ m T (ellVec (d := d) m (fun α => b α x)) +
        s55fΦ₂ m T ((hmem x).toLp (fun t => Fv t x)) := by
    funext x
    unfold s85Th
    rw [dif_pos (hmem x)]
  refine ⟨hmem, ?_, ?_⟩
  · rw [hfun]
    exact ((s55fΦ₁ m T).contDiff.comp hbaseE.1).add ((s55fΦ₂ m T).contDiff.comp hWc)
  · intro j hj x
    rw [hfun]
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
            (fun α => b α x)) x‖ +
          ‖s55fΦ₂ m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => Fv t x)) x‖ :=
          add_le_add e1 e2
      _ ≤ 2 * Bs + (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          have h1 : ‖s55fΦ₁ m T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m
              (fun α => b α x)) x‖ ≤ 2 * Bs :=
            mul_le_mul hn1 hb1 (norm_nonneg _) (by norm_num)
          have h2 : ‖s55fΦ₂ m T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => Fv t x)) x‖ ≤
              (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
            calc _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
                  mul_le_mul hn2 hb2 (norm_nonneg _) (by norm_num)
              _ ≤ (d : ℝ) ^ n * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
                  rw [one_mul]; exact mul_le_mul_of_nonneg_right hdj hX
          linarith

theorem s85_ellVec_smul (m : ℝ) (a : ℝ) {c : MultiIndex d → ℝ} (hc : Memℓp c 2) :
    ellVec (d := d) m (fun α => a * c α) = a • ellVec (d := d) m c := by
  have hfun : (fun α => a * c α) = a • c := by funext α; simp
  have h1 : Memℓp (fun α => a * c α) 2 := by rw [hfun]; exact hc.const_smul a
  have e1 := s55f_ellVec_eq (m := m) h1
  have e2 := s55f_ellVec_eq (m := m) hc
  rw [e1, e2]
  refine lp.ext ?_
  funext α
  rfl

theorem s85_Th_smul {m T : ℝ} (b : MultiIndex d → Euc d → ℝ) (o : MultiIndex d → ℝ → Euc d → ℝ)
    (w : Euc d → ℝ) (x : Euc d) (hb : Memℓp (fun α => b α x) 2)
    (ho : ∀ t, Memℓp (fun α => o α t x) 2)
    (hmem : MemLp (fun t => ellVec (d := d) m (fun α => o α t x)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T))) :
    s85Th m T (fun α y => w y * b α y) (fun α t y => w y * o α t y) x = w x • s85Th m T b o x := by
  have e : (fun t => ellVec (d := d) m (fun α => w x * o α t x)) =
      fun t => w x • ellVec (d := d) m (fun α => o α t x) :=
    funext fun t => s85_ellVec_smul m (w x) (ho t)
  have hmem2 : MemLp (fun t => w x • ellVec (d := d) m (fun α => o α t x)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := hmem.const_smul (w x)
  have hmem' : MemLp (fun t => ellVec (d := d) m (fun α => w x * o α t x)) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    rw [e]; exact hmem2
  have key : hmem'.toLp (fun t => ellVec (d := d) m (fun α => w x * o α t x)) =
      w x • hmem.toLp (fun t => ellVec (d := d) m (fun α => o α t x)) := by
    rw [← MemLp.toLp_const_smul (w x) hmem]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq e)
  unfold s85Th
  simp only [dif_pos hmem', dif_pos hmem]
  rw [s85_ellVec_smul m (w x) hb, key, map_smul, map_smul, smul_add]

end HRS.MS.S85
