import HRS.MS.Fp81S21IntervalRS
import HRS.MC.S7PIG6A

/-! The finite-sum RS density formula on an arbitrary interval. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.MS.R2Interp

/-- A continuous finite-dimensional integrand against an integrable density
has the expected RS value on every positive interval. -/
theorem fp81s21_isRSOn_density {ι : Type} [Fintype ι] (q r : ℝ) (hqr : q < r)
    (g h : ι → ℝ → ℝ)
    (hg : ∀ i, ContinuousOn (g i) (Icc q r))
    (hh : ∀ i, IntegrableOn (h i) (Icc q r)) :
    fp81s21_IsRSOn q r (fun t u v => ∑ i, g i t * ∫ x in Ioc u v, h i x)
      (∫ x in Ioc q r, ∑ i, g i x * h i x) := by
  have hshift (f : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v) :
      (∫ x in Ioc u v, f (q + x)) = ∫ x in Ioc (q + u) (q + v), f x := by
    calc
      _ = ∫ x in u..v, f (q + x) := (intervalIntegral.integral_of_le huv).symm
      _ = ∫ x in (q + u)..(q + v), f x := by
        simpa [add_comm] using (intervalIntegral.integral_comp_add_left f q)
      _ = _ := intervalIntegral.integral_of_le (by linarith : q + u ≤ q + v)
  have hgc : ∀ i, ContinuousOn (fun x => g i (q + x)) (Icc 0 (r - q)) := by
    intro i
    apply (hg i).comp (continuousOn_const.add continuousOn_id)
    intro x hx
    change q ≤ q + x ∧ q + x ≤ r
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hhi : ∀ i, IntegrableOn (fun x => h i (q + x)) (Icc 0 (r - q)) := by
    intro i
    have hi : IntervalIntegrable (h i) volume q r := (intervalIntegrable_iff_integrableOn_Icc_of_le hqr.le).2 (hh i)
    have ht := hi.comp_add_left q
    have ht' : IntervalIntegrable (fun x => h i (q + x)) volume 0 (r - q) := by
      simpa using ht
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : 0 ≤ r - q)).1 ht'
  have hd := HRS.MC.Sec7.S7PIS2.S7PIS2_RS_density (ι := ι) (r - q) (by linarith)
    (fun (i : ι) (x : ℝ) => g i (q + x)) (fun (i : ι) (x : ℝ) => h i (q + x)) hgc hhi
  have he : (∫ x in Ioc (0 : ℝ) (r - q), ∑ i, g i (q + x) * h i (q + x)) =
      ∫ x in Ioc q r, ∑ i, g i x * h i x := by
    simpa using hshift (fun x => ∑ i, g i x * h i x) (show (0 : ℝ) ≤ r - q by linarith)
  rw [he] at hd
  apply (s102_isR2RS_iff _ _ _).2
  apply HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr hd
  intro t u v ht hu huv hv
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hshift (h i) huv]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_isRSOn_density
