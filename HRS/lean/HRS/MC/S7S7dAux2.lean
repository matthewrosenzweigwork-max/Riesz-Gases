import Mathlib

/-!
# Packet `s7_S7d_uniform_limits`, helper 2: tails of (iterated) `tsum`s over a countable index set

Generic real-analysis lemmas used to split the sums over `NonzeroLattice d` into a finite block and a tail
controlled by the summable weights `b_k b_l` (resp. `b_k b_l b_j`).
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

variable {ι : Type*}

theorem s7d_tail_tendsto {b : ι → ℝ} (hb : Summable b) :
    Tendsto (fun S : Finset ι => (∑' i, b i) - ∑ i ∈ S, b i) atTop (𝓝 0) := by
  have h := hb.hasSum
  have := (tendsto_const_nhds (x := ∑' i, b i)).sub h
  simpa using this

theorem s7d_tsum1_tail {F b : ι → ℝ} (hb : Summable b) (hF : ∀ i, |F i| ≤ b i) (S : Finset ι) :
    |(∑' i, F i) - ∑ i ∈ S, F i| ≤ (∑' i, b i) - ∑ i ∈ S, b i := by
  have hFs : Summable F := Summable.of_norm_bounded hb (fun i => by simpa [Real.norm_eq_abs] using hF i)
  have h1 := hFs.sum_add_tsum_compl (s := S)
  have h2 := hb.sum_add_tsum_compl (s := S)
  have e1 : (∑' i, F i) - ∑ i ∈ S, F i = ∑' i : ((S : Set ι)ᶜ : Set ι), F i := by linarith
  have e2 : (∑' i, b i) - ∑ i ∈ S, b i = ∑' i : ((S : Set ι)ᶜ : Set ι), b i := by linarith
  rw [e1, e2]
  have hbs : Summable (fun i : ((S : Set ι)ᶜ : Set ι) => b i) := hb.subtype _
  have hFs' : Summable (fun i : ((S : Set ι)ᶜ : Set ι) => |F i|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => hF i) hbs
  calc |∑' i : ((S : Set ι)ᶜ : Set ι), F i| ≤ ∑' i : ((S : Set ι)ᶜ : Set ι), |F i| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun i : ((S : Set ι)ᶜ : Set ι) => F i) (by simpa [Real.norm_eq_abs] using hFs')
    _ ≤ ∑' i : ((S : Set ι)ᶜ : Set ι), b i := Summable.tsum_le_tsum (fun i => hF i) hFs' hbs

theorem s7d_tsum2_tail {F : ι → ι → ℝ} {b : ι → ℝ} {c : ℝ} (hb : Summable b) (hb0 : ∀ i, 0 ≤ b i)
    (hc : 0 ≤ c) (hF : ∀ k l, |F k l| ≤ c * (b k * b l)) (S : Finset ι) :
    |(∑' k, ∑' l, F k l) - ∑ k ∈ S, ∑ l ∈ S, F k l| ≤ c * ((∑' i, b i) ^ 2 - (∑ i ∈ S, b i) ^ 2) := by
  have hbb : Summable (fun p : ι × ι => b p.1 * b p.2) := Summable.mul_of_nonneg hb hb hb0 hb0
  have hF2 : Summable (fun p : ι × ι => F p.1 p.2) :=
    Summable.of_norm_bounded (hbb.mul_left c) (fun p => by simpa [Real.norm_eq_abs] using hF p.1 p.2)
  have e1 : (∑' k, ∑' l, F k l) = ∑' p : ι × ι, F p.1 p.2 := (hF2.tsum_prod).symm
  have e2 : ∑ k ∈ S, ∑ l ∈ S, F k l = ∑ p ∈ S ×ˢ S, F p.1 p.2 := by
    rw [Finset.sum_product]
  have h := s7d_tsum1_tail (F := fun p : ι × ι => F p.1 p.2) (b := fun p : ι × ι => c * (b p.1 * b p.2))
    (hbb.mul_left c) (fun p => hF p.1 p.2) (S ×ˢ S)
  rw [e1, e2]
  refine h.trans (le_of_eq ?_)
  have e3 : ∑' p : ι × ι, c * (b p.1 * b p.2) = c * (∑' i, b i) ^ 2 := by
    have hn : Summable (fun i => ‖b i‖) := by simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 _)] using hb
    rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hn hn]
    ring
  have e4 : ∑ p ∈ S ×ˢ S, c * (b p.1 * b p.2) = c * (∑ i ∈ S, b i) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_product, sq, Finset.sum_mul_sum]
  rw [e3, e4]; ring

end HRS.MC.Sec7.S7d

end
