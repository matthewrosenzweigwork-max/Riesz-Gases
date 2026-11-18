import HRS.MS.SA16RHeat3
import HRS.MS.SA16RExt3

/-!
# S.A.16 (SA16R) Heat4: pointwise jet bounds of the heat convolution

For `φ ∈ C_c^∞` and `f = g_a ⋆ φ`: every `∂^r f` with `|r| ≤ k+1` is `κ ⋆ ∂^{r'} φ` with `κ ∈ {g_a, ∂_i g_a}`
(`sa16r_pd_heat_eq`), hence in `L^p` and `‖jet_{k+1} f(x)‖ ≤ (K ⋆ ‖jet_k φ‖)(x)`, `K = g_a + ∑_i |∂_i g_a|`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat4
variable {d : ℕ}

/-- the kernel `K = g_a + ∑ |∂_i g_a|` -/
def sa16r_K (d : ℕ) (a : ℝ) (z : Euc d) : ℝ := sa16r_g d a z + ∑ i : Fin d, |sa16r_dg d a i z|

lemma sa16r_K_int {a : ℝ} (ha : 0 < a) : Integrable (sa16r_K d a) :=
  (sa16r_g_int ha).add (integrable_finsetSum _ fun i _ => (sa16r_dg_int ha i).abs)

lemma sa16r_K_nonneg {a : ℝ} (ha : 0 < a) (z : Euc d) : 0 ≤ sa16r_K d a z :=
  add_nonneg (sa16r_g_pos ha z).le (Finset.sum_nonneg fun i _ => abs_nonneg _)

lemma sa16r_K_cont (a : ℝ) : Continuous (sa16r_K d a) :=
  (sa16r_g_contDiff (a := a)).continuous.add (continuous_finset_sum _ fun i _ => (sa16r_dg_cont a i).abs)

lemma sa16r_g_le_K {a : ℝ} (ha : 0 < a) (z : Euc d) : |sa16r_g d a z| ≤ sa16r_K d a z := by
  rw [abs_of_pos (sa16r_g_pos ha z)]
  unfold sa16r_K
  linarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (sa16r_dg d a i z))]

lemma sa16r_dg_le_K {a : ℝ} (ha : 0 < a) (i : Fin d) (z : Euc d) : |sa16r_dg d a i z| ≤ sa16r_K d a z := by
  unfold sa16r_K
  have h1 := Finset.single_le_sum (f := fun i => |sa16r_dg d a i z|) (fun i _ => abs_nonneg _)
    (Finset.mem_univ i)
  linarith [sa16r_g_pos ha z]

lemma sa16r_K_integral_le {a : ℝ} (ha : 0 < a) :
    ∫ z, sa16r_K d a z ≤ 1 + d * (a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2)) := by
  unfold sa16r_K
  rw [integral_add (sa16r_g_int ha) (integrable_finsetSum _ fun i _ => (sa16r_dg_int ha i).abs),
    sa16r_g_mass ha, integral_finsetSum _ fun i _ => (sa16r_dg_int ha i).abs]
  have : ∑ i : Fin d, ∫ z, |sa16r_dg d a i z| ≤ ∑ i : Fin d, a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) :=
    Finset.sum_le_sum fun i _ => sa16r_dg_L1 ha i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

/-- Young: convolution of an `L^1` kernel with a continuous `L^p` function is in `L^p` -/
lemma sa16r_cv_memLp {κ u : Euc d → ℝ} (hκm : Measurable κ) (hκ : Integrable κ) (hu : Continuous u)
    {p : ℝ} (hp : 1 ≤ p) (hup : MemLp u (ENNReal.ofReal p) volume) :
    MemLp (sa16r_cv κ u) (ENNReal.ofReal p) volume :=
  lt_of_le_of_lt (sa16r_young hκm hu hp) (ENNReal.mul_lt_top hκ.2 hup.eLpNorm_lt_top)

/-- the pointwise structure of the derivatives of a heat convolution -/
lemma sa16r_pd_heat_eq {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {k j : ℕ}
    (hj : j ≤ k + 1) (r : Fin j → Fin d) :
    (∃ u, IsCcInfty u ∧ (∃ j' ≤ k, ∃ r' : Fin j' → Fin d, u = partialDeriv r' φ) ∧
        partialDeriv r (sa16r_cv (sa16r_g d a) φ) = sa16r_cv (sa16r_g d a) u) ∨
    (∃ (i : Fin d) (u : Euc d → ℝ), IsCcInfty u ∧ (∃ r' : Fin k → Fin d, u = partialDeriv r' φ) ∧
        partialDeriv r (sa16r_cv (sa16r_g d a) φ) = sa16r_cv (sa16r_dg d a i) u) := by
  rcases Nat.lt_or_ge j (k + 1) with hlt | hge
  · left
    exact ⟨partialDeriv r φ, sa16s_cc_partialDeriv hφ r, ⟨j, by omega, r, rfl⟩, sa16r_cv_pd ha hφ j r⟩
  · right
    have hjk : j = k + 1 := le_antisymm hj hge
    subst hjk
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin k → Fin d), r = Fin.cons i idx' :=
      ⟨r 0, Fin.tail r, (Fin.cons_self_tail r).symm⟩
    refine ⟨i, partialDeriv idx' φ, sa16s_cc_partialDeriv hφ idx', ⟨idx', rfl⟩, ?_⟩
    funext x
    exact sa16r_cv_pd_gain ha hφ i idx' x

end Heat4

end HRS.Whole.AppendixA.Phase2SA16R
