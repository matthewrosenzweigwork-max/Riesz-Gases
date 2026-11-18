import HRS.MS.S21H2_S14aD2
import HRS.MS.S21H2_S14aB
import HRS.MS.S21H2_S14aC

/-!
# S21H2, packet R26-T3.S14a (part D3): the eigenbasis of `K` on the centered classes

`V = (span {1})ᗮ ⊂ L²(μ)` (centered classes), `K_V : V → V` the restriction of the `KRep` operator.  It is symmetric, nonnegative and compact
(Hilbert-Schmidt bound `s21h2_hs_bound` for any Hilbert basis of `V`, then `s21h2_compact_of_hs`).  If `V` is infinite dimensional, `s21h2_eigen_basis` gives an
`ℕ`-indexed Hilbert basis of eigenvectors with nonnegative eigenvalues.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS.Whole.Q34 HRS.MS.S111X2

variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {g : HRS.Euc d → ℝ}
  {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ}

/-- The centered classes. -/
def s21h2_V (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (ℝ ∙ one2 μ)ᗮ

theorem s21h2_mem_V {U : Lp ℝ 2 μ} : U ∈ s21h2_V μ ↔ inner ℝ (one2 μ) U = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

instance : CompleteSpace (s21h2_V μ) :=
  (Submodule.isClosed_orthogonal (ℝ ∙ one2 μ)).completeSpace_coe

theorem s21h2_K_mem (hK : KRep g μ K Mg) (U : Lp ℝ 2 μ) : K U ∈ s21h2_V μ := by
  rw [s21h2_mem_V]
  have := inner_one2_Pc (ν := μ) (K U)
  rwa [hK.pc U] at this

/-- The restriction of `K` to the centered classes. -/
def s21h2_KV (hK : KRep g μ K Mg) : s21h2_V μ →L[ℝ] s21h2_V μ :=
  (K.comp (s21h2_V μ).subtypeL).codRestrict (s21h2_V μ) fun U => s21h2_K_mem hK U

theorem s21h2_KV_coe (hK : KRep g μ K Mg) (U : s21h2_V μ) :
    ((s21h2_KV hK U : s21h2_V μ) : Lp ℝ 2 μ) = K (U : Lp ℝ 2 μ) := rfl

theorem s21h2_eigen_exists (hK : KRep g μ K Mg)
    (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => g (z.1 - z.2)) 2 (μ.prod μ))
    (hinf : ¬ FiniteDimensional ℝ (s21h2_V μ)) :
    ∃ (b : HilbertBasis ℕ ℝ (s21h2_V μ)) (lam : ℕ → ℝ), (∀ k, 0 ≤ lam k) ∧
      ∀ k, K ((b k : s21h2_V μ) : Lp ℝ 2 μ) = lam k • ((b k : s21h2_V μ) : Lp ℝ 2 μ) := by
  have hsymm : ((s21h2_KV hK : s21h2_V μ →L[ℝ] s21h2_V μ) : s21h2_V μ →ₗ[ℝ] s21h2_V μ).IsSymmetric :=
    fun x y => hK.symm x y
  have hpos : ∀ x : s21h2_V μ, 0 ≤ ⟪x, s21h2_KV hK x⟫ := fun x => by
    have := hK.pos (x : Lp ℝ 2 μ)
    rw [real_inner_comm] at this
    exact this
  obtain ⟨w, bw, -⟩ := exists_hilbertBasis ℝ (s21h2_V μ)
  have hcomp : IsCompactOperator (s21h2_KV hK) := by
    refine s21h2_compact_of_hs bw _ ?_
    refine summable_of_sum_le (c := ∫ z : HRS.Euc d × HRS.Euc d,
      HRS.Whole.r2CenterKernel μ (fun a b => g (a - b)) z.1 z.2 ^ 2 ∂(μ.prod μ))
      (fun i => sq_nonneg _) fun s => ?_
    have hv : Orthonormal ℝ (fun i => ((bw i : s21h2_V μ) : Lp ℝ 2 μ)) :=
      bw.orthonormal.comp_linearIsometry (s21h2_V μ).subtypeₗᵢ
    have := s21h2_hs_bound hK hk (fun i => ((bw i : s21h2_V μ) : Lp ℝ 2 μ)) hv
      (fun i => s21h2_mem_V.1 (bw i).2) s
    exact this
  obtain ⟨b, lam, hlam, heig⟩ := s21h2_eigen_basis (s21h2_KV hK) hcomp hsymm hpos hinf
  refine ⟨b, lam, hlam, fun k => ?_⟩
  have h1 := congrArg (fun z : s21h2_V μ => (z : Lp ℝ 2 μ)) (heig k)
  have h2 := s21h2_KV_coe hK (b k)
  rw [← h2]
  exact h1

end HRS.MS.R26T3
