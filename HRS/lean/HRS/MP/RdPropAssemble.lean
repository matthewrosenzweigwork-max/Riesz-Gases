import HRS.MP.RdPropKernel

/-!
# S.A.22 on `ℝ^d`: assembly of `path_propagator_increment_rd`

`IncrementBoundRd` (`rpi_increment`) and `KernelBoundRd` (`rpk_kernel`) for the particle coefficients and, under
`LimitPathHyp`, for the limiting coefficient, with one constant independent of `S`, `L`, `N`.  The statement is
verbatim `HRS.Whole.AppendixALemmas.path_propagator_increment_rd`, tied by an `example`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdProp
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

lemma rpa_increment_mono {Cf : WholeCoeff d} {T : ℝ} {q m₀ : ℕ} {C C' : ℝ}
    (h : IncrementBoundRd Cf T q m₀ C) (hCC : C ≤ C') : IncrementBoundRd Cf T q m₀ C' := by
  intro r s' t hr hrs hst htT φ hφ l hl idx x
  refine (h r s' t hr hrs hst htT φ hφ l hl idx x).trans ?_
  have h1 : 0 ≤ |t - s'| * jbracket x * HRS.Whole.sobolevNorm (q : ℝ) φ :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (by unfold jbracket; positivity)) (Real.sqrt_nonneg _)
  nlinarith

lemma rpa_kernel_mono {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C C' : ℝ}
    (h : KernelBoundRd Cf T q C) (hCC : C ≤ C') : KernelBoundRd Cf T q C' := by
  refine ⟨h.1, fun Kern hK j r s' t hr hrs hst htT x => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 Kern hK j r s' t hr hrs hst htT x
  refine ⟨h1.trans ?_, h2.trans hCC⟩
  have : 0 ≤ |t - s'| * (1 + ‖x‖) := mul_nonneg (abs_nonneg _) (by positivity)
  nlinarith

/-- The statement of `path_propagator_increment_rd` without the (unused) hypothesis `1 ≤ m₀`. -/
theorem rpa_core (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → PDE.MatBound MB S.M → MeanFieldRegularityRd S (fd.Gamma + 5) Λ →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      (∀ N : ℕ, 1 ≤ N →
        IncrementBoundRd (S.coeff N) T (fd.Gamma + 2) m₀ C ∧
        KernelBoundRd (S.coeff N) T (fd.Gamma + 2) C) ∧
      ∀ L : LimitCoeffsRd d, LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ → L.invβ ≤ νbar →
        IncrementBoundRd (L.coeff S) T (fd.Gamma + 2) m₀ C ∧
        KernelBoundRd (L.coeff S) T (fd.Gamma + 2) C := by
  classical
  by_cases hex : ∃ S0 : WholeMainData d, S0.s = s ∧ fd.Holds S0 ν₀
  · obtain ⟨S0, hS0s, hS0⟩ := hex
    have hΓ : (mStar d : ℝ) + d / 2 + 4 < ((fd.Gamma : ℝ) + 2) := by
      have h := hS0 1 le_rfl
      rw [hS0s] at h
      exact rpi_hGamma fd h
    obtain ⟨Cgen, hCgen0, hgen⟩ :=
      rpi_increment (s := s) S0.hd (hS0s ▸ S0.hs0) (hS0s ▸ S0.hsd) fd.Gamma m₀ hm₀' hΓ MB Λ ΛV G₀ νbar
    set Cinc : ℝ := max Cw 0 * Real.exp (max Cw 0 * T) * Cgen with hCinc
    set Ck : ℝ := max (max Kadj Cinc) 0 with hCk
    refine ⟨max Cinc Ck, fun S hs hT hν hHold hMB hMF hV hP => ?_⟩
    have hd := S.hd
    -- the increment and kernel bounds for one coefficient, from the pieces
    have key : ∀ (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ), D.s = s → 0 ≤ D.invβ → D.invβ ≤ νbar →
        VHypRd (fd.Gamma + 5) ΛV G₀ D.V → HRS.PDE.MatBound MB D.M →
        IsRegularMFRd s (fd.Gamma + 2 + 3) Λ T ρ →
        AdjointInputOneD (((fd.Gamma + 2 : ℕ) : ℝ)) (m₀ + 1) (D.coeff ρ) T Kadj →
        (∃ U, IsWeightedExtension (D.coeff ρ) (m₀ + 1) (fd.Gamma + 2) T Cw U) →
        IncrementBoundRd (D.coeff ρ) T (fd.Gamma + 2) m₀ (max Cinc Ck) ∧
        KernelBoundRd (D.coeff ρ) T (fd.Gamma + 2) (max Cinc Ck) := by
      intro D ρ hDs hν0 hνD hVD hMD hreg hadj ⟨U, hU⟩
      have hinc := hgen D ρ T Kadj Cw U hDs hMD hVD hreg hν0 hνD hadj hU
      refine ⟨rpa_increment_mono hinc (le_max_left _ _), rpa_kernel_mono ?_ (le_max_right _ _)⟩
      exact rpk_kernel fd.Gamma m₀ (D.coeff ρ) T Kadj Cinc hadj hinc
    refine ⟨fun N hN => ?_, fun L hL hLν => ?_⟩
    · have hDs : (S.dyn N).s = s := hs
      have hreg : IsRegularMFRd s (fd.Gamma + 2 + 3) Λ T (S.ρ N) := by
        have h : IsRegularMFRd S.s (fd.Gamma + 5) Λ S.T (S.ρ N) := hMF.regular N hN
        rw [hs, hT] at h
        exact h
      exact key (S.dyn N) (S.ρ N) hDs (S.hinvβ N) (hν N) hV hMB
        hreg (hT ▸ hP.adjoint N hN) (hT ▸ hP.weighted N hN)
    · have hDs : (L.dyn S).s = s := hs
      have hLreg : IsRegularMFRd s (fd.Gamma + 2 + 3) Λ T L.ρ := by
        have h : IsRegularMFRd S.s (fd.Gamma + 2 + 3) Λ S.T L.ρ := hL.coeff.regular
        rw [hs, hT] at h
        exact h
      exact key (L.dyn S) L.ρ hDs L.hinvβ hLν hV hMB hLreg (hT ▸ hL.adjoint) (hT ▸ hL.weighted)
  · refine ⟨0, fun S hs hT hν hHold => ?_⟩
    exact absurd ⟨S, hs, hHold⟩ hex

theorem path_propagator_increment_rd_proof (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw : ℝ) (m₀ : ℕ) (_hm₀ : 1 ≤ m₀) (hm₀' : m₀ ≤ mStar d) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → PDE.MatBound MB S.M → MeanFieldRegularityRd S (fd.Gamma + 5) Λ →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      (∀ N : ℕ, 1 ≤ N →
        IncrementBoundRd (S.coeff N) T (fd.Gamma + 2) m₀ C ∧
        KernelBoundRd (S.coeff N) T (fd.Gamma + 2) C) ∧
      ∀ L : LimitCoeffsRd d, LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ → L.invβ ≤ νbar →
        IncrementBoundRd (L.coeff S) T (fd.Gamma + 2) m₀ C ∧
        KernelBoundRd (L.coeff S) T (fd.Gamma + 2) C :=
  rpa_core s fd ν₀ MB Λ ΛV G₀ νbar T Kadj Cw m₀ hm₀'

example := (@path_propagator_increment_rd_proof : type_of% @HRS.Whole.AppendixALemmas.path_propagator_increment_rd)

end HRS.MP.RdProp
