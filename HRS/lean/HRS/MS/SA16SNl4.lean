import HRS.MS.SA16SNl3
import HRS.MS.SA12LimitL7

/-!
# S.A.16 (SA16S) Nl4: the canonical nonlocal operator `G` and the packet P6 under `AdjointRdData`

* `sa16so_G d m p s M μ`: the continuous linear operator on `WmpSpace d m p` with zeroth component
  `eucNonlocal s M μ φ` on the jet of `φ ∈ C_c^∞` (zero if there is none); unique by density.
* `sa16so_P6`: under `AdjointRdData` with the `sub` case hypotheses `s ≤ d-2`, `d < p (s+1)`: a constant `C` (depending only on
  `d, m, s, p, MB, Λ`) with `‖G^r‖ ≤ C` for all `r ∈ [0,T]` and
  `ℓ_ψ(G^r Y) = ∫ (zeroth component of Y) · nonlocalTestRd (D.coeff μ) r ψ` for all `Y ∈ W^{m,p}`, `ψ ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nl4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- `T` is an operator with zeroth component `eucNonlocal s M μ φ` on the jets of `φ ∈ C_c^∞` -/
def SA16SubOp (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ : Euc d → ℝ)
    (T : WmpSpace d m p →L[ℝ] WmpSpace d m p) : Prop :=
  ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d m p φ)) =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M μ φ.1

lemma SA16SubOp.unique {m : ℕ} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {μ : Euc d → ℝ}
    {T T' : WmpSpace d m p →L[ℝ] WmpSpace d m p} (h : SA16SubOp d m p s M μ T)
    (h' : SA16SubOp d m p s M μ T') : T = T' := by
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d m p _ _ ?_
  filter_upwards [h φ, h' φ] with x h1 h2
  rw [h1, h2]

open Classical in
/-- the nonlocal operator on `W^{m,p}` -/
def sa16so_G (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ : Euc d → ℝ) :
    WmpSpace d m p →L[ℝ] WmpSpace d m p :=
  if h : ∃ T, SA16SubOp d m p s M μ T then Classical.choose h else 0

lemma sa16so_G_eq {m : ℕ} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {μ : Euc d → ℝ}
    {T : WmpSpace d m p →L[ℝ] WmpSpace d m p} (hT : SA16SubOp d m p s M μ T) :
    sa16so_G d m p s M μ = T := by
  have h : ∃ T, SA16SubOp d m p s M μ T := ⟨T, hT⟩
  unfold sa16so_G
  rw [dif_pos h]
  exact (Classical.choose_spec h).unique hT

lemma sa16so_conj_facts : 1 ≤ ENNReal.conjExponent (ENNReal.ofReal p) ∧
    ENNReal.conjExponent (ENNReal.ofReal p) ≠ ⊤ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  refine ⟨?_, ?_⟩
  · exact ENNReal.HolderConjugate.one_le _ (ENNReal.ofReal p)
  · unfold ENNReal.conjExponent
    refine ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 ?_⟩
    have : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    rw [this, ← ENNReal.ofReal_sub _ (by norm_num)]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith

lemma sa16so_regDensity_of_MF {s : ℝ} {r : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (h : IsRegularMFRd s r Λ T ρ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : IsRegularDensityW r Λ (ρ t) := by
  obtain ⟨hr, -⟩ := h
  obtain ⟨hcb, hfin, hsum⟩ := hr t ht
  refine ⟨hcb.1, hcb, ?_⟩
  have hcb0 : 0 ≤ cbNorm r (ρ t) := by
    unfold cbNorm
    refine Finset.sum_nonneg fun j _ => ?_
    exact Real.iSup_nonneg fun _ => norm_nonneg _
  calc ENNReal.ofReal (cbNorm r (ρ t)) + weightedSupE r ((d : ℝ) + 3) (ρ t)
      = ENNReal.ofReal (cbNorm r (ρ t)) + ENNReal.ofReal (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal := by
        rw [ENNReal.ofReal_toReal hfin.ne]
    _ = ENNReal.ofReal (cbNorm r (ρ t) + (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal) :=
        (ENNReal.ofReal_add hcb0 ENNReal.toReal_nonneg).symm
    _ ≤ ENNReal.ofReal Λ := ENNReal.ofReal_le_ofReal hsum

/-- **Packet P6** (weak identity of the nonlocal operator on `W^{m,p}`) together with its uniform bound -/
theorem sa16so_P6 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → Euc d → ℝ), AdjointRdData s m MB Λ ΛV G₀ νbar D T μ →
      ∀ r ∈ Icc (0 : ℝ) T, ‖sa16so_G d m p D.s D.M (μ r)‖ ≤ C ∧
        ∀ {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (Y : WmpSpace d m p),
          sa16r_ell d m p hψ (sa16so_G d m p D.s D.M (μ r) Y) =
            ∫ x, wrep d m p Y x * nonlocalTestRd (D.coeff μ) r ψ x := by
  obtain ⟨C, hC, hex⟩ := sa16so_G_exists d m hd s p MB Λ hs0 hsub.1 hsub.2
  refine ⟨C, hC, fun D μ hD r hr => ?_⟩
  have hDs : D.s = s := hD.hs.1
  have hMB : ∀ i j, |D.M i j| ≤ MB := hD.hM
  have hreg : IsRegularDensityW (m + 3) Λ (μ r) := sa16so_regDensity_of_MF hD.hμ.regular hr
  obtain ⟨T0, hT0, hT0s⟩ := hex D.M hMB (μ r) hreg
  have hDM : sa16so_G d m p D.s D.M (μ r) = T0 := by
    rw [hDs]
    exact sa16so_G_eq hT0s
  refine ⟨hDM ▸ hT0, fun {ψ} hψ Y => ?_⟩
  have hμ1 : ContDiff ℝ 1 (μ r) := hreg.1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  -- decay of the test function
  obtain ⟨K, -, hK⟩ := HRS.MH.AdjointRd.Phase2SA12Limit.test_nonlocal_decay hd s hs0 hsd m hm MB Λ ΛV G₀ νbar
    T D μ hD ψ hψ
  obtain ⟨hKc, hKb⟩ := hK r hr
  obtain ⟨hq1, hq⟩ := sa16so_conj_facts (p := p)
  have hN : MemLp (nonlocalTestRd (D.coeff μ) r ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    sa16so_memLp_decay hKc (K := K) (r := (d : ℝ) + 3 + s + 1) (by linarith) hKb hq1 hq
  rw [hDM]
  have := sa16so_weak_G (p := p) m (D.coeff μ) r (by simpa [WholeDyn.coeff, hDs] using hs0)
    (by simpa [WholeDyn.coeff, hDs] using hsd) (by simpa [WholeDyn.coeff] using hμ1) hψ hN T0
    (by intro φ; simpa [WholeDyn.coeff, hDs] using hT0s φ) Y
  exact this

end Nl4

end HRS.Whole.AppendixA.Phase2SA16R
