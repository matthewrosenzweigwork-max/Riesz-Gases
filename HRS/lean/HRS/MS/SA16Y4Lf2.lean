import HRS.MS.SA16Y4Lf1
import HRS.MS.SA16Y3L3

/-!
# S.A.16 (SA16Y4) Lf2: smooth `W^{m+2,p}` initial data for the approximations, with level-`m` bounds

`sa16y4_data_lifts`: there is `C ≥ 0` (depending on `d, m, p`) such that for every `φ` with `wNormE m p φ < ∞` there are
`Φ_n ∈ W^{m+2,p}` with `‖ι² Φ_n‖ ≤ C ((wNormE m p φ).toReal + 1)` and `ℓ_ψ(Φ_n) → ∫ φ ψ` for every `ψ ∈ C_c^∞`.
(`Φ_n = S_n G` for a near-optimal lift `G` of `φ`; `ι² Φ_n = T_n G` is the cut-off mollification of SA16S (iii).)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer Phase2SA16Q

section Lf2
variable {d : ℕ}

lemma sa16y4_lift_norm {p : ℝ} [Fact (2 ≤ p)] (m : ℕ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : wNormE m p u < ⊤) :
    ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] u ∧ ‖G‖ ≤ (wNormE m p u).toReal + 1 := by
  have hpos : (0 : ℝ) < (wNormE m p u).toReal + 1 := by positivity
  have hlt : wNormE m p u < ENNReal.ofReal ((wNormE m p u).toReal + 1) := by
    calc wNormE m p u = ENNReal.ofReal (wNormE m p u).toReal := (ENNReal.ofReal_toReal hu.ne).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
  have hlt' := hlt
  unfold wNormE at hlt'
  rw [iInf_lt_iff] at hlt'
  obtain ⟨G, hG⟩ := hlt'
  rw [iInf_lt_iff] at hG
  obtain ⟨h, hn⟩ := hG
  exact ⟨G, h, ((ENNReal.ofReal_lt_ofReal_iff hpos).1 hn).le⟩

lemma sa16y4_lift_lt {p : ℝ} [Fact (2 ≤ p)] (m : ℕ) {u : EuclideanSpace ℝ (Fin d) → ℝ} {ε : ℝ}
    (hε : wNormE m p u < ENNReal.ofReal ε) (hε0 : 0 < ε) :
    ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] u ∧ ‖G‖ ≤ ε := by
  have hlt' := hε
  unfold wNormE at hlt'
  rw [iInf_lt_iff] at hlt'
  obtain ⟨G, hG⟩ := hlt'
  rw [iInf_lt_iff] at hG
  obtain ⟨h, hn⟩ := hG
  exact ⟨G, h, ((ENNReal.ofReal_lt_ofReal_iff hε0).1 hn).le⟩

lemma sa16y4_lift_norm2 {p : ℝ} [Fact (2 ≤ p)] (m : ℕ) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : wNormE m p u < ⊤) :
    ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] u ∧ ‖G‖ ≤ 2 * (wNormE m p u).toReal := by
  by_cases hw : (wNormE m p u).toReal = 0
  · have hw0 : wNormE m p u = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 hw with h | h
      · exact h
      · exact absurd h hu.ne
    have hz : ∀ ε : ℝ, 0 < ε → eLpNorm u (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨G, hG, hGn⟩ := sa16y4_lift_lt m (u := u) (ε := ε) (by rw [hw0]; exact ENNReal.ofReal_pos.2 hε) hε
      have h1 := sa16y3_wrep_eLp G
      rw [eLpNorm_congr_ae hG] at h1
      exact h1.trans (ENNReal.ofReal_le_ofReal hGn)
    obtain ⟨G0, hG0, -⟩ := sa16y4_lift_lt m (u := u) (ε := 1) (by rw [hw0]; simp) one_pos
    have hmeas : AEStronglyMeasurable u volume := (sa16y3_wrep_aesm G0).congr hG0
    have hzero : eLpNorm u (ENNReal.ofReal p) volume = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
      have := hz ε (by exact_mod_cast hε)
      simpa using this
    have hu0 : u =ᵐ[volume] 0 := by
      have hp0 : ENNReal.ofReal p ≠ 0 := by
        have : (2 : ℝ) ≤ p := Fact.out
        simpa using (by linarith : 0 < p)
      exact (eLpNorm_eq_zero_iff hp0).1 hzero
    refine ⟨0, ?_, by simp⟩
    filter_upwards [hu0, sa16r_wrep_zero (d := d) (k := m) (p := p)] with x h1 h2
    rw [h2, h1]; rfl
  · have hwpos : 0 < (wNormE m p u).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hw)
    refine sa16y4_lift_lt m (ε := 2 * (wNormE m p u).toReal) ?_ (by linarith)
    calc wNormE m p u = ENNReal.ofReal (wNormE m p u).toReal := (ENNReal.ofReal_toReal hu.ne).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)

theorem sa16y4_data_lifts {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : EuclideanSpace ℝ (Fin d) → ℝ), wNormE m p φ < ⊤ →
      ∃ Φ : ℕ → WmpSpace d (m + 1 + 1) p,
        (∀ n, ‖sa16sz_iota2 d m p (Φ n)‖ ≤ C * (wNormE m p φ).toReal) ∧
        ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ),
          Tendsto (fun n => sa16r_ell d (m + 1 + 1) p hψ (Φ n)) atTop (𝓝 (∫ x, φ x * ψ x)) := by
  obtain ⟨C, hC0, hT⟩ := sa16y3_extend_cutmol (d := d) hp m
  choose T hTn hTJ using hT
  refine ⟨2 * C, by positivity, fun φ hφ => ?_⟩
  obtain ⟨G, hGφ, hGn⟩ := sa16y4_lift_norm2 m hφ
  have hS := fun n => sa16y4_extend_cutmol_gain (d := d) (p := p) hp m n
  choose S hSJ hSι using hS
  refine ⟨fun n => S n G, fun n => ?_, fun {ψ} hψ => ?_⟩
  · rw [hSι n (T n) (hTJ n) G]
    have := ((T n).le_opNorm G).trans (mul_le_mul (hTn n) hGn (norm_nonneg _) hC0)
    linarith
  · have hc : Tendsto (fun n => sa16r_ell d m p hψ (T n G)) atTop (𝓝 (sa16r_ell d m p hψ G)) := by
      have h := sa16y3_T_tendsto hp m hC0 T hTn hTJ G
      exact ((sa16r_ell d m p hψ).continuous.tendsto G).comp (tendsto_iff_norm_sub_tendsto_zero.2 h)
    have e1 : ∀ n, sa16r_ell d (m + 1 + 1) p hψ (S n G) = sa16r_ell d m p hψ (T n G) := fun n => by
      rw [← sa16y3_ell_iota2 hψ, hSι n (T n) (hTJ n) G]
    have e2 : sa16r_ell d m p hψ G = ∫ x, φ x * ψ x := by
      rw [sa16r_ell_apply]
      exact integral_congr_ae (by filter_upwards [hGφ] with x hx; rw [hx])
    simp_rw [e1]
    rwa [e2] at hc

end Lf2

end HRS.Whole.AppendixA.Phase2SA16R
