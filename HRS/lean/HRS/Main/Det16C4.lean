import HRS.Main.Det16C3
import HRS.Main.A9Aux32
import HRS.Main.A9Aux21

/-!
# Example A.16, lemma L7: `det16c_sup_bound`

Summing the mode bounds of L6 (`ℓ² ≤ ℓ¹` for the coordinate norm and `Σ_k a9K < ∞`): a.s., for all
`t ∈ [0,T]`,
`‖σ_N Ξ_N^t − V_N^{t,0}(κ_N Ξ_N^0)‖_{H^{-γ}} ≤ σ_N · c · T · G`,
and the same bound after embedding into `H^{-γ'}`, `γ' ≥ γ` (e.g. `γ' = γ + 2`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.Det16

open HRS HRS.Main.A8P HRS.Main.A9

variable {d : ℕ}

/-- `Z₀ = Σ_{k ≠ 0} ⟨k⟩^{-(d+3)}`. -/
def det16c_Z0 (d : ℕ) : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 3))

theorem det16c_Z0_nonneg (d : ℕ) : 0 ≤ det16c_Z0 d :=
  tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _

theorem det16c_norm_embed_le {m m' : ℝ} (hmm' : m ≤ m') (v : NegSobolev d m) :
    ‖NegSobolev.embed m' v‖ ≤ ‖v‖ := by
  have h : ‖NegSobolev.embed m' v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [HRS.A34.a34_embed_norm_sq hmm', (NegSobolev.coord_sq v).2]
    obtain ⟨h1, -⟩ := NegSobolev.coord_sq v
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ h1
    · have := HRS.A34.a34_weight_le_one (d := d) (δ := m' - m) (by linarith) k
      nlinarith [sq_nonneg (NegSobolev.coord v k)]
    · refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h1
      have := HRS.A34.a34_weight_le_one (d := d) (δ := m' - m) (by linarith) k
      nlinarith [sq_nonneg (NegSobolev.coord v k)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

section Sup

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

theorem det16c_sup_bound
    (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈)
    (hβ : ∀ N, S.invβ N = 0) {N : ℕ} (hN : 2 ≤ N) {G : ℝ} (hG : 0 ≤ G)
    (hE : ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t ≤ G)
    (x : ℝ≥0 → Config d N)
    (hx : ∀ᵐ ω ∂(R N).P, ∀ u : ℝ≥0, (u : ℝ) ≤ S.T → (R N).X u ω = x u)
    (Y : Config d N) (hY : ∀ᵐ ω ∂(R N).P, (R N).X 0 ω = Y) :
    ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) -
        transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
          (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical Y) S.μ0)‖ ≤
      S.sigma N * (((1 / 2) * (Cq * cT)) * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d)) * (S.T * G) := by
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hP' : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT :=
    ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩
  have hσ := a8p_sigma_nonneg S N
  have hT0 := S.hT.le
  have hmodes := fun k : NonzeroLattice d => det16c_rem_modes hP' hS hβ hN hG hE x hx k
  filter_upwards [ae_all_iff.2 hmodes, hY] with ω hω hY0 t ht
  set c : ℝ := S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * G) with hc
  have hc0 : 0 ≤ c := by positivity
  have hb : ∀ k : NonzeroLattice d, |NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω) k| ≤
      c * a9K d Λ₁ t k := fun k => by
    refine (hω k t ht).trans (le_of_eq ?_)
    rw [hc]; ring
  have hsum : Summable fun k : NonzeroLattice d => c * a9K d Λ₁ t k :=
    (a9K_summable (d := d) Λ₁ t).mul_left c
  have hsum' : Summable fun k : NonzeroLattice d =>
      |NegSobolev.coord (a9Z S R N t ω - a9I S R N t ω) k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hsum
  have hnorm : ‖a9Z S R N t ω - a9I S R N t ω‖ ≤
      S.sigma N * (((1 / 2) * (Cq * cT)) * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d)) * (S.T * G) := by
    refine (a9_norm_le_tsum _ hsum').trans ?_
    refine (Summable.tsum_le_tsum hb hsum' hsum).trans ?_
    rw [tsum_mul_left]
    have h1 := a9K_tsum_le (d := d) Λ₁ ht
    have : c * ∑' k, a9K d Λ₁ t k ≤ c * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d) :=
      mul_le_mul_of_nonneg_left h1 hc0
    refine this.trans (le_of_eq ?_)
    rw [hc]; ring
  have e : a9I S R N t ω = transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
      (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical Y) S.μ0) := by
    unfold a9I a9F0
    rw [det16c_AN_eq hβ, one_smul, hY0]
  exact e ▸ hnorm

theorem det16c_sup_bound_embed
    (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈)
    (hβ : ∀ N, S.invβ N = 0) {N : ℕ} (hN : 2 ≤ N) {G : ℝ} (hG : 0 ≤ G)
    (hE : ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t ≤ G)
    (x : ℝ≥0 → Config d N)
    (hx : ∀ᵐ ω ∂(R N).P, ∀ u : ℝ≥0, (u : ℝ) ≤ S.T → (R N).X u ω = x u)
    (Y : Config d N) (hY : ∀ᵐ ω ∂(R N).P, (R N).X 0 ω = Y) {γ' : ℝ}
    (hγ' : (gammaIdx d : ℝ) ≤ γ') :
    ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖S.sigma N • NegSobolev.ofMeasureDiff γ'
          (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) -
        NegSobolev.embed γ' (transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
          (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical Y) S.μ0))‖ ≤
      S.sigma N * (((1 / 2) * (Cq * cT)) * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d)) * (S.T * G) := by
  have hN1 : 1 ≤ N := by omega
  filter_upwards [det16c_sup_bound hP hS hβ hN hG hE x hx Y hY] with ω hω t ht
  have hρ := (hS.mean_field.solution N hN1).density t ht
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ N t)) := HRS.isProb_withDensityReal hρ
  haveI : IsProbabilityMeasure (empirical ((R N).X (Real.toNNReal t) ω)) :=
    empirical_isProbabilityMeasure hN1 _
  have e : S.sigma N • NegSobolev.ofMeasureDiff γ' (empirical ((R N).X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t)) -
      NegSobolev.embed γ' (transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
          (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical Y) S.μ0)) =
      NegSobolev.embed γ' (S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) -
        transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
          (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical Y) S.μ0)) := by
    rw [HRS.A34.a34_embed_sub hγ', a9_embed_smul hγ', a9_embed_ofMeasureDiff a9_gamma_gt]
  rw [e]
  exact (det16c_norm_embed_le hγ' _).trans (hω t ht)

end Sup

end HRS.Main.Det16
