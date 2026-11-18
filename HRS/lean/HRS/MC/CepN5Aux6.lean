import HRS.MC.CepN5Aux3
import HRS.MC.CepN5Aux5

/-!
# Packet N5, helper 6: the stopping times and the stopped, localised Itô process

On the shifted time axis (`s = t - t₁`): `τe` = first exit of `H` from `(δ, ε)`, `rhat` = `(ρ - t₁)⁺`,
`τ1 = τe ∧ rhat ∧ dur`, `A₁ = A ∩ {t₁ ≤ ρ} ∩ {G t₁ > δ} ∈ 𝒢 0`, `τR = τ1` on `A₁` and `0` elsewhere,
the drift `b = 1_{s ≤ τR} clip(dq Z)`, the initial value `X0 = clamp(G t₁)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Defs

variable (G : ℝ → Ω → ℝ) (ρ : Ω → WithTop ℝ) (t₁ : ℝ≥0) (δ ε dur : ℝ) (A : Set Ω)

def n5_A1 : Set Ω := A ∩ {ω | ((t₁ : ℝ) : WithTop ℝ) ≤ ρ ω} ∩ {ω | δ < G t₁ ω}

def n5_tauE : Ω → WithTop ℝ := hittingAfter (n5_H G t₁) (Iic δ ∪ Ici ε) 0

def n5_rhat : Ω → WithTop ℝ := fun ω => WithTop.map (fun r : ℝ => max (r - t₁) 0) (ρ ω)

def n5_tau1 : Ω → WithTop ℝ := fun ω => min (min (n5_tauE G t₁ δ ε ω) (n5_rhat ρ t₁ ω)) (dur : WithTop ℝ)

open Classical in
def n5_tauR : Ω → ℝ := fun ω =>
  if ω ∈ n5_A1 G ρ t₁ δ A then (n5_tau1 G ρ t₁ δ ε dur ω).untopA else 0

def n5_tau2 : Ω → WithTop ℝ := fun ω => ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ)

def n5_X0 : Ω → ℝ := fun ω => max δ (min (ε / 2) (G t₁ ω))

end Defs

section Props

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {G : ℝ → Ω → ℝ} {ρ : Ω → WithTop ℝ} {t₁ : ℝ≥0}
  {δ ε dur : ℝ} {A : Set Ω}

theorem n5_tauE_nonneg (G : ℝ → Ω → ℝ) (t₁ : ℝ≥0) (δ ε : ℝ) (ω : Ω) :
    (0 : WithTop ℝ) ≤ n5_tauE G t₁ δ ε ω := le_hittingAfter ω

theorem n5_rhat_nonneg (ρ : Ω → WithTop ℝ) (t₁ : ℝ≥0) (ω : Ω) : (0 : WithTop ℝ) ≤ n5_rhat ρ t₁ ω := by
  unfold n5_rhat
  cases h : ρ ω with
  | top => simp
  | coe r => simpa using (le_max_right (r - t₁) 0)

theorem n5_tau1_nonneg (hdur : 0 ≤ dur) (ω : Ω) : (0 : WithTop ℝ) ≤ n5_tau1 G ρ t₁ δ ε dur ω :=
  le_min (le_min (n5_tauE_nonneg G t₁ δ ε ω) (n5_rhat_nonneg ρ t₁ ω)) (by exact_mod_cast hdur)

theorem n5_tau1_le (ω : Ω) : n5_tau1 G ρ t₁ δ ε dur ω ≤ (dur : WithTop ℝ) := min_le_right _ _

theorem n5_tau1_ne_top (ω : Ω) : n5_tau1 G ρ t₁ δ ε dur ω ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (n5_tau1_le ω)

theorem n5_tau1_eq (ω : Ω) :
    n5_tau1 G ρ t₁ δ ε dur ω = (((n5_tau1 G ρ t₁ δ ε dur ω).untopA : ℝ) : WithTop ℝ) := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (n5_tau1_ne_top (G := G) (ρ := ρ) (t₁ := t₁) (δ := δ)
    (ε := ε) (dur := dur) ω)
  rw [← ha]; simp

theorem n5_tauR_nonneg (hdur : 0 ≤ dur) (ω : Ω) : 0 ≤ n5_tauR G ρ t₁ δ ε dur A ω := by
  unfold n5_tauR
  split_ifs with h
  · have h1 := n5_tau1_nonneg (G := G) (ρ := ρ) (t₁ := t₁) (δ := δ) (ε := ε) hdur ω
    have h2 := n5_tau1_eq (G := G) (ρ := ρ) (t₁ := t₁) (δ := δ) (ε := ε) (dur := dur) ω
    rw [h2] at h1
    exact_mod_cast h1
  · exact le_rfl

theorem n5_tauR_le (hdur : 0 ≤ dur) (ω : Ω) : n5_tauR G ρ t₁ δ ε dur A ω ≤ dur := by
  unfold n5_tauR
  split_ifs with h
  · have h1 := n5_tau1_le (G := G) (ρ := ρ) (t₁ := t₁) (δ := δ) (ε := ε) (dur := dur) ω
    have h2 := n5_tau1_eq (G := G) (ρ := ρ) (t₁ := t₁) (δ := δ) (ε := ε) (dur := dur) ω
    rw [h2] at h1
    exact_mod_cast h1
  · exact hdur

theorem n5_tauR_of_mem {ω : Ω} (hω : ω ∈ n5_A1 G ρ t₁ δ A) :
    ((n5_tauR G ρ t₁ δ ε dur A ω : ℝ) : WithTop ℝ) = n5_tau1 G ρ t₁ δ ε dur ω := by
  unfold n5_tauR
  rw [if_pos hω]
  exact (n5_tau1_eq ω).symm

theorem n5_tauR_of_not_mem {ω : Ω} (hω : ω ∉ n5_A1 G ρ t₁ δ A) : n5_tauR G ρ t₁ δ ε dur A ω = 0 := by
  unfold n5_tauR
  rw [if_neg hω]

end Props

end HRS.MC.CepN5
