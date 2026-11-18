import HRS.Equilibrium.Parametrix.PX4aAuxS

/-!
# Packet PX4a auxiliaries T: the nonlocal estimate for a general conormal kernel (`jop_engine`)

For `Ψ` in `ConormalL τ (b) (m'+2)` with `τ + 2 < d`, the kernel `offZero (Jop (Ψ(·, y)) (x))`
is in `ConormalL (τ + 2 + s - d) (b + 1) m'`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

lemma dirD_periodic_fst {f : Euc d × Euc d → ℝ} (n : Euc d)
    (hper : ∀ p : Euc d × Euc d, f (p + (n, (0 : Euc d))) = f p) (η : Euc d × Euc d) (p : Euc d × Euc d) :
    dirD η f (p + (n, (0 : Euc d))) = dirD η f p := by
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := p) (n, (0 : Euc d))
  have e : (fun q => f (q + (n, (0 : Euc d)))) = f := funext hper
  rw [e] at h
  unfold dirD
  rw [← h]

lemma dirD_periodic_snd {f : Euc d × Euc d → ℝ} (n : Euc d)
    (hper : ∀ p : Euc d × Euc d, f (p + ((0 : Euc d), n)) = f p) (η : Euc d × Euc d) (p : Euc d × Euc d) :
    dirD η f (p + ((0 : Euc d), n)) = dirD η f p := by
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := p) ((0 : Euc d), n)
  have e : (fun q => f (q + ((0 : Euc d), n))) = f := funext hper
  rw [e] at h
  unfold dirD
  rw [← h]

lemma SFsrc_periodic_fst (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    SFsrc ρ Ψ (Y + n, w) = SFsrc ρ Ψ (Y, w) := by
  unfold SFsrc Ssrc
  refine Finset.sum_congr rfl fun i _ => ?_
  have := dirD_periodic_fst (f := Fsrc (Psii ρ Ψ i)) n (fun p => by
    obtain ⟨p1, p2⟩ := p
    simpa using Fsrc_periodic (Psii ρ Ψ i) p1 p2 n hn) ((0 : Euc d), eVec d i) (Y, w)
  simpa using this

lemma SFsrc_periodic_snd (ρ : Torus d → ℝ) (Ψ : Torus d → Torus d → ℝ) (Y w n : Euc d) (hn : IsLat n) :
    SFsrc ρ Ψ (Y, w + n) = SFsrc ρ Ψ (Y, w) := by
  unfold SFsrc Ssrc
  refine Finset.sum_congr rfl fun i _ => ?_
  have := dirD_periodic_snd (f := Fsrc (Psii ρ Ψ i)) n (fun p => by
    obtain ⟨p1, p2⟩ := p
    simpa using Fsrc_periodic_w (Psii ρ Ψ i) p1 p2 n hn) ((0 : Euc d), eVec d i) (Y, w)
  simpa using this

lemma kPot_Lam_periodic_snd (s : ℝ) {g : Euc d × Euc d → ℝ} (Y z n : Euc d) (hn : IsLat n) :
    kPot d (Lam d s) g (Y, z + n) = kPot d (Lam d s) g (Y, z) := by
  unfold kPot
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  show Lam d s (z + n - w) * g (Y, w) = Lam d s (z - w) * g (Y, w)
  have : z + n - w = (z - w) + n := by abel
  rw [this, Lam_periodic _ n hn]

lemma farConv_periodic_fst (s : ℝ) {S : Euc d × Euc d → ℝ} (Y z n : Euc d)
    (h : ∀ w, S (Y + n, w) = S (Y, w)) : farConv d s S (Y + n, z) = farConv d s S (Y, z) := by
  unfold farConv
  refine setIntegral_congr_fun LocalDivAux.measurableSet_cube fun w _ => ?_
  simp only [h]

lemma farConv_periodic_snd (s : ℝ) {S : Euc d × Euc d → ℝ} (Y z n : Euc d)
    (h : ∀ w, S (Y, w + n) = S (Y, w)) : farConv d s S (Y, z + n) = farConv d s S (Y, z) := by
  unfold farConv
  refine setIntegral_congr_fun LocalDivAux.measurableSet_cube fun w _ => ?_
  show ghat d s w * S (Y, z + n - w) = ghat d s w * S (Y, z - w)
  have : z + n - w = (z - w) + n := by abel
  rw [this, h]

end HRS.Parx

end
