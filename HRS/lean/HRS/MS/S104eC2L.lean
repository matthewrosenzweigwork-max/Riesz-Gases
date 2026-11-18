import HRS.MS.S104eC2K

/-!
# S104E route C, packet C2, part L: `c2_Q_jc` (jointly continuous jets of `(v,x) ↦ Q_{ρ_v} G_v (x)`)

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  This is the field `A_jc` of `VolHyp` (`C5Ajc` of S104eC5E) for `A v = s103bQ d s (ρ v)`:
if `G_v ∈ HolB j η B` (`v ∈ [0,t]`) has jointly continuous jets of order `≤ j+1` and `v ↦ ρ_v` is continuous into `U2Dec (j+3) L`
(with uniform bound `A_ρ`), then the jets of order `≤ j` of `(v,x) ↦ Q_{ρ_v} G_v (x)` are jointly continuous on `[0,t] × ℝ^d`.
Proof: `Q_ρ G = -∑_i F_i ∂_i G + ∑_i ultK κ_i (ρ ∂_i G)`; the first sum by `s104c2_JC_mul`, the second by `s104c2_ultK_jc` and `s104c2_JC_mul`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

lemma s104c2_diff_jets {k : ℕ} {L ε : ℝ} (hL0 : 0 ≤ L) {f g : Euc d → ℝ} (hf : ContDiff ℝ k f)
    (hg : ContDiff ℝ k g) (hdf : U2Dec k L ε (fun y => f y - g y)) {a : ℕ} (ha : a ≤ k) (y : Euc d) :
    ‖iteratedFDeriv ℝ a f y - iteratedFDeriv ℝ a g y‖ ≤ ε := by
  have hak : (a : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast ha
  have e : (fun y => f y - g y) = f - g := rfl
  have h := hdf.2 a ha y
  rw [e, iteratedFDeriv_sub_apply (hf.of_le hak).contDiffAt (hg.of_le hak).contDiffAt] at h
  refine h.trans ?_
  have hw := u2Wt_le_one (d := d) hL0 y
  have hε : 0 ≤ ε := by
    have := (norm_nonneg _).trans (hdf.2 0 (Nat.zero_le _) y)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L y)).1 this
  nlinarith

lemma s104c2_force_uc (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) (i : Fin d) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ {A ε : ℝ} {ρ1 ρ2 : Euc d → ℝ}, U2Dec (j + 1) L A ρ1 → U2Dec (j + 1) L A ρ2 →
      U2Dec (j + 1) L ε (fun y => ρ1 y - ρ2 y) → ∀ a ≤ j, ∀ y : Euc d,
        ‖iteratedFDeriv ℝ a (fun x => movForce d s ρ1 x i) y - iteratedFDeriv ℝ a (fun x => movForce d s ρ2 x i) y‖
          ≤ Cf * ε := by
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hηd : s + 1 - η < (d : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hη0
    linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hL' : (d : ℝ) < L := by linarith
  obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd j (L := L) (by linarith)
  refine ⟨Cf, hCf0, fun {A ε ρ1 ρ2} h1 h2 hΔ a ha y => ?_⟩
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (h1.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  have hε : 0 ≤ ε := by
    have := (norm_nonneg _).trans (hΔ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  have hF1 := hCf A ρ1 hA h1 i
  have hF2 := hCf A ρ2 hA h2 i
  have hFd := hCf ε (fun y => ρ1 y - ρ2 y) hε hΔ i
  have hint : ∀ ρ : Euc d → ℝ, U2Dec (j + 1) L A ρ → ∀ x, Integrable (ultInt s ρ x) volume := fun ρ hρ x =>
    s104c2_int_rho (by omega) hs0 hsd hη1 hηd hηp hL' (ult_U2Dec_mono hρ (by omega : 1 ≤ j + 1)) x
  have hfun : (fun x => movForce d s (fun y => ρ1 y - ρ2 y) x i) =
      fun x => movForce d s ρ1 x i - movForce d s ρ2 x i :=
    funext fun x => s104c2_conv_sub s x (hint ρ1 h1 x) (hint ρ2 h2 x) i
  have hak : (a : ℕ∞ω) ≤ (j : ℕ∞ω) := by exact_mod_cast ha
  have e1 : iteratedFDeriv ℝ a (fun x => movForce d s ρ1 x i) y - iteratedFDeriv ℝ a (fun x => movForce d s ρ2 x i) y =
      iteratedFDeriv ℝ a (fun x => movForce d s (fun y => ρ1 y - ρ2 y) x i) y := by
    rw [hfun]
    exact (iteratedFDeriv_sub_apply (f := fun x => movForce d s ρ1 x i) (g := fun x => movForce d s ρ2 x i)
      (hF1.1.of_le hak).contDiffAt (hF2.1.of_le hak).contDiffAt).symm
  rw [e1]
  refine (hFd.2 a ha y).trans ?_
  have hw : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
  have : 0 ≤ Cf * ε := mul_nonneg hCf0 hε
  nlinarith

theorem c2_Q_jc (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) {ρ : ℝ → Euc d → ℝ}
    {t Aρ : ℝ} (hA0 : 0 ≤ Aρ) (hρ : ∀ v ∈ Icc (0 : ℝ) t, U2Dec (j + 3) L Aρ (ρ v))
    (hρc : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) t, ∀ r₀ ∈ Icc (0 : ℝ) t, |r - r₀| < δ →
      U2Dec (j + 3) L e (fun y => ρ r y - ρ r₀ y))
    {B : ℝ} (hB0 : 0 ≤ B) {G : ℝ → Euc d → ℝ} (hG : ∀ v ∈ Icc (0 : ℝ) t, HolB j η B (G v))
    (hGc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (Icc 0 t ×ˢ univ)) :
    ∀ i ≤ j, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (s103bQ d s (ρ p.1) (G p.1)) p.2)
      (Icc 0 t ×ˢ univ) := by
  set S : Set ℝ := Icc 0 t with hS
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hηd : s + 1 - η < (d : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hη0
    linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd1 : 1 ≤ d := by omega
  have hL' : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hρ1 : ∀ v ∈ S, U2Dec (j + 1) L Aρ (ρ v) := fun v hv => ult_U2Dec_mono (hρ v hv) (by omega)
  have hρN : ∀ v ∈ S, ContDiff ℝ j (ρ v) := fun v hv =>
    (hρ v hv).1.of_le (by exact_mod_cast (by omega : j ≤ j + 3))
  have hG1 : ∀ v ∈ S, ContDiff ℝ (j + 1) (G v) := fun v hv => (hG v hv).bd.1
  have hMu : ∀ v ∈ S, ∀ a ≤ j, ∀ y, ‖iteratedFDeriv ℝ a (ρ v) y‖ ≤ Aρ := fun v hv a ha y => by
    refine ((hρ v hv).2 a (by omega) y).trans ?_
    have := u2Wt_le_one (d := d) hL0 y
    nlinarith
  have he : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hgb : ∀ i : Fin d, ∀ v ∈ S, ∀ a ≤ j, ∀ y, ‖iteratedFDeriv ℝ a
      (fun y => fderiv ℝ (G v) y (EuclideanSpace.single i (1 : ℝ))) y‖ ≤ B := fun i v hv a ha y => by
    have := ((hG v hv).bd.deriv (N := j) (EuclideanSpace.single i (1 : ℝ))).2 a ha y
    rwa [he i, mul_one] at this
  have hdir : ∀ i : Fin d, JC S j (fun v y => fderiv ℝ (G v) y (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => s104c2_dir_jc hG1 hGc _
  have huc : ∀ v0 ∈ S, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ S, |v - v0| < δ → ∀ a ≤ j, ∀ y,
      ‖iteratedFDeriv ℝ a (ρ v) y - iteratedFDeriv ℝ a (ρ v0) y‖ ≤ ε := fun v0 hv0 ε hε => by
    obtain ⟨δ, hδ, h⟩ := hρc ε hε
    exact ⟨δ, hδ, fun v hv hvv a ha y =>
      s104c2_diff_jets (k := j + 3) hL0 (hρ v hv).1 (hρ v0 hv0).1 (h v hv v0 hv0 hvv) (by omega) y⟩
  have T1 : ∀ i : Fin d, JC S j (fun v y => (-1 : ℝ) * (movForce d s (ρ v) y i *
      fderiv ℝ (G v) y (EuclideanSpace.single i (1 : ℝ)))) := by
    intro i
    obtain ⟨Cf, hCf0, hCf⟩ := s103n_force_sy hd hs0 hsd j (L := L) (by linarith)
    obtain ⟨Cu, hCu0, hCu⟩ := s104c2_force_uc hd hs0 hsd j hη0 hη1 hL i
    have hSy : ∀ v ∈ S, Sy j (Cf * Aρ) (fun y => movForce d s (ρ v) y i) := fun v hv =>
      hCf Aρ (ρ v) hA0 (hρ1 v hv) i
    refine (s104c2_JC_mul (u := fun v y => movForce d s (ρ v) y i)
      (w := fun v y => fderiv ℝ (G v) y (EuclideanSpace.single i (1 : ℝ))) (Mu := Cf * Aρ) (Mw := B)
      (fun v hv => (hSy v hv).1) (hdir i) (fun v hv a ha y => (hSy v hv).bd.2 a ha y)
      (fun v hv a ha y => hgb i v hv a ha y) ?_).const_mul (-1)
    intro v0 hv0 ε hε
    obtain ⟨δ, hδ, h⟩ := hρc (ε / (Cu + 1)) (by positivity)
    refine ⟨δ, hδ, fun v hv hvv a ha y => ?_⟩
    have := hCu (hρ1 v hv) (hρ1 v0 hv0) (ult_U2Dec_mono (h v hv v0 hv0 hvv) (by omega : j + 1 ≤ j + 3)) a ha y
    refine this.trans ?_
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have T2 : ∀ i : Fin d, JC S j (fun v y => movForce d s
      (fun z => ρ v z * fderiv ℝ (G v) z (EuclideanSpace.single i (1 : ℝ))) y i) := by
    intro i
    have hkjc : JC S j (fun v y => ρ v y * fderiv ℝ (G v) y (EuclideanSpace.single i (1 : ℝ))) :=
      s104c2_JC_mul hρN (hdir i) hMu (fun v hv a ha y => hgb i v hv a ha y) huc
    have hpack := fun v (hv : v ∈ S) =>
      s104c2_k_pack hd hs0 hsd j hη0 hη1 hL i (hρ1 v hv) (hG v hv) (EuclideanSpace.single i (1 : ℝ)) (he i)
    refine ⟨fun v hv => ?_, fun m hm => ?_⟩
    · obtain ⟨hf, -, hcd, -⟩ := hpack v hv
      show ContDiff ℝ j (fun y => movForce d s (fun z => ρ v z * fderiv ℝ (G v) z (EuclideanSpace.single i (1 : ℝ))) y i)
      rw [hf]; exact hcd
    · have hH0 : 0 ≤ 2 ^ j * Aρ * (B * 1 + 2 * (B * 1)) := by positivity
      have hA0' : 0 ≤ Aρ * (B * 1) * 2 ^ j := by positivity
      have hcont : ContinuousOn (fun p : ℝ × Euc d => ultK (u2_kap d s i)
          (iteratedFDeriv ℝ m (fun y => ρ p.1 y * fderiv ℝ (G p.1) y (EuclideanSpace.single i (1 : ℝ)))) p.2)
          (S ×ˢ univ) :=
        s104c2_ultK_jc (F := Euc d [×m]→L[ℝ] ℝ) hd1 (ult_ker_kap hs0 hsd i) hη1 hηd hH0 hL' hA0'
          (Gf := fun v => iteratedFDeriv ℝ m (fun y => ρ v y * fderiv ℝ (G v) y (EuclideanSpace.single i (1 : ℝ))))
          (fun v hv => (hpack v hv).2.2.2.2.1 m hm) (fun v hv => (hpack v hv).2.2.2.2.2 m hm)
          (hkjc.2 m hm)
      refine hcont.congr fun p hp => ?_
      obtain ⟨hf, hit, -⟩ := hpack p.1 hp.1
      show iteratedFDeriv ℝ m (fun y => movForce d s
        (fun z => ρ p.1 z * fderiv ℝ (G p.1) z (EuclideanSpace.single i (1 : ℝ))) y i) p.2 = _
      rw [hf, hit m hm]
  have hQ := (JC.sum Finset.univ (fun i (_ : i ∈ Finset.univ) => T1 i)).add
    (JC.sum Finset.univ (fun i (_ : i ∈ Finset.univ) => T2 i))
  intro i hi
  exact hQ.2 i hi

end HRS.MS.S104e.C

end
