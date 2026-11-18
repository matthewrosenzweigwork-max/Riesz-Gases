import HRS.MS.S104eC5C
import HRS.MS.S104eC2H

/-!
# S104E route C, packet C5 part D: the perturbation side of `VolHyp`

`c5_Atc`: time continuity of `v ↦ s103bQ d s (ρ v) (u v)` in the sup norm of the jets `≤ 2` from that of `u` in the jets `≤ 3` and `HolB 2 η`-boundedness
(Hölder interpolation `interp_hol` to an exponent `η' < η`, `c2_Q_bd` at `η'`, `c2_Q_lip`, `c5_rho_cont`).
Uses the C2 theorems `c2_Q_bd`, `c2_Q_lip`, `c2_Q_lin` (branch S104C2) at `j = 2`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.R2WinOrb HRS.MS.Ul

variable {d : ℕ}

/-- difference of two `HolB` functions -/
theorem holB_sub {j : ℕ} {η B B' : ℝ} {f g : Euc d → ℝ} (hf : HolB j η B f) (hg : HolB j η B' g) :
    HolB j η (B + B') (fun x => f x - g x) := by
  have hfc : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f := hf.1.1
  have hgc : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g := hg.1.1
  have hD : ∀ (i : ℕ) (x : Euc d), i ≤ j + 1 → iteratedFDeriv ℝ i (fun x => f x - g x) x =
      iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i g x := fun i x hi =>
    iteratedFDeriv_sub_apply ((hfc.of_le (by exact_mod_cast hi)).contDiffAt)
      ((hgc.of_le (by exact_mod_cast hi)).contDiffAt)
  refine ⟨⟨hfc.sub hgc, fun i hi x => ?_⟩, fun x z => ?_⟩
  · rw [hD i x hi]
    exact (norm_sub_le _ _).trans (add_le_add (hf.1.2 i hi x) (hg.1.2 i hi x))
  · rw [hD (j + 1) (x + z) le_rfl, hD (j + 1) x le_rfl]
    have h1 := hf.2 x z
    have h2 := hg.2 x z
    calc ‖iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) g (x + z) -
          (iteratedFDeriv ℝ (j + 1) f x - iteratedFDeriv ℝ (j + 1) g x)‖
        = ‖(iteratedFDeriv ℝ (j + 1) f (x + z) - iteratedFDeriv ℝ (j + 1) f x) -
          (iteratedFDeriv ℝ (j + 1) g (x + z) - iteratedFDeriv ℝ (j + 1) g x)‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by nlinarith)

theorem holB_nonneg {j : ℕ} {η B : ℝ} {f : Euc d → ℝ} (h : HolB j η B f) : 0 ≤ B :=
  (norm_nonneg _).trans (h.1.2 0 (Nat.zero_le _) 0)

theorem u2dec_lower {K K' : ℕ} {L A : ℝ} {f : Euc d → ℝ} (h : K' ≤ K) (hf : U2Dec K L A f) : U2Dec K' L A f :=
  ⟨hf.1.of_le (by exact_mod_cast h), fun m hm => hf.2 m (hm.trans h)⟩

theorem c5_Atc (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ρ : ℝ → Euc d → ℝ) {η η' L Aρ H : ℝ}
    (hη0 : max 0 (s - d + 1) < η') (hηη : η' < η) (hη1 : η < 1)
    (hL : (d : ℝ) + ((2 : ℕ) : ℝ) + s + 4 < L)
    (hρU : ∀ v ∈ Icc (0 : ℝ) H, U2Dec (2 + 3) L Aρ (ρ v)) (hA0 : 0 ≤ Aρ)
    (hρc : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) H, ∀ r' ∈ Icc (0 : ℝ) H, |r - r'| < δ →
      U2Dec (2 + 3) L e (fun y => ρ r y - ρ r' y))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) {B : ℝ} {u : ℝ → Euc d → ℝ}
    (hu : ∀ v ∈ Icc (0 : ℝ) t, HolB 2 η B (u v)) (hTC : s104c3_TC t (2 + 1) u) :
    s104c3_TC t 2 (fun v => s103bQ d s (ρ v) (u v)) := by
  have hη'p : 0 < η' := lt_of_le_of_lt (le_max_left _ _) hη0
  have hη0' : max 0 (s - d + 1) < η := hη0.trans hηη
  have hη' : η' < 1 := hηη.trans hη1
  have hdL : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ ((2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨C', hC'0, hC'⟩ := c2_Q_bd hd hs0 hsd 2 hη0 hη' hL
  obtain ⟨Cb, hCb0, hCb⟩ := c2_Q_bd hd hs0 hsd 2 hη0' hη1 hL
  obtain ⟨Cl, hCl0, hCl⟩ := c2_Q_lip hd hs0 hsd 2 hη0' hη1 hL
  have hB0 : 0 ≤ B := holB_nonneg (hu t ⟨ht.1, le_rfl⟩)
  have hmemH : ∀ v ∈ Icc (0 : ℝ) t, v ∈ Icc (0 : ℝ) H := fun v hv => ⟨hv.1, hv.2.trans ht.2⟩
  have hρ1 : ∀ v ∈ Icc (0 : ℝ) H, U2Dec 1 L Aρ (ρ v) := fun v hv => u2dec_lower (by norm_num) (hρU v hv)
  set θ : ℝ := η' / η with hθ
  have hη : 0 < η := hη'p.trans hηη
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hη]; exact hηη
  intro i hi ε hε
  set κ : ℝ := ε / (2 * (C' * (1 + Aρ) + 1)) with hκ
  have hκpos : 0 < κ := by positivity
  set gfun : ℝ → ℝ := fun e => max e ((2 * e) ^ (1 - θ) * (B + B) ^ θ) with hgfun
  have hg0 : gfun 0 = 0 := by
    simp only [hgfun, mul_zero]
    rw [Real.zero_rpow (by linarith : (1 - θ) ≠ 0)]
    simp
  have hgc : ContinuousAt gfun 0 := by
    refine continuousAt_id.max ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    exact (Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).comp
      (by fun_prop : ContinuousAt (fun e : ℝ => 2 * e) 0)
  obtain ⟨e₁, he₁, hge₁⟩ : ∃ e₁ : ℝ, 0 < e₁ ∧ gfun e₁ ≤ κ := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hgc κ hκpos
    refine ⟨δ / 2, by positivity, ?_⟩
    have := h (x := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rw [hg0, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  obtain ⟨δa, hδa, ha⟩ := hTC 0 (by norm_num) e₁ he₁
  obtain ⟨δb, hδb, hb⟩ := hTC 1 (by norm_num) e₁ he₁
  obtain ⟨δc, hδc, hc⟩ := hTC 2 (by norm_num) e₁ he₁
  obtain ⟨δd, hδd, hd'⟩ := hTC 3 (by norm_num) e₁ he₁
  set ε₂ : ℝ := ε / (2 * (Cl * B + 1)) with hε₂
  have hε₂pos : 0 < ε₂ := by positivity
  obtain ⟨δ₂, hδ₂, hρδ⟩ := hρc ε₂ hε₂pos
  refine ⟨min (min (min δa δb) (min δc δd)) δ₂, lt_min (lt_min (lt_min hδa hδb) (lt_min hδc hδd)) hδ₂,
    fun r hr r' hr' hdist x => ?_⟩
  have hd1 : |r - r'| < min (min δa δb) (min δc δd) := hdist.trans_le (min_le_left _ _)
  have hdA : |r - r'| < δa := hd1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hdB : |r - r'| < δb := hd1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hdC : |r - r'| < δc := hd1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdD : |r - r'| < δd := hd1.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hd2 : |r - r'| < δ₂ := hdist.trans_le (min_le_right _ _)
  set f := u r' with hf
  set g := u r with hg
  have hrH := hmemH r hr
  have hr'H := hmemH r' hr'
  have hdiff : HolB 2 η (B + B) (fun x => g x - f x) := holB_sub (hu r hr) (hu r' hr')
  have hjets : ∀ k ≤ 2 + 1, ∀ z, ‖iteratedFDeriv ℝ k (fun x => g x - f x) z‖ ≤ e₁ := by
    intro k hk z
    have hD : iteratedFDeriv ℝ k (fun x => g x - f x) z = iteratedFDeriv ℝ k g z - iteratedFDeriv ℝ k f z :=
      iteratedFDeriv_sub_apply (((hu r hr).1.1.of_le (by exact_mod_cast hk)).contDiffAt)
        (((hu r' hr').1.1.of_le (by exact_mod_cast hk)).contDiffAt)
    rw [hD]
    interval_cases k
    · exact ha r hr r' hr' hdA z
    · exact hb r hr r' hr' hdB z
    · exact hc r hr r' hr' hdC z
    · exact hd' r hr r' hr' hdD z
  have hint := interp_hol hη'p hηη (by positivity) he₁.le hdiff hjets
  have hX : Bd 2 (C' * (1 + Aρ) * κ) (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r) f x) := by
    have e : (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r) f x) =
        s103bQ d s (ρ r) (fun x => g x - f x) := by
      have := c2_Q_lin (by omega) hs0 hsd hη0' hη1 hdL (hρ1 r hrH) (hu r' hr') (hu r hr) (-1)
      rw [show (fun x => g x - f x) = fun x => -1 * f x + g x by funext x; ring, this]
      funext x; ring
    rw [e]
    refine (hC' Aρ (ρ r) hA0 (hρU r hrH) _ _ hint).mono_A ?_
    have hbase : 0 ≤ C' * (1 + Aρ) := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans (le_refl _) hge₁) hbase
  have hY : Bd 2 (Cl * ε₂ * B) (fun x => s103bQ d s (ρ r) f x - s103bQ d s (ρ r') f x) :=
    hCl ε₂ Aρ Aρ (ρ r) (ρ r') hε₂pos.le (hρ1 r hrH) (hρ1 r' hr'H) (hρδ r hrH r' hr'H hd2) B f (hu r' hr')
  have hFb := hCb Aρ (ρ r) hA0 (hρU r hrH) B g (hu r hr)
  have hGb := hCb Aρ (ρ r') hA0 (hρU r' hr'H) B f (hu r' hr')
  have hF2 : ContDiff ℝ 2 (s103bQ d s (ρ r) g) := by simpa using hFb.1
  have hG2 : ContDiff ℝ 2 (s103bQ d s (ρ r') f) := by simpa using hGb.1
  have hX2 : ContDiff ℝ 2 (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r) f x) := by simpa using hX.1
  have hY2 : ContDiff ℝ 2 (fun x => s103bQ d s (ρ r) f x - s103bQ d s (ρ r') f x) := by simpa using hY.1
  have hsum : (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r') f x) =
      fun x => (s103bQ d s (ρ r) g x - s103bQ d s (ρ r) f x) +
        (s103bQ d s (ρ r) f x - s103bQ d s (ρ r') f x) := by funext x; ring
  have h1 : iteratedFDeriv ℝ i (s103bQ d s (ρ r) g) x - iteratedFDeriv ℝ i (s103bQ d s (ρ r') f) x =
      iteratedFDeriv ℝ i (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r') f x) x :=
    (iteratedFDeriv_sub_apply ((hF2.of_le (by exact_mod_cast hi)).contDiffAt)
      ((hG2.of_le (by exact_mod_cast hi)).contDiffAt)).symm
  have h2 : iteratedFDeriv ℝ i (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r') f x) x =
      iteratedFDeriv ℝ i (fun x => s103bQ d s (ρ r) g x - s103bQ d s (ρ r) f x) x +
      iteratedFDeriv ℝ i (fun x => s103bQ d s (ρ r) f x - s103bQ d s (ρ r') f x) x := by
    rw [hsum]
    exact iteratedFDeriv_add_apply ((hX2.of_le (by exact_mod_cast hi)).contDiffAt)
      ((hY2.of_le (by exact_mod_cast hi)).contDiffAt)
  show ‖iteratedFDeriv ℝ i (s103bQ d s (ρ r) g) x - iteratedFDeriv ℝ i (s103bQ d s (ρ r') f) x‖ ≤ ε
  rw [h1, h2]
  refine (norm_add_le _ _).trans ?_
  have a1 := hX.2 i hi x
  have a2 := hY.2 i hi x
  have b1 : C' * (1 + Aρ) * κ ≤ ε / 2 := by
    have : C' * (1 + Aρ) * κ ≤ (C' * (1 + Aρ) + 1) * κ :=
      mul_le_mul_of_nonneg_right (by linarith) hκpos.le
    have e : (C' * (1 + Aρ) + 1) * κ = ε / 2 := by rw [hκ]; field_simp
    linarith
  have b2 : Cl * ε₂ * B ≤ ε / 2 := by
    have : Cl * ε₂ * B = (Cl * B) * ε₂ := by ring
    rw [this]
    have h3 : (Cl * B) * ε₂ ≤ (Cl * B + 1) * ε₂ := mul_le_mul_of_nonneg_right (by linarith) hε₂pos.le
    have e : (Cl * B + 1) * ε₂ = ε / 2 := by rw [hε₂]; field_simp
    linarith
  linarith

end HRS.MS.S104e.C
