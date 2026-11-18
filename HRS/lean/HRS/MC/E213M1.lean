import HRS.MC.E213J2
import HRS.MC.E213J4
import HRS.MC.S7PIDTMain

/-!
# Packet E213M1: family-quantified `s7_PID_nuc_trunc_proof` (Theorem 2.13, translation-uniform PI-D)

The constant `K = 162 C₁² K₁ + 36 C₁ K₁` is chosen before the shift `b ≥ 0`; the regimes are `E213F.shift R b hb`
at the fixed horizon `T`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213M

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDT

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
theorem e213m_trunc (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, ∀ hb : 0 ≤ b, ∀ (p q : ℝ → ℝ) (Bp Bq : ℝ), Measurable p → Measurable q → (∀ u, |p u| ≤ Bp) →
      (∀ u, |q u| ≤ Bq) → ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ (k l : NonzeroLattice d)
      (F : Finset (NonzeroLattice d)) (n : ℕ) (M : PathSpace d m T [×2]→L[ℝ] ℝ),
      |nuc (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m T c c' n
          (fun u i => truncF m F (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m c c' n p (modeVec m k) u i))
          (fun u i => truncF m F (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m c c' n q (modeVec m l) u i)) M| ≤
        ‖M‖ * (K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c)) ∧
      |(nuc (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m T c c' (n + 1)
          (fun u i => truncF m F (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m c c' (n + 1) p (modeVec m k) u i))
          (fun u i => truncF m F (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m c c' (n + 1) q (modeVec m l) u i)) -
        nuc (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m T c c' n
          (fun u i => truncF m F (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m c c' n p (modeVec m k) u i))
          (fun u i => truncF m F (kernelNodes (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m c c' n q (modeVec m l) u i))) M| ≤
        ‖M‖ * (K * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) *
          (2 : ℝ) ^ (-(n : ℝ) / 4)) := by
  obtain ⟨K₁, Cb, hK₁, hCb, hfam⟩ := HRS.MC.E213J.e213j_fam R m hm T hT
  obtain ⟨C₁, hC₁, hpoly⟩ := HRS.MC.E213J.e213j_poly R m hm T hT
  have hC₁0 : 0 ≤ C₁ := by linarith
  refine ⟨162 * C₁ ^ 2 * K₁ + 36 * C₁ * K₁, by positivity, fun b hb => ?_⟩
  have hpoly := hpoly b hb
  set Rb := HRS.MC.E213F.shift R b hb with hRb
  intro p q Bp Bq hp hq hpB hqB c c' hc hcc hc' k l F n M
  have hBp : 0 ≤ Bp := (abs_nonneg _).trans (hpB 0)
  have hBq : 0 ≤ Bq := (abs_nonneg _).trans (hqB 0)
  by_cases hceq : c = c'
  · subst hceq
    have h0 : ∀ μ w w', nuc Rb.D Rb.ρ m T c c μ w w' = 0 := by
      intro μ w w'
      unfold nuc
      rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
    simp [h0]
  have hlt : c < c' := lt_of_le_of_ne hcc hceq
  have hΔ0 : 0 < c' - c := sub_pos.2 hlt
  obtain ⟨r, emb, G, hemb, hG1, hG0, hGc, hembG⟩ := S7PIDT_vec' m F
  have hjk : 0 ≤ Lattice.jp k.1 := (Torus.jp_pos k.1).le
  have hjl : 0 ≤ Lattice.jp l.1 := (Torus.jp_pos l.1).le
  have hak : Lattice.jp k.1 ^ (-(2 * (m - 1))) = (Lattice.jp k.1 ^ (-(m - 1))) ^ 2 :=
    (HRS.MC.Sec7.S7PIDI.S7PIDI_rpow_sq _ hjk (m - 1)).symm
  have hal : Lattice.jp l.1 ^ (-(2 * (m - 1))) = (Lattice.jp l.1 ^ (-(m - 1))) ^ 2 :=
    (HRS.MC.Sec7.S7PIDI.S7PIDI_rpow_sq _ hjl (m - 1)).symm
  have hαk : 0 ≤ Lattice.jp k.1 ^ (-(m - 1)) := Real.rpow_nonneg hjk _
  have hαl : 0 ≤ Lattice.jp l.1 ^ (-(m - 1)) := Real.rpow_nonneg hjl _
  have hF := fun ν => hfam b hb G hG1 hG0 hGc p Bp hp hpB c c' hc hcc hc' k ν
  have hF' := fun ν => hfam b hb G hG1 hG0 hGc q Bq hq hqB c c' hc hcc hc' l ν
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = K₁ * Bp ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (c' - c) := ⟨_, rfl⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, κ' = K₁ * Bq ^ 2 * Lattice.jp l.1 ^ (-(2 * (m - 1))) * (c' - c) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = K₁ * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) * Lattice.jp l.1 ^ (-(m - 1)) *
    (c' - c) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hκ'0 : 0 ≤ κ' := by rw [hκ']; positivity
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hW2 : W ^ 2 = κ * κ' := by rw [hW, hκ, hκ', hak, hal]; ring
  -- the Gaussian system at level ν
  have hg : ∀ ν, ∀ i ≤ 2 ^ ν, MemLp (fun u => G (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i)) 2
      (volume.restrict (Set.Ioc c c')) := fun ν => (hF ν).1
  have hg' : ∀ ν, ∀ i ≤ 2 ^ ν, MemLp (fun u => G (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i)) 2
      (volume.restrict (Set.Ioc c c')) := fun ν => (hF' ν).1
  have hv : ∀ ν, ∀ i j, i ≤ j → j ≤ 2 ^ ν →
      ∫ u in Set.Ioc c c', ‖G (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u j) -
        G (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i)‖ ^ 2 ≤ κ * (((j : ℝ) - i) / 2 ^ ν) := by
    intro ν i j hij hj
    refine ((hF ν).2.1 i j hij hj).trans (le_of_eq ?_)
    rw [hκ, S7PIDT_grid_sub]; ring
  have hv' : ∀ ν, ∀ i j, i ≤ j → j ≤ 2 ^ ν →
      ∫ u in Set.Ioc c c', ‖G (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u j) -
        G (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i)‖ ^ 2 ≤ κ' * (((j : ℝ) - i) / 2 ^ ν) := by
    intro ν i j hij hj
    refine ((hF' ν).2.1 i j hij hj).trans (le_of_eq ?_)
    rw [hκ', S7PIDT_grid_sub]; ring
  have h0 : ∀ ν, ∀ i ≤ 2 ^ ν,
      ∫ u in Set.Ioc c c', ‖G (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i)‖ ^ 2 ≤ κ := by
    intro ν i hi
    exact ((hF ν).2.2.1 i hi).trans (le_of_eq hκ.symm)
  have h0' : ∀ ν, ∀ i ≤ 2 ^ ν,
      ∫ u in Set.Ioc c c', ‖G (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i)‖ ^ 2 ≤ κ' := by
    intro ν i hi
    exact ((hF' ν).2.2.1 i hi).trans (le_of_eq hκ'.symm)
  have hsys := fun ν => S7PIDT_sys (X := PathSpace d m T) ν (Set.Ioc c c')
    (fun i u => G (kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i))
    (fun i u => G (kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i)) κ κ' hκ0 hκ'0 (hg ν) (hg' ν)
    (hv ν) (hv' ν) (h0 ν) (h0' ν)
  -- the bound on the kernel nodes (for `nuc`)
  obtain ⟨bb, hbb⟩ : ∃ bb : ℝ, bb = max (Bp * (Cb * ‖modeVec m k‖)) (Bq * (Cb * ‖modeVec m l‖)) := ⟨_, rfl⟩
  have hbd : ∀ ν, ∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c',
      ‖kernelNodes Rb.D Rb.ρ m c c' ν p (modeVec m k) u i‖ ≤ bb := fun ν i hi u hu =>
    ((hF ν).2.2.2.2 i hi u hu).trans (hbb ▸ le_max_left _ _)
  have hbd' : ∀ ν, ∀ i ≤ 2 ^ ν, ∀ u ∈ Set.Ioc c c',
      ‖kernelNodes Rb.D Rb.ρ m c c' ν q (modeVec m l) u i‖ ≤ bb := fun ν i hi u hu =>
    ((hF' ν).2.2.2.2 i hi u hu).trans (hbb ▸ le_max_right _ _)
  have hnucg := fun (ν μ : ℕ) (τ : ℕ → ℕ) (hτ : ∀ j ≤ 2 ^ μ, τ j ≤ 2 ^ ν)
      (Φ : (Fin (2 ^ μ + 1) → NegSobolev d m) →L[ℝ] PathSpace d m T)
      (hΦ : ∀ v : ℕ → NegSobolev d m, polyPath Rb.D Rb.ρ m T c c' μ v = Φ (fun i => v i.1)) M' =>
    S7PIDT_nucg Rb m hm T hT c c' hc hlt hc' F emb G hembG hGc p q (modeVec m k) (modeVec m l) bb
      (fun ν i hi => (hF ν).2.2.2.1 i hi) (fun ν i hi => (hF' ν).2.2.2.1 i hi) hbd hbd' ν μ τ hτ Φ hΦ M'
  have hKW : (162 * C₁ ^ 2 * K₁ + 36 * C₁ * K₁) * Bp * Bq * Lattice.jp k.1 ^ (-(m - 1)) *
      Lattice.jp l.1 ^ (-(m - 1)) * (c' - c) = (162 * C₁ ^ 2 + 36 * C₁) * W := by
    rw [hW]; ring
  rw [hKW]
  have hMn : 0 ≤ ‖M‖ := norm_nonneg M
  refine ⟨?_, ?_⟩
  · -- the bound for the level `n`
    obtain ⟨Φ, hΦ⟩ := S7PIDT_Phi Rb m hm T hT c c' hc hlt hc' n
    obtain ⟨Ω, hΩ, P, hP, Y, Y', hid, ⟨S, S', hSm, hSm', hS0, hS0', hSb, hSb', hSi, hSi', hSI, hSI'⟩, -⟩ :=
      hsys n
    have hn := hnucg n n (fun i => i) (fun j hj => hj) Φ hΦ M
    let Ψ : (Fin (2 ^ n + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] PathSpace d m T :=
      Φ.comp (ContinuousLinearMap.pi fun j : Fin (2 ^ n + 1) => emb.comp (ContinuousLinearMap.proj j))
    have hid' := (hid Ψ Ψ M).2
    have hΨ : ∀ x, Ψ x = Φ (fun j => emb (x j)) := fun x => rfl
    simp only [hΨ] at hid'
    have key : nuc Rb.D Rb.ρ m T c c' n
        (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' n p (modeVec m k) u i))
        (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' n q (modeVec m l) u i)) M =
        ∫ ω, M ![polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y i ω)),
          polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y' i ω))] ∂P := by
      refine hn.trans (hid'.trans ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show _ = M ![polyPath Rb.D Rb.ρ m T c c' n _, polyPath Rb.D Rb.ρ m T c c' n _]
      rw [hΦ, hΦ]
    rw [key]
    have hbS : ∀ ω, ‖polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y i ω))‖ ≤ C₁ * S ω := fun ω =>
      (hpoly c c' hc hcc hc' n (fun i => emb (Y i ω))).2.1 (S ω) fun i hi =>
        (hemb _).trans (hSb ω i hi)
    have hbS' : ∀ ω, ‖polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y' i ω))‖ ≤ C₁ * S' ω := fun ω =>
      (hpoly c c' hc hcc hc' n (fun i => emb (Y' i ω))).2.1 (S' ω) fun i hi =>
        (hemb _).trans (hSb' ω i hi)
    have h1 := S7PIDT_B1 P M _ _ C₁ κ κ' W hC₁0 hW0 hW2 S S' hSm hSm' hS0 hS0' hbS hbS' hSi hSi' hSI hSI'
    refine h1.trans ?_
    have : 0 ≤ 36 * C₁ * W := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (show 0 ≤ 36 * C₁ * W from this) hMn,
      mul_nonneg hMn (mul_nonneg hC₁0 this)]
  · -- the increment: fine system at level `n + 1`
    obtain ⟨Φ1, hΦ1⟩ := S7PIDT_Phi Rb m hm T hT c c' hc hlt hc' (n + 1)
    obtain ⟨Φ0, hΦ0⟩ := S7PIDT_Phi Rb m hm T hT c c' hc hlt hc' n
    obtain ⟨Ω, hΩ, P, hP, Y, Y', hid, ⟨S, S', hSm, hSm', hS0, hS0', hSb, hSb', hSi, hSi', hSI, hSI'⟩,
      ⟨δ, δ', hδm, hδm', hδ0, hδ0', hδb, hδb', hδi, hδi', hδI, hδI'⟩⟩ := hsys (n + 1)
    -- the fine tensor
    have hn1 := hnucg (n + 1) (n + 1) (fun i => i) (fun j hj => hj) Φ1 hΦ1 M
    let Ψ1 : (Fin (2 ^ (n + 1) + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] PathSpace d m T :=
      Φ1.comp (ContinuousLinearMap.pi fun j : Fin (2 ^ (n + 1) + 1) => emb.comp (ContinuousLinearMap.proj j))
    obtain ⟨hI1, hE1⟩ := hid Ψ1 Ψ1 M
    have hΨ1 : ∀ x, Ψ1 x = Φ1 (fun j => emb (x j)) := fun x => rfl
    simp only [hΨ1] at hI1 hE1
    -- the coarse tensor, read off the fine system by the reindexing `i ↦ 2 i`
    have hdbl : ∀ (pp : ℝ → ℝ) (ee : NegSobolev d m) (u : ℝ) (i : ℕ),
        kernelNodes Rb.D Rb.ρ m c c' n pp ee u i = kernelNodes Rb.D Rb.ρ m c c' (n + 1) pp ee u (2 * i) := by
      intro pp ee u i
      unfold kernelNodes
      rw [S7PIDT_grid_double c c' n i]
    have hτ : ∀ j ≤ 2 ^ n, 2 * j ≤ 2 ^ (n + 1) := fun j hj => by rw [pow_succ]; omega
    have hn0 := hnucg (n + 1) n (fun i => 2 * i) hτ Φ0 hΦ0 M
    let Ψ0 : (Fin (2 ^ (n + 1) + 1) → EuclideanSpace ℝ (Fin r)) →L[ℝ] PathSpace d m T :=
      Φ0.comp (ContinuousLinearMap.pi fun j : Fin (2 ^ n + 1) =>
        emb.comp (ContinuousLinearMap.proj (⟨2 * j.1, Nat.lt_succ_of_le (hτ j.1 (Nat.lt_succ_iff.1 j.2))⟩ :
          Fin (2 ^ (n + 1) + 1))))
    obtain ⟨hI0, hE0⟩ := hid Ψ0 Ψ0 M
    have hΨ0 : ∀ x, Ψ0 x = Φ0 (fun j => emb (x ⟨2 * j.1, Nat.lt_succ_of_le (hτ j.1 (Nat.lt_succ_iff.1 j.2))⟩)) :=
      fun x => rfl
    simp only [hΨ0] at hI0 hE0
    have hcoarse : nuc Rb.D Rb.ρ m T c c' n
        (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' n p (modeVec m k) u i))
        (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' n q (modeVec m l) u i)) M =
        ∫ ω, M ![polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y (2 * i) ω)),
          polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y' (2 * i) ω))] ∂P := by
      simp only [hdbl]
      refine hn0.trans (hE0.trans ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show _ = M ![polyPath Rb.D Rb.ρ m T c c' n _, polyPath Rb.D Rb.ρ m T c c' n _]
      rw [hΦ0, hΦ0]
    have hfine : nuc Rb.D Rb.ρ m T c c' (n + 1)
        (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' (n + 1) p (modeVec m k) u i))
        (fun u i => truncF m F (kernelNodes Rb.D Rb.ρ m c c' (n + 1) q (modeVec m l) u i)) M =
        ∫ ω, M ![polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y i ω)),
          polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y' i ω))] ∂P := by
      refine hn1.trans (hE1.trans ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show _ = M ![polyPath Rb.D Rb.ρ m T c c' (n + 1) _, polyPath Rb.D Rb.ρ m T c c' (n + 1) _]
      rw [hΦ1, hΦ1]
    rw [ContinuousLinearMap.sub_apply, hfine, hcoarse]
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 : ℝ) ^ (-(n : ℝ) / 4) := ⟨_, rfl⟩
    rw [← hθ]
    have hθ0 : 0 < θ := by rw [hθ]; exact Real.rpow_pos_of_pos (by norm_num) _
    have hθ4 : θ ^ 4 = 1 / 2 ^ n := by rw [hθ]; exact S7PIDT_theta4 n
    have h2n : (0 : ℝ) < 2 ^ n := by positivity
    have hδ2 : ∫ ω, δ ω ^ 2 ∂P ≤ 2 * κ * θ ^ 2 := by
      refine S7PIDT_le_of_sq (by positivity) (hδI.trans ?_)
      have e1 : (2 * κ * θ ^ 2) ^ 2 = 4 * κ ^ 2 * (1 / 2 ^ n) := by rw [← hθ4]; ring
      have e2 : 3 * κ ^ 2 / 2 ^ (n + 1) = (3 / 2) * κ ^ 2 * (1 / 2 ^ n) := by
        field_simp; ring
      have e3 : 0 ≤ κ ^ 2 * (1 / 2 ^ n) := by positivity
      rw [e1, e2]; linarith
    have hδ2' : ∫ ω, δ' ω ^ 2 ∂P ≤ 2 * κ' * θ ^ 2 := by
      refine S7PIDT_le_of_sq (by positivity) (hδI'.trans ?_)
      have e1 : (2 * κ' * θ ^ 2) ^ 2 = 4 * κ' ^ 2 * (1 / 2 ^ n) := by rw [← hθ4]; ring
      have e2 : 3 * κ' ^ 2 / 2 ^ (n + 1) = (3 / 2) * κ' ^ 2 * (1 / 2 ^ n) := by
        field_simp; ring
      have e3 : 0 ≤ κ' ^ 2 * (1 / 2 ^ n) := by positivity
      rw [e1, e2]; linarith
    have hbA : ∀ ω, ‖polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y' i ω))‖ ≤ C₁ * S' ω := fun ω =>
      (hpoly c c' hc hcc hc' (n + 1) (fun i => emb (Y' i ω))).2.1 (S' ω) fun i hi =>
        (hemb _).trans (hSb' ω i hi)
    have hbS : ∀ ω, ‖polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y (2 * i) ω))‖ ≤ C₁ * S ω := fun ω =>
      (hpoly c c' hc hcc hc' n (fun i => emb (Y (2 * i) ω))).2.1 (S ω) fun i hi =>
        (hemb _).trans (hSb ω (2 * i) (hτ i hi))
    have hdel : ∀ ω, ‖polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y i ω)) -
        polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y (2 * i) ω))‖ ≤ C₁ * δ ω := fun ω => by
      have h := (hpoly c c' hc hcc hc' n (fun i => emb (Y i ω))).2.2 (δ ω) fun j hj => by
        rw [← map_sub]; exact (hemb _).trans (hδb ω j hj)
      have := hδ0 ω
      nlinarith
    have hdel' : ∀ ω, ‖polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y' i ω)) -
        polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y' (2 * i) ω))‖ ≤ C₁ * δ' ω := fun ω => by
      have h := (hpoly c c' hc hcc hc' n (fun i => emb (Y' i ω))).2.2 (δ' ω) fun j hj => by
        rw [← map_sub]; exact (hemb _).trans (hδb' ω j hj)
      have := hδ0' ω
      nlinarith
    have hi1 : Integrable (fun ω => M ![polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y i ω)),
        polyPath Rb.D Rb.ρ m T c c' (n + 1) (fun i => emb (Y' i ω))]) P := by
      simpa only [hΦ1] using hI1
    have hi2 : Integrable (fun ω => M ![polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y (2 * i) ω)),
        polyPath Rb.D Rb.ρ m T c c' n (fun i => emb (Y' (2 * i) ω))]) P := by
      simpa only [hΦ0] using hI0
    have hB := S7PIDT_B2 P M _ _ _ _ C₁ hC₁0 (2 * κ * θ ^ 2) (162 * κ) (2 * κ' * θ ^ 2) (162 * κ')
      (18 * W * θ) (18 * W * θ) (by positivity) (by positivity)
      (by linear_combination (324 * θ ^ 2) * hW2) (by linear_combination (324 * θ ^ 2) * hW2)
      S S' δ δ' hSm hSm' hδm hδm' hS0 hS0' hδ0 hδ0' hbA hbS hdel hdel' hSi hSi' hδi hδi' hδ2 hδ2' hSI hSI'
      hi1 hi2
    refine hB.trans ?_
    have : 0 ≤ W * θ := by positivity
    nlinarith [mul_nonneg hMn (mul_nonneg (sq_nonneg C₁) this), mul_nonneg hMn (mul_nonneg hC₁0 this)]

end HRS.MC.E213M

end
