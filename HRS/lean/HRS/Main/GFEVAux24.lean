import HRS.Main.GFEVAux23

/-!
# Packet GFEVG, part 24: the evolution data `EV`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

/-- the projection `P_n` on `E_γ` -/
def gfevPH (d γ n : ℕ) : NegSobolev d (γ : ℝ) →L[ℝ] NegSobolev d (γ : ℝ) := gfevP (gfevSn d n)

open Classical in
/-- the `E_{γ-4}`-norm of a vector of the core -/
def gfevN (d γ : ℕ) (x : NegSobolev d (γ : ℝ)) : ℝ :=
  if h : ∃ w : NegSobolev d ((γ : ℝ) - 4), NegSobolev.embed (γ : ℝ) w = x then ‖h.choose‖ else 0

theorem gfevN_embed (γ : ℕ) (w : NegSobolev d ((γ : ℝ) - 4)) : gfevN d γ (NegSobolev.embed (γ : ℝ) w) = ‖w‖ := by
  have h : ∃ w' : NegSobolev d ((γ : ℝ) - 4), NegSobolev.embed (γ : ℝ) w' = NegSobolev.embed (γ : ℝ) w := ⟨w, rfl⟩
  unfold gfevN
  rw [dif_pos h, gfev_embed_injective (gfev_le4 γ) h.choose_spec]

theorem gfevN_nonneg (γ : ℕ) (x : NegSobolev d (γ : ℝ)) : 0 ≤ gfevN d γ x := by
  unfold gfevN; split_ifs <;> positivity

theorem GFPde.evolData (h : GFPde d s γ R VB Λ D T ρ) (l₀ l₂ l₄ : ℝ)
    (hq0 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) (γ : ℝ) l₀)
    (hq2 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 2) l₂)
    (hq4 : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 4) l₄) :
    ∃ EV : EvolData (NegSobolev d (γ : ℝ)) (NegSobolev d (γ : ℝ)),
      EV.IsEvolution T ∧ (∀ K : ℝ, 2 * l₀ ≤ K → EV.Dissipative T K) ∧
      (∀ z, EV.j z = NegSobolev.embed (γ : ℝ) z) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (z : NegSobolev d (γ : ℝ)) (φ : Torus d → ℝ), Torus.IsSmooth φ →
        NegSobolev.eval (EV.VE t u z) φ = NegSobolev.eval z (UpF D (gfevMu T ρ) u t φ)) := by
  obtain ⟨V, W, A2, M, hAbs, hM, hA2n, hA2c, hVd, hWb, hcons⟩ := h.absData l₀ l₂ l₄ hq0 hq2 hq4
  set A : ℝ → gfevD d γ →ₗ[ℝ] NegSobolev d (γ : ℝ) := fun s => gfevAop (A2 s) with hA
  let EV : EvolData (NegSobolev d (γ : ℝ)) (NegSobolev d (γ : ℝ)) :=
    { j := ContinuousLinearMap.id ℝ _, VH := V, VE := V, D := gfevD d γ, A := A }
  have hT0 : 0 ≤ T := h.hT.le
  have hjid : ∀ z, EV.j z = z := fun z => rfl
  refine ⟨EV, ?_, ?_, fun z => ?_, ?_⟩
  · -- IsEvolution
    refine ⟨fun x y hxy => hxy, gfev_dense_D γ, fun t ht => hAbs.self t ht.1, fun t ht => hAbs.self t ht.1,
      fun s' r t hs hsr hrt _ => hAbs.comp s' r t hs hsr hrt, fun s' r t hs hsr hrt _ => hAbs.comp s' r t hs hsr hrt,
      fun r t hr hrt _ => ContinuousLinearMap.ext fun z => rfl,
      fun x => hAbs.cont T x, ?_⟩
    intro t ht x r hr
    have := hAbs.deriv_r ht.1 (x.2) hr
    rw [gfevAt_of_mem r x.2] at this
    exact this
  · intro K hK
    refine ⟨fun x => rfl, fun y => ⟨y, rfl⟩, ?_, ?_, ?_⟩
    · intro r hr z
      have := hAbs.quasi hr.1 z.2
      rw [gfevAt_of_mem r z.2] at this
      change 2 * inner ℝ (z : NegSobolev d (γ : ℝ)) (A r z) ≤ K * ‖(z : NegSobolev d (γ : ℝ))‖ ^ 2
      nlinarith [sq_nonneg ‖(z : NegSobolev d (γ : ℝ))‖]
    · intro r hr t ht x
      have hxD : (x : NegSobolev d (γ : ℝ)) ∈ gfevD d γ := x.2
      have hinv := hAbs.inv r t hr.1 ht.1 _ hxD
      refine ⟨hinv, ?_⟩
      have := hAbs.forward hr.1 hr.2 hxD t ht
      rw [gfevAt_of_mem t hinv] at this
      exact this
    · -- Galerkin
      have hproj : GFProj (gfevD d γ) (gfevPH d γ) := GFEV_proj d γ
      have hε0 : ∀ n : ℕ, 0 ≤ M * (1 / ((n : ℝ) + 1)) ^ 2 := fun n => by positivity
      have hε : Tendsto (fun n : ℕ => M * (1 / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
        simpa using this.const_mul M
      have htail : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → ∀ x ∈ gfevD d γ,
          ‖gfevAt (gfevD d γ) A s (x - gfevPH d γ n x)‖ ≤
            (M * (1 / ((n : ℝ) + 1)) ^ 2) * gfevN d γ x := by
        intro n s' hs' x hx
        obtain ⟨w, rfl⟩ := gfev_mem_D hx
        have e1 : NegSobolev.embed (γ : ℝ) (w - q48bFin ((γ : ℝ) - 4) (gfevSn d n)
            (fun k => NegSobolev.fourierCoeff w k)) =
            NegSobolev.embed (γ : ℝ) w - gfevPH d γ n
              (NegSobolev.embed (γ : ℝ) w) := by
          rw [gfev_embed_sub (gfev_le4 γ), gfev_embed_trunc]; rfl
        rw [← e1, gfevN_embed]
        change ‖gfevAt (gfevD d γ) (fun s => gfevAop (A2 s)) s' _‖ ≤ _
        rw [gfevAt_embed A2 s']
        calc ‖A2 s' (NegSobolev.embed ((γ : ℝ) - 2) _)‖ ≤ ‖A2 s'‖ * ‖NegSobolev.embed ((γ : ℝ) - 2)
              (w - q48bFin ((γ : ℝ) - 4) (gfevSn d n) (fun k => NegSobolev.fourierCoeff w k))‖ :=
            (A2 s').le_opNorm _
          _ ≤ M * ((1 / ((n : ℝ) + 1)) ^ 2 * ‖w‖) :=
            mul_le_mul (hA2n s') (gfev_tail_bound γ n w) (norm_nonneg _) hM
          _ = _ := by ring
      have hprop : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x ∈ gfevD d γ,
          gfevN d γ (V t r x) ≤ Real.exp (|l₄| * T) * gfevN d γ x := by
        intro r t hr hrt htT x hx
        obtain ⟨w, rfl⟩ := gfev_mem_D hx
        rw [hcons r t hr hrt w, gfevN_embed, gfevN_embed]
        calc ‖W t r w‖ ≤ ‖W t r‖ * ‖w‖ := (W t r).le_opNorm w
          _ ≤ Real.exp (|l₄| * T) * ‖w‖ := by
            refine mul_le_mul_of_nonneg_right ((hWb r t hr hrt).trans (gfev_exp_le l₄ (by linarith)
              (by linarith))) (norm_nonneg _)
      obtain ⟨Vn, hV1, hV2, hV3, hV4⟩ := gfev_galerkin (V := V) (D := gfevD d γ) (A := A) (C := l₀) hAbs hproj
        (gfev_dense_D γ) (N := gfevN d γ) (ε := fun n => M * (1 / ((n : ℝ) + 1)) ^ 2)
        (M4 := Real.exp (|l₄| * T)) (gfevN_nonneg γ) hε0 hε htail T hprop
      refine ⟨gfevPH d γ, Vn,
        fun n => ContinuousLinearMap.ext fun x => hproj.idem n x, hproj.symm, hproj.findim, hproj.mem,
        hproj.tendsto, hV1, hV2, ?_, hV4⟩
      intro n r t x y hmem hr ht hy
      have := hV3 n r t x y hr ht hy
      rw [gfevAt_of_mem t hmem] at this
      exact this
  · exact (hjid z).trans (gfev_embed_self _ z).symm
  · intro u t hu hut htT z φ hφ
    exact hVd u t hu hut z φ (dom_smooth hφ)

end HRS.GF
