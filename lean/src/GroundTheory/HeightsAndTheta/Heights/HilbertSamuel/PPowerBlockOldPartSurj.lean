import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.ChartForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockOldPartSurj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockOldPartSurj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

alias homog_congr := SectionNormSqExtension.homog_congr
alias homog_zero := SectionNormSqExtension.homog_zero
alias homog_add := SectionNormSqExtension.homog_add
alias homog_neg := SectionNormSqExtension.homog_neg
alias homog_sub := SectionNormSqExtension.homog_sub
alias homog_sum := SectionNormSqExtension.homog_sum
alias homog_one := SectionNormSqExtension.homog_one
alias homog_C := SectionNormSqExtension.homog_C
alias homog_mul := SectionNormSqExtension.homog_mul
alias homog_X := SectionNormSqExtension.homog_X
alias homog_pow := SectionNormSqExtension.homog_pow

def chartMon (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k

theorem homog_chartMon (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMon c d) d :=
  SectionNormSqExtension.homog_chartMon c d

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k :=
  SectionNormSqExtension.aeval_chartMon y c d

theorem eval_chartMon (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMon c d)) = ∏ k, z ⟨k, c k⟩ ^ d k :=
  SectionNormSqExtension.eval_chartMon z c d

alias mConeMap_homog := SectionNormSqExtension.mConeMap_homog

theorem mem_of_homog {y : (Σ k, ι k) → Ω} {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y hg, h0]
  simp

alias exists_form_of_mem_chartRingZ := SectionNormSqExtension.exists_form_of_mem_chartRingZ
alias exists_chartForm := SectionNormSqExtension.exists_chartForm

theorem exists_chart_at {y : (Σ k, ι k) → Ω} {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hx.1
  exact ⟨c, hc, fun k => SectionNormSqExtension.y_ne_zero hx (hc k)⟩

theorem exists_common_forms (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ)
    (m N : ℕ) (v : Fin N → Ω) (hv : ∀ j, v j ∈ chartLat y a m) :
    ∃ (L E : K → ℕ) (G : Fin N → MRing ι), (∀ j, IsMultiHomog (G j) E) ∧ (∀ k, (E k : ℤ) = m * a k + L k) ∧
      ∀ j, aeval y (G j) = v j * ∏ k, y ⟨k, c k⟩ ^ L k := by
  obtain ⟨L, E, G, he, hG, hvG⟩ := SectionNormSqExtension.exists_chartForms_of_degree y a m N v hv c
  exact ⟨L, E, G, hG, fun k => (he k).trans (add_comm _ _), fun j => by
    simpa only [SectionNormSqExtension.aeval_chartMon] using hvG j⟩

theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * a k) v) {L E : K → ℕ} {G : Fin N → MRing ι}
    (hG : ∀ j, IsMultiHomog (G j) E) (hE : ∀ k, (E k : ℤ) = m * a k + L k)
    (hGy : ∀ j, aeval y (G j) = v j * ∏ k, y ⟨k, c k⟩ ^ L k)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 := by
  apply SectionNormSqExtension.exists_eval_ne_of_generates hgen hc (fun k => (hE k).trans (add_comm _ _)) hG _ hx hxc
  intro j
  simpa only [SectionNormSqExtension.aeval_chartMon] using hGy j

def substForms {N : ℕ} (G : Fin N → MRing ι) : (Σ k, addIdx ι N k) → MRing ι
  | ⟨none, j⟩ => G j
  | ⟨some k, i⟩ => X ⟨k, i⟩

theorem vanish_new {N : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin N → Ω) (E : K → ℕ) (ρ : Ω) (G : Fin N → MRing ι)
    (hG : ∀ j, IsMultiHomog (G j) E) (hGy : ∀ j, aeval y (G j) = v j * ρ)
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) {f : MRing (addIdx ι N)}
    (hf : f ∈ mCoordIdeal (addBlock y v)) :
    eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) f) = 0 := by
  classical

  let Γ : MRing (addIdx ι N) →ₐ[ℤ] MvPolynomial (Option K) (MRing ι) :=
    aeval fun p => MvPolynomial.C (substForms G p) * MvPolynomial.X p.1

  let Θ : MvPolynomial (Option K) Ω →+* MvPolynomial (Option K) (MvPolynomial K Ω) :=
    eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) fun o => Option.elim o
      (MvPolynomial.C (MvPolynomial.C ρ * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ E k) * MvPolynomial.X none)
      fun k => MvPolynomial.C (MvPolynomial.X k) * MvPolynomial.X (some k)
  have hcomm : (MvPolynomial.map (mConeMap y).toRingHom).comp Γ.toRingHom =
      Θ.comp (mConeMap (addBlock y v)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int
        (((MvPolynomial.map (mConeMap y).toRingHom).comp Γ.toRingHom).comp C)
        ((Θ.comp (mConeMap (addBlock y v)).toRingHom).comp C)) r
    · obtain ⟨o, i⟩ := p
      cases o with
      | none =>
        change Fin N at i
        have hΓ : Γ (X ⟨none, i⟩) = MvPolynomial.C (G i) * MvPolynomial.X none := by
          simp only [Γ, aeval_X]
          rfl
        have hM : mConeMap (addBlock y v) (X ⟨none, i⟩) = MvPolynomial.C (v i) * MvPolynomial.X none := by
          simp only [mConeMap, aeval_X]
          rfl
        show MvPolynomial.map (mConeMap y).toRingHom (Γ (X ⟨none, i⟩)) = Θ (mConeMap (addBlock y v) (X ⟨none, i⟩))
        rw [hΓ, hM, map_mul, map_C, map_X, map_mul]
        have hC : ∀ w : Ω, Θ (MvPolynomial.C w) = MvPolynomial.C (MvPolynomial.C w) := fun w => eval₂Hom_C _ _ _
        have hX : Θ (MvPolynomial.X none) = MvPolynomial.C (MvPolynomial.C ρ *
            ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ E k) * MvPolynomial.X none := eval₂Hom_X' _ _ _
        rw [hC, hX, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, mConeMap_homog y (hG i), hGy i]
        simp only [map_mul]
        ring
      | some k =>
        have hΓ : Γ (X ⟨some k, i⟩) = MvPolynomial.C (X ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [Γ, aeval_X]
          rfl
        have hM : mConeMap (addBlock y v) (X ⟨some k, i⟩) = MvPolynomial.C (y ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [mConeMap, aeval_X]
          rfl
        show MvPolynomial.map (mConeMap y).toRingHom (Γ (X ⟨some k, i⟩)) =
          Θ (mConeMap (addBlock y v) (X ⟨some k, i⟩))
        rw [hΓ, hM, map_mul, map_C, map_X, map_mul]
        have hC : Θ (MvPolynomial.C (y ⟨k, i⟩)) = MvPolynomial.C (MvPolynomial.C (y ⟨k, i⟩)) := eval₂Hom_C _ _ _
        have hX : Θ (MvPolynomial.X (some k)) = MvPolynomial.C (MvPolynomial.X k) * MvPolynomial.X (some k) :=
          eval₂Hom_X' _ _ _
        have hY : (mConeMap y).toRingHom (X ⟨k, i⟩) = MvPolynomial.C (y ⟨k, i⟩) * MvPolynomial.X k := by
          simp [mConeMap]
        rw [hC, hX, hY, C_mul]
        ring
  have hzero : MvPolynomial.map (mConeMap y).toRingHom (Γ f) = 0 := by
    have h1 : MvPolynomial.map (mConeMap y).toRingHom (Γ f) = Θ (mConeMap (addBlock y v) f) :=
      RingHom.congr_fun hcomm f
    have h2 : mConeMap (addBlock y v) f = 0 := RingHom.mem_ker.mp hf
    rw [h1, h2, map_zero]

  let ψ : MRing ι →+* ℂ := (eval x).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hcoef : MvPolynomial.map ψ (Γ f) = 0 := by
    ext μ
    rw [coeff_map, coeff_zero]
    have hm : coeff μ (Γ f) ∈ mCoordIdeal y := by
      show _ ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker]
      have := congrArg (coeff μ) hzero
      rwa [coeff_map, coeff_zero] at this
    exact hx.2 _ hm

  have hval : ((eval fun _ => (1 : ℂ)).comp ((MvPolynomial.map ψ).comp Γ.toRingHom)) =
      (eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)))).comp
        (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int
        (((eval fun _ => (1 : ℂ)).comp ((MvPolynomial.map ψ).comp Γ.toRingHom)).comp C)
        (((eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)))).comp
          (MvPolynomial.map (Int.castRingHom ℂ))).comp C)) r
    · obtain ⟨o, i⟩ := p
      cases o with
      | none =>
        change Fin N at i
        have hΓ : Γ (X ⟨none, i⟩) = MvPolynomial.C (G i) * MvPolynomial.X none := by
          simp only [Γ, aeval_X]
          rfl
        show eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ (X ⟨none, i⟩))) =
          eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) (X ⟨none, i⟩))
        rw [hΓ, map_mul, map_C, map_X, map_X, eval_X, map_mul, eval_C, eval_X, mul_one]
        rfl
      | some k =>
        have hΓ : Γ (X ⟨some k, i⟩) = MvPolynomial.C (X ⟨k, i⟩) * MvPolynomial.X (some k) := by
          simp only [Γ, aeval_X]
          rfl
        show eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ (X ⟨some k, i⟩))) =
          eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) (X ⟨some k, i⟩))
        rw [hΓ, map_mul, map_C, map_X, map_X, eval_X, map_mul, eval_C, eval_X, mul_one]
        simp [ψ]
        rfl
  have h3 : eval (fun _ => (1 : ℂ)) (MvPolynomial.map ψ (Γ f)) =
      eval (addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j))) (map (Int.castRingHom ℂ) f) :=
    RingHom.congr_fun hval f
  rw [← h3, hcoef, map_zero]

end PowerBlockOldPartSurj

open PowerBlockOldPartSurj in

theorem PowerBlockOldPartSurj.proof : PowerBlockOldPartSurj.Statement := by
  intro K _ ι _ Ω _ y a m N v hv hgen x hx
  classical
  obtain ⟨c, hxc, hyc⟩ := exists_chart_at hx
  obtain ⟨L, E, G, hG, hE, hGy⟩ := exists_common_forms y c hyc a m N v hv
  obtain ⟨j, hj⟩ := exists_ne_zero hyc hgen hG hE hGy hx hxc
  refine ⟨addBlock x fun j => eval x (map (Int.castRingHom ℂ) (G j)), ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | none => exact ⟨j, hj⟩
    | some k => exact ⟨c k, hxc k⟩
  · exact vanish_new y v E _ G hG hGy hx hf

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
