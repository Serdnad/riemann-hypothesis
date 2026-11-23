module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem prvE_of_gl_operators_form_representation (D : Formalism.BasicNotions.D7) (hME : ManyEdges) (hS7 : S7) (hAsm : Asm) (hNum : Num)
    (hBP : BePerfect) (hOE : LPOneEvery)
    (Ct0 CD1 Cr C₁ : ℝ) (h0 : 0 < Ct0) (h1 : 0 < CD1) (h2 : 0 < Cr) (h3 : 0 < C₁)
    (hE : ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0 CD1 Cr) : tableLineDegreeFive.ConclusionE D := by
  refine ⟨max C₁ (max 2 (max Ct0 (max CD1 (Cr + 1)))), lt_of_lt_of_le h3 (le_max_left _ _), ?_⟩
  intro C hC
  have hC1 : C₁ ≤ C := le_trans (le_max_left _ _) hC
  have hC' := le_trans (le_max_right _ _) hC
  have hC2 : 2 ≤ C := le_trans (le_max_left _ _) hC'
  have hC'' := le_trans (le_max_right _ _) hC'
  have hC3 : Ct0 ≤ C := le_trans (le_max_left _ _) hC''
  have hC''' := le_trans (le_max_right _ _) hC''
  have hC4 : CD1 ≤ C := le_trans (le_max_left _ _) hC'''
  have hC5 : Cr + 1 ≤ C := le_trans (le_max_right _ _) hC'''
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet hp hr
    hOrb hN1 hWt hY hLa hk hL1 hD hc hsz t ht
  have hH : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar :=
    ⟨hp, hr, hOrb, hN1, hWt, hY, hLa, hk, hL1, hD, hc, hsz⟩
  have hdom : IsDominant lam0 := hWt.2.1
  apply hOE p n' W Qq O Kf ι σ j w hSet.1 m r lam0 t Dp _ cStar hdom
  refine ⟨by omega, colSpan W 1, ⟨1, by simp, rfl⟩, ?_⟩
  apply hS7 p n' W Qq O Kf ι σ j w hSet.1 hBP m r lam0 t Dp _ cStar _ hdom (by omega)
  obtain ⟨E, hE1, hE2⟩ := hME p n' W Qq O Kf ι σ j w hSet.1 (m + 1) r (by omega)
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hNum C Ct0 CD1 Cr h0 h1 h2 hC2 hC3 hC4 hC5 p n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hH
  have key : ∀ e ∈ E, _ := fun e he =>
    hE C hC1 p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet hH e
      (hE1 e he).1 (hE1 e he).2
  choose! nE tS tT D1 hkey using key
  apply hAsm p n' W Qq O Kf ι σ j w hSet.1 m r lam0 t Dp _ cStar _ E nE hE1
  · intro e he
    obtain ⟨a1, a2, a3, _, a5⟩ := hkey e he
    refine ⟨tS e, tT e, D1 e, ?_, ?_, ?_, a5⟩
    · have : (tS e : ℝ) ≤ t := by linarith
      exact_mod_cast this
    · have : (tT e : ℝ) ≤ t := by linarith
      exact_mod_cast this
    · have : (D1 e : ℝ) ≤ Dp := by linarith
      exact_mod_cast this
  · set ρ : ℝ := (1 - Cr * (TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) *
      (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card with hρ
    set Qr : ℝ := (p : ℝ) ^ (n' * (r * (m + 1 - r))) with hQr
    have hp0 : (0 : ℝ) < p := by
      have : 0 < p := by omega
      exact_mod_cast this
    have hQpos : 0 < Qr := pow_pos hp0 _
    have hdim : (0 : ℝ) ≤ (dimV Kf lam0 : ℝ) := Nat.cast_nonneg _
    have hle : (1 - C * TT.card * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) * (dimV Kf lam0 : ℝ) ≤
        ρ * (dimV Kf lam0 : ℝ) := mul_le_mul_of_nonneg_right hn4 hdim
    refine le_trans hle ?_
    rcases le_or_gt 0 (ρ * (dimV Kf lam0 : ℝ)) with hpos | hneg
    · have hsum : (E.card : ℝ) * (ρ * (dimV Kf lam0 : ℝ) / Qr) ≤ ((∑ e ∈ E, nE e : ℕ) : ℝ) := by
        push_cast
        rw [← nsmul_eq_mul]
        apply Finset.card_nsmul_le_sum
        intro e he
        exact (hkey e he).2.2.2.1
      have hcard : Qr ≤ (E.card : ℝ) := by
        rw [hQr]
        exact_mod_cast hE2
      have : Qr * (ρ * (dimV Kf lam0 : ℝ) / Qr) ≤ (E.card : ℝ) * (ρ * (dimV Kf lam0 : ℝ) / Qr) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hpos hQpos.le)
      have h4 : Qr * (ρ * (dimV Kf lam0 : ℝ) / Qr) = ρ * (dimV Kf lam0 : ℝ) := by
        field_simp
      linarith
    · exact le_trans hneg.le (Nat.cast_nonneg _)

theorem theorem_II_of_edge_bound_constants (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hME : ManyEdges) (hS7 : S7) (hAsm : Asm) (hNum : Num)
    (hA : tableLineDegreeFive.admitted D CLa Ck Crk Cdeg) (h14a : SourceCleaning.aux₃ D CLa' CD Csz) (h14b : PlaneGramData.aux₃ D CH CE C6 C18)
    (hR : RestEdge D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) : tableLineDegreeFive.ConclusionE D := by
  obtain ⟨Ct0, CD1, Cr, C₁, h0, h1, h2, h3, hE⟩ := hR hA h14a h14b
  have hBP : BePerfect := hA.2.2.2.1
  have hOE : LPOneEvery := hA.2.2.2.2.1
  exact prvE_of_gl_operators_form_representation D hME hS7 hAsm hNum hBP hOE Ct0 CD1 Cr C₁ h0 h1 h2 h3 hE

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

theorem w_ne_zero {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) :
    algebraMap O Kf w ≠ 0 := by
  intro h
  have := hS.frac_alt
  have h2 : algebraMap O Kf ((p : ℕ) : O) = 0 := by
    rw [← hS.w_sq, map_pow, h, zero_pow two_ne_zero]
  have h3 : ι (algebraMap W Qq ((p : ℕ) : W)) = 0 := by
    rw [hS.ι_comp, map_natCast j]
    exact h2
  have h4 : algebraMap W Qq ((p : ℕ) : W) = 0 := (map_eq_zero ι).mp h3
  have h5 : ((p : ℕ) : W) = 0 := IsFractionRing.injective W Qq (by rw [h4, map_zero])
  exact hS.p_unif.ne_zero h5

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem mem_scale {c : Kf} {M : Submodule O X} {x : X} : x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  simp only [scale, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]

theorem scale_neg_mono (w : O) (hw : algebraMap O Kf w ≠ 0) {s t : ℕ} (hst : s ≤ t) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ (-(s : ℤ))) M ≤ scale (algebraMap O Kf w ^ (-(t : ℤ))) M := by
  intro x hx
  rw [mem_scale] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨w ^ (t - s) • y, M.smul_mem _ hy, ?_⟩
  rw [← algebraMap_smul Kf (w ^ (t - s)) y, smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw,
    show -(t : ℤ) + ((t - s : ℕ) : ℤ) = -(s : ℤ) by omega]

theorem scale_pos_le (w : O) (c : ℕ) (M : Submodule O X) : scale (algebraMap O Kf w ^ (c : ℤ)) M ≤ M := by
  intro x hx
  rw [mem_scale] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [zpow_natCast, ← map_pow, algebraMap_smul]
  exact M.smul_mem _ hy

end Scale

theorem ValLe.mono {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {π : O} {D D' : ℕ} {x : Kf}
    (h : ValLe π D x) (hD : D ≤ D') : ValLe π D' x := by
  obtain ⟨a, b, hx, hab⟩ := h
  refine ⟨a, b * π ^ (D' - D), hx, ?_⟩
  rw [← mul_assoc, hab, ← pow_add, Nat.add_sub_cancel' hD]

theorem asm : Asm := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r lam0 t D κ cStar L E nE hE hF hcard
  classical
  have hw := w_ne_zero hS
  unfold EdgeFam at hF
  choose tS tT D1 htS htT hD1 F hF1 hF2 hF3 using hF
  unfold SrcTests
  refine ⟨E, nE, fun e => if h : e ∈ E then F e h else fun _ => 0, hE, ?_, ?_, ?_, hcard⟩
  · intro e he i
    simp only [dif_pos he]
    unfold Nsrc
    refine Submodule.mem_inf.mpr ⟨scale_neg_mono w hw (htS e he) _ (hF1 e he i).1, ?_⟩
    refine (Submodule.mem_iInf _).mpr fun e' => (Submodule.mem_iInf _).mpr fun he' => ?_
    by_cases hee : e' = e
    · subst hee
      exact (hF1 e' he i).2
    · exact scale_pos_le w cStar _ (hF2 e he i e' he'.1 he'.2 hee)
  · intro e he i e' he' hsrc hne
    simp only [dif_pos he]
    exact hF2 e he i e' he' hsrc hne
  · intro e he c hc
    obtain ⟨G, hG1, hG2, hG3, hG4⟩ := hF3 e he c hc
    refine ⟨G, ?_, ?_, ?_⟩
    · rw [(hE e he).2] at hG1
      unfold Ntgt
      refine Submodule.mem_inf.mpr ⟨scale_neg_mono w hw (htT e he) _ hG1, ?_⟩
      refine (Submodule.mem_iInf _).mpr fun e' => (Submodule.mem_iInf _).mpr fun he' => ?_
      by_cases hee : e' = e
      · subst hee
        exact hG2
      · exact scale_pos_le w cStar _ (hG3 e' he'.1 (he'.2.trans (hE e he).2.symm) hee)
    · simp only [dif_pos he]
      exact ValLe.mono hG4 (hD1 e he)
    · intro e' he' hne
      exact hG3 e' (hE e' he').1 ((hE e' he').2.trans (hE e he).2.symm) hne

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def EdgeFamOf : Prop :=
  ∀ (D : Formalism.BasicNotions.D7), tableLineDegreeFive.LevelPrimesProviso D → BePerfect → DualHeightInclusion →
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
  ∀ (m r : ℕ) (fl rest lam0 : Fin n' → Fin (m + 1) → ℤ) (hnu : lam0 = fl + rest) (h1 : IsDominant fl)
    (h2 : IsDominant rest) (e : Edge W Qq (m + 1)), IsEdge p n' r e →
  ∀ (nb n2 T oS tT D1 cStar c' : ℕ), cStar + oS ≤ c' → 2 * (D1 + 1) ≤ c' →
  ∀ (Fvb Sy : Fin nb → Vsp Kf fl) (sh : Fin n2 → Vsp Kf rest),
    (∀ b, Fvb b ∈ scale (algebraMap O Kf w ^ (-(T : ℤ))) (HL (O := O) ι σ fl e.src)) →
    (∀ b, Fvb b - Sy b ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r fl e)) →
    (∀ b, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      Fvb b ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r fl e')) →
    (∀ b, Sy b ∈ Re p ι σ w r fl e) →
    (∀ i, sh i ∈ Re p ι σ w r rest e ∧
      sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ rest e.src)) →
    (∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
      ∃ G : Module.Dual Kf (Vsp Kf lam0),
        G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
        G ∈ Re' p ι σ w r lam0 e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
        ValLe (p : O) D1 (be p r lam0 (∑ x, c x • mulV hnu h1 h2 (Sy x.1) (sh x.2)) G)) →
    EdgeFam (W := W) (O := O) p n' ι σ w r lam0 (T + oS) tT D1 cStar e (nb * n2)

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Ring

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem p_nonunit (hS : HidaSetting p n' W Qq O Kf ι σ j w) : ¬ IsUnit (p : O) := by
  intro hu
  let _ : Algebra W O := j.toAlgebra
  have _ : Module.Finite W O := hS.finite
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := W) (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (IsLocalRing.maximalIdeal O)
  have heq : (IsLocalRing.maximalIdeal O).comap (algebraMap W O) = IsLocalRing.maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal hmax
  have hpW : (p : W) ∈ IsLocalRing.maximalIdeal W := hS.p_unif.not_isUnit
  rw [← heq, Ideal.mem_comap, map_natCast] at hpW
  exact hpW hu

end Ring

theorem goodRank_of_prim {O Kf X : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup X] [Module O X]
    (hinj : Function.Injective (algebraMap O Kf)) (π : O) (A : Submodule O X) {M : ℕ} (φ : Fin M → X → Kf) (D : ℕ)
    (hadd : ∀ i G G', φ i (G + G') = φ i G + φ i G')
    (hsmul : ∀ i (c : O) G, φ i (c • G) = algebraMap O Kf c * φ i G)
    (hint : ∀ i, ∀ G ∈ A, φ i G ∈ Set.range (algebraMap O Kf))
    (hprim : ∀ c : Fin M → O, (∃ i, IsUnit (c i)) →
      ∃ G ∈ A, ValLe π D (∑ i, algebraMap O Kf (c i) * φ i G)) :
    GoodRankK π A φ M D := by
  classical
  have h0 : ∀ i, φ i 0 = 0 := fun i => by
    have h := hadd i 0 0
    rw [add_zero] at h
    linear_combination -h
  let S : Submodule O (Fin M → O) :=
    { carrier := {v | ∃ G ∈ A, ∀ i, algebraMap O Kf (v i) = φ i G}
      add_mem' := by
        rintro v v' ⟨G, hG, hv⟩ ⟨G', hG', hv'⟩
        exact ⟨G + G', A.add_mem hG hG', fun i => by rw [Pi.add_apply, map_add (f := _), hv, hv', hadd]⟩
      zero_mem' := ⟨0, A.zero_mem, fun i => by rw [Pi.zero_apply, map_zero, h0]⟩
      smul_mem' := by
        rintro c v ⟨G, hG, hv⟩
        exact ⟨c • G, A.smul_mem c hG, fun i => by rw [Pi.smul_apply, smul_eq_mul, map_mul, hv, hsmul]⟩ }
  have hS : ∀ c : Fin M → O, (∃ i, IsUnit (c i)) → ∃ s ∈ S, (∑ i, c i * s i) ∣ π ^ D := by
    intro c hc
    obtain ⟨G, hG, a, b, hab, hb⟩ := hprim c hc
    choose v hv using fun i => hint i G hG
    refine ⟨v, ⟨G, hG, hv⟩, ?_⟩
    have hsum : ∑ i, c i * v i = a := hinj (by rw [← hab, map_sum]; simp only [map_mul, hv])
    exact ⟨b, by rw [hsum, hb]⟩
  have hmem : ∀ k : Fin M, π ^ D • Pi.single k (1 : O) ∈ S := fun k => smith_mem S (π ^ D) hS _
  choose G hGA hG using hmem
  have hsumφ : ∀ i (s : Finset (Fin M)) (f : Fin M → X), φ i (∑ k ∈ s, f k) = ∑ k ∈ s, φ i (f k) :=
    fun i s f => map_sum (AddMonoidHom.mk' (φ i) (hadd i)) f s
  let u : (Fin M → O) →ₗ[O] A :=
    { toFun := fun x => ∑ k, x k • (⟨G k, hGA k⟩ : A)
      map_add' := fun x y => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have key : ∀ x i, φ i (u x : X) = algebraMap O Kf (π ^ D * x i) := by
    intro x i
    have hu : (u x : X) = ∑ k, x k • G k := by simp [u]
    rw [hu, hsumφ]

    simp_rw [hsmul, ← hG, ← map_mul, ← map_sum]
    congr 1
    simp [Pi.single_apply, mul_comm]
  refine ⟨u, 1, fun x k => ?_⟩
  simp [key, Matrix.one_apply]

section Be

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

theorem be_add_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0)
    (G G' : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (G + G') = be p r lam0 F G + be p r lam0 F G' := by
  simp only [be, LinearMap.add_apply]

theorem be_smul_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) (c : O)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (c • G) = algebraMap O Kf c * be p r lam0 F G := by
  simp only [be, LinearMap.smul_apply, Algebra.smul_def]

theorem be_smulK_right (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F : Vsp Kf lam0) (c : Kf)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 F (c • G) = c * be p r lam0 F G := by
  simp only [be, LinearMap.smul_apply, smul_eq_mul]

theorem be_sum_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) {n : ℕ} (c : Fin n → O) (F : Fin n → Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) :
    be p r lam0 (∑ i, c i • F i) G = ∑ i, algebraMap O Kf (c i) * be p r lam0 (F i) G := by

  simp only [be, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul Kf (c i) (F i), smul_smul, mul_comm, ← smul_smul, map_smul, smul_eq_mul]

end Be

theorem s7 : S7 := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS hBP m r lam0 t D κ cStar L hdom hc hsrc
  classical
  have _ := hS.frac_O
  obtain ⟨E, nE, F, hE, hFsrc, hFoth, hprim, hcard⟩ := hsrc
  have hRe : ∀ e ∈ E, ∀ i, F e i ∈ Re p ι σ w r lam0 e := by
    intro e he i
    have h := (Submodule.mem_inf.mp (hFsrc e he i)).2
    rw [Submodule.mem_iInf] at h
    exact (Submodule.mem_iInf _).mp (h e) ⟨(hE e he).1, rfl⟩
  let T := Σ e : E, Fin (nE e.1)
  let eqv : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, fun k => (eqv k).1.1, fun k => F (eqv k).1.1 (eqv k).2,
    fun k => hE _ (eqv k).1.2, fun k => hFsrc _ (eqv k).1.2 _,
    fun k e' he' hs' hne => hFoth _ (eqv k).1.2 _ e' he' hs' hne, Fintype.card T, ?_, ?_⟩
  · have hT : Fintype.card T = ∑ e ∈ E, nE e := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort E nE
    rw [hT]
    exact hcard
  refine goodRank_of_prim (IsFractionRing.injective O Kf) (p : O) _ _ D
    (fun k G G' => be_add_right p r lam0 _ G G') (fun k c G => be_smul_right p r lam0 _ c G) ?_ ?_
  · intro k G hG
    have he := hE _ (eqv k).1.2
    have hG' : G ∈ Re' p ι σ w r lam0 (eqv k).1.1 := by
      have h := (Submodule.mem_inf.mp hG).2
      rw [Submodule.mem_iInf] at h
      exact (Submodule.mem_iInf _).mp (h _) he
    exact ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom _ he.1).1 G).mp hG' _ (hRe _ (eqv k).1.2 _)
  · rintro c ⟨k0, hk0⟩
    obtain ⟨⟨e0, i0⟩, hx⟩ : ∃ x, eqv k0 = x := ⟨_, rfl⟩
    have hk0' : IsUnit (c (eqv.symm ⟨e0, i0⟩)) := by
      rw [← hx, Equiv.symm_apply_apply]
      exact hk0
    obtain ⟨G, hGN, hval, hGoth⟩ := hprim e0.1 e0.2 (fun i => c (eqv.symm ⟨e0, i⟩)) ⟨i0, hk0'⟩
    obtain ⟨a, b, hva, hab⟩ := hval
    refine ⟨G, hGN, ?_⟩
    have hterm : ∀ e : E, ∀ i : Fin (nE e.1), e ≠ e0 →
        ∃ z : O, be p r lam0 (F e.1 i) G = algebraMap O Kf ((p : O) ^ (D + 1) * z) := by
      intro e i hne
      have he := hE e.1 e.2
      obtain ⟨G₀, hG₀, hGeq⟩ := Submodule.mem_map.mp (hGoth e.1 e.2 (fun h => hne (Subtype.ext h)))
      obtain ⟨y, hy⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom _ he.1).1 G₀).mp hG₀ _ (hRe _ e.2 i)
      refine ⟨w ^ (cStar - 2 * (D + 1)) * y, ?_⟩
      rw [← hGeq, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, be_smulK_right, ← hy, zpow_natCast,
        ← map_pow, ← map_mul, ← hS.w_sq, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 3
      omega
    have hsplit : ∑ k, algebraMap O Kf (c k) * be p r lam0 (F (eqv k).1.1 (eqv k).2) G =
        be p r lam0 (∑ i, c (eqv.symm ⟨e0, i⟩) • F e0.1 i) G +
          ∑ e ∈ Finset.univ.erase e0, ∑ i, algebraMap O Kf (c (eqv.symm ⟨e, i⟩)) * be p r lam0 (F e.1 i) G := by
      have h1 : ∑ k, algebraMap O Kf (c k) * be p r lam0 (F (eqv k).1.1 (eqv k).2) G =
          ∑ x : T, algebraMap O Kf (c (eqv.symm x)) * be p r lam0 (F x.1.1 x.2) G :=
        Fintype.sum_equiv eqv _ _ (fun k => by rw [Equiv.symm_apply_apply])
      rw [h1, Fintype.sum_sigma, be_sum_left, ← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
    have hrest : ∃ z : O, (∑ e ∈ Finset.univ.erase e0, ∑ i,
        algebraMap O Kf (c (eqv.symm ⟨e, i⟩)) * be p r lam0 (F e.1 i) G) = algebraMap O Kf ((p : O) ^ (D + 1) * z) := by
      refine Finset.sum_induction _ (fun x => ∃ z : O, x = algebraMap O Kf ((p : O) ^ (D + 1) * z))
        (fun x y ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => ⟨z₁ + z₂, by rw [h₁, h₂, mul_add, map_add (f := _)]⟩) ⟨0, by simp⟩ ?_
      intro e he
      refine Finset.sum_induction _ (fun x => ∃ z : O, x = algebraMap O Kf ((p : O) ^ (D + 1) * z))
        (fun x y ⟨z₁, h₁⟩ ⟨z₂, h₂⟩ => ⟨z₁ + z₂, by rw [h₁, h₂, mul_add, map_add (f := _)]⟩) ⟨0, by simp⟩ ?_
      intro i _
      obtain ⟨z, hz⟩ := hterm e i (Finset.ne_of_mem_erase he)
      exact ⟨c (eqv.symm ⟨e, i⟩) * z, by rw [hz, ← map_mul]; congr 1; ring⟩
    obtain ⟨z, hz⟩ := hrest
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D a z ⟨b, hab.symm⟩
    exact ⟨a + (p : O) ^ (D + 1) * z, b', by rw [hsplit, hva, hz, map_add (f := _)], hb'.symm⟩

end Formalism.MainNotions.Pf14
end
end
