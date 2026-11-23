module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Mathlib.LinearAlgebra.Matrix.Swap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle094
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle020
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.NonDominant

open AlgebraicGeometry CategoryTheory NumberField Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem poly_eq_zero (P Q : ℂ[X]) (d : ℕ) (hd : 0 < d) (ε : ℂ)
    (h : ∀ c : ℂ, c ≠ 0 → c ^ d * P.eval c = ε * Q.eval c⁻¹) : P = 0 := by
  have key : X ^ (Q.natDegree + d) * P = C ε * Q.reverse := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (((Set.finite_singleton (0 : ℂ)).infinite_compl).mono fun c hc => ?_)
    have hc : c ≠ 0 := hc
    letI := invertibleOfNonzero (inv_ne_zero hc)
    have h1 := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) c⁻¹ Q
    rw [invOf_eq_inv, inv_inv] at h1
    have h2 : Q.reverse.eval c * c⁻¹ ^ Q.natDegree = Q.eval c⁻¹ := h1
    show eval c _ = eval c _
    rw [eval_mul, eval_mul, eval_pow, eval_X, eval_C, pow_add, mul_assoc, h c hc, ← h2, inv_pow]
    field_simp
  by_contra hP
  have h1 := congrArg natDegree key
  rw [natDegree_X_pow_mul _ hP] at h1
  have h2 := (natDegree_C_mul_le ε Q.reverse).trans (reverse_natDegree_le Q)
  omega

theorem transvection_eq {n : ℕ} {i j : Fin n} (hij : i < j) (c : ℂ) (hc : c ≠ 0) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, (∀ k m, k < m → B k m = 0) ∧
      (∀ k, B k k = if k = i then c else if k = j then -c⁻¹ else 1) ∧
      B * (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j) = Matrix.transvection i j c := by
  have hne : i ≠ j := hij.ne
  refine ⟨Matrix.diagonal (fun k => if k = i then c else if k = j then -c⁻¹ else 1) + Matrix.single j i 1,
    fun k m hkm => ?_, fun k => ?_, ?_⟩
  · rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hkm.ne, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.2 hkm.le)
  · rw [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.single_apply_of_ne, add_zero]
    rintro ⟨rfl, h⟩
    exact hne h
  · ext k m
    have hT : ∀ (s : ℂ) a b, Matrix.transvection i j s a b = (if a = b then 1 else 0) + if i = a ∧ j = b then s else 0 :=
      fun s a b => by simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
    have hW : ∀ a b, (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j) a b =
        Matrix.transvection i j c⁻¹ a (Equiv.swap i j b) := fun a b => by
      by_cases h1 : b = i
      · subst h1; rw [Matrix.mul_swap_apply_left, Equiv.swap_apply_left]
      by_cases h2 : b = j
      · subst h2; rw [Matrix.mul_swap_apply_right, Equiv.swap_apply_right]
      · rw [Matrix.mul_swap_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
    rw [Matrix.add_mul, Matrix.add_apply, Matrix.diagonal_mul]
    have hS : (Matrix.single j i (1 : ℂ) * (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j)) k m =
        if k = j then (Matrix.transvection i j c⁻¹ * Matrix.swap ℂ i j) i m else 0 := by
      split_ifs with h
      · subst h; rw [Matrix.single_mul_apply_same, one_mul]
      · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
    rw [hS, hW, hW, hT, hT, hT, Equiv.swap_apply_def]
    by_cases h1 : k = i <;> by_cases h2 : k = j <;> by_cases h3 : m = i <;> by_cases h4 : m = j <;>
      simp_all [eq_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_weight {S : Type} [CommRing S] [Algebra c.F S] [IsReduced S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} (h : FrBor t y y') :
    evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hall : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  exact wtAll_of_borChart (borChartF_of_cover (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
    (ex Dw a n) hf.1 hf.2 S t y y' (hall S y) (hall S y') h

theorem evR_map {S T : Type} [CommRing S] [Algebra c.F S] [IsReduced S] [CommRing T] [Algebra c.F T]
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (φ : S →ₐ[c.F] T) {y : FrPt Xo c S}
    {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hy := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c S y
  have hW := evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have h1 := frMap_trans _ _ _ _ φ _ _ _ hy.choose_spec.choose_spec.choose_spec h
  have hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨_, _, _, h1⟩
  unfold evR evalAt
  rw [dite_eq_left hz, dite_eq_left hy]
  exact hW f hf.1 T _ _ _ _ _ _ z hz.choose_spec.choose_spec.choose_spec h1

variable {σ : c.F →+* ℂ}

instance (σ : c.F →+* ℂ) : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)

theorem exists_poly {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (y : FrPt Xo c (CAt σ))
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)[X]) (hG : ∀ τ, IsUnit (G τ).det) :
    ∃ P : (CAt σ)[X], ∀ (s : CAt σ) (y' : FrPt Xo c (CAt σ)),
      FrChg (fun τ => (G τ).map (eval s)) 1 y y' → evR Xo c f y' = P.eval s := by
  let π : CAt σ →ₐ[c.F] (CAt σ)[X] := IsScalarTower.toAlgHom _ _ _
  obtain ⟨y₁, h₁⟩ := FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c _ _ π y
  obtain ⟨z, hz, -⟩ := existsUnique_frChg E H Dw l Xo c _ y₁ G 1 hG
  refine ⟨evR Xo c f z, fun s y' hy' => ?_⟩
  let ev : (CAt σ)[X] →ₐ[c.F] CAt σ := (aeval s).restrictScalars c.F
  have hev : ∀ p, ev p = p.eval s := fun p => coe_aeval_eq_eval s ▸ rfl
  obtain ⟨y₂, h₂⟩ := FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c _ _ ev y₁
  have h₃ := frMap_trans _ _ _ π ev _ _ _ h₁ h₂
  have e : ev.comp π = AlgHom.id _ _ := AlgHom.ext fun x => by
    rw [AlgHom.comp_apply, hev]; exact eval_C
  rw [e] at h₃
  obtain rfl : y₂ = y := (frMap_unique_refl_iff E H Dw l Xo c _ _ _ y).1 _ _ h₃ (frMapUniq_refl y)
  rw [← hev]
  refine evR_map hf ev ((ChgBC.frChg_baseChange E H Dw l Xo c _ _ ev y₁ z y₂ y' G _ hz h₂).2 ?_)
  rw [Units.val_one, map_one, show (ev : (CAt σ)[X] → CAt σ) = eval s from funext hev]
  exact hy'

end GlobalTheory.NonDominant
end
end

section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

theorem thetaFrame_det_mul_sq_invariant_uncond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((U.Di i).La →+ (Fin g → ℂ))) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.Di i).La) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ), (∀ b ∈ B, IsPeriod (U.Di i) ty (P b)) → (∀ a a', (U.Di i).EF (bas a) (bas a') = -omegaStd a a') → (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → (∀ b ∈ B, (∀ k, h b *ᵥ P b (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h b *ᵥ P b (bas (Pi.single (Sum.inr k) 1)) = τ b *ᵥ Pi.single k 1)) → (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ (U.ex i (P bz.1) bz.2).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) → (∀ j b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, z) ≠ 0) → (∀ j j' b z, b ∈ B → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') → fr j (b, z) = valAt' (U.ex i (P b) z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' (b, z)) → (∀ j b, b ∈ B → ⊤ ≤ (U.ex i (P b) 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j (b, 0) = valAt' (U.u i (P b)) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) → (∀ b ∈ B, ∃ s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom (U.u i (P b))), x ≫ pullback.fst _ _ = (U.ex i (P b) z).left → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom (U.u i (P b)))).U (fun _ => j)) (s.f (fun _ => j)) = thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) → ∀ b ∈ B, ∀ b' ∈ B, ∀ (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P b' (gam a) = h₀ *ᵥ P b a) → ∀ j z, ⊤ ≤ (U.ex i (P b) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → (h b).det * (thetaChar (τ b) c₁ c₂ (h b *ᵥ z) * fr j (b, z)) ^ 2 = (h b').det * h₀.det * (thetaChar (τ b') c₁ c₂ (h b' *ᵥ (h₀ *ᵥ z)) * fr j (b', h₀ *ᵥ z)) ^ 2 :=
  thetaFrame_det_mul_sq_invariant latMinkowski abelianSchemeLaws_all.2.secTwist
    theta_sq_transform_level_eight

end GlobalTheory
end
end
