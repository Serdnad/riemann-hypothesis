module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodGeneratorsAgreeOverAlgClosedSubfield
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

noncomputable section

namespace GlobalTheory.Mum.TensPol

theorem psi_pos_tendsto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Q.IsPos (maximalIdeal R) → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hψ hW hQ
  obtain ⟨hN, hI, -, -⟩ := hR
  have hk0 : ∀ a b, ∃ k, Q.TauCoord a b k ∧
      (a = b → a ≠ 0 → ∃ s ∈ maximalIdeal R, (k : FractionRing R) = algebraMap R _ s) := by
    intro a b
    by_cases h : a = b ∧ a ≠ 0
    · obtain ⟨rfl, ha⟩ := h
      obtain ⟨s, hs, k, hk, hc⟩ := hQ a ha
      exact ⟨k, hc, fun _ _ => ⟨s, hs, hk⟩⟩
    · obtain ⟨k, hk⟩ := GlobalTheory.T.exists_periodScalarCoordinate_polarisedData_local R Q a b
      exact ⟨k, hk, fun e ne => (h ⟨e, ne⟩).elim⟩
  choose k hk hkp using hk0
  obtain ⟨hs, ha⟩ := GlobalTheory.T.periodScalarCoordinates_symm_bimult_up_to_units R Q k hk
  obtain ⟨ga', a', h'⟩ := GlobalTheory.exists_psiScal R D'
  obtain ⟨hp, ht⟩ := GlobalTheory.T.tensorData_scalars_mem_maximalIdeal_tendsto_zero R Q.X k hs ha (fun y hy => hkp y y rfl hy) W hW (fun z => a' (xe.symm z))
    (fun z => by simpa only [AddEquiv.apply_symm_apply] using GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods R Q D' W pr xe w hψ k hk ga' a' h' (xe.symm z))
  refine ⟨fun χ hχ => ?_, fun n => ((ht n).preimage xe.injective.injOn).subset fun χ hχ hm => hχ ?_⟩
  · obtain ⟨s, hs, e⟩ := hp (xe χ) (fun h0 => hχ (xe.map_eq_zero_iff.1 h0))
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩
  · obtain ⟨s, hs, e⟩ := hm
    rw [AddEquiv.symm_apply_apply] at e
    exact (GlobalTheory.PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩

end GlobalTheory.Mum.TensPol
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitExpansion_descends_from_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  first | exact @GlobalTheory.Mum.TraitDescent.exp_of_values | exact GlobalTheory.Mum.TraitDescent.exp_of_values | (intros; apply GlobalTheory.Mum.TraitDescent.exp_of_values <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀), ∃ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) ∧ ρ₂.i₀ = D.X.ρ.i₀ ∧ spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ ∧ R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) ∧ ∃ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ ∧ IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ ∧ LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) ∧ (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) ∧ ∃ y₂ : R₂ →+* PadicAlgCl p, (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) ∧ (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) ∧ ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.UPoinc.ULiftW.transport | exact GlobalTheory.UPoinc.ULiftW.transport | (intros; apply GlobalTheory.UPoinc.ULiftW.transport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_equivariant_bijection_larger_closed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  first | exact @GlobalTheory.Mum.UpExt.exists_eqv_ext | exact GlobalTheory.Mum.UpExt.exists_eqv_ext | (intros; apply GlobalTheory.Mum.UpExt.exists_eqv_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periodGenerators_agree_over_algClosedSubfield : ∀ (R : Type) [CommRing R] [IsDomain R]
    (Q : DegPre R) (τ₀ : Gens Q) (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) →
    ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
      (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
      (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)),
      IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' Q.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ →
      w.IsGen →
      (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) →
      ∀ (a b : Q.X) (τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])),
        τ₁.IsGen → ∃ x : k₀ˣ, ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val (τ₀ a b) (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) * val τ₁ (spMap k₀.subtype) z J₀ := by
  first | exact @GlobalTheory.UCanon.BaseDescent.main | exact GlobalTheory.UCanon.BaseDescent.main | (intros; apply GlobalTheory.UCanon.BaseDescent.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.Poinc.FibLat

namespace GlobalTheory.UPoinc.GFib

theorem TT_le_HH_of_uIsLab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} (X : USetup C) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy)
    (hker : yy.ker = X.S.HH X.M z) : X.S.TT X.M z ≤ X.S.HH X.M z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hlab, -⟩ := h
  have hk : lb.yy.ker ≤ yy.ker := fun a ha => by
    have h0 : lb.yy a = QuotientAddGroup.mk 0 := by rw [AddMonoidHom.mem_ker.1 ha]; rfl
    have := hlab a 0 h0
    rw [map_zero] at this
    exact AddMonoidHom.mem_ker.2 this
  intro t ht
  rw [← hker]
  refine hk ?_
  have h1 : t ∈ (X.S.rechart c₀ hc R' fg frac hth hev).perp lb.yy.ker := fun h hh => ht h (hker ▸ hk hh)
  have h2 := lb.isoFree.1 h1
  rwa [ThetaSys.perp_perp] at h2

end GlobalTheory.UPoinc.GFib

theorem GlobalTheory.UPoinc.GFib.labelled_lattices_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p _ z hz ct ct' y y' hy hy' yy yy' hl hl'
  have hker := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct yy hl.uIsLab
  have hker' := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct' yy' hl'.uIsLab
  have hTH := GlobalTheory.UPoinc.GFib.TT_le_HH_of_uIsLab X ct yy hl.uIsLab hker.2
  obtain ⟨f, gγ, hf, hg⟩ := GlobalTheory.T.unitaryEndomorphisms_torsion_extend_semiAbelian E H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO hE hpt z hTH
  have hL : 0 < X.S.r * X.S.N := Nat.mul_pos (by have := X.S.r_pos; omega) (by have := X.S.N_ge; omega)
  have hprim : IsPrimitiveRoot (X.S.ζ ^ (X.S.r * X.S.N)) (X.S.r * X.S.N) :=
    X.S.prim.pow (by positivity) (by ring)
  let ζ : X.o₁ˣ := (hprim.isUnit hL.ne').unit
  have hζ : IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) := hprim
  obtain ⟨s, σ, hs, hσ, hc⟩ :=
    GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre E H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p z f gγ hf hg ζ hζ
  obtain ⟨c, hc1, hc2⟩ := hc ct y hy yy hl
  obtain ⟨c', hc1', hc2'⟩ := hc ct' y' hy' yy' hl'
  have hx : q.base (y (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy, ct.cen]
  have hx' : q.base (y' (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy', ct'.cen]

  have hrk : ∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt FinalForm.G w r₀ := by
    obtain ⟨r₀, -, ⟨e₀⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE (y (cPt p))
    refine ⟨r₀, fun w hw => ?_⟩
    obtain ⟨r, hr, ⟨e⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE w
    have hT : X.S.TT Y w = X.S.TT Y (y (cPt p)) := by
      simp only [ThetaSys.TT]
      rw [GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv w,
        GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv (y (cPt p))]
      simp only [hw, hx]
    have e₁ : (Fin r → ZMod (X.S.r * X.S.N)) ≃ (Fin r₀ → ZMod (X.S.r * X.S.N)) :=
      (e.symm.toEquiv.trans (by rw [hT])).trans
        e₀.toEquiv
    haveI : NeZero (X.S.r * X.S.N) := ⟨hL.ne'⟩
    have hcard := Fintype.card_congr e₁
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have h2 : 2 ≤ X.S.r * X.S.N := by
      have := X.S.r_pos; have := X.S.N_ge; nlinarith
    rwa [Nat.pow_right_injective h2 hcard] at hr
  have hmove := GlobalTheory.T.characterLatticeAtFibre_const_preconnected X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi _ q z hz hrk (𝓞 E) _ f (fun a => (hf a).1) gγ ζ
    (X.S.r * X.S.N) hL (Units.ext (by simpa using hζ.pow_eq_one)) X.S.unit (fun t => (hg t).1)
    (fun t w hw => (hg t).2.2 w hw) ct.T.P.D.toPre.X _ c _ _ hx hx' hc1
  haveI : IsDomain X.o₁ := (inferInstance : GlobalTheory.ZH.ArithBase X.o₁ X.Ω₁).ded.toIsDomain
  obtain ⟨θ, hθm, hθc⟩ := GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi (𝓞 E) _ f gγ ζ (X.S.r * X.S.N) hL hζ
    X.S.unit ct.T.P.D.toPre.X ct'.T.P.D.toPre.X _ c _ c' _ hmove hc1'
  refine ⟨θ, fun a v hv => ?_, fun a v => ?_⟩
  · obtain ⟨a', ha'⟩ := hker'.1 (QuotientAddGroup.mk (θ v))
    have hd : a' - a ∈ X.S.HH X.M z := by
      rw [← ThetaSys.perp_TT]
      refine ThetaSys.mem_perp'.2 fun t ht => ?_
      have e1 := hc2' a' (θ v) ⟨t, ht⟩ ha'
      rw [hθc, hc2 a v ⟨t, ht⟩ hv] at e1
      have e2 := hs.mul_left_cancel e1
      rw [sub_eq_add_neg, eStd_add_right, eStd_neg_right, ← e2]
      exact add_neg_cancel _
    rw [← hker'.2, AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hd
    rw [← hd, ha']
  · obtain ⟨b, rfl⟩ := hσ a
    exact hθm b v
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumBC


open GlobalTheory.HalfBC GlobalTheory.PullLinear GlobalTheory.FactorPull in

theorem refine_factor_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (D' : DegData R' (maximalIdeal R')) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal R') D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (inc : G₁ ⟶ G') (pr : G' ⟶ G₁) (π : G₁.left ⟶ G.left) (π₂ : (G2 G₁).left ⟶ (G2 G).left), IsSemiAbelian G' ∧ U'.toUnifPre.OLinear F.O F.o oA oG ∧ IsSemiAbelian G₁ ∧ IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 G₁ ∧ pr ≫ inc = oG.act F.e ∧ IsGrpPullback G₁ G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso ((abelian₂ G' U'.LG.L).pull (lift (fst G₁ G₁ ≫ inc) (snd G₁ G₁ ≫ inc ≫ oG.act F.f) : G2 G₁ ⟶ G2 G').left) (P.pull π₂) := by
  intro R _ _ _ hCN Q G _ _ P hG hC R' _ _ _ ρ hCN' hρ hfin D ε hRef
  obtain ⟨hPL, D', F, A', G', _, _, U', oA, oG, inc, pr, hG', hlin, mi, mp, hip, hpi, hP⟩ := hC
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  have hR' := admissibleBase_of_completeNormalLocalCharZero hCN'
  have hloc : IsLocalHom ρ := by
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ρ
      (RingHom.IsIntegral.of_finite hfin) (maximalIdeal R')
    have hc : (maximalIdeal R').comap ρ = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal R').comap ρ := hc.symm ▸ (mem_maximalIdeal a).2 hna
    exact (mem_maximalIdeal _).1 this ha
  obtain ⟨D₁', hD', A₁', U₁', hU, oG₁, oA₁, h₁, h₂⟩ :=
    unif_pull hR hR' ρ hρ (map_maximalIdeal_le ρ) hG' U' F.O F.o oA oG hlin
  obtain ⟨m, o₁, hx, ho⟩ := degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R R' ρ _ _ hD' F.O F.o
  have lin := oLinear_pull R R' _ _ ρ D' D₁' hD' A' A₁' G' _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) U' U₁' hU
    F.O F.o o₁ oA oA₁ oG oG₁ hlin h₁ h₂ hx ho
  obtain ⟨inc', pr', xi, xp, w, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁⟩ :=
    GlobalTheory.T.polarisedIdempotentFactor_pullback_refinement ρ hρ Q D'.toPre F D.toPre ε hRef D₁'.toPre hD' o₁ hx fun a => act_proj _ hD'.e.hom (ho a)
  let F₁ : Factor D.toPre D₁'.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := b₁₀, tau := b₁₁ }
  have alg : F₁.Alg := F.alg
  have ha : ∀ a, oG₁.act a = (Over.pullback (specOf ρ)).map (oG.act a) := fun a =>
    (Category.comp_id _).symm.trans ((h₁ a).trans (Category.id_comp _))
  have gG := isGrpPullback_pullback G (specOf ρ)
  have gG' := (isGrpPullback_pullback G' (specOf ρ)).congr rfl (Category.id_comp _).symm
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁', F₁, alg, A₁', _, _, _, U₁', oA₁, oG₁, (Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance,
    (Over.pullback (specOf ρ)).map inc, (Over.pullback (specOf ρ)).map pr, _, sqOf gG,
    IsSemiAbelian.pullback _ G' hG', lin, IsSemiAbelian.pullback _ G hG, inferInstance, inferInstance, ?_, ?_, gG,
    isSquare_sqOf gG, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, hpi, ha]
  · have hm := lift_sq gG gG' (u := inc) (v := inc ≫ oG.act F.f) (u₁ := (Over.pullback (specOf ρ)).map inc)
      (v₁ := (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f)
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (map_left_fst _ _))
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (by
        rw [ha, ← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _))
    have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
    have H1 : LBIso ((abelian₂ ((Over.pullback (specOf ρ)).obj G') U₁'.LG.L).pull
        (lift (fst _ _ ≫ (Over.pullback (specOf ρ)).map inc) (snd _ _ ≫ (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f) :
          G2 ((Over.pullback (specOf ρ)).obj G) ⟶ G2 ((Over.pullback (specOf ρ)).obj G')).left)
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullLinComb (abelian₂ G' U'.LG.L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)
    have H2 : LBIso (P.pull (sqOf gG))
        (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull (sqOf gG)) :=
      hP.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl)
    exact LBIso.trans (pull_isLB (DVR.linComb_isLB _ U₁'.LG.isLB _ _) _)
      (pull_isLB (pull_isLB (DVR.linComb_isLB _ U'.LG.isLB _ _) _) _) (pull_isLB hPL _) H1 (LBIso.symm H2)

end GlobalTheory.MumBC

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lattice_iso_eq_of_tautPts : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  intro o W _ _ _ T ψ m N n ε hn hcone hdef V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂
    hs₁ hu₁ hs₂ hu₂ hM hpts
  let ga : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e₁.symm.trans φ).trans e₂).toIntLinearEquiv
  have hga : ∀ a, ga a = e₂ (φ (e₁.symm a)) := fun _ => rfl

  have hcong : ∀ a, GlobalTheory.Poinc.CongMod n (ga a) a := by
    intro a
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpts a
    have h : e₂ p₂.y = e₂ (φ p₁.y) + n • e₂ z := by rw [hz, map_add (f := _), hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(e₂ z), ?_⟩
    rw [smul_neg, eq_add_neg_iff_add_eq, hga]
    exact h.symm

  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε n V D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F hτ₁ hτ₂ hF₁ hF₂ hM
  have hab : ∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) =
      algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i a b) := by
    intro a b
    obtain ⟨u, hu⟩ := hpu (e₁.symm a) (e₁.symm b)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hu
    exact ⟨u, hu⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r m N n (by omega) ε s₁ s₂ ga hs₁ hu₁ hs₂ hu₂ hab
  have hS := GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint ψ (Fin T.r → ℤ) m m (fun k => ε (.inl k)) (fun k => pull ga.toLinearMap (ε (.inl k))) hcone
    (hcone.pull_equiv ga) c₁ c₂ hc₁ hc₂ hsum

  have he : ∀ x y, (∑ k, ε (.inl k)) (ga x) (ga y) = (∑ k, ε (.inl k)) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, ε (.inl k)) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hcone.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  have hrefl := GlobalTheory.Poinc.eq_refl_of_isometry_congMod (Fin T.r → ℤ) (∑ k, ε (.inl k)) hpos ga he n hn hcong
  intro y
  have h := DFunLike.congr_fun hrefl (e₁ y)
  rw [hga, AddEquiv.symm_apply_apply, LinearEquiv.refl_apply] at h
  exact h

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.TInj.lamVal_axes_one | exact GlobalTheory.TInj.lamVal_axes_one | (intros; apply GlobalTheory.TInj.lamVal_axes_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.twistedAdicSum_terms_of_fractionField_sum : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  first | exact @GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF | exact GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF | (intros; apply GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_add_add_pull_sub {K : Type} [Field K] {A B : AbVar K} (d : Pic B.X.left)
    (hd : CechPic.pull (Hom.hom (-(𝟙 B))).left d = d) (f g : A ⟶ B) :
    CechPic.pull (f + g).hom.left d + CechPic.pull (f - g).hom.left d
      = (2 : ℤ) • CechPic.pull f.hom.left d + (2 : ℤ) • CechPic.pull g.hom.left d := by
  have hl := (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K B d A.X f.hom g.hom g.hom (-1)).2.2.2.2
  have hq := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd g (-1)).2
  rw [zpow_neg_one] at hl
  rw [neg_one_zsmul] at hq
  norm_num at hq
  have e1 : CechPic.pull (f + g).hom.left d
      = lam d f.hom g.hom + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [lam, add_hom]; abel
  have e2 : CechPic.pull (f - g).hom.left d
      = lam d f.hom (g.hom⁻¹) + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [sub_eq_add_neg, ← hq, lam, add_hom, neg_hom]; abel
  rw [e1, e2, hl]
  simp only [neg_one_smul, two_smul]
  abel

theorem exists_posDef_quadratic_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ,
    (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  intro K _ A B
  obtain ⟨d, hdA, hd⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨c, hc⟩ := GlobalTheory.AV.exists_isAmpleCls K A
  rcases hA : A.dim with _ | n
  · refine ⟨fun _ => 0, fun _ _ => by simp, fun _ => le_rfl, fun f _ => GlobalTheory.T.eq_zero_of_dim_eq_zero' K A B (Or.inl hA) f⟩
  · obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hA])
    refine ⟨fun f => inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left), ?_, ?_, ?_⟩
    · intro f g
      simp only [← hM]
      rw [← MultilinearMap.cons_add, pull_add_add_pull_sub d hd f g, MultilinearMap.cons_add,
        MultilinearMap.cons_smul, MultilinearMap.cons_smul]
      simp [two_mul]
    · intro f
      by_cases hf : f = 0
      · subst hf
        have h0 := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd (0 : A ⟶ B) 0).2
        rw [zero_smul] at h0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul] at h0
        show 0 ≤ inter A _
        rw [← hM, h0, M.map_coord_zero (0 : Fin (n + 1)) (by simp)]
      · exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).le
    · intro f hf0
      by_contra hf
      exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).ne' hf0

end GlobalTheory.AV.AbVar
end
