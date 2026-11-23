module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3222
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle412
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.val_extensionPoint_eq_image_of_val : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  first | exact @GlobalTheory.GSep.Tower.val_om_ext | exact GlobalTheory.GSep.Tower.val_om_ext | (intros; apply GlobalTheory.GSep.Tower.val_om_ext <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.val_galoisConjugate_extension_eq : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  exact @GlobalTheory.GSep.val_galois_conj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_stalk : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  first | exact @GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk | exact GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk | (intros; apply GlobalTheory.GSep.Tower.exists_point_integralClosure_stalk <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_trait_lift_to_semiAbelianModel : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  first | exact @GlobalTheory.GSep.TraitLift.exists_lift | exact GlobalTheory.GSep.TraitLift.exists_lift | (intros; apply GlobalTheory.GSep.TraitLift.exists_lift <;> assumption)
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
open GlobalTheory.UT.CoefBasic


theorem _root_.GlobalTheory.T.section_eq_of_values_at_label_torsion : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th th₂ : SecA 𝔪.A (FractionRing V) 1),
  (∀ a, (fr a).IsGen) → (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) →
  (∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → th₂ = th := by
  first | exact @GlobalTheory.GSep.GMem.sec_eq_of_valAt | exact GlobalTheory.GSep.GMem.sec_eq_of_valAt | (intros; apply GlobalTheory.GSep.GMem.sec_eq_of_valAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.thetaConstant_le_commonBound_monomial : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ))), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → ∀ c : WithZero (Multiplicative ℤ), (∀ b, ν (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) ≤ c) → ∀ a, ∃ w : Fin 8 → X, 𝔪.YY a w ∧ ν (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) ^ ((X₁.S.r * X₁.S.N) ^ 2) ≤ c ^ ((X₁.S.r * X₁.S.N) ^ 2) * ν (algebraMap V (FractionRing V) (mono W t δ w))) := by
  first | exact @GlobalTheory.Poinc.Sep.DivBound.theta_pow_le | exact GlobalTheory.Poinc.Sep.DivBound.theta_pow_le | (intros; apply GlobalTheory.Poinc.Sep.DivBound.theta_pow_le <;> assumption)
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


theorem _root_.GlobalTheory.T.twisted_sum_terms_eq_theta_constant_translate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → ∃ e : ℕ, SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) := by
  first | exact @GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate | exact GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate | (intros; apply GlobalTheory.Poinc.Sep.TwistTranslate.twistSum_translate <;> assumption)
end

section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  first | exact @GlobalTheory.Poinc.finite_types | exact GlobalTheory.Poinc.finite_types | (intros; apply GlobalTheory.Poinc.finite_types <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum


namespace GlobalTheory.RefSum.WFree

theorem conj_eq_neg {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) : (starRingEnd ℂ) z = -z ∧ z ≠ 0 :=
  _root_.GlobalTheory.ClosingLemmaFourth.main hd h

theorem two_mul_sum_mult {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) : 2 * ∑ τ : E →+* ℂ, Dw.mult τ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  have key : ∀ τ : E →+* ℂ, Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := fun τ => by
    have hs : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
      simpa using this
    obtain ⟨h1, h2⟩ := conj_eq_neg H.d_prime.pos hs
    have h3 : ComplexEmbedding.conjugate τ (H.rt : E) = -τ (H.rt : E) := h1
    unfold Datum.mult
    rw [h3]
    by_cases h : τ (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg fun e => h2 (by linear_combination (h - e) / 2)]
    · have : -τ (H.rt : E) = H.rt0 := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hs.trans H.sqrt_neg_disc_sq.symm) with e | e
        · exact absurd e h
        · rw [e, neg_neg]
      rw [if_neg h, if_pos this, add_comm]
  have hinv : Function.Involutive (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := fun τ => star_star τ
  have e := Equiv.sum_comp hinv.toPerm Dw.mult
  rw [two_mul]
  nth_rewrite 2 [← e]
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun τ _ => key τ).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Embeddings.card, smul_eq_mul]

theorem one_le_vAdd {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q ≠ 0)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 1 ≤ vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K (q : 𝓞 K)) < 1 := (w.valuation_lt_one_iff_mem (K := K) _).2 h
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hq)
  have := WithZero.log_lt_log h0 one_ne_zero |>.2 h1
  rw [WithZero.log_one] at this
  unfold vAdd
  omega

theorem notMem_of_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := fun h' => by
  have hc : IsCoprime ((p : ℕ) : 𝓞 K) ((q : ℕ) : 𝓞 K) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨a, b, e⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ h') (Ideal.mul_mem_left _ _ h)))

theorem different_vp_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : Level H) {q : ℕ} (hq : q.Prime) (h : q ∉ badPrimes H l) : different_vp E q = 0 := by
  have : ¬ q ∣ (discr E).natAbs := fun hd => h (Nat.mem_primeFactors.2 ⟨hq, (hd.mul_left _).mul_right _,
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) (Int.natAbs_ne_zero.2 (discr_ne_zero E)))
      (Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne')⟩)
  rw [different_vp, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd this]
  simp

theorem refExp_vp_le_of_laws {E : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : GlobalTheory.FlatCore.Laws U x) (hN : UnramPts Xo c (badPrimes H l))
    (hF : FlatExists U x) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (cst : ℝ) {q : ℕ} (hq : q.Prime) {N : ℝ}
    (hs : ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) = N) :
    refExp_vp U cst (wtOf Dw u 0) q ≤ refExp_vp U cst (wtOf Dw (u + parWt Dw w₀) m) q +
      (((if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0 : ℝ)) : EReal) := by
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread E H Dw l Xo c r U hL.unf x hL.xi hL.geo hL.pos hL.good hN
  have hz : ∀ Z : Comp Xo c, ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m),
      IntOff (badPrimes H l) z.lo ∧ ∀ w, z.hi w - z.lo w ≤
        m * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) := fun Z => by
    obtain ⟨t, ht1, ht2⟩ := ht Z
    obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat E H Dw l Xo c r U x _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
    exact GlobalTheory.CombTw.exists_twSec_comb E H Dw l Xo c r U hL.unf x _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  choose z hz1 hz2 using hz
  have key := GlobalTheory.T.baseLocusExponent_twistingSection_mul_le E H Dw l Xo c r U hL.unf x (wtOf Dw (u + parWt Dw w₀) m) _ (even_two_mul (m : ℤ)) cst
    (if q ∈ badPrimes H l then (m * N * (different_vp E q : ℝ) + 1) else 0) q hq z fun Z w hw => by
      have h1 := hz2 Z w
      simp only [fun τ => (GlobalTheory.DifferentGalois.ord_conjDifferent_and_sum E c.F (embF c τ) q w hq hw).1, ← Finset.sum_mul, hs] at h1
      split_ifs with hb
      · have h2 : (1 : ℝ) ≤ (vAdd w (q : c.F) : ℝ) := by exact_mod_cast one_le_vAdd w hq.ne_zero hw
        have h3 := Int.lt_floor_add_one ((z Z).lo w)
        linarith
      · obtain ⟨n, hn⟩ := hz1 Z w fun p hp =>
          notMem_of_ne w (Nat.prime_of_mem_primeFactors hp) hq (fun e => hb (e ▸ hp)) hw
        rw [different_vp_eq_zero l hq hb, hn] at h1
        rw [hn, Int.floor_intCast]
        simpa using h1
  rwa [add_sub_cancel] at key

end GlobalTheory.RefSum.WFree
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorTau

theorem lift_square {S S' : Scheme.{0}} {B C : Over S} {B₁ C₁ : Over S'} {β : B₁.left ⟶ B.left} {δ : C₁.left ⟶ C.left}
    {β₂ : (G2 B₁).left ⟶ (G2 B).left} {δ₂ : (G2 C₁).left ⟶ (G2 C).left} (hβ : IsSquare β β₂) (hδ : IsSquare δ δ₂)
    {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁} (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ δ₂ =
      β₂ ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, hδ.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc β₂,
      hβ.1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, hδ.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc β₂,
      hβ.2, Category.assoc]

theorem pair_square {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} {B₁ T : Over S'} {β : B₁.left ⟶ B.left}
    {β₂ : (G2 B₁).left ⟶ (G2 B).left} (hβ : IsSquare β β₂) {a b : 𝟙_ (Over S) ⟶ B} {a₁ b₁ : 𝟙_ (Over S') ⟶ B₁}
    (ha : a₁.left ≫ β = f ≫ a.left) (hb : b₁.left ≫ β = f ≫ b.left) :
    (lift (toUnit T ≫ a₁) (toUnit T ≫ b₁)).left ≫ β₂ = (T.hom ≫ f) ≫ (lift a b).left := by
  have hT : (toUnit T).left = T.hom := (Category.comp_id _).symm.trans (Over.w (toUnit T))
  apply pullback.hom_ext
  · show _ ≫ (fst B B).left = _ ≫ (fst B B).left
    rw [Category.assoc, hβ.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc, ha, hT, Category.assoc]
  · show _ ≫ (snd B B).left = _ ≫ (snd B B).left
    rw [Category.assoc, hβ.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc, hb, hT, Category.assoc]



theorem factor_tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  intro R V _ _ _ _ θ Q D₀ F D₁ hD _ o₁ hx ho Q' ex hQ
  obtain ⟨β, β₂, wP, gβ, sβ, hwP, hc, hτ⟩ := hQ
  refine ⟨β, gβ, hc, fun inc xi hi hxi hcx => ?_⟩
  letI := D₀.P.isAb.comm
  letI := D₁.P.isAb.comm
  obtain ⟨w₁₂, hw₁₂, v₁₂⟩ := GlobalTheory.T.mumfordBundleIso_comp_values_mul _ _ _ Q'.B Q.B D₀.P.A Q'.M.L Q.M.L D₀.P.L Q'.M.isLB Q.M.isLB D₀.P.isLB
    β₂ _ _ rfl F.w F.w_gen wP hwP
  obtain ⟨δ₂, w₀, sδ, hw₀, v₀⟩ := GlobalTheory.T.exists_periods_pulled_degeneration_data R V θ D₀ D₁ hD
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  obtain ⟨w, hw, vw⟩ := GlobalTheory.T.mumfordBundleIso_cancel_values_mul _ _ _ Q'.B D₁.P.A D₀.P.A Q'.M.L D₁.P.L D₀.P.L Q'.M.isLB D₁.P.isLB D₀.P.isLB
    _ δ₂ _ (lift_square sβ sδ hi hf) w₀ hw₀ w₁₂ hw₁₂
  refine ⟨w, hw, fun a b z J J' hJ hJ' => ?_⟩
  obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
  obtain ⟨JQ, hJQ⟩ := DegPull.exists_good' Q.M.isLB z
  obtain ⟨u, x, y, k, k', hu, hy, hk, hk', t₀, t₁⟩ := hτ a b
  have e₁ := t₁ z JQ J' hJQ hJ'
  have e₂ := GlobalTheory.T.idempotent_factor_periods_at_generating_point R V θ Q D₀ F hD.W hD.psiW hD.g hD.g_comm (ex a) (ex b) u x y k k' hu hy hk hk' t₀
    z J₀ JQ hJ₀ hJQ
  have e₃ := v₁₂ _ (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J' JQ J₀ hJ' hJQ hJ₀
  have e₄ := vw _ (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J' J J₀ hJ' hJ hJ₀
  have e₅ := v₀ (xi a) (F.f • xi b) z J₀ J hJ₀ hJ
  have hP := pair_square (T := TK V) sβ (hc a) (hc b)
  have hq : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫
      (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left =
      (lift (toUnit (TK V) ≫ D₁.c (xi a)) (toUnit (TK V) ≫ D₁.c (F.f • xi b))).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hcx, hcx]
    simp only [Category.assoc]
  rw [hP] at e₃
  rw [hq] at e₄
  rw [hx, hxi, hxi] at e₅
  rw [e₁, e₅, mul_left_comm, ← _root_.mul_assoc (lamVal w _ z J J'), ← e₄, e₃, _root_.mul_assoc]
  exact congrArg _ e₂

end GlobalTheory.FactorTau

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.connection_closedFibre_eq_derivation_identification : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) ∧ ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  first | exact @GlobalTheory.HeatConn.connK_eq_ident | exact GlobalTheory.HeatConn.connK_eq_ident | (intros; apply GlobalTheory.HeatConn.connK_eq_ident <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.CoverDec

theorem exists_cover_sqDec : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (L M : LB G.left), L.IsLB → M.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (π : G'.left ⟶ G.left), Function.Injective ρ ∧ ρ.Finite ∧ IsGrpPullback G' G (spMap ρ) π ∧ SqDec G' (L.pull π) (M.pull π) := by
  intro R _ _ _ _ hc G _ hG hAb L M hL hM hAL hAM hSL hSM
  have sL := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) L hL hSL
  have sM := GlobalTheory.T.symmetric_lineBundle_pullback_baseChange _ _ G (jK R) M hM hSM
  obtain ⟨K', _, _, _, hD⟩ := GlobalTheory.T.exists_squareDecomposition_finiteExtension_ampleBundle (FractionRing R) ((Over.pullback (jK R)).obj G) hAb _ _
    (pull_isLB hL _) (pull_isLB hM _) hAL hAM sL sM
  obtain ⟨R', _, _, _, _, _, ρ, τ, hinj, hfin, hcomp⟩ := GlobalTheory.T.exists_finite_normal_noetherian_cover_fractionFieldExt R hc K'
  obtain ⟨π₀, hP, hLL⟩ := GlobalTheory.T.genericFibre_baseChange_grpPullback_domains R R' ρ (τ.comp (algebraMap (FractionRing R) K')) hcomp G
  have hD' := GlobalTheory.SqDecTransport.transport (FractionRing R) (FractionRing R') K' (FractionRing R')
    (τ.comp (algebraMap (FractionRing R) K')) (algebraMap (FractionRing R) K') (RingHom.id _) τ rfl
    ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) π₀ hP _ _ _ _
    (pull_isLB hL _) (pull_isLB hM _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (hLL L hL) (hLL M hM) hD
  have h1 := GlobalTheory.T.squareDecomposition_of_baseChange_along_identity _ _ _ _ (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _) hD'
  have h2 := GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian R' ((Over.pullback (spMap ρ)).obj G) (IsSemiAbelian.pullback (spMap ρ) G hG) _ _
    (pull_isLB hL _) (pull_isLB hM _) h1
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    (Over.pullback (spMap ρ)).obj G, inferInstance, pullback.fst G.hom (spMap ρ), hinj, hfin,
    isGrpPullback_pullback G (spMap ρ), h2⟩

end GlobalTheory.CoverDec
end
end
