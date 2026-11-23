module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3394
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  first | (exact @GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (exact GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (intros; apply GlobalTheory.HTDeform.liftFil_isCompl_red_stable  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.semiabelian_uniformization_linear_action_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → EvenOn P₉ → IsMonHom gen₉.hom → LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  first | exact @GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits | exact GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits | (intros; apply GlobalTheory.Mum.TraitTwist.exists_bundle_data_at_traits <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_classicalTrait_system_at_closedPoint : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧ (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  first | exact @GlobalTheory.Poinc.PreSys.main | exact GlobalTheory.Poinc.PreSys.main | (intros; apply GlobalTheory.Poinc.PreSys.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O), ∃ (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG := by
  first | exact @GlobalTheory.Mum.exists_oLinear_of_oAct | exact GlobalTheory.Mum.exists_oLinear_of_oAct | (intros; apply GlobalTheory.Mum.exists_oLinear_of_oAct <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.galois_transport_torsion_labels_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.Poinc.galTransport | exact GlobalTheory.Poinc.galTransport | (intros; apply GlobalTheory.Poinc.galTransport <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_balanced_lattice_data_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ (2 * X₁.S.N)) (T.be (π (μ cl)) (π (μ cl))).toNat := by
  first | exact @GlobalTheory.UPoinc.ClosedPt.exists_lattice_data | exact GlobalTheory.UPoinc.ClosedPt.exists_lattice_data | (intros; apply GlobalTheory.UPoinc.ClosedPt.exists_lattice_data <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem isTautB_of_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → (∃ hm : C.m = m, ∀ i, C.s i = bdParam k m e (Fin.cast hm i)) → IsTautB C := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi k _ m e C hC hms
  obtain ⟨hm, hs⟩ := hms
  have hB : GlobalTheory.Mum.Base (ChartRing k m e) := GlobalTheory.ChartQF.base_chartRing C.toFam
  have hR : HasRigidCoords C := GlobalTheory.T.canonicalFamily_has_pointRigid_coordinates Xo c φ (ChartRing k m e) hB C hC
  obtain ⟨hft, hdim⟩ := GlobalTheory.T.canonicalChart_residueField_dimension Xo c φ C hC
  obtain ⟨N, s, ε, τ₀, h1, h2, h3, h4, -⟩ := id hR
  exact ⟨⟨hm, hs, GlobalTheory.T.openPart_classified_monomialBoundaryFamily Xo c φ _ hB C, GlobalTheory.T.canonicalFamily_localInjections_eq_same_point Xo c φ hpq hfan hnsi _ hB C hC,
    ⟨GlobalTheory.T.canonical_data_rigid_along_stratum Xo c φ _ hB C hC, GlobalTheory.T.isPointRigidBoundaryFamily_of_rigidCoordinates Xo c φ _ C hR, hft⟩, ⟨N, s, ε, τ₀, h1, h2, h3, h4⟩, hdim⟩, hR⟩

end GlobalTheory.UCanon
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DeepDiv

end GlobalTheory.Poinc.Sep.DeepDiv

open GlobalTheory.Poinc.Sep

theorem GlobalTheory.Poinc.Sep.DeepDiv.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ :=
  GlobalTheory.T.dividingLabel_persists_thetaSetupTower
end
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


theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_indep_of_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (t₁ : Y₁ → V₁) (δ₁ : I → Y₁ → Y₁) (𝔪₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : Y₁ → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (t₂ : Y₂ → V₂) (δ₂ : I → Y₂ → Y₂) (𝔪₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : Y₂ → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  first | exact @GlobalTheory.GSep.twistSum_indep | exact GlobalTheory.GSep.twistSum_indep | (intros; apply GlobalTheory.GSep.twistSum_indep <;> assumption)
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

namespace GlobalTheory.KBracket

theorem exists_der_ext {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ δS : Derivation ℤ S S, ∀ a, δS (algebraMap A S a) = algebraMap A S (δ a) := by
  let h : A →+* DualNumber S :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A S a) + TrivSqZeroExt.inr (algebraMap A S (δ a))
      map_one' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, Algebra.smul_def, mul_comm, add_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_add' := fun a b => by ext <;> simp [add_add_add_comm, -DualNumber.inr_eq_smul_eps] }
  have hu : ∀ m : M, IsUnit (h m) := fun m => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [h] using IsLocalization.map_units S m)
  let L : S →+* DualNumber S := IsLocalization.lift hu
  have hfst : ∀ x, (L x).fst = x := by
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp L = RingHom.id S := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
      simp [L, h, -DualNumber.inr_eq_smul_eps]
    exact fun x => congr($this x)
  let δS : Derivation ℤ S S := Derivation.mk'
    ((show S →+ S from
      { toFun := fun x => (L x).snd, map_zero' := by simp, map_add' := fun x y => by simp }).toIntLinearMap)
    (fun x y => by
      show (L (x * y)).snd = x • (L y).snd + y • (L x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
      simp [mul_comm])
  refine ⟨δS, fun a => ?_⟩
  show (L (algebraMap A S a)).snd = _
  simp [L, h, Algebra.smul_def, -DualNumber.inr_eq_smul_eps]

theorem exists_der_fun {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ f : S →+ S, (∀ x y, f (x * y) = x * f y + y * f x) ∧
      ∀ a, f (algebraMap A S a) = algebraMap A S (δ a) := by
  obtain ⟨δS, hδS⟩ := exists_der_ext M δ (S := S)
  exact ⟨δS.toLinearMap.toAddMonoidHom, fun x y => by simp [Derivation.leibniz, smul_eq_mul], hδS⟩

theorem exists_der_frac (Ω : Type) [CommRing Ω] [IsDomain Ω] (δ : Derivation ℤ Ω Ω) :
    ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω) := by
  obtain ⟨f, hf1, hf2⟩ := exists_der_fun (nonZeroDivisors Ω) δ (S := FractionRing Ω)
  have hf0 : f 1 = 0 := by
    have h11 := hf1 1 1
    rw [_root_.mul_one, _root_.one_mul] at h11
    linear_combination -h11
  have hfc : ∀ (c : ℤ) (y : FractionRing Ω), f ((c : FractionRing Ω) * y) = (c : FractionRing Ω) * f y := by
    intro c y
    have h2 : f (c : FractionRing Ω) = 0 := by
      rw [← zsmul_one, map_zsmul, hf0]
      simp
    rw [hf1, h2]
    simp
  refine ⟨{ toFun := f
            map_add' := f.map_add
            map_smul' := (fun c y => ?_)
            map_one_eq_zero' := hf0
            leibniz' := (fun x y => ?_) }, hf2⟩
  · simp only [RingHom.id_apply]
    rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul]
    exact hfc c y
  · exact hf1 x y

theorem isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
  letI := H.starRing
  have hsm : Smooth Y.H.hom := GlobalTheory.RayTan.smooth_H R _ _ _ Y
  have hint : IsIntegral Y.H.left := GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local R _ _ _ Y
  obtain ⟨i0, hi0⟩ : ∃ i0, ⊤ ≤ (η[Y.H]).left ⁻¹ᵁ h.W i0 := by
    have hm : (η[Y.H]).left (IsLocalRing.closedPoint R) ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i0, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨i0, (ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem ((η[Y.H]).left ⁻¹ᵁ h.W i0) hi).ge⟩
  obtain ⟨Ω, _, _, _, φ, x, δ, dΩ, hΩc, hx, hxW, hdΩ, hδφ, hδ, hd, hinj⟩ :=
    GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme R Y.H hsm hint n vH dd hdd ⇑D (h.W i0) (h.d i0) (h.lift i0) hi0
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : valR x ⊤ (Y.H.hom.appTop.hom (e.inv.hom r)) = φ r := by
      refine (GlobalTheory.ZH.EvCrd.valR_comp x Y.H.hom ⊤ (by simp) _).trans ?_
      rw [hx]
      exact GlobalTheory.ZH.EvCrd.valR_fn φ r
    have h2 := GlobalTheory.PrimScale.valR_const (η[Y.H]).left Y.H.hom (Over.w η[Y.H]) r
    have h3 := hinj ⊤ _ (by simp) (h1.trans hr)
    rw [h3] at h2
    rw [← h2]
    simp [valR]

  obtain ⟨x', hx', dd', hdd', hδ', hinj', hpt⟩ :=
    GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' Ω φ x δ hΩc hφ hx hδφ hδ
  obtain ⟨g, hg⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := Ω) t.PP.L t.PP.isLB (K := PUnit)
    (fun _ => x' ≫ 𝟙 t.G.left) (fun _ => 1)
  have hex : ∀ a, ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ a ω) :=
    fun a => exists_der_frac Ω (δ a)
  choose δL hδL using hex
  obtain ⟨dt, u', p, p', hdt, hact⟩ := GlobalTheory.T.commuting_heatOperators_act_on_values E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
    i0 Ω φ x x' δ hΩc hx hx' hδφ hδ hpt dΩ hxW hd g hg δL hδL
  obtain ⟨b, rfl⟩ := GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension E H R t P Y n vH v' hv'
  let D₀ : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤) := Derivation.mk'
    ((e.inv.hom.toAddMonoidHom.comp ((D : R →ₗ[ℤ] R).toAddMonoidHom.comp e.hom.hom.toAddMonoidHom)).toIntLinearMap)
    (fun a a' => by
      simp [Derivation.leibniz, smul_eq_mul])
  haveI := (isAffineOpen_top (Sp R)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  obtain ⟨DV, hDV⟩ := exists_der_ext (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) D₀ (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))))
  have hDV' : ∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (D r)) := fun r => by
    show DV (algebraMap _ _ (e.inv.hom r)) = algebraMap _ _ (e.inv.hom (D r))
    rw [hDV]
    congr 1
    simp [D₀]

  obtain ⟨Θ₁, hsym, hKS⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus E H R t P m tt gam hmon htt hab n b DV
  obtain ⟨iota, dt₂, u₂, p₂, p₂', hiota, hdt₂, hact₂⟩ := GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd'
    hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL Θ₁ DV hDV' hKS
  have heq := GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd' hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL
    (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) (iota.mapMatrix Θ₁) dt dt₂ u' u₂ p p' p₂ p₂'
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, h.symm])
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, hsym])
    (fun r => (hdt r).trans (hdt₂ r).symm) hact hact₂
  have hi : Function.Injective iota := by
    have key : ∀ y : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))), iota y = 0 → y = 0 := by
      intro y hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) y
      dsimp only at hy ⊢
      have h1 : iota (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) a) = 0 := by
        rw [← IsLocalization.mk'_spec (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) a s]
        erw [map_mul, hy, zero_mul]
      have h2 : (algebraMap Γ(Sp R, ⊤) _ a : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (e.hom.hom a)) := by
        rw [Iso.hom_inv_id_apply]
        rfl
      rw [h2, hiota] at h1
      have h3 : φ (e.hom.hom a) = 0 := IsFractionRing.injective Ω (FractionRing Ω) (by rw [h1, map_zero])
      have h4 : e.hom.hom a = 0 := hφ (by rw [h3, map_zero])
      have h5 : a = 0 := by simpa using congrArg e.inv.hom h4
      rw [h5, IsLocalization.mk'_zero]
    exact (injective_iff_map_eq_zero iota).2 key
  have hΘ : Θ₁ = (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp e.inv.hom).mapMatrix h.Θ := by
    ext a a'
    apply hi
    have := congrFun (congrFun heq a) a'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply] at this ⊢
    rw [← this, hiota]
  rw [hΘ] at hKS
  exact GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen E H R t m tt n ⇑b D DV h.Θ hDV' hKS

end GlobalTheory.KBracket
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) m.cart → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) m.cart) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) m.cart := by
  first | (exact @GlobalTheory.HTLiftLie.lie_liftFil) | (exact GlobalTheory.HTLiftLie.lie_liftFil) | (intros; apply GlobalTheory.HTLiftLie.lie_liftFil  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def graphFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : HdR A₀ →ₗ[k] HdR A₀) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

variable {A₀ : Over (Sp k)} [GrpObj A₀]

theorem mem_graphFil {f : HdR A₀ →ₗ[k] HdR A₀} {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} :
    d ∈ graphFil A₀ f ↔ ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c) := Iff.rfl

theorem isBC_constMor (hA : IsAbelianScheme A₀) : (constMor A₀).IsBC :=
  GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k A₀ hA (SqExt.dual k).sq (constMor A₀)

theorem exists_crys (hA : IsAbelianScheme A₀) (u v : HdR A₀) :
    ∃ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  obtain ⟨d₁, h₁⟩ := (isBC_constMor hA).exists u
  obtain ⟨d₂, h₂⟩ := (isBC_constMor hA).exists v
  refine ⟨d₁ + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • d₂, fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, h₁ c, h₂ c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]



theorem crys_ext (hA : IsAbelianScheme A₀) {d d' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = d' ((constMor A₀).pull c)) : d = d' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c'
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def coordOf (g : DualNumber k →ₗ[k] k) (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) : HdR A₀ where
  toFun c := g (d ((constMor A₀).pull c))
  map_add' a b := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' r a := by
    rw [map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul]
    rfl

theorem exists_coords (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) :
    ∃ u v : HdR A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  refine ⟨coordOf (TrivSqZeroExt.fstHom k k k).toLinearMap d, coordOf (TrivSqZeroExt.sndHom k k) d, fun c => ?_⟩
  ext <;> simp [coordOf]

end GlobalTheory.HTRealise
end
end
