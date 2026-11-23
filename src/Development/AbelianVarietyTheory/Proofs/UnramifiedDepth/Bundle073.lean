module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle071
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpec
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle022
public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle070
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cubicalWeil_trivial_of_localArtinian_points : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (n : ℕ), IsFinite ((𝟙 G) ^ n : G ⟶ G).left → ∀ (D : Type) [CommRing D] [Algebra Ω D] [Module.Finite Ω D] (x : overAt s D ⟶ G), x ^ n = 1 → (∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ (f : D →ₐ[Ω] A) (y : overAt s A ⟶ G), y ^ n = 1 → CubWeil c n (homAt s f ≫ x) y 1) → ∀ (T' : Over S) (ρ : T' ⟶ overAt s D) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1 := by
  first | exact @GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian | exact GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian | (intros; apply GlobalTheory.AlphaPair.cubWeil_one_of_local_artinian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.universalChart_points_over_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtUniv (spMap β) t.G P := by
  first | exact @GlobalTheory.AlphaPair.jetUniv | exact GlobalTheory.AlphaPair.jetUniv | (intros; apply GlobalTheory.AlphaPair.jetUniv <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.evalPowerSeries_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  first | exact @GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | exact GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | (intros; apply GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.eq_one_of_tangent_vector_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G), IsAlpha p s G g → g (DualNumber Ω) DualNumber.eps = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → g A a = 1 := by
  first | exact @GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | exact GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | (intros; apply GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_torusExtension_points_pullback_fieldPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  first | exact @GlobalTheory.AlphaPair.exists_isTorExt_pull | exact GlobalTheory.AlphaPair.exists_isTorExt_pull | (intros; apply GlobalTheory.AlphaPair.exists_isTorExt_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianPart_projection_respects_orthogonality : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegData W I) (Av : Out.PolAV (Spec (CommRingCat.of (FractionRing W)))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D Av G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∀ τ : PtHom (spMap β) (spMap β) G D.toPre.P.A, (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ (U.gt 0).pG.left) → ∀ n : ℕ, Transfer n U.cubG D.toPre.cub τ := by
  first | exact @GlobalTheory.AlphaPair.transfer_of_unif | exact GlobalTheory.AlphaPair.transfer_of_unif | (intros; apply GlobalTheory.AlphaPair.transfer_of_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.degenerate_direction_of_not_nondegenerate : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (d : ℕ) (Y : FBChart C V O d) (R₀ : Type) [CommRing R₀] (j : R₀ →+* V.RR) (F : Fin d → PS R₀ 2 d) (ph2 : PS R₀ 3 d), (∀ i, MvPowerSeries.constantCoeff (F i) = 0) → (∀ i, Y.B.G.F i = MvPowerSeries.map (V.RR.subtype.comp j) (F i)) → Y.B.ph2 = MvPowerSeries.map (V.RR.subtype.comp j) ph2 → ∀ (Ω : Type) [Field Ω] (ρ : V.RR →+* Ω), (∀ x : V.RR, ρ x = 0 ↔ V.MM (x : C)) → ¬ NDG Y → Degenerate V.l (fun i => MvPowerSeries.map (ρ.comp j) (F i)) (MvPowerSeries.map (ρ.comp j) ph2) := by
  first | exact @GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg | exact GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg | (intros; apply GlobalTheory.AlphaPair.Reduce.degenerate_of_not_ndg <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_isTorusExtensionOnPoints_mod_ideal : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  first | exact @GlobalTheory.TorExtPoints.exists_isTorExt | exact GlobalTheory.TorExtPoints.exists_isTorExt | (intros; apply GlobalTheory.TorExtPoints.exists_isTorExt <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetPt

section Rho

variable {V Ω : Type} [CommRing V] [CommRing Ω] (β : V →+* Ω)

def Compat {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) : Prop :=
  ∀ v : V, ψ (algebraMap V B v) = algebraMap Ω A (β v)

variable {β}

theorem Compat.left {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) : Compat β (ψ.comp (f : B' →+* B)) := fun v => by
  rw [RingHom.comp_apply, RingHom.coe_coe, f.commutes, h v]

theorem Compat.right {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') : Compat β ((g : A →+* A').comp ψ) := fun v => by
  rw [RingHom.comp_apply, h v, RingHom.coe_coe, g.commutes]

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def rho {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) (h : Compat β ψ) :
    overAt (spMap β) A ⟶ overAt (𝟙 (Sp V)) B :=
  Over.homMk (spMap ψ) (by
    change spMap ψ ≫ spMap (algebraMap V B) ≫ 𝟙 _ = spMap (algebraMap Ω A) ≫ spMap β
    rw [Category.comp_id, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext h)

theorem rho_homAt {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) :
    rho ψ h ≫ homAt (𝟙 (Sp V)) f = rho (ψ.comp (f : B' →+* B)) (h.left f) :=
  Over.OverMorphism.ext (sp_comp _ _)

theorem homAt_rho {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') :
    homAt (spMap β) g ≫ rho ψ h = rho ((g : A →+* A').comp ψ) (h.right g) :=
  Over.OverMorphism.ext (sp_comp _ _)

def co {d m : ℕ} {A : Type} [CommRing A] (ψ : Jet V (Fin 1 × Fin d) m →+* A) : Fin d → A :=
  fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))

theorem eq_of_co {d m : ℕ} {A : Type} [CommRing A] [Algebra Ω A] {ψ ψ' : Jet V (Fin 1 × Fin d) m →+* A}
    (h : Compat β ψ) (h' : Compat β ψ') (e : co ψ = co ψ') : ψ = ψ' := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => (h v).trans (h' v).symm) ?_)
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact congrFun e j

theorem jetMap_X {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (i : κ) :
    (jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i) := by
  change Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  change MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]

theorem exists_jet {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [CommRing A] [Algebra Ω A] (a : κ → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V κ m →+* A), Compat β ψ ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := by
  have hn : IsNilpotent (Ideal.span (Set.range a)) := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact ha i
  obtain ⟨m, hm⟩ := hn
  obtain ⟨ψ, hψ, -⟩ := (GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β κ m).1 a (by rw [pow_succ, hm, zero_mul]; rfl)
  exact ⟨m, ψ, hψ⟩

theorem exists_jet_one {d : ℕ} {A : Type} [CommRing A] [Algebra Ω A] (a : Fin d → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A), Compat β ψ ∧ co ψ = a := by
  obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 1 × Fin d => a q.2) fun q => ha q.2
  exact ⟨m, ψ, h, funext fun j => e (0, j)⟩

variable {G : Over (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}

theorem lift_add (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} (ψ : Jet V (Fin 1 × Fin d) m →+* A) (h : Compat β ψ)
    {n : ℕ} (hn : m ≤ n) :
    ∃ (χ : Jet V (Fin 1 × Fin d) n →+* A) (hχ : Compat β χ), co χ = co ψ ∧ rho χ hχ ≫ x n = rho ψ h ≫ x m := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨ψ, h, rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨χ, hχ, e, e'⟩ := ih
    refine ⟨_, hχ.left jetTrunc, e, ?_⟩
    rw [← rho_homAt hχ, Category.assoc, hx, e']

theorem indep (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m n : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {ψ' : Jet V (Fin 1 × Fin d) n →+* A} (h' : Compat β ψ') (e : co ψ = co ψ') :
    rho ψ h ≫ x m = rho ψ' h' ≫ x n := by
  obtain ⟨χ, hχ, e₁, e₂⟩ := lift_add hx ψ h (le_max_left m n)
  obtain ⟨χ', hχ', e₁', e₂'⟩ := lift_add hx ψ' h' (le_max_right m n)
  obtain rfl : χ = χ' := eq_of_co hχ hχ' (by rw [e₁, e₁', e])
  rw [← e₂, ← e₂']

end Rho

section Main

variable {V Ω : Type} [CommRing V] [Field Ω] (β : V →+* Ω) {G : Over (Sp V)} [GrpObj G] {d : ℕ}
  (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G)


open Classical in
def ptOf : PtFam (spMap β) G d := fun A _ _ a =>
  if h : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a then
    rho h.choose.2 h.choose_spec.1 ≫ x h.choose.1
  else 1

variable {β x}

theorem ptOf_co (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {a : Fin d → A} (e : co ψ = a) : ptOf β x A a = rho ψ h ≫ x m := by
  have hh : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a := ⟨⟨m, ψ⟩, h, e⟩
  rw [ptOf, dite_eq_left hh]
  exact indep hx _ h (hh.choose_spec.2.trans e.symm)

end Main

end GlobalTheory.AlphaPair.JetPt


open GlobalTheory.AlphaPair.JetPt in
theorem GlobalTheory.AlphaPair.exists_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), IsChartG t (𝟙 (Sp V)) d F act tg uv x → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω), ∃ P : PtFam (spMap β) t.G d, IsJetPt β x P ∧ IsPtLaw (spMap β) t.G (fun j => MvPowerSeries.map β (F j)) P := by
  intro E _ _ _ H V _ t d F act tg uv x hc hF Ω _ β
  refine ⟨ptOf β x, fun A _ _ m ψ h => ?_, fun A B _ _ _ _ f a ha => ?_, fun A _ _ => ?_, fun A _ _ a b ha hb => ?_⟩
  · exact congrArg CommaMorphism.left (ptOf_co hc.trunc (ψ := ψ) h rfl)
  · obtain ⟨m, ψ, h, rfl⟩ := exists_jet_one (β := β) a ha
    rw [ptOf_co hc.trunc h rfl, ptOf_co hc.trunc (h.right f) (a := fun j => f (co ψ j)) rfl, ← Category.assoc, homAt_rho]
  · have h : Compat β ((algebraMap Ω A).comp β) := fun v => rfl
    rw [ptOf_co hc.trunc (h.left (jetAug : Jet V (Fin 1 × Fin d) 0 →ₐ[V] V))
      (funext fun j => by simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetAug_X, map_zero, Pi.zero_apply]),
      ← rho_homAt h, Category.assoc, hc.zero, MonObj.comp_one]
  · obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) (by
      rintro ⟨i, j⟩
      fin_cases i
      exacts [ha j, hb j])
    have hi : ∀ i : Fin 2, ptOf β x A (![a, b] i) = rho ψ h ≫ jptG t (𝟙 (Sp V)) d x m i := fun i => by
      rw [jptG, ← Category.assoc, rho_homAt]
      refine ptOf_co hc.trunc _ (funext fun j => ?_)
      simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetCopy, jetMap_X, e]
    have h0 : ptOf β x A a = _ := hi 0
    have h1 : ptOf β x A b = _ := hi 1
    rw [h0, h1, ← MonObj.comp_mul, ← hc.law m, ← Category.assoc, rho_homAt]
    refine ptOf_co hc.trunc _ (funext fun j => ?_)
    have h3 := ((GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β (Fin 2 × Fin d) m).2 ψ h).2.2 (F j)
    simp only [e] at h3
    simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetSubstP, jetMap_X]
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.cc_psTrunc, hF, map_zero, sub_zero]
    exact h3

end
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem _root_.GlobalTheory.T.rowLaw_formal_statements_selfConjugate : CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  first | exact @GlobalTheory.RowLaw.formal_statements_selfConj | exact GlobalTheory.RowLaw.formal_statements_selfConj | (intros; apply GlobalTheory.RowLaw.formal_statements_selfConj <;> assumption)
end
