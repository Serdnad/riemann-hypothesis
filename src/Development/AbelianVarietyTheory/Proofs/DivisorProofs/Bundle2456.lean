module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004

@[expose] public section

section

set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

namespace GlobalTheory.TwoLevelsDom

theorem lact_tr_mem_dom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {rr : ℕ} {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E rr U C) (g : U) (c : C) (x : Frame M.Ψ rr), x ∈ M.dom → lact (M.tr g c) x ∈ M.dom :=
  fun M g c _x hx => GlobalTheory.CuspEmb.lact_tr_mem M g c hx

end GlobalTheory.TwoLevelsDom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  exact @GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf
end

section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.DivOn

theorem unitAt_of {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {u : Z.functionField} (h0 : u ≠ 0)
    (h : u ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range)
    (h' : u⁻¹ ∈ (algebraMap (Z.presheaf.stalk z) Z.functionField).range) : UnitAt z u :=
  (unitAt_iff h0).2 ⟨h, h'⟩

theorem key {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) {gr : Root m → Y.Dv}
    {B : Mat m Y.Fn} (hB : B ∈ E'.S (genericPoint Y.X))
    (hgr : ∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t)
    (W : Dbl Y) (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) {τ : ι} {a b : Fin (m τ)} (hab : (b : ℕ) = a + 1)
    (hC : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹)) {D₁ D₂ : Root m → CartierDiv W.Z}
    (hD₁ : ∀ x, IsPull W.p₁ (D₁ x) (gr x)) (hD₂ : ∀ x, IsPull W.p₂ (D₂ x) (gr x)) (z : W.Z)
    {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) :
    ∃ t₁ t₂ : Root m → W.Z.functionFieldˣ, (∀ x, (D₁ x).IsEqn z (t₁ x)) ∧ (∀ x, (D₂ x).IsEqn z (t₂ x)) ∧
      AlmostLow τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∧
      (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ →
        UnitAt z ((t₁ x : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) x.1 x.2 x.2 * t₂ x)) ∧
      UnitAt z ((t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (t₁ ⟨τ, b⟩ : W.Z.functionField)⁻¹ *
        minor τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) * (t₂ ⟨τ, a⟩ * t₂ ⟨τ, b⟩)) ∧
      (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b =
        (t₁ ⟨τ, a⟩ : W.Z.functionField)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) τ a b * t₂ ⟨τ, b⟩ ∧
      RegAt z ((A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨hP₁, h₁⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₁ hA₁
  obtain ⟨hP₂, h₂⟩ := GlobalTheory.T.isCartierLocalEquation_diagonal_of_adaptedFrame F Y ι m E' gr B hB hgr _ A₂ hA₂
  choose s₁ e₁ q₁ using h₁
  choose s₂ e₂ q₂ using h₂
  have hT₁ : Par m ⊤ ((B * A₁⁻¹).map W.α₁) := hP₁.map W.α₁ fun _ _ => trivial
  have hT₂ : Par m ⊤ ((B * A₂⁻¹).map W.α₂) := hP₂.map W.α₂ fun _ _ => trivial
  have hloc := GlobalTheory.T.isUnit_stalk_transition_pulledBack_flagFrames F X Y ι m E E' φ f hf W hα z A₁ hA₁ A₂ hA₂
  have dB₁ : ∀ σ, (B.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dB₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hB σ)
  have dA₁ : ∀ σ, (A₁.map W.α₁ σ).det ≠ 0 := fun σ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hA₁ σ)
  have eg : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ =
      ((B * A₁⁻¹).map W.α₁)⁻¹ * (B.map W.α₁ * (B.map W.α₂)⁻¹) * (B * A₂⁻¹).map W.α₂ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, Mat.mul_inv_rev, Mat.inv_inv dA₁, mul_assoc, mul_assoc,
      mul_assoc, ← mul_assoc (B.map W.α₂)⁻¹, Mat.inv_mul dB₂, one_mul, ← mul_assoc (B.map W.α₁)⁻¹, Mat.inv_mul dB₁,
      one_mul]
  obtain ⟨hal, hd, hab', hmin⟩ := GlobalTheory.T.minor_two_by_two_triangular_product ι m τ a b hab _ _ _ _ hT₁.inv hT₂ hC
  rw [← eg] at hal hd hab' hmin
  obtain ⟨hu, hm0, hm1⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ _ _ hal hloc
  have i₁ : ∀ x : Root m, ((B * A₁⁻¹).map W.α₁)⁻¹ x.1 x.2 x.2 = (W.α₁ (s₁ x))⁻¹ := fun x => by
    rw [(GlobalTheory.T.parabolicMatrixFamily_diag_isUnit ι m _ ⊤ _ hT₁ x).2.2.1, ← e₁ x]; rfl
  have i₂ : ∀ x : Root m, ((B * A₂⁻¹).map W.α₂) x.1 x.2 x.2 = W.α₂ (s₂ x) := fun x => by
    rw [← e₂ x]; rfl
  refine ⟨fun x => Units.map W.α₁.toMonoidHom (s₁ x), fun x => Units.map W.α₂.toMonoidHom (s₂ x),
    fun x => hD₁ x _ _ (q₁ x) z rfl, fun x => hD₂ x _ _ (q₂ x) z rfl, hal, fun x hxa hxb => ?_, ?_, ?_,
    (hloc τ).1 a b⟩
  · have := unitAt_of (hu x hxa hxb).1 ((hloc x.1).1 x.2 x.2) (hu x hxa hxb).2
    rw [hd x hxa hxb, i₁, i₂] at this
    exact this
  · have hmem : minor τ a b (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) ∈
        (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range :=
      sub_mem (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _)) (mul_mem ((hloc τ).1 _ _) ((hloc τ).1 _ _))
    have := unitAt_of hm0 hmem hm1
    rw [hmin, i₁ ⟨τ, a⟩, i₁ ⟨τ, b⟩, i₂ ⟨τ, a⟩, i₂ ⟨τ, b⟩] at this
    exact this
  · rw [hab', i₁ ⟨τ, a⟩, i₂ ⟨τ, b⟩]
    rfl

theorem exists_divisors : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => GlobalTheory.T.exists_cartierDivisor_pullback_of_dominant W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := GlobalTheory.T.almostLowerTriangular_diag_minor_isUnit ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add (f := _), toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add (f := _), ← map_add (f := _), ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add (f := _), toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine GlobalTheory.T.mem_range_diagonal_of_not_unit_transitionEntry F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact GlobalTheory.T.not_isUnit_offDiagonal_transition_on_commonSection F X Y ι m E E' φ f hf W hα τ a b hne y A hA

end GlobalTheory.FlagPush.DivOn
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Dbl

theorem interPoly_rename_swap : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (gr : κ → Y.Dv) (D₁ D₂ : κ → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ a → x ≠ b → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ a) + toPic (D₁ b) = toPic (D₂ a) + toPic (D₂ b) ∧ toPic Θ = toPic (D₂ b) - toPic (D₁ a) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ → ∀ Q : MvPolynomial κ ℝ, Y.interPoly gr (rename (Equiv.swap a b) Q) = - Y.interPoly gr Q := by
  intro F _ Y W hW κ a b hab gr D₁ D₂ Θ ⟨h₁, h₂, hx, hsum, hΘ, hE, hS⟩
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.T.exists_intersectionForm_picard_doubleSpace F Y W hW
  obtain ⟨μ, hμ, hc⟩ := GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section F Y W hW Θ hE hS
  let N : AddSubgroup (CartierDiv W.Z) := (toPic (X := W.Z)).ker
  let π : CartierDiv W.Z →+ CartierDiv W.Z ⧸ N := QuotientAddGroup.mk' N
  let φ : (CartierDiv W.Z ⧸ N) →+ Pic W.Z := QuotientAddGroup.kerLift toPic
  have hφ : Function.Injective φ := QuotientAddGroup.kerLift_injective _
  have hπ (D : CartierDiv W.Z) : φ (π D) = toPic D := rfl
  let T' : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (Y.dim + 1) => CartierDiv W.Z ⧸ N) ℤ :=
    T.compLinearMap fun _ => φ.toIntLinearMap
  have hT' (y : Fin (Y.dim + 1) → CartierDiv W.Z) : T' (fun i => π (y i)) = W.num y := hT y
  refine GlobalTheory.T.linearForm_antisymm_of_doublePoint_symmMultilinear κ a b hab (CartierDiv W.Z ⧸ N) Y.dim T' (fun σ y => hTs σ fun i => φ (y i))
    (fun x => π (D₁ x)) (fun x => π (D₂ x))
    (Y.interPoly gr) μ hμ (fun x ha hb => hφ (hx x ha hb)) (hφ ?_) (fun s => ?_) (fun s => ?_)
    (fun k P hP hk => GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim F Y κ gr k P hP hk) (fun s => ?_)
  · simpa only [map_add (f := _), hπ] using hsum
  · exact (hT' (fun i => D₁ (s i))).trans
      (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₁ _ (fun i => gr (s i)) fun i => h₁ (s i))
  · exact (hT' (fun i => D₂ (s i))).trans
      (GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero F Y W hW W.p₂ _ (fun i => gr (s i)) fun i => h₂ (s i))
  · have hΘ' : π (D₂ b) - π (D₁ a) = π Θ := hφ (by simp only [map_sub, hπ, hΘ])
    have e : (Fin.cons (π (D₂ b) - π (D₁ a))
        (Sum.elim (fun x => π (D₁ x)) (fun x => π (D₂ x)) ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z ⧸ N) =
        fun i => π ((Fin.cons Θ (Sum.elim D₁ D₂ ∘ s) : Fin (Y.dim + 1) → CartierDiv W.Z) i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero, hΘ']
      · simp only [Fin.cons_succ, Function.comp_apply]
        cases s j <;> rfl
    have r := GlobalTheory.T.doubleSpace_section_intersectionNumber_eq_base F Y W (Sum.elim D₁ D₂ ∘ s) (gr ∘ fun i => Sum.elim id id (s i)) fun i => by
      simp only [Function.comp_apply]
      cases s i with
      | inl x => exact Or.inl (h₁ x)
      | inr x => exact Or.inr (h₂ x)
    rw [e, hT', hc, r, Var.interPoly_prod]
    push_cast
    rfl

end GlobalTheory.FlagPush.Dbl
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.Cyc

theorem coinv_eq_rel (P Q R S : ℕ) (x : ℚ) : coinv P Q R S (x : ℂ) = GlobalTheory.FockQuot.rel P Q R S x := rfl

theorem fockAct2_good (P Q R S : ℕ) : Good (fockAct2 P Q R S) :=
  ⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2,
    GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩

theorem rel_stab (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (y : Pol P Q R S) (hy : y ∈ GlobalTheory.FockQuot.rel P Q R S x) :
    fockAct2 P Q R S Y y ∈ GlobalTheory.FockQuot.rel P Q R S x := by
  have h := GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy
  rw [Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply] at h
  simpa using h

theorem actQ_zero_mk (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (fockAct2 P Q R S Y f) := by
  rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; simp

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (T : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act T) : act Z y ∈ genSub act T := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro N hN
  exact hN.2 Z y (hy N hN)

theorem mem_genSub_self {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (v : V) : v ∈ genSub act {v} := by
  unfold genSub
  rw [Submodule.mem_sInf]
  intro N hN
  exact hN.1 rfl

theorem cycMod_rel (P Q R S : ℕ) (x : ℚ) (hne : GlobalTheory.FockQuot.rel P Q R S x ≠ ⊤) :
    CycMod (fockAct2 P Q R S) (GlobalTheory.FockQuot.rel P Q R S x) := by
  set C := GlobalTheory.FockQuot.rel P Q R S x with hC
  have hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V := by
    show Nontrivial (Pol P Q R S ⧸ C)
    exact Submodule.Quotient.nontrivial_iff.2 hne
  have hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ := by
    refine ⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩
    show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _
    rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; rfl
  obtain ⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩ :=
    GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt
  change w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw
  change genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective C w
  change (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0
  have hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈
      hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0) := hwhw
  obtain ⟨hwt0, hpos0⟩ := Submodule.mem_inf.1 hwhw'
  have hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) =
      (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) := fun c => by
    unfold wtSub at hwt0
    have h := (Submodule.mem_iInf _).1 hwt0 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  have hpos : ∀ c d, posC c d →
      GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0 := fun c d hcd => by
    have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd
    exact h
  have hKC : KStable (fockAct2 P Q R S) C := fun X _ y hy => rel_stab P Q R S x X y hy
  have hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S)) := fun _ _ _ _ => Submodule.mem_top
  have h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C := by
    intro c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← actQ_zero_mk, hwt c]
    simp
  have h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C := by
    intro c d hcd
    rw [← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]
    exact hpos c d hcd
  obtain ⟨v, -, hv, hfv⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁
      Submodule.mem_top h1 h2
  have hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁ :=
    ((Submodule.Quotient.eq C).2 hfv).symm
  refine ⟨μ', v, hv, ?_, ?_⟩
  ·
    set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN
    have hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N := by
      intro Z y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add (f := _)]
      exact N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha))
        (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))
    have hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ := by
      refine sInf_le ⟨?_, ?_⟩
      · rw [Set.singleton_subset_iff, ← hmk]
        exact ⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩
      · rintro Z _ ⟨n, hn, rfl⟩
        refine ⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩
        simp only [Submodule.mkQ_apply]
        rw [actQ_zero_mk]
    have hle2 : N.map C.mkQ = ⊤ := top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)
    rw [eq_top_iff]
    intro f _
    have hf : Submodule.Quotient.mk f ∈ N.map C.mkQ := by rw [hle2]; exact Submodule.mem_top
    obtain ⟨n, hn, hnf⟩ := hf
    have hd : n - f ∈ C := (Submodule.Quotient.eq C).1 hnf
    have : f = n - (n - f) := by abel
    rw [this]
    exact N.sub_mem hn (Submodule.mem_sup_right hd)
  ·
    obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants P Q R S x μ' hJ
    rw [coinv_eq_rel] at hf₀
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hf₀ hv)
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz : z ≠ 0 := by
      rintro rfl
      apply hw0
      rw [← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]
      simpa using hc
    have hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C := by
      have : f₀ = z⁻¹ • v - z⁻¹ • c := by
        rw [← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (Submodule.mem_sup_right (C.smul_mem _ hc))
    refine hf₀.trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf₀mem

end GlobalTheory.HoweR.Cyc

theorem GlobalTheory.HoweR.coinv_cycMod : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  rcases GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩
  · rw [h]
    refine ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
  · rw [h, GlobalTheory.HoweR.Cyc.coinv_eq_rel] at *
    by_cases hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤
    · rw [hne]
      exact ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_frames_fockMap_polynomial_lie_actions : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  first | exact @GlobalTheory.HoweD.FockData.exists_fock_data | exact GlobalTheory.HoweD.FockData.exists_fock_data | (intros; apply GlobalTheory.HoweD.FockData.exists_fock_data <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

theorem _root_.GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  first | exact @GlobalTheory.LowMainTerm.main_le_lowB | exact GlobalTheory.LowMainTerm.main_le_lowB | (intros; apply GlobalTheory.LowMainTerm.main_le_lowB <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → FiniteDimensional ℂ (forms S lam K') ∧ ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)), (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ π i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, π i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K' ∧ ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → π₀ ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∃ i, ∀ w (σ : SmIrr (UL n w)), IsCompU π₀ w σ → IsCompU (π i) w σ := by
  first | exact @GlobalTheory.BCT.forms_decomp | exact GlobalTheory.BCT.forms_decomp | (intros; apply GlobalTheory.BCT.forms_decomp <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.level_stabiliser_le_centraliser_compact_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ x : finU (E := E) (n := n), twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S (KL n)).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ)) ∧ (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ) ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ))) ≠ 0 := by
  first | exact @GlobalTheory.BCT.CentLev.stab_le_cptPart | exact GlobalTheory.BCT.CentLev.stab_le_cptPart | (intros; apply GlobalTheory.BCT.CentLev.stab_le_cptPart <;> assumption)
end
