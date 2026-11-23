module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3194
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_galois_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk | exact GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk | (intros; apply GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.BaseSch

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lowMap_eq {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) :
    lowMap c b = spMap b ≫ lowMap c (RingHom.id c.F) := by
  simp only [lowMap, RingHom.id_comp]
  rw [← spMap_comp']

theorem objMap_congr {D : Datum H} {l : Geo.Tor.Level H} {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    {s' : S' ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {f f' : S' ⟶ S} (h : f = f')
    (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ : 𝟙_ (Over S) ⟶ G) :
    ∃ σ' : 𝟙_ (Over S') ⟶ G', σ'.left ≫ φ = q ≫ σ.left := by
  have hw : (q ≫ σ.left) ≫ G.hom = 𝟙 S' ≫ q := by
    rw [Category.assoc, Over.w σ]
    simp
  refine ⟨Over.homMk (h.1.lift (q ≫ σ.left) (𝟙 S') hw) (by simpa using h.1.lift_snd _ _ hw), ?_⟩
  simp

theorem hom_ext_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) {T : Over S'} (σ₁ σ₂ : T ⟶ G')
    (e : σ₁.left ≫ φ = σ₂.left ≫ φ) : σ₁ = σ₂ := by
  ext1
  exact h.1.hom_ext e (by rw [Over.w σ₁, Over.w σ₂])

theorem pull_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ₁ σ₂ : 𝟙_ (Over S') ⟶ G') (τ₁ τ₂ : 𝟙_ (Over S) ⟶ G)
    (h₁ : σ₁.left ≫ φ = q ≫ τ₁.left) (h₂ : σ₂.left ≫ φ = q ≫ τ₂.left) :
    (σ₁ * σ₂).left ≫ φ = q ≫ (τ₁ * τ₂).left := by
  let Q : Over.mk ((𝟙_ (Over S')).hom ≫ q) ⟶ 𝟙_ (Over S) := Over.homMk q (by simp)
  have e := h.2 (𝟙_ (Over S')) σ₁ σ₂ (Q ≫ τ₁) (Q ≫ τ₂) (by simp [Q, h₁]) (by simp [Q, h₂])
  rw [← e, ← MonObj.comp_mul]
  simp [Q]

theorem sec_comp_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (hw : φ ≫ G.hom = G'.hom ≫ f) (σ : 𝟙_ (Over S') ⟶ G') (τ : 𝟙_ (Over S) ⟶ G) :
    (σ.left ≫ φ) ≫ G.hom = (f ≫ τ.left) ≫ G.hom := by
  rw [Category.assoc, hw, Category.assoc, Over.w τ, ← Category.assoc, Over.w σ]
  simp

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}



theorem of_homScheme (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F)
    (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F)))
    (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)) (N : ℕ) (hsm : SmoothOfRelativeDimension N g)
    (hex : ∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV)
      (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) →
      (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v),
        v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left)
    (huniq : ∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g →
      ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
        (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)),
        s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) →
        (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂)
    (heps : ∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l)))
      (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v)
      (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
      s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) →
      (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)
    (hadd : ∀ y z, u (y + z) = u y * u z) (hlin : ∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV)
    (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)) (hx : ∀ y z, x (y + z) = x y * x z)
    (hxl : ∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b)
      (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)),
      b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧
      IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧
      ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b →
        ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂))
          (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧
        (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f))
          (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
          (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) →
          (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧
      (letI := ((residue W).comp b).toAlgebra
        ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = N) := by
  obtain ⟨v, m0, hvg, hvx⟩ := hex V bV o' x hx hxl
  obtain ⟨hreg, b, hqb, hft, hdim⟩ :=
    GlobalTheory.SmoothStalk.stalk_regular_essFiniteType_dim c.F Cs g N hsm (v (closedPoint V))
  haveI : IsDomain (Cs.presheaf.stalk (v (closedPoint V))) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨q, hq⟩ : ∃ q, q = Cs.fromSpecStalk (v (closedPoint V)) := ⟨_, rfl⟩
  rw [← hq] at hqb
  have hs : lowMap c b = q ≫ g ≫ lowMap c (RingHom.id c.F) := by
    rw [lowMap_eq c b, ← hqb, Category.assoc]
  obtain ⟨o, ⟨mq⟩⟩ := (obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (g ≫ lowMap c (RingHom.id c.F)) oC q (lowMap c b) hs
  have hsec := fun y => exists_section_pull mq.toSABMap.cart (u y)
  choose x₀ hx₀ using hsec
  set θ₀ : Cs.presheaf.stalk (v (closedPoint V)) →+* V := (Scheme.stalkClosedPointTo v).hom with hθ₀
  have hθq : spMap θ₀ ≫ q = v := by
    rw [hq]
    simpa [hθ₀, spMap] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk v
  have hθb : θ₀.comp b = bV := by
    apply spMap_injective
    rw [spMap_comp', ← hqb, ← Category.assoc, hθq, hvg]
  obtain ⟨m0', hm0'⟩ := objMap_congr hθq.symm m0
  obtain ⟨n, hn⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o' q (spMap θ₀) mq).2 m0'
  have hmono : ∀ {T : Scheme.{0}} (a₁ a₂ : T ⟶ Sp (Cs.presheaf.stalk (v (closedPoint V)))), a₁ ≫ q = a₂ ≫ q → a₁ = a₂ :=
    fun a₁ a₂ h => by rw [hq] at h; exact (cancel_mono _).1 h
  refine ⟨Cs.presheaf.stalk (v (closedPoint V)), inferInstance, inferInstance, hreg, b, o, x₀, θ₀, n, hft, ?_, ?_, ?_, hθb, ?_, ⟨?_, ?_⟩, hdim⟩
  · intro y z
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hadd, pull_mul mq.toSABMap.cart _ _ _ _ (hx₀ y) (hx₀ z)]
  · intro a y
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hlin, Over.comp_left, Over.comp_left, Category.assoc, mq.toSABMap.act a, reassoc_of% (hx₀ y)]
  · exact inferInstance
  · intro y
    refine mq.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn, hm0', hvx, Category.assoc, hx₀, ← Category.assoc, hθq]
    · exact sec_comp_eq _ _ n.toSABMap.cart.1.w (x y) (x₀ y)
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₁) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₂) mq).1 m₂
    have hg : ∀ f : Cs.presheaf.stalk (v (closedPoint V)) →+* A, (spMap f ≫ q) ≫ g = spMap (f.comp b) := fun f => by
      rw [Category.assoc, hqb, spMap_comp']
    have e := huniq A (spMap f₁ ≫ q) (spMap f₂ ≫ q) (by rw [hg, hg, hf]) _ o'' k₁ k₂ z
      (by rw [lowMap_eq c (f₁.comp b), ← hg, Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, Category.assoc])
    exact spMap_injective (hmono _ _ e)
  · intro k _ f o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q
      (spMap (GlobalTheory.RigChart.constHom f)) mq).1 m₂
    have hc : spMap (GlobalTheory.RigChart.constHom f) ≫ q = constPt (spMap f ≫ q) := by
      simp only [constPt, GlobalTheory.RigChart.constHom, spMap_comp', Category.assoc]
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hc k₂
    have e := heps k (spMap f ≫ q) _ o'' k₁ k₂' z
      (by rw [lowMap_eq c (f.comp b), spMap_comp', ← hqb]; simp only [Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, ← Category.assoc, hc])
    rw [← hc] at e
    exact spMap_injective (hmono _ _ e)

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

theorem exists_baseSch_of_homScheme (hcs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)) : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hx hxl
  obtain ⟨Cs, g, oC, u, hsm, hadd, hlin, hex, huniq, heps⟩ := hcs D' c X
  exact of_homScheme D' c X Cs g oC u _ hsm hex huniq heps hadd hlin V bV o' x hx hxl

end GlobalTheory.UCanon.BaseSch
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCanon.LowPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f : L.W →+* A) :
    ∃ (o' : LowObj D' c (f.comp L.b)) (m : ObjMap o' L.o (spMap f)) (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  have hs : lowMap c (f.comp L.b) = spMap f ≫ lowMap c L.b := by
    simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨o', ⟨m⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (lowMap c L.b) L.o (spMap f) (lowMap c (f.comp L.b)) hs
  have hB := L.ab.1.1
  have u : ∀ y, ∃ u : Sp L.W ⟶ L.o.t.G.left, u ≫ L.φB = (L.D.c y).left ∧ u ≫ L.o.t.G.hom = 𝟙 _ := by
    intro y
    refine ⟨hB.lift (L.D.c y).left (𝟙 _) ?_, hB.lift_fst _ _ _, hB.lift_snd _ _ _⟩
    simpa using Over.w (L.D.c y)
  choose u hu₁ hu₂ using u
  have hm := m.toSABMap.cart.1
  refine ⟨o', m, fun y => hm.lift (spMap f ≫ u y) (𝟙 _) ?_, fun y => ?_, fun y => hm.lift_snd _ _ _⟩
  · rw [Category.assoc, hu₂, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, hm.lift_fst, Category.assoc, hu₁]

theorem exists_pull₂ {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f₁ f₂ : L.W →+* A) (h : f₁ = f₂) :
    ∃ (o' : LowObj D' c (f₁.comp L.b)) (m₁ : ObjMap o' L.o (spMap f₁)) (m₂ : ObjMap o' L.o (spMap f₂))
      (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f₁ ≫ (L.D.c y).left) ∧
      (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap f₂ ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  subst h
  obtain ⟨o', m, x, hx, hxs⟩ := exists_pull L A f₁
  exact ⟨o', m, m, x, hx, hx, hxs⟩

end GlobalTheory.UCanon.LowPull

namespace GlobalTheory.UCanon.LowPull
theorem comp_b_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (F : Fam Xo c R)
    {V : Type} [CommRing V] [IsDomain V] (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (h₁ : κ₁ ≫ jK R = jK V ≫ spMap θ₁) (h₂ : κ₂ ≫ jK R = jK V ≫ spMap θ₂) (hy : κ₁ ≫ F.y = κ₂ ≫ F.y) :
    θ₁.comp F.b = θ₂.comp F.b := by
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp F.b) = κ ≫ F.y ≫ pullback.snd _ _ := by
    intro θ κ h
    rw [F.y_over, ← Category.assoc, h, Category.assoc, spMap_comp]
  have e : jK V ≫ spMap (θ₁.comp F.b) = jK V ≫ spMap (θ₂.comp F.b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hy, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end GlobalTheory.UCanon.LowPull
end
end

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBaseData

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  intro E _ _ _ H W _ _ _ t hp hA hK ⟨g, hg⟩ X _ _ _ _ x₀ hadd hlin
  letI := H.starRing
  let P := GlobalTheory.GenericPol.toPolAV t g hg hp hA hK
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ t.PP).1 t.sym
  have hψ0 : ∀ y : X, ∃ ψ : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (x₀ y)) (fun _ => -1)), ψ.IsGen :=
    fun y => ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := FractionRing W) P.L P.isLB _ _
  choose ψ hψ using hψ0
  let D₀ : DegPre W :=
    { P := P, rig := t.PP.rig, rig_gen := t.PP.rigGen, cub := t.cub, sym := sym, sym_gen := hsym, sym_rig := hsym',
      X := X, c := x₀, c_add := hadd, psi := ψ, psi_gen := hψ }
  letI : Module (𝓞 E) D₀.X := ‹Module (𝓞 E) X›
  haveI : Module.Projective (𝓞 E) D₀.X := GlobalTheory.PointStepCompare.projective_of_free E (X := X)
  haveI : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  have := t.act.hom H.w0
  let onB : D₀.P.OAct (𝓞 E) := ⟨t.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj t⟩
  obtain ⟨u, hu, hu0⟩ := GlobalTheory.ArcCM.CxFibre.exists_primGen t.PP (t.act.act H.w0) t.prim
  obtain ⟨ψ', hψ', oa, hoa, he, hb, hw, hU⟩ := GlobalTheory.UTau0.exists_symmetric_balanced_generator_psi_zero_localRing W D₀ (𝓞 E) onB hlin H.w0
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) ⟨u, hu, hu0⟩
  refine ⟨{ D₀ with psi := ψ', psi_gen := hψ' }, ‹Module (𝓞 E) X›, oa, 𝟙 _, LinearEquiv.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he
  · exact hb
  · exact hU
  · exact hw
  · refine ⟨GlobalTheory.PolDeg.Wit.grpPullback_id t.G, fun a => ?_, GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen t.PP.isLB⟩
    rw [hoa]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro y
    exact Category.comp_id _

end GlobalTheory.UBaseData
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

noncomputable section

namespace GlobalTheory.GSep.TwistSum₂

theorem val_stalkHom (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem twistSum_of_sumF : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ C lab T sg c τ χ e hθ hY hχ hS
  intro zt h hzt hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : ∀ s, X₁.M.stalkHom z₁ s ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := fun s =>
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ s).2
  have hR : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := 𝔪.reg
  have hyK : ∀ (a : X₁.Ω₁) (ha : a ∈ X₁.S.R), 𝔪.yK ⟨a, ha⟩ = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a :=
    fun a ha => 𝔪.yK_eq ⟨a, ha⟩
  have hyA : ∀ b : X₁.o₁, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R b) =
      X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (algebraMap X₁.o₁ X₁.Ω₁ b) := fun b => by
    rw [𝔪.yK_eq, Subalgebra.coe_algebraMap]
  have hzt' : algebraMap V (FractionRing V) (ev zt) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := by
    rw [← val_stalkHom X₁ z₁ ev, hzt, hyA]
  have hth0 : X₁.S.th x₀ ≠ 0 := by
    intro h0
    apply hθ
    rw [hyK, h0, RatModel.val_zero]
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩ := by
    rw [← val_stalkHom X₁ z₁ ev, hyA, hyK, hyK, ← RatModel.val_mul hsp (hO h) (hR _ (X₁.S.th_mem x₀)),
      ← RatModel.val_mul hsp (hR _ (Subalgebra.algebraMap_mem _ _)) (hR _ (X₁.S.th_mem _)), hh,
      div_mul_cancel₀ _ hth0]
  have hterm : ∀ mu : X, ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) *
      (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) =
      algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro mu
    obtain ⟨a, ha⟩ := hY mu
    rw [hχ a mu ha, ← hwt a mu ha, pow_mul, map_pow, map_pow, ← hzt', map_mul, map_pow]
    ring
  refine GlobalTheory.Poinc.TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  convert hS using 1
  · funext mu
    exact (hterm mu).symm

end GlobalTheory.GSep.TwistSum₂
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_canonical_deRham_rigidExtension_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime], ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧ ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A] (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A), IsCan t c (e hR hA t c) := by
  first | exact @GlobalTheory.DeRhamExt.exists_canonical_family | exact GlobalTheory.DeRhamExt.exists_canonical_family | (intros; apply GlobalTheory.DeRhamExt.exists_canonical_family <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧ Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (exact GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (intros; apply GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B), tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  first | (exact @GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (exact GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (intros; apply GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul  <;> assumption)
end
