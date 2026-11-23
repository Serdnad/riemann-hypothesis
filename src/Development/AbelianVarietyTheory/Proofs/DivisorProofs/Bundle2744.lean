module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

def omegaMod {h : ℕ} (M : ℕ) (x y : Fin h ⊕ Fin h → ZMod M) : ZMod M :=
  ∑ i, (x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))

def sympSimGrp (h M : ℕ) :
    Subgroup ((Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) where
  carrier := {g | ∃ m : (ZMod M)ˣ, ∀ x y, omegaMod M (g x) (g y) = m * omegaMod M x y}
  one_mem' := ⟨1, fun x y => by simp⟩
  mul_mem' := by
    rintro g g' ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m * m', fun x y => ?_⟩
    change omegaMod M (g (g' x)) (g (g' y)) = _
    rw [hm, hm', Units.val_mul, _root_.mul_assoc]
  inv_mem' := by
    rintro g ⟨m, hm⟩
    refine ⟨m⁻¹, fun x y => ?_⟩
    have hg := hm (g⁻¹ x) (g⁻¹ y)
    have e : ∀ z, g (g⁻¹ z) = z := fun z => by
      change (g * g⁻¹) z = z
      rw [mul_inv_cancel]; rfl
    rw [e, e] at hg
    rw [hg, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

instance sympSimGrp_finite (h M : ℕ) [NeZero M] : Finite (sympSimGrp h M) := by
  haveI : Finite ((Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) :=
    Finite.of_injective (fun g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M) =>
      (g : (Fin h ⊕ Fin h → ZMod M) → (Fin h ⊕ Fin h → ZMod M))) DFunLike.coe_injective
  infer_instance

def reduceMod {h : ℕ} (M : ℕ) (a : Fin h ⊕ Fin h → ℤ) : Fin h ⊕ Fin h → ZMod M := fun i => (a i : ZMod M)

def liftMod {h : ℕ} {M : ℕ} (x : Fin h ⊕ Fin h → ZMod M) : Fin h ⊕ Fin h → ℤ := fun i => ((x i).val : ℤ)

theorem reduceMod_liftMod {h M : ℕ} [NeZero M] (x : Fin h ⊕ Fin h → ZMod M) : reduceMod M (liftMod x) = x := by
  funext i
  simp [reduceMod, liftMod]

def sympTwist {h M : ℕ} {T : Type*} (g : sympSimGrp h M) (l : (Fin h ⊕ Fin h → ℤ) → T) :
    (Fin h ⊕ Fin h → ℤ) → T :=
  fun a => l (liftMod ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M a)))

def IsMultOf {h M : ℕ} (g : sympSimGrp h M) (n : ℕ) : Prop :=
  ∀ x y, omegaMod M ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x)
    ((g : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y) = n * omegaMod M x y

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HarrisTaylorSymplecticLevelFamilyUniversalProperty (b : Base D R) (N h M : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) : Prop :=
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
    (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
    ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

def SympActs {b : Base D R} {N h M : ℕ} {X : Scheme.{0}} (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (ρ : sympSimGrp h M → (X ⟶ X)) : Prop :=
  ∀ a, ρ a ≫ s = s ∧
    (∃ (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n ∧ σ (zetaAway M) = zetaAway M ^ n ∧
      ρ a ≫ s₁ = s₁ ≫ spMap σ) ∧
    ∃ m : ObjMap u u (ρ a), ∀ x, (sympTwist a lev x).left ≫ m.φ = ρ a ≫ (lev x).left

end GlobalTheory.UPel.HT
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibre

theorem one_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_push h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

theorem comp_pow_pt {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end GlobalTheory.KerKilledFibre

namespace GlobalTheory.KerKilledFibre

theorem fibreKilled_of_base : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  intro d S' _ G _ _ P _ hP _ _ _ T g A' _ _ φ φ₂ P' hpb hsq hP' hiso _ H t T' x hT' hgen
  obtain ⟨f, hf⟩ := hT'
  obtain ⟨c, hc⟩ := hgen
  let r : Spec (T.residueField t) ⟶ Spec (S'.residueField (g.base t)) := Spec.map (g.residueFieldMap t)
  have hr : r ≫ S'.fromSpecResidueField (g.base t) = T.fromSpecResidueField t ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t
  let p1 : pullback f r ⟶ T'.left := pullback.fst f r
  let p2 : pullback f r ⟶ Spec (T.residueField t) := pullback.snd f r
  let T'' : Over T := Over.mk (p2 ≫ T.fromSpecResidueField t)
  have hw : p1 ≫ T'.hom = T''.hom ≫ g := by
    show p1 ≫ T'.hom = (p2 ≫ T.fromSpecResidueField t) ≫ g
    rw [hf, ← Category.assoc, pullback.condition, Category.assoc, hr, Category.assoc]
  have hxw : (p1 ≫ x.left) ≫ G.hom = T''.hom ≫ g := by rw [Category.assoc, Over.w x]; exact hw
  let x'' : T'' ⟶ A' := Over.homMk (hpb.1.lift (p1 ≫ x.left) T''.hom hxw) (hpb.1.lift_snd _ _ _)
  have hx''φ : x''.left ≫ φ = p1 ≫ x.left := hpb.1.lift_fst _ _ _

  let Y : Over S' := Over.mk ((A' ⊗ T'').hom ≫ g)
  let a : Y ⟶ G := Over.homMk ((fst A' T'').left ≫ φ) (by
    show ((fst A' T'').left ≫ φ) ≫ G.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hpb.1.w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst A' T'')))
  let b : Y ⟶ T' := Over.homMk ((snd A' T'').left ≫ p1) (by
    show ((snd A' T'').left ≫ p1) ≫ T'.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hw, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd A' T'')))
  let m := (lift a b).left
  let ψ := (lift (snd G T' ≫ x) (fst G T')).left
  let ψ'' := (lift (snd A' T'' ≫ x'') (fst A' T'')).left
  have heq : ψ'' ≫ φ₂ = m ≫ ψ := by
    have k1 : ψ ≫ (fst G G).left = (snd G T' ≫ x).left := by rw [← Over.comp_left, lift_fst]
    have k2 : ψ'' ≫ (fst A' A').left = (snd A' T'' ≫ x'').left := by rw [← Over.comp_left, lift_fst]
    have k3 : m ≫ (snd G T').left = b.left := by rw [← Over.comp_left, lift_snd]
    have k4 : ψ ≫ (snd G G).left = (fst G T').left := by rw [← Over.comp_left, lift_snd]
    have k5 : ψ'' ≫ (snd A' A').left = (fst A' T'').left := by rw [← Over.comp_left, lift_snd]
    have k6 : m ≫ (fst G T').left = a.left := by rw [← Over.comp_left, lift_fst]
    apply Over.tensorObj_ext
    · show ψ'' ≫ φ₂ ≫ (fst G G).left = m ≫ ψ ≫ (fst G G).left
      rw [hsq.1, reassoc_of% k2, k1]
      simp only [Over.comp_left, Category.assoc]
      rw [reassoc_of% k3, hx''φ]
      show _ = ((snd A' T'').left ≫ p1) ≫ x.left
      rw [Category.assoc]
    · show ψ'' ≫ φ₂ ≫ (snd G G).left = m ≫ ψ ≫ (snd G G).left
      rw [hsq.2, reassoc_of% k5, k4, k6]
      rfl
  obtain ⟨w, hwg⟩ := hiso
  obtain ⟨c1, hc1⟩ := gen_chartPull
    (chartPullSame P (fun _ : PUnit => ψ'' ≫ φ₂) (fun _ => ψ) (fun _ => 1) m (fun _ => heq)) c hc
  obtain ⟨c2, hc2⟩ := exists_down ((isGen_iff w).1 hwg) hP hP' (φ' := fun _ : PUnit => ψ'')
    (ε := fun _ => 1) c1 hc1
  have hx'' : x'' ^ d = 1 := H T'' x'' ⟨c2, hc2⟩

  let ρ : Over.mk (T''.hom ≫ g) ⟶ T' := Over.homMk p1 hw
  have hρ : (ρ ≫ x).left = x''.left ≫ φ := hx''φ.symm
  have e1 : ((ρ ≫ x) ^ d).left = (1 : Over.mk (T''.hom ≫ g) ⟶ G).left := by
    rw [pow_left_push hpb x'' (ρ ≫ x) hρ d, hx'', one_left_push hpb T'']
  have e2 : p1 ≫ (x ^ d).left = p1 ≫ (1 : T' ⟶ G).left := by
    have := congrArg CommaMorphism.left ((comp_pow_pt ρ x d).trans
      ((Over.OverMorphism.ext e1).trans (MonObj.comp_one ρ).symm))
    exact this
  have : Flat r := inferInstance
  have : Surjective r := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi p1 := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi p1).1 e2)

end GlobalTheory.KerKilledFibre
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Extend

theorem exists_factor {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U} [GrpObj G] [GrpObj G'] [GrpObj A]
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {a : A.left ⟶ G.left} (hb : IsGrpPullback G' G f b)
    (ha : IsGrpPullback A G (j ≫ f) a) : ∃ c : A.left ⟶ G'.left, IsGrpPullback A G' j c ∧ c ≫ b = a := by
  have w : a ≫ G.hom = (A.hom ≫ j) ≫ f := by rw [Category.assoc]; exact ha.1.w
  exact ⟨hb.1.lift _ _ w, hb.cancel (ha.congr rfl (hb.1.lift_fst _ _ w).symm) (hb.1.lift_snd _ _ w),
    hb.1.lift_fst _ _ w⟩

theorem exists_end {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (e₀ : G ⟶ G) (e : A ⟶ A) (h : e.left ≫ c ≫ b = (c ≫ b) ≫ e₀.left) :
    ∃ e' : G' ⟶ G', e'.left ≫ b = b ≫ e₀.left ∧ c ≫ e'.left = e.left ≫ c := by
  have w : (b ≫ e₀.left) ≫ G.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hb.w]
  refine ⟨Over.homMk (hb.lift _ _ w) (hb.lift_snd _ _ w), hb.lift_fst _ _ w, hb.hom_ext ?_ ?_⟩
  · show (c ≫ hb.lift _ _ w) ≫ b = _
    rw [Category.assoc, hb.lift_fst, Category.assoc, h, Category.assoc]
  · show (c ≫ hb.lift _ _ w) ≫ _ = _
    rw [Category.assoc, hb.lift_snd, Category.assoc, hc, ← Category.assoc, Over.w]

theorem exists_sec {S S' U : Scheme.{0}} {G : Over S} {G' : Over S'} {A : Over U}
    {f : S' ⟶ S} {j : U ⟶ S'} {b : G'.left ⟶ G.left} {c : A.left ⟶ G'.left} (hb : IsPullback b G'.hom G.hom f)
    (hc : c ≫ G'.hom = A.hom ≫ j) (t : S ⟶ G.left) (ht : t ≫ G.hom = 𝟙 S) (w : U ⟶ A.left)
    (h : w ≫ c ≫ b = (j ≫ f) ≫ t) :
    ∃ s : S' ⟶ G'.left, s ≫ b = f ≫ t ∧ s ≫ G'.hom = 𝟙 S' ∧ ((w ≫ A.hom) ≫ j) ≫ s = w ≫ c := by
  have u : (f ≫ t) ≫ G.hom = 𝟙 S' ≫ f := by rw [Category.assoc, ht, Category.comp_id, Category.id_comp]
  have k : ((w ≫ A.hom) ≫ j) ≫ f = j ≫ f := by
    have := congrArg (· ≫ G.hom) h
    simp only [Category.assoc, ht, Category.comp_id, hb.w, reassoc_of% hc] at this
    simpa only [Category.assoc] using this
  refine ⟨hb.lift _ _ u, hb.lift_fst _ _ u, hb.lift_snd _ _ u, hb.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hb.lift_fst, ← Category.assoc, k, Category.assoc w, h]
  · rw [Category.assoc, hb.lift_snd, Category.comp_id, Category.assoc w c, hc, Category.assoc]

theorem lbIso_of_generic {O Ω : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] (H : Over (Sp O)) [GrpObj H]
    (hH : IsAbelianScheme H) {X : Scheme.{0}} {p : X ⟶ Sp Ω} {c : X ⟶ H.left}
    (hc : IsPullback c p H.hom (spMap (algebraMap O Ω))) {L L' : LB H.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso (L.pull c) (L'.pull c)) : LBIso L L' := by
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have : IsPreimmersion (spMap (algebraMap O Ω)) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have : Flat (spMap (algebraMap O Ω)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors O))
  have : IsDominant (spMap (algebraMap O Ω)) := by
    obtain ⟨_, _⟩ := (IsGenericPointHom.fractionField O Ω).quasiCompact_and_dominant
    infer_instance
  have : QuasiCompact (spMap (algebraMap O Ω)) := inferInstance
  have := hH.smooth
  have := geometricallyIntegral_of_isAbelianScheme H
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1
    (GlobalTheory.ZH.EndoExtend.pic_ext (spMap (algebraMap O Ω)) hn H (eSec H) (Over.w η[H]) ?_ ?_)
  · rw [GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _)]
    exact (GlobalTheory.DualOpen.pic_sp_local_eq_zero O (GlobalTheory.CechPic.pull (eSec H) _)).symm
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2
      (GenSpread.lbIso_pull_comp hc.isoPullback.inv hc.isoPullback_inv_fst.symm hc.isoPullback_inv_fst.symm h)

end GlobalTheory.Poinc.Extend


open GlobalTheory.Poinc.Extend in
theorem GlobalTheory.Poinc.sameAt_of_generic : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  intro O Ω R₁ R₂ M Γ _ _ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ ⟨P, a₁, a₂, h₁, h₂, l₁, l₂, hE, hx⟩
  have spc : ∀ {R : Type} [CommRing R] (f : R →+* O),
      spMap ((algebraMap O Ω).comp f) = spMap (algebraMap O Ω) ≫ spMap f := fun f => by
    rw [← Spec.map_comp]; rfl
  rw [spc] at h₁ h₂
  simp only [spc] at hx
  obtain ⟨Q₁, b₁, g₁, m₁⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₁.A.left),
      IsGrpPullback Q.A P₁.A (spMap f₁) b ∧ LBIso Q.L (P₁.L.pull b) :=
    ⟨StrictPull.polPull P₁ (spMap f₁), _, isGrpPullback_pullback _ _,
      PolBaseChange.lbIso_refl (pull_isLB P₁.isLB _)⟩
  obtain ⟨Q₂, b₂, g₂⟩ : ∃ (Q : PolAV (Sp O)) (b : Q.A.left ⟶ P₂.A.left),
      IsGrpPullback Q.A P₂.A (spMap f₂) b :=
    ⟨StrictPull.polPull P₂ (spMap f₂), _, isGrpPullback_pullback _ _⟩
  obtain ⟨c₁, k₁, rfl⟩ := exists_factor g₁ h₁
  obtain ⟨c₂, k₂, rfl⟩ := exists_factor g₂ h₂
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp O) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj : IsGenericPointHom (spMap (algebraMap O Ω)) := IsGenericPointHom.fractionField O Ω
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  have s₁ := isSemiAbelian_of_isAbelianScheme Q₁.A Q₁.isAb
  have s₂ := isSemiAbelian_of_isAbelianScheme Q₂.A Q₂.isAb
  have := s₁.smooth
  have := s₂.smooth
  have := s₁.separated
  have := s₂.separated
  obtain ⟨F, ⟨hF, eF⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₁ s₂ k₁ k₂ (𝟙 P.A)
  obtain ⟨F', ⟨-, eF'⟩, -⟩ := semiAbelianHomExtension_holds.generic_of_isGrpPullback hn hj s₂ s₁ k₂ k₁ (𝟙 P.A)
  rw [Over.id_left, Category.id_comp] at eF eF'
  let I : Q₁.A ≅ Q₂.A :=
    ⟨F, F', ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF, ← eF', Over.id_left, Category.comp_id]),
      ExtUnique.over_hom_ext_of_isPullback k₂.1 (by
        rw [Over.comp_left, ← Category.assoc, ← eF', ← eF, Over.id_left, Category.comp_id])⟩
  have : IsMonHom I.hom := hF
  have g₂' : IsGrpPullback Q₁.A P₂.A (spMap f₂) (F.left ≫ b₂) :=
    ((isGrpPullback_of_iso I).comp g₂).congr (Category.id_comp _) rfl
  refine ⟨Q₁, b₁, F.left ≫ b₂, g₁, g₂', m₁, ?_, fun E => ?_, fun x => ?_⟩
  · refine lbIso_of_generic Q₁.A Q₁.isAb k₁.1 Q₁.isLB (pull_isLB P₂.isLB _) ?_
    refine LBIso.trans (pull_isLB Q₁.isLB _) (pull_isLB P₁.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _)
      (GenSpread.lbIso_pull_of_lbIso m₁ c₁ rfl) ?_
    refine LBIso.trans (pull_isLB P₁.isLB _) P.isLB (pull_isLB (pull_isLB P₂.isLB _) _) l₁.symm ?_
    exact LBIso.trans P.isLB (pull_isLB P₂.isLB _) (pull_isLB (pull_isLB P₂.isLB _) _) l₂
      (GenSpread.lbIso_pull_pull P₂.isLB c₁ (by rw [eF, Category.assoc]))
  · obtain ⟨e, u₁, u₂⟩ := hE E
    obtain ⟨d₁, v₁, w₁⟩ := exists_end g₁.1 k₁.1.w (e₁ E) e u₁
    obtain ⟨d₂, v₂, w₂⟩ := exists_end g₂.1 k₂.1.w (e₂ E) e u₂
    have : d₁ ≫ F = F ≫ d₂ := ExtUnique.over_hom_ext_of_isPullback k₁.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, w₁, Category.assoc, ← eF, ← Category.assoc, ← eF, w₂])
    refine ⟨d₁, v₁, ?_⟩
    rw [← Category.assoc, ← Over.comp_left, this, Over.comp_left, Category.assoc, v₂, Category.assoc]
  · obtain ⟨w, u₁, u₂⟩ := hx x
    obtain ⟨d₁, v₁, z₁, w₁⟩ := exists_sec g₁.1 k₁.1.w (t₁ x).left (Over.w (t₁ x)) w u₁
    obtain ⟨d₂, v₂, z₂, w₂⟩ := exists_sec g₂.1 k₂.1.w (t₂ x).left (Over.w (t₂ x)) w u₂
    have : Surjective (w ≫ P.A.hom) :=
      ⟨fun y => ⟨y, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
    have : d₁ ≫ F.left = d₂ := ext_of_isDominant_of_isSeparated Q₂.A.hom
      (by rw [Category.assoc, Over.w, z₁, z₂]) ((w ≫ P.A.hom) ≫ spMap (algebraMap O Ω))
      (by rw [← Category.assoc, w₁, w₂, eF, Category.assoc])
    exact ⟨d₁, v₁, by rw [← Category.assoc, this, v₂]⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio

theorem exists_div_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s a b : LB.Sec (LB.LinComb L φ ε)) (U : Y.Opens) (f : Γ(Y, U))
    (hs : ∀ z ∈ U, ∀ J, Good L z J → IsUnit (sval s (𝟙 Y) z J)) :
    ∃ g : Γ(Y, U), ∀ z ∈ U, ∀ J, Good L z J →
      sval a (𝟙 Y) z J = gs (𝟙 Y) z U f * sval b (𝟙 Y) z J + gs (𝟙 Y) z U g * sval s (𝟙 Y) z J := by
  have hun : ∀ (j : K → L.ι) (y : Y), y ∈ U → y ∈ LB.wchart L φ j →
      IsUnit (gs (𝟙 Y) y (LB.wchart L φ j) (s.f j)) := fun j y hU hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    rw [e]
    exact (Units.isUnit _).mul (hs y hU J hJ)
  let W : (K → L.ι) → Y.Opens := fun j => U ⊓ LB.wchart L φ j
  have hloc : ∀ j, ∃ u : Γ(Y, W j), ∀ y ∈ W j,
      gs (𝟙 Y) y (LB.wchart L φ j) (a.f j) = gs (𝟙 Y) y U f * gs (𝟙 Y) y (LB.wchart L φ j) (b.f j) +
        gs (𝟙 Y) y (W j) u * gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) := by
    intro j
    have l₁ : W j ≤ U := inf_le_left
    have l₂ : W j ≤ LB.wchart L φ j := inf_le_right
    have hu : IsUnit ((Y.presheaf.map (homOfLE l₂).op).hom (s.f j)) :=
      Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
        (congrArg IsUnit ((gs_eq (𝟙 Y) y (W j) hy _).symm.trans (gs_res (𝟙 Y) y l₂ hy (s.f j)))).mpr
          (hun j y hy.1 hy.2)
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have key : (Y.presheaf.map (homOfLE l₂).op).hom (a.f j) =
        (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j) +
        (((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v) *
          (Y.presheaf.map (homOfLE l₂).op).hom (s.f j) := by
      rw [_root_.mul_assoc, hv]; ring
    refine ⟨((Y.presheaf.map (homOfLE l₂).op).hom (a.f j) -
          (Y.presheaf.map (homOfLE l₁).op).hom f * (Y.presheaf.map (homOfLE l₂).op).hom (b.f j)) * v, fun y hy => ?_⟩
    refine (gs_res (𝟙 Y) y l₂ hy _).symm.trans ((congrArg (gs (𝟙 Y) y (W j)) key).trans ?_)
    refine (gs_add (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 Y) y l₁ hy _) (gs_res (𝟙 Y) y l₂ hy _))
    · exact (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg _ (gs_res (𝟙 Y) y l₂ hy _))
  choose u hu using hloc
  obtain ⟨g, hg, -⟩ := Y.sheaf.existsUnique_gluing' W U (fun j => homOfLE inf_le_left) (fun y hy => by
      choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => I (φ k), hy, Set.mem_iInter.2 fun k => hI _⟩) u
    (fun j j' => fn_ext (V := W j ⊓ W j') fun y hy => by
      refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
      have e₁ := hu j y hy.1
      have e₂ := hu j' y hy.2
      rw [sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, sec_trans b (𝟙 Y) y hy.1.2 hy.2.2,
        sec_trans s (𝟙 Y) y hy.1.2 hy.2.2] at e₁
      have hc := (Units.isUnit (trF φ ε (𝟙 Y) y j j')).mul (hun j' y hy.1.1 hy.2.2)
      refine hc.mul_right_cancel ?_
      linear_combination (trF φ ε (𝟙 Y) y j j').val * e₂ - e₁)
  refine ⟨g, fun z hz J hJ => ?_⟩
  have hm : z ∈ W (fun k => J (𝟙 Y ≫ φ k)) := ⟨hz, hJ.mem φ (𝟙 Y)⟩
  have e : gs (𝟙 Y) z U g = gs (𝟙 Y) z (W _) (u (fun k => J (𝟙 Y ≫ φ k))) :=
    (gs_res (𝟙 Y) z inf_le_left hm g).symm.trans (congrArg (gs (𝟙 Y) z (W _)) (hg _))
  rw [e]
  exact hu _ z hm

theorem exists_isRem : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (N : ℕ) (α : Q.X) (σ σ' σp σp' : Q.SecB N α) (U : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio Q σ σ' U f → ∃ g : Γ(Q.P.A.left, U), GlobalTheory.HeatRatio.IsRem Q σ' σp σp' U f g := by
  intro R _ _ Q N α σ σ' σp σp' U f h
  exact exists_div_sec Q.P.isLB σ' σp σp' U f fun z hz J hJ => (h z hz J hJ).1

end GlobalTheory.HeatRatio
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.isTwistedThetaValue_pullback_base_change : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T), IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_pull | exact GlobalTheory.UPoinc.USum.isTwVal_pull | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_pull <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.isTwistedThetaValue_translate_orthogonal_torsion : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_transl | exact GlobalTheory.UPoinc.USum.isTwVal_transl | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_transl <;> assumption)
end
