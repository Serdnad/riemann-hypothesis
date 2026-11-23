module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegFibreFinite

open GlobalTheory.CechPic GlobalTheory.SiegelPull GlobalTheory.ZM.SiegPull

theorem finite_torsion {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {n : ℕ} (hn : 1 ≤ n) : Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1} := by
  have := hB.smooth
  have := GlobalTheory.MulFiniteAny.isFinite_mulA K B hB n hn
  have := GlobalTheory.TorsionDivisible.finite_fibre_points (Out.mulA B n) 1
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ Out.mulA B n = 1) fun x => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id])

theorem finite_over_point {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (hamp : Out.RelAmple A L) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (z : Sp K ⟶ S) (m : Pic B.left) :
    Set.Finite {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} := by
  rcases Set.eq_empty_or_nonempty {φ : B.left ⟶ A.left | IsGrpPullback B A z φ ∧ pull φ (cls L hL) = m} with
    h | ⟨φ₁, h₁, -⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.AmpleFiniteOrder.exists_ge_cast_ne_zero K 3
  have := hB.comm
  obtain ⟨hfin, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K B hB N hNK
  let U : Over (Sp K) := 𝟙_ (Over (Sp K))
  have hfin' : Finite {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1} := by
    refine Finite.of_surjective (fun x : {x : U ⟶ B // x ^ N = 1} =>
      (⟨pushHom h₁ U x.1, by rw [← map_pow, x.2, map_one]⟩ : {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})) ?_
    rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := push_surjective h₁ U g
    exact ⟨⟨x, push_injective h₁ U (by rw [map_pow, hg, map_one])⟩, rfl⟩
  refine Set.finite_coe_iff.1 ?_
  refine Finite.of_injective (β := {x : U ⟶ B // x ^ N = 1} → {g : Over.mk (U.hom ≫ z) ⟶ A // g ^ N = 1})
    (fun φ x => ⟨pushHom φ.2.1 U x.1, by rw [← map_pow, x.2, map_one]⟩) ?_
  rintro ⟨φ, h, hc⟩ ⟨φ', h', hc'⟩ e
  have e₀ : ∀ x : U ⟶ B, x ^ N = 1 → x.left ≫ φ = x.left ≫ φ' := fun x hx =>
    congrArg (fun q => q.1.left) (congrFun e ⟨x, hx⟩)
  obtain ⟨σ, hσ, eσ⟩ := GlobalTheory.SiegRigid.exists_aut h h'
  have hu : IsMonHom (σ.hom * (𝟙 B)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨ψ, hψ, eψ⟩ := hdiv _ hu fun x hx => by
    have : x ≫ σ.hom = x := Over.OverMorphism.ext (h'.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, eσ]; exact e₀ x hx) (by rw [Over.w, Over.w]))
    rw [MonObj.comp_mul, GrpObj.comp_inv, this, Category.comp_id, mul_inv_cancel]
  refine Subtype.ext (GlobalTheory.SiegRigid.eq_of_field hL hamp hB h h' (hc.trans hc'.symm) hN hNK fun Ω _ _ t x hx => ?_)
  have e₁ : x ≫ (σ.hom * (𝟙 B)⁻¹) = 1 := by
    rw [eψ, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp]
  rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, mul_inv_eq_one] at e₁
  change x.left ≫ φ = x.left ≫ φ'
  rw [← eσ, ← Category.assoc, ← Over.comp_left, e₁]

theorem pull_diag {S S' : Scheme.{0}} {A : Over S} {B : Over S'} {φ : B.left ⟶ A.left}
    {φ₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂) (m : Pic (A ⊗ A).left) :
    pull φ (pull (lift (𝟙 A) (𝟙 A)).left m) = pull (lift (𝟙 B) (𝟙 B)).left (pull φ₂ m) := by
  have e : (lift (𝟙 B) (𝟙 B)).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq hs (T := Over.mk (φ ≫ A.hom)) (T' := B) (𝟙 B.left) (𝟙 B) (𝟙 B)
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  rw [← pull_comp, ← pull_comp, e]

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

theorem point_eq (F : SFam g n ζ) {R : Type} [CommRing R] [IsLocalRing R] {B : Over (Sp R)} [GrpObj B]
    {x x' : Sp R ⟶ F.X} {φ φ' : B.left ⟶ F.univ.A.left} {φ₂ φ₂' : (G2 B).left ⟶ (G2 F.univ.A).left}
    (hs : x ≫ F.s = x' ≫ F.s) (h : IsGrpPullback B F.univ.A x φ) (h' : IsGrpPullback B F.univ.A x' φ')
    (q : IsSquare φ φ₂) (q' : IsSquare φ' φ₂')
    (hc : pull φ₂ (cls F.univ.P F.univ.isLB) = pull φ₂' (cls F.univ.P F.univ.isLB))
    (hl : ∀ a, SiegelPull.secPull h (F.univ.lev a) = SiegelPull.secPull h' (F.univ.lev a)) : x = x' := by
  obtain ⟨c, hc₀⟩ := (GlobalTheory.siegPre_pullback g n o ζ F.X (Sp R) F.s _ x F.univ rfl).1
  refine F.inj R x x' _ c hs hc₀ ?_
  obtain ⟨χ, χ₂, k, r, w, l⟩ := hc₀
  obtain ⟨e, he, ee⟩ := grpPullback_iso k h
  have k' : IsGrpPullback c.A F.univ.A x' (e.hom.left ≫ φ') :=
    ((isGrpPullback_of_iso e).comp h').congr (Category.id_comp _) rfl
  refine ⟨e.hom.left ≫ φ', (e.hom ⊗ₘ e.hom).left ≫ φ₂', k', GlobalTheory.ZM.SiegPull.isSquare_comp (isSquare_tensor e.hom) q', ?_,
    fun a => ?_⟩
  · have e₂ : χ₂ = (e.hom ⊗ₘ e.hom).left ≫ φ₂ := isSquare_unique r (GlobalTheory.ZM.SiegPull.isSquare_comp (isSquare_tensor e.hom) q) ee.symm
    refine (cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).1 ?_
    rw [(cls_eq_iff c.isLB (pull_isLB F.univ.isLB _)).2 w, cls_pull F.univ.isLB, cls_pull F.univ.isLB, e₂, pull_comp,
      pull_comp, hc]
  · have e₃ : c.lev a ≫ e.hom = SiegelPull.secPull h (F.univ.lev a) := Over.OverMorphism.ext (h.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, ee, SiegelPull.secPull_left]; exact l a) (by rw [Over.w, Over.w]))
    rw [← Category.assoc, ← Over.comp_left, e₃, hl, SiegelPull.secPull_left]

theorem finite_points (F : SFam g n ζ) (hn : 1 ≤ n) {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) (s : Sp K ⟶ Sp o) (m : Pic (G2 B).left) :
    Set.Finite {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} := by
  have := finite_torsion B hB hn
  have := hB.comm
  refine Set.finite_coe_iff.1 ?_
  have H := fun x : {x : Sp K ⟶ F.X | x ≫ F.s = s ∧ ∃ (φ : B.left ⟶ F.univ.A.left)
      (φ₂ : (G2 B).left ⟶ (G2 F.univ.A).left), IsGrpPullback B F.univ.A x φ ∧ IsSquare φ φ₂ ∧
        pull φ₂ (cls F.univ.P F.univ.isLB) = m} => x.2.2
  choose φ φ₂ h q hc using H
  refine Finite.of_injective (β := (Fin g ⊕ Fin g) → {y : 𝟙_ (Over (Sp K)) ⟶ B // y ^ n = 1})
    (fun x i => ⟨SiegelPull.secPull (h x) (F.univ.lev (Pi.single i 1)), push_injective (h x) _ (by
      rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, F.univ.lev_tors, MonObj.comp_one])⟩) ?_
  intro x x' e
  refine Subtype.ext (point_eq F (x.2.1.trans x'.2.1.symm) (h x) (h x') (q x) (q x') ((hc x).trans (hc x').symm) ?_)
  let p := fun y => (AddMonoidHom.mk' (fun a => Additive.ofMul (SiegelPull.secPull (h y) (F.univ.lev a))) fun a b => by
      rw [← ofMul_mul]
      exact congrArg _ (push_injective (h y) _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', F.univ.lev_add, MonObj.comp_mul])) :
    (Fin g ⊕ Fin g → ℤ) →+ Additive (𝟙_ (Over (Sp K)) ⟶ B))
  have hp : p x = p x' := AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int
    (congrArg (fun z => Additive.ofMul z.1) (congrFun e i))
  exact fun a => congrArg Additive.toMul (DFunLike.congr_fun hp a)

theorem finite_identifications : ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ'), 1 ≤ n' → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B] (x₀ : Sp K ⟶ F'.X) (φ₀ : B.left ⟶ F'.univ.A.left) (φ₀₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), IsGrpPullback B F'.univ.A x₀ φ₀ → IsSquare φ₀ φ₀₂ → ∀ p₀ : Sp K ⟶ B.left, Set.Finite {P' : Sp K ⟶ F'.univ.A.left | ∃ (x' : Sp K ⟶ F'.X) (φ : B.left ⟶ F'.univ.A.left) (φ₂ : (G2 B).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = x₀ ≫ F'.s ∧ IsGrpPullback B F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ P' = p₀ ≫ φ} := by
  intro o _ ζ g n F hn K _ _ B _ x₀ φ₀ φ₀₂ h₀ _ p₀
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback F.univ.ab h₀
  let m := pull φ₀₂ (cls F.univ.P F.univ.isLB)
  have h₁ := finite_points F hn hB (x₀ ≫ F.s) m
  have h₂ := fun x => finite_over_point (pull_isLB F.univ.isLB _) F.princ.1 hB x (pull (lift (𝟙 B) (𝟙 B)).left m)
  refine ((h₁.biUnion fun x _ => h₂ x).image (p₀ ≫ ·)).subset ?_
  rintro _ ⟨x, φ, φ₂, hs, h, q, w, rfl⟩
  have e : pull φ₂ (cls F.univ.P F.univ.isLB) = m := by
    have := (cls_eq_iff (pull_isLB F.univ.isLB _) (pull_isLB F.univ.isLB _)).2 w
    rw [cls_pull F.univ.isLB, cls_pull F.univ.isLB] at this
    exact this.symm
  refine ⟨φ, Set.mem_biUnion (x := x) ⟨hs, φ, φ₂, h, q, e⟩ ⟨h, ?_⟩, rfl⟩
  rw [← e, ← pull_diag q]
  exact congrArg _ (cls_pull F.univ.isLB _ _)

end GlobalTheory.SiegFibreFinite
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.FieldDescent

open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.GenSpread

variable {K Ω : Type} [Field K] [Field Ω] {l : K →+* Ω} {D₁ D₂ : DegPre K} {D : DegPre Ω}

theorem lbIso_of_common_pull (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) {Φ : D₂.P.A.left ⟶ D₁.P.A.left}
    (hΦ : proj h₂ ≫ Φ = proj h₁) : LBIso D₂.P.L (D₁.P.L.pull Φ) := by
  have e : pullback.fst D₂.P.A.hom (specOf l) = h₂.e.inv.left ≫ proj h₂ := by
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact (Category.id_comp _).symm
  have e' : pullback.fst D₂.P.A.hom (specOf l) ≫ Φ = h₂.e.inv.left ≫ proj h₁ :=
    (congrArg (· ≫ Φ) e).trans ((Category.assoc _ _ _).trans (congrArg (h₂.e.inv.left ≫ ·) hΦ))
  exact PolIsoDescent.lbIso_descend globalFns_holds (specOf l) D₂.P.A D₂.P.isAb D₂.P.isLB (pull_isLB D₁.P.isLB Φ)
    (LBIso.trans (pull_isLB D₂.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
      (lbIso_pull_of_lbIso ⟨h₂.w, h₂.w_gen⟩ h₂.e.inv.left e).symm
      (LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB D₁.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
        (lbIso_pull_of_lbIso ⟨h₁.w, h₁.w_gen⟩ h₂.e.inv.left e') (lbIso_pull_pull D₁.P.isLB _ rfl)))

theorem om_eq (h₁ : IsPullDeg l D₁ D) {ψ : D.P.A.left ⟶ D₁.P.A.left} (v : LB.Iso D.P.L (D₁.P.L.pull ψ))
    (hψ : ψ = proj h₁) (gv : PGen v)
    (pv : PMaps v (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap l))
    {Z : Scheme.{0}} (z : Z) (J J') (q : Z ⟶ D.P.A.left) : om v z J J' q = om h₁.w z J J' q := by
  subst hψ
  rw [iso_unique_of_rig globalFns_holds D.P.A D.P.isAb D.P.isLB D₁.P.isLB ((isGen_iff v).2 gv) h₁.w_gen
    ((maps_iff v _ (fun _ => eSec D₁.P.A) _ D.rig D₁.rig (specOf l) _
      (rigPull_le (proj h₁) (specOf l) h₁.he D₁.P.L) (fun _ => rfl)).2 pv) h₁.w_rig]

end GlobalTheory.FieldDescent


open GlobalTheory.PsiEvenPull (proj) in
theorem GlobalTheory.nonempty_isPullDeg_id_of_common_pull : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  intro K Ω _ _ l D₁ D₂ D h₁ h₂ φ hm hφ
  have hΦ : proj h₂ ≫ φ.hom.left = proj h₁ := (Category.assoc _ _ _).trans hφ
  have hs : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id (CommRingCat.of K)
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id K)) φ.hom.left :=
    (Geo.Tor.isGrpPullback_of_iso φ).congr hs.symm rfl
  have he : eSec D₂.P.A ≫ φ.hom.left = spMap (RingHom.id K) ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨w, gw', rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id K)) D₁.P.A D₂.P.A φ.hom.left he
    ⟨D₁.P.L, D₁.rig, D₁.P.isLB, D₁.rig_gen⟩ ⟨D₂.P.L, D₂.rig, D₂.P.isLB, D₂.rig_gen⟩
    (FieldDescent.lbIso_of_common_pull h₁ h₂ hΦ)
  have pw' := (isGen_iff w).1 gw'
  have p₂ := (isGen_iff h₂.w).1 h₂.w_gen
  have r₀ := (maps_iff w _ (fun _ => eSec D₁.P.A) _ D₂.rig D₁.rig (spMap (RingHom.id K)) _
    (rigPull_le φ.hom.left (spMap (RingHom.id K)) he D₁.P.L) (fun _ => rfl)).1 rw'
  obtain ⟨v, T⟩ := exists_comp D₂.P.isLB w h₂.w pw' p₂ D₁.P.isLB D.P.isLB
  have r₂ := T.pmaps_comp D₂.P.isLB (fun _ => h₂.he) r₀ (FieldPull.pmaps_rig h₂)
  rw [← spMap_comp] at r₂
  have hom := fun {Z : Scheme.{0}} (z : Z) J J' q =>
    FieldDescent.om_eq h₁ v hΦ (T.pgen_comp D₂.P.isLB pw' p₂) r₂ z J J' q
  obtain ⟨f₁, f₂⟩ := PolIsoDescent.flat_surjective (spMap l)
  have : Epi (spMap l) := Flat.epi_of_flat_of_surjective _
  let xe : D₂.X ≃+ D₁.X := h₂.xe.symm.trans h₁.xe
  have hxe : ∀ y, xe (h₂.xe y) = h₁.xe y := fun y => congrArg h₁.xe (h₂.xe.symm_apply_apply y)
  have hc : ∀ x, (D₂.c x).left ≫ φ.hom.left = spMap (RingHom.id K) ≫ (D₁.c (xe x)).left := fun x => by
    obtain ⟨y, rfl⟩ := h₂.xe.surjective x
    rw [hxe, hs]
    refine Eq.trans ?_ (Category.id_comp _).symm
    refine (cancel_epi (spMap l)).1 ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ φ.hom.left) (h₂.c_pr y).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((D.c y).left ≫ ·) hΦ).trans (h₁.c_pr y)))
  have si : jK K ≫ spMap (RingHom.id K) = genMap (RingHom.id K).injective ≫ jK K :=
    (Category.id_comp _).symm.trans (fracMap_sq (RingHom.id K).injective)
  have si' : genMap (RingHom.id K).injective ≫ jK K = jK K :=
    si.symm.trans ((congrArg (jK K ≫ ·) hs).trans (Category.comp_id _))
  have sl := fracMap_sq l.injective
  obtain ⟨hD, -⟩ := FieldPull.exists_isPullDeg_of_val (RingHom.id K) D₁ D₂ gp w pw' r₀ xe hc
    (fun x z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨y, rfl⟩ := h₂.xe.surjective x
      have hx : D₂.xK (h₂.xe y) ≫ φ.hom.left = genMap (RingHom.id K).injective ≫ D₁.xK (xe (h₂.xe y)) := by
        show (jK K ≫ (D₂.c _).left) ≫ _ = _ ≫ jK K ≫ (D₁.c _).left
        rw [Category.assoc, hc, ← Category.assoc, si, Category.assoc]
      obtain ⟨a, ha, va⟩ := exists_down_om gw' D₁.P.isLB D₂.P.isLB (K := PUnit) (φ' := fun _ => D₂.xK (h₂.xe y))
        (genMap (RingHom.id K).injective) (fun _ => hx) (D₁.psi (xe (h₂.xe y))) (D₁.psi_gen _)
      obtain ⟨k₁, k₂⟩ := PolIsoDescent.flat_surjective (F := FractionRing Ω) (C := FractionRing K) (genMap l.injective)
      have ea := PsiEvenPull.val_eq_of_app_injective D₂.P.isLB (fun _ _ _ => rfl) (genMap l.injective)
        (fun U => FunDescent.app_injective (genMap l.injective) U) ha (D₂.psi_gen (h₂.xe y)) (fun u I₂ hI₂ => by
          obtain ⟨I₁, hI₁⟩ := DegPull.exists_good' D₁.P.isLB u
          obtain ⟨I, hI⟩ := DegPull.exists_good' D.P.isLB u
          have v₂ := psi_val h₂ _ _ sl hI₂ hI y
          have v₁ := psi_val h₁ (genMap l.injective ≫ genMap (RingHom.id K).injective) _
            (sl.trans ((congrArg (_ ≫ ·) si'.symm).trans (Category.assoc _ _ _).symm)) hI₁ hI y
          have v₀ := va _ (genMap l.injective) u I₁ I₂ hI₁ hI₂
          have hq : genMap l.injective ≫ D₂.xK (h₂.xe y) = (𝟙 _ ≫ D.xK y) ≫ proj h₂ := by
            show _ ≫ jK K ≫ (D₂.c _).left = (𝟙 _ ≫ jK Ω ≫ (D.c y).left) ≫ _
            rw [← Category.assoc, ← sl]
            simp only [Category.assoc]
            exact congrArg (fun q => 𝟙 _ ≫ jK Ω ≫ q) (h₂.c_pr y).symm
          have t : om v u I₁ I (𝟙 _ ≫ D.xK y) =
              om w u I₁ I₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂) * om h₂.w u I₂ I (𝟙 _ ≫ D.xK y) := by
            rw [om, om, om, Category.assoc (𝟙 _ ≫ D.xK y)]
            exact T _ _ u _ _ _ (hI₁ ((𝟙 _ ≫ D.xK y) ≫ proj h₂ ≫ φ.hom.left)) (hI₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂)) (hI _)
          rw [Fintype.prod_unique, zpow_neg_one, hq, hxe, v₁, ← hom, t, mul_inv, _root_.mul_assoc] at v₀
          exact (mul_left_cancel v₀).symm.trans v₂.symm) _ (𝟙 _) z J₂ hJ₂
      have v₀ := va _ (𝟙 _) z J₁ J₂ hJ₁ hJ₂
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp, ea] at v₀
      exact v₀)
  exact ⟨hD⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompGen

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem nonempty_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    Nonempty (IsPullDeg (j.comp i) D D'') := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, -⟩ := exists_isPullDeg_of_valW D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r⟩

end GlobalTheory.PullDegCompGen

namespace GlobalTheory.Mum

theorem nonempty_isPullDeg_comp_of_injective : ∀ (R R' R'' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] (φ : R →+* R') (φ' : R' →+* R'') (D : DegPre R) (D' : DegPre R') (D'' : DegPre R''), Function.Injective φ' → Nonempty (IsPullDeg φ D D') → Nonempty (IsPullDeg φ' D' D'') → Nonempty (IsPullDeg (φ'.comp φ) D D'') := by
  intro R R' R'' _ _ _ _ _ _ φ φ' D D' D'' hj ⟨p⟩ ⟨q⟩
  exact GlobalTheory.PullDegCompGen.nonempty_isPullDeg_comp hj p q

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenEqual

theorem key {X₁ X₂ X₃ XE S₁ S₂ S₃ SE : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {LE : LB XE}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) (hLE : LE.IsLB)
    (Fp : X₃ ⟶ X₁) (Φ : X₃ ⟶ X₂) (κ : XE ⟶ X₃)
    (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂) (e₃ : S₃ ⟶ X₃) (eE : SE ⟶ XE)
    (t₁ : S₃ ⟶ S₁) (t₂ : S₃ ⟶ S₂) (sE : SE ⟶ S₃) (pE : XE ⟶ SE) (hpE : eE ≫ pE = 𝟙 _)
    (hsurj : Function.Surjective pE.appTop.hom) (hc : eE ≫ κ = sE ≫ e₃)
    (r₁ : LB.Gen (L₁.pull e₁)) (r₂ : LB.Gen (L₂.pull e₂)) (r₃ : LB.Gen (L₃.pull e₃)) (rE : LB.Gen (LE.pull eE))
    (wp : LB.Iso L₃ (L₁.pull Fp)) (w : LB.Iso L₃ (L₂.pull Φ)) (F₁ : XE ⟶ X₁) (F₂ : XE ⟶ X₂) (h₁ : κ ≫ Fp = F₁) (h₂ : κ ≫ Φ = F₂) (u₁ : LB.Iso LE (L₁.pull F₁))
    (u₂ : LB.Iso LE (L₂.pull F₂)) (gp : PGen wp) (gw' : PGen w) (g₁ : PGen u₁) (g₂ : PGen u₂)
    (mp : PMaps wp (K := PUnit) (fun _ => e₃) (fun _ => e₁) (fun _ => 1) r₃ r₁ t₁)
    (mw : PMaps w (K := PUnit) (fun _ => e₃) (fun _ => e₂) (fun _ => 1) r₃ r₂ t₂)
    (m₁ : PMaps u₁ (K := PUnit) (fun _ => eE) (fun _ => e₁) (fun _ => 1) rE r₁ (sE ≫ t₁))
    (m₂ : PMaps u₂ (K := PUnit) (fun _ => eE) (fun _ => e₂) (fun _ => 1) rE r₂ (sE ≫ t₂))
    (Z : Scheme.{0}) (f : Z ⟶ XE) (z : Z) (j : L₂.ι) (i : L₃.ι) (k : LE.ι) (l : L₁.ι)
    (hj : F₂ (f z) ∈ L₂.U j) (hi : κ (f z) ∈ L₃.U i) (hk : f z ∈ LE.U k) (hl : F₁ (f z) ∈ L₁.U l) :
    gw w (f ≫ κ) z j i * (gw wp (f ≫ κ) z l i)⁻¹ = gw u₂ f z j k * (gw u₁ f z l k)⁻¹ := by
  subst h₁ h₂
  obtain ⟨v, Tv⟩ := exists_cancel hL₁ wp u₁ gp g₁ hL₃ hLE
  have gv := Tv.pgen_cancel hL₁ gp g₁
  have rv := Tv.pmaps_cancel hL₁ (fun _ => hc) mp m₁
  obtain ⟨u, Tu⟩ := exists_comp hL₃ w v gw' gv hL₂ hLE
  have gu := Tu.pgen_comp hL₃ gw' gv
  have ru := Tu.pmaps_comp hL₃ (fun _ => hc) mw rv
  have e := GlobalTheory.OverMove.gw_eq_of_pmaps hL₂ hLE pE eE hpE hsurj rfl gu g₂ rfl ru m₂ f z j k
  rw [← e, Tu Z f z j i k hj hi hk, Tv Z f z l i k hl hi hk]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genequal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ hκp hκΦ w hw hr Z f z j i k l hj hi hk hl
  have hs : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have m₁ := GlobalTheory.FieldPull.pmaps_rig q₁
  have m₂ := GlobalTheory.FieldPull.pmaps_rig q₂
  rw [hs] at m₁ m₂
  exact key D₁.P.isLB D₂.P.isLB D₃.P.isLB E.P.isLB (GlobalTheory.PsiEvenPull.proj p) Φ κ (eSec D₁.P.A) (eSec D₂.P.A)
    (eSec D₃.P.A) (eSec E.P.A) (spMap ρ) (spMap ρ) (spMap (algebraMap R' (FractionRing R'))) E.P.A.hom
    (Over.w η[E.P.A]) (GlobalTheory.globalFns_holds _ E.P.A E.P.isAb).2 (cubeMapOf hκ).e_comm D₁.rig D₂.rig D₃.rig E.rig
    p.w w _ _ hκp hκΦ q₁.w q₂.w ((isGen_iff _).1 p.w_gen) hw ((isGen_iff _).1 q₁.w_gen) ((isGen_iff _).1 q₂.w_gen)
    (GlobalTheory.FieldPull.pmaps_rig p) hr m₁ m₂ Z f z j i k l hj hi hk hl

end GlobalTheory.GenEqual
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

theorem _root_.GlobalTheory.T.nonempty_pullDeg_id_of_common_fieldExtension : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  first | exact @GlobalTheory.nonempty_isPullDeg_id_of_common_pull | exact GlobalTheory.nonempty_isPullDeg_id_of_common_pull | (intros; apply GlobalTheory.nonempty_isPullDeg_id_of_common_pull <;> assumption)

end
end
