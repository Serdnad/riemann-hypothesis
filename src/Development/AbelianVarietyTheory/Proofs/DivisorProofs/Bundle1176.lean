module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.TrNum

section
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')

theorem img_mul (g h : N.Gt) : I.img (g * h) = I.img g * I.img h :=
  ((I.rel_iff _ _).1 ((I.rel_img g).mul (I.rel_img h))).symm

theorem img_pow (g : N.Gt) (n : ℕ) : I.img (g ^ n) = I.img g ^ n :=
  ((I.rel_iff _ _).1 ((I.rel_img g).pow n)).symm

theorem img_io (y : N.X) : I.img (N.io y) = N'.io (I.e y) :=
  ((I.rel_iff _ _).1 (I.rel_io y)).symm

def imgQ {k : ℕ} (p : N.QT k) : N'.QT k :=
  ⟨(Multiplicative.ofAdd (I.e p.1.1.toAdd), I.img p.1.2), by
    have h : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
    change I.img p.1.2 ^ k = N'.io (I.e p.1.1.toAdd)
    rw [← img_pow, h, img_io]⟩

theorem imgQ_mul {k : ℕ} (p q : N.QT k) : imgQ I (p * q) = imgQ I p * imgQ I q :=
  Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add I.e p.1.1.toAdd q.1.1.toAdd)) (img_mul I p.1.2 q.1.2))

theorem qEq_imgQ (hi : Function.Injective I.img) {k : ℕ} (p q : N.QT k) :
    N'.QEq (imgQ I p) (imgQ I q) ↔ N.QEq p q := by
  constructor
  · rintro ⟨z, h1, h2⟩
    obtain ⟨z, rfl⟩ := I.e.surjective z
    refine ⟨z, I.e.injective ?_, hi ?_⟩
    · rw [map_add (f := _), map_nsmul]; exact h1
    · rw [img_mul, img_io]; exact h2
  · rintro ⟨z, h1, h2⟩
    refine ⟨I.e z, ?_, ?_⟩
    · change I.e q.1.1.toAdd = I.e p.1.1.toAdd + k • I.e z
      rw [h1, map_add (f := _), map_nsmul]
    · change I.img q.1.2 = I.img p.1.2 * N'.io (I.e z)
      rw [h2, img_mul, img_io]

theorem imgQ_surjective (hi : Function.Bijective I.img) {k : ℕ} : Function.Surjective (imgQ I (k := k)) := by
  intro p'
  obtain ⟨g, hg⟩ := hi.2 p'.1.2
  have h : p'.1.2 ^ k = N'.io p'.1.1.toAdd := p'.2
  refine ⟨⟨(Multiplicative.ofAdd (I.e.symm p'.1.1.toAdd), g), ?_⟩, Subtype.ext (Prod.ext ?_ hg)⟩
  · change g ^ k = N.io (I.e.symm p'.1.1.toAdd)
    apply hi.1
    rw [img_pow, img_io, hg, h, AddEquiv.apply_symm_apply]
  · change Multiplicative.ofAdd (I.e (I.e.symm p'.1.1.toAdd)) = p'.1.1
    rw [AddEquiv.apply_symm_apply]; rfl

def formImg {k : ℕ} (β : N.Form k) : N'.Form k where
  be := β.be.compl₁₂ I.e.symm.toIntLinearEquiv.toLinearMap I.e.symm.toIntLinearEquiv.toLinearMap
  symm y z := β.symm _ _
  pos y hy := β.pos (I.e.symm y) (fun h => hy (by simpa using congrArg I.e h))
  dvd y z := β.dvd _ _

end

variable {F F' : Type} [Field F] [Field F'] {e : F ≃+* F'} {N : NumD F} {N' : NumD F'} (I : NumD.Hom (e : F →+* F') N N')

theorem units_bij (e : F ≃+* F') : Function.Bijective (Units.map (e : F →+* F').toMonoidHom) :=
  (Units.mapEquiv e.toMulEquiv).bijective

theorem img_bijective (hφ : Function.Bijective I.φ) (hh : ∀ x, I.h x = 1) : Function.Bijective I.img := by
  have hu := units_bij e
  constructor
  · intro g g' h
    have a := I.rel_img g
    have b := I.rel_img g'
    rw [h] at a
    refine NumD.Gt.ext (hφ.1 (a.1.symm.trans b.1)) (funext fun χ => hu.1 ?_)
    have a2 := a.2 χ
    have b2 := b.2 χ
    simp only [hh, _root_.mul_one] at a2 b2
    exact a2.symm.trans b2
  · intro g'
    obtain ⟨b, hb⟩ := hφ.2 g'.b
    choose s hs using fun χ => hu.2 (g'.s (I.e χ))
    refine ⟨⟨b, s, fun χ χ' => hu.1 ?_⟩, ((I.rel_iff _ _).1 ⟨hb.symm, fun χ => ?_⟩).symm⟩
    · have a := I.θ_eq (N.c χ) (N.c χ') b
      simp only [hh, _root_.mul_one] at a
      rw [map_mul, map_mul, hs, hs, hs, ← a, ← I.c_eq, ← I.c_eq, hb, map_add (f := _)]
      exact g'.mult _ _
    · simp only [hh, _root_.mul_one]
      exact (hs χ).symm

theorem transport : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  intro F F' _ _ e N N' I hφ hh hl
  have hi := img_bijective I hφ hh
  have hu := units_bij e
  refine ⟨fun k β => ⟨formImg I β, fun a b => ?_⟩, fun m g hm ζ q hq => ⟨fun a => imgQ I (q a), ?_, ?_⟩⟩
  · change β.be (I.e.symm (I.e a)) (I.e.symm (I.e b)) = _
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    refine ⟨h1.map_of_injective hu.1, fun a b => ?_, fun a b h => h3 a b ((qEq_imgQ I hi.1 _ _).1 h), fun p => ?_,
      fun i j => ?_⟩
    · rw [← imgQ_mul]; exact (qEq_imgQ I hi.1 _ _).2 (h2 a b)
    · obtain ⟨p, rfl⟩ := imgQ_surjective I hi p
      obtain ⟨a, ha⟩ := h4 p
      exact ⟨a, (qEq_imgQ I hi.1 _ _).2 ha⟩
    · rw [I.wp_eq (q (Pi.single i 1)) (q (Pi.single j 1)) _ _ rfl (I.rel_img _) rfl (I.rel_img _), h5, map_zpow]
  · rintro a f f' ⟨h1, h2⟩ hf
    refine ⟨fun h' χ => ?_, fun α hα x => ?_⟩
    · obtain ⟨h, rfl⟩ := hi.2 h'
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      rw [I.evT_eq hm (q a) _ rfl (I.rel_img _) χ h _ (I.rel_img _), ← h1]
      have r := (I.rel_img h).2 ((q a).1.1.toAdd + m • χ)
      simp only [hh, _root_.mul_one] at r
      have t : (imgQ I (q a)).1.1.toAdd + m • I.e χ = I.e ((q a).1.1.toAdd + m • χ) := by
        rw [map_add (f := _), map_nsmul]; rfl
      rw [t, r, (I.rel_img h).1, hf, hl, hh]
      simp
    · obtain ⟨α, rfl⟩ := I.e.surjective α
      obtain ⟨x, rfl⟩ := hφ.2 x
      rw [hf, h2 α (fun χ h => hα (I.e χ) (by rw [h, map_add (f := _), map_nsmul]; rfl)), map_zero]

end GlobalTheory.MBLow.TrNum
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a := by
  first | exact @GlobalTheory.Pinch.Semiloc.exists_locGen_near_finite | exact GlobalTheory.Pinch.Semiloc.exists_locGen_near_finite | (intros; apply GlobalTheory.Pinch.Semiloc.exists_locGen_near_finite <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

theorem _root_.GlobalTheory.T.exists_nhds_characterUnit_kernel_action : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∀ y : (A' ⊗ T).left, ∃ V : (A' ⊗ T).left.Opens, y ∈ V ∧ ∃ e : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ V)ˣ, ∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)) (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)), res h₁ (pullU (actMap i T).left _ e) = res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ e) := by
  first | exact @GlobalTheory.CharKer.exists_nhds_charUnit | exact GlobalTheory.CharKer.exists_nhds_charUnit | (intros; apply GlobalTheory.CharKer.exists_nhds_charUnit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.finrank_killed_eq_of_equal_multiplicities : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  first | exact @GlobalTheory.RepCount.finrank_inf_killed_eq | exact GlobalTheory.RepCount.finrank_inf_killed_eq | (intros; apply GlobalTheory.RepCount.finrank_inf_killed_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  first | exact @GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed | exact GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed | (intros; apply GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates

theorem exists_eigEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] {a : OAct O G} {a' : OAct O G'}
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R : Type} [CommRing R] (x : Sp R ⟶ S')
    (x' : Sp R ⟶ S) (hx : x' = x ≫ f) :
    ∃ e : (epsAt x ⟶ G') ≃ (epsAt x' ⟶ G), (∀ v, (e v).left = v.left ≫ φ) ∧
      ∀ (χ : O →+* R) (n : ℕ) (v : Fin n → (epsAt x ⟶ G')),
        IsEigenBasis a' x χ v ↔ IsEigenBasis a x' χ (fun i => e (v i)) := by
  subst hx
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsAt x ⟶ G'), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  refine ⟨e.toEquiv, he, fun χ n v => ?_⟩
  have hP : ∀ v : epsAt x ⟶ G', IsEigenTangent a' x χ v ↔ IsEigenTangent a (x ≫ f) χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin n → (epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin n → R) (w : epsAt x ⟶ G'), IsCombination x c (fun i => (v i).left) w ↔
      IsCombination (x ≫ f) c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_eigenBasis_sameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) :
    ∃ v : Fin n → (epsAt ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _) ⟶ Y.t.G),
      IsEigenBasis Y.t.act _ (chr c τ (algebraMap c.F S)) v ∧
      ∀ i : Fin n, ∃ j : Fin (Dw.mult τ), (j : ℕ) = i ∧ SameVec Y y (y.u τ j) (v i).left := by
  subst hn
  obtain ⟨e₀, he₀, hb₀⟩ := exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act (ptF y) y.x
    (pullback.lift_fst _ _ _).symm
  obtain ⟨e, he, hb⟩ := exists_eigEquiv Y.m.cart Y.m.act (ptF y) ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _)
    (Category.assoc _ _ _)
  let u : Fin (Dw.mult τ) → (epsAt y.x ⟶ Xo.univ.t.G) := fun i => Over.homMk (y.u τ i) (y.tan τ i).1
  have hu : IsEigenBasis Xo.univ.t.act y.x (chr c τ (algebraMap c.F S)) u := by
    refine ⟨fun i => ⟨(y.tan τ i).2, fun a => y.eig τ i a⟩, fun w hw => ?_⟩
    refine (existsUnique_congr fun a => ⟨?_, ?_⟩).1 (y.basis τ w.left ⟨Over.w w, hw.1⟩ fun a => hw.2 a)
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, Over.OverMorphism.ext h2.symm⟩
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, congrArg (fun z => z.left) h2.symm⟩
  have hw := (hb₀ (chr c τ (algebraMap c.F S)) _ fun i => e₀.symm (u i)).2
    ((funext fun i => e₀.apply_symm_apply (u i) : (fun i => e₀ (e₀.symm (u i))) = u).symm ▸ hu)
  refine ⟨fun i => e (e₀.symm (u i)), (hb _ _ _).1 hw, fun i => ⟨i, rfl, (e₀.symm (u i)).left,
    ⟨Over.w _, (hw.1 i).1⟩, ?_, (he _).symm⟩⟩
  rw [← he₀, Equiv.apply_symm_apply]
  rfl

theorem exists_matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) (hy : ∀ s, ptF y s ∈ (V : Set (Xo.XF c))) :
    ∃ a : Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a := by
  obtain ⟨v, hv, ev⟩ := exists_eigenBasis_sameVec Y y τ.1 Dw.p (if_pos τ.2)
  obtain ⟨w, hw, ew⟩ := exists_eigenBasis_sameVec Y y (conjEmb τ.1) Dw.q (if_neg (conj_not_mem τ))
  refine ⟨⟨ptF y ≫ Y.jQ, by rw [Category.assoc, Y.jQ_over, ptF, pullback.lift_snd], ?_, v, w, hv, hw⟩,
    rfl, ev, ew⟩
  rintro _ ⟨z, rfl⟩
  exact subset_closure ⟨ptF y z, hy z, by simp⟩

end GlobalTheory.BdryUnit
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.RatDegZeros

theorem mem_range_fst : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → x ∈ Set.range (ratFibre.fst p) := by
  intro k _ X p x hx
  let q : Spec (X.residueField x) ⟶ Sp ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ (X.residueField x)))
  let y0 := (ratFibre.isPullback p).lift (X.fromSpecResidueField x) q (specZIsTerminal.hom_ext _ _)
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  refine ⟨y0 z, ?_⟩
  have e : (y0 ≫ ratFibre.fst p) z = X.fromSpecResidueField x z := by
    rw [(ratFibre.isPullback p).lift_fst]
  rw [Scheme.Hom.comp_apply] at e
  exact e.trans (X.fromSpecResidueField_apply x z)

end GlobalTheory.RatDegZeros
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.strictHenselisation_enlarge_good_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_good) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_good) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_good  <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.OrthoFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_approx_cmType (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : Ψ → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : E, ∀ τ : Ψ, dist (w τ) (τ.1 x) < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  choose z hz using fun τ : Ψ => Metric.denseRange_iff.1
    (GlobalTheory.ShortVec.denseRange_emb τ.1 (IsTotallyComplex.complexEmbedding_not_isReal τ.1)) (w τ) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (v := fun τ : Ψ => (InfinitePlace.mk τ.1).1) (fun τ => InfinitePlace.isNontrivial _)
    (by
      intro σ τ hne h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.eq_iff_isEquiv.2 h) with h1 | h1
      · exact hne (Subtype.ext h1)
      · exact (hΨ σ.1).1 σ.2 (h1 ▸ τ.2)) z hε2
  refine ⟨x, fun τ => ?_⟩
  have h1 : ‖τ.1 (z τ - x)‖ < ε / 2 := by
    rw [← InfinitePlace.apply]; exact hx τ
  rw [map_sub, ← dist_eq_norm] at h1
  have h2 := dist_triangle (w τ) (τ.1 (z τ)) (τ.1 x)
  have h3 := hz τ
  linarith

theorem dom_nonempty {r : ℕ} (X : Data E r) : X.dom.Nonempty := by
  choose P hP using X.signature
  refine ⟨fun τ k a => P τ k a, fun τ => ⟨(hP τ).1, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ k a => P τ k a) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    change lminor (gram τ.1 X.Gm (P τ)) i = _
    rw [(hP τ).2, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  unfold sgn
  split_ifs <;> norm_num

theorem exists_frm_mem_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r),
    ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  intro E _ _ _ r X
  obtain ⟨P, hP⟩ := dom_nonempty X
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (FourierCoefficientDomain.isOpen_dom X) P hP
  choose u hu using fun a k : Fin r =>
    exists_approx_cmType X.Ψ X.cmType (fun τ => P τ k a) hε
  refine ⟨u, hb ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_pi_lt_iff hε]
  intro τ
  rw [dist_pi_lt_iff hε]
  intro k
  rw [dist_pi_lt_iff hε]
  intro a
  exact hu a k τ

end GlobalTheory.OrthoFrame
end
