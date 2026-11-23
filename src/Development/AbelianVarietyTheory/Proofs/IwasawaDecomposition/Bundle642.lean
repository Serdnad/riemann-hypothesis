module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle629
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle189
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Group.Tannery
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle027
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.HTMap

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by rw [← Spec.map_comp]; rfl

theorem spc_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) {Z : Scheme.{0}}
    (h : Sp A ⟶ Z) : spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by rw [← Category.assoc, spc]

def pull (g : T' ⟶ T) (h : g ≫ y = y') : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G) := Formalism.L2.Pj.preHom (Over.homMk g h)

omit [GrpObj G] in
theorem over_w (w : Over.mk y ⟶ G) : w.left ≫ G.hom = y := Over.w w


omit [GrpObj G] in
def mkPt (w : T ⟶ G.left) (h : w ≫ G.hom = y) : Over.mk y ⟶ G := Over.homMk w h

omit [GrpObj G] in
theorem mkPt_left (w : T ⟶ G.left) (h : w ≫ G.hom = y) : (mkPt w h).left = w := rfl

theorem eq_pull {g : T' ⟶ T} (w : Over.mk y ⟶ G) (w' : Over.mk y' ⟶ G) (e : w'.left = g ≫ w.left) :
    ∃ h : g ≫ y = y', w' = pull g h w :=
  ⟨by rw [← over_w w, ← over_w w', e, Category.assoc], Over.OverMorphism.ext e⟩

theorem tors_of {g : T' ⟶ T} {w : Over.mk y ⟶ G} {w' : Over.mk y' ⟶ G} (e : w'.left = g ≫ w.left) {q : ℕ}
    (hw : w ^ q = 1) : w' ^ q = 1 := by
  obtain ⟨h, rfl⟩ := eq_pull w w' e
  rw [← map_pow, hw, map_one]

theorem one_of {g : T' ⟶ T} (h : g ≫ y = y') : (1 : Over.mk y' ⟶ G).left = g ≫ (1 : Over.mk y ⟶ G).left := by
  rw [← map_one (pull (G := G) g h)]; rfl

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}


variable (t x₀ q) in
structure FP : Type 1 where
  f : A
  B : Type
  [ring : CommRing B]
  [alg : Algebra (Localization.Away f) B]
  u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap A (Localization.Away f)) ≫ x₀) ⟶ t.G
  ne : f ≠ 0
  fin : IsFinPart t (spMap (algebraMap A (Localization.Away f)) ≫ x₀) q u

attribute [instance] FP.ring FP.alg

namespace FP

variable (P : FP t x₀ q) {S S' : Type} [CommRing S] [CommRing S']

def str : A →+* P.B := (algebraMap (Localization.Away P.f) P.B).comp (algebraMap A (Localization.Away P.f))

def At (φ : A →+* S) (w : Sp S ⟶ t.G.left) (β : P.B →+* S) : Prop := β.comp P.str = φ ∧ spMap β ≫ P.u.left = w

variable {P}

theorem alg_ext {β β' : P.B →+* S} (h : β.comp P.str = β'.comp P.str) :
    β.comp (algebraMap (Localization.Away P.f) P.B) = β'.comp (algebraMap (Localization.Away P.f) P.B) :=
  IsLocalization.ringHom_ext (Submonoid.powers P.f) h

theorem At.map {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) (ψ : S →+* S') :
    P.At (ψ.comp φ) (spMap ψ ≫ w) (ψ.comp β) :=
  ⟨by rw [← h.1]; rfl, by rw [← h.2]; exact (spc_assoc _ _ _).symm⟩

theorem At.over {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) :
    w ≫ t.G.hom = spMap φ ≫ x₀ := by
  rw [← h.2, ← h.1, Category.assoc, over_w P.u, spc_assoc, spc_assoc]; rfl

theorem At.tors {φ : A →+* S} {y : Sp S ⟶ X} {w : Over.mk y ⟶ t.G} {β : P.B →+* S} (h : P.At φ w.left β) :
    w ^ q = 1 := tors_of h.2.symm P.fin.tors

theorem At.unit {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) : IsUnit (φ P.f) := by
  rw [← h.1]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away P.f) P.f).map
    (algebraMap (Localization.Away P.f) P.B)).map β

theorem at_iff (φ : Localization.Away P.f →+* S) (w : Sp S ⟶ t.G.left) :
    (∃ β, P.At (φ.comp (algebraMap A _)) w β) ↔ Thru t P.u.left φ w :=
  exists_congr fun _ => and_congr_left fun _ =>
    ⟨fun h => IsLocalization.ringHom_ext (Submonoid.powers P.f) h, fun h => by rw [← h]; rfl⟩

theorem ex_lift {φ : A →+* S} (hu : IsUnit (φ P.f)) :
    ∃ φ' : Localization.Away P.f →+* S, φ'.comp (algebraMap A _) = φ :=
  ⟨IsLocalization.Away.lift P.f hu, IsLocalization.Away.lift_comp _ _⟩

theorem at_open {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) (w : Over.mk y ⟶ t.G)
    (hw : w ^ q = 1) (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      ∃ β, P.At ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left) β) :
    ∃ β, P.At φ w.left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.isOpen S φ' w hw fun 𝔪 h𝔪 => (at_iff _ _).1 (h 𝔪 h𝔪))

theorem at_one {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) :
    ∃ β, P.At φ (1 : Over.mk y ⟶ t.G).left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.one S φ')

theorem At.mul {φ : A →+* S} {y : Sp S ⟶ X} {w w' : Over.mk y ⟶ t.G} {β β' : P.B →+* S} (h : P.At φ w.left β)
    (h' : P.At φ w'.left β') : ∃ β'', P.At φ (w * w').left β'' := by
  have hy : y = spMap φ ≫ x₀ := (over_w w).symm.trans h.over
  obtain ⟨φ', rfl⟩ := ex_lift h.unit
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.mul S φ' w w' ((at_iff _ _).1 ⟨_, h⟩) ((at_iff _ _).1 ⟨_, h'⟩))


end FP



section Dom

variable [IsDomain A]

namespace FP

variable (P : FP t x₀ q)

variable {P}



end FP

variable [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ}

end Dom

section Tan

variable {S : Type} [CommRing S] {x : Sp S ⟶ X}

theorem tan_tors {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (hq : (q : S) = 0)
    {y : Sp (DualNumber S) ⟶ X} (w : Over.mk y ⟶ t.G) (e : w.left = v) : w ^ q = 1 := by
  have key : ∀ n : ℕ, smT x (n : S) (ovT hv) = ovT hv ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero, smT_zero_ovT]
    | succ n ih => rw [Nat.cast_succ, smT_add x _ (smT_zero_ovT hv), ih, smT_unit, pow_succ]
  have h : ovT hv ^ q = 1 := by rw [← key, hq, smT_zero_ovT]
  exact tors_of (w := ovT hv) (g := 𝟙 _) (e.trans (Category.id_comp _).symm) h

theorem comb_single {g : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) (i : Fin g) :
    IsCombAtG t x e (Pi.single i 1) (e i) :=
  (isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [combT_single _ _ fun j => smT_zero_ovT _]; rfl)

theorem tan_at (P : FP t x₀ q) {φ : A →+* S} {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t (spMap φ ≫ x₀) v)
    (hq : (q : S) = 0) {S' : Type} [CommRing S'] (ψ : DualNumber S →+* S')
    (hu : IsUnit (ψ (((algebraMap S (DualNumber S)).comp φ) P.f))) :
    ∃ β, P.At (ψ.comp ((algebraMap S (DualNumber S)).comp φ)) (spMap ψ ≫ v) β := by
  refine FP.at_open (φ := ψ.comp ((algebraMap S (DualNumber S)).comp φ)) hu ?_ (mkPt (spMap ψ ≫ v) rfl)
    (tors_of (g := spMap ψ) (w := ovT hv) rfl (tan_tors hv hq _ rfl)) fun 𝔪 h𝔪 => ?_
  · rw [Category.assoc, hv.1, spc_assoc, spc_assoc]
  let ρ := (Ideal.Quotient.mk 𝔪).comp ψ
  have hρ : ρ = (ρ.comp (algebraMap S (DualNumber S))).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    refine RingHom.ext fun z => ?_
    have h0 : ρ (TrivSqZeroExt.inr z.snd) = 0 :=
      mul_self_eq_zero.1 (by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero])
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z, map_add (f := _), h0, add_zero]
    rfl
  have e : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ψ ≫ v =
      (1 : Over.mk (spMap (ρ.comp (algebraMap S (DualNumber S))) ≫ spMap φ ≫ x₀) ⟶ t.G).left := by
    rw [one_of rfl, ← hv.2]
    exact (spc_assoc _ _ _).trans ((congrArg (fun z => spMap z ≫ v) hρ).trans (spc_assoc _ _ _).symm)
  rw [mkPt_left, e]
  exact FP.at_one (hu.map (Ideal.Quotient.mk 𝔪)) (spc_assoc _ _ _)

end Tan

section Char

variable {O : Type} [CommRing O] [IsLocalRing O] {x : A →+* O} {P : FP t x₀ q}

end Char


theorem cast_quot (R : Type) [CommRing R] (p n : ℕ) : ((p ^ n : ℕ) : R ⧸ Ideal.span {(p : R) ^ n}) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

end GlobalTheory.HTMap
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart sp fB)

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem exists_univChart_pullback {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    ∃ xc : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ (Over.pullback x).obj t.G, IsUnivChart _ n xc ∧
      ∀ cc : Fin n → A, LieLocBasis.vec t x xc cc = (tvec (x := y) cc).left ≫ ψ := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback t.G x)
  refine ⟨fun m => y m ≫ e.hom, gfp_chart_iso e hy, fun cc => ?_⟩
  have key : (tvec (x := fun m => y m ≫ e.hom) cc).left = (tvec (x := y) cc).left ≫ e.hom.left := by
    show (_ ≫ y 1 ≫ e.hom).left = (_ ≫ y 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => y m ≫ e.hom) cc).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ]

theorem isTanBasis_of_chart {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart G₁) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    IsTanBasis t x fun j => (tvec (x := y) (Pi.single j 1)).left ≫ ψ := by
  refine ⟨fun j => ?_, fun S' _ φ w hw => ?_⟩
  · obtain ⟨xc, hx, hv⟩ := exists_univChart_pullback t x h hy
    have h1 := LieLocBasis.vec_tan hx (Pi.single j 1)
    rw [hv] at h1
    exact h1
  let _ : Algebra A S' := φ.toAlgebra
  obtain ⟨y', hy', e'⟩ := LieChart.univChart_baseChange_of_chart (R' := S') G₁ C n y hy
  obtain ⟨xc', hx', hv⟩ := exists_univChart_pullback t (spMap φ ≫ x)
    ((isGrpPullback_pullback G₁ (fB A S')).comp h) hy'
  obtain ⟨cc, rfl⟩ := LieLocBasis.vec_exists hx' w hw
  have hD : (fun j => spMap (dualMap φ) ≫ (tvec (x := y) (Pi.single j 1)).left ≫ ψ) =
      fun j => LieLocBasis.vec t (spMap φ ≫ x) xc' (Pi.single j 1) := by
    funext j
    have h1 : (Pi.single j 1 : Fin n → S') = algebraMap A S' ∘ (Pi.single j 1 : Fin n → A) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    rw [hv, h1, ← Category.assoc (tvec (x := y') _).left, e', Category.assoc]
    rfl
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (LieLocBasis.comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((LieLocBasis.comb_iff hx' _ _ _).1 ha).symm

theorem exists_affine_isTanBasis (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Scheme.{0}) (ρ : S ⟶ X) (z : S) :
    ∃ (V : S.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left)),
      z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e := by
  let G : Over S := (Over.pullback ρ).obj t.G
  have : Smooth G.hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom ρ)
    infer_instance
  obtain ⟨U, hU, V, hV, e, hxU, -, hs, h⟩ :=
    LieChart.exists_isStandardSmooth_section G.hom (η[G]).left (Over.w η[G]) z ⊤ trivial
  let i : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  let G₀ : Over (Spec (CommRingCat.of Γ(S, U))) := (Over.pullback i).obj G
  have hφ₀ : IsGrpPullback G₀ G i (pullback.fst G.hom i) := isGrpPullback_pullback G i
  obtain ⟨C, hC⟩ := LieChart.exists_chart_pullback G hU hV e hs h G₀ _ hφ₀
  obtain ⟨n, y, hy⟩ := LieChart.univChart_of_chart G₀ C hC
  exact ⟨⟨U, hU⟩, n, _, hxU,
    isTanBasis_of_chart t (i ≫ ρ) (hφ₀.comp (isGrpPullback_pullback t.G ρ)) C hy⟩

end GlobalTheory.LineNorm
end
end

section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom Filter Topology

namespace GlobalTheory.CuspLimit


open Classical in
theorem tendsto_dirichlet {ι : Type*} (A : ι → ℂ) (a : ι → ℝ) (F : ℝ → ℂ) (T : ℝ)
    (ha : ∀ i, A i ≠ 0 → 0 ≤ a i)
    (hs : ∀ t, T < t → HasSum (fun i => A i * (Real.exp (-(a i * t)) : ℂ)) (F t)) :
    Tendsto F atTop (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
  have h0 : Summable fun i => ‖A i * (Real.exp (-(a i * (T + 1))) : ℂ)‖ :=
    (hs (T + 1) (by linarith)).summable.norm
  have hlim : Tendsto (fun t : ℝ => ∑' i, A i * (Real.exp (-(a i * t)) : ℂ)) atTop
      (𝓝 (∑' i, if a i = 0 then A i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence h0 (fun i => ?_) ?_
    · by_cases hi : A i = 0
      · simp [hi]
      by_cases hz : a i = 0
      · simp [hz]
      have hp : 0 < a i := lt_of_le_of_ne (ha i hi) (Ne.symm hz)
      rw [if_neg hz]
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(a i * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hp)
      have h2 := ((Complex.continuous_ofReal.tendsto 0).comp h1).const_mul (A i)
      simpa using h2
    · filter_upwards [eventually_ge_atTop (T + 1)] with t ht i
      by_cases hi : A i = 0
      · simp [hi]
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      exact neg_le_neg (mul_le_mul_of_nonneg_left ht (ha i hi))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  exact (hs t ht).tsum_eq

theorem fj_zero_eq_zero_of_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  intro E _ _ _ r X la P ξ x s d T g hP hnn hξ hx hd hg hw
  classical
  have hpi := Real.pi_pos
  set F : ℝ → ℂ := fun t => P (X.flow ξ (fun τ => s τ + (I * t) * (d τ : ℂ)) x) with hF
  have him : ∀ t : ℝ, T < t → T < (I * (t : ℂ)).im := fun t ht => by simpa using ht
  have h1 := tendsto_dirichlet g (fun m : ℤ => 2 * Real.pi * m) F T
    (fun m hm => by
      have : 0 < m := by
        by_contra h
        exact hm (hg m (not_lt.mp h))
      positivity)
    (fun t ht => by
      have h := (hw _ (him t ht)).2
      convert h using 3 with m
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi, ← Complex.exp_int_mul]
      push_cast
      congr 1
      linear_combination (-(2 * (Real.pi : ℂ) * m * t)) * Complex.I_mul_I)
  have e1 : (∑' m : ℤ, if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = 0 := by
    have : (fun m : ℤ => if 2 * Real.pi * (m : ℝ) = 0 then g m else 0) = fun _ => 0 := by
      funext m
      split_ifs with h
      · have hm : m = 0 := by simpa [hpi.ne'] using h
        exact hg m hm.le
      · rfl
    rw [this, tsum_zero]
  have h2 := tendsto_dirichlet
    (fun ν : X.Ψ → ℝ => X.fj la ξ ν P x * cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ))
    (fun ν => 4 * Real.pi * ∑ τ, ν τ * d τ) F T
    (fun ν hν => by
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hν)
      have : 0 ≤ ∑ τ, ν τ * d τ := Finset.sum_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le
      positivity)
    (fun t ht => by
      have h := m3bExp_holds r X la P hP ξ hξ x hx _ (hw _ (him t ht)).1
      convert h using 2 with ν
      rw [mul_assoc]
      congr 1
      push_cast
      rw [← Complex.exp_add]
      congr 1
      have e : ∑ τ, (ν τ : ℂ) * (s τ + I * t * (d τ : ℂ)) =
          ∑ τ, (ν τ : ℂ) * s τ + I * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun τ _ => by ring
      rw [e]
      linear_combination (-(4 * (Real.pi : ℂ) * t * ∑ τ, (ν τ : ℂ) * (d τ : ℂ))) * Complex.I_mul_I)
  rw [tsum_eq_single (0 : X.Ψ → ℝ) (fun ν hν => by
    split_ifs with h
    · by_contra hne
      have h0 := hnn ξ hξ ν x hx (left_ne_zero_of_mul hne)
      have hz : ∑ τ, ν τ * d τ = 0 := by simpa [hpi.ne'] using h
      refine hν (funext fun τ => ?_)
      have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => mul_nonneg (h0 τ) (hd τ).le).mp hz τ
        (Finset.mem_univ τ)
      exact (mul_eq_zero.mp this).resolve_right (hd τ).ne'
    · rfl)] at h2
  rw [e1] at h1
  simpa using tendsto_nhds_unique h2 h1

end GlobalTheory.CuspLimit
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Principalise

theorem comap_mul_idealSheaf : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (I J : X.IdealSheafData),
    (I * J).comap f = I.comap f * J.comap f := by
  intro X X' f I J
  have h : ∀ y : X', ∃ (U : X.affineOpens) (A : X'.affineOpens), y ∈ A.1 ∧ A.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨A, hA⟩, hyA, hAU⟩
  choose U A hyA hAU using h
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, comapIdealAffine _ f (U y) (A y) (hAU y),
      comapIdealAffine _ f (U y) (A y) (hAU y), comapIdealAffine _ f (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end GlobalTheory.Principalise
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_pow_eq_unit_of_continuous_complex_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  first | exact @GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root | exact GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root | (intros; apply GlobalTheory.ContRoot.exists_pow_eq_of_continuous_root <;> assumption)
end
