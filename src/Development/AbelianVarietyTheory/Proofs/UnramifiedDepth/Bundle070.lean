module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle064
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle061
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle056
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle062
import Formalism.LocalToGlobal.CharacterGerms.Bundle007
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich

@[expose] public section

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

namespace GlobalTheory.AlphaPair

section Alg

open Polynomial

variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime]

theorem root_pow_eq_zero : AdjoinRoot.root ((X : Polynomial Ω) ^ p) ^ p = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

def truncLift {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    AdjoinRoot ((X : Polynomial Ω) ^ p) →ₐ[Ω] A :=
  Ideal.Quotient.liftₐ _ (aeval a) (by
    intro f hf
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton.1 hf
    simp [ha])

theorem truncLift_mk {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) (f : Polynomial Ω) :
    truncLift a ha (AdjoinRoot.mk _ f) = aeval a f := rfl

theorem truncLift_root {A : Type} [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    truncLift (Ω := Ω) a ha (AdjoinRoot.root _) = a := by
  rw [← AdjoinRoot.mk_X, truncLift_mk, aeval_X]

theorem isLocalRing_trunc : IsLocalRing (AdjoinRoot ((X : Polynomial Ω) ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Nontrivial (AdjoinRoot ((X : Polynomial Ω) ^ p)) :=
    (truncLift (0 : Ω) (zero_pow hp)).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective a
  have hn : IsNilpotent (AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (X * f.divX)) := by
    refine ⟨p, ?_⟩
    rw [map_mul, mul_pow, AdjoinRoot.mk_X, root_pow_eq_zero, zero_mul]
  rw [← X_mul_divX_add f, map_add (f := _)]
  by_cases hc : f.coeff 0 = 0
  · right
    rw [hc, C_0, map_zero, add_zero]
    exact hn.isUnit_one_sub
  · left
    exact hn.isUnit_add_right_of_commute ((isUnit_C.2 (Ne.isUnit hc)).map _) (Commute.all _ _)

theorem mk_eq_const_of_derivative [CharP Ω p] (f : Polynomial Ω)
    (h : AdjoinRoot.mk ((X : Polynomial Ω) ^ p) (derivative f) = 0) :
    AdjoinRoot.mk ((X : Polynomial Ω) ^ p) f = algebraMap Ω _ (aeval (0 : Ω) f) := by
  rw [AdjoinRoot.mk_eq_zero, X_pow_dvd_iff] at h
  change _ = AdjoinRoot.mk _ (C _)
  rw [AdjoinRoot.mk_eq_mk, X_pow_dvd_iff]
  intro d hd
  rcases d with _ | d
  · simp [coeff_zero_eq_eval_zero]
  · have h1 := h d (by omega)
    rw [coeff_derivative] at h1
    have h2 : ((d : Ω) + 1) ≠ 0 := by
      intro h0
      have : ((d + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h0
      exact absurd (Nat.le_of_dvd (Nat.succ_pos d) ((CharP.cast_eq_zero_iff Ω p _).1 this)) (by omega)
    simpa [coeff_C] using (mul_eq_zero.1 h1).resolve_right h2

end Alg

theorem spMap_comp_eq_of_equalizer {R B : Type} [CommRing R] [CommRing B] [IsLocalRing R] {Y : Scheme.{0}}
    (y : Sp R ⟶ Y) (d₁ d₀ : R →+* B) (e : R →+* R) (he : ∀ x, d₁ x = d₀ x → e x = x)
    (h : spMap d₁ ≫ y = spMap d₀ ≫ y) : spMap e ≫ y = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  obtain ⟨φ, rfl⟩ : ∃ φ : Γ(Y, V) ⟶ CommRingCat.of R, Spec.map φ ≫ hV.fromSpec = y :=
    ⟨Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  exact he _ (congrArg (fun k => k.hom a) h')

theorem IsAlpha.eq_one_of_tangent (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0})
    (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) (hg : IsAlpha p s G g)
    (h1 : g (DualNumber Ω) DualNumber.eps = 1) (A : Type) [CommRing A] [Algebra Ω A] (a : A) (ha : a ^ p = 0) :
    g A a = 1 := by
  have hp : p.Prime := Fact.out
  let R := AdjoinRoot ((Polynomial.X : Polynomial Ω) ^ p)
  haveI : IsLocalRing R := isLocalRing_trunc
  let t : R := AdjoinRoot.root _
  have ht : t ^ p = 0 := root_pow_eq_zero
  have heps : ∀ (B : Type) [CommRing B], (DualNumber.eps : DualNumber B) ^ p = 0 := fun B _ =>
    pow_eq_zero_of_le hp.two_le (by rw [sq, DualNumber.eps_mul_eps])
  haveI : CharP R p := charP_of_injective_algebraMap (algebraMap Ω R).injective p
  haveI : CharP (DualNumber R) p := charP_of_injective_algebraMap (algebraMap Ω (DualNumber R)).injective p
  let t' : DualNumber R := TrivSqZeroExt.inl t
  have ht' : t' ^ p = 0 := by
    change TrivSqZeroExt.inlAlgHom Ω R R t ^ p = 0
    rw [← map_pow, ht, map_zero]
  have hs : (t' + DualNumber.eps) ^ p = 0 := by rw [add_pow_char, ht', heps, add_zero]
  have he : g (DualNumber R) DualNumber.eps = 1 := by
    let j : DualNumber Ω →ₐ[Ω] DualNumber R :=
      DualNumber.lift ⟨(Algebra.ofId _ _, DualNumber.eps), DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩
    have hj : j DualNumber.eps = DualNumber.eps := DualNumber.lift_apply_eps _
    rw [← hj, hg.1 _ _ j _ (heps Ω), h1, MonObj.comp_one]
  have key : homAt s (truncLift _ hs) ≫ g R t = homAt s (truncLift _ ht') ≫ g R t := by
    rw [← hg.1 _ _ _ _ ht, ← hg.1 _ _ _ _ ht, truncLift_root, truncLift_root, hg.2 _ _ _ ht' (heps R), he, _root_.mul_one]
  let e : R →ₐ[Ω] R := truncLift 0 (zero_pow hp.ne_zero)
  have hr : homAt s e ≫ g R t = g R t := by
    apply Over.OverMorphism.ext
    refine spMap_comp_eq_of_equalizer (g R t).left (truncLift _ hs).toRingHom (truncLift _ ht').toRingHom
      e.toRingHom ?_ (congrArg (·.left) key)
    intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    change Polynomial.aeval (t' + DualNumber.eps) f = Polynomial.aeval t' f at hx
    rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ (by rw [sq, DualNumber.eps_mul_eps]), add_eq_left] at hx
    have h3 : Polynomial.aeval t' (Polynomial.derivative f) =
        TrivSqZeroExt.inl (Polynomial.aeval t (Polynomial.derivative f)) :=
      Polynomial.aeval_algHom_apply (TrivSqZeroExt.inlAlgHom Ω R R) t _
    have h4 := congrArg TrivSqZeroExt.snd hx
    rw [h3] at h4
    have h5 : Polynomial.aeval t (Polynomial.derivative f) = 0 := by simpa using h4
    rw [AdjoinRoot.aeval_eq] at h5
    rw [mk_eq_const_of_derivative f h5]
    exact e.commutes _
  have h0 : g R t = 1 := by
    rw [← hr, ← hg.1 _ _ _ _ ht, truncLift_root, hg.zero hp.ne_zero]
  have := hg.1 _ _ (truncLift a ha) t ht
  rwa [truncLift_root, h0, MonObj.comp_one] at this

end GlobalTheory.AlphaPair
end
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

namespace GlobalTheory.AlphaPair.JetUniv

open GlobalTheory.ChartBaseChange (fib fibLift fibFst fibSnd fib_cond fib_ker exists_pt_of_aug pt_eps_self)

def unitSec {S : Scheme.{0}} (G : Over S) [GrpObj G] : S ⟶ G.left := (η[G]).left

def lft {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : T ⟶ G.left := y.left

theorem lft_w {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} (y : Over.mk f ⟶ G) : lft y ≫ G.hom = f := Over.w y

theorem lft_inj {S T : Scheme.{0}} {G : Over S} {f : T ⟶ S} {y z : Over.mk f ⟶ G} (h : lft y = lft z) : y = z :=
  Over.OverMorphism.ext h

theorem unitSec_w {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ G.hom = 𝟙 S := Over.w (η[G])

theorem eq_one_iff {S T : Scheme.{0}} {G : Over S} [GrpObj G] {f : T ⟶ S} (y : Over.mk f ⟶ G) :
    y = 1 ↔ lft y = f ≫ unitSec G := by
  have e : lft (1 : Over.mk f ⟶ G) = f ≫ unitSec G := by
    show (toUnit (Over.mk f) ≫ η[G]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  exact ⟨fun h => h ▸ e, fun h => lft_inj (h.trans e.symm)⟩

variable {V : Type} [CommRing V] {G : Over (Sp V)} [GrpObj G] {κ : Type}

theorem aug_X (m : ℕ) (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = 0
  simp

theorem ker_aug_pow (m : ℕ) : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug : Jet V κ m →ₐ[V] V) ≤ (orig V κ).map (Ideal.Quotient.mk _) := fun z hz => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h0 : MvPolynomial.aeval (fun _ : κ => (0 : V)) p = 0 := hz
    have h1 : MvPolynomial.constantCoeff p = 0 := by simpa using h0
    have h2 := sub_const_mem_orig p
    rw [h1, map_zero, sub_zero] at h2
    exact Ideal.mem_map_of_mem _ h2
  rw [eq_bot_iff]
  refine (Ideal.pow_right_mono hle _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

def toSp {A : Type} [CommRing A] [Algebra V A] (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp {A : Type} [CommRing A] [Algebra V A] (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem one_at_iff {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (y : overAt (𝟙 (Sp V)) A ⟶ G) : homAt (𝟙 (Sp V)) f ≫ y = 1 ↔ Chart.spMap f ≫ toSp y = 1 := by
  rw [eq_one_iff, eq_one_iff]
  have e : (spMap (algebraMap V B) ≫ 𝟙 (Sp V)) ≫ unitSec G = spMap (algebraMap V B) ≫ unitSec G := by
    rw [Category.comp_id]
  rw [e]
  rfl

theorem univ_over [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Chart.sp (R₀ := V) A ⟶ G) (hy : Chart.spMap q ≫ y = 1) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y.left = spMap (ψ : Jet V κ m →+* A) ≫ (x m).left := by
  obtain ⟨C⟩ := Chart.exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug : Jet V κ m →ₐ[V] V)
    (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (ker_aug_pow m) (toSp (x m)) ((one_at_iff _ _).1 (hx.2.1 m))
  have hk' : (x m).left = (Chart.pt C k).left := congrArg CommaMorphism.left hk
  have mv : ∀ {B : Type} [CommRing B] [Algebra V B] (v : Jet V κ m →ₐ[V] B),
      spMap (v : Jet V κ m →+* B) ≫ (x m).left = (Chart.pt C (v.comp k)).left := by
    intro B _ _ v
    rw [hk', ← Chart.spMap_pt]
    rfl
  let h₀ := fibLift q (Chart.eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJ) (ofSp (Chart.pt C h₀)) (by
    rw [one_at_iff]
    show Chart.spMap _ ≫ Chart.pt C h₀ = 1
    rw [Chart.spMap_pt]
    exact pt_eps_self C)
  have h0 : h₀ = ψ₀.comp k :=
    Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hψ₀).trans (mv ψ₀)))
  refine ⟨(fibSnd q).comp ψ₀, ⟨fun i => ?_, ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, fib_cond, ← AlgHom.comp_apply (fibFst q), ha, aug_X, map_zero]
  · rw [mv, AlgHom.comp_assoc, ← h0, hh]
    rfl
  · rintro v ⟨hv0, hv1⟩
    have hv : q.comp v = (Algebra.ofId V Ω).comp jetAug :=
      Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext fun i => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, hv0, aug_X, map_zero]
    have hvk : h = v.comp k :=
      Chart.pt_injective C (Over.OverMorphism.ext ((congrArg CommaMorphism.left hh).symm.trans (hv1.trans (mv v))))
    have e := hu (fibLift q jetAug v hv) ⟨rfl, Over.OverMorphism.ext (by
      refine Eq.trans ?_ (mv _).symm
      show (Chart.pt C h₀).left = _
      congr 2
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s)⟩
    rw [← e]
    rfl

theorem univ_left [IsLocalRing V] {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A Ω : Type} [CommRing A] [Algebra V A] [CommRing Ω] [Algebra V Ω] (q : A →ₐ[V] Ω) (hq : Function.Surjective q)
    {m : ℕ} (hJ : RingHom.ker q ^ (m + 1) = ⊥) (y : Sp A ⟶ G.left) (hw : y ≫ G.hom = spMap (algebraMap V A))
    (hy : spMap (q : A →+* Ω) ≫ y = spMap (algebraMap V Ω) ≫ unitSec G) :
    ∃! ψ : Jet V κ m →ₐ[V] A, (∀ i, q (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = 0) ∧
      y = spMap (ψ : Jet V κ m →+* A) ≫ lft (x m) :=
  univ_over hx q hq hJ (Over.homMk y hw) ((eq_one_iff _).2 hy)

theorem aug_left {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) (A : Type) [CommRing A] [Algebra V A]
    (m : ℕ) : spMap (algebraMap V A) ≫ unitSec G =
      spMap (((Algebra.ofId V A).comp jetAug : Jet V κ m →ₐ[V] A) : Jet V κ m →+* A) ≫ lft (x m) := by
  have h2 : Chart.spMap ((Algebra.ofId V A).comp jetAug) ≫ toSp (x m) = 1 := by
    rw [← Chart.spMap_comp, Category.assoc, (one_at_iff _ _).1 (hx.2.1 m), MonObj.comp_one]
  exact ((eq_one_iff _).1 h2).symm

section Field

variable {Ω : Type} [Field Ω] [Algebra V Ω] {A : Type} [CommRing A] [Algebra Ω A] [Algebra V A] [IsScalarTower V Ω A]

theorem hom_eq : spMap (algebraMap Ω A) ≫ spMap (algebraMap V Ω) = spMap (algebraMap V A) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem exists_jetHom {B : Type} [CommRing B] [Algebra V B] {m : ℕ} {I : Ideal B} (hI : I ^ (m + 1) = ⊥) (a : κ → B)
    (ha : ∀ i, a i ∈ I) : ∃ ψ : Jet V κ m →ₐ[V] B, ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i :=
  ⟨liftJet (MvPolynomial.aeval a) (by
      rw [eq_bot_iff, ← hI]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨i, rfl⟩
      simpa using ha i), fun i => MvPolynomial.aeval_X a i⟩

theorem universalJetCoordinates_points_over_field [IsLocalRing V] {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {P : PtFam (spMap (algebraMap V Ω)) G d}
    (hP : IsJetPt (algebraMap V Ω) x P) (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π)) :
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt (spMap (algebraMap V Ω)) A ⟶ G, homAt _ π ≫ z = 1 →
      ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z := by
  have hq : Function.Surjective (π.restrictScalars V) := fun r => ⟨algebraMap Ω A r, π.commutes r⟩
  obtain ⟨m, hm⟩ := hπ
  have hJ : RingHom.ker (π.restrictScalars V) ^ (m + 1) = ⊥ := by
    show RingHom.ker π ^ (m + 1) = ⊥
    rw [pow_succ, hm, zero_mul]
    rfl
  have hP' : ∀ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
      lft (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) =
        spMap (ψ : Jet V (Fin 1 × Fin d) m →+* A) ≫ lft (x m) := fun ψ =>
    hP A m (ψ : Jet V (Fin 1 × Fin d) m →+* A) fun v =>
      (ψ.commutes v).trans (IsScalarTower.algebraMap_apply V Ω A v)
  refine ⟨fun a ha h1 => ?_, fun z hz => ?_⟩
  · have ha0 : ∀ j, π.restrictScalars V (a j) = 0 := fun j => ((ha j).map (π.restrictScalars V)).eq_zero
    obtain ⟨ψ, hψ⟩ := exists_jetHom (V := V) hJ (fun p : Fin 1 × Fin d => a p.2) fun p => ha0 p.2
    have hl := hP' ψ
    rw [show (fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))) = a from funext fun j => hψ _,
      (eq_one_iff _).1 h1, hom_eq] at hl
    have e := (univ_left hx _ hq hJ (spMap (algebraMap V A) ≫ unitSec G)
      (by rw [Category.assoc, unitSec_w, Category.comp_id])
      (by rw [← Category.assoc, spMap_comp_alg])).unique (y₁ := ψ)
      (y₂ := (Algebra.ofId V A).comp jetAug) ⟨fun i => by rw [hψ, ha0], hl⟩
      ⟨fun i => by rw [AlgHom.comp_apply, aug_X, map_zero, map_zero], aug_left hx A m⟩
    funext j
    have h3 := hψ (0, j)
    rw [e, AlgHom.comp_apply, aug_X, map_zero] at h3
    exact h3.symm
  · obtain ⟨ψ, ⟨h0, h1⟩, -⟩ := univ_left hx _ hq hJ (lft z) ((lft_w z).trans hom_eq) (by
      have h3 : spMap (π : A →+* Ω) ≫ lft z = _ := (eq_one_iff _).1 hz
      rw [hom_eq (A := Ω)] at h3
      exact h3)
    refine ⟨fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (0, j))), fun j => ⟨m + 1, ?_⟩,
      lft_inj ((hP' ψ).trans h1.symm)⟩
    have := Ideal.pow_mem_pow (RingHom.mem_ker.2 (h0 (0, j))) (m + 1)
    rwa [hJ, Ideal.mem_bot] at this

end Field

end GlobalTheory.AlphaPair.JetUniv

namespace GlobalTheory.AlphaPair

theorem jetUniv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtUniv (spMap β) t.G P := by
  intro E _ _ _ H V _ _ t d x hx Ω _ β P hP A _ _ π hπ
  letI : Algebra V Ω := β.toAlgebra
  letI : Algebra V A := ((algebraMap Ω A).comp β).toAlgebra
  haveI : IsScalarTower V Ω A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact JetUniv.universalJetCoordinates_points_over_field hx hP π hπ

end GlobalTheory.AlphaPair
end
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

namespace GlobalTheory.AlphaPair

theorem exists_pullEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) (n : ℕ) {Y : Scheme.{0}} (a : Y ⟶ S')
    (u : Y ⟶ S) (hu : a ≫ f = u) :
    ∃ e : (Over.mk u ⟶ t.G) ≃* (Over.mk a ⟶ t'.G), (∀ x, (e x).left ≫ m.cm.F = x.left) ∧
      ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 := by
  subst hu
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y (Out.toBase hw x) (Out.toBase hw y) rfl rfl).symm
  let β : (Over.mk a ⟶ t'.G) →* (Over.mk (a ≫ f) ⟶ t.G) := GlobalTheory.UU.toBaseHom mul (Over.mk a)
  have hβ : Function.Bijective β := by
    refine ⟨fun x y e => Over.OverMorphism.ext
      (m.cart.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
    exact ⟨Over.homMk (m.cart.1.lift x.left a (Over.w x)) (m.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (m.cart.1.lift_fst _ _ _)⟩
  let e := (MulEquiv.ofBijective β hβ).symm
  have he : ∀ x, β (e x) = x := fun x => (MulEquiv.ofBijective β hβ).apply_symm_apply x
  refine ⟨e, fun x => congrArg (fun q => q.left) (he x), fun x y h => ?_⟩
  obtain ⟨ζ, hζ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub (N := n) (x := e x) (y := e y)
    (by rw [← map_pow, h.1, map_one]) (by rw [← map_pow, h.2.1, map_one])
  have h' : CubWeil t.cub n (β (e x)) (β (e y)) ζ :=
    GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin n _ _ _ ζ hζ
  rw [he, he] at h'
  obtain rfl : ζ = 1 := h'.unique h
  exact hζ

theorem exists_isTorExt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (f : S' ⟶ S) (t : SAB H S) (t' : SAB H S') (_ : SABMap t' t f) (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S'), s' ≫ f = s → ∀ n : ℕ, ∃ (τ : PtHom s s' t.G t'.G) (io : TorHom s t.G PUnit), IsTorExt s s' t.G t'.G PUnit τ io ∧ Transfer n t.cub t'.cub τ := by
  intro E _ _ _ H S S' f t t' m Ω _ s s' hs n
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A], ∃ e : (overAt s A ⟶ t.G) ≃* (overAt s' A ⟶ t'.G),
      (∀ x, (e x).left ≫ m.cm.F = x.left) ∧ ∀ x y, CubWeil t.cub n x y 1 → CubWeil t'.cub n (e x) (e y) 1 :=
    fun A _ _ => exists_pullEquiv m n _ _ (by rw [Category.assoc, hs])
  choose e he hc using key
  have nat : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s A ⟶ t.G), e A' (homAt s g ≫ x) = homAt s' g ≫ e A x := by
    intro A A' _ _ _ _ g x
    refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, he]
    rfl
  refine ⟨fun A _ _ => (e A).toMonoidHom, fun A _ _ => 1, ⟨nat, ?_, ?_, ?_, ?_⟩, fun A _ _ => hc A⟩
  · intro A A' _ _ _ _ g χ
    exact (MonObj.comp_one _).symm
  · intro A _ _ χ χ' _
    exact MonoidHom.ext fun x => by rw [Subsingleton.elim x 1, map_one, map_one]
  · intro A _ _ x
    exact (e A).map_eq_one_iff.trans ⟨fun h => ⟨1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · intro A _ _ π _ y hy
    refine ⟨(e A).symm y, (e Ω).map_eq_one_iff.1 ?_, (e A).apply_symm_apply y⟩
    rw [nat, (e A).apply_symm_apply, hy]

end GlobalTheory.AlphaPair
end

section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem formal_statements_selfConj :
    CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d I0 p)
      (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    have h := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p
    exact RawChart.axes_of _ h.exc h.axes
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact intGerm_indep_of_rlaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p _
    exact GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)

end GlobalTheory.RowLaw
end
