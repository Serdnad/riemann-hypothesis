module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle627
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle626
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

section Cpt

variable (C : FlagCpt Z e)

def Fk : Type := C.Y.Fn

instance : Field (Fk C) := inferInstanceAs (Field C.Y.Fn)

instance : Algebra c.F (Fk C) := RingHom.toAlgebra (constF e C.Y : c.F →+* C.Y.Fn)

def St (y : C.Y.X) : Type := C.Y.X.presheaf.stalk y

instance (y : C.Y.X) : CommRing (St C y) := inferInstanceAs (CommRing (C.Y.X.presheaf.stalk y))

def pt (y : C.Y.X) : Sp (St C y) ⟶ C.Y.X := stalkPt C.Y y

instance (y : C.Y.X) : Mono (pt C y) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk y))

instance (y : C.Y.X) : Algebra c.F (St C y) := (Spec.preimage (pt C y ≫ C.π ≫ genStr Z)).hom.toAlgebra

theorem pt_str (y : C.Y.X) : pt C y ≫ C.π ≫ genStr Z = spMap (algebraMap c.F (St C y)) := (Spec.map_preimage _).symm

def gpt : Sp (Fk C) ⟶ C.Y.X := genericPt C.Y

def fr0 : FrPt Xo c (Fk C) := C.y0

theorem frame_point_over : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.jQ = gpt C ≫ C.π := C.y0_x

theorem str_of_over {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T} {x : Sp T ⟶ gen Z}
    (h : GlobalTheory.AllWt.ptF z ≫ Z.jQ = x) : x ≫ genStr Z = spMap (algebraMap c.F T) := by
  rw [← h, Category.assoc, Z.jQ_over, ptF_snd]


variable {C} in
def algOf {T : Type} [CommRing T] [Algebra c.F T] {y : C.Y.X} (ψ : St C y →+* T) {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) : St C y →ₐ[c.F] T :=
  { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F (St C y))) (by
      rw [← sp_comp, ← pt_str, ← Category.assoc, h, hp])) a }

def toFkR (y : C.Y.X) : St C y →+* Fk C := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField

theorem toFkR_pt (y : C.Y.X) : spMap (toFkR C y) ≫ pt C y = gpt C :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

def toFk (y : C.Y.X) : St C y →ₐ[c.F] Fk C :=
  algOf (toFkR C y) (toFkR_pt C y) (by rw [← Category.assoc]; exact str_of_over (frame_point_over C))

theorem toFk_pt (y : C.Y.X) : spMap (toFk C y).toRingHom ≫ pt C y = gpt C := toFkR_pt C y

theorem toFk_injective (y : C.Y.X) : Function.Injective (toFk C y) :=
  IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField

variable {C}

theorem specializes_of {T : Type} [CommRing T] {y : C.Y.X} {ψ : St C y →+* T} {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (s : Sp T) : p s ⤳ y := by
  have : p s ∈ Set.range (C.Y.X.fromSpecStalk y) := ⟨spMap ψ s, by rw [← h]; rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem hom_eq {T : Type} [CommRing T] {y : C.Y.X} {ψ ψ' : St C y →+* T} (h : spMap ψ ≫ pt C y = spMap ψ' ≫ pt C y) :
    ψ = ψ' := sp_inj ((cancel_mono _).1 h)

theorem exists_spec {y y' : C.Y.X} (h : y' ⤳ y) : ∃ sp : St C y →ₐ[c.F] St C y',
    spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  have k : spMap (R := St C y) (R' := St C y') (C.Y.X.presheaf.stalkSpecializes h).hom ≫ pt C y = pt C y' :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  refine ⟨algOf _ k (pt_str C y'), k, fun a => ?_⟩
  refine DFunLike.congr_fun (hom_eq (ψ := (toFk C y').toRingHom.comp (algOf _ k (pt_str C y')).toRingHom)
    (ψ' := (toFk C y).toRingHom) ?_) a
  rw [← sp_comp, Category.assoc, toFk_pt]
  exact (congrArg (_ ≫ ·) k).trans (toFk_pt C y')


variable (C) in
def rationalEigenFrame : EigFrame Z (algebraMap c.F (Fk C)) (gpt C ≫ C.π ≫ genι Z) := C.f0


variable (C) in
structure Chart (y : C.Y.X) (P : FrPt Xo c (St C y)) (t : Ix Dw → (Fk C)ˣ) : Prop where
  ov : GlobalTheory.AllWt.ptF P ≫ Z.jQ = pt C y ≫ C.π
  bm : BM (toFk C y) t P (fr0 C)

end Cpt

section Wit

variable {C : FlagCpt Z e} {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']


variable (C) in
structure Wit (p : Sp T ⟶ C.Y.X) (z : FrPt Xo c T) : Type where
  y : C.Y.X
  ψ : St C y →ₐ[c.F] T
  P : FrPt Xo c (St C y)
  t : Ix Dw → (Fk C)ˣ
  t' : Ix Dw → Tˣ
  chart : Chart C y P t
  hp : spMap ψ.toRingHom ≫ pt C y = p
  bm : BM ψ t' P z

variable {p : Sp T ⟶ C.Y.X} {z : FrPt Xo c T}

theorem Wit.ov (w : Wit C p z) : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π := by
  rw [ptF_map w.bm.x_eq, Category.assoc, w.chart.ov, ← Category.assoc, w.hp]

theorem carries_iff {k : Type} [Field k] {p : Sp k ⟶ C.Y.X} {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} :
    C.Carries p g ↔ ∃ (y : C.Y.X) (ψ : St C y →+* k) (φ₁ : c.F →+* St C y)
    (f : EigFrame Z φ₁ (pt C y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fk C)ˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), p = spMap ψ ≫ pt C y ∧
      f.Tri (toFk C y).toRingHom (rationalEigenFrame C) t ∧ f.Tri ψ g t' := Iff.rfl

theorem dual_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

end Wit

section Global

variable {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ)
  (s : ∀ k, Fk (Φ.C k)) {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

variable {Φ ex s}

variable (hex : ex none = 0)
  (hs : ∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k))

include hex hs


end Global

end Descent

end GlobalTheory.ShFam
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.CoordComp

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)


open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem comb_comb {S : Type} [CommRing S] [IsLocalRing S] {x : Sp S ⟶ X} {m n : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    {w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    {u : Sp (DualNumber S) ⟶ t.G.left} (hu : IsTanAtG t x u) (B : Fin n → Fin m → S) (a : Fin n → S)
    (h1 : ∀ i, IsCombAtG t x v (B i) (w i)) (h2 : IsCombAtG t x w a u) :
    IsCombAtG t x v (fun k => ∑ j, a j * B j k) u := by
  obtain ⟨d, xc, hx⟩ := GlobalTheory.ShFam.EigLoc.exists_chart t x
  choose p hp using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hv j)
  choose q hq using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hw j)
  obtain ⟨r, rfl⟩ := GlobalTheory.LieLocBasis.vec_exists hx _ hu
  obtain rfl : v = _ := funext hp
  obtain rfl : w = _ := funext hq
  simp only [GlobalTheory.LieLocBasis.comb_iff hx] at h1 h2 ⊢
  rw [h2]
  simp only [h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem spMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := (spMap_comp' _ _).symm

theorem dualMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]

end GlobalTheory.ShFam.CoordComp


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.CoordComp in
theorem GlobalTheory.ShFam.CoordComp.coord_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (g : EigFrame Z φ' x') (R'' : Type) [CommRing R''] (φ'' : c.F →+* R'') (x'' : Sp R'' ⟶ Z.X) (h : EigFrame Z φ'' x'') (ψ : R →+* R') (ψ' : R' →+* R'') (A : Mat Dw.mult R') (A' : Mat Dw.mult R''), IsLocalRing R'' → f.Coord ψ g A → g.Coord ψ' h A' → f.Coord (ψ'.comp ψ) h (A' * A.map ψ') := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' g R'' _ φ'' x'' h ψ ψ' A A' hl h₁ h₂
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  subst a1 a2 b1 b2
  refine ⟨by rw [spMap_comp2, Category.assoc], rfl, fun τ i => ?_⟩
  have e : (fun k => spMap (dualMap (ψ'.comp ψ)) ≫ f.v τ k) =
      fun k => spMap (dualMap ψ') ≫ spMap (dualMap ψ) ≫ f.v τ k :=
    funext fun k => by rw [dualMap_comp2, spMap_comp2, Category.assoc]
  rw [e]
  exact comb_comb Z.t
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)))
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (g.tan τ j)) (h.tan τ i) (fun j k => ψ' (A τ j k)) (A' τ i)
    (fun j => comb_map Z.t ψ' (a3 τ j)) (b3 τ i)
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

namespace GlobalTheory.CuspFrom

theorem arc_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) [Algebra c.F ℂ⸨X⸩] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (y : FrPt Xo c ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → ArcBasis W (fun τ => σ.comp (embK c τ)) e → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → χ (IsLocalRing.closedPoint (PowerSeries ℂ)) ∉ abLocus Y.t.G → BdExt Y ((PowerSeries.C (R := ℂ)).comp σ) y := by
  intro E _ _ _ H Dw l Xo c σ O _ β Y a χ W _ e th y hF hχ hβ hB hA hab
  have hι : algebraMap (PowerSeries ℂ) ℂ⸨X⸩ = HahnSeries.ofPowerSeries ℤ ℂ := rfl
  have hFr : algebraMap c.F ℂ⸨X⸩ = ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))).comp σ :=
    RingHom.ext hF
  have hcond : χ ≫ Y.s = spMap ((PowerSeries.C (R := ℂ)).comp σ) ≫ spMap β := by
    rw [hχ, OpenReg.spMap_comp, OpenReg.spMap_comp]
  let χ' : Sp (PowerSeries ℂ) ⟶ gen Y := pullback.lift χ (spMap ((PowerSeries.C (R := ℂ)).comp σ)) hcond
  have hχ'1 : χ' ≫ genι Y = χ := pullback.lift_fst _ _ _
  have hχ'2 : χ' ≫ genStr Y = spMap ((PowerSeries.C (R := ℂ)).comp σ) := pullback.lift_snd _ _ _
  obtain ⟨v, hvL, hv⟩ := hB
  obtain ⟨z, t', m1, m2, φ, hz, hzx, hφ, h0, hm, hu, -⟩ := hA
  have hG : Out.GlobalFnsSt := known_holds.laws.globalFns

  have hzF : z = GlobalTheory.AllWt.ptF y := by
    apply pullback.hom_ext
    · rw [hzx, Descent.ptF_fst]
    · rw [Descent.ptF_snd]
      apply hβ.right_cancellation
      have e1 : z ≫ pullback.snd _ _ = z ≫ Y.jQ ≫ pullback.snd _ _ := by rw [Y.jQ_over]
      rw [e1, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc z, ← Category.assoc (z ≫ Y.jQ)]
      change (z ≫ Y.j) ≫ Y.s = _
      rw [hz, Category.assoc, hχ, OpenReg.spMap_comp, OpenReg.spMap_comp, OpenReg.spMap_comp, hFr]
  have hw : ∀ τ k, (v τ k).left ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
    fun τ k => (Over.w (v τ k)).trans (Category.comp_id _).symm
  let g : EigFrame Y ((PowerSeries.C (R := ℂ)).comp σ) (χ' ≫ genι Y) :=
    { v := fun τ k => (v τ k).left ≫ W.m.φ
      tan := fun τ k => by
        rw [hχ'1]
        exact (OpenReg.tan_iff W.m (Category.id_comp χ) (hw τ k)).2
          ((DepthExt.tan_iff W.t (v τ k)).1 ((hv τ).1 k).1)
      eig := fun τ k x => by
        exact (OpenReg.eig_iff W.m (hw τ k) x _).2 (((hv τ).1 k).2 x)
      basis := fun τ w htan heig => by
        rw [hχ'1] at htan ⊢
        obtain ⟨w0, hw01, hw02⟩ := OpenReg.exists_lift W.m (spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))))
          w (by rw [htan.1])
        subst hw02
        have hw0 : w0 ≫ W.t.G.hom = spMap (algebraMap (PowerSeries ℂ) (DualNumber (PowerSeries ℂ))) ≫ 𝟙 _ :=
          hw01.trans (Category.comp_id _).symm
        let W0 : epsR (PowerSeries ℂ) ⟶ W.t.G := Over.homMk w0 hw01
        have t0 : IsTangent W0 := (DepthExt.tan_iff W.t W0).2 ((OpenReg.tan_iff W.m (Category.id_comp χ) hw0).1 htan)
        have e0 : ∀ x : 𝓞 E, (W0 ≫ W.t.act.act x).left =
            spMap (epsScaleR (PowerSeries.C (R := ℂ) ((σ.comp (embK c τ)) x))) ≫ W0.left := fun x =>
          (OpenReg.eig_iff W.m hw0 x _).1 (heig x)
        obtain ⟨cf, hcf, hu1⟩ := (hv τ).2 W0 t0 e0
        refine ⟨cf, ?_, fun cf' hcf' => hu1 cf' ?_⟩
        · exact (OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf hw0).2
            ((DepthExt.comb_iff W.t (v τ) cf W0).1 hcf)
        · exact (DepthExt.comb_iff W.t (v τ) cf' W0).2
            ((OpenReg.comb_iff W.m (Category.id_comp χ) (hw τ) cf' hw0).1 hcf') }
  refine ⟨χ', g, hχ'2, ?_, fun τ k => ?_, ?_⟩
  · rw [← hzF]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hχ'1]
      exact hz
    · rw [Category.assoc, Category.assoc, hχ'2, Y.jQ_over, hzF, Descent.ptF_snd, OpenReg.spMap_comp, hFr]
  · obtain ⟨v1, u', hL, h1, h2, h3⟩ := hu τ k
    obtain rfl : v1 = v τ k := (ConstLie.main hG E H Dw l Xo c O β Y ℂ (σ.comp β) a χ W (e τ k)).1.unique hL (hvL τ k)
    refine ⟨u' ≫ φ, ?_, ?_, ?_⟩
    · rw [Category.assoc, hφ, ← Category.assoc, h3, hzF]
    · rw [Category.assoc, h0, h1]
    · rw [Category.assoc, hm, ← Category.assoc, h2, Category.assoc]
  · rw [mem_genBd_iff]
    rw [← hχ'1] at hab
    exact hab

end GlobalTheory.CuspFrom
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigCoord

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.FlagBundle
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}

theorem exists_basis (hx : IsUnivChart _ n xc) (g : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ B : Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ), ∀ i, g.v τ i = vec Z.t x xc (B i) := by
  choose e he using fun i => vec_exists hx (g.v τ i) (g.tan τ i)
  have hm : ∀ i, e i ∈ eig c φ hx τ := fun i => (vec_eig_iff hx _ _).1 (by rw [← he i]; exact g.eig τ i)
  let b : Fin (Dw.mult τ) → eig c φ hx τ := fun i => ⟨e i, hm i⟩
  have key : ∀ w : eig c φ hx τ, ∃! a : Fin (Dw.mult τ) → R, ∑ j, a j • b j = w := fun w => by
    have h := g.basis τ (vec Z.t x xc w) (vec_tan hx _) ((vec_eig_iff hx _ _).2 w.2)
    rw [show g.v τ = fun j => vec Z.t x xc (e j) from funext he] at h
    simp only [comb_iff hx] at h
    refine (existsUnique_congr fun a => ?_).1 h
    rw [Subtype.ext_iff, eq_comm]
    simp [b]
  have li : LinearIndependent R b := Fintype.linearIndependent_iff.2 fun a ha i =>
    congrFun ((key 0).unique ha (show ∑ j, (0 : Fin (Dw.mult τ) → R) j • b j = 0 by simp)) i
  have sp' : ⊤ ≤ Submodule.span R (Set.range b) := fun w _ =>
    (Submodule.mem_span_range_iff_exists_fun R).2 (key w).exists
  exact ⟨Module.Basis.mk li sp', fun i => by rw [Module.Basis.mk_apply]; exact he i⟩

theorem exists_frame (hx : IsUnivChart _ n xc) (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R (eig c φ hx τ)) :
    ∃ g : EigFrame Z φ x, ∀ τ i, g.v τ i = vec Z.t x xc (B τ i) := by
  refine ⟨⟨fun τ i => vec Z.t x xc (B τ i), fun τ i => vec_tan hx _, fun τ i => (vec_eig_iff hx _ _).2 (B τ i).2,
    fun τ w hw he => ?_⟩, fun _ _ => rfl⟩
  obtain ⟨cc, rfl⟩ := vec_exists hx w hw
  let v : eig c φ hx τ := ⟨cc, (vec_eig_iff hx _ _).1 he⟩
  have k : ∀ a, IsCombAtG Z.t x (fun i => vec Z.t x xc (B τ i)) a (vec Z.t x xc cc) ↔ (B τ).equivFun v = a := fun a => by
    rw [comb_iff hx, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [v]
  simp only [k]
  exact existsUnique_eq'

theorem exists_basis_of_isUnit {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B : Module.Basis ι R M) (A : Matrix ι ι R) (h : IsUnit A.det) :
    ∃ B' : Module.Basis ι R M, ∀ i, B' i = ∑ j, A i j • B j := by
  refine ⟨B.map (Matrix.toLinearEquiv B A.transpose (by rwa [Matrix.det_transpose])), fun i => ?_⟩
  simp [Matrix.toLin_self]

theorem isUnit_det_of_basis {M ι : Type} [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
    (B B' : Module.Basis ι R M) (A : Matrix ι ι R) (h : ∀ i, B' i = ∑ j, A i j • B j) : IsUnit A.det := by
  have e : A = (B.toMatrix B').transpose := by
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, h i, Module.Basis.repr_sum_self]
  rw [e, Matrix.det_transpose]
  exact B.isUnit_det B'

end GlobalTheory.ShFam.EigCoord


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.EigCoord GlobalTheory.LieLocBasis in
theorem GlobalTheory.ShFam.EigCoord.coord_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (ψ : R →+* R'), IsLocalRing R' → f.Stable → x' = spMap ψ ≫ x → φ' = ψ.comp φ → (∀ g : EigFrame Z φ' x', (∃! A : Mat Dw.mult R', f.Coord ψ g A) ∧ ∀ A, f.Coord ψ g A → ∀ τ, IsUnit (A τ).det) ∧ ∀ A : Mat Dw.mult R', (∀ τ, IsUnit (A τ).det) → ∃ g : EigFrame Z φ' x', f.Coord ψ g A := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' ψ _ hf hx' hφ'
  subst hx' hφ'
  obtain ⟨g₀, hg₀⟩ := hf R' ψ
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t (spMap ψ ≫ x)
  choose B₀ hB₀ using exists_basis hx g₀
  have hv : ∀ τ, (fun k => spMap (dualMap ψ) ≫ f.v τ k) = g₀.v τ := fun τ => funext fun k => (hg₀ τ k).symm
  have key : ∀ (g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x))
      (B : ∀ τ, Module.Basis (Fin (Dw.mult τ)) R' (eig c (ψ.comp φ) hx τ)),
      (∀ τ i, g.v τ i = vec Z.t _ xc (B τ i)) → ∀ A : Mat Dw.mult R',
        f.Coord ψ g A ↔ ∀ τ i, B τ i = ∑ j, A τ i j • B₀ τ j := fun g B hB A => by
    simp only [EigFrame.Coord, true_and]
    refine forall_congr' fun τ => forall_congr' fun i => ?_
    rw [hv, hB, show g₀.v τ = fun j => vec Z.t _ xc (B₀ τ j) from funext (hB₀ τ), comb_iff hx, Subtype.ext_iff]
    simp
  refine ⟨fun g => ⟨?_, fun A hA τ => ?_⟩, fun A hA => ?_⟩
  · choose A hA hu using fun τ i => g₀.basis τ (g.v τ i) (g.tan τ i) (g.eig τ i)
    refine ⟨A, ⟨rfl, rfl, fun τ i => by rw [hv]; exact hA τ i⟩, fun A' hA' => ?_⟩
    funext τ i
    exact hu τ i _ (by have := hA'.2.2 τ i; rwa [hv] at this)
  · choose B hB using exists_basis hx g
    exact isUnit_det_of_basis (B₀ τ) (B τ) (A τ) ((key g B hB A).1 hA τ)
  · choose B hB using fun τ => exists_basis_of_isUnit (B₀ τ) (A τ) (hA τ)
    obtain ⟨g, hg⟩ := exists_frame hx B
    exact ⟨g, (key g B hg A).2 hB⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_base_field_multiple_of_nth_root_complexification : ∀ (K : Type) [Field K] [Algebra K ℂ] (A : Type) [CommRing A] [Algebra K A] [IsDomain (ℂ ⊗[K] A)] (n : ℕ) (w : ℂ ⊗[K] A) (C : ℂ) (u : A), 0 < n → C ≠ 0 → u ≠ 0 → w ^ n = C ⊗ₜ[K] u → ∃ (a : K) (b : A), a ≠ 0 ∧ u = a • b ^ n := by
  first | exact @GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul | exact GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul | (intros; apply GlobalTheory.KeyFourth.exists_eq_smul_pow_of_pow_eq_tmul <;> assumption)
end
