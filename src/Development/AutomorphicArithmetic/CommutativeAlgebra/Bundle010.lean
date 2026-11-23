module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Development.EtaleCohomology.EtaleSheaves.Bundle003

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.PicD

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)) ⟨Additive.ofMul v⟩

theorem unitSec_one {U : Scheme.{0}} : unitSec (1 : (Γ(U, ⊤))ˣ) = 0 := by
  unfold unitSec ofRings.sec
  exact map_zero (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have h := congrArg (fun f => (ModuleCat.Hom.hom f)
    (⟨Additive.ofMul u⟩ : ULift.{1, 0} (Additive (Γ(U, ⊤))ˣ)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op)
  exact h.symm

end UpperTheory.PicD
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Bc

abbrev prodW (W : Scheme.{0}) : Scheme.{0} ⥤ Scheme.{0} := prod.functor.obj W

set_option backward.isDefEq.respectTransparency false in
theorem prodW_compatible (W : Scheme.{0}) :
    CompatiblePreserving Scheme.etaleTopology.{0} (prodW W) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  have hfst : f₁ ≫ prod.fst = f₂ ≫ prod.fst := by
    have h := congrArg (· ≫ (prod.fst : W ⨯ Z ⟶ W)) e
    simpa using h
  have hsnd : (f₁ ≫ prod.snd) ≫ g₁ = (f₂ ≫ prod.snd) ≫ g₂ := by
    have h := congrArg (· ≫ (prod.snd : W ⨯ Z ⟶ Z)) e
    simpa using h
  let u : X ⟶ (prodW W).obj X := prod.lift (f₁ ≫ prod.fst) (𝟙 X)
  have k₁ : f₁ = u ≫ (prodW W).map (f₁ ≫ prod.snd) := by
    apply prod.hom_ext <;> simp [u]
  have k₂ : f₂ = u ≫ (prodW W).map (f₂ ≫ prod.snd) := by
    apply prod.hom_ext <;> simp [u, hfst]
  have hc := hx (f₁ ≫ prod.snd) (f₂ ≫ prod.snd) hg₁ hg₂ hsnd
  calc ℱ.obj.map f₁.op (x g₁ hg₁)
      = ℱ.obj.map u.op (ℱ.obj.map ((prodW W).map (f₁ ≫ prod.snd)).op (x g₁ hg₁)) := by
        rw [← Functor.map_comp_apply, ← op_comp, ← k₁]
    _ = ℱ.obj.map u.op (ℱ.obj.map ((prodW W).map (f₂ ≫ prod.snd)).op (x g₂ hg₂)) :=
        congrArg _ hc
    _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by
        rw [← Functor.map_comp_apply, ← op_comp, ← k₂]

set_option backward.isDefEq.respectTransparency false in
theorem prodW_cover (W : Scheme.{0}) :
    CoverPreserving Scheme.etaleTopology.{0} Scheme.etaleTopology.{0} (prodW W) := by
  constructor
  intro U S hS
  rw [GlobalTheory.T.mem_etale_covering_sieves_iff_points]
  intro u
  obtain ⟨V, j, v, hj, hv, hS'⟩ := (GlobalTheory.T.mem_etale_covering_sieves_iff_points U S).1 hS ((prod.snd : W ⨯ U ⟶ U) u)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := (prod.snd : W ⨯ U ⟶ U)) (g := j) u v hv.symm
  haveI := hj
  refine ⟨pullback (prod.snd : W ⨯ U ⟶ U) j, pullback.fst _ _, z, ?_, hz1, ?_⟩
  · exact MorphismProperty.pullback_fst _ _ hj
  refine ⟨V, j, prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _), hS', ?_⟩
  apply Limits.prod.hom_ext
  · simp
  · simp [pullback.condition]

instance prodW_cont (W : Scheme.{0}) :
    (prodW W).IsContinuous Scheme.etaleTopology.{0} Scheme.etaleTopology.{0} :=
  Functor.isContinuous_of_coverPreserving (prodW_compatible W) (prodW_cover W)

variable (R : Type) [CommRing R]

def pw (W : Scheme.{0}) : Shv R ⥤ Shv R :=
  (prodW W).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) Scheme.etaleTopology.{0} Scheme.etaleTopology.{0}

instance (W : Scheme.{0}) : (pw R W).Additive where
  map_add {F G} {f g} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

variable {R}

abbrev Bc (W : Scheme.{0}) (I : Cx R) : Cx R := ((pw R W).mapHomologicalComplex _).obj I

def Supp (Q : Scheme.{0} → Prop) (P : PSh) : Prop := ∀ U : Scheme.{0}, Nonempty (P.obj (op U)) → Q U

def Acy (Q : Scheme.{0} → Prop) (F : Shv ℤ) : Prop :=
  ∀ P : PSh, Supp Q P → ∀ n : ℤ, 0 < n → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n)

def cl {M F : Shv ℤ} (f : M ⟶ F) : HK ℤ (sgl M) F 0 :=
  CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))

end UpperTheory.Bc
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} (v : Fin N → A)
    (h : Ideal.span (Set.range v) = ⊤) (a b : A) (hab : ∀ j, a * v j = b * v j) : a = b := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range v) := by rw [h]; trivial
  have key : ∀ c ∈ Ideal.span (Set.range v), (a - b) * c = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [sub_mul, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  have h2 := key 1 h1
  rw [mul_one] at h2
  exact sub_eq_zero.1 h2

private theorem fam_inj (D : Type) [CommRing D] (d m : ℕ) {A : Type} [CommRing A]
    (x y : Fin (m + 1) → (L2 D d).obj A)
    (hx : ∀ i j, (L2 D d).rel (x i) (x j)) (hy : ∀ i j, (L2 D d).rel (y i) (y j))
    (h1 : ∀ i, (fstV D d).app A (x i) = (fstV D d).app A (y i))
    (h2 : (x 0).1.1.2 (Fin.last d) = (y 0).1.1.2 (Fin.last d)) : x = y := by
  have hv : ∀ i (j : Fin d), (x i).1.1.2 j.castSucc = (y i).1.1.2 j.castSucc :=
    fun i j => congrFun (congrArg (fun z => z.1.2) (h1 i)) j
  have hr : ∀ i, (x i).1.1.1 = (y i).1.1.1 := fun i => congrArg (fun z => z.1.1) (h1 i)
  refine funext fun i => Subtype.ext (Subtype.ext (Prod.ext (hr i) (funext fun j => ?_)))
  obtain ⟨-, u, hu⟩ := hx i 0
  obtain ⟨-, u', hu'⟩ := hy i 0
  have huu : (u : A) = u' := by
    refine unit_unique (fun j : Fin d => (x 0).1.1.2 j.castSucc) (x 0).2 _ _ fun j => ?_
    have e1 : (x i).1.1.2 j.castSucc = (u : A) * (x 0).1.1.2 j.castSucc := congrFun hu _
    have e2 : (y i).1.1.2 j.castSucc = (u' : A) * (y 0).1.1.2 j.castSucc := congrFun hu' _
    change (u : A) * (x 0).1.1.2 j.castSucc = (u' : A) * (x 0).1.1.2 j.castSucc
    rw [← e1, hv i j, e2, hv 0 j]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have e1 : (x i).1.1.2 (Fin.last d) = (u : A) * (x 0).1.1.2 (Fin.last d) := congrFun hu _
    have e2 : (y i).1.1.2 (Fin.last d) = (u' : A) * (y 0).1.1.2 (Fin.last d) := congrFun hu' _
    change (x i).1.1.2 (Fin.last d) = (y i).1.1.2 (Fin.last d)
    rw [e1, e2, huu, h2]
  · exact hv i j
end
