module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle131
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle004
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

def wch (i : X ⟶ PSpace K N) (j : Fin (N + 1)) : X.Opens := i ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)

def uy (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (k : Fin m) : X.Opens :=
  i ⁻¹ᵁ Proj.basicOpen _ (y k)

def wK (q : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (s : ℕ) (k : Fin m) : ObjectProperty (Thick (smFun X q)) :=
  St (TF 1 s) (Set.range fun j => uy i y k ⊓ wch i j)

def wU (q : X ⟶ Spec (CommRingCat.of K)) (i : X ⟶ PSpace K N) {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (s : ℕ) : ObjectProperty (Thick (smFun X q)) :=
  fun T => ∃ k, wK q i y s k T

def yQ {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) :
    Γ(PSpace K N, Proj.basicOpen _ (y k')) :=
  (Proj.awayToSection _ (y k')).hom
    (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

def E.LineData.pb {X X' : Scheme.{0}} (D : E.LineData X) (f : X' ⟶ X) : E.LineData X' where
  Y := pullback D.f f
  f := pullback.snd D.f f
  sm := by have := D.sm; infer_instance
  surj := by have := D.surj; infer_instance
  u a b h := D.u (a ≫ pullback.fst _ _) (b ≫ pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
  nat g a b h := by
    have := D.nat g (a ≫ pullback.fst _ _) (b ≫ pullback.fst _ _)
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
    simpa only [Category.assoc] using this
  coc a b c h h' := D.coc _ _ _ _ _

namespace Pb

def plogK {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) (x : B) : B :=
  ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : B) * δ.dpow (k + 1) x

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

structure CLiftK {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) (D : E.LineData X) where
  p : ∀ c : C, Spec (CommRingCat.of ((g.obj c).B ⧸ (g.obj c).J)) ⟶ D.Y
  hp : ∀ c : C, p c ≫ D.f = pt (g.obj c)
  w : ∀ {c c' : C}, (c ⟶ c') → (g.obj c').Bˣ
  hw : ∀ {c c' : C} (φ : c ⟶ c')
    (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
    Ideal.Quotient.mk (g.obj c').J (w φ) = (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c').B ⧸ (g.obj c').J))).hom.hom
      (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) (p c') h)

def CLiftK.r {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (s : ComposableArrows C 2) : (g.obj (s.obj (Fin.last 2))).Bˣ :=
  Units.map (g.map (s.map' 1 2)).φ.toMonoidHom (Λ.w (s.map' 0 1)) * Λ.w (s.map' 1 2) * (Λ.w (s.map' 0 2))⁻¹


variable (q) in
def IsFirstChernDeRham (D : E.LineData X) (x : HdR q 2) : Prop :=
  ∀ (s : ℕ) (C : Type 1) [Category.{0} C] (g : C ⥤ Thick (smFun X q)), (∀ c, (g.obj c).pdPow s = ⊥) →
    (∀ c, ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V (g.obj c)) →
    ∀ Λ : CLiftK g D, ∃ (z : CH.Cn (g ⋙ O (smFun X q)) 2) (hz : CH.d _ 2 z = 0),
      (∀ σ : ComposableArrows C 2, (show (g.obj (σ.obj (Fin.last 2))).B from z σ) =
        plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (O (smFun X q)) g).pull 2 x

end K

section O1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem X_mem (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 1 :=
  MvPolynomial.isHomogeneous_X R j

abbrev ChartR (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) : Type :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)

def chart (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) : Spec (CommRingCat.of (ChartR R N j)) ⟶ PSpace R N :=
  Proj.awayι _ (MvPolynomial.X j) (X_mem R N j) one_pos

def ratio (R : Type) [CommRing R] (N : ℕ) (j k : Fin (N + 1)) : ChartR R N j :=
  HomogeneousLocalization.Away.mk _ (X_mem R N j) 1 (MvPolynomial.X k) (by simpa using X_mem R N k)

def IsTautologicalLineAt {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace R N) : Prop :=
  Etale D.f ∧ ∃ s : ∀ j : Fin (N + 1), pullback i (chart R N j) ⟶ D.Y,
    ∃ hs : ∀ j, s j ≫ D.f = pullback.fst _ _,
    ∀ (V : Scheme.{0}) (j k : Fin (N + 1)) (a : V ⟶ pullback i (chart R N j)) (b : V ⟶ pullback i (chart R N k))
      (h : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _),
      ((D.u (a ≫ s j) (b ≫ s k) (by rw [Category.assoc, Category.assoc, hs, hs, h]) : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) =
        (a ≫ pullback.snd _ _).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom (ratio R N j k))

def IsTautologicalLine {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (D : E.LineData X) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = p ∧ IsTautologicalLineAt D N i

end O1

end Pb

end CrystallineSemistableComparison
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] [CharZero K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

theorem trace_chart (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (u : Fin (n + 1) → torusS K t S)
    (hinj : Function.Injective (MvPolynomial.aeval u : MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t S))
    (hloc : ∀ a : torusS K t S, ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval u g) ∧ a * MvPolynomial.aeval u g = MvPolynomial.aeval u f)
    (hfr : ∀ k, ∃ a' ∈ torusS K t S, a' ≠ 0 ∧ (t k : R) * a' ∈ torusS K t S)
    (B' : Subalgebra K R) (hTB : torusS K t S ≤ B') (hFG : B'.FG) (hInt : ∀ b ∈ B', IsIntegral (torusS K t S) b)
    (hFrac : ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b)
    (E : Fin (n + 1) → Derivation K R R) (hE : ∀ k j, E k (u j : R) = if k = j then 1 else 0)
    {m : ℕ} (κ : Fin m → Fin (n + 1)) (hκ : Function.Injective κ) :
    ∀ y ∈ jacS B' E κ, ∃ a ∈ torusS K t S,
      algebraMap (fldF K t) (FractionRing R)
        (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) y)) =
          algebraMap R (FractionRing R) a := by
  classical

  have hι : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)
  have hιne : ∀ r : R, r ≠ 0 → algebraMap R (FractionRing R) r ≠ 0 := fun r hr h =>
    hr (hι (h.trans (map_zero _).symm))

  letI : Algebra (torusS K t S) B' := (Subalgebra.inclusion hTB).toRingHom.toAlgebra
  haveI : IsScalarTower K (torusS K t S) B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAB : Function.Injective (algebraMap (torusS K t S) B') := Subalgebra.inclusion_injective hTB
  let f : B' →ₐ[torusS K t S] R := { B'.val with commutes' := fun _ => rfl }
  haveI : Algebra.IsIntegral (torusS K t S) B' :=
    ⟨fun b => (isIntegral_algHom_iff f Subtype.val_injective).mp (hInt b b.2)⟩
  haveI : Algebra.FiniteType K B' := Subalgebra.fg_iff_finiteType B' |>.mp hFG
  haveI : Algebra.FiniteType (torusS K t S) B' := Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  haveI : Module.Finite (torusS K t S) B' := Algebra.IsIntegral.finite

  let ψ : torusS K t S →+* fldF K t :=
    { toFun := fun a => ⟨algebraMap R (FractionRing R) a, torus_mem_fldF t S a a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ (a : R) b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ (a : R) b) }
  letI : Algebra (torusS K t S) (fldF K t) := ψ.toAlgebra
  have hψ : ∀ a : torusS K t S, ((algebraMap (torusS K t S) (fldF K t) a : fldF K t) : FractionRing R) =
      algebraMap R (FractionRing R) a := fun _ => rfl
  have hψinj : Function.Injective (algebraMap (torusS K t S) (fldF K t)) := fun a b h =>
    Subtype.ext (hι (by rw [← hψ, ← hψ, h]))

  have hQ : ∀ z ∈ fldF K t, ∃ x y : torusS K t S, algebraMap R (FractionRing R) (y : R) ≠ 0 ∧
      z = algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y := fun z hz => by
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a', ha', ha'0, hta⟩ := hfr k
      refine ⟨⟨_, hta⟩, ⟨a', ha'⟩, hιne _ ha'0, ?_⟩
      simp only [map_mul]
      rw [mul_div_assoc, div_self (hιne _ ha'0), mul_one]
    | algebraMap c =>
      refine ⟨algebraMap K _ c, 1, by simpa using one_ne_zero, ?_⟩
      simp [IsScalarTower.algebraMap_apply K R (FractionRing R)]
    | add x y _ _ hx hy =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      obtain ⟨y1, y2, hy2, rfl⟩ := hy
      refine ⟨x1 * y2 + y1 * x2, x2 * y2, by simpa using mul_ne_zero hx2 hy2, ?_⟩
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul, map_add (f := _), map_mul]
      rw [div_add_div _ _ hx2 hy2]
      ring
    | inv x _ hx =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      by_cases h1 : algebraMap R (FractionRing R) (x1 : R) = 0
      · exact ⟨0, 1, by simpa using one_ne_zero, by simp [h1]⟩
      · exact ⟨x2, x1, h1, by rw [inv_div]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      obtain ⟨y1, y2, hy2, rfl⟩ := hy
      refine ⟨x1 * y1, x2 * y2, by simpa using mul_ne_zero hx2 hy2, ?_⟩
      simp only [Subalgebra.coe_mul, map_mul]
      rw [div_mul_div_comm]
  haveI : FaithfulSMul (torusS K t S) (fldF K t) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hψinj
  haveI : IsFractionRing (torusS K t S) (fldF K t) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, hy, hz⟩ := hQ z z.2
    refine ⟨x, y, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div, hψ, hψ, ← hz]

  have hBL : Function.Injective (algebraMap B' (FractionRing R)) := fun a b h => Subtype.ext (hι h)
  haveI : FaithfulSMul B' (FractionRing R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  haveI : IsFractionRing B' (FractionRing R) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    obtain ⟨b1, hb1, b1', hb1', hb1'0, hr⟩ := hFrac r
    obtain ⟨b2, hb2, b2', hb2', hb2'0, hs'⟩ := hFrac s
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hb20 : b2 ≠ 0 := by rw [← hs']; exact mul_ne_zero hs0 hb2'0
    refine ⟨⟨b1 * b2', mul_mem hb1 hb2'⟩, ⟨b1' * b2, mul_mem hb1' hb2⟩, ?_⟩
    change _ = algebraMap R (FractionRing R) (b1 * b2') / algebraMap R (FractionRing R) (b1' * b2)
    have hden : algebraMap R (FractionRing R) (b1' * b2) ≠ 0 := hιne _ (mul_ne_zero hb1'0 hb20)
    rw [div_eq_div_iff (hιne _ hs0) hden, ← map_mul, ← map_mul, ← hr, ← hs']
    congr 1
    ring
  haveI : IsScalarTower (torusS K t S) (fldF K t) (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (torusS K t S) B' (FractionRing R) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  choose Dl hDl using fun k => frac_deriv (E k)
  have hDu : ∀ k j, Dl k (algebraMap (torusS K t S) (FractionRing R) (u j)) = if k = j then 1 else 0 := by
    intro k j
    change Dl k (algebraMap R (FractionRing R) (u j : R)) = _
    rw [hDl, hE]
    split_ifs <;> simp
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, bs, rfl⟩ := hy
    obtain ⟨a, ha⟩ := GlobalTheory.T.fraction_field_transcendence_basis_ext K (n + 1) (torusS K t S) u hinj hloc B' hAB (fldF K t) (FractionRing R)
      Dl hDu m ⟨κ, hκ⟩ b bs
    refine ⟨a, a.2, ?_⟩
    have hX : algebraMap R (FractionRing R) ((b : R) * (Matrix.of fun k l => E (κ k) (bs l : R)).det) =
        algebraMap B' (FractionRing R) b *
          (Matrix.of fun k l => Dl ((⟨κ, hκ⟩ : Fin m ↪ Fin (n + 1)) k) (algebraMap B' (FractionRing R) (bs l))).det := by
      rw [map_mul, RingHom.map_det]
      refine congrArg₂ (· * ·) rfl (congrArg Matrix.det ?_)
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rw [← hDl]
      rfl
    rw [← hψ, ha, hX]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by simp only [map_add (f := _)] at hxa hyb ⊢; rw [hxa, hyb]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨-a, neg_mem ha, by simp only [map_neg] at hxa ⊢; rw [hxa]⟩

end CrystallineSemistableComparison.Pb
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev grK (K : Type) [Field K] (N : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

theorem xv_mem (K : Type) [Field K] (N : ℕ) (j : Fin (N + 1)) : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ∈ grK K N 1 :=
  MvPolynomial.isHomogeneous_X K j

def evV {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K)
    (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) : HomogeneousLocalization.Away (grK K N) g →+* Γ(X, V) :=
  (i.appLE _ V h).hom.comp (Proj.awayToSection (grK K N) g).hom

def homIdeal {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) : Ideal (MvPolynomial (Fin (N + 1)) K) :=
  Ideal.span {f | ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), ∀ j : Fin (N + 1),
    evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0}

def yS {K : Type} [Field K] {N m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) :
    MvPolynomial (Fin (N + 1)) K :=
  ∏ k ∈ S, y k

theorem yS_mem {K : Type} [Field K] {N m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (S : Finset (Fin m)) : yS y S ∈ grK K N (S.card * e) := by
  have h := MvPolynomial.IsHomogeneous.prod S y (fun _ => e) (fun k _ => hy k)
  simpa [yS, Finset.sum_const, smul_eq_mul] using h

theorem aeval_mem {K : Type} [Field K] {N m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (S : Finset (Fin m)) {j : ℕ} (c : MvPolynomial (Fin m) K)
    (hc : c.IsHomogeneous (j * S.card)) : MvPolynomial.aeval y c ∈ grK K N (j • (S.card * e)) := by
  have h := hc.aeval y hy
  rw [MvPolynomial.mem_homogeneousSubmodule, smul_eq_mul]
  convert h using 1
  ring

def yRatio {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : Γ(PSpace K N, Proj.basicOpen _ (y 0)) :=
  (Proj.awayToSection _ (y 0)).hom
    (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y 0)).2 (hy 0)) 1 (y k.succ)
      (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k.succ)).2 (hy k.succ)))

def tV {K : Type} [Field K] {X : Scheme.{0}} {N e d : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (V : X.Opens)
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (k : Fin d) : Γ(X, V) :=
  (i.appLE _ V (hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0))).hom (yRatio y hy k)

abbrev resO {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) : Γ(X, W) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom

theorem le_biInf_of_le {X : Scheme.{0}} {m : ℕ} {U : Fin m → X.Opens} {V : X.Opens} (hV : V ≤ ⨅ k, U k)
    (S : Finset (Fin m)) : V ≤ ⨅ k ∈ S, U k :=
  hV.trans (le_iInf₂ fun k _ => iInf_le U k)

theorem strV_res {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : V ≤ W) : strV q V = (resO h).comp (strV q W) := by
  change _ = CommRingCat.Hom.hom (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top) ≫
      X.presheaf.map (homOfLE h).op)
  rw [Category.assoc, Scheme.Hom.appLE_map]
  rfl

end CrystallineSemistableComparison.Pb
end
end
