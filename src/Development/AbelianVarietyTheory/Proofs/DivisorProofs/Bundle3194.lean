module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.PiTensorProduct
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitForm

theorem exists_coords {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (τ : Forms.balForms ℤ O X B) :
    ∃ c : J → B, ∀ a b, (τ : Forms.Bil X B) a b = ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel (O := O) (X := X))
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  refine ⟨fun k => ∑ j, ε.repr (β j) k • Forms.balTensorLift τ (e j), fun a b => ?_⟩
  have h1 (j) : e.repr (Forms.balTensorMk O a b) j =
      ∑ k, ε.repr (β j) k * (ε k : LinearMap.BilinForm ℤ X) a b := by
    have h := congrArg (fun g : PolFan.balForms (star : O → O) X =>
      (g : LinearMap.BilinForm ℤ X) a b) (ε.sum_repr (β j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    exact h.symm

  rw [← Forms.balTensorLift_mk, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
  simp only [map_zsmul]
  simp only [h1, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [_root_.mul_comm]

theorem exists_root {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    [IsAlgClosed (ResidueField V)] {n : ℕ} (hn : IsUnit (n : V)) (u : Vˣ) :
    ∃ v : Vˣ, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue V u) (Nat.pos_of_ne_zero hn0)
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsUnit a := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0] at hz
    exact (residue_ne_zero_iff_isUnit _).2 u.isUnit hz.symm
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian (R := V) (I := maximalIdeal V)
    (Polynomial.X ^ n - Polynomial.C (u : V)) (Polynomial.monic_X_pow_sub_C _ hn0) a
    (by
      rw [← residue_eq_zero_iff]
      simp [hz])
    (by
      refine IsUnit.map _ ?_
      simpa [Polynomial.derivative_X_pow] using ⟨hn, ha.pow _⟩)
  have hy' : y ^ n = u := by
    simpa [sub_eq_zero] using hy
  have hyu : IsUnit y := (isUnit_pow_iff hn0).1 (hy' ▸ u.isUnit)
  exact ⟨hyu.unit, Units.ext (by simpa using hy')⟩

theorem mem_of_diag {O : Type} [CommRing O] (bar : O → O) {w : O} (hw : w + bar w = 1)
    {X : Type} [AddCommGroup X] [Module O X] {G : Type} [CommGroup G] (U : Subgroup G)
    (q : X → X → G) (hs : ∀ a b, q a b = q b a) (ha : ∀ a a' b, q (a + a') b = q a b * q a' b)
    (hb : ∀ (x : O) a b, q (x • a) b = q a (bar x • b)) (hd : ∀ y, q y (w • y) ∈ U) (a b : X) :
    q a b ∈ U := by
  have hr (a b b') : q a (b + b') = q a b * q a b' := by rw [hs, ha, hs b, hs b']
  have h1 : q a (w • b) * q b (w • a) = q a b := by
    rw [hs b, hb, ← hr, ← add_smul, hw, one_smul]
  have h2 : q a b = q (a + b) (w • (a + b)) / (q a (w • a) * q b (w • b)) := by
    rw [smul_add, ha, hr, hr, ← h1, eq_div_iff_mul_eq']
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [h2]
  exact U.div_mem (hd _) (U.mul_mem (hd _) (hd _))

theorem exists_unit_coords : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  intro E _ _ _ H X _ _ _ _ V _ _ _ hV hk n hn m N ε t ht q hs ha hb hd
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  let φ : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V) : V →* FractionRing V)
  have hφ : Function.Injective φ := Units.map_injective hinj
  let τ : Fin m → (FractionRing V)ˣ := fun i =>
    Units.mk0 (algebraMap V (FractionRing V) (t i)) (fun h => ht i (hinj (by rw [h, map_zero])))
  let M : X → X → (FractionRing V)ˣ := fun a b =>
    ∏ i, τ i ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) a b)
  have Ms (a b) : M a b = M b a := Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.1 a b]
  have Ma (a a' b) : M (a + a') b = M a b * M a' b := by
    simp only [M, map_add (f := _), LinearMap.add_apply, mul_add, zpow_add, Finset.prod_mul_distrib]
  have Mb (x : 𝓞 E) (a b) : M (x • a) b = M a (H.bar x • b) :=
    Finset.prod_congr rfl fun i _ => by rw [(ε (.inl i)).2.2 x a b]
  have hmem := mem_of_diag H.bar hw φ.range (fun a b => q a b / M a b)
    (fun a b => by rw [hs, Ms]) (fun a a' b => by rw [ha, Ma, mul_div_mul_comm])
    (fun x a b => by rw [hb, Mb]) (fun y => by
      obtain ⟨u, hu⟩ := hd y
      refine ⟨u, ?_⟩
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      rw [hu]
      simp [M, τ, φ])
  choose u hu using hmem
  have us (a b) : u a b = u b a := hφ (by rw [hu, hu, hs, Ms])
  have ua (a a' b) : u (a + a') b = u a b * u a' b :=
    hφ (by rw [map_mul, hu, hu, hu, ha, Ma, mul_div_mul_comm])
  have ub (x : 𝓞 E) (a b) : u (x • a) b = u a (H.bar x • b) := hφ (by rw [hu, hu, hb, Mb])
  have ur (a b b') : u a (b + b') = u a b * u a b' := by rw [us, ua, us b, us b']
  obtain ⟨c, hc⟩ := exists_coords (O := 𝓞 E) hw ε ⟨Forms.bilOfMul u ua ur, us, ub⟩
  choose v hv using fun k => exists_root hn (c k).toMul
  refine ⟨Sum.elim (fun i => t i * v (.inl i)) (fun j => v (.inr j)),
    fun i => ⟨(v (.inl i))⁻¹, by simp⟩, fun j => Units.isUnit _, fun a b => ?_⟩
  have h1 : u a b = ∏ k, v k ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
    have h := congrArg Additive.toMul (hc a b)
    simp only [toMul_sum, toMul_zsmul, ← hv] at h
    simp only [zpow_mul, zpow_natCast]
    exact h
  have h2 : q a b = M a b * φ (u a b) := by rw [hu, mul_div_cancel]
  rw [h2, h1]
  simp [M, τ, φ, Fintype.prod_sum_type, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.UnitForm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinGlue
open GlobalTheory.SiegelDescent GlobalTheory.SiegDesc GlobalTheory.CechPic

theorem lem_ab : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := GlobalTheory.T.abelianScheme_glue_artinian_local_fibreProduct

theorem lem_lb : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := GlobalTheory.T.exists_lineBundle_glue_milnorPatching_artinLocal

theorem lem_triv : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := GlobalTheory.T.pic_eq_zero_of_pullbacks_eq_zero_artinFibreProduct

theorem lem_pt : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := GlobalTheory.T.fibreProduct_spec_fieldPoint_factors

theorem lem_princ : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := GlobalTheory.T.siegel_principal_artinian_of_principal_pullback

theorem geom_transfer {S S' : Scheme.{0}} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B} {h M : ℕ}
    (c : SiegPre h M ζ s') (A₀ : Over S) [GrpObj A₀] [IsCommMonObj A₀] (f : S' ⟶ S) (φ : c.A.left ⟶ A₀.left)
    (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A₀)) (hs : s' = f ≫ s)
    (hp : IsGrpPullback c.A A₀ f φ) (hP₀ : P₀.IsLB)
    (diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ))
    (hlev : ∀ a, (c.lev a).left ≫ φ = f ≫ (lev₀ a).left) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (y : Sp k ⟶ S') (hy : y ≫ f = x) (β : B →+* k) (z : kˣ) (hx : x ≫ s = spMap β)
    (hz : (z : k) = β ζ) :
    (∀ a, (toUnit (Over.mk x) ≫ lev₀ a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A₀, g ^ M = 1 → ∃ a, toUnit _ ≫ lev₀ a = g) ∧
    ∀ a b, Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) M (toUnit (Over.mk x) ≫ lev₀ a) (toUnit _ ≫ lev₀ b)
      (unitOn (z ^ (2 * omegaStd a b))) := by
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ f := hp.1.w
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ c.A f φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

theorem spec_isPushout (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (hP : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P) (s₁ : Function.Surjective g₁)
    (s₂ : Function.Surjective g₂) : IsPushout (Spec.map g₁) (Spec.map g₂) (Spec.map f₁) (Spec.map f₂) := by
  have w : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hP.w]
  exact GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hl ha s₁ s₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
    (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂) (show Flat (𝟙 (Spec P)) from inferInstance) (IsPullback.id_vert _)
    (IsPullback.id_vert _) (IsPullback.id_vert _) w (by simp)

theorem nontrivial_of_pt (R : CommRingCat.{0}) (k : Type) [Field k] (y : Spec (CommRingCat.of k) ⟶ Spec R) :
    Nontrivial R := by
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y.base pt⟩

theorem exists_principal_glue : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ β c₁ c₂ hp₁ hp₂ hc₀
  obtain ⟨c₀, ⟨ψ₁, ψ₁₂, hψ₁, sψ₁, iψ₁, lψ₁⟩, ⟨ψ₂, ψ₂₂, hψ₂, sψ₂, iψ₂, lψ₂⟩⟩ := hc₀
  obtain ⟨A, instA, φ₁, φ₂, hA, hφ₁, hφ₂, hcomm⟩ :=
    lem_ab P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ c₁.A c₂.A c₀.A ψ₁ ψ₂ c₁.ab c₂.ab hψ₁ hψ₂
  haveI := hA.comm
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨φ₁₂, sφ₁⟩ := exists_isSquare hφ₁.1.w
  obtain ⟨φ₂₂, sφ₂⟩ := exists_isSquare hφ₂.1.w
  obtain ⟨χ₂, sχ⟩ := exists_isSquare (f := Spec.map g₁ ≫ Spec.map f₁) (φ := ψ₁ ≫ φ₁)
    (by rw [Category.assoc, hφ₁.1.w]; exact (reassoc_of% hψ₁.1.w) _)
  have e₁₂ : ψ₁₂ ≫ φ₁₂ = χ₂ := isSquare_comp rfl sψ₁ sφ₁ sχ
  have e₂₂ : ψ₂₂ ≫ φ₂₂ = χ₂ := isSquare_comp hcomm.symm sψ₂ sφ₂ sχ
  have flat : Flat (G2 A).hom := by
    haveI := hAA.smooth
    infer_instance
  have hiso₀ : LBIso (c₁.P.pull ψ₁₂) (c₂.P.pull ψ₂₂) :=
    LBIso.trans (pull_isLB c₁.isLB _) c₀.isLB (pull_isLB c₂.isLB _) iψ₁.symm iψ₂
  obtain ⟨L, hL, w₁, w₂⟩ := lem_lb P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (G2 A) (G2 c₁.A) (G2 c₂.A)
    (G2 c₀.A) φ₁₂ φ₂₂ ψ₁₂ ψ₂₂ flat (isPullback_of_isSquare hφ₁.1 sφ₁) (isPullback_of_isSquare hφ₂.1 sφ₂)
    (isPullback_of_isSquare hψ₁.1 sψ₁) (e₁₂.trans e₂₂.symm) (isSquare_w hψ₂.1.w sψ₂) c₁.P c₂.P c₁.isLB c₂.isLB
    hiso₀
  have clsP₁ : cls c₁.P c₁.isLB = pull φ₁₂ (cls L hL) := by
    rw [← cls_pull hL φ₁₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₁
  have clsP₂ : cls c₂.P c₂.isLB = pull φ₂₂ (cls L hL) := by
    rw [← cls_pull hL φ₂₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₂
  have rig : ∀ (a₁ : c₁.A ⟶ c₁.A ⊗ c₁.A) (a₂ : c₂.A ⟶ c₂.A ⊗ c₂.A) (a : A ⟶ A ⊗ A),
      a₁.left ≫ φ₁₂ = φ₁ ≫ a.left → a₂.left ≫ φ₂₂ = φ₂ ≫ a.left →
      (∃ t : (c₁.P.pull a₁.left).Gen, t.IsGen) → (∃ t : (c₂.P.pull a₂.left).Gen, t.IsGen) →
      ∃ t : (L.pull a.left).Gen, t.IsGen := by
    intro a₁ a₂ a e₁ e₂ t₁ t₂
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL _ (pull_isLB hL _)]
    refine lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A c₁.A c₂.A φ₁ φ₂ hA hφ₁.1 hφ₂.1 _ ?_ ?_
    · rw [← pull_comp, ← e₁, pull_comp, ← clsP₁, ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _)]
      exact (cls_eq_zero_iff _).2 t₁
    · rw [← pull_comp, ← e₂, pull_comp, ← clsP₂, ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _)]
      exact (cls_eq_zero_iff _).2 t₂
  have one₁ := one_comp hφ₁ c₁.A A φ₁ hφ₁.1.w
  have one₂ := one_comp hφ₂ c₂.A A φ₂ hφ₂.1.w
  have idφ₁ : (𝟙 c₁.A : c₁.A ⟶ c₁.A).left ≫ φ₁ = φ₁ ≫ (𝟙 A : A ⟶ A).left := by simp
  have idφ₂ : (𝟙 c₂.A : c₂.A ⟶ c₂.A).left ≫ φ₂ = φ₂ ≫ (𝟙 A : A ⟶ A).left := by simp
  have symm : LBIso L (L.pull (lift (snd A A) (fst A A)).left) := by
    have sw₁ := lift_square sφ₁ sφ₁.2.symm sφ₁.1.symm
    have sw₂ := lift_square sφ₂ sφ₂.2.symm sφ₂.1.symm
    refine (cls_eq_iff hL (pull_isLB hL _)).1 (sub_eq_zero.1 (lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
      (G2 A) (G2 c₁.A) (G2 c₂.A) φ₁₂ φ₂₂ hAA (isPullback_of_isSquare hφ₁.1 sφ₁)
      (isPullback_of_isSquare hφ₂.1 sφ₂) _ ?_ ?_))
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₁, pull_comp, ← clsP₁,
        ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₁.symm
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₂, pull_comp, ← clsP₂,
        ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₂.symm

  have hpo := spec_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
  have levc : ∀ a, Spec.map g₁ ≫ (c₁.lev a).left ≫ φ₁ = Spec.map g₂ ≫ (c₂.lev a).left ≫ φ₂ := fun a => by
    simp only [← Category.assoc]
    rw [← lψ₁ a, ← lψ₂ a, Category.assoc, Category.assoc, hcomm]
  have sec : ∀ {X : Scheme.{0}} {Bv : Over X} (u : 𝟙_ (Over X) ⟶ Bv), u.left ≫ Bv.hom = 𝟙 X := fun u => by
    simpa using Over.w u
  have hlev : ∀ a, ∃ l : 𝟙_ (Over (Spec P)) ⟶ A, Spec.map f₁ ≫ l.left = (c₁.lev a).left ≫ φ₁ ∧
      Spec.map f₂ ≫ l.left = (c₂.lev a).left ≫ φ₂ := fun a =>
    ⟨Over.homMk (hpo.desc _ _ (levc a)) (by
      refine hpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hpo.inl_desc, Category.assoc, hφ₁.1.w, ← Category.assoc, sec]
        simp
      · rw [← Category.assoc, hpo.inr_desc, Category.assoc, hφ₂.1.w, ← Category.assoc, sec]
        simp), hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  choose lev hl₁ hl₂ using hlev
  obtain ⟨ρ₁, hρ₁⟩ := exists_liftHom hφ₁ (𝟙_ _) (𝟙_ _) (Spec.map f₁)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ρ₂, hρ₂⟩ := exists_liftHom hφ₂ (𝟙_ _) (𝟙_ _) (Spec.map f₂)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρl₁ : ∀ a, ρ₁ (lev a) = c₁.lev a := fun a => (hρ₁ _ _).2 (hl₁ a).symm
  have ρl₂ : ∀ a, ρ₂ (lev a) = c₂.lev a := fun a => (hρ₂ _ _).2 (hl₂ a).symm
  have inj : ∀ x y : 𝟙_ (Over (Spec P)) ⟶ A, ρ₁ x = ρ₁ y → ρ₂ x = ρ₂ y → x = y := fun x y e₁ e₂ =>
    Over.OverMorphism.ext (hpo.hom_ext
      (by rw [← (hρ₁ x _).1 rfl, ← (hρ₁ y _).1 rfl, e₁])
      (by rw [← (hρ₂ x _).1 rfl, ← (hρ₂ y _).1 rfl, e₂]))
  have diag₁ : LBIso (c₁.P.pull (lift (𝟙 c₁.A) (𝟙 c₁.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₁) :=
    lbIso_square c₁.isLB hL w₁ (lift_square sφ₁ idφ₁ idφ₁)
  have diag₂ : LBIso (c₂.P.pull (lift (𝟙 c₂.A) (𝟙 c₂.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₂) :=
    lbIso_square c₂.isLB hL w₂ (lift_square sφ₂ idφ₂ idφ₂)
  let c : SiegPre g n (zetaAway n) (Spec.map β) :=
    { A := A, ab := hA, P := L, isLB := hL
      rig₁ := rig _ _ _ (lift_square sφ₁ one₁ idφ₁) (lift_square sφ₂ one₂ idφ₂) c₁.rig₁ c₂.rig₁
      rig₂ := rig _ _ _ (lift_square sφ₁ idφ₁ one₁) (lift_square sφ₂ idφ₂ one₂) c₁.rig₂ c₂.rig₂
      symm := symm, lev := lev
      lev_add := fun a b => inj _ _ (by rw [map_mul, ρl₁, ρl₁, ρl₁, c₁.lev_add])
        (by rw [map_mul, ρl₂, ρl₂, ρl₂, c₂.lev_add])
      lev_tors := fun a => inj _ _ (by rw [map_pow, ρl₁, c₁.lev_tors, map_one])
        (by rw [map_pow, ρl₂, c₂.lev_tors, map_one])
      geom := by
        intro k _ _ x β' z hx hz
        rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ k x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact geom_transfer c₁ A (Spec.map f₁) φ₁ L lev rfl hφ₁ hL diag₁ (fun a => (hl₁ a).symm) k x y hy β' z hx hz
        · exact geom_transfer c₂ A (Spec.map f₂) φ₂ L lev rfl hφ₂ hL diag₂ (fun a => (hl₂ a).symm) k x y hy β' z hx hz }
  have pb₁ : SiegPB c₁ c (Spec.map f₁) := ⟨φ₁, φ₁₂, hφ₁, sφ₁, w₁, fun a => (hl₁ a).symm⟩
  have pb₂ : SiegPB c₂ c (Spec.map f₂) := ⟨φ₂, φ₂₂, hφ₂, sφ₂, w₂, fun a => (hl₂ a).symm⟩
  refine ⟨c, ?_, pb₁, pb₂⟩
  rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ (IsLocalRing.ResidueField P)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue P))) with ⟨y, -⟩ | ⟨y, -⟩
  · haveI := nontrivial_of_pt R₁ _ y
    exact lem_princ g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ inferInstance β c c₁ pb₁ hp₁
  · haveI := nontrivial_of_pt R₂ _ y
    exact lem_princ g n hn hodd P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hs₂ hs₁ inferInstance β c c₂ pb₂ hp₂

end GlobalTheory.ArtinGlue
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DeRhamExt

def canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) :=
  Classical.choose (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA)

theorem isCan_iff_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A)
    (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : IsCan t c x ↔ canMap p hA t c = x :=
  Classical.choose_spec (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA) c x

theorem isCan_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A) :
    IsCan t c (canMap p hA t c) :=
  (isCan_iff_canMap p hA t c _).2 rfl

theorem canMap_bijective (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] {R : Type}
    [CommRing R] (hR : IsNilpotent (p : R)) {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : Function.Bijective (canMap p hA t) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
  exact GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hP p R hR A g hA hg G t _ (isCan_canMap p hA t)

def canFamily (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] :
    GlobalTheory.Published.DeRhamVectorExtension.Family p :=
  fun _ _ hR _ _ hA _ t => LinearEquiv.ofBijective (canMap p hA t) (canMap_bijective hP p hR hA t)

theorem exists_canonical_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime],
    ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧
      ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
        (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A),
        IsCan t c (e hR hA t c) := by
  intro hP p _
  refine ⟨canFamily hP p, ?_, ?_, ?_, ?_⟩
  · intro R R' _ _ hR hR' A _ A' _ hA hA' G G' t t' σ φ m c
    exact ((isCan_iff_canMap p hA' t' _ _).1
      (GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality p R R' A A' G G' t t' σ φ m c _ (isCan_canMap p hA t c)))
  · intro R _ hR A _ hA G t
    obtain ⟨N, hN⟩ := hR
    exact GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms p R N hN A hA G t (canMap p hA t)
      (canMap_bijective hP p ⟨N, hN⟩ hA t).2 (isCan_canMap p hA t)
  · intro R _ hR A _ hA G t h v
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
    exact GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension hP p R hR A g hA hg G t (canFamily hP p hR hA t)
      (isCan_canMap p hA t) h v
  · intro R _ hR A _ hA G t c
    exact isCan_canMap p hA t c

end GlobalTheory.DeRhamExt
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareKer

theorem mem_fil_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ y : HdR B, (∀ x ∈ Fil A, φ x y = 0) → y ∈ Fil B := by
  intro hH R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ y hy
  have hL := hP.isLB

  obtain ⟨v, hv, -⟩ := ((GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange hH).2.1 R B g hB hgB).1.1 y

  have horth := GlobalTheory.T.hodgeFiltrations_orthogonal_lineBundlePairing_product hH R A B g hA hB hgA hgB P hL φ hφ
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_isChartChoiceForPoints_of_nontrivial R A B P hL

  have hpairZero (h : HdR A) (hh : h ∈ Fil A) : φ h y = h (0 : primDR A) :=
    (hy h hh).trans h.map_zero.symm
  have hc : Cohom (chartsA P) (fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))) (tanCoc P j v).neg :=
    GlobalTheory.T.cohomologous_neg_torsor_cocycle_of_orthogonal hH R A B g hA hB hgA hgB P hL φ hφ horth y v hv 0
      hpairZero 0 (by rw [LinearMap.map_zero]; rfl) j hj
  obtain ⟨k, hk⟩ := hc
  have hk' : IsCob (chartsA P) (tanCoc P j v) k := by
    intro D _ _ D' _ _ ψ x hx
    have e := hk D D' ψ x hx
    have h0 : fv (0 : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) D D' ψ x = 0 := rfl
    simp only [Fn1.add, Fn1.neg, h0, zero_add, neg_neg] at e
    exact e

  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_pointwiseLineBundleGenerator_of_trivial_pullback R (A ⊗ B) A P hL (AbDual.inl A B) hP.zero_right

  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary R A B P hL v hv.1 j hj s hs k hk'
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_pointwiseGenerator_of_dualNumberLineBundleGenerator R A B P hL v hv.1 T hT
  have htriv := GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator R (A ⊗ B) (A ⊗ epsR R) P hL _ t ht

  have hv1 : v = 1 := hP.ker_right (epsR R) v htriv
  subst hv1
  exact isLieImage_one_iff.mp hv

end GlobalTheory.PoincareKer
end
