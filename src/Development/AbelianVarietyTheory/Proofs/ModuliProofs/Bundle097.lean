module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenTranslEqPairing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle090
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelDirect

open GlobalTheory.SiegelPullComp

private theorem tensor_left_hom_ext' {T : Scheme.{0}} {G : Over T} {X : Scheme.{0}} (a b : X ⟶ (G ⊗ G).left)
    (h1 : a ≫ (fst G G).left = b ≫ (fst G G).left) (h2 : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b := by
  have hw : b ≫ (G ⊗ G).hom = a ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), reassoc_of% h1]
  have key := CartesianMonoidalCategory.hom_ext
    (Over.homMk a rfl : Over.mk (a ≫ (G ⊗ G).hom) ⟶ G ⊗ G) (Over.homMk b hw)
    (by ext; simpa using h1) (by ext; simpa using h2)
  simpa using congrArg (fun k => k.left) key

theorem exists_inverse {T : Scheme.{0}} {A G : Over T} [GrpObj A] [GrpObj G] {φ : A.left ⟶ G.left}
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hφ : IsGrpPullback A G (𝟙 T) φ) (hs : Geo.Tor.IsSquare φ φ₂) :
    ∃ (F : G.left ⟶ A.left) (F₂ : (G2 G).left ⟶ (G2 A).left), IsGrpPullback G A (𝟙 T) F ∧ Geo.Tor.IsSquare F F₂ ∧
      φ ≫ F = 𝟙 _ ∧ F₂ ≫ φ₂ = 𝟙 _ := by
  have hw : φ ≫ G.hom = A.hom := by simpa using hφ.1.w
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  let e : A ≅ G := Over.isoMk (asIso φ) hw
  have heL : e.inv.left = inv φ := rfl
  have hsF : Geo.Tor.IsSquare (inv φ) (e.inv ⊗ₘ e.inv).left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst, Over.comp_left, heL]
    · rw [← Over.comp_left, tensorHom_snd, Over.comp_left, heL]
  refine ⟨inv φ, (e.inv ⊗ₘ e.inv).left, ⟨?_, ?_⟩, hsF, by simp, ?_⟩
  · refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← hw]
    simp
  · intro U x y x₀ y₀ hx hy
    have key := hφ.2 (Over.mk (U.hom ≫ 𝟙 T)) x₀ y₀ (Over.homMk x.left (by simp))
      (Over.homMk y.left (by simp)) (by simp [hx]) (by simp [hy])
    have hxy := mul_left_congr (a := (U.hom ≫ 𝟙 T) ≫ 𝟙 T) (b := U.hom) (by simp)
      (Over.homMk x.left (by simp)) (Over.homMk y.left (by simp)) x y (by simp) (by simp)
    rw [hxy.symm.trans key]
    simp
  · apply tensor_left_hom_ext'
    · rw [Category.assoc, hs.1, ← Category.assoc, hsF.1]
      simp
    · rw [Category.assoc, hs.2, ← Category.assoc, hsF.2]
      simp

theorem direct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (O : Type) [CommRing O] (T : Scheme.{0}) (sT : T ⟶ Sp O) (t : SAB H T) (lev : D.La → (𝟙_ (Over T) ⟶ t.G)) (g p N : ℕ) (Ag : SiegelFamily g p N) (z : ZP p N →+* O) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (w : T ⟶ pullback Ag.s (spMap z)), SiegData sT t lev Ag z bas w → ∃ (θ : t.G.left ⟶ Ag.univ.A.left) (θ₂ : (G2 t.G).left ⟶ (G2 Ag.univ.A).left), IsGrpPullback t.G Ag.univ.A (w ≫ pullback.fst _ _) θ ∧ IsSquare θ θ₂ ∧ LBIso (abelian₂ t.G t.PP.L) (Ag.univ.P.pull θ₂) ∧ ∀ u, (lev (bas u)).left ≫ θ = (w ≫ pullback.fst _ _) ≫ (Ag.univ.lev u).left := by
  intro E _ _ _ H D O _ T sT t lev g p N Ag z bas w hd
  obtain ⟨o, φ, φ₂, hφ, hs, hL, hlev, hcl, ψ, ψ₂, hψ, hs', hP, hlev'⟩ := hd
  obtain ⟨F, F₂, hF, hsF, hφF, hF₂⟩ := exists_inverse hφ hs
  have h0 : t.PP.L.IsLB := t.PP.isLB
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := by
    unfold abelian₂
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ h0 _ _
  refine ⟨F ≫ ψ, F₂ ≫ ψ₂, (hF.comp hψ).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hs'.1, ← Category.assoc, hsF.1, Category.assoc]
  · rw [Category.assoc, hs'.2, ← Category.assoc, hsF.2, Category.assoc]
  · have hΛ₁ := pull_isLB hΛ (𝟙 (G2 t.G).left)
    have hΛ₂ := pull_isLB (pull_isLB hΛ φ₂) F₂
    have hO := pull_isLB o.isLB F₂
    have hU₁ := pull_isLB (pull_isLB Ag.univ.isLB ψ₂) F₂
    have hU₂ := pull_isLB Ag.univ.isLB (F₂ ≫ ψ₂)
    have s1 : LBIso (abelian₂ t.G t.PP.L) ((abelian₂ t.G t.PP.L).pull (𝟙 _)) := iso_pull_id hΛ
    have s2 : LBIso ((abelian₂ t.G t.PP.L).pull (𝟙 _)) (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) := by
      have k := iso_pull_pull hΛ φ₂ F₂
      rw [hF₂] at k
      exact k.symm
    have s3 : LBIso (((abelian₂ t.G t.PP.L).pull φ₂).pull F₂) (o.P.pull F₂) := (iso_pull F₂ hL).symm
    have s4 : LBIso (o.P.pull F₂) ((Ag.univ.P.pull ψ₂).pull F₂) := iso_pull F₂ hP
    have s5 : LBIso ((Ag.univ.P.pull ψ₂).pull F₂) (Ag.univ.P.pull (F₂ ≫ ψ₂)) := iso_pull_pull Ag.univ.isLB ψ₂ F₂
    exact LBIso.trans hΛ hΛ₁ hU₂ s1 (LBIso.trans hΛ₁ hΛ₂ hU₂ s2
      (LBIso.trans hΛ₂ hO hU₂ s3 (LBIso.trans hO hU₁ hU₂ s4 s5)))
  · intro u
    rw [← hlev u]
    simp only [Category.assoc, reassoc_of% hφF]
    exact hlev' u

end GlobalTheory.SiegelDirect

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.ThetaToObj

section Comb
variable {Q L : Type} [AddCommGroup L] {n : ℕ}

theorem add_zero' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have := hf 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem add_nsmul' [Group Q] {f : L → Q} (hf : ∀ x y, f (x + y) = f x * f y) (m : ℕ) (x : L) :
    f (m • x) = f x ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, add_zero' hf]
  | succ m ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem ext_basis [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) {f f' : L → Q} (hf : ∀ x y, f (x + y) = f x * f y)
    (hf' : ∀ x y, f' (x + y) = f' x * f' y) (h : ∀ i, f (bas (Pi.single i 1)) = f' (bas (Pi.single i 1))) (x : L) :
    f x = f' x := by
  let F : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) fun x y => by rw [hf]; rfl
  let F' : L →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (f' x)) fun x y => by rw [hf']; rfl
  have : F.toIntLinearMap ∘ₗ bas.toLinearMap = F'.toIntLinearMap ∘ₗ bas.toLinearMap := by
    refine (Pi.basisFun ℤ (Fin n)).ext fun i => ?_
    rw [Pi.basisFun_apply]
    exact congrArg Additive.ofMul (h i)
  have e := LinearMap.congr_fun this (bas.symm x)
  simpa [F, F'] using e

theorem exists_comb [CommGroup Q] (bas : (Fin n → ℤ) ≃ₗ[ℤ] L) (p : Fin n → Q) (k : ℕ) (hp : ∀ i, p i ^ k = 1) :
    ∃ f : L → Q, (∀ x y, f (x + y) = f x * f y) ∧ (∀ x, f (k • x) = 1) ∧ ∀ i, f (bas (Pi.single i 1)) = p i := by
  have hf : ∀ x y : L, ∏ i, p i ^ bas.symm (x + y) i = (∏ i, p i ^ bas.symm x i) * ∏ i, p i ^ bas.symm y i := by
    intro x y
    simp only [map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  refine ⟨fun x => ∏ i, p i ^ bas.symm x i, hf, fun x => ?_, fun i => ?_⟩
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, hp, one_zpow]
  · beta_reduce
    rw [LinearEquiv.symm_apply_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp

end Comb

theorem smul_mem_of_mul {O L : Type} [CommRing O] [AddCommGroup L] [Module O L] {I J : Ideal O} {M : ℕ}
    (h : I * J = Ideal.span {(M : O)}) {u : O} (hu : u ∈ I) {x : L} (hx : x ∈ J • (⊤ : Submodule O L)) :
    ∃ y : L, u • x = M • y := by
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule O L) := by
    rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu hx
  rw [h, Submodule.ideal_span_singleton_smul] at h1
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
  exact ⟨y, by rw [← hy, Nat.cast_smul_eq_nsmul]⟩

theorem isGrpPullback_of_iso {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (φ : G' ≅ G) [IsMonHom φ.hom] :
    IsGrpPullback G' G (𝟙 S) φ.hom.left := by
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget S).map φ.hom))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ φ.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ φ.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

theorem exists_obj_under : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (o : Type) [CommRing o] [Algebra o (KA l)] (b : TBase o l.A) (ρ : o) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (t : TObj g l.A J b (s ≫ spMap (algebraMap o (KA l)))) (τ : SAB H S), l.M ∣ l.A → IsSympBasis D bas → IsFractionRing o (KA l) → algebraMap o (KA l) ρ = (baseKA l).ρ → algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ → (IsReduced S ∨ IsLocallyNoetherian S) → IsPEL D a bas ρ t τ → ∃ ob : Obj D l (baseKA l) s, ObjUnder ob a bas t := by
  intro _ _ E _ _ _ H D g J a bas l o _ _ b ρ S s t τ hMA _ _ hρ hζ _ hP
  obtain ⟨φ, hmon, hL, hact, hgeo⟩ := hP
  obtain ⟨r, hr⟩ := hMA
  have hrpos : 0 < r := Nat.pos_of_ne_zero fun h => by
    have := l.A_pos
    rw [hr, h] at this
    simp at this
  have hMpos : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨hab, hamp, hk⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S t.A τ.G (𝟙 S)
    φ.hom.left t.L τ.PP.L t.isLB τ.PP.isLB t.ab (isGrpPullback_of_iso φ) hL
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (by simp)
  obtain ⟨f, fadd, fker, fbas⟩ := exists_comb (Q := 𝟙_ (Over S) ⟶ τ.G) bas (fun i => j ≫ t.pt i ≫ φ.inv) l.A
    fun i => by
      rw [← MonObj.comp_pow, ← MonObj.pow_comp, t.torsion, MonObj.one_comp, MonObj.comp_one]
  obtain ⟨e', he', e, he, hee⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ _ from l.coprime ▸ Submodule.mem_top)
  refine ⟨⟨τ, hab.proper, hamp t.ample, hk t.ktriv, fun x => f (r • e • x), fun x y => ?_, fun x hx => ?_, f, fadd, fker,
    fun K _ _ x β hβ => ?_⟩, φ, hmon, hL, hact, fun i => ?_⟩
  · rw [smul_add, smul_add, fadd]
  · obtain ⟨y, hy⟩ := smul_mem_of_mul ((mul_comm _ _).trans l.prod) he hx
    rw [hy, smul_smul, mul_comm, ← hr, fker]
  · have : CharZero K := RingHom.charZero_iff β.injective |>.1 inferInstance
    obtain ⟨hd, I, hI, hev⟩ := hgeo K x (β.comp (algebraMap o (KA l))) (by
      rw [← Category.assoc, hβ, ← Spec.map_comp]; rfl)
    have hA : ∀ y, toUnit (Over.mk x) ≫ f y = I.ev l.A y := by
      refine ext_basis (Q := Over.mk x ⟶ τ.G) bas (fun y z => ?_) (I.add _) fun i => ?_
      · rw [fadd, MonObj.comp_mul]
      · rw [fbas, ← cancel_mono φ.hom, hev]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [← Category.assoc]
        congr 1
    refine ⟨by rw [← hρ]; exact hd, I, by rw [← hζ]; exact hI, hA, fun y hy => ?_⟩
    obtain ⟨z, hz⟩ := smul_mem_of_mul l.prod he' hy
    have h1 : y = e • y + l.M • z := by rw [← hz, ← add_smul, add_comm, hee, one_smul]
    rw [hA, add_nsmul' (I.add _), hr, I.tower _ _ hMpos hrpos]
    conv_rhs => rw [h1, I.add, (I.ker _ hMpos _).2 ⟨z, rfl⟩, _root_.mul_one]
  · show (f _ ≫ φ.hom).left = _
    rw [fbas]
    simp [j]

end GlobalTheory.ThetaToObj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem exists_forms_forall_mem_basicOpen {Γ : Type} [Finite Γ] {R : Type} [CommRing R] {N : ℕ}
    {X : Scheme.{0}} [CompactSpace X] (φ : Γ → (X ⟶ PSpace R N)) :
    ∃ (d n : ℕ) (F : Fin n → MvPolynomial (Fin (N + 1)) R), 0 < d ∧ (∀ i, (F i).IsHomogeneous d) ∧
      ∀ x : X, ∃ i, ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (F i) := by
  classical

  have orbit : ∀ x : X, ∃ e : ℕ, 0 < e ∧ ∃ f ∈ ProjSpace.grading R N e,
      Set.range (fun g => φ g x) ⊆ Proj.basicOpen (ProjSpace.grading R N) f := fun x =>
    FiniteSubsetsInAffineOpens.exists_proj_basicOpen (ProjSpace.grading R N) (Set.finite_range _)
  choose e he f hf hsub using orbit

  let U : X → Set X := fun x => {z | ∀ g, φ g z ∈ Proj.basicOpen (ProjSpace.grading R N) (f x)}
  have hU : ∀ x, U x ∈ nhds x := fun x => by
    refine IsOpen.mem_nhds ?_ fun g => hsub x ⟨g, rfl⟩
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun g =>
      (φ g).continuous.isOpen_preimage _ (Proj.basicOpen (ProjSpace.grading R N) (f x)).isOpen

  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  have hD : 0 < ∏ x ∈ t, e x := Finset.prod_pos fun x _ => he x
  have hdvd : ∀ x ∈ t, e x ∣ ∏ y ∈ t, e y := fun x hx => Finset.dvd_prod_of_mem e hx
  refine ⟨∏ x ∈ t, e x, t.card,
    fun i => f (t.equivFin.symm i) ^ ((∏ x ∈ t, e x) / e (t.equivFin.symm i)), hD, fun i => ?_, fun x => ?_⟩
  · have h1 : (f (t.equivFin.symm i)).IsHomogeneous (e (t.equivFin.symm i)) := hf _
    have h2 := h1.pow ((∏ x ∈ t, e x) / e (t.equivFin.symm i))
    rwa [Nat.mul_div_cancel' (hdvd _ (t.equivFin.symm i).2)] at h2
  · have hx : x ∈ ⋃ y ∈ t, U y := by rw [ht]; exact Set.mem_univ x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 hx
    have hxy' : ∀ g, φ g x ∈ Proj.basicOpen (ProjSpace.grading R N) (f y) := hxy
    refine ⟨t.equivFin ⟨y, hy⟩, fun g => ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [Proj.basicOpen_pow]
    · exact hxy' g
    · exact Nat.div_pos (Nat.le_of_dvd hD (hdvd y hy)) (he y)

theorem exists_sections_orbit_subset_nonzeroLocus : ∀ (Γ : Type) [Group Γ] [Finite Γ] (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ρ : Γ →* Aut X), IsProjOver s → ∃ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ∀ x : X, ∃ i, ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
  intro Γ _ _ R _ X s ρ hs
  obtain ⟨N, j, hj, -⟩ := hs

  haveI : CompactSpace (PSpace R N) := by
    refine ⟨?_⟩
    have hcov : (Set.univ : Set (PSpace R N)) = ⋃ i, (ProjSpace.chart R N i : Set (PSpace R N)) := by
      ext y
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact ProjSpace.exists_mem_chart R N y
    rw [hcov]
    exact isCompact_iUnion fun i => (ProjSpace.isAffineOpen_chart R N i).isCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j

  obtain ⟨d, n, F, hd, hF, hcov⟩ := exists_forms_forall_mem_basicOpen (fun g => (ρ g).asIso.hom ≫ j)
  refine ⟨(lbPow (ProjSpace.O1 R N) d).pull j, n, fun i => secPull (ProjSpace.formSec d (F i) (hF i)) j,
    pull_isLB (isLB_lbPow (ProjSpace.O1_isLB R N) d) j, fun i => ?_, fun x => ?_⟩
  · rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact (Proj.isAffineOpen_basicOpen (ProjSpace.grading R N) (F i) (hF i) hd).preimage j
  · obtain ⟨i, hi⟩ := hcov x
    refine ⟨i, fun g => ?_⟩
    rw [nonzeroLocus_secPull, ProjSpace.nonzeroLocus_formSec]
    exact hi g

end GlobalTheory
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PairingDetermines

open Out CommutatorPairing DescentPairing PrimCocycle IsoDescent

section OnePoint

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A}

theorem exists_gen_transl (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (cb : CubicalStr A L) {T : Over S} (p₀ : T.left)
    (hT : ∀ p : T.left, p = p₀) (n : ℕ) (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(mulT A T n ≫ translPt A x).left, (snd T A ^ n).left] ![1, -1]),
      u.IsGen ∧ ∀ (y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), y ^ n = 1 → WeilIs A L.L n x y c →
        ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A) (z : Z.left) (J), Good L.L z J →
          val u (lift t ((t ≫ y) * a)).left z J = val u (lift t a).left z J * gm t.left z ⊤ c := by
  obtain ⟨θx, rfl, -⟩ := exists_theta cb p₀ hT n x hx
  obtain ⟨u, hu, vu⟩ := exists_triv cb p₀ hT n θx
  refine ⟨u, hu, fun y c hy hc Z t a z J hJ => ?_⟩
  obtain ⟨θy, rfl, vy⟩ := exists_theta cb p₀ hT n y hy
  have hcm := (commIsOf_iff L.isLB θx θy c).1 ((GlobalLift.weilIs_iff_commIsOf hG hA L.isLB θx θy c).1 hc)
  obtain ⟨s, hs⟩ := vu _ t z J hJ
  obtain ⟨s', hs'⟩ := vy _ t z J hJ
  have k₁ := hcm _ t a z J hJ
  have k₂ := cubN_transl (isCub_cubV cb hJ) n (t ≫ θy.pt) a (t ≫ θx.pt)
    ((map_pow (preHom t) θy.pt n).symm.trans (by rw [hy]; exact map_one _))
  refine (hs _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (hs _) k₁.symm).symm)
  have t₁ := hs' a
  have t₂ := hs' ((t ≫ θx.pt) * a)
  apply Additive.ofMul.injective
  have E := fun {p q : (Z.left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E t₁; have a₂ := E t₂; have a₃ := E k₂
  simp only [commVal, ofMul_mul, ofMul_inv] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₃ + a₁ - a₂

end OnePoint

section Field

variable {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] [IsCommMonObj A]

theorem exists_gen_lam (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (α : A ⟶ P.A) [IsMonHom α] (d n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ A) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L
        (fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (fun I => lamε I * d)),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ A) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ α) (y ≫ α) c → ∀ (z : A.left) (J), Good P.L z J →
          val u ((toUnit A ≫ y) * 𝟙 A).left z J = val u (𝟙 _) z J * gm (toUnit A).left z ⊤ (c ^ d) := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hpow : ∀ y : T ⟶ A, y ^ n = 1 → (y ≫ α) ^ n = 1 := fun y hy => by
    rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ α) (hpow x hx)
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ α).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u₁, hu₁, v₁⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA A n).left ≫ (lift (toUnit A ≫ x) (𝟙 A)).left ≫ lamφ A I ≫ α.left) (ε' := lamε)
    (fun U _ h => by
      have e₀ : mulA A n ≫ lift (toUnit A ≫ x) (𝟙 A) = lift (toUnit A ≫ x) (𝟙 A ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit A) α ≫ mulT P.A T n ≫ translPt P.A (x ≫ α) = ((toUnit A ≫ x) * 𝟙 A ^ n) ≫ α := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd, MonObj.mul_comp,
          MonObj.pow_comp, Category.id_comp, Category.assoc]
      have e₂ : lift (toUnit A) α ≫ snd T P.A ^ n = (𝟙 A ^ n) ≫ α := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit A ≫ (1 : T ⟶ P.A) = (1 : A ⟶ A) ≫ α := by rw [MonObj.comp_one, MonObj.one_comp]
      have e := prod_lam (toUnit A ≫ x) (𝟙 A ^ n) (fun q => h (q ≫ α.left))
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit A) α).left) (LB.pullGen P.L _ _ σ (toUnit A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  obtain ⟨u, hu, v⟩ := WeilIsogeny.exists_gen_pow (ε' := fun I => lamε I * d) d (fun _ => rfl) u₁ hu₁
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have w : ∀ a : A ⟶ A, val u a.left z J =
      (val u₀ (lift (toUnit A) (a ≫ α)).left z J * val σ (toUnit A).left z J) ^ d := fun a => by
    rw [v, v₁ _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ α) c (hpow y hy) hc A (toUnit A) (𝟙 A ≫ α) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 A))).symm)
  rw [MonObj.mul_comp, Category.assoc, map_pow, ← mul_pow, mul_right_comm]
  exact congrArg (fun q => (q * _) ^ d) w₀

theorem exists_gen_axis {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : A.left ⟶ X) (e : ℤ) :
    ∃ u : LB.Gen (LB.LinComb L (fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (fun I => lamε I * e)),
      u.IsGen := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ := PEmpty.elim) (ε := PEmpty.elim)
    (φ' := fun I => (lift (𝟙 A) (1 : A ⟶ A)).left ≫ lamφ A I ≫ F) (ε' := fun I => lamε I * e) (fun U _ h => by
      have q := prod_lam (𝟙 A) (1 : A ⟶ A) (fun q => h (q ≫ F) ^ e)
      rw [_root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel] at q
      refine (Fintype.prod_empty _).trans (q.symm.trans (Finset.prod_congr rfl fun I _ => ?_))
      rw [← zpow_mul, mul_comm e, Category.assoc]) (LB.oneGen L)
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  exact ⟨u, hu⟩

end Field

end GlobalTheory.PairingDetermines

namespace GlobalTheory

open PairingDetermines IsoDescent PrimCocycle

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_glue_rigidified_lineBundles_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (M : ∀ i, LB (G i).left) (B : I → I → Scheme.{0}) (a : ∀ i j, B i j ⟶ (G i).left) (b : ∀ i j, B i j ⟶ (G j).left), (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i, (M i).IsLB) → (∀ i, Out.Rigidified (G i) (M i)) → (∀ i j, LBIso ((M i).pull (a i j)) ((M j).pull (b i j))) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ ∀ i, LBIso (M i) (L.pull (ψ i)) := by
  first | exact @GlobalTheory.RigidBundleGlue.exists_glue | exact GlobalTheory.RigidBundleGlue.exists_glue | (intros; apply GlobalTheory.RigidBundleGlue.exists_glue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.symmetric_local_on_base_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → (∀ i, Out.Sym (G i) (M i)) → Out.Sym A L := by
  first | exact @GlobalTheory.CoverGlue.sym_of_cover | exact GlobalTheory.CoverGlue.sym_of_cover | (intros; apply GlobalTheory.CoverGlue.sym_of_cover <;> assumption)
end
