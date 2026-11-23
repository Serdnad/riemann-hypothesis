module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle191
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle237
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle003
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle236
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem exists_model (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    ∃ (Ep : Type) (_ : AddCommGroup Ep) (_ : Module (regAt ξ p) Ep) (Mp : LieModel G (regPt h p) Ep)
      (j : Ep →ₗ[regAt ξ p] E), IsBaseChange Ω j ∧
        ∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := GlobalTheory.T.lie_model_descends_base_change X G (regAt ξ p) Ω (regPt h p) E
    (castPt (spMap_algebraMap_regPt h p).symm M)
  exact ⟨Ep, i1, i2, Mp, j, hb, fun e =>
    (castPt_pt_left (spMap_algebraMap_regPt h p).symm M (j e)).symm.trans (hj e)⟩

theorem lat_fin (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    Module.Finite (regAt ξ p) (M.lat p) ∧ Module.Projective (regAt ξ p) (M.lat p) ∧
      Submodule.span Ω (M.lat p : Set E) = ⊤ := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := exists_model h G M p
  have hr := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M p Ep Mp j hj
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G (regAt ξ p) (regPt h p) Ep Mp
  haveI := GlobalTheory.T.regular_local_ring_fraction_field X Ω ξ h p
  have hl : IsLocalizedModule (nonZeroDivisors (regAt ξ p)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (regAt ξ p)) Ω j).mpr hb
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (regAt ξ p)) j).1 hm
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Ep) c.2
    exact hreg (show (c : regAt ξ p) • m = (c : regAt ξ p) • 0 by rw [smul_zero]; exact hc)
  have hMeq : M.lat p = LinearMap.range j := SetLike.coe_injective (hr.trans (LinearMap.coe_range j).symm)
  let e : Ep ≃ₗ[regAt ξ p] M.lat p := (LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hMeq.symm)
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, ?_⟩
  rw [eq_top_iff]
  intro v _
  refine hb.inductionOn v (motive := fun v => v ∈ Submodule.span Ω (M.lat p : Set E)) (fun m => ?_)
    (fun s n hn => Submodule.smul_mem _ s hn) (fun a b ha hb => add_mem ha hb)
  exact Submodule.subset_span (by rw [hr]; exact ⟨m, rfl⟩)

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  apply RingHom.ext
  intro a
  ext <;> simp [dualMap]

theorem lat_gen (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    M.lat q = Submodule.span (regAt ξ q) (M.lat p : Set E) := by
  obtain ⟨Eq, i1, i2, Mq, jq, hbq, hjq⟩ := exists_model h G M q
  letI : Algebra (regAt ξ p) (regAt ξ q) := (regIncl hs).toAlgebra
  letI : Module (regAt ξ p) Eq := Module.compHom Eq (regIncl hs)
  haveI : IsScalarTower (regAt ξ p) (regAt ξ q) Eq := ⟨fun a b c => by
    change (regIncl hs a * b) • c = regIncl hs a • (b • c)
    rw [mul_smul]⟩
  obtain ⟨Ep, i3, i4, Mp, j, hb, hj⟩ := GlobalTheory.T.lie_model_descends_base_change X G (regAt ξ p) (regAt ξ q) (regPt h p) Eq
    (castPt (spMap_regIncl_regPt h hs).symm Mq)
  let jp : Ep →ₗ[regAt ξ p] E :=
    { toFun := fun e => jq (j e)
      map_add' := fun a b => by simp
      map_smul' := fun c e => by
        rw [map_smul]
        change jq (regIncl hs c • j e) = _
        rw [map_smul]
        rfl }
  have hjp : ∀ e, (M.pt (jp e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
    intro e
    have h1 := hjq (j e)
    have h2 := (castPt_pt_left (spMap_regIncl_regPt h hs).symm Mq (j e)).symm.trans (hj e)
    have h3 : (dualMap (algebraMap (regAt ξ q) Ω)).comp (dualMap (algebraMap (regAt ξ p) (regAt ξ q))) =
        dualMap (algebraMap (regAt ξ p) Ω) := dualMap_comp _ _
    refine h1.trans ?_
    rw [h2, ← h3]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hrp := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M p Ep Mp jp hjp
  have hrq := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M q Eq Mq jq hjq
  have hMq : M.lat q = LinearMap.range jq := SetLike.coe_injective (hrq.trans (LinearMap.coe_range jq).symm)
  rw [hrp, hMq]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    refine hb.inductionOn w (motive := fun w => jq w ∈ Submodule.span (regAt ξ q) (Set.range jp)) (fun m => ?_)
      (fun s n hn => by rw [map_smul]; exact Submodule.smul_mem _ s hn)
      (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    exact Submodule.subset_span ⟨m, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    exact ⟨j e, rfl⟩

theorem mem_localizedIn_iff (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1)
    (P : PrimeSpectrum (regAt ξ p)) (hu : ∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q)
    (hd : ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p) (v : E) :
    v ∈ GroundTheory.Heights₂.Heights.Model.localizedIn P.asIdeal (M.lat p) ↔ v ∈ M.lat q := by
  have hg := lat_gen h G M hs
  constructor
  · rintro ⟨s, hsP, hv⟩
    have h0 : (s : Ω) ≠ 0 := fun h0 => hsP (by
      have : s = 0 := Subtype.ext h0
      rw [this]; exact zero_mem _)
    have h1 : (s : Ω) • v ∈ M.lat q := by rw [hg]; exact Submodule.subset_span hv
    have h2 := (M.lat q).smul_mem (⟨_, hu s hsP⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu s hsP⟩ : regAt ξ q) • (s : Ω) • v = v := by
      rw [Subring.smul_def, smul_smul]
      simp [h0]
    rwa [h3] at h2
  · intro hv
    rw [hg] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hw⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a w _ hw =>
      obtain ⟨s, hsP, hsw⟩ := hw
      obtain ⟨t, htP, hta⟩ := hd a a.2
      refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim htP hsP, ?_⟩
      have e : (t * s) • a • w = (⟨_, hta⟩ : regAt ξ p) • s • w := by
        simp only [Subring.smul_def, smul_smul, Subring.coe_mul]
        congr 1
        ring
      rw [e]
      exact (M.lat p).smul_mem _ hsw

theorem lat_eq_of_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (M' : LieModel G' ξ E), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → M.lat = M'.lat := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hS hS' hP hP' E _ _ M M' hv hN hnorm
  funext p
  haveI := hS.comm
  haveI := hS.smooth
  haveI := hS'.comm
  haveI := hS'.smooth
  haveI := GlobalTheory.T.regular_local_ring_fraction_field X Ω ξ hξ p
  obtain ⟨hdom, hic⟩ := hnorm p.1
  haveI : IsDomain (regAt ξ p) := inferInstance
  haveI : IsNoetherianRing (X.presheaf.stalk p.1) := inferInstance
  haveI : IsNoetherianRing (regAt ξ p) := isNoetherianRing_of_ringEquiv _ (regIso hξ p)
  haveI : IsIntegrallyClosed (regAt ξ p) := IsIntegrallyClosed.of_equiv (regIso hξ p)
  haveI : FiniteDimensional Ω E := (GlobalTheory.T.lie_model_finite_projective X G Ω ξ E M).1
  obtain ⟨f1, p1, s1⟩ := lat_fin hξ G M p
  obtain ⟨f2, p2, s2⟩ := lat_fin hξ G' M' p
  refine GroundTheory.Heights₂.Heights.Model.LatticesAgree.proof GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof (regAt ξ p) Ω E (M.lat p) (M'.lat p) f1 p1 f2 p2 s1 s2 ?_
  intro P hP1
  obtain ⟨q, hs, hdvr, hu, hd⟩ := GlobalTheory.T.height_one_prime_dvr_stalk X Ω ξ hξ hN hnorm p P hP1
  have hq := GlobalTheory.T.semiabelian_lie_lattice_eq X Ω ξ hξ G G' GΩ φ φ' hS hS' hP hP' E M M' hv q hdvr
  ext v
  rw [mem_localizedIn_iff hξ G M hs P hu hd, mem_localizedIn_iff hξ G' M' hs P hu hd, hq]

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext

section General
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def pre {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) : (Y ⟶ A) →* (Y' ⟶ A) where
  toFun x := ρ ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

def post {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] : (Y ⟶ A) →* (Y ⟶ A') where
  toFun x := x ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' _ _ := MonObj.mul_comp _ _ _

theorem pre_pow {Y Y' A : C} [MonObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) (n : ℕ) : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n :=
  map_pow (pre ρ) x n

theorem post_pow {Y A A' : C} [MonObj A] [MonObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n :=
  map_pow (post φ) x n

theorem post_inv {Y A A' : C} [GrpObj A] [GrpObj A'] (φ : A ⟶ A') [IsMonHom φ] (x : Y ⟶ A) :
    x⁻¹ ≫ φ = (x ≫ φ)⁻¹ :=
  map_inv (post φ) x

theorem pre_inv {Y Y' A : C} [GrpObj A] (ρ : Y' ⟶ Y) (x : Y ⟶ A) : ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  map_inv (pre ρ) x

theorem isPullback_of_lift {Z P G B : C} {f : Z ⟶ P} {g : Z ⟶ G} {h : P ⟶ B} {k : G ⟶ B}
    (w : f ≫ h = g ≫ k) (hm : ∀ {Y : C} {a b : Y ⟶ Z}, a ≫ f = b ≫ f → a ≫ g = b ≫ g → a = b)
    (hl : ∀ {Y : C} (x : Y ⟶ P) (y : Y ⟶ G), x ≫ h = y ≫ k → ∃ l : Y ⟶ Z, l ≫ f = x ∧ l ≫ g = y) :
    IsPullback f g h k :=
  ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (hl s.fst s.snd s.condition).choose)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.1)
    (fun s => (hl s.fst s.snd s.condition).choose_spec.2)
    (fun s m h1 h2 => hm (h1.trans (hl s.fst s.snd s.condition).choose_spec.1.symm)
      (h2.trans (hl s.fst s.snd s.condition).choose_spec.2.symm))⟩⟩

end General

theorem mulN_eq_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih]; rfl

section Main
variable {S : Scheme.{0}} {T Gt B : Over S} [GrpObj T] [IsCommMonObj T] [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B]
  [IsCommMonObj B] {u : T ⟶ Gt} {q : Gt ⟶ B} [IsMonHom u] [IsMonHom q] {N : ℕ}
  {TN GN BN : Over S} {jT : TN ⟶ T} {jG : GN ⟶ Gt} {jB : BN ⟶ B} {eB : 𝟙_ _ ⟶ BN}

theorem mono_of_ext (hu : IsPullback u (toUnit _) q η[B]) : Mono u :=
  ⟨fun _ _ h => hu.hom_ext h (toUnit_unique _ _)⟩

theorem lift_of_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (y : Y ⟶ Gt) (hy : y ≫ q = 1) :
    ∃ z : Y ⟶ T, z ≫ u = y :=
  ⟨hu.lift y (toUnit Y) (by rw [hy, Hom.one_def]), hu.lift_fst _ _ _⟩

theorem comp_ext (hu : IsPullback u (toUnit _) q η[B]) {Y : Over S} (z : Y ⟶ T) : (z ≫ u) ≫ q = 1 := by
  rw [Category.assoc, hu.w, Hom.one_def, ← Category.assoc, toUnit_unique (z ≫ toUnit T) (toUnit Y)]

theorem isPullback_kernel (hu : IsPullback u (toUnit _) q η[B])
    (hT : IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[T]) (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt])
    (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B]) (he : eB ≫ jB = η[B])
    {a : TN ⟶ GN} {b : GN ⟶ BN} (ha : a ≫ jG = jT ≫ u) (hb : b ≫ jB = jG ≫ q) :
    IsPullback a (toUnit TN) b eB := by
  have := mono_of_ext hu
  have := mono_of_pullback hT
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  refine GlobalTheory.Diag.isPullback_toUnit_of_lift S ?_ (fun {Y} x y h => ?_) (fun {Y} t ht => ?_)
  · rw [← cancel_mono jB, Category.assoc, hb, reassoc_of% ha, Category.assoc, he]
    have := comp_ext hu jT
    rw [Category.assoc] at this
    rw [this, Hom.one_def]
  · rw [← cancel_mono jG, Category.assoc, Category.assoc, ha] at h
    rw [← cancel_mono (jT ≫ u)]
    simpa using h
  · have h1 : (t ≫ jG) ≫ q = 1 := by
      have : t ≫ b ≫ jB = t ≫ jG ≫ q := by rw [hb]
      rw [Category.assoc, ← this, ← Category.assoc, ht, Category.assoc, he, Hom.one_def]
    obtain ⟨v, hv⟩ := lift_of_ext hu _ h1
    have h2 : v ^ N = 1 := by
      rw [← cancel_mono u, post_pow, hv, torsion_of_comp hG, MonObj.one_comp]
    obtain ⟨w, hw⟩ := lift_of_torsion hT v h2
    refine ⟨w, ?_⟩
    rw [← cancel_mono jG, Category.assoc, ha, reassoc_of% hw, hv]

theorem exists_isPullback_cover (hu : IsPullback u (toUnit _) q η[B])
    (hG : IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt]) (hB : IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B])
    {b : GN ⟶ BN} (hb : b ≫ jB = jG ≫ q) {P : Over S} {pG : P ⟶ Gt} {pB : P ⟶ BN} (hP : pG ≫ q = pB ≫ jB) :
    ∃ (φ : P ⟶ T) (c : pullback φ ((𝟙 T) ^ N) ⟶ GN), IsPullback (pullback.fst _ _) c pB b := by
  have := mono_of_ext hu
  have := mono_of_pullback hG
  have := mono_of_pullback hB
  have h0 : (pG ^ N)⁻¹ ≫ q = 1 := by
    rw [post_inv, post_pow, hP, torsion_of_comp hB, inv_one]
  obtain ⟨φ, hφ⟩ := lift_of_ext hu _ h0
  have key : ∀ {Y : Over S} (y : Y ⟶ P), (y ≫ φ) ≫ u = ((y ≫ pG) ^ N)⁻¹ := fun y => by
    rw [Category.assoc, hφ, pre_inv, pre_pow]
  have hz : ∀ {Y : Over S} (z : Y ⟶ T), z ≫ ((𝟙 T) ^ N) = z ^ N := fun z => by
    rw [pre_pow, Category.comp_id]
  have tor : ((pullback.snd φ ((𝟙 T) ^ N) ≫ u) * (pullback.fst φ ((𝟙 T) ^ N) ≫ pG)) ^ N = 1 := by
    rw [mul_pow, ← post_pow u, ← hz (pullback.snd φ ((𝟙 T) ^ N)), ← pullback.condition, key, inv_mul_cancel]
  obtain ⟨c, hc⟩ := lift_of_torsion hG _ tor
  refine ⟨φ, c, isPullback_of_lift ?_ (fun {Y} a a' h1 h2 => ?_) (fun {Y} x k hxk => ?_)⟩
  · rw [← cancel_mono jB, Category.assoc, Category.assoc, hb, ← hP, reassoc_of% hc, MonObj.mul_comp,
      comp_ext hu, _root_.one_mul, Category.assoc]
  · refine pullback.hom_ext h1 ?_
    have h3 : a ≫ c ≫ jG = a' ≫ c ≫ jG := by rw [reassoc_of% h2]
    rw [hc, MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc a (pullback.fst _ _) pG,
      ← Category.assoc a' (pullback.fst _ _) pG, h1, mul_left_inj] at h3
    rw [← cancel_mono u, Category.assoc, Category.assoc]
    exact h3
  · have e : (k ≫ jG) ≫ q = (x ≫ pG) ≫ q := by
      rw [Category.assoc, Category.assoc, ← hb, hP, reassoc_of% hxk]
    have hw : ((k ≫ jG) * (x ≫ pG)⁻¹) ≫ q = 1 := by
      rw [MonObj.mul_comp, post_inv, e, mul_inv_cancel]
    obtain ⟨s, hs⟩ := lift_of_ext hu _ hw
    have hsN : x ≫ φ = s ≫ ((𝟙 T) ^ N) := by
      rw [← cancel_mono u, key x, hz, post_pow, hs, mul_pow, torsion_of_comp hG, _root_.one_mul, inv_pow]
    refine ⟨pullback.lift x s hsN, pullback.lift_fst _ _ _, ?_⟩
    rw [← cancel_mono jG, Category.assoc, hc, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
      pullback.lift_fst, pullback.lift_snd, hs, inv_mul_cancel_right]

end Main

theorem torsion_exact : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Gt B : Over S) [GrpObj Gt] [IsCommMonObj Gt] [GrpObj B] [IsCommMonObj B] (u : splitTorus S X ⟶ Gt) (q : Gt ⟶ B) [IsMonHom u] [IsMonHom q], Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback u (toUnit _) q η[B] → ∀ (N : ℕ), 1 ≤ N → ∀ (TN GN BN : Over S) (jT : TN ⟶ splitTorus S X) (jG : GN ⟶ Gt) (jB : BN ⟶ B) (eB : 𝟙_ _ ⟶ BN), IsPullback jT (toUnit _) ((𝟙 _) ^ N) η[splitTorus S X] → IsPullback jG (toUnit _) ((𝟙 _) ^ N) η[Gt] → IsPullback jB (toUnit _) ((𝟙 _) ^ N) η[B] → eB ≫ jB = η[B] → ∀ (a : TN ⟶ GN) (b : GN ⟶ BN), a ≫ jG = jT ≫ u → b ≫ jB = jG ≫ q → Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit TN) b eB := by
  intro S X _ _ _ Gt B _ _ _ _ u q _ _ hfl hsu hqc hu N hN TN GN BN jT jG jB eB hT hG hB he a b ha hb
  have hN' : N ≠ 0 := by omega
  have hP := IsPullback.of_hasPullback q jB
  obtain ⟨φ, c, sq⟩ := exists_isPullback_cover hu hG hB hb hP.w
  have sql : IsPullback (pullback.fst φ ((𝟙 _) ^ N)).left c.left (pullback.snd q jB).left b.left :=
    sq.map (Over.forget S)
  have hPl : IsPullback (pullback.fst q jB).left (pullback.snd q jB).left q.left jB.left :=
    hP.map (Over.forget S)
  have hZl : IsPullback (pullback.snd φ ((𝟙 _) ^ N)).left (pullback.fst φ ((𝟙 _) ^ N)).left
      ((𝟙 (splitTorus S X)) ^ N).left φ.left :=
    (IsPullback.of_hasPullback φ ((𝟙 _) ^ N)).flip.map (Over.forget S)
  have f1 : Flat ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.flat_mulN S X hN'
  have s1 : Surjective ((𝟙 (splitTorus S X)) ^ N).left := by
    rw [← mulN_eq_pow]; exact GlobalTheory.Diag.surjective_mulN S X hN'
  have f2 : Flat (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl f1
  have s2 : Surjective (pullback.fst φ ((𝟙 _) ^ N)).left := MorphismProperty.of_isPullback hZl s1
  have f3 : Flat (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hfl
  have s3 : Surjective (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hsu
  have c3 : QuasiCompact (pullback.snd q jB).left := MorphismProperty.of_isPullback hPl hqc
  refine ⟨?_, ?_, isPullback_kernel hu hT hG hB he ha hb⟩
  · haveI := GlobalTheory.flat_descendsAlong_fpqc
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sql ⟨⟨s3, f3⟩, c3⟩ f2
  · have : Surjective (c.left ≫ b.left) := by
      rw [← sql.w]; infer_instance
    exact Surjective.of_comp c.left b.left

end GlobalTheory.CompanionTheory.Ar.BT.Tors.Ext
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.power_map_flat_semiabelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ N : ℕ, 1 ≤ N → Flat ((𝟙 G) ^ N).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian | exact GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem surjective_pow_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 →
      Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro K _ A _ hA n hn
  haveI : Smooth A.hom := IsAbelianScheme.smooth (self := hA)
  haveI : IsProper A.hom := IsAbelianScheme.proper (self := hA)
  haveI : GeometricallyConnected A.hom := IsAbelianScheme.geomConnected (self := hA)
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI : ConnectedSpace (Sp K) := inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of K)))
  have hw : ((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  haveI : Flat ((𝟙 A) ^ n : A ⟶ A).left :=
    GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Sp K) A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA) n
      (Nat.one_le_iff_ne_zero.mpr hn)
  haveI : LocallyOfFiniteType ((𝟙 A) ^ n : A ⟶ A).left :=
    HasRingHomProperty.of_comp (fun _ _ h => RingHom.FiniteType.of_comp_finiteType h)
      (by rw [hw]; infer_instance)
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  haveI : LocallyOfFinitePresentation ((𝟙 A) ^ n : A ⟶ A).left := inferInstance
  haveI : UniversallyOpen ((𝟙 A) ^ n : A ⟶ A).left := UniversallyOpen.of_flat _
  haveI : IsProper (((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom) := by rw [hw]; infer_instance
  haveI : IsProper ((𝟙 A) ^ n : A ⟶ A).left := IsProper.of_comp _ A.hom
  haveI : UniversallyOpen A.hom := UniversallyOpen.of_flat _
  haveI : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have hclopen : IsClopen (Set.range ((𝟙 A) ^ n : A ⟶ A).left) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  refine ⟨fun y => ?_⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have hy := Set.mem_range_self (f := ⇑((𝟙 A) ^ n : A ⟶ A).left) y
    rw [h] at hy
    exact hy.elim
  · have hy : y ∈ Set.range ⇑((𝟙 A) ^ n : A ⟶ A).left := by rw [h]; trivial
    exact hy

end GlobalTheory.CompanionTheory.Ar.Approx
end

end

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

theorem _root_.GlobalTheory.T.abelianScheme_nsmul_surjective : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme | exact GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme <;> assumption)

end
end
