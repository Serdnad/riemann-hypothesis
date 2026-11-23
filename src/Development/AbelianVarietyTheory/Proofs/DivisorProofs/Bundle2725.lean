module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem regAt_pow_of_regAt {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {u : Y.functionField} (h : RegAt y u) (n : ℕ) :
    RegAt y (u ^ n) :=
  have ⟨a, ha⟩ := h; ⟨a ^ n, by rw [map_pow, ha]⟩

theorem exists_regAt_mul_pow_affine {Y : Scheme.{0}} [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (hg : genericPoint Y ∈ U) {u g : Y.functionField} (hu0 : u ≠ 0) (hu : ∀ y ∈ U, RegAt y u)
    (h : ∀ y ∈ U, UnitAt y u → RegAt y g) : ∃ n : ℕ, ∀ y ∈ U, RegAt y (g * u ^ n) := by
  obtain ⟨f, rfl⟩ := exists_fnOf_eq hg hu
  have hb : genericPoint Y ∈ Y.basicOpen f := (unitAt_fnOf_iff hg hg f).1 (unitAt_genericPoint hu0)
  obtain ⟨b, rfl⟩ := exists_fnOf_eq hb fun y hy =>
    h y (Y.basicOpen_le f hy) ((unitAt_fnOf_iff (Y.basicOpen_le f hy) hg f).2 hy)
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) b
  refine ⟨n, fun y hy => ?_⟩
  have e' := congrArg (fnOf _ hb) e
  have r (c : Γ(Y, U)) : fnOf _ hb (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) c) = fnOf U hg c :=
    fnOf_resG (Y.basicOpen_le f) hb c
  simp only [map_mul, r] at e'
  rw [map_pow] at e'
  rw [e']
  exact regAt_fnOf hy hg a

theorem exists_mul_pow_mem_sec (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] (D : CartierDiv Y) (k : ℕ)
    (s : Y.functionField) (hs : s ∈ Sec D k) (g : Y.functionField) (hg : ∀ y ∈ locus D k s, RegAt y g) :
    ∃ n : ℕ, g * s ^ n ∈ Sec D (k * n) := by
  by_cases hs0 : s = 0
  · refine ⟨1, fun x => ?_⟩
    rw [hs0, pow_one, mul_zero]
    exact (CartierDiv.vanishesAt_zero _ x).regularAt
  have key (x : Y) : ∃ U : Y.Opens, x ∈ U ∧ ∃ n : ℕ, ∀ m, n ≤ m → ∀ y ∈ U,
      ((k * m) • D).RegularAt y (g * s ^ m) := by
    obtain ⟨V, hV, e, he⟩ := (k • D).exists_isEqn_nhds x
    obtain ⟨U, hU, hx, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
    have hu (y) (hy : y ∈ U) : RegAt y (s * e) := (he y (hUV hy)).regularAt_iff.1 (hs y)
    obtain ⟨n, hn⟩ := exists_regAt_mul_pow_affine (g := g) hU (gen_mem hx) (mul_ne_zero hs0 e.ne_zero) hu
      fun y hy h => hg y ⟨e, he y (hUV hy), h⟩
    refine ⟨U, hx, n, fun m hm y hy => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [mul_nsmul]
    refine ⟨_, (he y (hUV hy)).nsmul _, ?_⟩
    have := (hn y hy).mul (regAt_pow_of_regAt (hu y hy) d)
    rwa [_root_.mul_assoc, ← pow_add, mul_pow, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val] at this
  choose U hU n hn using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set Y)) (fun x => (U x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩
  refine ⟨t.sup n, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact hn x _ (Finset.le_sup hx) y hy

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem hom_ext_of_cartesian {S S₀ X : Scheme.{0}} {q : X ⟶ S} {s₀ : S₀ ⟶ S} {A : Over S₀}
    {i : A.left ⟶ X} (h : IsPullback i A.hom q s₀) {T : Scheme.{0}} {t₀ : T ⟶ S₀}
    (c c' : Over.mk t₀ ⟶ A) (hc : c.left ≫ i = c'.left ≫ i) : c = c' := by
  apply Over.OverMorphism.ext
  apply h.hom_ext hc
  rw [Over.w c, Over.w c']

theorem oneAgree_invAgree_of_mulAgree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  intro S S₀ S₁ X q s₀ s₁ A _ G _ i e h he hm
  have one : OneAgree s₁ s₀ G A e i := by
    intro T t₁ t₀ ht
    have hw : ((1 : Over.mk t₁ ⟶ G).left ≫ e) ≫ q = t₀ ≫ s₀ := by
      rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
    let a' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
    have ha' : a'.left ≫ i = (1 : Over.mk t₁ ⟶ G).left ≫ e := h.lift_fst _ _ _
    have hmm := hm T t₁ t₀ 1 1 a' a' ha'.symm ha'.symm
    rw [_root_.mul_one] at hmm
    have h2 : a' * a' = a' := hom_ext_of_cartesian h _ _ (by rw [← hmm, ha'])
    have h3 : a' = 1 := by simpa using h2
    rw [← ha', h3]
  refine ⟨one, ?_⟩
  intro T t₁ t₀ a a' haa
  have ht : t₁ ≫ s₁ = t₀ ≫ s₀ := by
    have w1 : a.left ≫ G.hom = t₁ := Over.w a
    have w0 : a'.left ≫ A.hom = t₀ := Over.w a'
    calc t₁ ≫ s₁ = (a.left ≫ G.hom) ≫ s₁ := by rw [w1]
      _ = (a.left ≫ e) ≫ q := by rw [Category.assoc, Category.assoc, he]
      _ = (a'.left ≫ i) ≫ q := by rw [haa]
      _ = (a'.left ≫ A.hom) ≫ s₀ := by rw [Category.assoc, Category.assoc, h.w]
      _ = t₀ ≫ s₀ := by rw [w0]
  have hw : ((a⁻¹).left ≫ e) ≫ q = t₀ ≫ s₀ := by
    rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
  let b' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
  have hb' : b'.left ≫ i = (a⁻¹).left ≫ e := h.lift_fst _ _ _
  have hmm := hm T t₁ t₀ a a⁻¹ a' b' haa hb'.symm
  rw [_root_.mul_inv_cancel] at hmm
  have h2 : a' * b' = 1 := hom_ext_of_cartesian h _ _ (by rw [← hmm, one T t₁ t₀ ht])
  have h3 : b' = a'⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h3, hb']

end GlobalTheory.Desc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

variable {Y X : Scheme.{0}} [IsIntegral Y] [IsIntegral X]

theorem theta_stalk {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    (a : X.presheaf.stalk (π y)) :
    θ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a) := by
  obtain ⟨l, h₁, h₂⟩ := h
  rw [Category.comp_id] at h₁
  subst h₁
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes y)
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (π y))
  have e₁ : Spec.map sY ≫ Y.fromSpecStalk y = gp Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : π.stalkMap y ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (π y)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  exact (congrArg (fun f => CommRingCat.Hom.hom f a) e₂).symm

theorem theta_fnOf {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ)
    (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hU s) = fnOf (π ⁻¹ᵁ U) hU' (π.app U s) := by
  have hU'' : π (genericPoint Y) ∈ U := hU'
  rw [← algebraMap_germ (x := π (genericPoint Y)) hU'' s, theta_stalk h,
    Scheme.Hom.germ_stalkMap_apply]
  exact algebraMap_germ hU' _

theorem regAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨_, (theta_stalk h y a).symm⟩

theorem unitAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : UnitAt (π y) u) : UnitAt y (θ u) := by
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨_, ha.map _, (theta_stalk h y a).symm⟩

theorem preimage_regSet {π : Y ⟶ X} [Flat π] {θ : X.functionField →+* Y.functionField}
    (h : PFF (𝟙 _) π θ) (y : Y) : θ ⁻¹' (regSet y) = regSet (π y) := by
  ext u
  refine ⟨fun ⟨c, hc⟩ => ?_, fun hu => regAt_theta h y hu⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (π y)) u
  have hb0 : algebraMap _ X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  letI := (π.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π y))
    (B := Y.presheaf.stalk y)
  have e : π.stalkMap y a = c * π.stalkMap y b := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, hc, ← theta_stalk h, ← theta_stalk h, ← map_mul, div_mul_cancel₀ _ hb0]
  have hm : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) (Ideal.span {b}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, e.symm⟩
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨d, by rw [map_mul, mul_div_cancel_right₀ _ hb0]⟩

theorem spMap_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : spMap (GlobalTheory.Desc.cst p) = gp X ≫ p := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  conv_rhs => rw [h, gp, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

theorem comp_cst {V : Scheme.{0}} {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {p : X ⟶ Sp R}
    {q : Y ⟶ Sp R₁} {i : V ⟶ Y} {φ : V ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF i φ θ)
    (w : φ ≫ p = (i ≫ q) ≫ spMap ρ) : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst q).comp ρ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap ((GlobalTheory.Desc.cst q).comp ρ) := by
    have e1 : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap θ ≫ spMap (GlobalTheory.Desc.cst p) := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((GlobalTheory.Desc.cst q).comp ρ) = spMap (GlobalTheory.Desc.cst q) ≫ spMap ρ := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, spMap_cst, spMap_cst, ← Category.assoc, ← h₂, ← h₁]
    simp only [Category.assoc, w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem regAt_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) : RegAt x (GlobalTheory.Desc.cst p r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem unitAt_cst_iff {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    UnitAt x (GlobalTheory.Desc.cst p r) ↔ r ∉ (p x).asIdeal := by
  refine (unitAt_fnOf_iff (U := ⊤) trivial trivial _).trans ?_
  change x ∈ X.basicOpen (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

end GlobalTheory.Desc.GaussPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.StalkMap

variable {X : Scheme.{0}}

theorem top_le_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem appLE_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (top_le_fromSpecStalk x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (top_le_fromSpecStalk x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

def val {R : Type} [CommRing R] (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

theorem val_congr {R : Type} [CommRing R] {g g' : Sp R ⟶ X} (e : g = g') (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(X, V)) : val g V h u = val g' V h' u := by
  subst e; rfl

theorem val_gp [IsIntegral X] (V : X.Opens) (hV : genericPoint X ∈ V) (h : ⊤ ≤ gp X ⁻¹ᵁ V) (u : Γ(X, V)) :
    val (gp X) V h u = GlobalTheory.Cartier.fnOf V hV u := by
  have : (gp X).appLE V ⊤ h = X.presheaf.germ V _ hV ≫ (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv :=
    appLE_fromSpecStalk (genericPoint X) V hV
  unfold val
  rw [RingHom.comp_apply, this]
  exact (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv_hom_id_apply _

end GlobalTheory.Desc.StalkMap

namespace GlobalTheory.Desc.StalkMap

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem val_appLE (g : Sp R ⟶ X) (φ : X ⟶ X') (V : X'.Opens) (W : X.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(X', V)) :
    val g W h ((φ.appLE V W e).hom u) = val (g ≫ φ) V h' u :=
  congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u))
    (Scheme.Hom.appLE_comp_appLE g φ V W ⊤ e h)

theorem val_top (g : Sp R ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(X, ⊤)) :
    val g ⊤ h u = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  have : g.appLE ⊤ ⊤ h = g.appTop := Scheme.Hom.appLE_eq_app g
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u)) this

theorem val_spMap (σ : R →+* R') (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ (spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(X, V)) : val (spMap σ ≫ g) V h' u = σ (val g V h u) := by
  refine (val_appLE (spMap σ) g V ⊤ h le_top h' u).symm.trans ((val_top (spMap σ) le_top _).trans ?_)
  exact congrArg (fun q => CommRingCat.Hom.hom q ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem fnOf_app_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField) (hm : gp Y ≫ m = spMap φ ≫ gp P) {W : P.Opens}
    (hY : genericPoint Y ∈ m ⁻¹ᵁ W) (hP : genericPoint P ∈ W) (s : Γ(P, W)) :
    GlobalTheory.Cartier.fnOf (m ⁻¹ᵁ W) hY ((m.app W).hom s) = φ (GlobalTheory.Cartier.fnOf W hP s) := by
  have h1 : ⊤ ≤ gp Y ⁻¹ᵁ (m ⁻¹ᵁ W) := top_le_fromSpecStalk _ _ hY
  have h2 : ⊤ ≤ gp P ⁻¹ᵁ W := top_le_fromSpecStalk _ _ hP
  have h3 : ⊤ ≤ (gp Y ≫ m) ⁻¹ᵁ W := h1
  have h4 : ⊤ ≤ (spMap φ ≫ gp P) ⁻¹ᵁ W := hm ▸ h3
  rw [← val_gp _ hY h1, ← val_gp _ hP h2, ← val_spMap φ (gp P) W h2 h4,
    ← val_congr hm W h3 h4, ← val_appLE (gp Y) m W (m ⁻¹ᵁ W) le_rfl h1 h3, Scheme.Hom.app_eq_appLE]

end GlobalTheory.Desc.StalkMap


open GlobalTheory.Desc.StalkMap in
theorem GlobalTheory.Desc.regAt_map_of_gp : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField),
    RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  intro Y P _ _ m φ hm y v hv
  obtain ⟨W, hW, s, rfl⟩ := hv.exists_fnOf
  have hy : y ∈ m ⁻¹ᵁ W := hW
  have hY : genericPoint Y ∈ m ⁻¹ᵁ W := gen_mem hy
  rw [← fnOf_app_eq m φ hm hY (gen_mem hW) s]
  refine ⟨regAt_fnOf hy hY _, ?_⟩
  rw [unitAt_fnOf_iff hy hY, unitAt_fnOf_iff hW (gen_mem hW), ← Scheme.preimage_basicOpen]
  rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.RegPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem germ_gp (V : Y.Opens) (hY : genericPoint Y ∈ V) (h : gp Y (closedPoint _) ∈ V) :
    Y.presheaf.germ V (gp Y (closedPoint _)) h ≫ Scheme.stalkClosedPointTo (gp Y) =
      Y.presheaf.germ V (genericPoint Y) hY := by
  have hC : ∀ G : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ Y,
      G = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) → ∀ h,
      Y.presheaf.germ V (G (closedPoint _)) h ≫ Scheme.stalkClosedPointTo G =
        Y.presheaf.germ V (genericPoint Y) hY ≫ 𝟙 _ := by
    rintro G rfl h
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 _) V h
  have e : gp Y = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [Spec.map_id, Category.id_comp]; rfl
  exact (hC (gp Y) e h).trans (Category.comp_id _)

theorem fnOf_map (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField)
    (e : gp Y ≫ π = spMap θ ≫ gp X) (U : X.Opens) (hX : genericPoint X ∈ U)
    (hY : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hX s) = fnOf (π ⁻¹ᵁ U) hY (π.app U s) := by
  have hA : ∀ F : Sp Y.functionField ⟶ X, F = spMap θ ≫ gp X → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        X.presheaf.germ U (genericPoint X) hX ≫ CommRingCat.ofHom θ := by
    rintro F rfl hU
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom θ) U hU
  have hg : gp Y (closedPoint _) = genericPoint Y := Scheme.fromSpecStalk_closedPoint
  have hV : gp Y (closedPoint _) ∈ π ⁻¹ᵁ U := by rw [hg]; exact hY
  have hB : ∀ F : Sp Y.functionField ⟶ X, F = gp Y ≫ π → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        π.app U ≫ Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hY := by
    rintro F rfl hU
    rw [Scheme.stalkClosedPointTo_comp]
    refine (Scheme.Hom.germ_stalkMap_assoc π U (gp Y (closedPoint _)) hV _).trans ?_
    exact congrArg (π.app U ≫ ·) (germ_gp (π ⁻¹ᵁ U) hY hV)
  have := (hA _ e hV).symm.trans (hB _ rfl hV)
  exact congrArg (fun g => g.hom s) this

theorem regAt_map (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (θ : X.functionField →+* Y.functionField) (hθ : PFF (𝟙 _) π θ) (y : Y) (u : X.functionField)
    (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨l, hl, e⟩ := hθ
  rw [Category.comp_id] at hl
  subst hl
  obtain ⟨U, hx, s, rfl⟩ := hu.exists_fnOf
  have hy : y ∈ π ⁻¹ᵁ U := hx
  rw [fnOf_map π θ e U _ (gen_mem hy) s]
  exact regAt_fnOf hy _ _

end GlobalTheory.Desc.RegPull
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

namespace GlobalTheory.Desc.FlatLinDisj

theorem linDisj_of_flat (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁]
    [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L)
    (h : ∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) :
    LinDisj (algebraMap R K) c θ := by
  intro n u hu r hr
  let f : (Fin n → R) →ₗ[R] K := Fintype.linearCombination R u
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply hu a
    simpa [f, Fintype.linearCombination_apply, Algebra.smul_def] using ha
  have hft : Function.Injective (f.rTensor R₁) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  set x : (Fin n → R) ⊗[R] R₁ := ∑ j, Pi.single j 1 ⊗ₜ[R] r j with hx
  have hx0 : x = 0 := by
    apply hft

    rw [map_zero, hx, map_sum]
    simp only [LinearMap.rTensor_tmul]
    have := h n u r hr
    simpa [f, Fintype.linearCombination_apply_single] using this
  funext i
  have key : TensorProduct.lid R R₁ ((LinearMap.proj (R := R) (φ := fun _ : Fin n => R) i).rTensor R₁ x) = r i := by

    rw [hx, map_sum, map_sum]
    simp [LinearMap.rTensor_tmul, Pi.single_apply]
  rw [← key, hx0]
  simp

end GlobalTheory.Desc.FlatLinDisj
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstOrderLift_derivation_comm_translations : ∀ (k : Type) [Field k] (Y Y' X : Scheme.{0}) (m : Y ⟶ X) (π : Y' ⟶ Sp (DualNumber k)) (ρ' : Y' ⟶ Y) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) (Φ : Y' ⟶ X), (∀ y, Φ y = m (ρ' y)) → (∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ' ≫ m) f (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) + constFn π (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W)) DualNumber.eps * pbT ρ' (d W f) (ρ' ⁻¹ᵁ (m ⁻¹ᵁ W))) → ∀ (T : X ⟶ X) (T₀ : Y ⟶ Y) (TY : Y' ⟶ Y'), T₀ ≫ m = m ≫ T → TY ≫ ρ' = ρ' ≫ T₀ → TY ≫ π = π → (∀ (W : X.Opens) (f : Γ(X, W)), d (T ⁻¹ᵁ W) ((T.app W).hom f) = pbT T₀ (d W f) (m ⁻¹ᵁ (T ⁻¹ᵁ W))) → TY ≫ Φ = Φ ≫ T := by
  first | exact @GlobalTheory.KS.LiftComm.translate_comm | exact GlobalTheory.KS.LiftComm.translate_comm | (intros; apply GlobalTheory.KS.LiftComm.translate_comm <;> assumption)
end
