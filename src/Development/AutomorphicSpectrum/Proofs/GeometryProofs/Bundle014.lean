module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.PullSub

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T)
  {R' : Type} [CommRing R'] [IsDomain R'] (Γ' : QFGroup R' T) (φ : R →+* R')
  (F : Γ'.G.left ⟶ Γ.G.left)

def pushPt (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    Over.mk (S.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G :=
  Over.homMk (x.left ≫ F) (by
    have hx : x.left ≫ Γ'.G.hom = S.hom := Over.w x
    simp only [Over.mk_hom, Category.assoc, hw]
    rw [← Category.assoc, hx])

variable {Γ Γ' φ F}

theorem pushPt_left (hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    (pushPt Γ Γ' φ F hw x).left = x.left ≫ F := rfl

theorem pushPt_mul (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x y : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w (x * y) = pushPt Γ Γ' φ F h.cart.w x * pushPt Γ Γ' φ F h.cart.w y := by
  apply Over.OverMorphism.ext
  rw [pushPt_left]
  exact (h.mul S x y _ _ (pushPt_left h.cart.w x) (pushPt_left h.cart.w y)).symm

theorem pushPt_one (h : Γ'.IsBaseChange Γ φ F) (S : Over (Spec (CommRingCat.of R'))) :
    pushPt Γ Γ' φ F h.cart.w (1 : S ⟶ Γ'.G) = 1 := by
  have h1 := pushPt_mul h (1 : S ⟶ Γ'.G) 1
  rw [_root_.mul_one] at h1
  exact _root_.mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)

theorem pushPt_inv (h : Γ'.IsBaseChange Γ φ F)
    {S : Over (Spec (CommRingCat.of R'))} (x : S ⟶ Γ'.G) :
    pushPt Γ Γ' φ F h.cart.w x⁻¹ = (pushPt Γ Γ' φ F h.cart.w x)⁻¹ := by
  have h2 := pushPt_mul h x⁻¹ x
  rw [_root_.inv_mul_cancel, pushPt_one h S] at h2
  exact eq_inv_of_mul_eq_one_left h2.symm

end GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub

open GlobalTheory.CompanionTheory.Ar.BT.PullSub in
theorem GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F h U hU
  have hpb := (isPullback_morphismRestrict F U).paste_vert h.cart
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) hpb hU.finite, ?_, ?_, ?_⟩
  · intro x
    have e1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G) = MonObj.one := by
      change SemiCartesianMonoidalCategory.toUnit _ ≫ MonObj.one = MonObj.one
      rw [SemiCartesianMonoidalCategory.toUnit_unique (SemiCartesianMonoidalCategory.toUnit _) (𝟙 _),
        Category.id_comp]
    have e2 : (1 : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ Γ'.G).left ≫ F =
        (1 : Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R'))) ⟶ Γ.G).left := by
      rw [← pushPt_left h.cart.w, pushPt_one h]
    rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← e1, e2]
    change (Over.Hom.left (SemiCartesianMonoidalCategory.toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R')))).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (MonObj.one : 𝟙_ _ ⟶ Γ.G))) x ∈ U
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hU.one _
  · intro S x y hx hy z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hy' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w y).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hy w)
    have hxy := hU.mul _ _ _ hx' hy' z
    rw [← pushPt_mul h, pushPt_left, Scheme.Hom.comp_apply] at hxy
    exact (Scheme.Hom.mem_preimage F).mpr hxy
  · intro S x hx z
    have hx' : ∀ w, (pushPt Γ Γ' (algebraMap R R') F h.cart.w x).left w ∈ U := fun w => by
      rw [pushPt_left, Scheme.Hom.comp_apply]
      exact (Scheme.Hom.mem_preimage F).mp (hx w)
    have hxi := hU.inv _ _ hx' z
    rw [← pushPt_inv h, pushPt_left, Scheme.Hom.comp_apply] at hxi
    exact (Scheme.Hom.mem_preimage F).mpr hxi
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.EtaleTop

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem stalk_spec_normal [IsIntegrallyClosed R] (y : Spec (CommRingCat.of R)) :
    IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) y
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

theorem genPt_asIdeal (Γ : QFGroup R T) (t : T) (x : Spec (CommRingCat.of (FractionRing R))) :
    (Γ.G.hom ((Γ.pt t).left x)).asIdeal = ⊥ := by
  have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
  have : Γ.G.hom ((Γ.pt t).left x) = (genPt R).hom x := by
    rw [← hw]; rfl
  rw [this]
  show Ideal.comap (algebraMap R (FractionRing R)) x.asIdeal = ⊥
  have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime
  rw [hx, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))

theorem eq_of_specializes_bot {y z : Spec (CommRingCat.of R)} (h : y ⤳ z) (hz : z.asIdeal = ⊥) :
    y = z := by
  have h' : @LE.le (PrimeSpectrum R) _ y z := (PrimeSpectrum.le_iff_specializes (R := R) y z).2 h
  have h'' : y.asIdeal ≤ z.asIdeal := h'
  refine PrimeSpectrum.ext (le_antisymm h'' ?_)
  rw [hz]; exact bot_le

theorem eq_of_specializes_lqf {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] {a b : X}
    (h : a ⤳ b) (e : f a = f b) : a = b := by
  have hd := (f.isDiscrete_preimage_singleton (f b)).to_subtype
  have : (⟨a, e⟩ : f ⁻¹' {f b}) ⤳ ⟨b, rfl⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val this.eq

theorem eq_of_specializes_pt [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (x : Spec (CommRingCat.of (FractionRing R))) (g : Γ.G.left) (s t : T)
    (hs : (Γ.pt s).left x ⤳ g) (ht : (Γ.pt t).left x ⤳ g) : s = t := by
  have := Γ.quasiFinite
  obtain ⟨h1, h2⟩ := stalk_spec_normal (R := R) (Γ.G.hom g)
  have hdom : IsDomain (Γ.G.left.presheaf.stalk g) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth Γ.G.hom g).1
  let e₀ : Spec (Γ.G.left.presheaf.stalk g) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have key : ∀ u : T, (Γ.pt u).left x ⤳ g → Γ.G.left.fromSpecStalk g e₀ = (Γ.pt u).left x := by
    intro u hu
    have hr : (Γ.pt u).left x ∈ Set.range (Γ.G.left.fromSpecStalk g) := by
      rw [Scheme.range_fromSpecStalk]; exact hu
    obtain ⟨a, ha⟩ := hr
    have he₀a : e₀ ⤳ a := (PrimeSpectrum.le_iff_specializes (R := Γ.G.left.presheaf.stalk g) e₀ a).1
      (show (⊥ : Ideal _) ≤ _ from bot_le)
    have h3 : Γ.G.left.fromSpecStalk g e₀ ⤳ (Γ.pt u).left x := ha ▸ he₀a.map (Γ.G.left.fromSpecStalk g).continuous
    refine eq_of_specializes_lqf Γ.G.hom h3 ?_
    exact eq_of_specializes_bot (h3.map Γ.G.hom.continuous) (genPt_asIdeal Γ u x)
  exact Γ.pt_inj s t x x ((key s hs).symm.trans (key t ht))

theorem genPt_appLE (f : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R))
    (hf : f = (genPt R).hom) (e) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ ⊤ e ≫
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
      CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
  subst hf
  have : (genPt R).hom.appLE ⊤ ⊤ e = (genPt R).hom.appTop := rfl
  rw [this]
  change (Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop ≫ _ = _
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem regularAt_const [Finite T] [IsIntegrallyClosed R] (Γ : QFGroup R T) (hE : Etale Γ.G.hom)
    (φ : T → R) (g : Γ.G.left) :
    Γ.RegularAt (fun h => algebraMap R (FractionRing R) (φ h)) g := by
  classical
  let x₀ : Spec (CommRingCat.of (FractionRing R)) :=
    (IsLocalRing.closedPoint (FractionRing R) : PrimeSpectrum _)
  let P : T → Γ.G.left := fun t => (Γ.pt t).left x₀
  let Z : Set Γ.G.left := ⋃ t ∈ {t | ¬ P t ⤳ g}, closure {P t}
  have hZ : IsClosed Z := (Set.toFinite _).isClosed_biUnion fun _ _ => isClosed_closure
  let U : Γ.G.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hgU : g ∈ U := by
    show g ∉ Z
    simp only [Z, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro t ht hg
    exact ht (specializes_iff_mem_closure.2 hg)
  have hPU : ∀ t, P t ∈ U → P t ⤳ g := by
    intro t ht
    by_contra hn
    exact ht (Set.mem_biUnion (x := t) hn (subset_closure rfl))
  refine ⟨U, hgU, ?_⟩
  by_cases hex : ∃ t₀, P t₀ ⤳ g
  · obtain ⟨t₀, ht₀⟩ := hex
    refine ⟨(Γ.G.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ t₀)), ?_⟩
    intro t h
    have htU : P t ∈ U := h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
    have := eq_of_specializes_pt Γ hE x₀ g t t₀ (hPU t htU) ht₀
    subst this
    have hw : (Γ.pt t).left ≫ Γ.G.hom = (genPt R).hom := Over.w (Γ.pt t)
    have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Γ.G.hom.appLE ⊤ U le_top ≫
        (Γ.pt t).left.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom =
          CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
      erw [Scheme.Hom.appLE_comp_appLE_assoc]
      exact genPt_appLE _ hw _
    exact congrArg (fun m => m.hom (φ t)) key
  · refine ⟨0, fun t h => ?_⟩
    exact absurd ⟨t, hPU t (h (show x₀ ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial))⟩ hex

theorem btOrder_top_eq_top_of_etale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), Etale Γ.G.hom → Γ.btOrder ⊤ = ⊤ := by
  intro R _ _ _ T _ _ Γ hE
  refine eq_top_iff.2 fun f _ => Algebra.subset_adjoin ?_
  intro t g _
  exact regularAt_const Γ hE (fun h => f (t * h)) g

end GlobalTheory.CompanionTheory.Ar.BT.EtaleTop
end

section

open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich.Sep

open NumberField Matrix

private theorem exists_discr_dual_basis_of_discr_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (E : Type) [Field E]
    [NumberField E] (ω : Module.Basis ι ℤ (𝓞 E)) (hd : Algebra.discr ℤ ω ≠ 0) :
    ∃ b : ι → 𝓞 E, ∑ i, ω i * b i = ((Algebra.discr ℤ ω : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∀ i, x * b i = ∑ j, ((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j := by
  obtain ⟨T, hT⟩ : ∃ T, T = Algebra.traceMatrix ℤ ω := ⟨_, rfl⟩
  have hTsymm : ∀ j k, T j k = T k j := fun j k => by
    simp only [hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [mul_comm]
  have hAT : T.adjugate * T = Algebra.discr ℤ ω • (1 : Matrix ι ι ℤ) := by
    rw [Matrix.adjugate_mul, Algebra.discr_def, hT]

  have e1 : ∀ (c : ℤ) (y : 𝓞 E), Algebra.trace ℤ (𝓞 E) ((c : 𝓞 E) * y) =
      c * Algebra.trace ℤ (𝓞 E) y := by
    intro c y
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]
  have htrω : ∀ z : 𝓞 E, ∀ k, Algebra.trace ℤ (𝓞 E) (z * ω k) = ∑ j, ω.repr z j * T j k := by
    intro z k
    conv_lhs => rw [← ω.sum_repr z]

    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_zsmul, smul_eq_mul, hT, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]

  obtain ⟨b, hb⟩ : ∃ b : ι → 𝓞 E, b = fun i => ∑ k, (T.adjugate i k : 𝓞 E) * ω k := ⟨_, rfl⟩
  have hDB : ∀ z : 𝓞 E, ∀ i, Algebra.trace ℤ (𝓞 E) (z * b i) = Algebra.discr ℤ ω * ω.repr z i := by
    intro z i
    calc Algebra.trace ℤ (𝓞 E) (z * b i)
        = ∑ k, T.adjugate i k * Algebra.trace ℤ (𝓞 E) (z * ω k) := by

          simp only [hb, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_left_comm, e1]
      _ = ∑ k, T.adjugate i k * ∑ j, ω.repr z j * T j k := by simp only [htrω]
      _ = ∑ j, ω.repr z j * (T.adjugate * T) i j := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hTsymm j k]
          ring
      _ = Algebra.discr ℤ ω * ω.repr z i := by
          rw [hAT]
          simp [Matrix.smul_apply, Matrix.one_apply]
          try ring
  have hnd : ∀ s : 𝓞 E, (∀ l, Algebra.trace ℤ (𝓞 E) (s * ω l) = 0) → s = 0 := by
    intro s hs
    have hb0 : ∀ i, Algebra.trace ℤ (𝓞 E) (s * b i) = 0 := by
      intro i

      simp only [hb, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mul_left_comm, e1, hs, mul_zero]
    have hr : ∀ i, ω.repr s i = 0 := fun i => by
      have h := hDB s i
      rw [hb0 i] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hd
    rw [← ω.sum_repr s]
    simp [hr]
  have htr : ∀ y : 𝓞 E, Algebra.trace ℤ (𝓞 E) y = ∑ i, ω.repr (y * ω i) i := by
    intro y
    rw [Algebra.trace_eq_matrix_trace ω, Matrix.trace]
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  refine ⟨b, ?_, ?_⟩
  · apply sub_eq_zero.mp
    apply hnd
    intro l

    rw [sub_mul, map_sub, Finset.sum_mul, map_sum, e1, htr (ω l)]
    have h : ∀ i, Algebra.trace ℤ (𝓞 E) (ω i * b i * ω l) =
        Algebra.discr ℤ ω * ω.repr (ω l * ω i) i := fun i => by
      rw [mul_right_comm, hDB, mul_comm (ω i)]
    simp only [h, Finset.mul_sum, sub_self]
  · intro x i
    apply sub_eq_zero.mp
    apply hnd
    intro l

    rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    have h1 : Algebra.trace ℤ (𝓞 E) (x * b i * ω l) = Algebra.discr ℤ ω * ω.repr (x * ω l) i := by
      rw [mul_right_comm, hDB]
    have h2 : ∀ j, Algebra.trace ℤ (𝓞 E) (((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j * ω l) =
        ω.repr (x * ω j) i * (Algebra.discr ℤ ω * ω.repr (ω l) j) := fun j => by
      rw [mul_assoc, e1, mul_comm (b j), hDB]
    simp only [h1, h2, ω.repr_self, Finsupp.single_apply]
    simp
    try ring

theorem exists_sep_element (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∑ i, a i * b i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∃ m : Matrix (Fin n) (Fin n) ℤ, (∀ i, x * a i = ∑ j, (m i j : 𝓞 E) * a j) ∧
        ∀ i, x * b i = ∑ j, (m j i : 𝓞 E) * b j := by
  classical
  let ω := (RingOfIntegers.basis E).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))
  have hdisc : Algebra.discr ℤ ω = discr E := by
    simp only [ω, Module.Basis.coe_reindex]
    rw [Algebra.discr_reindex]
  obtain ⟨b, hsum, hb⟩ := exists_discr_dual_basis_of_discr_ne_zero E ω (by rw [hdisc]; exact discr_ne_zero E)
  refine ⟨_, ω, b, by rw [← hdisc]; exact hsum, fun x =>
    ⟨fun i j => ω.repr (x * ω i) j, fun i => ?_, fun i => hb x i⟩⟩
  conv_lhs => rw [← ω.sum_repr (x * ω i)]
  simp [zsmul_eq_mul]

theorem exists_eigen_op_discr (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (ρ : 𝓞 E →+* Module.End R V) (σ : 𝓞 E →+* R),
      (∀ v, ∑ i, σ (b i) • ρ (a i) v ∈ eigSp ρ σ) ∧
        ∀ v ∈ eigSp ρ σ, ∑ i, σ (b i) • ρ (a i) v = ((discr E : ℤ) : R) • v := by
  obtain ⟨n, a, b, hsum, hm⟩ := exists_sep_element E
  refine ⟨n, a, b, fun R _ V _ _ ρ σ => ⟨fun v => ?_, fun v hv => ?_⟩⟩
  · rw [eigSp, Submodule.mem_iInf]
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply]
    obtain ⟨m, hma, hmb⟩ := hm x
    have L : ∀ i, ρ x (ρ (a i) v) = ∑ j, (m i j : R) • ρ (a j) v := fun i => by

      rw [← Module.End.mul_apply, ← map_mul, hma i, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
        Int.cast_smul_eq_zsmul]
    have Rr : ∀ j, σ x * σ (b j) = ∑ i, (m i j : R) * σ (b i) := fun j => by

      rw [← map_mul, hmb j, map_sum]
      simp [map_mul, map_intCast]

    rw [map_sum, Finset.smul_sum]
    simp only [map_smul, L, Finset.smul_sum, smul_smul, Rr, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · have hv' : ∀ x, ρ x v = σ x • v := by
      intro x
      rw [eigSp, Submodule.mem_iInf] at hv
      have h := hv x
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    simp only [hv', smul_smul, ← Finset.sum_smul]
    congr 1

    rw [← map_intCast σ, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Sandwich.Sep
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RegAtRing

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def stalkEquiv (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ hab => h.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem genMap_germ (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U) (hg : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg s) := by
  obtain ⟨q, hq⟩ := p
  have e := congrArg (fun f => (f ≫ Scheme.stalkClosedPointTo ξ).hom s)
    (X.presheaf.germ_stalkSpecializes hp hq)
  simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  exact e

theorem exists_div (h : IsCptGen ξ) (p : Cpt ξ) (z : Ω) :
    ∃ a b : regAt ξ p, z = (a : Ω) / (b : Ω) := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (show p.1 ∈ (⊤ : X.Opens) from trivial)
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨t, rfl⟩ := h.bij.2 z
  change X.presheaf.stalk (genPt ξ) at t
  let x : U := ⟨genPt ξ, hgU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (x : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have : IsLocalization.AtPrime (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf x).asIdeal.primeCompl
    (S := X.presheaf.stalk (x : X)) t
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (x : X)) a s
  simp only at hs
  rw [hs] at hspec
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) (s : Γ(X, U))) :=
    IsLocalization.map_units _ s
  have hne : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) (s : Γ(X, U))) ≠ 0 :=
    (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨genMap ξ p (X.presheaf.germ U p.1 hpU a), ⟨_, rfl⟩⟩,
    ⟨genMap ξ p (X.presheaf.germ U p.1 hpU (s : Γ(X, U))), ⟨_, rfl⟩⟩, ?_⟩
  simp only [genMap_germ p U hpU hgU]
  have hspec' : t * X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U)) = X.presheaf.germ U (genPt ξ) hgU a := hspec
  have hne' : ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U))) : Ω) ≠ 0 := hne
  have key : (Scheme.stalkClosedPointTo ξ).hom t *
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U))) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU a) := by
    rw [← congrArg (Scheme.stalkClosedPointTo ξ).hom hspec']
    exact (map_mul _ _ _).symm
  exact (eq_div_iff hne').2 key

theorem regAt_ring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  intro X Ω _ ξ h p
  refine ⟨?_, fun _ => isNoetherianRing_of_ringEquiv _ (stalkEquiv h p),
    fun _ => IsIntegrallyClosed.of_equiv (stalkEquiv h p)⟩
  haveI : FaithfulSMul (regAt ξ p) Ω :=
    (faithfulSMul_iff_algebraMap_injective (regAt ξ p) Ω).2 Subtype.val_injective
  exact IsFractionRing.of_field (regAt ξ p) Ω fun z => exists_div h p z

end GlobalTheory.CompanionTheory.Ar.RegAtRing
end
end
