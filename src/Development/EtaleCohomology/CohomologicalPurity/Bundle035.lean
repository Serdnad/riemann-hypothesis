module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle030
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
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
import Mathlib.Tactic.Basify
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Thom
namespace RepPt

def specEq (U : Scheme.{0}) (B : Type) [CommRing B] : (CommRingCat.of B ⟶ Γ(U, ⊤)) ≃ (U ⟶ Spec (CommRingCat.of B)) where
  toFun φ := ΓSpec.adjunction.homEquiv U (op (CommRingCat.of B)) φ.op
  invFun f := (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop
  left_inv φ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  right_inv f := by
    refine ext_to_Spec ?_
    simp only [Scheme.Γ_map, Quiver.Hom.unop_op]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

theorem specEq_symm_apply (U : Scheme.{0}) (B : Type) [CommRing B] (f : U ⟶ Spec (CommRingCat.of B)) :
    (specEq U B).symm f = (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f.appTop := rfl

theorem appTop_specEq (U : Scheme.{0}) (B : Type) [CommRing B] (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specEq U B φ).appTop = φ :=
  (specEq U B).left_inv φ

theorem symm_comp {V U : Scheme.{0}} (B : Type) [CommRing B] (f : V ⟶ U) (g : U ⟶ Spec (CommRingCat.of B)) :
    (specEq V B).symm (f ≫ g) = (specEq U B).symm g ≫ f.appTop := by
  simp only [specEq_symm_apply, Scheme.Hom.comp_appTop, Category.assoc]

theorem comp_specEq {V U : Scheme.{0}} (B : Type) [CommRing B] (f : V ⟶ U) (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) :
    f ≫ specEq U B φ = specEq V B (φ ≫ f.appTop) := by
  apply (specEq V B).symm.injective
  rw [symm_comp, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem specEq_comp_Spec (U : Scheme.{0}) {B C : Type} [CommRing B] [CommRing C]
    (ψ : CommRingCat.of B ⟶ CommRingCat.of C) (φ : CommRingCat.of C ⟶ Γ(U, ⊤)) :
    specEq U C φ ≫ Spec.map ψ = specEq U B (ψ ≫ φ) := by
  apply (specEq U B).symm.injective
  rw [Equiv.symm_apply_apply, specEq_symm_apply, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, appTop_specEq]

theorem mem_basicOpen_specEq (U : Scheme.{0}) (B : Type) [CommRing B] (φ : CommRingCat.of B ⟶ Γ(U, ⊤)) (b : B)
    (x : U) : (specEq U B φ x : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen b ↔ x ∈ U.basicOpen (φ b) := by
  have h := Scheme.preimage_basicOpen_top (specEq U B φ) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  rw [basicOpen_eq_of_affine] at h
  have h2 : (specEq U B φ).appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) = φ b := by
    calc _ = ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specEq U B φ).appTop) b := rfl
      _ = φ b := by rw [appTop_specEq]
  rw [h2] at h
  rw [← h]
  rfl

theorem mem_off_iff {B : Type} [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B) (hJ : J = Ideal.span (Set.range S))
    (x : PrimeSpectrum B) : x ∈ off B J ↔ ∃ i, x ∈ PrimeSpectrum.basicOpen (S i) := by
  subst hJ
  change x ∉ PrimeSpectrum.zeroLocus _ ↔ _
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le, Set.range_subset_iff,
    PrimeSpectrum.mem_basicOpen, SetLike.mem_coe, not_forall]

theorem range_sub (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S))
    (φ : {φ : CommRingCat.of B ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (S i))}) :
    Set.range (specEq U B φ.1) ⊆ Set.range (off B J).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨p, rfl⟩
  obtain ⟨i, hi⟩ := φ.2 p
  exact (mem_off_iff S J hJ _).2 ⟨i, (mem_basicOpen_specEq U B φ.1 _ p).2 hi⟩

def offEq (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) :
    (U ⟶ (off B J).toScheme) ≃ {φ : CommRingCat.of B ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (S i))} where
  toFun h := ⟨(specEq U B).symm (h ≫ (off B J).ι), fun p => by
    have hp' : (h ≫ (off B J).ι) p ∈ Set.range (off B J).ι := ⟨h p, rfl⟩
    have hp : (h ≫ (off B J).ι) p ∈ off B J := by rwa [Scheme.Opens.range_ι] at hp'
    obtain ⟨i, hi⟩ := (mem_off_iff S J hJ _).1 hp
    refine ⟨i, ?_⟩
    rw [← mem_basicOpen_specEq, Equiv.apply_symm_apply]
    exact hi⟩
  invFun φ := IsOpenImmersion.lift (off B J).ι (specEq U B φ.1) (range_sub U B S J hJ φ)
  left_inv h := by
    apply (cancel_mono (off B J).ι).1
    dsimp only
    rw [IsOpenImmersion.lift_fac, Equiv.apply_symm_apply]
  right_inv φ := Subtype.ext (by
    dsimp only
    rw [IsOpenImmersion.lift_fac (off B J).ι (specEq U B φ.1) (range_sub U B S J hJ φ), Equiv.symm_apply_apply])

theorem offEq_symm_ι (U : Scheme.{0}) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) φ :
    (offEq U B S J hJ).symm φ ≫ (off B J).ι = specEq U B φ.1 := IsOpenImmersion.lift_fac _ _ _

theorem comp_offEq_symm {V U : Scheme.{0}} (f : V ⟶ U) (B : Type) [CommRing B] {ι : Type} (S : ι → B) (J : Ideal B)
    (hJ : J = Ideal.span (Set.range S)) φ ψ (h : ψ.1 = φ.1 ≫ f.appTop) :
    f ≫ (offEq U B S J hJ).symm φ = (offEq V B S J hJ).symm ψ := by
  rw [← cancel_mono (off B J).ι, Category.assoc, offEq_symm_ι, offEq_symm_ι, comp_specEq, h]


open MvPolynomial in
def e₂ (d : ℕ) (R : Type) [CommRing R] (U : Scheme.{0}) : Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃
    {φ : CommRingCat.of (MvPolynomial (Fin d) R) ⟶ Γ(U, ⊤) // ∀ p : U, ∃ i, p ∈ U.basicOpen (φ (X i))} where
  toFun vg := ⟨CommRingCat.ofHom (eval₂Hom ((specEq U R).symm vg.2).hom vg.1.1), fun p => by
    obtain ⟨i, -, hi⟩ := vg.1.2 p
    exact ⟨i, by simpa using hi⟩⟩
  invFun φ := (⟨fun i => φ.1 (X i), fun p => (φ.2 p).imp fun _ h => ⟨Nat.zero_le _, h⟩⟩,
    specEq U R (CommRingCat.ofHom C ≫ φ.1))
  left_inv vg := by
    obtain ⟨v, g⟩ := vg
    refine Prod.ext (Subtype.ext (funext fun i => by simp)) ?_
    dsimp only
    conv_rhs => rw [← (specEq U R).apply_symm_apply g]
    congr 1
    ext r
    simp
  right_inv φ := by
    apply Subtype.ext
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp


open MvPolynomial in
def e₁ (d : ℕ) (R : Type) [CommRing R] (U : Scheme.{0}) : Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
    {φ : CommRingCat.of (Polynomial (MvPolynomial (Fin d) R)) ⟶ Γ(U, ⊤) //
      ∀ p : U, ∃ j, p ∈ U.basicOpen (φ (Polynomial.C (X j)))} where
  toFun vg := ⟨CommRingCat.ofHom (Polynomial.eval₂RingHom
      (eval₂Hom ((specEq U R).symm vg.2).hom (fun j => vg.1.1 j.succ)) (vg.1.1 0)), fun p => by
    obtain ⟨i, hi, hp⟩ := vg.1.2 p
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (show i ≠ 0 by rintro rfl; simp at hi)
    exact ⟨j, by simpa using hp⟩⟩
  invFun φ := (⟨(Fin.cons (φ.1 Polynomial.X) (fun j => φ.1 (Polynomial.C (X j))) : Fin (d + 1) → Γ(U, ⊤)),
      fun p => by
        obtain ⟨j, hj⟩ := φ.2 p
        exact ⟨j.succ, by simp, by simpa using hj⟩⟩,
    specEq U R (CommRingCat.ofHom (Polynomial.C.comp C) ≫ φ.1))
  left_inv vg := by
    obtain ⟨v, g⟩ := vg
    refine Prod.ext (Subtype.ext (funext fun i => Fin.cases (by simp) (fun j => by simp) i)) ?_
    dsimp only
    conv_rhs => rw [← (specEq U R).apply_symm_apply g]
    congr 1
    ext r
    simp
  right_inv φ := by
    apply Subtype.ext
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp
    · simp

theorem hJ (d : ℕ) (R : Type) [CommRing R] :
    (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) R))).map Polynomial.C =
      Ideal.span (Set.range fun j => (Polynomial.C (MvPolynomial.X j) : Polynomial (MvPolynomial (Fin d) R))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

end RepPt


open RepPt in
theorem LeafRepPt_of : LeafRepPt := by
  intro d R _
  refine ⟨MvPolynomial (Fin d) R, inferInstance, Ideal.span (Set.range MvPolynomial.X), MvPolynomial.C,
    Submodule.fg_span (Set.finite_range _), off_le_C _ _,
    fun U => (e₁ d R U).trans (offEq U _ _ _ (hJ d R)).symm,
    fun U => (e₂ d R U).trans (offEq U _ _ _ rfl).symm, ?_, ?_, ?_⟩
  · intro V U f v g
    refine (comp_offEq_symm f _ _ _ (hJ d R) _ _ ?_).symm
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [e₁, symm_comp]
      · intro i; simp [e₁, Vec.map]
    · simp [e₁, Vec.map]
  · intro V U f v g
    refine (comp_offEq_symm f _ _ _ rfl _ _ ?_).symm
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e₂, symm_comp]
    · intro i; simp [e₂, Vec.map]
  · intro U v g
    rw [← cancel_mono (off _ _).ι, Category.assoc, Scheme.Hom.resLE_comp_ι]
    simp only [Equiv.trans_apply]
    rw [offEq_symm_ι, ← Category.assoc, offEq_symm_ι, specEq_comp_Spec]
    congr 1
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro r; simp [e₁, e₂]
    · intro i; simp [e₁, e₂, Vec.tail]

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vec.smul' {N k : ℕ} {U : Scheme.{0}} (c : (Γ(U, ⊤))ˣ) (v : Vec N k U) : Vec N k U :=
  ⟨fun i => (c : Γ(U, ⊤)) * v.1 i, fun p => by
    obtain ⟨i, hi, hp⟩ := v.2 p
    refine ⟨i, hi, ?_⟩
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit (X := U) c.isUnit]
    exact ⟨trivial, hp⟩⟩

def tprod {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) (i : Fin (m + 1)) : Rˣ :=
  ∏ j : Fin m, if i.val ≤ j.val then u j else 1

theorem tprod_castSucc {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) (i : Fin m) :
    tprod u i.castSucc = u i * tprod u i.succ := by
  unfold tprod
  have h : ∀ j : Fin m, (if i.castSucc.val ≤ j.val then u j else 1) =
      (if j = i then u i else 1) * (if i.succ.val ≤ j.val then u j else 1) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · have : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp only [Fin.val_castSucc, Fin.val_succ, hj, if_false, one_mul]
      by_cases h1 : i.val ≤ j.val
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem tprod_last {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) : tprod u (Fin.last m) = 1 := by
  unfold tprod
  apply Finset.prod_eq_one
  intro j _
  simp

def vert (N k : ℕ) (n : SimplexCategoryᵒᵖ) : (Pj N k).obj n ⟶ (Pj N k).obj (op (SimplexCategory.mk 0)) :=
  (Pj N k).map (SimplexCategory.const (SimplexCategory.mk 0) n.unop (Fin.last _)).op

def utsT (N k : ℕ) (n : SimplexCategoryᵒᵖ) : (Pj N k).obj n ⟶ Uts n.unop.len where
  app U := TypeCat.ofHom fun x i =>
    ((x : ComposableArrows (Vec N k U.unop) n.unop.len).map' i.val (i.val + 1)).1
  naturality U V f := rfl

def phi (N k : ℕ) (n : SimplexCategoryᵒᵖ) :
    (Pj N k).obj n ⟶ FunctorToTypes.prod ((Pj N k).obj (op (SimplexCategory.mk 0))) (Uts n.unop.len) :=
  FunctorToTypes.prod.lift (vert N k n) (utsT N k n)

theorem chain_ext {N k : ℕ} {U : Scheme.{0}} {m : ℕ} (x y : ComposableArrows (Vec N k U) m)
    (h0 : x.obj (Fin.last m) = y.obj (Fin.last m))
    (hu : ∀ i : Fin m, (x.map' i.val (i.val + 1)).1 = (y.map' i.val (i.val + 1)).1) : x = y := by
  have hobj : ∀ t : ℕ, ∀ i : Fin (m + 1), i.val + t = m → x.obj i = y.obj i := by
    intro t
    induction t with
    | zero =>
      intro i hi
      have : i = Fin.last m := Fin.ext (by simp; omega)
      subst this; exact h0
    | succ t ih =>
      intro i hi
      have hlt : i.val < m := by omega
      have e := ih ⟨i.val + 1, by omega⟩ (by simp; omega)
      apply Subtype.ext; funext j
      have hx := (x.map' i.val (i.val + 1)).2 j
      have hy := (y.map' i.val (i.val + 1)).2 j
      have hu' := hu ⟨i.val, hlt⟩
      change (x.obj i).1 j = (y.obj i).1 j
      erw [hx, hy, hu', e]
  exact ComposableArrows.ext (fun i => hobj (m - i.val) i (by omega))
    (fun i hi => (Vec.hom_subsingleton N k U _ _).elim _ _)

theorem smul'_one {N k : ℕ} {U : Scheme.{0}} (v : Vec N k U) : Vec.smul' 1 v = v := by
  apply Subtype.ext; funext i; simp [Vec.smul']

theorem phi_bij (N k : ℕ) (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}ᵒᵖ) :
    Function.Bijective ((phi N k n).app U) := by
  constructor
  · intro x y hxy
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    apply chain_ext (U := U.unop) x y
    · exact congrArg (fun z : ComposableArrows (Vec N k U.unop) 0 => z.obj 0) h1
    · intro i; exact congrFun h2 i
  · rintro ⟨w, u0⟩
    let u : Fin n.unop.len → (Γ(U.unop, ⊤))ˣ := u0
    let obj : Fin (n.unop.len + 1) → Vec N k U.unop := fun i => Vec.smul' (tprod u i) (w.obj 0)
    let ms : ∀ i : Fin n.unop.len, obj i.castSucc ⟶ obj i.succ := fun i => ⟨u i, fun j => by
      dsimp only [obj, Vec.smul']
      rw [show tprod u i.castSucc = u i * tprod u i.succ from tprod_castSucc u i, Units.val_mul, mul_assoc]⟩
    refine ⟨ComposableArrows.mkOfObjOfMapSucc obj ms, ?_⟩
    apply Prod.ext
    · apply ComposableArrows.ext₀
      change obj (Fin.last _) = w.obj 0
      exact (congrArg (fun c => Vec.smul' c (w.obj 0)) (tprod_last u)).trans (smul'_one _)
    · funext i
      exact congrArg Subtype.val (ComposableArrows.mkOfObjOfMapSucc_map_succ obj ms i.val i.isLt)

instance isIso_phi (N k : ℕ) (n : SimplexCategoryᵒᵖ) : IsIso (phi N k n) := by
  have : ∀ U, IsIso ((phi N k n).app U) := fun U => (isIso_iff_bijective _).2 (phi_bij N k n U)
  exact NatIso.isIso_of_isIso_app _

theorem LeafNerveSplit_of : LeafNerveSplit := by
  intro d n
  refine ⟨asIso (phi (d + 1) 1 n) ≪≫ (FunctorToTypes.binaryProductIso _ _).symm,
    asIso (phi d 0 n) ≪≫ (FunctorToTypes.binaryProductIso _ _).symm, ?_⟩
  apply prod.hom_ext
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, prod.map_fst,
      reassoc_of% FunctorToTypes.binaryProductIso_inv_comp_fst, FunctorToTypes.binaryProductIso_inv_comp_fst]
    simp only [phi, reassoc_of% FunctorToTypes.prod.lift_fst, FunctorToTypes.prod.lift_fst]
    exact ((Pj.tail d).naturality _).symm
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, prod.map_snd, Category.comp_id, FunctorToTypes.binaryProductIso_inv_comp_snd]
    simp only [phi, FunctorToTypes.prod.lift_snd]
    rfl

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Thom.UnitsRepPf

variable (R : Type) [CommRing R] (m : ℕ)

abbrev P := MvPolynomial (Fin m) R
abbrev f : P R m := ∏ i, MvPolynomial.X i
abbrev R' := Localization.Away (f R m)

def ι : R →+* R' R m := (algebraMap (P R m) (R' R m)).comp MvPolynomial.C

variable {R m}

theorem hunit {B : Type} [CommRing B] (ψ : R' R m →+* B) (i : Fin m) :
    IsUnit (ψ (algebraMap (P R m) (R' R m) (MvPolynomial.X i))) :=
  isUnit_of_dvd_unit (map_dvd ψ (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))))
    ((IsLocalization.Away.algebraMap_isUnit (f R m)).map ψ)

def Φ {B : Type} [CommRing B] (ψ : R' R m →+* B) : (Fin m → Bˣ) × (R →+* B) :=
  (fun i => (hunit ψ i).unit, ψ.comp (ι R m))

theorem Φ_inj {B : Type} [CommRing B] : Function.Injective (Φ (R := R) (m := m) (B := B)) := by
  intro ψ₁ ψ₂ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply IsLocalization.ringHom_ext (Submonoid.powers (f R m))
  apply MvPolynomial.ringHom_ext
  · intro r
    exact RingHom.congr_fun h2 r
  · intro i
    have := congrArg (fun u => ((u i : Bˣ) : B)) h1
    simpa [Φ] using this

theorem Φ_surj {B : Type} [CommRing B] : Function.Surjective (Φ (R := R) (m := m) (B := B)) := by
  rintro ⟨u, g⟩
  let e : P R m →+* B := MvPolynomial.eval₂Hom g (fun i => (u i : B))
  have hg : IsUnit (e (f R m)) := ⟨∏ i, u i, by simp [e, map_prod]⟩
  refine ⟨IsLocalization.Away.lift (f R m) hg, ?_⟩
  refine Prod.ext ?_ ?_
  · funext i; apply Units.ext; simp [Φ, IsLocalization.Away.lift_eq, e]
  · ext r; simp [Φ, ι, IsLocalization.Away.lift_eq, e]

def back {X : Scheme.{0}} {A : CommRingCat.{0}} (φ : X ⟶ Spec A) : A ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso A).inv ≫ φ.appTop

theorem back_inj {X : Scheme.{0}} {A : CommRingCat.{0}} : Function.Injective (back (X := X) (A := A)) := by
  intro a b h
  exact (ΓSpec.adjunction.homEquiv X (op A)).symm.injective (Opposite.unop_injective h)

theorem back_surj {X : Scheme.{0}} {A : CommRingCat.{0}} : Function.Surjective (back (X := X) (A := A)) := by
  intro φ
  exact ⟨_, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ⟩

theorem back_comp {X : Scheme.{0}} {A A' : CommRingCat.{0}} (φ : X ⟶ Spec A') (g : A ⟶ A') :
    back (φ ≫ Spec.map g) = g ≫ back φ := by
  simp only [back, Scheme.Hom.comp_appTop, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

theorem back_nat {X Y : Scheme.{0}} {A : CommRingCat.{0}} (h : Y ⟶ X) (φ : X ⟶ Spec A) :
    back (h ≫ φ) = back φ ≫ h.appTop := by
  simp [back]

theorem back_ι {X : Scheme.{0}} (φ : X ⟶ Spec (CommRingCat.of (R' R m))) :
    (back (φ ≫ Spec.map (CommRingCat.ofHom (ι R m)))).hom = (back φ).hom.comp (ι R m) := by
  rw [back_comp]; rfl

def τ : yoneda.obj (Spec (CommRingCat.of (R' R m))) ⟶
    FunctorToTypes.prod (Uts m) (yoneda.obj (Spec (CommRingCat.of R))) where
  app X := ↾fun φ => ((Φ (back φ).hom).1, φ ≫ Spec.map (CommRingCat.ofHom (ι R m)))
  naturality X Y h := by
    ext φ
    · funext i
      apply Units.ext
      change ((hunit (back (h.unop ≫ φ)).hom i).unit : Γ(Y.unop, ⊤)) =
        (Units.map ((Scheme.Hom.appTop h.unop).hom : Γ(X.unop, ⊤) →* Γ(Y.unop, ⊤))
          ((hunit (back φ).hom i).unit) : Γ(Y.unop, ⊤))
      simp only [IsUnit.unit_spec, Units.coe_map, back_nat]
      rfl
    · change (h.unop ≫ φ) ≫ Spec.map (CommRingCat.ofHom (ι R m)) =
        h.unop ≫ (φ ≫ Spec.map (CommRingCat.ofHom (ι R m)))
      rw [Category.assoc]

theorem τ_bij (X : Scheme.{0}ᵒᵖ) : Function.Bijective ((τ (R := R) (m := m)).app X) := by
  constructor
  · intro φ₁ φ₂ h
    have h1 : (Φ (back φ₁).hom).1 = (Φ (back φ₂).hom).1 := by
      have := congrArg Prod.fst h; exact this
    have h2' : φ₁ ≫ Spec.map (CommRingCat.ofHom (ι R m)) = φ₂ ≫ Spec.map (CommRingCat.ofHom (ι R m)) := by
      have := congrArg Prod.snd h; exact this
    have h2 := congrArg (fun p => (back p).hom) h2'
    simp only [back_ι] at h2
    apply back_inj
    apply CommRingCat.hom_ext
    apply Φ_inj
    exact Prod.ext h1 h2
  · rintro ⟨u, χ⟩
    obtain ⟨ψ, hψ⟩ := Φ_surj (R := R) (m := m) (B := Γ(X.unop, ⊤)) (u, (back χ).hom)
    obtain ⟨φ, hφ⟩ := back_surj (CommRingCat.ofHom ψ)
    refine ⟨φ, ?_⟩
    refine Prod.ext ?_ ?_
    · change (Φ (back φ).hom).1 = u
      rw [hφ]; exact congrArg Prod.fst hψ
    · change φ ≫ Spec.map (CommRingCat.ofHom (ι R m)) = χ
      apply back_inj
      apply CommRingCat.hom_ext
      rw [back_ι, hφ]
      exact congrArg Prod.snd hψ

instance (X : Scheme.{0}ᵒᵖ) : IsIso ((τ (R := R) (m := m)).app X) :=
  (isIso_iff_bijective _).mpr (τ_bij X)

instance : IsIso (τ (R := R) (m := m)) := NatIso.isIso_of_isIso_app _

end LateralTheory.CohomologicalPurity.Thom.UnitsRepPf

namespace LateralTheory.CohomologicalPurity.Thom
open UnitsRepPf in
theorem LeafUnitsRep_of : LeafUnitsRep := by
  intro R _ m
  exact ⟨R' R m, inferInstance, ι R m,
    ⟨FunctorToTypes.binaryProductIso _ _ ≪≫ (asIso (τ (R := R) (m := m))).symm⟩⟩

end LateralTheory.CohomologicalPurity.Thom
end
end
