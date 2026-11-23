module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem genericBaseChange_ringHom_eq {R : Type} [CommRing R] [IsDomain R]
    {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R'] {B : Type} [CommRing B]
    (i : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R')
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (hj : Function.Injective j) (hji : j.comp i = algebraMap R _)
    (hj'i : j'.comp i = (algebraMap R' _).comp (algebraMap R R')) :
    j' = κ.comp j := by
  ext b
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) (j b)
  have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
    simpa using IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing R) hs
  have e1 : algebraMap R (FractionRing R) s * j b = algebraMap R (FractionRing R) r := by
    rw [← hrs]; field_simp
  have hjs : ∀ x : R, j (i x) = algebraMap R (FractionRing R) x := fun x =>
    RingHom.congr_fun hji x
  have e2 : i s * b = i r := by
    apply hj
    rw [map_mul, hjs, hjs, e1]
  have hj's : ∀ x : R, j' (i x) = κ (algebraMap R (FractionRing R) x) := fun x =>
    (RingHom.congr_fun hj'i x).trans (RingHom.congr_fun hκ x).symm
  have e3 : κ (algebraMap R (FractionRing R) s) * j' b = κ (algebraMap R (FractionRing R) r) := by
    rw [← hj's, ← hj's, ← map_mul, e2]
  have e4 : κ (algebraMap R (FractionRing R) s) * κ (j b) = κ (algebraMap R (FractionRing R) r) := by
    rw [← map_mul, e1]
  have hκs : κ (algebraMap R (FractionRing R) s) ≠ 0 := by
    simpa using hs0
  exact mul_left_cancel₀ hκs (e3.trans e4.symm)

theorem genericPoint_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ t, (Γ'.pt t).left ≫ F = Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ t
  obtain ⟨B, _, i, j, j', σ, hj, hji, hj'i, -, hσ, hσ'⟩ := hF.pts
  have hjj : j' = κ.comp j := genericBaseChange_ringHom_eq i j j' κ hκ hj hji hj'i
  rw [← hσ' t, ← hσ t, hjj, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

theorem unitAt_iff_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ u, IsUnit u ∧ genMap ξ p u = a := by
  constructor
  · rintro ⟨h0, ⟨u, rfl⟩, ⟨v, hv⟩⟩
    refine ⟨u, IsUnit.of_mul_eq_one v (h.inj p ?_), rfl⟩
    rw [map_mul, hv, map_one, mul_inv_cancel₀ h0]
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(w⁻¹ : _ˣ), ?_⟩⟩
    exact map_units_inv _ w

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TanLift

theorem comp_one_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact MonObj.comp_one u

theorem comp_mul_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    u ≫ (a * b) = (u ≫ a) * (u ≫ b) := by
  exact MonObj.comp_mul u a b

theorem comp_pow_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a : X ⟶ M) (n : ℕ) :
    u ≫ a ^ n = (u ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_mul_over, ih]

section

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

theorem pt_zero (M : LieModel G x L) : M.pt 0 = 1 := by
  have h : M.pt 0 * M.pt 0 = M.pt 0 := by rw [← M.5, add_zero]
  exact mul_eq_left.mp h

theorem pt_nsmul (M : LieModel G x L) (e : L) (n : ℕ) : M.pt (n • e) = M.pt e ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_zero]
  | succ n ih => rw [succ_nsmul, M.5, ih, pow_succ]

theorem dualMap_epsMul (I : Ideal R) (c : R) (hc : Ideal.Quotient.mk I c = 0) :
    (dualMap (Ideal.Quotient.mk I)).comp (epsMul c) =
      ((algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I)).comp
        (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, hc]

theorem dualMap_algebraMap (I : Ideal R) :
    (dualMap (Ideal.Quotient.mk I)).comp (algebraMap R (DualNumber R)) =
      (algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end

theorem tangent_mod_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L), ∃! (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M e
  obtain ⟨-, -, hinj, htors⟩ := hi
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
      (Ideal.Quotient.mk (Ideal.span {(N : R)})))))
  have hu : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
      (GlobalTheory.CompanionTheory.Ar.epsAt x).hom = (Over.mk (Y.hom ≫ x)).hom := by
    simp only [GlobalTheory.CompanionTheory.Ar.epsAt, Over.mk_hom, Y]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_algebraMap]
  let u : Over.mk (Y.hom ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x := Over.homMk _ hu
  let u₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : Ideal.Quotient.mk (Ideal.span {(N : R)}) (N : R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have htan : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left =
      (1 : Over.mk x ⟶ G).left := M.2 e
  have hg : (u ≫ M.pt e) ^ N = 1 := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_pow_over, ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_nsmul, ← Nat.cast_smul_eq_nsmul R,
      ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u₀]
    apply Over.OverMorphism.ext
    have e₁ : (u ≫ M.pt ((N : R) • e)).left =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (N : R))) ≫ (M.pt e).left := by
      rw [Over.comp_left, M.6]
      rfl
    have e₂ : (u₀ ≫ (1 : Over.mk x ⟶ G)).left =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
            (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left := by
      rw [Over.comp_left, htan]
      rfl
    rw [e₁, e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_epsMul _ _ hN]
  obtain ⟨y, hy⟩ := (htors Y (u ≫ M.pt e)).1 hg
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · rw [hy]
    rfl
  · rintro v ⟨hv₁, hv₂⟩
    have hv : Over.homMk (U := Y) (V := Γ.G) v hv₁ = y := by
      refine hinj Y _ y ?_
      change v ≫ i = _
      rw [hv₂, hy]
      rfl
    calc v = (Over.homMk (U := Y) (V := Γ.G) v hv₁).left := rfl
      _ = y.left := by rw [hv]

end GlobalTheory.CompanionTheory.Ar.BT.TanLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isClosedImmersion_torsion_lift {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom]
    (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left)
    (h : Γ.IsTorsionAlong G x N i) :
    IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  obtain ⟨i', hi'⟩ : ∃ i' : Γ.G.left ⟶ pullback G.hom x, i' = pullback.lift i Γ.G.hom h.isOver :=
    ⟨_, rfl⟩
  rw [← hi']
  have i'fst : i' ≫ pullback.fst G.hom x = i := by rw [hi']; exact pullback.lift_fst _ _ _
  have i'snd : i' ≫ pullback.snd G.hom x = Γ.G.hom := by
    rw [hi']
    exact pullback.lift_snd _ _ _
  let PO : Over X := Over.mk (pullback.snd G.hom x ≫ x)
  let u : PO ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  obtain ⟨f, hfdef⟩ : ∃ f : pullback G.hom x ⟶ G.left, f = (u ^ N).left := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : pullback G.hom x ⟶ G.left, g = (1 : PO ⟶ G).left := ⟨_, rfl⟩
  have hf : f ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hfdef]; exact Over.w (u ^ N)
  have hg : g ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hgdef]; exact Over.w (1 : PO ⟶ G)
  have hfg : f ≫ G.hom = g ≫ G.hom := hf.trans hg.symm

  let jq : pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) ⟶ pullback G.hom x :=
    pullback.snd _ _
  haveI : IsClosedImmersion jq := inferInstance
  have l1 : pullback.lift f g hfg ≫ pullback.fst G.hom G.hom = f := pullback.lift_fst _ _ _
  have l2 : pullback.lift f g hfg ≫ pullback.snd G.hom G.hom = g := pullback.lift_snd _ _ _
  have cond := pullback.condition (f := pullback.diagonal G.hom) (g := pullback.lift f g hfg)
  have jqf : jq ≫ f = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.fst G.hom G.hom) cond
    simpa [jq, l1] using this.symm
  have jqg : jq ≫ g = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.snd G.hom G.hom) cond
    simpa [jq, l2] using this.symm
  have jqeq : jq ≫ f = jq ≫ g := jqf.trans jqg.symm

  have key : i' ≫ f = i' ≫ g := by
    let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
    have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
    let ψ : Over.mk (Γ.G.hom ≫ x) ⟶ PO :=
      Over.homMk i' (by simp [PO, reassoc_of% i'snd])
    have h1 : ψ ≫ u = g₀ := by
      ext1
      simpa [ψ, u, g₀] using i'fst
    have h2 : ψ ≫ u ^ N = ψ ≫ 1 := by rw [MonObj.comp_pow, h1, h0, MonObj.comp_one]
    have h3 : i' ≫ (u ^ N).left = i' ≫ (1 : PO ⟶ G).left := congrArg (fun m => m.left) h2
    rw [hfdef, hgdef]
    exact h3
  let b : Γ.G.left ⟶ pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) :=
    pullback.lift (i' ≫ f) i' (by
      apply pullback.hom_ext
      · simp [l1]
      · simp [l2, key])
  have bjq : b ≫ jq = i' := pullback.lift_snd _ _ _

  let Qs : Over (Spec (CommRingCat.of R)) := Over.mk (jq ≫ pullback.snd G.hom x)
  let g' : Over.mk (Qs.hom ≫ x) ⟶ G := Over.homMk (jq ≫ pullback.fst G.hom x)
    (by simp [Qs, pullback.condition])
  have hg' : g' ^ N = 1 := by
    let φ : Over.mk (Qs.hom ≫ x) ⟶ PO := Over.homMk jq (by simp [PO, Qs])
    have h1 : φ ≫ u = g' := by
      ext1
      simp [φ, u, g']
    have h2 : φ ≫ u ^ N = φ ≫ 1 := by
      apply Over.OverMorphism.ext
      change jq ≫ (u ^ N).left = jq ≫ (1 : PO ⟶ G).left
      rw [← hfdef, ← hgdef]
      exact jqeq
    rw [← h1, ← MonObj.comp_pow, h2, MonObj.comp_one]
  obtain ⟨y, hy⟩ := (h.kernel Qs g').1 hg'
  have hyl : y.left ≫ i = jq ≫ pullback.fst G.hom x := hy
  have hys : y.left ≫ Γ.G.hom = jq ≫ pullback.snd G.hom x := Over.w y
  have yi' : y.left ≫ i' = jq := by
    apply pullback.hom_ext
    · simp [i'fst, hyl]
    · simp [i'snd, hys]
  have ab : y.left ≫ b = 𝟙 _ := by
    rw [← cancel_mono jq]
    simp [bjq, yi']
  have ba : b ≫ y.left = 𝟙 _ := by
    have e : (Over.homMk (b ≫ y.left) (by
        change (b ≫ y.left) ≫ Γ.G.hom = Γ.G.hom
        rw [Category.assoc, hys, ← Category.assoc, bjq, i'snd]) : Γ.G ⟶ Γ.G) = 𝟙 Γ.G := by
      apply h.inj Γ.G
      change (b ≫ y.left) ≫ i = 𝟙 _ ≫ i
      rw [Category.assoc, hyl, ← Category.assoc, bjq, i'fst, Category.id_comp]
    exact congrArg (fun m => m.left) e
  haveI : IsIso b := ⟨y.left, ba, ab⟩
  rw [← bjq]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.BT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_existsUnique_equiv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  intro S G _ R _ x E E' _ _ _ _ M M'

  choose f hf using fun e => M'.onto (M.pt e) (M.tan e)
  choose g hg using fun e' => M.onto (M'.pt e') (M'.tan e')
  let φ : E ≃ₗ[R] E' :=
    { toFun := f
      invFun := g
      map_add' := fun e e' => M'.inj (by rw [M'.add, hf, hf, hf, M.add])
      map_smul' := fun c e => by
        show f (c • e) = c • f e
        apply M'.inj
        apply Over.OverMorphism.ext
        rw [M'.smul, hf, hf, M.smul]
      left_inv := fun e => M.inj (by rw [hg, hf])
      right_inv := fun e' => M'.inj (by rw [hf, hg]) }
  refine ⟨φ, fun e => hf e, fun ψ hψ => ?_⟩
  exact LinearEquiv.ext fun e => M'.inj ((hψ e).trans (hf e).symm)

end GlobalTheory.CompanionTheory.Ar
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem _root_.GlobalTheory.T.btOrder_comap_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (T' : Type) [CommGroup T'] [Finite T'] (Γ' : QFGroup R T') (a : Γ.G ⟶ Γ'.G) (α : T →* T'), (∀ t, Γ.pt t ≫ a = Γ'.pt (α t)) → ∀ f ∈ Γ'.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤ := by
  intro R _ _ T _ _ Γ T' _ _ Γ' a α ha f hf
  let Φ : (T' → R) →ₐ[R] (T → R) :=
    { toFun := fun f t => f (α t)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hle : Γ'.btOrder ⊤ ≤ (Γ.btOrder ⊤).comap Φ := by
    refine Algebra.adjoin_le fun f hf => ?_
    refine Algebra.subset_adjoin fun t g _ => ?_
    obtain ⟨U, hU, s, hs⟩ := hf (α t) (a.left g) trivial
    refine ⟨a.left ⁻¹ᵁ U, hU, (a.left.app U).hom s, fun x h => ?_⟩
    have hx : (Γ.pt x).left ≫ a.left = (Γ'.pt (α x)).left := by
      rw [← ha x, Over.comp_left]
    have h' : ⊤ ≤ (Γ'.pt (α x)).left ⁻¹ᵁ U := by
      rw [← hx]
      exact h
    have hval : valAt (Γ.pt x).left (a.left ⁻¹ᵁ U) h ((a.left.app U).hom s) =
        valAt (Γ'.pt (α x)).left U h' s := by
      simp only [valAt, ← hx, Scheme.Hom.comp_appLE]
      rfl
    change valAt (Γ.pt x).left (a.left ⁻¹ᵁ U) h ((a.left.app U).hom s) =
      algebraMap R (FractionRing R) (f (α (t * x)))
    rw [hval, map_mul]
    exact hs (α x) h'
  exact hle hf
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.OrVert

def DomBy {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (W : Subring Ω') (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) : Prop :=
  (∀ a ∈ regAt ξ q, i a ∈ W) ∧ ∀ a ∈ regAt ξ q, a ≠ 0 → (i a)⁻¹ ∈ W → a⁻¹ ∈ regAt ξ q

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem eigSp_comp_ringEquiv : ∀ (R E O : Type) [CommRing R] [AddCommGroup E] [Module R E] [CommRing O] (ρ : O →+* Module.End R E) (s : O ≃+* O) (τ : O →+* R), eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ := by
  intro R E O _ _ _ _ ρ s τ
  unfold eigSp
  exact s.surjective.iInf_comp (fun b => LinearMap.ker (ρ b - τ b • LinearMap.id))

end GlobalTheory.CompanionTheory.Ar
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem IsTanAt.comp_monHom {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G') [IsMonHom f] :
    IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem lieModel_exists_unique_diff :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R]
      (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E']
      [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f],
      ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  intro S G G' _ _ R _ x E E' _ _ _ _ M M' f _
  have hex : ∀ e, ∃ e', M'.pt e' = M.pt e ≫ f := fun e => M'.onto _ ((M.tan e).comp_monHom f)
  choose A hA using hex
  have hadd : ∀ e₁ e₂, A (e₁ + e₂) = A e₁ + A e₂ := fun e₁ e₂ => M'.inj (by
    rw [hA, M'.add, hA, hA, M.add, MonObj.mul_comp])
  have hsmul : ∀ (c : R) e, A (c • e) = c • A e := fun c e => M'.inj (by
    rw [hA]
    apply Over.OverMorphism.ext
    rw [M'.smul, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc])
  refine ⟨⟨⟨A, hadd⟩, hsmul⟩, fun e => hA e, ?_⟩
  intro B hB
  ext e
  exact M'.inj ((hB e).trans (hA e).symm)

end GlobalTheory.CompanionTheory.Ar
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled

theorem pow_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  intro R _ _ T _ Γ S G _ x N i h t
  let lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun y =>
    Over.homMk (y.left ≫ i) (by
      have w := Over.w y
      simp only [Over.mk_hom, Category.assoc, h.isOver]
      rw [← Category.assoc, w]
      rfl)
  have lift_left : ∀ y, (lift y).left = y.left ≫ i := fun y => rfl
  have lift_mul : ∀ y z, lift (y * z) = lift y * lift z := fun y z => by
    ext1
    rw [h.mul (genPt R) y z (lift y) (lift z) rfl rfl]
    rfl
  have lift_one : lift 1 = 1 := by
    have e : lift 1 * lift 1 = lift 1 := by rw [← lift_mul, _root_.mul_one]
    exact mul_eq_left.mp e
  let L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) :=
    { toFun := lift, map_one' := lift_one, map_mul' := lift_mul }
  have hk : lift (Γ.pt t) ^ N = 1 := (h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩
  have hL : L (Γ.pt t ^ N) = L 1 := by
    rw [map_pow, map_one]
    exact hk
  have hy : Γ.pt t ^ N = 1 := h.inj (genPt R) _ _ (by
    have := congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL
    exact this)
  have hp : Γ.pt (t ^ N) = Γ.pt 1 := by rw [map_pow, map_one, hy]
  let c : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  exact Γ.pt_inj (t ^ N) 1 c c (by rw [hp])

end GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled
end
end
