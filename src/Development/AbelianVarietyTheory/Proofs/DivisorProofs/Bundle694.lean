module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Mathlib.Data.Finsupp.Notation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle241
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle661
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.UG GlobalTheory.SatakeWeyl

theorem _root_.GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by
  first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧ LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.representing_qc_qs_loft) | (exact GlobalTheory.HilbAff.representing_qc_qs_loft) | (intros; apply GlobalTheory.HilbAff.representing_qc_qs_loft <;> assumption)
end

section

open IsLocalRing Polynomial CategoryTheory Limits

namespace GlobalTheory.TorsorColimElem

theorem exists_torsor_model_of_elements : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  intro ι _ _ _ R _ f hid hcomp B _ g hcompat hsurj hinj q hq D _ _ act hT
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (R i)
      map := fun {i j} h => CommRingCat.ofHom (f i j h.le)
      map_id := fun i => by
        ext x
        simp [hid]
      map_comp := fun {i j k} a b => by
        ext x
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
          Function.comp_apply]
        exact (RingHom.congr_fun (hcomp i j k a.le b.le) x).symm }
  let c : Cocone F :=
    { pt := CommRingCat.of B
      ι := { app := fun i => CommRingCat.ofHom (g i)
             naturality := fun i j h => by
               ext x
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
                 CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, F]
               exact RingHom.congr_fun (hcompat i j h.le) x } }
  have hc : IsColimit c := by
    haveI : ReflectsColimit F (forget CommRingCat) :=
      reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat)
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf
    · intro x
      obtain ⟨i, y, hy⟩ := hsurj x
      exact ⟨i, y, hy.symm⟩
    · intro i j x y hxy
      have hxy' : g i x = g j y := hxy
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
      have h0 : g k (f i k hik x - f j k hjk y) = 0 := by
        have e1 : g k (f i k hik x) = g i x := by rw [← hcompat i k hik]; rfl
        have e2 : g k (f j k hjk y) = g j y := by rw [← hcompat j k hjk]; rfl
        rw [map_sub, e1, e2, hxy', sub_self]
      obtain ⟨l, hkl, hl⟩ := hinj k _ h0
      refine ⟨l, homOfLE (hik.trans hkl), homOfLE (hjk.trans hkl), ?_⟩
      change f i l _ x = f j l _ y
      rw [map_sub, sub_eq_zero] at hl
      rw [← hcomp i k l hik hkl, ← hcomp j k l hjk hkl]
      exact hl
  have hT' : GlobalTheory.LocAcyc.IsZModTorsor B D q act := hT
  obtain ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩ :=
    @GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit ι _ _ F c hc q hq D _ ‹Algebra B D› act hT'
  exact ⟨j, Dj, i1, i2, actj, hTj, ⟨e⟩⟩

end GlobalTheory.TorsorColimElem
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OriginResidue

theorem isSepClosed_of_ringEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] :
    IsSepClosed L := by
  refine ⟨fun p hp => ?_⟩
  have h := IsSepClosed.splits_domain (f := e.toRingHom) (p.map e.symm.toRingHom) hp.map
  rwa [Polynomial.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from by
    ext; simp, Polynomial.map_id] at h

variable {A : Type} [CommRing A] [IsLocalRing A]

def constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    A →+* (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField :=
  (algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField).comp Polynomial.C

theorem constToResidue_eq_zero [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] {a : A}
    (ha : a ∈ maximalIdeal A) : constToResidue a = 0 := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [Ideal.algebraMap_residueField_eq_zero, GlobalTheory.LocalStage.mem_originIdeal_iff]
  simpa using ha

instance [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] : IsLocalHom (constToResidue (A := A)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have := constToResidue_eq_zero ((mem_maximalIdeal a).2 h)
  rw [this] at ha
  exact not_isUnit_zero ha

theorem algebraMap_eq_constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] (f : Polynomial A) :
    algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField f =
      constToResidue (f.coeff 0) := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero,
    GlobalTheory.LocalStage.mem_originIdeal_iff]
  simp

theorem lift_surjective [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    Function.Surjective (ResidueField.lift (constToResidue (A := A))) := by
  set p := GlobalTheory.KeyOriginCut.originIdeal A
  intro x
  obtain ⟨z, rfl⟩ := residue_surjective x
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : algebraMap (Polynomial A) p.ResidueField s ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  have key : residue _ (IsLocalization.mk' (Localization.AtPrime p) f s) *
      algebraMap (Polynomial A) p.ResidueField s = algebraMap (Polynomial A) p.ResidueField f := by
    rw [IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField f,
      ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]
  refine ⟨residue A (f.coeff 0) / residue A ((s : Polynomial A).coeff 0), ?_⟩
  rw [map_div₀, ResidueField.lift_residue_apply, ResidueField.lift_residue_apply,
    ← algebraMap_eq_constToResidue, ← algebraMap_eq_constToResidue, ← key, mul_div_cancel_right₀ _ hs]

theorem residue_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  intro A _ _ _ E _ _ _ Q _ hQ y
  set p := GlobalTheory.KeyOriginCut.originIdeal A with hp
  haveI : p.IsPrime := hQ ▸ Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨hQ.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  haveI : IsSepClosed p.ResidueField := isSepClosed_of_ringEquiv
    (RingEquiv.ofBijective _ ⟨(ResidueField.lift (constToResidue (A := A))).injective, lift_surjective⟩)
  obtain ⟨x, hx⟩ := IsSepClosed.algebraMap_surjective p.ResidueField Q.ResidueField
    (residue (Localization.AtPrime Q) y)
  obtain ⟨c, rfl⟩ := lift_surjective x
  obtain ⟨c, rfl⟩ := residue_surjective c
  refine ⟨Polynomial.C c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.lift_residue_apply]
  simp only [constToResidue, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime Q) Q.ResidueField, ResidueField.algebraMap_eq, sub_self]

end GlobalTheory.OriginResidue
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_localStage_tensor_polynomial_origin : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  first | (exact @GlobalTheory.LocalStage.localStage) | (exact GlobalTheory.LocalStage.localStage) | (intros; apply GlobalTheory.LocalStage.localStage  <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyOrigin

theorem originIdeal_eq_comap (T : Type) [CommRing T] [IsLocalRing T] :
    GlobalTheory.KeyOriginCut.originIdeal T = (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
  ext g
  rw [GlobalTheory.LocalStage.mem_originIdeal_iff, Ideal.mem_comap, Polynomial.constantCoeff_apply]

theorem originIdeal_isMaximal (T : Type) [CommRing T] [IsLocalRing T] :
    (GlobalTheory.KeyOriginCut.originIdeal T).IsMaximal := by
  rw [originIdeal_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨Polynomial.C a, by simp⟩)

theorem mapRingHom_isIntegral {A S : Type} [CommRing A] [CommRing S] (f : A →+* S) (hf : f.IsIntegral) :
    (Polynomial.mapRingHom f).IsIntegral := by
  letI : Algebra (Polynomial A) (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  have hC : ∀ s : S, IsIntegral (Polynomial A) (Polynomial.C s) := by
    intro s
    obtain ⟨P, hPm, hP⟩ := hf s
    refine ⟨P.map Polynomial.C, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Polynomial A) (Polynomial S)).comp Polynomial.C = Polynomial.C.comp f := by
      refine RingHom.ext fun a => ?_
      change Polynomial.map f (Polynomial.C a) = _
      simp
    rw [hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  have hX : IsIntegral (Polynomial A) (Polynomial.X : Polynomial S) := by
    have : algebraMap (Polynomial A) (Polynomial S) Polynomial.X = Polynomial.X := Polynomial.map_X f
    rw [← this]
    exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact hp.add hq
  | monomial n a _ => exact (hC a).mul (hX.pow _)

theorem polyOrigin : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  intro A S _ _ _ _ f hf

  have hmA : (maximalIdeal S).comap f = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (maximalIdeal S)
    exact IsLocalRing.eq_maximalIdeal this
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal S).comap f := by
      rw [hmA]; exact (mem_maximalIdeal a).mpr hna
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨mapRingHom_isIntegral f hf, (originIdeal_isMaximal S).isPrime,
    GlobalTheory.LocalStage.comap_originIdeal f, ?_⟩
  intro 𝔔 h𝔔 hc
  have hXmem : (Polynomial.X : Polynomial S) ∈ 𝔔 := by
    have : (Polynomial.X : Polynomial A) ∈ 𝔔.comap (Polynomial.mapRingHom f) := by
      rw [hc, GlobalTheory.LocalStage.mem_originIdeal_iff]; simp
    simpa using this

  haveI : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsPrime := Ideal.comap_isPrime _ _
  have hcC : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).comap f = maximalIdeal A := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h1 : Polynomial.C (f a) = Polynomial.mapRingHom f (Polynomial.C a) := by simp
    rw [h1, ← Ideal.mem_comap, hc, GlobalTheory.LocalStage.mem_originIdeal_iff, Polynomial.coeff_C_zero]
  have hmax : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf _ (by rw [hcC]; infer_instance)
  have hP : 𝔔.comap (Polynomial.C : S →+* Polynomial S) = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hmax
  have hle : GlobalTheory.KeyOriginCut.originIdeal S ≤ 𝔔 := by
    intro g hg
    rw [GlobalTheory.LocalStage.mem_originIdeal_iff] at hg
    rw [← Polynomial.X_mul_divX_add g]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hXmem) ?_
    have : g.coeff 0 ∈ 𝔔.comap (Polynomial.C : S →+* Polynomial S) := by rw [hP]; exact hg
    exact this
  exact ((originIdeal_isMaximal S).eq_of_le h𝔔.ne_top hle).symm

end GlobalTheory.PolyOrigin
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LinearPartIteration

variable {R : Type} [CommRing R] {d : ℕ}

def part (F : MvPowerSeries (Fin d) R) (j : Fin d) : MvPowerSeries (Fin d) R :=
  fun α => if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0

theorem coeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (part F j) = if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0 := rfl

theorem constantCoeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) :
    constantCoeff (part F j) = coeff (Finsupp.single j 1) F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_part]
  simp

theorem coeff_X_mul_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (β : Fin d →₀ ℕ) :
    coeff β (X j * part F j) = if β j ≠ 0 ∧ ∀ k < j, β k = 0 then coeff β F else 0 := by
  classical
  rw [X_def, coeff_monomial_mul, one_mul, coeff_part]
  by_cases h : β j = 0
  · rw [if_neg, if_neg]
    · simp [h]
    · rw [Finsupp.single_le_iff]; omega
  · have hle : Finsupp.single j 1 ≤ β := by rw [Finsupp.single_le_iff]; omega
    rw [if_pos hle, tsub_add_cancel_of_le hle]
    have : (∀ k < j, (β - Finsupp.single j 1 : Fin d →₀ ℕ) k = 0) ↔ (β j ≠ 0 ∧ ∀ k < j, β k = 0) := by
      constructor
      · intro H
        refine ⟨h, fun k hk => ?_⟩
        have := H k hk
        rwa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk.ne, Nat.sub_zero] at this
      · intro H k hk
        rw [Finsupp.tsub_apply, H.2 k hk, Nat.zero_sub]
    simp only [this]

theorem eq_const_add_sum (F : MvPowerSeries (Fin d) R) :
    F = C (constantCoeff F) + ∑ j, X j * part F j := by
  classical
  ext β

  rw [map_add (f := _), map_sum, coeff_C]
  simp only [coeff_X_mul_part]
  by_cases hβ : β = 0
  · subst hβ
    simp
  · rw [if_neg hβ, zero_add]
    have hne : β.support.Nonempty := Finsupp.support_nonempty_iff.2 hβ
    have h0 : β (β.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.1 (β.support.min'_mem hne)
    have h1 : ∀ k < β.support.min' hne, β k = 0 := fun k hk => by
      by_contra hk0
      exact absurd (β.support.min'_le k (Finsupp.mem_support_iff.2 hk0)) (not_le.2 hk)
    rw [Finset.sum_eq_single (β.support.min' hne), if_pos ⟨h0, h1⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne hj with h | h
      · exact h2 (h1 j h)
      · exact h0 (h3 _ h)
    · simp

theorem iterate_linear_part : ∀ (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [inst : CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ (i : Fin d), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) R → R) (μ i) = (0 : R)) → ((GlobalTheory.Katz.op μ (fun (i : Fin d) ↦ MvPowerSeries.X i) fun (x : Fin d) ↦ (0 : MvPowerSeries (Fin d) R)) = fun (i : Fin d) ↦ MvPowerSeries.X i) → (∀ (i : Fin d), GlobalTheory.Katz.swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ (r : R), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] F) - ∑ j : Fin d, (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] (MvPowerSeries.X j)) * (MvPowerSeries.coeff fun₀ | j => (1 : ℕ) : MvPowerSeries (Fin d) R → R) F = (↑p : R) * r := by
  intro p hp R _ d μ h0 h1 _ u F
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ h0 u
  let D : MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R :=
    { toFun := GlobalTheory.LawDer.invDer μ u, map_add' := hadd, map_smul' := hsmul }
  have hD : ∀ G, (GlobalTheory.LawDer.invDer μ u)^[p] G = (D ^ p) G := fun G => by
    rw [Module.End.pow_apply]; rfl
  have hDC : ∀ a : R, (D ^ p) (C a) = 0 := fun a => by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
    rw [hn, pow_succ, Module.End.mul_apply, show D (C a) = 0 from hC a, map_zero]
  have key : ∀ j : Fin d, ∃ r : R, constantCoeff ((D ^ p)
      (X j * (part F j - C (coeff (Finsupp.single j 1) F)))) = p * r := fun j => by
    rw [← hD]
    exact GlobalTheory.T.constantCoeff_iterate_p_invariantDerivation_mul p R d μ h0 h1 u _ _ (by simp) (by simp [constantCoeff_part])
  choose r hr using key
  refine ⟨∑ j, r j, ?_⟩
  have hF : constantCoeff ((D ^ p) F) = ∑ j, constantCoeff ((D ^ p) (X j * part F j)) := by
    conv_lhs => rw [eq_const_add_sum F]

    rw [map_add (f := _), hDC, zero_add, map_sum, map_sum]
  simp only [hD]
  rw [hF, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hr j, mul_sub, map_sub, map_sub, mul_comm (X j) (C _), ← smul_eq_C_mul, map_smul,
    ← coeff_zero_eq_constantCoeff_apply ((_ : R) • _), map_smul, coeff_zero_eq_constantCoeff_apply,
    smul_eq_mul, mul_comm (constantCoeff _)]

end GlobalTheory.LinearPartIteration
end
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem exists_lift_of_chart_lifts : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ spMap π ≫ e = g₀ := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps R R₀ π hπ hI X hX g₀ hg₀ κ f hf V hV hL
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_glue_spec_localizationAway_morphisms R κ f hf X.left e he3
  refine ⟨E, ?_, ?_⟩
  · refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R κ f hf (Sp R) _ _ (fun k => ?_)
    rw [← Category.assoc, hE k, he1 k, Category.comp_id]
  · have hf₀ : Ideal.span (Set.range (fun k => π (f k))) = ⊤ := by
      rw [show (fun k => π (f k)) = π ∘ f from rfl, Set.range_comp, ← Ideal.map_span, hf, Ideal.map_top]
    refine GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top R₀ κ (fun k => π (f k)) hf₀ X.left _ _ (fun k => ?_)
    rw [← he2 k, ← hE k, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp _).symm

end GlobalTheory.SecGlue
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], ∀ b : H, counit (R := K) b = 0 → dUnit (R := K) b = 0 → Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (Ideal.Quotient.mkₐ K (frobKerIdeal p K H)) (cobOne K H b) = 0 → b ∈ frobKerIdeal p K H := by
  first | exact @GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne | exact GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne | (intros; apply GlobalTheory.PDiv.FrobKerPrim.mem_frobKerIdeal_of_cobOne <;> assumption)
end
