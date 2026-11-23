module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdMulOfIdem
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle002
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory IsLocalRing

namespace GlobalTheory.LocalIndEtaleUnramified

theorem exists_local_of_algHom {A S B : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)] [CommRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] (g : B →ₐ[A] S) (b : B) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = g b := by
  let P : Ideal B := (maximalIdeal S).comap (g : B →+* S)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (g y) := by
    intro y
    by_contra h
    exact y.2 (show (g : B →+* S) y ∈ maximalIdeal S from h)
  let φ : Localization.AtPrime P →ₐ[A] S := IsLocalization.liftAlgHom (M := P.primeCompl) hu
  have hφ : ∀ y : B, φ (algebraMap B (Localization.AtPrime P) y) = g y := fun y =>
    IsLocalization.lift_eq (M := P.primeCompl) (g := (g : B →+* S)) hu y
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    refine (IsLocalization.AtPrime.isUnit_mk'_iff _ P y s).2 ?_
    have h1 : φ (IsLocalization.mk' (Localization.AtPrime P) y s) * g s = g y := by
      rw [← hφ, ← map_mul, IsLocalization.mk'_spec, hφ]
    have h2 : IsUnit (g y) := h1 ▸ ha.mul (hu s)
    intro hy
    exact (show (g : B →+* S) y ∈ maximalIdeal S from hy) h2
  have hA : IsLocalHom (algebraMap A (Localization.AtPrime P)) := by
    refine ⟨fun a ha => ?_⟩
    have := ha.map φ
    rw [AlgHom.commutes] at this
    exact IsLocalHom.map_nonunit a this
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  haveI : Algebra.EssFiniteType B (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  exact ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, hA,
    Algebra.FormallyUnramified.comp A B _, Algebra.EssFiniteType.comp A B _, φ, hloc,
    algebraMap B _ b, hφ b⟩

theorem exists_local_unramified_of_isIndEtale {A S : Type} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = s := by
  obtain ⟨J, _, _, D, t, c, hc, H⟩ := h
  obtain ⟨j, b, hb⟩ := Limits.Concrete.isColimit_exists_rep D hc s
  obtain ⟨hE, hcomp⟩ := H j
  let f : A →+* D.obj j := (t.app j).hom
  let g₀ : D.obj j →+* S := (c.app j).hom
  letI : Algebra A (D.obj j) := f.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := hE
  have hg : ∀ a : A, g₀ (f a) = algebraMap A S a := fun a =>
    congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom a) hcomp
  let g : D.obj j →ₐ[A] S := { g₀ with commutes' := hg }
  have hb' : g b = s := hb
  rw [← hb']
  exact exists_local_of_algHom g b

end GlobalTheory.LocalIndEtaleUnramified
end

section

open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTate

theorem exists_local_iso {R : Type} [CommRing R] [IsDedekindDomain R] {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R M'] (hr : Module.finrank R M = Module.finrank R M') (P : Ideal R) [P.IsPrime] :
    ∃ (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) (s : R), s ∉ P ∧ (∀ a, φ' (φ a) = s • a) ∧ ∀ y, φ (φ' y) = s • y := by
  have hle : P.primeCompl ≤ R⁰ := P.primeCompl_le_nonZeroDivisors
  have : Module.Flat R M := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.Flat R M' := IsDedekindDomain.flat_iff_torsion_eq_bot.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have : Module.FinitePresentation R M' := Module.finitePresentation_of_finite R M'
  let S := Localization.AtPrime P
  let N := LocalizedModule P.primeCompl M
  let N' := LocalizedModule P.primeCompl M'
  let j : M →ₗ[R] N := LocalizedModule.mkLinearMap P.primeCompl M
  let j' : M' →ₗ[R] N' := LocalizedModule.mkLinearMap P.primeCompl M'
  have : Module.Free S N := Module.free_of_flat_of_isLocalRing
  have : Module.Free S N' := Module.free_of_flat_of_isLocalRing
  have hr' : Module.finrank S N = Module.finrank S N' := by
    rw [IsLocalization.finrank_eq S P.primeCompl hle, IsLocalization.finrank_eq S P.primeCompl hle,
      IsLocalizedModule.finrank_eq P.primeCompl j hle, IsLocalizedModule.finrank_eq P.primeCompl j' hle, hr]
  let θ : N ≃ₗ[R] N' := (LinearEquiv.ofFinrankEq N N' hr').restrictScalars R
  obtain ⟨φ, s, hφ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl j'
    (θ.toLinearMap ∘ₗ j)
  obtain ⟨φ', s', hφ'⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule P.primeCompl j
    (θ.symm.toLinearMap ∘ₗ j')
  have h1 : ∀ a, j' (φ a) = (s : R) • θ (j a) := fun a => LinearMap.congr_fun hφ a
  have h2 : ∀ a, j (φ' a) = (s' : R) • θ.symm (j' a) := fun a => LinearMap.congr_fun hφ' a
  have hj : Function.Injective j := (IsLocalizedModule.injective_iff_isRegular P.primeCompl j).2
    fun c => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero (hle c.2))
  have hj' : Function.Injective j' := (IsLocalizedModule.injective_iff_isRegular P.primeCompl j').2
    fun c => IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero (hle c.2))
  refine ⟨φ, φ', (s * s' : P.primeCompl), (s * s').2, fun a => hj ?_, fun y => hj' ?_⟩
  · rw [h2, h1, map_smul, map_smul, LinearEquiv.symm_apply_apply, smul_smul, mul_comm]; rfl
  · rw [h1, h2, map_smul, map_smul, LinearEquiv.apply_symm_apply, smul_smul]; rfl

theorem mem_of_orth {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (B : M →+ M →+ ℤ)
    (hB : Function.Bijective B) {m c : ℕ} (hm : m ≠ 0) (hg : m ^ Module.finrank ℤ M = c * c) (C : AddSubgroup M)
    (hC : (nsmulAddMonoidHom (α := M) m).range ≤ C)
    (hc : (nsmulAddMonoidHom (α := M) m).range.relIndex C = c)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (x : M) (hx : ∀ y ∈ C, (m : ℤ) ∣ B x y) : x ∈ C := by
  classical
  have : NeZero m := ⟨hm⟩
  set K := (nsmulAddMonoidHom (α := M) m).range with hK
  have hKi : K.index = c * c := by rw [hK, AddSubgroup.index_range_nsmul, hg]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ hm (by simpa using hg)
  have hCi : C.index = c := by
    have := AddSubgroup.relIndex_mul_index hC
    rw [hc, hKi] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) this
  have : C.FiniteIndex := ⟨hCi ▸ hc0⟩
  let D : AddSubgroup M :=
    { carrier := {x | ∀ y ∈ C, (m : ℤ) ∣ B x y}
      add_mem' := fun {a b} ha hb y hy => by
        rw [map_add (f := _), AddMonoidHom.add_apply]; exact (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by
        rw [map_neg, AddMonoidHom.neg_apply]; exact (ha y hy).neg_right }
  have hCD : C ≤ D := fun x hx => hiso x hx
  let f : D → (M ⧸ C →+ ZMod m) := fun x =>
    QuotientAddGroup.lift C ((Int.castAddHom (ZMod m)).comp (B x)) fun y hy =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (x.2 y hy)
  have hf : ∀ (x : D) (y : M), f x (y : M ⧸ C) = (B x y : ZMod m) := fun _ _ => rfl
  let F : D →+ (M ⧸ C →+ ZMod m) := AddMonoidHom.mk' f fun a b => by
    ext y
    simp [hf]
  have hker : F.ker = K.addSubgroupOf D := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h
      have h1 : ∀ y, (m : ℤ) ∣ B x y := fun y =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [← hf]; exact DFunLike.congr_fun h _)
      choose t ht using h1
      have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
      obtain ⟨z, hz⟩ := hB.2 (AddMonoidHom.mk' t fun a b => mul_left_cancel₀ hm' (by
        rw [← ht, map_add (f := _), ht, ht, mul_add]))
      refine ⟨z, hB.1 (AddMonoidHom.ext fun y => ?_)⟩
      rw [ht, nsmulAddMonoidHom_apply, map_nsmul, hz]
      simp
    · rintro ⟨z, hz⟩
      ext y
      change f x y = 0
      rw [hf, ← hz, nsmulAddMonoidHom_apply, map_nsmul]
      simp
  have := Fintype.ofFinite (M ⧸ C)
  let T : (M ⧸ C →+ ZMod m) → AddChar (M ⧸ C) ℂ := fun φ => ZMod.stdAddChar.compAddMonoidHom φ
  have hT : Function.Injective T := fun φ ψ h => AddMonoidHom.ext fun x =>
    ZMod.injective_stdAddChar (DFunLike.congr_fun h x)
  have : Finite (M ⧸ C →+ ZMod m) := Finite.of_injective T hT
  have h1 : K.relIndex D ≤ c := by
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
      ((Nat.card_le_card_of_injective T hT).trans_eq ?_)
    rw [← hCi, AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have h2 := AddSubgroup.relIndex_mul_relIndex K C D hC hCD
  have h3 : C.relIndex D ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have h4 : C.relIndex D = 1 := by
    rw [hc] at h2
    have := Nat.pos_of_ne_zero hc0
    have := Nat.pos_of_ne_zero h3
    nlinarith
  exact (AddSubgroup.relIndex_eq_one.1 h4) hx

theorem exists_unimod_div {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {σ : R ≃+* R}
    {B : M →+ M →+ ℤ} (h : IsUnimod σ B) {m : ℕ} (hm : m ≠ 0) (C : Submodule R M) (hC : ∀ a, m • a ∈ C)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (horth : ∀ x, (∀ y ∈ C, (m : ℤ) ∣ B x y) → x ∈ C) :
    ∃ B' : C →+ C →+ ℤ, IsUnimod σ B' ∧ ∀ x y : C, B x y = m * B' x y := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  choose t ht using fun x y : C => hiso x x.2 y y.2
  let B' : C →+ C →+ ℤ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (t x) fun a b => mul_left_cancel₀ hm' (by
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add (f := _)]))
    fun a b => AddMonoidHom.ext fun y => mul_left_cancel₀ hm' (by
      change m * t (a + b) y = m * (t a y + t b y)
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add (f := _), AddMonoidHom.add_apply])
  have hB' : ∀ x y : C, B x y = m * B' x y := ht
  refine ⟨B', ⟨fun x y => mul_left_cancel₀ hm' ?_, fun a x y => mul_left_cancel₀ hm' ?_, ?_, fun f => ?_⟩, hB'⟩
  · rw [mul_neg, ← hB', ← hB', h.skew]
  · rw [← hB', ← hB', Submodule.coe_smul, Submodule.coe_smul, h.adj]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    apply (injective_iff_map_eq_zero _).1 h.bij.1
    ext a
    have := hB' x ⟨m • a, hC a⟩
    rw [hx, map_nsmul] at this
    simpa [hm] using this
  · let u : M →+ C := AddMonoidHom.mk' (fun a => ⟨m • a, hC a⟩) fun a b => Subtype.ext (smul_add _ _ _)
    obtain ⟨x, hx⟩ := h.bij.2 (f.comp u)
    have key : ∀ y : C, B x y = m * f y := fun y => by
      rw [hx, ← nsmul_eq_mul, ← map_nsmul]
      rfl
    refine ⟨⟨x, horth x fun y hy => ⟨_, key ⟨y, hy⟩⟩⟩, AddMonoidHom.ext fun y => mul_left_cancel₀ hm' ?_⟩
    rw [← hB', key]

end GlobalTheory.HeckeTate
end

section

open Polynomial

namespace GlobalTheory.AdicNoeth

theorem isNoetherianRing_graded {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing (reesAlgebra I ⧸ reesShiftIdeal I) := by
  have hker : ∀ a ∈ I, algebraMap R (reesAlgebra I ⧸ reesShiftIdeal I) a = 0 := by
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    rcases n with _ | n
    · simpa using ha
    · simp
  letI : Algebra (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    (Ideal.Quotient.lift I (algebraMap R _) hker).toAlgebra
  have : IsScalarTower R (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R (reesAlgebra I) := ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  have : Algebra.FiniteType R (reesAlgebra I ⧸ reesShiftIdeal I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (reesShiftIdeal I))
      (Ideal.Quotient.mkₐ_surjective R _)
  have : Algebra.FiniteType (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) _
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I) _

private lemma coeff_mul_monomial_eq_ite {R : Type} [CommRing R] (p : R[X]) (d n : ℕ) (r : R) :
    (p * monomial d r).coeff n = if d ≤ n then p.coeff (n - d) * r else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

theorem exists_leading_generators {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] (J : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → R) (d : ι → ℕ), (∀ i, f i ∈ J) ∧
      ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1) := by
  classical
  have := isNoetherianRing_graded I hI
  let lf : {p : ℕ × R // p.2 ∈ J ∧ p.2 ∈ I ^ p.1} → reesAlgebra I ⧸ reesShiftIdeal I := fun x =>
    Ideal.Quotient.mk (reesShiftIdeal I) ⟨monomial x.1.1 x.1.2, reesAlgebra.monomial_mem.mpr x.2.2⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range lf)).mp
    (IsNoetherian.noetherian (Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I) (Set.range lf)))
  have hpre : ∀ q : s, ∃ x, lf x = q := fun q => hsS q.2
  choose pre hpre using hpre
  refine ⟨s, inferInstance, fun q => (pre q).1.2, fun q => (pre q).1.1, fun q => (pre q).2.1, ?_⟩
  intro n g hgJ hgn
  have hs : (↑s : Set (reesAlgebra I ⧸ reesShiftIdeal I)) = Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
    ext x; simp
  have hmem : lf ⟨(n, g), hgJ, hgn⟩ ∈ Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I)
      (Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I)) := by
    rw [← hs, ← hspan]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  choose p hp using fun q => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (c q)
  have hz : (⟨monomial n g, reesAlgebra.monomial_mem.mpr hgn⟩ : reesAlgebra I) -
      ∑ q : s, p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩
      ∈ reesShiftIdeal I := by

    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hq : ∀ q : s, Ideal.Quotient.mk (reesShiftIdeal I) (p q *
        ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩) =
        c q • (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
      intro q
      rw [map_mul, hp q, smul_eq_mul]
      exact congrArg _ (hpre q)
    simp only [hq, hc]
    exact sub_self _
  rw [mem_reesShiftIdeal] at hz
  refine ⟨fun q => if (pre q).1.1 ≤ n then ((p q : reesAlgebra I) : R[X]).coeff (n - (pre q).1.1)
    else 0, ?_, ?_⟩
  · intro q
    dsimp only
    split_ifs
    · exact (mem_reesAlgebra_iff I _).mp (p q).2 _
    · exact zero_mem _
  · convert hz n using 1
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      coeff_sub, finsetSum_coeff, coeff_mul_monomial_eq_ite, ite_mul, zero_mul]
    rw [coeff_monomial_same]

theorem mem_span_of_leading {R : Type} [CommRing R] (I : Ideal R) [hc : IsAdicComplete I R]
    (J : Ideal R) {ι : Type} [Fintype ι] (f : ι → R) (d : ι → ℕ) (hf : ∀ i, f i ∈ J)
    (h : ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1))
    (g : R) (hg : g ∈ J) : g ∈ Ideal.span (Set.range f) := by
  classical
  have step : ∀ (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}), ∃ c : ι → R,
      (∀ i, c i ∈ I ^ (n - d i)) ∧ r.1 - ∑ i, c i * f i ∈ I ^ (n + 1) :=
    fun n r => h n r.1 r.2.1 r.2.2
  choose c hc1 hc2 using step
  let res : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n} := fun n =>
    Nat.rec (motive := fun n => {r : R // r ∈ J ∧ r ∈ I ^ n})
      ⟨g, hg, by simp⟩
      (fun n r => ⟨r.1 - ∑ i, c n r i * f i,
        J.sub_mem r.2.1 (J.sum_mem fun i _ => J.mul_mem_left _ (hf i)), hc2 n r⟩) n
  let a : ℕ → ι → R := fun n i => c n (res n) i
  have ha : ∀ n i, a n i ∈ I ^ (n - d i) := fun n i => hc1 n (res n) i
  have hres_succ : ∀ n, (res (n + 1)).1 = (res n).1 - ∑ i, a n i * f i := fun n => rfl
  have hdecomp : ∀ N, g = ∑ i, (∑ m ∈ Finset.range N, a m i) * f i + (res N).1 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, Finset.sum_const_zero, zero_add]
      rfl
    | succ N ih =>
      rw [hres_succ]
      simp only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      conv_lhs => rw [ih]
      ring
  have hpow : ∀ {m n : ℕ} {x : R}, m ≤ n → x ∈ I ^ n → x ∈ I ^ m :=
    fun hmn hx => Ideal.pow_le_pow_right hmn hx
  have htop : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R R) = I ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let T : ι → ℕ → R := fun i k => ∑ m ∈ Finset.range (k + d i), a m i
  have hT : ∀ i {m n : ℕ}, m ≤ n → T i m ≡ T i n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m n hmn
    rw [SModEq.sub_mem, htop]
    have hd : T i n - T i m = ∑ k ∈ Finset.Ico (m + d i) (n + d i), a k i := by
      simp only [T]
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
    rw [← neg_sub, hd]
    refine neg_mem (Ideal.sum_mem _ fun k hk => hpow ?_ (ha k i))
    rw [Finset.mem_Ico] at hk
    omega
  choose L hL using fun i => IsPrecomplete.prec' (I := I) (T i) (hT i)
  have hzero : g - ∑ i, L i * f i = 0 := by
    refine IsHausdorff.haus' (I := I) _ fun N => ?_
    rw [SModEq.sub_mem, sub_zero, htop]
    have hdD : ∀ i, d i ≤ ∑ j, d j := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    rw [hdecomp (N + ∑ j, d j)]
    have hS : ∀ i, ∑ m ∈ Finset.range (N + ∑ j, d j), a m i = T i (N + ∑ j, d j - d i) := by
      intro i
      simp only [T]
      rw [Nat.sub_add_cancel (by have := hdD i; omega)]
    have hrw : ∑ i, (∑ m ∈ Finset.range (N + ∑ j, d j), a m i) * f i + (res (N + ∑ j, d j)).1 -
        ∑ i, L i * f i =
        ∑ i, (T i (N + ∑ j, d j - d i) - L i) * f i + (res (N + ∑ j, d j)).1 := by
      simp only [hS, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hrw]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
      (hpow (by omega) (res (N + ∑ j, d j)).2.2)
    have hLi := hL i (N + ∑ j, d j - d i)
    rw [SModEq.sub_mem, htop] at hLi
    exact hpow (by have := hdD i; omega) hLi
  rw [sub_eq_zero] at hzero
  rw [hzero]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem isNoetherianRing_of_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R), I.FG →
    IsAdicComplete I R → IsNoetherianRing (R ⧸ I) → IsNoetherianRing R := by
  intro R _ I hI hc hq
  refine isNoetherianRing_iff.mpr ⟨fun J => ?_⟩
  obtain ⟨ι, _, f, d, hf, hlead⟩ := exists_leading_generators I hI J
  have hJ : J = Ideal.span (Set.range f) := le_antisymm
    (fun g hg => mem_span_of_leading I J f d hf hlead g hg)
    (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i))
  rw [hJ]
  exact Submodule.fg_span (Set.finite_range f)

end GlobalTheory.AdicNoeth
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem GlobalTheory.exists_finiteType_model_of_smooth_affine :
    ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (p : X ⟶ Sp V), IsAffine X → Smooth p → ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth p₀ ∧ IsAffine X₀ ∧ IsPullback φ p p₀ (spMap f) := by
  intro V _ X p _ _
  let B : CommRingCat.{0} := Γ(X, ⊤)
  let g : CommRingCat.of V ⟶ B := (Scheme.Spec.preimage (X.isoSpec.inv ≫ p)).unop
  have hg : Spec.map g = X.isoSpec.inv ≫ p := Scheme.Spec.map_preimage _
  have hpg : p = X.isoSpec.hom ≫ Spec.map g := by rw [hg, Iso.hom_inv_id_assoc]
  have hsg : Smooth (Spec.map g) := by rw [hg]; infer_instance
  have hgs : g.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsg
  let _ : Algebra V B := g.hom.toAlgebra
  have : Algebra.Smooth V B := hgs
  obtain ⟨A₀, B₀, _, _, hA₀, hsm, ⟨ψe⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ V B
  let T : CommRingCat.{0} := CommRingCat.of (TensorProduct A₀ V B₀)
  let inl : CommRingCat.of V ⟶ T := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of B₀ ⟶ T :=
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A₀) (A := V)).toRingHom
  let jIso : T ≅ B :=
    { hom := CommRingCat.ofHom ψe.symm.toRingHom
      inv := CommRingCat.ofHom ψe.toRingHom
      hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.apply_symm_apply x)
      inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x => ψe.symm_apply_apply x) }
  have hj : inl ≫ jIso.hom = g := by
    ext v
    exact ψe.symm.commutes v
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ V B₀)).flip
  let e : X ≅ Spec T := X.isoSpec ≪≫ Scheme.Spec.mapIso jIso.op
  refine ⟨A₀, inferInstance, algebraMap A₀ V, Spec (CommRingCat.of B₀),
    Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)), e.hom ≫ Spec.map inr, ?_, ?_,
    inferInstance, ?_⟩
  · convert (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  · exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hsm)
  · refine IsPullback.of_iso hpb e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp, hpg]
      change (X.isoSpec.hom ≫ Spec.map jIso.hom) ≫ Spec.map inl = _
      rw [Category.assoc, ← Spec.map_comp, hj]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
end
