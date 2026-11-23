module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem exists_one_tmul_eq_of_isIntegral_smooth_fractionField
    (R K B : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (x : K ⊗[R] B) (hx : IsIntegral R x) : ∃ b : B, x = (1 : K) ⊗ₜ[R] b := by
  let e := Algebra.TensorProduct.comm R K B
  have h1 : IsIntegral R (e x) := hx.map e.toAlgHom
  have h2 : IsIntegral B (e x) := h1.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩
  have hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x := congrArg Subtype.val hy
  have key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B,
      (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
    intro y
    induction y with
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add (f := _), Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, e.injective ?_⟩
  rw [← hy', hb]
  simp [e]

theorem etale_integralClosure_tensor_of_etale_of_isIntegral :
    ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  intro S₁ K₁ T _ _ _ _ _ _ _ _ hE hI
  let i : T →ₐ[S₁] K₁ ⊗[S₁] T := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)
  have hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T) := fun t =>
    (Algebra.IsIntegral.isIntegral (R := S₁) t).map i
  let φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T) := i.codRestrict _ hint
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx
      exact ⟨b, Subtype.ext hb.symm⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.RootFibre

section
variable (R K L : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
include K

end

variable (R L Q : Type) [CommRing R] [CommRing L] [Algebra R L] [CommRing Q] [Algebra R Q] [IsDomain Q]

noncomputable def toFrac : Q ⊗[R] L →ₐ[Q] FractionRing Q ⊗[R] L :=
  Algebra.TensorProduct.map (Algebra.ofId Q (FractionRing Q)) (AlgHom.id R L)

theorem toFrac_injective [Module.Flat R L] : Function.Injective (toFrac R L Q) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L)
    ((IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap)
    (IsFractionRing.injective Q (FractionRing Q))
  have e : ⇑(toFrac R L Q) =
      ⇑(LinearMap.rTensor L (IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [toFrac]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [e]; exact h

theorem finite_integralClosure [Module.Flat R L] [Algebra.FormallyEtale R L] [Algebra.EssFiniteType R L]
    [IsIntegrallyClosed Q] [IsNoetherianRing Q] :
    Module.Finite Q (integralClosure Q (Q ⊗[R] L)) := by
  classical
  have : Algebra.EssFiniteType (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.EssFiniteType.baseChange R L (FractionRing Q)
  have hfin : Module.Finite (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  obtain ⟨I, _, A, _, _, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing Q) (FractionRing Q ⊗[R] L)).1
      inferInstance
  letI : ∀ i, Algebra Q (A i) := fun i =>
    ((algebraMap (FractionRing Q) (A i)).comp (algebraMap Q (FractionRing Q))).toAlgebra
  haveI : ∀ i, IsScalarTower Q (FractionRing Q) (A i) := fun i =>
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : ∀ i, FiniteDimensional (FractionRing Q) (A i) := fun i =>
    Module.Finite.of_surjective ((Pi.evalAlgHom (FractionRing Q) A i).comp e.toAlgHom).toLinearMap
      (fun a => ⟨e.symm (Pi.single i a), by simp⟩)
  haveI : ∀ i, IsNoetherian Q (integralClosure Q (A i)) := fun i =>
    IsIntegralClosure.isNoetherian Q (FractionRing Q) (A i) (integralClosure Q (A i))
  let g : Q ⊗[R] L →ₐ[Q] (∀ i, A i) :=
    ((e.toAlgHom).restrictScalars Q).comp (toFrac R L Q)
  have hg : Function.Injective g := e.injective.comp (toFrac_injective R L Q)
  let ψ : integralClosure Q (Q ⊗[R] L) →ₗ[Q] (∀ i, integralClosure Q (A i)) :=
    { toFun := fun y i => ⟨g y i, ((y.2.map g).map (Pi.evalAlgHom Q A i))⟩
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hg
    funext i
    have := congrArg (fun f => ((f i : A i))) hab
    simpa [ψ] using this
  have : IsNoetherian Q (integralClosure Q (Q ⊗[R] L)) := isNoetherian_of_injective ψ hψ
  exact Module.IsNoetherian.finite Q _

end GlobalTheory.RootFibre
end

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem etale_localization_of_cokernel_killed (S : Type) [CommRing S] (A B : Type) [CommRing A]
    [CommRing B] [Algebra S A] [Algebra S B] (ι : A →ₐ[S] B) (hι : Function.Injective ι)
    (p : Ideal S) [p.IsPrime] (s : S) (hs : s ∉ p) (hB : ∀ y : B, s • y ∈ ι.range)
    (hA : Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) :
    Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) B) := by
  let Φ : TensorProduct S (Localization.AtPrime p) A →ₐ[Localization.AtPrime p]
      TensorProduct S (Localization.AtPrime p) B :=
    Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ι
  have inj : Function.Injective Φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Localization.AtPrime p)
      (ι.toLinearMap.restrictScalars S) hι
  have hu : IsUnit (algebraMap S (Localization.AtPrime p) s) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
  obtain ⟨u, hu'⟩ := hu
  have surj : Function.Surjective Φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r y =>
      obtain ⟨a, ha⟩ := hB y
      refine ⟨(r * ↑u⁻¹) ⊗ₜ a, ?_⟩
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [show ι a = s • y from ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, ← hu', mul_left_comm, Units.mul_inv, mul_one]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective Φ ⟨inj, surj⟩)

end GlobalTheory
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem etale_localization_atPrime_tensor_of_etale_away : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ b hE P _ hb
  let Rp := Localization.AtPrime P
  let Cb := Localization.Away (algebraMap R C b)
  haveI : Algebra.Etale Rp (Rp ⊗[R] Cb) := Algebra.Etale.baseChange R Cb Rp
  have hu : IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).toRingHom
      (algebraMap R C b)) := by
    change IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C) (algebraMap R C b))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R Rp (Rp ⊗[R] C)]
    exact (IsLocalization.map_units Rp (⟨b, hb⟩ : P.primeCompl)).map _
  let g0 : Cb →+* Rp ⊗[R] C := IsLocalization.Away.lift (algebraMap R C b) hu
  have hg0 : ∀ c : C, g0 (algebraMap C Cb c) = (1 : Rp) ⊗ₜ[R] c := fun c =>
    IsLocalization.Away.lift_eq (algebraMap R C b) hu c
  let g : Cb →ₐ[R] Rp ⊗[R] C :=
    { g0 with
      commutes' := fun r => by
        change g0 (algebraMap R Cb r) = _
        rw [IsScalarTower.algebraMap_apply R C Cb, hg0]
        exact (Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).commutes r }
  let Φ : Rp ⊗[R] Cb →ₐ[Rp] Rp ⊗[R] C :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp _) g (fun _ _ => Commute.all _ _)
  let Ψ : Rp ⊗[R] C →ₐ[Rp] Rp ⊗[R] Cb :=
    Algebra.TensorProduct.map (AlgHom.id Rp Rp) (IsScalarTower.toAlgHom R C Cb)
  have h1 : Φ.comp Ψ = AlgHom.id Rp _ := by
    ext c
    simp [Φ, Ψ, g, hg0]
  have h2 : Ψ.comp Φ = AlgHom.id Rp _ := by
    ext x
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change Ψ (Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x)) = (1 : Rp) ⊗ₜ[R] algebraMap C Cb x
    have : Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x) = (1 : Rp) ⊗ₜ[R] x := by
      simp [Φ, g, hg0]
    rw [this]
    simp [Ψ]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom Ψ Φ h2 h1).symm

end GlobalTheory
end

section

open IsLocalRing

namespace GlobalTheory

theorem etale_quotient_of_etale_punctured :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R)
      [IsLocalRing (R ⧸ Ideal.span {f})],
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) →
        Algebra.Etale (Localization.AtPrime P)
          (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P)
            (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  intro R A _ _ _ _ f _ H P _ hP
  set S := R ⧸ Ideal.span {f}
  set T := Localization.AtPrime P
  set p : Ideal R := P.comap (algebraMap R S) with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hx (hu.map _)
    rw [← h] at hr
    exact hr
  haveI := H p hp
  let φ : Localization.AtPrime p →+* T := Localization.localRingHom p P (algebraMap R S) rfl
  letI : Algebra (Localization.AtPrime p) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) T :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show algebraMap R T r = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S T])
  haveI : Algebra.Etale T (TensorProduct (Localization.AtPrime p) T
      (TensorProduct R (Localization.AtPrime p) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) T T A
  let e2 := Algebra.TensorProduct.cancelBaseChange R S T T A
  let e3 : (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[S] TensorProduct R S A :=
    AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {f})).restrictScalars R).trans
        (Algebra.TensorProduct.comm R A S))
  let e4 : TensorProduct S T (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[T]
      TensorProduct S T (TensorProduct R S A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e3
  exact Algebra.Etale.of_equiv (e1.trans (e4.trans e2).symm)

end GlobalTheory
end

section

open IsLocalRing TensorProduct

namespace GlobalTheory.OffDivisor

theorem etale_localization_of_comap : ∀ (R Q A : Type) [CommRing R] [CommRing Q] [Algebra R Q] [CommRing A] [Algebra R A] (p : Ideal R) [p.IsPrime] (q : Ideal Q) [q.IsPrime], q.comap (algebraMap R Q) = p → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A) → Algebra.Etale (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime q) A) := by
  intro R Q A _ _ _ _ _ p _ q _ hpq h
  subst hpq
  letI : Algebra (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) :=
    (Localization.localRingHom _ q (algebraMap R Q) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R Q (Localization.AtPrime q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (q.comap (algebraMap R Q))) (B := Localization.AtPrime q) (A := TensorProduct R (Localization.AtPrime (q.comap (algebraMap R Q))) A)
  exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) (Localization.AtPrime q) A :
    TensorProduct (Localization.AtPrime (q.comap (algebraMap R Q))) (Localization.AtPrime q) (TensorProduct R (Localization.AtPrime (q.comap (algebraMap R Q))) A) ≃ₐ[Localization.AtPrime q] TensorProduct R (Localization.AtPrime q) A))

end GlobalTheory.OffDivisor
end

section

open IsLocalRing

namespace GlobalTheory

theorem essEtaleLocal_le_of_directed :
  ∀ (R T : Type) [CommRing R] [CommRing T] [Algebra R T] (U : Subalgebra R T) (μ : Type) [Preorder μ] [IsDirected μ (· ≤ ·)] [Nonempty μ] (V : μ → Subalgebra R T), Monotone V → (∀ x ∈ U, ∃ m, x ∈ V m) → (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) → ∀ (W : Subalgebra R T), W ≤ U → (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] W)) → ∃ m, W ≤ V m := by
  classical
  intro R T _ _ _ U μ _ _ _ V hmono hcov hloc W hWU hW
  obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hW
  let L := Localization.AtPrime q
  let φ : A →ₐ[R] T := W.val.comp (e.toAlgHom.comp (IsScalarTower.toAlgHom R A L))
  have hφW : ∀ a, φ a ∈ W := fun a => (e (algebraMap A L a)).2
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  choose f hf using fun a : A => hcov (φ a) (hWU (hφW a))
  obtain ⟨M, hM⟩ := (s.image f).exists_le
  have hrange : ∀ a, φ a ∈ V M := by
    have hle : (⊤ : Subalgebra R A) ≤ (V M).comap φ := by
      rw [← hs]
      refine Algebra.adjoin_le ?_
      intro a ha
      exact hmono (hM _ (Finset.mem_image_of_mem f ha)) (hf a)
    intro a
    exact hle Algebra.mem_top
  refine ⟨M, fun w hw => ?_⟩
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨w, hw⟩)
  set y : T := ((e (IsLocalization.mk' L (1 : A) t) : W) : T) with hy
  have hyU : y ∈ U := hWU (e _).2
  have hxy : φ t * y = 1 := by
    have h1 : algebraMap A L t * IsLocalization.mk' L (1:A) t = 1 := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self']
    have h2 : ((e (algebraMap A L t * IsLocalization.mk' L (1:A) t) : W) : T) = 1 := by
      rw [h1, map_one]; rfl
    rw [map_mul, Subalgebra.coe_mul] at h2
    exact h2
  obtain ⟨z, hzV, hz⟩ := hloc M (φ t) (hrange t) y hyU hxy
  have hzy : z = y := by
    calc z = (y * φ t) * z := by rw [mul_comm y, hxy, one_mul]
      _ = y * (φ t * z) := by ring
      _ = y := by rw [hz, mul_one]
  have hw' : w = φ a * y := by
    have h1 : (⟨w, hw⟩ : W) = e (IsLocalization.mk' L a t) := by
      change IsLocalization.mk' L a t = _ at hat
      rw [hat, AlgEquiv.apply_symm_apply]
    have h2 : IsLocalization.mk' L a t = algebraMap A L a * IsLocalization.mk' L (1:A) t := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one]
    have h3 : w = ((e (IsLocalization.mk' L a t) : W) : T) := congrArg Subtype.val h1
    rw [h3, h2, map_mul, Subalgebra.coe_mul]
    rfl
  rw [hw', ← hzy]
  exact (V M).mul_mem (hrange a) hzV

end GlobalTheory
end

section

set_option autoImplicit false

namespace GlobalTheory.GenericEtale

theorem exists_etale_away_of_isAlgebraic : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Algebra.Etale A' B' := by
  intro A B _ _ _ _ _ _ _ _ _ _
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  haveI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  haveI : Algebra.IsAlgebraic B L := IsLocalization.isAlgebraic L (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A L := Algebra.IsAlgebraic.trans A B L
  haveI : Algebra.IsAlgebraic K L := (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).1 inferInstance
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have e1 : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have e2 : Algebra.FormallyEtale K L := .of_isSeparable K L
  have e3 : Algebra.FormallyEtale A L := .comp A K L
  have hl : IsLocalization.AtPrime L (⊥ : Ideal B) := by
    rw [IsLocalization.AtPrime, Ideal.primeCompl_bot]; infer_instance
  have e4 : Algebra.IsEtaleAt A (⊥ : Ideal B) :=
    .of_equiv ((IsLocalization.algEquiv (⊥ : Ideal B).primeCompl L
      (Localization.AtPrime (⊥ : Ideal B))).restrictScalars A)
  obtain ⟨b, hb, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  obtain ⟨h, hh, hd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero (by simpa using hb))
  refine ⟨h, hh, fun c A' B' _ _ _ _ _ _ _ _ hA' hB' => ?_⟩
  have e5 : Algebra.Etale A (Localization.Away (algebraMap A B (h * c))) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hE ⊢
    intro x hx
    refine hE fun hxb => hx ?_
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ hd hxb)
  haveI : Algebra.Etale A B' := .of_equiv ((IsLocalization.algEquiv (.powers (algebraMap A B (h * c)))
    (Localization.Away (algebraMap A B (h * c))) B').restrictScalars A)
  haveI : Algebra.Etale A A' := .of_isLocalizationAway (h * c)
  exact Algebra.Etale.of_restrictScalars A A' B'

end GlobalTheory.GenericEtale
end

section

open TensorProduct KaehlerDifferential

namespace GlobalTheory

theorem injective_cotangentComplexBaseChange_of_forms_extend : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ hext
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  refine (Module.forall_dual_apply_eq_zero_iff K z).1 fun φ => ?_
  let ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K :=
    (φ.restrictScalars P) ∘ₗ (TensorProduct.mk P K (RingHom.ker (algebraMap P R)) 1)
  obtain ⟨D, hD⟩ := hext ℓ
  let Λ : K ⊗[P] Ω[P⁄A] →ₗ[K] K := LinearMap.liftBaseChange K D.liftKaehlerDifferential
  have key : Λ ∘ₗ cotangentComplexBaseChange A R P K = φ := by
    ext i
    simp [Λ, cotangentComplexBaseChange_tmul, kerToTensor_apply, hD, ℓ]
  have h2 := congrArg (fun f => f z) key
  simpa [hz] using h2.symm

end GlobalTheory
end
