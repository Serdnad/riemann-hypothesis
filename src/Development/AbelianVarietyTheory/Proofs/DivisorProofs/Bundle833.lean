module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle805
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.EtC.ExcisionNat

abbrev C (R : Type) [CommRing R] (B : Type) [CommRing B] : Cx R := (chains R).obj (sp B)

abbrev Cm (R : Type) [CommRing R] {B B' : Type} [CommRing B] [CommRing B'] (g : B →+* B') : C R B' ⟶ C R B :=
  (chains R).map (spMap g)

theorem spMap_comp {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B) (g : B →+* B') :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem Cm_comp (R : Type) [CommRing R] {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B)
    (g : B →+* B') : Cm R g ≫ Cm R h = Cm R (g.comp h) := by
  rw [← Functor.map_comp, spMap_comp]

theorem awayMap_comp_algebraMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
  IsLocalization.map_comp _

theorem awayHom_comp_awayMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (Localization.awayMap (algebraMap A A') f) = Localization.awayMap (algebraMap A A'') f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, awayMap_comp_algebraMap, ← RingHom.comp_assoc, awayHom_comp_algebraMap,
    awayMap_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

def exSC (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    ShortComplex (Cx R) :=
  ShortComplex.mk
    (biprod.lift (Cm R (Localization.awayMap (algebraMap A A') f))
      (-Cm R (algebraMap A' (Localization.Away (algebraMap A A' f)))))
    (biprod.desc (Cm R (algebraMap A (Localization.Away f))) (Cm R (algebraMap A A')))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Cm_comp, Cm_comp, awayMap_comp_algebraMap, add_neg_cancel])

theorem exSC_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A) (hN : IsNbhd A A' f) : (exSC R A A' f).ShortExact := by
  refine GlobalTheory.T.chain_complex_exact_square R _ _ _ _ ?_ (exSC R A A' f).zero (GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f hN ?_)
  all_goals
    simp only [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      awayMap_comp_algebraMap, add_neg_cancel]

def exMap (R : Type) [CommRing R] {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) : exSC R A A'' f ⟶ exSC R A A' f where
  τ₁ := Cm R (awayHom φ f)
  τ₂ := biprod.map (𝟙 _) (Cm R φ.toRingHom)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [exSC, Category.assoc, biprod.lift_fst, biprod.map_fst, Category.comp_id, Cm_comp, awayHom_comp_awayMap]
    · simp only [exSC]
      rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
        Preadditive.comp_neg, Preadditive.neg_comp, Cm_comp, Cm_comp, awayHom_comp_algebraMap]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [exSC, biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc, Category.comp_id]
    · simp only [exSC, biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id, Cm_comp]
      congr 2
      exact RingHom.ext fun a => φ.commutes a

theorem excision_natural : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  intro q A A' _ _ _ _ f hN n i
  have hI : ∀ k, Injective ((res (ZMod q) (tw q i)).X k) := fun k =>
    inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X k))
  obtain ⟨d, hex, hnat⟩ := longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) hI
  have hS := exSC_shortExact (ZMod q) A A' f hN
  refine ⟨d (exSC (ZMod q) A A' f) hS n, ?_, ?_⟩
  · intro x
    refine Iff.trans ?_ ((hex _ hS n).2.2 x)
    have hb := (cpull_biprod_bijective (ZMod q) (C (ZMod q) (Localization.Away f)) (C (ZMod q) A')
      (res (ZMod q) (tw q i)) (n + 1)).1
    have e1 : pull (ZMod q) (spMap (algebraMap A (Localization.Away f))) (tw q i) (n + 1) x =
        cpull (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A (Localization.Away f)) := biprod.inl_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    have e2 : pull (ZMod q) (spMap (algebraMap A A')) (tw q i) (n + 1) x =
        cpull (biprod.inr : C (ZMod q) A' ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inr : C (ZMod q) A' ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A A') := biprod.inr_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    change (_, _) = ((0, 0) : _ × _) ↔ _
    rw [e1, e2]
    obtain ⟨y, hy⟩ : ∃ y : CohomologyClass (C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') (res (ZMod q) (tw q i)) (n + 1),
      y = cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x := ⟨_, rfl⟩
    rw [← hy]
    constructor
    · intro h
      apply hb
      dsimp only
      rw [h]
      exact Prod.ext (map_zero _).symm (map_zero _).symm
    · intro h
      rw [h]
      exact Prod.ext (map_zero _) (map_zero _)
  · intro A'' _ _ _ φ hN'' z hz
    have hS'' := exSC_shortExact (ZMod q) A A'' f hN''
    have h := hnat _ _ hS'' hS (exMap (ZMod q) φ f) n z
    have hz' : cpull (exMap (ZMod q) φ f).τ₁ (res (ZMod q) (tw q i)) n z = 0 := hz
    rw [hz', map_zero] at h
    have hid : cpull (exMap (ZMod q) φ f).τ₃ (res (ZMod q) (tw q i)) (n + 1) (d _ hS n z) = d _ hS n z :=
      ZcFun.cpull_id _ _ _ _
    rw [hid] at h
    exact h

end GlobalTheory.EtC.ExcisionNat
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv.FrobKerInter

theorem isHopfIdeal_sup {k A : Type} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (I J : Ideal A) [I.IsHopfIdeal k] [J.IsHopfIdeal k] : (I ⊔ J).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 := Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hy
    have h2 := Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars k) hz
    rw [map_add (f := _), h1, h2, add_zero]
  · intro x hx
    set K := (I ⊔ J).restrictScalars k
    have key : ∀ (L : Ideal A) [L.IsHopfIdeal k], L ≤ I ⊔ J → ∀ y ∈ L,
        TensorProduct.map K.mkQ K.mkQ (comul (R := k) y) = 0 := by
      intro L _ hL y hy
      have hle : L.restrictScalars k ≤ K := fun a ha => hL ha
      have e : K.mkQ = (Submodule.mapQ (L.restrictScalars k) K LinearMap.id hle) ∘ₗ
          (L.restrictScalars k).mkQ := by
        rw [Submodule.mapQ_mkQ, LinearMap.comp_id]
      rw [e, TensorProduct.map_comp, LinearMap.comp_apply,
        Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := L.restrictScalars k) hy, map_zero]
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), key I le_sup_left y hy, key J le_sup_right z hz, add_zero]
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Ideal.IsHopfIdeal.antipode_mem (R := k) hy)
      (Ideal.IsHopfIdeal.antipode_mem (R := k) hz)

theorem exists_quotient_kerIdeal_sup_frobKerIdeal : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  intro p hp k _ _ G H q
  have : (kerIdeal (q.app 1)).IsHopfIdeal k := isHopfIdeal_kerIdeal_of_bialgHom k _ _ (q.app 1)
  have : (frobKerIdeal p k (G.A 1)).IsHopfIdeal k := by
    let J := frobKerIdeal p k (G.A 1)
    let f := Ideal.Quotient.mkₐ k J
    refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
    · exact frobKerIdeal_le_augIdeal hp.out.ne_zero k (G.A 1)
    · intro x hx
      have h : J ≤ RingHom.ker
          ((Algebra.TensorProduct.map f f).comp (comulAlgHom k (G.A 1))) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, AlgHom.comp_apply,
          FrobKerOrder.map_pow_eq, comulAlgHom_apply, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul, ← map_pow]
        have hpow : f (a ^ p) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
        rw [hpow, tmul_zero]
      exact h hx
    · intro x hx
      have h : J ≤ J.comap (HopfAlgebra.antipodeAlgHom k (G.A 1)) := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, map_pow]
        apply pow_mem_frobKerIdeal
        have ha' : counit (R := k) a = 0 := ha
        simp [RingHom.mem_ker, ha']
      exact h hx
  set I := kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) with hI
  have : I.IsHopfIdeal k := isHopfIdeal_sup _ _
  let π : G.A 1 →ₐc[k] G.A 1 ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have : Module.Finite k (G.A 1) := G.finite 1
  refine ⟨G.A 1 ⧸ I, inferInstance, inferInstance, KerGrp.isCocomm_of_surjective π hπ,
    Module.Finite.of_surjective (π : G.A 1 →ₗ[k] G.A 1 ⧸ I) hπ, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_, FrobKerOrder.le_sq p k (G.A 1)⟩
  intro a ha
  obtain ⟨b, rfl⟩ := hπ a
  have hb : b ∈ augIdeal k (G.A 1) := ha
  change Ideal.Quotient.mk I b ^ p = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (pow_mem_frobKerIdeal hb)

end GlobalTheory.PDiv.FrobKerInter
end
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem exists_section_strictHenselisation_at_closed : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  intro hKey T E _ _ _ _ _ _ _ _ hT y _ hyT hyne q hq hqu DE _ _ actE htor
  obtain ⟨S, _, _, _, _, _, _, _, _, hmax, hflat, hloc, φ, hφ, hsh⟩ := GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt T E y
  have hKey' := hKey
  unfold GlobalTheory.LocAcyc.KeyClosedPts GlobalTheory.LocAcyc.KeyLocalWith at hKey'
  have htriv : GlobalTheory.LocAcyc.TorsorsTrivial (GlobalTheory.LocAcyc.GenFib T S) q :=
    hKey' T S hT (y.comap (algebraMap (Polynomial T) E)) φ hφ hsh hyT hyne q hq hqu
  have hMN : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors T)).comap (algebraMap E S) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.mp hx
    exact Submonoid.mem_map.mpr ⟨t, ht, IsScalarTower.algebraMap_apply T E S t⟩
  let f : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T S :=
    IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S) hMN
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) := f.toAlgebra
  obtain ⟨act', -, htor'⟩ :=
    GlobalTheory.T.isZModTorsorFiniteProjective_baseChange (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S) DE q hq actE htor
  obtain ⟨σ⟩ := (GlobalTheory.LocAcyc.torsorsTrivial_iff _ q).mp htriv _ act' htor'
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hmax, hflat, hloc, σ.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        DE →ₐ[GlobalTheory.LocAcyc.GenFib T E] GlobalTheory.LocAcyc.GenFib T S ⊗[GlobalTheory.LocAcyc.GenFib T E] DE).toRingHom,
    fun e => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  have hσ := σ.commutes (algebraMap (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T S)
    (algebraMap E (GlobalTheory.LocAcyc.GenFib T E) e))
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at hσ
  rw [hσ, RingHom.algebraMap_toAlgebra]
  exact IsLocalization.map_eq hMN e

end GlobalTheory.LocAcyc
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem res_defect : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ),
    IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) =
      GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  intro Q q _ hqQ V U g v hQ
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (zero_dvd_iff.mp hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hqU : IsUnit (q : Γ(U, ⊤)) := by
    obtain ⟨k, hk⟩ := hqQ
    rw [hk, Nat.cast_mul] at hQ
    exact isUnit_of_mul_isUnit_left hQ
  unfold defect
  rw [Sec.res, map_sub]
  change Sec.res g _ - Sec.res g _ = _
  rw [(redMap Q q 1).nat g 0, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).1 V U g v hQ, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g _ hqU, map_pow]

end GlobalTheory.EtC.RedChern
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.enlarge_base_separable_point_integralClosure : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (exact GlobalTheory.KeyOriginEnlargePoint.enlarge_point) | (intros; apply GlobalTheory.KeyOriginEnlargePoint.enlarge_point  <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.isSection_holomorphic_mul_frame_extendByZero : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  first | exact @GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable | exact GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable | (intros; apply GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable <;> assumption)
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.low_rank_filtration_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | exact GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | (intros; apply GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT


theorem _root_.GlobalTheory.T.translation_isos_commute_of_commutatorPairing_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G) (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1])) (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])), φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 → LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left)) (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | exact GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs | (intros; apply GlobalTheory.UPel.HT.Hecke.gen_commute_of_weilIs <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.pull_h1_surjective_bijective_fibre : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective_base : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) :=
  fun R R' _ _ σ X X' s s' φ h hσ ↦ pullHO1_surjective_of_bijective R R' σ hσ X s X' s' φ h

end GlobalTheory.AbCoh
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

theorem _root_.GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∃ F, IsCoordEnd g a a' h' u F := by
  first | exact @GlobalTheory.Mum.EndThick.exists_isCoordEnd | exact GlobalTheory.Mum.EndThick.exists_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.exists_isCoordEnd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

theorem _root_.GlobalTheory.T.thickenedGroup_endomorphism_transition_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  first | exact @GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat | exact GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat | (intros; apply GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat <;> assumption)
end
