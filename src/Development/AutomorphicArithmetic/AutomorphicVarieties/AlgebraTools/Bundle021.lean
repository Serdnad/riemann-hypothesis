module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle006
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GrSpan
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TowerFin
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Flat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle007

@[expose] public section

section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem fibre_reg (R : Type) [CommRing R] (J n : Ideal R) [n.IsPrime] (hn : J ≤ n)
    [IsRegularRing (R ⧸ J)] (A : Type) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A n] :
    IsRegularLocalRing (A ⧸ J.map (algebraMap R A)) := by
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker]
  have hm : (n.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem UpperTheory.V.AlgebraTools.regular_polynomial_localization :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ A)) [Q.IsPrime],
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A) ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x →
        CotInd (Localization.AtPrime Q) (fun k => algebraMap (MvPolynomial σ A) _ (MvPolynomial.C (x k))) := by
  intro A _ _ σ _ Q _ hQ
  have hcomp : algebraMap A (Localization.AtPrime Q) =
      (algebraMap (MvPolynomial σ A) (Localization.AtPrime Q)).comp MvPolynomial.C :=
    IsScalarTower.algebraMap_eq A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsRegularRing (MvPolynomial σ A ⧸
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A)) := by
    letI := Ideal.Quotient.field (maximalIdeal A)
    haveI : IsRegularRing (MvPolynomial σ (A ⧸ maximalIdeal A)) := inferInstance
    exact IsRegularRing.of_ringEquiv
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (maximalIdeal A)).toRingEquiv
  have hf := fibre_reg _ _ Q hQ (Localization.AtPrime Q)
  rw [Ideal.map_map, ← hcomp] at hf
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat (MvPolynomial σ A) (Localization.AtPrime Q) :=
    IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat A (Localization.AtPrime Q) :=
    Module.Flat.trans A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : MvPolynomial.C a ∈ Q := hQ (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna))
    rw [hcomp] at ha
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).1 ha h1
  have H := regular_of_flat_fibre A (Localization.AtPrime Q)
  rw [hcomp] at H
  exact H
end

section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

private theorem hkEv_coe (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (x : G)
    (v : fixd ρ I) : (hk ρ I x v : M) = dc ρ I I x v := by
  have h := (UpperTheory.V.Hi.dcSum A G M ρ I I x (hI x)).2.1
  unfold hk hk2
  rw [dite_eq_left h]
  rfl

private noncomputable def hkEv_phi (ρ : Representation A G M) (I : Subgroup G) (m : M) :
    MonoidAlgebra A (G ⧸ I) →ₗ[A] M :=
  Finsupp.linearCombination A (fun q : G ⧸ I => ρ q.out m) ∘ₗ (MonoidAlgebra.coeffLinearEquiv A).toLinearMap

private theorem hkEv_phi_single (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (g : G) (c : A) :
    hkEv_phi ρ I m (MonoidAlgebra.single (g : G ⧸ I) c) = c • ρ g m := by
  have h1 : g⁻¹ * (g : G ⧸ I).out ∈ I := QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have h2 : ρ (g⁻¹ * (g : G ⧸ I).out) m = m := m.2 _ h1
  have h3 : ρ (g : G ⧸ I).out m = ρ g m := by
    calc ρ (g : G ⧸ I).out m = ρ (g * (g⁻¹ * (g : G ⧸ I).out)) m := by rw [mul_inv_cancel_left]
      _ = ρ g (ρ (g⁻¹ * (g : G ⧸ I).out) m) := by rw [map_mul ρ g]; rfl
      _ = ρ g m := by rw [h2]
  rw [← h3]
  simp [hkEv_phi]

private theorem hkEv_phi_equiv (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) (h : G)
    (a : MonoidAlgebra A (G ⧸ I)) : hkEv_phi ρ I m (permRep A I h a) = ρ h (hkEv_phi ρ I m a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single q c =>
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [Representation.ofMulAction_single]
    have : h • (g : G ⧸ I) = ((h * g : G) : G ⧸ I) := rfl
    rw [this, hkEv_phi_single, hkEv_phi_single, map_smul, map_mul]
    rfl

private noncomputable def hkEv_psi (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    fixd (permRep A I) I →ₗ[A] fixd ρ I :=
  (hkEv_phi ρ I m).restrict (fun a ha u hu => by rw [← hkEv_phi_equiv, ha u hu])

private theorem hkEv_psi_hk (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (m : fixd ρ I)
    (x : G) (a : fixd (permRep A I) I) :
    hkEv_psi ρ I m (hk (permRep A I) I x a) = hk ρ I x (hkEv_psi ρ I m a) := by
  apply Subtype.ext
  rw [hkEv_coe ρ I hI]
  change hkEv_phi ρ I m (hk (permRep A I) I x a : MonoidAlgebra A (G ⧸ I)) = dc ρ I I x (hkEv_phi ρ I m a)
  rw [hkEv_coe _ I hI]
  exact (UpperTheory.V.Hi.dcSum A G _ (permRep A I) I I x (hI x)).2.2.2 A M ρ
    (hkEv_phi ρ I m).toAddMonoidHom (hkEv_phi_equiv ρ I m) a

private theorem hkEv_psi_surj (ρ : Representation A G M) (I : Subgroup G) (m : fixd ρ I) :
    ∃ a, hkEv_psi ρ I m a = m := by
  refine ⟨⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => ?_⟩, Subtype.ext ?_⟩
  · rw [Representation.ofMulAction_single]
    congr 1
    change ((u * 1 : G) : G ⧸ I) = _
    exact QuotientGroup.eq.mpr (by simpa using hu)
  · change hkEv_phi ρ I m (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = m
    rw [hkEv_phi_single]
    simp

private def hkEv_R (ρ : Representation A G M) (I : Subgroup G)
    (T : Module.End A (fixd (permRep A I) I)) (E : Module.End A (fixd ρ I)) : Prop :=
  ∀ m a, hkEv_psi ρ I m (T a) = E (hkEv_psi ρ I m a)

private theorem hkEv_uniq {ρ : Representation A G M} {I : Subgroup G}
    {T : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T E') : E = E' := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨a, ha⟩ := hkEv_psi_surj ρ I m
  rw [← ha, ← h, ← h']

private theorem hkEv_alg (ρ : Representation A G M) (I : Subgroup G) (c : A) :
    hkEv_R ρ I (algebraMap A _ c) (algebraMap A _ c) := fun m a => by
  simp only [Module.algebraMap_end_apply, map_smul]

private theorem hkEv_add {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T + T') (E + E') := fun m a => by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), h, h']

private theorem hkEv_mul {ρ : Representation A G M} {I : Subgroup G}
    {T T' : Module.End A (fixd (permRep A I) I)} {E E' : Module.End A (fixd ρ I)}
    (h : hkEv_R ρ I T E) (h' : hkEv_R ρ I T' E') : hkEv_R ρ I (T * T') (E * E') := fun m a => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h, h']

private theorem hkEv_ex (ρ : Representation A G M) (I : Subgroup G) (hI : HeckePair I) (T : HkAlg A I) :
    ∃ E, hkEv_R ρ I T.1 E := by
  obtain ⟨T, hT⟩ := T
  induction hT using Algebra.adjoin_induction with
  | mem T h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨hk ρ I x, fun m a => hkEv_psi_hk ρ I hI m x a⟩
  | algebraMap c => exact ⟨_, hkEv_alg ρ I c⟩
  | add T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_add h h'⟩
  | mul T T' _ _ h h' =>
    obtain ⟨E, h⟩ := h
    obtain ⟨E', h'⟩ := h'
    exact ⟨_, hkEv_mul h h'⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.hkEv :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G), HeckePair I → ∃ ev : HkAlg A I →ₐ[A] Module.End A (fixd ρ I), ∀ x : G, ev (hT A I x) = hk ρ I x := by
  intro A G M _ _ _ _ ρ I hI
  choose f hf using hkEv_ex ρ I hI
  have halg : ∀ c : A, f (algebraMap A _ c) = algebraMap A _ c := fun c =>
    hkEv_uniq (hf _) (hkEv_alg ρ I c)
  refine ⟨{ toFun := f
            map_one' := by simpa using halg 1
            map_mul' := fun T T' => hkEv_uniq (hf _) (hkEv_mul (hf T) (hf T'))
            map_zero' := by simpa using halg 0
            map_add' := fun T T' => hkEv_uniq (hf _) (hkEv_add (hf T) (hf T'))
            commutes' := halg }, fun x => ?_⟩
  exact hkEv_uniq (hf _) (fun m a => hkEv_psi_hk ρ I hI m x a)
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem inj_of_sandwich {R Q F ι : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Fintype ι] (g : (ι → R) →ₗ[R] Q) (f : Q →ₗ[R] F)
    (e : F ≃ₗ[R] (ι → R)) (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Injective f := by
  have hs : Function.Surjective (e.toLinearMap ∘ₗ f ∘ₗ g) := e.surjective.comp (hf.comp hg)
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  obtain ⟨x, rfl⟩ := hg a
  obtain ⟨y, rfl⟩ := hg b
  have : x = y := hi (by simp [hab])
  rw [this]

theorem UpperTheory.V.AlgebraTools.groupRing_ker :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) → Function.Surjective φ →
      RingHom.ker φ = Ideal.span (Set.range fun s => (1 + MvPowerSeries.X s : MvPowerSeries σ Λ) ^ l ^ e s - 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e φ hφ hsurj
  haveI : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  set w : σ → MvPowerSeries σ Λ := fun s => (1 + MvPowerSeries.X s) ^ l ^ e s - 1 with hw
  set I : Ideal (MvPowerSeries σ Λ) := Ideal.span (Set.range w) with hI
  have hle : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    have h1 : (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))) :
        ∀ s, Multiplicative (ZMod (l ^ e s))) ^ (l ^ e s) = 1 := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
        Pi.mulSingle_one]
    simp only [SetLike.mem_coe, RingHom.mem_ker, hw, map_sub, map_pow, hφ, map_one]
    rw [← map_pow, h1, map_one, sub_self]
  have hwm : ∀ s, w s - MvPowerSeries.X s ^ (l ^ e s) ∈
      Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
    intro s
    obtain ⟨m, hm⟩ : ∃ m, l ^ e s = m + 1 := ⟨l ^ e s - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos _)).symm⟩
    have hlC : ((l : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := Λ))]
      exact Ideal.mem_map_of_mem _ hlm
    simp only [hw]
    rw [add_comm, add_pow, hm, Finset.sum_range_succ, Finset.sum_range_succ']
    have key : ∀ k ∈ Finset.range m, MvPowerSeries.X s ^ (k + 1) * (1 : MvPowerSeries σ Λ) ^ (m + 1 - (k + 1)) *
        (((m + 1).choose (k + 1) : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      intro k hk
      have hd : l ∣ (m + 1).choose (k + 1) := by
        rw [← hm]
        refine hl.dvd_choose_pow (Nat.succ_ne_zero k) ?_
        rw [hm]; have := Finset.mem_range.mp hk; omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hlC)
    have hsum := Ideal.sum_mem _ key
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
      Nat.sub_zero, one_mul] at hsum ⊢
    convert hsum using 1
    ring
  have hIφ : ∀ a ∈ I, φ a = 0 := fun a ha => hle ha
  refine le_antisymm ?_ hle
  have hspan := UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials Λ σ (fun s => l ^ e s) w hwm
  let ψ := Ideal.Quotient.liftₐ I φ hIφ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  let v := fun α : ((s : σ) → Fin (l ^ e s)) => Ideal.Quotient.mk I (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
  have hg : Function.Surjective (Fintype.linearCombination Λ v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  let eqv : ((s : σ) → Fin (l ^ e s)) ≃ (∀ s, Multiplicative (ZMod (l ^ e s))) :=
    Equiv.piCongrRight fun s => (ZMod.finEquiv (l ^ e s)).toEquiv.trans Multiplicative.ofAdd
  let E : MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) ≃ₗ[Λ] (((s : σ) → Fin (l ^ e s)) → Λ) :=
    (MonoidAlgebra.coeffLinearEquiv Λ).trans
      ((Finsupp.linearEquivFunOnFinite Λ Λ _).trans (LinearEquiv.funCongrLeft Λ Λ eqv))
  have hinj := inj_of_sandwich (Fintype.linearCombination Λ v) ψ.toLinearMap E hg hψs
  intro x hx
  have h0 : ψ (Ideal.Quotient.mk I x) = 0 := hx
  have : Ideal.Quotient.mk I x = 0 := hinj (by simpa using h0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem tc_mod (R : Type) [CommRing R] (a : Ideal R) (k : ℕ) (N : Type) [AddCommGroup N]
    [Module R N] (h : (a ^ k • ⊤ : Submodule R N) = ⊥) :
    ∃ _ : Module (AdicCompletion a R) N, ∀ (s : AdicCompletion a R) (r : R),
      AdicCompletion.evalₐ a k s = Ideal.Quotient.mk _ r → ∀ x : N, s • x = r • x := by
  have ht : Module.IsTorsionBySet R N ((a ^ k : Ideal R) : Set R) := fun x b => by
    have hb : (b : R) • x ∈ (a ^ k • ⊤ : Submodule R N) :=
      Submodule.smul_mem_smul b.2 Submodule.mem_top
    rw [h] at hb
    exact (Submodule.mem_bot R).mp hb
  letI iq : Module (R ⧸ a ^ k) N := ht.module
  letI inst : Module (AdicCompletion a R) N :=
    Module.compHom N (AdicCompletion.evalₐ a k).toRingHom
  refine ⟨inst, fun s r hs x => ?_⟩
  show (AdicCompletion.evalₐ a k s) • x = r • x
  rw [hs]
  exact ht.mk_smul r x

private theorem tc_eval (R : Type) [CommRing R] (a : Ideal R) (k : ℕ) (s : AdicCompletion a R) :
    ∃ r : R, AdicCompletion.evalₐ a (k + 1) s = Ideal.Quotient.mk _ r ∧
      AdicCompletion.evalₐ a k s = Ideal.Quotient.mk _ r := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective a R s
  refine ⟨x (k + 1), AdicCompletion.evalₐ_mk a (k + 1) x, ?_⟩
  rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hc := x.property (Nat.le_succ k)
  rw [SModEq.sub_mem] at hc
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hc

private theorem tc_smul {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (a : Ideal R) (k : ℕ)
    (N : Type) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (x : N) :
    x ∈ ((a.map (algebraMap R S)) ^ k • ⊤ : Submodule S N) ↔ x ∈ (a ^ k • ⊤ : Submodule R N) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]

theorem UpperTheory.V.AlgebraTools.exists_tower_limit_completion :
    ∀ (R : Type) [CommRing R] (a : Ideal R), a.FG → ∀ (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (π : ∀ k, P (k + 1) →ₗ[R] P k),
      (∀ k, Function.Surjective (π k)) → (∀ k, LinearMap.ker (π k) = a ^ k • ⊤) → (∀ k, (a ^ k • ⊤ : Submodule R (P k)) = ⊥) →
      Module.Finite R (P 1) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module (AdicCompletion a R) M) (_ : IsScalarTower R (AdicCompletion a R) M)
        (q : ∀ k, M →ₗ[R] P k), Module.Finite (AdicCompletion a R) M ∧ (∀ k, Function.Surjective (q k)) ∧
        (∀ k, LinearMap.ker (q k) = a ^ k • ⊤) ∧ (∀ k x, π k (q (k + 1) x) = q k x) ∧
        ∀ x : M, (∀ k, q k x = 0) → x = 0 := by
  intro R _ a ha P _ _ π hπ hker hkill hfin
  haveI : IsAdicComplete (a.map (algebraMap R (AdicCompletion a R))) (AdicCompletion a R) :=
    AdicCompletion.isAdicComplete_self a ha
  choose inst hinst using fun k => tc_mod R a k (P k) (hkill k)
  haveI tow : ∀ k, IsScalarTower R (AdicCompletion a R) (P k) := fun k => ⟨fun r s x => by
    obtain ⟨r₀, h₀⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ a k s)
    have h1 : AdicCompletion.evalₐ a k (r • s) = Ideal.Quotient.mk _ (r * r₀) := by
      rw [map_smul, ← h₀, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    rw [hinst k (r • s) (r * r₀) h1, hinst k s r₀ h₀.symm, mul_smul]⟩
  let π' : ∀ k, P (k + 1) →ₗ[AdicCompletion a R] P k := fun k =>
    { toFun := π k
      map_add' := (π k).map_add
      map_smul' := fun s x => by
        obtain ⟨r, h1, h2⟩ := tc_eval R a k s
        show π k (s • x) = s • π k x
        rw [hinst (k + 1) s r h1, hinst k s r h2, (π k).map_smul] }
  have hker' : ∀ k, LinearMap.ker (π' k) = (a.map (algebraMap R (AdicCompletion a R))) ^ k • ⊤ := by
    intro k
    ext x
    rw [tc_smul (S := AdicCompletion a R) a k (P (k + 1)) x, ← hker k, LinearMap.mem_ker,
      LinearMap.mem_ker]
    all_goals exact Iff.rfl
  have hkill' : ∀ k, ((a.map (algebraMap R (AdicCompletion a R))) ^ k • ⊤ :
      Submodule (AdicCompletion a R) (P k)) = ⊥ := by
    intro k
    rw [eq_bot_iff]
    intro x hx
    rw [tc_smul (S := AdicCompletion a R) a k (P k) x, hkill k] at hx
    exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot _).mp hx)
  have hfin' : Module.Finite (AdicCompletion a R) (P 1) :=
    Module.Finite.of_restrictScalars_finite R _ (P 1)
  obtain ⟨M, _, _, q, hfinM, hsurj, hkerq, hcompat, hsep⟩ :=
    UpperTheory.V.AlgebraTools.exists_tower_limit (AdicCompletion a R) (a.map (algebraMap R (AdicCompletion a R)))
      P π' (fun k => hπ k) hker' hkill' hfin'
  letI : Module R M := Module.compHom M (algebraMap R (AdicCompletion a R))
  haveI : IsScalarTower R (AdicCompletion a R) M := ⟨fun r s m => by
    show (r • s) • m = (algebraMap R (AdicCompletion a R) r) • (s • m)
    rw [Algebra.smul_def, mul_smul]⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    fun k => (q k).restrictScalars R, hfinM, fun k => hsurj k, ?_, fun k x => hcompat k x,
    fun x hx => hsep x hx⟩
  intro k
  ext x
  rw [LinearMap.mem_ker, ← tc_smul (S := AdicCompletion a R) a k M x, ← hkerq k, LinearMap.mem_ker]
  all_goals exact Iff.rfl
end

section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.dim_minimalPrime_eq :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type) [AddCommGroup M] [Module B M]
      [Module.Finite B M] (xs : List B), (∀ x ∈ xs, x ∈ maximalIdeal B) → RingTheory.Sequence.IsWeaklyRegular M xs →
      Module.supportDim B M ≤ (xs.length : ℕ) →
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = (xs.length : ℕ) := by
  intro B _ _ _ M _ _ _ xs hxs hreg hdim Z hZ
  apply le_antisymm
  · calc ringKrullDim (B ⧸ Z) ≤ ringKrullDim (B ⧸ Module.annihilator B M) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ.1.2)
            (Ideal.Quotient.factor_surjective hZ.1.2)
      _ = Module.supportDim B M := (Module.supportDim_eq_ringKrullDim_quotient_annihilator B M).symm
      _ ≤ _ := hdim
  · exact GlobalTheory.length_le_ringKrullDim_quotient_of_isAssociatedPrime hxs hreg
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B M hZ)
end
