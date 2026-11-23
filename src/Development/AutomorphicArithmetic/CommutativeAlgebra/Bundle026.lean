module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.UPel.HT.EtLev

private theorem eq_zero_or_of_mul_eq_zero_of_add_reg {A : Type} [CommRing A] [IsLocalRing A] [IsIntegrallyClosed A]
    {a b : A} (hab : a * b = 0) (hreg : a + b ∈ nonZeroDivisors A) : a = 0 ∨ b = 0 := by
  let F := FractionRing A
  have hinj : Function.Injective (algebraMap A F) := IsLocalization.injective F le_rfl
  let e : F := IsLocalization.mk' F a (⟨a + b, hreg⟩ : nonZeroDivisors A)
  have hu : IsUnit (algebraMap A F (a + b)) := IsLocalization.map_units F (⟨a + b, hreg⟩ : nonZeroDivisors A)
  have he : e * algebraMap A F (a + b) = algebraMap A F a := IsLocalization.mk'_spec F a ⟨a + b, hreg⟩
  have hidem : e * e = e := by
    apply hu.mul_right_cancel
    apply hu.mul_right_cancel
    have h2 : algebraMap A F a * algebraMap A F (a + b) = algebraMap A F a * algebraMap A F a := by
      rw [← map_mul, ← map_mul, mul_add, hab, add_zero]
    calc e * e * algebraMap A F (a + b) * algebraMap A F (a + b)
        = (e * algebraMap A F (a + b)) * (e * algebraMap A F (a + b)) := by ring
      _ = algebraMap A F a * algebraMap A F a := by rw [he]
      _ = algebraMap A F a * algebraMap A F (a + b) := h2.symm
      _ = e * algebraMap A F (a + b) * algebraMap A F (a + b) := by rw [he]
  have hint : IsIntegral A e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by simp)
    · simp [Polynomial.eval₂_sub, pow_two, hidem]
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hint
  have hcc : c * c = c := hinj (by rw [map_mul, hc, hidem])
  have hca : c * (a + b) = a := hinj (by rw [map_mul, hc, he])
  have h01 : c = 0 ∨ c = 1 := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
    · right
      exact h.mul_left_cancel (by rw [hcc, _root_.mul_one])
    · left
      have : (1 - c) * c = 0 := by rw [sub_mul, _root_.one_mul, hcc, sub_self]
      exact h.mul_right_eq_zero.1 this
  rcases h01 with rfl | rfl
  · left
    simpa using hca.symm
  · right
    simpa using hca

private theorem isDomain_of_isReduced_of_isIntegrallyClosed (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced A] [IsIntegrallyClosed A] : IsDomain A := by
  classical
  by_contra hdom
  have hbot : ¬ (⊥ : Ideal A).IsPrime := fun h => hdom (IsDomain.of_bot_isPrime A)
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hzero : ∀ x : A, (∀ Q ∈ minimalPrimes A, x ∈ Q) → x = 0 := fun x hx => by
    have : x ∈ (⊥ : Ideal A).radical := by
      rw [← Ideal.sInf_minimalPrimes]
      exact (Submodule.mem_sInf).2 hx
    obtain ⟨n, hn⟩ := this
    exact (IsNilpotent.eq_zero ⟨n, by simpa using hn⟩)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := IsLocalRing.maximalIdeal A) bot_le
  have hPp : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  have hprime : ∀ Q ∈ minimalPrimes A, Q.IsPrime := fun Q hQ => Ideal.minimalPrimes_isPrime hQ
  have hle : ∀ Q ∈ minimalPrimes A, ∀ Q' ∈ minimalPrimes A, Q ≤ Q' → Q = Q' := fun Q hQ Q' hQ' h =>
    le_antisymm h (hQ'.2 hQ.1 h)
  let T : Finset (Ideal A) := hfin.toFinset.erase P
  have hT : ∀ Q ∈ T, Q ∈ minimalPrimes A ∧ Q ≠ P := fun Q hQ => by
    have := Finset.mem_erase.1 hQ
    exact ⟨hfin.mem_toFinset.1 this.2, this.1⟩
  have hTm : ∀ Q ∈ minimalPrimes A, Q ≠ P → Q ∈ T := fun Q hQ h =>
    Finset.mem_erase.2 ⟨h, hfin.mem_toFinset.2 hQ⟩

  obtain ⟨a, haP, ha⟩ : ∃ a ∈ P, a ∉ ⋃ i ∈ (↑(insert ⊥ T) : Set (Ideal A)), (i : Set A) := by
    by_contra hcon
    push_neg at hcon
    have hsub : (P : Set A) ⊆ ⋃ i ∈ (↑(insert ⊥ T) : Set (Ideal A)), ((id i : Ideal A) : Set A) := hcon
    obtain ⟨Q, hQ, hPQ⟩ := (Ideal.subset_union_prime (⊥ : Ideal A) (⊥ : Ideal A)
      (fun i hi h1 _ => (hT i ((Finset.mem_insert.1 hi).resolve_left h1)).1 |> hprime i)).1 hsub
    rcases Finset.mem_insert.1 hQ with rfl | hQ
    · exact hbot ((le_bot_iff.1 hPQ) ▸ hPp)
    · exact (hT Q hQ).2 (hle P hP Q (hT Q hQ).1 hPQ).symm
  have ha0 : a ≠ 0 := fun h => ha (by
    simp only [Set.mem_iUnion]
    exact ⟨⊥, by simp, by simp [h]⟩)
  have haT : ∀ Q ∈ T, a ∉ Q := fun Q hQ h => ha (by
    simp only [Set.mem_iUnion]
    exact ⟨Q, by simp [hQ], h⟩)

  obtain ⟨b, hbT, hbP⟩ : ∃ b ∈ T.inf id, b ∉ P := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.IsPrime.inf_le' hPp).1 (show T.inf id ≤ P from hcon)
    exact (hT Q hQ).2 (hle Q (hT Q hQ).1 P hP hQP)
  have hbT' : ∀ Q ∈ T, b ∈ Q := fun Q hQ => by
    have := Finset.inf_le (f := id) hQ
    exact this hbT
  have hab : a * b = 0 := hzero _ fun Q hQ => by
    by_cases h : Q = P
    · exact h ▸ Ideal.mul_mem_right _ _ haP
    · exact Ideal.mul_mem_left _ _ (hbT' Q (hTm Q hQ h))
  have hreg : a + b ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hzero x fun Q hQ => ?_
    have hQp := hprime Q hQ
    have hx' : x * (a + b) ∈ Q := hx ▸ Q.zero_mem
    refine (hQp.mem_or_mem hx').resolve_right fun hs => ?_
    by_cases h : Q = P
    · subst h
      exact hbP ((Q.add_mem_iff_right haP).1 hs)
    · have hm := hTm Q hQ h
      exact haT Q hm ((Q.add_mem_iff_left (hbT' Q hm)).1 hs)
  rcases eq_zero_or_of_mul_eq_zero_of_add_reg hab hreg with h | h
  · exact ha0 h
  · exact hbP (h ▸ P.zero_mem)
end

section

noncomputable section

open TensorProduct Polynomial

private theorem isIntegrallyClosed_of_AIC (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.EtC.AIC T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      have h1 : p = 1 := hp.natDegree_eq_zero.1 h
      simp [h1] at hpx
    · obtain ⟨a, ha⟩ := hT p hp (h ▸ hpos)
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 ha
      have hqm : q.Monic := (monic_X_sub_C a).of_mul_monic_left (hq ▸ hp)
      have hdeg : p.natDegree = 1 + q.natDegree := by
        rw [hq, (monic_X_sub_C a).natDegree_mul hqm, natDegree_X_sub_C]
      rw [hq, eval₂_mul] at hpx
      rcases mul_eq_zero.1 hpx with h1 | h1
      · refine ⟨a, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.1 h1).symm
      · exact ih q.natDegree (by omega) q hqm h1 rfl

private theorem exists_of_idem (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] (z : C ⊗[T] FractionRing T) (hz : z * z = z) :
    ∃ s : C, algebraMap C (C ⊗[T] FractionRing T) s = z := by
  have hint : IsIntegral C z := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_X_le (by norm_num)), ?_⟩
    simp [eval₂_sub, pow_two, hz]
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := T) (S := C)
    (B := FractionRing T)).2 ⟨z, hint⟩
  have ht' : Algebra.TensorProduct.map (AlgHom.id C C)
      (integralClosure T (FractionRing T)).val t = z := congrArg Subtype.val ht
  rw [← ht']
  clear ht ht'
  induction t with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul x y =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) y.2
    refine ⟨r • x, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem core (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] {n : ℕ}
    (g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T)) :
    ∃ (e : Fin n → C), CompleteOrthogonalIdempotents e ∧
      ∀ j, IsDomain (Localization.Away (e j)) := by
  classical
  let G : C →+* (Fin n → FractionRing T) :=
    g.toRingHom.comp (algebraMap C (C ⊗[T] FractionRing T))
  have hι : Function.Injective (algebraMap C (C ⊗[T] FractionRing T)) :=
    Algebra.TensorProduct.includeLeft_injective (S := T)
      (IsFractionRing.injective T (FractionRing T))
  have hG : Function.Injective G := g.injective.comp hι
  have hex : ∀ j : Fin n, ∃ s : C, G s = Pi.single j 1 := by
    intro j
    obtain ⟨s, hs⟩ := exists_of_idem T C (g.symm (Pi.single j 1)) (by
      apply g.injective
      rw [map_mul, g.apply_symm_apply, ← Pi.single_mul, one_mul])
    exact ⟨s, by simp [G, hs]⟩
  choose c hc using hex
  have hcoi : CompleteOrthogonalIdempotents c := by
    refine ⟨⟨fun i => hG ?_, fun i j hij => hG ?_⟩, hG ?_⟩
    · rw [map_mul, hc, ← Pi.single_mul, one_mul]
    · rw [map_mul, hc, hc, map_zero]
      ext k
      by_cases h : k = i
      · subst h; simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne h]

    · rw [map_sum, map_one]
      simp only [hc]
      exact Finset.univ_sum_single 1
  refine ⟨c, hcoi, fun j => ?_⟩
  have hidem : IsIdempotentElem (c j) := hcoi.idem j
  let φ : C →+* FractionRing T := (Pi.evalRingHom _ j).comp G
  have hφ : φ (c j) = 1 := by simp [φ, hc]
  have hu : IsUnit (φ (c j)) := by rw [hφ]; exact isUnit_one
  let ψ : Localization.Away (c j) →+* FractionRing T := IsLocalization.Away.lift (c j) hu
  have hψ : ∀ x, ψ (algebraMap C _ x) = φ x := fun x => IsLocalization.Away.lift_eq (c j) hu x
  have hsurj : Function.Surjective (algebraMap C (Localization.Away (c j))) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (c j) hidem
  have hone : algebraMap C (Localization.Away (c j)) (c j) = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit (c j))).1
      (hidem.map _)
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := hsurj a
    rw [hψ] at ha
    have hx : x * c j = 0 := by
      apply hG
      rw [map_mul, hc, map_zero]
      ext k
      by_cases h : k = j
      · subst h
        simpa [φ] using ha
      · simp [Pi.single_eq_of_ne h]
    have := congrArg (algebraMap C (Localization.Away (c j))) hx
    rwa [map_mul, hone, mul_one, map_zero] at this
  exact hinj.isDomain ψ

theorem UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale :
    ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], GlobalTheory.EtC.AIC T →
      ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j)) := by
  intro T C _ _ _ _ _ hT
  haveI := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := isIntegrallyClosed_of_AIC T hT
  let e0 := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) (FractionRing T ⊗[T] C)
  haveI := Algebra.FormallyUnramified.finite_of_free (FractionRing T) (FractionRing T ⊗[T] C)
  haveI : IsArtinianRing (FractionRing T ⊗[T] C) := isArtinian_of_tower (FractionRing T) inferInstance
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (PrimeSpectrum (FractionRing T ⊗[T] C))
  let g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T) :=
    ((Algebra.TensorProduct.comm T C (FractionRing T)).toRingEquiv.trans e0.toRingEquiv).trans
      (RingEquiv.piCongrLeft (fun _ : Fin n => FractionRing T) eq)
  obtain ⟨e, h1, h2⟩ := core T C g
  exact ⟨n, e, h1, h2⟩

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private noncomputable def UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx {R : Type} [CommRing R] {L B : Cx R} (ρ : SemiMap L B) :
    SemiMap L ((rcx (Int.castRingHom R)).obj B) where
  app U s := ((idSemi (Int.castRingHom R) B).app U s).comp (ρ.app U s)
  nat g s a := ((idSemi (Int.castRingHom R) B).nat g s _).trans
    (congrArg ((idSemi (Int.castRingHom R) B).app _ s) (ρ.nat g s a))
  comm U s t a := ((idSemi (Int.castRingHom R) B).comm U s t _).trans
    (congrArg ((idSemi (Int.castRingHom R) B).app U t) (ρ.comm U s t a))

theorem UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward :
    ∀ (R : Type) [CommRing R] (L B : Cx R) (ρ : SemiMap L B) (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains ℤ).obj E) ρ.toZ n) → Function.Bijective (ρ.op.app E n) := by
  intro R _ L B ρ E n hb
  have idBij : ∀ (K : Cx R) (U : Scheme.{0}) (s : ℤ),
      Function.Bijective ((idSemi (Int.castRingHom R) K).app U s) :=
    fun _ _ _ => ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩
  have bL := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) L) (idSemi (Int.castRingHom R) L) (𝟙 _)
    (fun _ _ _ => rfl)).2 (idBij L) E n
  have bB := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) B) (idSemi (Int.castRingHom R) B) (𝟙 _)
    (fun _ _ _ => rfl)).2 (idBij B) E n
  have key : ∀ x, (idSemi (Int.castRingHom R) B).op.app E n (ρ.op.app E n x) =
      cpush ((chains ℤ).obj E) ρ.toZ n ((idSemi (Int.castRingHom R) L).op.app E n x) := by
    intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).1 E n α
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (idSemi (Int.castRingHom R) B)).1 E n β
    have h1 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R R ρ).2 E n α β hβ
    have h2 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (idSemi (Int.castRingHom R) B)).2 E n β γ hγ
    have h3 := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ (UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx ρ)).2 E n α γ
      (fun p s h U y => (hγ p s h U y).trans (congrArg _ (hβ p s h U y)))
    rw [h1, h2, ← h3]
    exact (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ (idSemi (Int.castRingHom R) L) (UpperTheory.bijective_semiMap_op_of_bijective_cochain_pushforward.toRcx ρ) ρ.toZ
      (fun _ _ _ => rfl)).1 E n _
  have comp : Function.Bijective
      ((idSemi (Int.castRingHom R) B).op.app E n ∘ ρ.op.app E n) := by
    have : ((idSemi (Int.castRingHom R) B).op.app E n ∘ ρ.op.app E n) =
        (cpush ((chains ℤ).obj E) ρ.toZ n ∘ (idSemi (Int.castRingHom R) L).op.app E n) := funext key
    rw [this]
    exact hb.comp bL
  exact (Function.Bijective.of_comp_iff' bB _).1 comp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

namespace UpperTheory.Lev

section Twist

variable {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop}

private theorem ev_MN (I : GTateIso G k Q act e) {n : ℕ} (hn : 0 < n) {a b : G.La} (h : MN n a b) :
    I.ev n a = I.ev n b := by
  obtain ⟨c, rfl⟩ := h
  rw [I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]

private theorem zpow_congr_of_dvd {u : kˣ} {n : ℕ} (hu : u ^ n = 1) {a b : ℤ} (h : (n : ℤ) ∣ a - b) :
    u ^ a = u ^ b := by
  obtain ⟨c, hc⟩ := h
  have hab : a = b + n * c := by linarith
  rw [hab, zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, _root_.mul_one]

private theorem prim_zpow {u : kˣ} {n : ℕ} (hu : IsPrimitiveRoot u n) {v : ℤ}
    (hc : IsCoprime v (n : ℤ)) : IsPrimitiveRoot (u ^ v) n := by
  exact hu.zpow_of_gcd_eq_one v (Int.isCoprime_iff_gcd_eq_one.mp hc)

end Twist

end UpperTheory.Lev

theorem UpperTheory.exists_gTateIso_twist_of_similitude :
    ∀ {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
        (I : GTateIso G k Q act e) (g : GSim G),
        ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g.f n x) := by
  intro G k _ Q _ act e I g
  have hφadd : ∀ n, 0 < n → ∀ x y, I.ev n (g.f n (x + y)) = I.ev n (g.f n x) * I.ev n (g.f n y) :=
    fun n hn x y => by rw [Lev.ev_MN I hn ((g.sim n hn).add x y), I.add]
  have hφpow : ∀ n, 0 < n → ∀ (j : ℕ) y, I.ev n (g.f n (j • y)) = I.ev n (g.f n y) ^ j := by
    intro n hn j y
    induction j with
    | zero =>
      rw [zero_smul, pow_zero]
      have h0 := hφadd n hn 0 0
      rw [add_zero] at h0
      exact (mul_eq_left.mp h0.symm)
    | succ j ih => rw [succ_nsmul, hφadd n hn, ih, pow_succ]
  refine ⟨⟨fun n => I.ζ n ^ g.ν n, ?_, ?_, fun n x => if n = 0 then I.ev 0 x else I.ev n (g.f n x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    exact Lev.prim_zpow (I.ζ_prim n hn) (g.sim n hn).cop
  · intro n m hn hm
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one (g.νtower n m hn hm)
  · intro n x y
    by_cases hn : n = 0
    · simp only [hn, if_true, I.add]
    · simp only [hn, if_false]
      exact hφadd n (Nat.pos_of_ne_zero hn) x y
  · intro n b x
    by_cases hn : n = 0
    · simp only [hn, if_true, I.lin]
    · simp only [hn, if_false]
      rw [Lev.ev_MN I (Nat.pos_of_ne_zero hn) ((g.sim n (Nat.pos_of_ne_zero hn)).lin b x), I.lin]
  · intro n hn x
    simp only [hn.ne', if_false]
    constructor
    · intro h1
      obtain ⟨y, hy⟩ := (I.ker n hn _).mp h1
      obtain ⟨c, hc⟩ := (g.sim n hn).inj x ⟨y, by rw [hy, zero_add]⟩
      exact ⟨c, by rw [hc, zero_add]⟩
    · rintro ⟨y, rfl⟩
      rw [hφpow n hn]
      exact (I.onto n hn _).mpr ⟨_, rfl⟩
  · intro n hn q
    simp only [hn.ne', if_false]
    rw [I.onto n hn]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := (g.sim n hn).surj z
      exact ⟨x, Lev.ev_MN I hn hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    simp only [(Nat.mul_pos hn hm).ne', hn.ne', if_false]
    rw [I.tower n m hn hm, Lev.ev_MN I hn (g.tower n m hn hm x)]
  · intro n hn x y
    simp only [hn.ne', if_false]
    have h := I.isom n hn (g.f n x) (g.f n y)
    have hd := ((g.sim n hn).isom x y)
    rw [Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one hd] at h
    rw [← zpow_mul]
    exact h
  · intro n hn x
    simp only [hn.ne', if_false]
end
