module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeterminantIdentities
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle017
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiDet :
    ∀ {n : ℕ} {B A H G : Type} [CommRing B] [CommRing A] [Group H] [Group G] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace G] (I : Ideal B) [IsHausdorff I B] (f : B →+* A), Function.Injective f → ∀ (π : H →* G), Function.Surjective π → Topology.IsQuotientMap π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (cp : H → B[X]), (∀ g, (cp g).map f = (ρ g).charpoly) → (∀ j, AdicCont I fun g => (cp g).coeff j) → (∀ U : Subgroup H, IsClosed (U : Set H) → ρ.ker ≤ U → π.ker ≤ U) → ∃ D : W.GDet n B G, (D.comap π).map f = W.GDet.ofRep ρ ∧ (∀ g, D.chi (MonoidAlgebra.single (π g) 1) = cp g) ∧ D.IsCont I :=
  _root_.UpperTheory.Reformulated.B.DeterminantIdentities.phiDet
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem pp_chi {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H] (f : B →+* A)
    (π : H →* G) (D : W.GDet n B G) (ρ : H →* Matrix (Fin n) (Fin n) A) (hD : (D.comap π).map f = W.GDet.ofRep ρ)
    (y : MonoidAlgebra B H) :
    (D.chi (MonoidAlgebra.mapDomainRingHom B π y)).map f =
      (W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f y)).charpoly := by
  have h : (D.comap π).chi y = D.chi (MonoidAlgebra.mapDomainRingHom B π y) := by
    change D.D B[X] (MonoidAlgebra.mapDomainRingHom B[X] π _) = D.D B[X] _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => simp
  rw [← h, ← (UpperTheory.V.AlgebraTools.Det.mapApi (D.comap π) f).1, hD, (UpperTheory.V.AlgebraTools.Det.repApi ρ).1]

private theorem pp_single {n : ℕ} {A H : Type} [CommRing A] [Group H] (ρ : H →* Matrix (Fin n) (Fin n) A) (g : H) (a : A) :
    W.GDet.repAlg ρ A (MonoidAlgebra.single g a) = a • ρ g := by
  simp [W.GDet.repAlg, MonoidAlgebra.lift_single]

private theorem pp_tr {n : ℕ} {A B G H : Type} [CommRing A] [CommRing B] [Group G] [Group H] (hn : 0 < n) (f : B →+* A)
    (hf : Function.Injective f)
    (π : H →* G) (D : W.GDet n B G) (ρ : H →* Matrix (Fin n) (Fin n) A) (hD : (D.comap π).map f = W.GDet.ofRep ρ)
    (h : H) (y : MonoidAlgebra B H) (hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f y) = 0) :
    D.tr (MonoidAlgebra.single (π h) 1 * MonoidAlgebra.mapDomainRingHom B π y) = 0 := by
  have e1 : MonoidAlgebra.single (π h) (1 : B) * MonoidAlgebra.mapDomainRingHom B π y =
      MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single h 1 * y) := by
    rw [map_mul]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  have e2 : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * y)) = 0 := by
    rw [map_mul, map_mul, hy, mul_zero]
  have hc := pp_chi f π D ρ hD (MonoidAlgebra.single h 1 * y)
  rw [e2, Matrix.charpoly_zero, Fintype.card_fin] at hc
  rw [e1]
  simp only [W.GDet.tr, W.GDet.lam]
  have h0 : f ((D.chi (MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single h 1 * y))).coeff (n - 1)) = 0 := by
    rw [← Polynomial.coeff_map, hc, Polynomial.coeff_X_pow]
    rw [if_neg (by omega)]
  rw [(map_eq_zero_iff f hf).1 h0, mul_zero]


theorem UpperTheory.V.Ws.phiPair :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} (r : W.Resid F O n) {B A H : Type} [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Group H], Function.Injective (algebraMap B A) → 0 < n → ∀ (π : H →* F.G₀), Function.Surjective π → ∀ (ρ : H →* Matrix (Fin n) (Fin n) A) (D : W.GDet n B F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Bˣ), (D.comap π).map (algebraMap B A) = W.GDet.ofRep ρ → D.IsCont (maximalIdeal B) → (∀ g, (D.chi (MonoidAlgebra.single (π g) 1)).map (res O B : B →+* ResidueField O) = ∏ i, (Polynomial.X - C (r.chib i (π g) : ResidueField O))) → (∀ v i, r.IsPsi v i (ψ v i)) → (∀ g, ∃ g', π g' = (F.conj (π g))⁻¹ ∧ (((F.eps O A (π g) ^ (1 - (n : ℤ)) : Aˣ) : A) • ρ g').charpoly = (ρ g).charpoly) → (∀ v, ∃ j : F.Gv v →* H, π.comp j = F.φ v ∧ W.HasFlag (ρ.toHomUnits.comp j) fun i => W.pushCh (algebraMap B A) (ψ v i)) → (∀ u, ∀ g ∈ r.Ip u, ∃ g', π g' = g ∧ ρ g' = 1) → ∃ p : W.Pair r B, p.D = D ∧ p.ψ = ψ := by
  intro l _ F O _ _ _ n r B A H _ _ _ _ _ _ _ _ hinj hn π hπ ρ D ψ hD hcont hred hpsi hstar hflag hI
  refine ⟨{ D := D, ψ := ψ, cont := hcont, red := ?_, psi := hpsi, P := ?_, Ord := ?_, I := ?_ }, rfl, rfl⟩
  · apply CA.d_gext
    intro g i _ _
    obtain ⟨g', rfl⟩ := hπ g
    have h1 : (D.map (res O B : B →+* ResidueField O)).chi (MonoidAlgebra.single (π g') 1) =
        r.Dbar.chi (MonoidAlgebra.single (π g') 1) := by
      have := (AlgebraTools.Det.mapApi D (res O B : B →+* ResidueField O)).1 (MonoidAlgebra.single (π g') 1)
      rw [MonoidAlgebra.mapRingHom_single, map_one] at this
      rw [this, hred, W.Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]
      simp [W.diagRep, Matrix.charpoly_diagonal]
    simp only [W.GDet.lam, h1]
  · intro i g
    obtain ⟨g0, rfl⟩ := hπ g
    obtain ⟨g', hg', hc⟩ := hstar g0
    have hs : F.star O B n (MonoidAlgebra.single (π g0) 1) =
        MonoidAlgebra.single (π g') ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B) := by
      rw [hg']
      simp [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single]
    have he : algebraMap B A ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((F.eps O A (π g0) ^ (1 - (n : ℤ)) : Aˣ) : A) := by
      have hu : Units.map (algebraMap B A : B →* A) (F.eps O B (π g0)) = F.eps O A (π g0) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O B A]
      rw [← hu, ← map_zpow (Units.map (algebraMap B A : B →* A))]
      rfl
    have h1 := pp_chi (algebraMap B A) π D ρ hD
      (MonoidAlgebra.single g' ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B))
    have h2 := pp_chi (algebraMap B A) π D ρ hD (MonoidAlgebra.single g0 1)
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single,
      pp_single, he] at h1
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single,
      pp_single, map_one, one_smul] at h2
    have hcc : D.chi (MonoidAlgebra.single (π g') ((F.eps O B (π g0) ^ (1 - (n : ℤ)) : Bˣ) : B)) =
        D.chi (MonoidAlgebra.single (π g0) 1) :=
      Polynomial.map_injective _ hinj (by rw [h1, h2, hc])
    simp only [W.GDet.lam, hs, hcc]
  · intro v g h
    obtain ⟨j, hj, hfl⟩ := hflag v
    obtain ⟨h', rfl⟩ := hπ h
    have hz := (AlgebraTools.Det.flagRel _ _ hfl).2 g
    have hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H (algebraMap B A)
        (List.ofFn fun i => MonoidAlgebra.single (j (g i)) (1 : B) - MonoidAlgebra.single 1 ((ψ v i (g i) : Bˣ) : B)).prod) = 0 := by
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, ← hz]
      congr 1
      refine List.ofFn_inj.2 (funext fun i => ?_)
      simp [pp_single, MonoidAlgebra.mapRingHom_single, W.mat]
    have := pp_tr hn (algebraMap B A) hinj π D ρ hD h' _ hy
    have hj' : ∀ x, π (j x) = F.φ v x := fun x => by rw [← hj]; rfl
    have e : MonoidAlgebra.mapDomainRingHom B π
        (List.ofFn fun i => MonoidAlgebra.single (j (g i)) (1 : B) - MonoidAlgebra.single 1 ((ψ v i (g i) : Bˣ) : B)).prod =
        F.oEl v (ψ v) g := by
      rw [map_list_prod, List.map_ofFn]
      simp only [W.GFrame.oEl]
      congr 1
      refine List.ofFn_inj.2 (funext fun i => ?_)
      rw [Function.comp_apply, map_sub, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_single, hj', map_one]
    rw [e] at this
    exact this
  · intro u g hg h
    obtain ⟨g', rfl, hg'⟩ := hI u g hg
    obtain ⟨h', rfl⟩ := hπ h
    have hy : W.GDet.repAlg ρ A (MonoidAlgebra.mapRingHom H (algebraMap B A) (MonoidAlgebra.single g' 1 - 1)) = 0 := by
      rw [map_sub, map_one, MonoidAlgebra.mapRingHom_single, map_one, map_sub, pp_single, hg', one_smul, map_one, sub_self]
    have := pp_tr hn (algebraMap B A) hinj π D ρ hD h' _ hy
    have e : MonoidAlgebra.mapDomainRingHom B π (MonoidAlgebra.single g' (1 : B) - 1) = MonoidAlgebra.single (π g') 1 - 1 := by
      rw [map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    rw [e] at this
    exact this
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem coprime_of_residue {B : Type} [CommRing B] [IsLocalRing B] (p q : B[X]) (hp : p.Monic)
    (h : IsCoprime (p.map (residue B)) (q.map (residue B))) : IsCoprime p q := by
  rw [← isUnit_resultant_iff_isCoprime hp]
  have hp' : (p.map (residue B)).Monic := hp.map _
  have h1 := (isUnit_resultant_iff_isCoprime hp').2 h
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (natDegree_map_le (f := residue B) (p := q))
  have h2 : residue B (p.resultant q) = (p.map (residue B)).resultant (q.map (residue B)) := by
    rw [← resultant_map_map, hj, resultant_add_right_deg _ _ _ _ _ le_rfl,
      ← hp.natDegree_map (residue B), hp'.coeff_natDegree, one_pow, one_mul]
  rw [← h2] at h1
  exact (isUnit_map_iff (residue B) _).1 h1

theorem UpperTheory.V.Ws.phiRigid :
    ∀ {B E k : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field k] (f : B →+* k), (∀ x, f x = 0 → x ∈ maximalIdeal B) → ∀ (M : E) (p : B[X]) (d m : ℕ), p.Monic → aeval M p = 0 → p.map f = (Polynomial.X - 1) ^ d → M ^ m = 1 → IsUnit (m : B) → M = 1 := by
  intro B E k _ _ _ _ _ f hf M p d m hp hM hpf hm hu
  have h1 : p.map (residue B) = (Polynomial.X - 1) ^ d := by
    have h0 : (p - (Polynomial.X - 1) ^ d).map f = 0 := by
      simp [Polynomial.map_sub, Polynomial.map_pow, hpf]
    have h2 : (p - (Polynomial.X - 1) ^ d).map (residue B) = 0 := by
      ext i
      rw [coeff_map, coeff_zero, residue_eq_zero_iff]
      apply hf
      rw [← coeff_map, h0, coeff_zero]
    simpa [Polynomial.map_sub, Polynomial.map_pow, sub_eq_zero] using h2
  set S : B[X] := ∑ i ∈ Finset.range m, Polynomial.X ^ i with hS
  have hc : IsCoprime p S := by
    apply coprime_of_residue p S hp
    rw [h1]
    apply IsCoprime.pow_left
    have hirr : Irreducible (Polynomial.X - C (1 : ResidueField B)) := irreducible_X_sub_C 1
    rw [← C_1, hirr.coprime_iff_not_dvd, dvd_iff_isRoot]
    have h3 : ((m : ℕ) : ResidueField B) ≠ 0 := by
      have := (hu.map (residue B)).ne_zero
      rwa [map_natCast] at this

    simpa [hS, Polynomial.map_sum, eval_finsetSum] using h3
  obtain ⟨a, b, hab⟩ := hc
  have h4 : aeval M b * aeval M S = 1 := by
    have := congrArg (aeval M) hab
    simpa [hM] using this
  have h5 : aeval M S * (M - 1) = 0 := by
    have : aeval M S = ∑ i ∈ Finset.range m, M ^ i := by simp [hS]
    rw [this, geom_sum_mul, hm, sub_self]
  have h6 : M - 1 = 0 := by
    have := congrArg (aeval M b * ·) h5
    simpa only [← mul_assoc, h4, one_mul, mul_zero] using this
  exact sub_eq_zero.1 h6
end
