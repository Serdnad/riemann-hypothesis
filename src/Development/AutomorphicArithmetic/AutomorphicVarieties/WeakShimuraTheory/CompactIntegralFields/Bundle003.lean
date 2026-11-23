module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.ComplOfNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.FibTTrace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.FibTrdeg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegCosetFour
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.ExistsStabilizerIndexDvdOfNotIrreducibleRestrict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.IsClosedZeroLocusMvPolynomialEvalAdicContinuous
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
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
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.fib_low {K : Type} [Field K] (E : Subfield K) (n : M4 K) (h : IsLow n) (h10 : n 1 0 ∈ E)
    (h20 : n 2 0 ∈ E) (h30 : n 3 0 ∈ E) (h21 : n 2 1 ∈ E) (i j : Fin 4) : n i j ∈ E := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := congrFun (congrFun h1 1) 0
  have e2 := congrFun (congrFun h1 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3] at e1 e2
  have h32 : n 3 2 ∈ E := by
    have : n 3 2 = -n 1 0 := by linear_combination e1
    rw [this]; exact neg_mem h10
  have h31 : n 3 1 ∈ E := by
    have : n 3 1 = n 2 0 - n 2 1 * n 1 0 := by linear_combination -e2
    rw [this]; exact sub_mem h20 (mul_mem h21 h10)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [h3 i j hij]; exact zero_mem _
  · rw [h2]; exact one_mem _
  · fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)

private theorem UpperTheory.V.Ws.fib_gen {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) {K : Type} [Field K] (y : X.A →+* K)
    (hne : ∀ i j, i ≠ j → y (X.P.r Φ.g0 i i) ≠ y (X.P.r Φ.g0 j j)) (hirr : Irr (mapRep y X.P.r)) :
    ∃ T : Finset K, T.card ≤ 2 + 4 * Nat.card Φ.ι ∧ ∀ E : Subfield K, (∀ b, y (algebraMap X.B X.A b) ∈ E) → (∀ t ∈ T, t ∈ E) →
      (∀ (p : K[X]) (x : K), p.Monic → (∀ n, p.coeff n ∈ E) → p.IsRoot x → x ∈ E) → ∀ z, y z ∈ E := by
  classical
  haveI := Fintype.ofFinite Φ.ι
  have hp := X.pair.map y
  obtain ⟨s, t, hst⟩ := fibTorus (mapRep y X.P.r) _ Φ.g0 hp.mult hp.nrm hne hirr
  let u : Φ.ι × Fin 4 → K := fun x => y (X.P.n x.1 (![1, 2, 3, 2] x.2) (![0, 0, 0, 1] x.2))
  refine ⟨{s, t} ∪ Finset.univ.image u, ?_, fun E hB hT hE z => ?_⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add Finset.card_le_two (Finset.card_image_le.trans ?_))
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card, Nat.mul_comm]
  · have hc : ∀ g n, (mapRep y X.P.r g).charpoly.coeff n ∈ E := fun g n => by
      have : (mapRep y X.P.r g).charpoly.coeff n = y (algebraMap X.B X.A ((X.cp g).coeff n)) := by
        show ((X.P.r g).map y).charpoly.coeff n = _
        rw [Matrix.charpoly_map, ← X.cp_map, coeff_map, coeff_map]
      rw [this]; exact hB _
    have hs : s ∈ {s, t} ∪ Finset.univ.image u :=
      Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    have ht : t ∈ {s, t} ∪ Finset.univ.image u :=
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hr := hst E (hT _ hs) (hT _ ht)
      (fun g => by
        have := hB (algebraMap Λ X.B (a (Φ.ν g)))
        rwa [← IsScalarTower.algebraMap_apply] at this)
      (fun g => by rw [Matrix.trace_eq_neg_charpoly_coeff]; exact neg_mem (hc _ _))
      (fun i => hE _ _ (Matrix.charpoly_monic _) (hc Φ.g0) (by
        have hd : mapRep y X.P.r Φ.g0 = Matrix.diagonal fun i => mapRep y X.P.r Φ.g0 i i := hp.nrm.diagonal_diag.symm
        rw [IsRoot, hd, Matrix.charpoly_diagonal, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)))
    have hu : ∀ x, u x ∈ E := fun x => hT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
    have hn := fun v => fib_low E _ (hp.low v) (hu (v, 0)) (hu (v, 1)) (hu (v, 2)) (hu (v, 3))
    have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
    rw [← X.gen] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact hr _ _ _
      · exact hn _ _ _
    | algebraMap b => exact hB b
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem UpperTheory.V.Ws.fib :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (c : PD Φ.ι Γ (ResidueField Λ)), Φ.IsRes ((residue Λ).comp a) c → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R),
      Φ.IsDef a c (X.P.map (f : X.A →+* R)) → ∀ (q : Ideal R) [q.IsPrime],
      Irr (mapRep ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp ((Ideal.Quotient.mk q).comp (f : X.A →+* R))) X.P.r) →
      ringKrullDim (R ⧸ q) ≤ ringKrullDim (X.B ⧸ q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) + (2 + 4 * Nat.card Φ.ι : ℕ) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hΦ X c hc R _ _ hCO f hf q hq hirr
  haveI : IsLocalRing R := hCO.toIsLocalRing
  haveI : IsLocalRing X.B := X.coB.toIsLocalRing
  haveI := X.noeth
  haveI := X.ft
  letI : Algebra X.A R := (f : X.A →+* R).toAlgebra
  haveI : IsScalarTower Λ X.A R := IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  have hff : IsScalarTower.toAlgHom Λ X.A R = f := AlgHom.ext fun _ => rfl
  obtain ⟨hx, hR⟩ := fibCpl (Λ := Λ) (A := X.A) (R := R) (fun R' _ _ _ g hg => by
    rw [hff] at hg ⊢
    obtain ⟨h, hh, hu⟩ := hf.2 R' (X.P.map (g : X.A →+* R')) ⟨X.pair_map g, X.cont_map g, by
      rw [← hf.1.red]
      exact congrArg (fun φ : X.A →ₐ[Λ] ResidueField Λ => X.P.map (φ : X.A →+* ResidueField Λ)) hg⟩
    exact ⟨h, X.hom_ext _ _ hh, fun h' e => hu h' (by rw [← e]; rfl)⟩)
  have hxB : ((maximalIdeal R).comap (algebraMap X.A R)).comap (algebraMap X.B X.A) = maximalIdeal X.B := by
    ext b
    show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R ↔ _
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
  haveI hη : (q.comap (algebraMap X.A R)).IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨t, h1, h2⟩ := UpperTheory.V.CA.c3b Λ _ (UpperTheory.V.CA.IsCL.of_isCO Λ X.B) hxB (q.comap (algebraMap X.A R))
    (Ideal.comap_mono (le_maximalIdeal hq.ne_top))
  obtain ⟨T, hT, hE⟩ := fib_gen X _ (fun i j hij e => by
    have e1 : f (X.P.r Φ.g0 i i) - f (X.P.r Φ.g0 j j) ∈ q :=
      Ideal.Quotient.eq.1 (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q)) e)
    have e2 := (res_eq_zero_iff Λ R _).2 (le_maximalIdeal hq.ne_top e1)
    have e3 : ∀ i, res Λ R (f (X.P.r Φ.g0 i i)) = (residue Λ).comp a (Φ.χ i Φ.g0) := fun i => by
      rw [← hc.res.diag, ← hf.1.red]; rfl
    rw [map_sub, e3, e3] at e2
    exact (hΦ.ok.dist i j hij).ne_zero e2) hirr
  have h3 := fibTrdeg (D := X.B ⧸ (q.comap (algebraMap X.A R)).comap (algebraMap X.B X.A))
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.quotientMap q (algebraMap X.A R) le_rfl)) T
    (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective (R ⧸ q) _).comp Ideal.quotientMap_injective) Ideal.quotientMap_injective
    (fun E hB hT' hcl z => by
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact hE E (fun b => hB (Ideal.Quotient.mk _ b)) hT' hcl z)
  rw [h1] at h3
  have h4 : t ≤ 2 + 4 * Nat.card Φ.ι := le_trans (by exact_mod_cast h3) hT
  refine ((UpperTheory.V.CA.c3c _ hR).2 _ q le_rfl).trans ?_
  rw [h2]
  exact add_le_add le_rfl (by exact_mod_cast h4)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.h4 :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l]
      (r : W.Resid F O 4) (x : W.Point r), Nonempty F.Vl → (∀ v i, Alg.AdicCont (maximalIdeal x.A) fun g => ((x.ψ v i g : x.Aˣ) : x.A)) →
      (∀ v i j, i ≠ j → ∃ g, F.φ v g ∈ F.G' ∧ r.psib v i g = r.psib v j g ∧ x.ψ v i g ≠ x.ψ v j g) →
      U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) →
      (∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) →
      (∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (r.chib i / r.chib j) ^ n ≠ 1) → x.N1 ∧ x.TypeI ∧ x.N3 := by
  intro l _ hl F O _ _ _ _ _ r x ⟨v⟩ _ ha hb hc hd
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharP x.K l := charP_of_injective_algebraMap (algebraMap (ResidueField O) x.K).injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  let j : x.A →+* x.Fb := (algebraMap x.Fr x.Fb).comp (algebraMap x.A x.Fr)
  have hj : Function.Injective j := (algebraMap x.Fr x.Fb).injective.comp (IsFractionRing.injective x.A x.Fr)
  let ρ : F.G₀ →* Matrix (Fin 4) (Fin 4) x.Fb := W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)
  have hρ : ∀ g, ρ g = (W.mat x.ρ g).map j := fun g => rfl
  have two : ∀ (k : Type) [Field k] [CharP k l], (2 : k) ≠ 0 := fun k _ _ h =>
    hl ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast h)))
  haveI : CharP x.Fb l := charP_of_injective_ringHom (j.comp (PowerSeries.C : x.K →+* x.A)).injective l
  obtain ⟨cpR, cpL⟩ := h4Cp l F O 4 r x

  obtain ⟨g, hg, hfree⟩ := exists_mem_powerSeries_char_ratios_not_isOfFinOrder l (F.Gv v) x.K 4 (x.ψ v) (F.G'.comap (F.φ v)) fun a b hab => by
    obtain ⟨s, h1, h2, h3⟩ := ha v a b hab
    refine ⟨s, h1, ?_, h3⟩
    have h4 : ∀ i, PowerSeries.constantCoeff (x.ψ v i s : PowerSeries x.K) =
        algebraMap (ResidueField O) x.K (r.psib v i s) := fun i =>
      congrArg Units.val (DFunLike.congr_fun (x.ψ_red v i) s)
    rw [h4, h4, h2]
  let a : Fin 4 → x.Fbˣ := fun i => Units.map (j : x.A →* x.Fb) (x.ψ v i g)
  have hu : (ρ (F.φ v g)).charpoly = ∏ i, (X - C (a i : x.Fb)) := by
    rw [hρ, Matrix.charpoly_map, cpL, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => hfree s t hst <| by
    rw [← _root_.map_div] at h
    exact (Function.Injective.isOfFinOrder_iff (Units.map_injective (f := (j : x.A →* x.Fb)) hj)).1 h
  have hsep := charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _

  have hI : x.TypeI := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := exists_stabilizer_index_dvd_of_not_irreducible_restriction x.Fb F.G₀ 4 ρ hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := exists_sign_twist_charpoly_of_not_irreducible_restriction x.Fb F.G₀ (two _) ρ hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := isClosed_setOf_matrix_stabilizes_submodule F.G₀ x.Fb 4 _ (Pr.linClosedOfAdic F.G₀ x.A x.Fb j hj 4 (W.mat x.ρ) x.cont) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (exists_sign_twist_char_eq_of_charpoly_twist_invariant x.Fb (ResidueField O) x.K x.A F.G₀ 4 (W.mat x.ρ) j _ _ r.chib η hj cpR hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) (two (ResidueField O))
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨fun w => ⟨fun s t hst h => ?_, fun s t hst h => ?_⟩, hI, ?_⟩
  · obtain ⟨y, -, -, h3⟩ := ha w s t hst
    exact h3 (by rw [h])
  · obtain ⟨y, h1, -, h3⟩ := ha w s t hst.ne
    have h4 : (F.ε.comp F.η.ker.subtype) (F.φ w y) = 1 := h1
    refine h3 ?_
    rw [h, MonoidHom.mul_apply, MonoidHom.comp_apply, W.GFrame.eps, MonoidHom.comp_apply, h4, map_one, mul_one]
  · have hsp : Submodule.span x.Fb (Set.range (ρ.comp F.G'.subtype)) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
    have hsp' : Submodule.span x.Fb (Set.range ρ) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
    have hnc := exists_noncommuting_images_in_finiteIndex_normal_subgroup x.Fb x.K x.A F.G₀ ρ j PowerSeries.constantCoeff
      (fun i => W.pushCh (algebraMap (ResidueField O) x.K) (r.chib i)) hj
      (fun s => ⟨(W.mat x.ρ s).charpoly, by rw [hρ, Matrix.charpoly_map], cpR s⟩) hsp' (by
        obtain ⟨s, t, h⟩ := hd
        refine ⟨s, t, fun n h0 h4 he => h n h0 h4 (MonoidHom.ext fun y => ?_)⟩
        apply Units.map_injective (f := (algebraMap (ResidueField O) x.K : ResidueField O →* x.K)) (RingHom.injective _)
        simpa using DFunLike.congr_fun he y) F.G' _ hg hsep
    refine exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat x.ρF s).charpoly.Separable) fun V hV σ => ?_
    obtain ⟨y, hy, hs⟩ := AlgebraTools.regCosetFour x.Fb F.G' (two _) (ρ.comp F.G'.subtype)
      (fun f => (isClosed_zeroLocus_mvPolynomial_eval_adicContinuous F.G₀ x.A x.Fb (Fin 4 × Fin 4) j hj (fun p s => W.mat x.ρ s p.1 p.2) (fun p => x.cont p.1 p.2) f).preimage
        continuous_subtype_val) hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
    refine ⟨y, hy, (Polynomial.separable_map (algebraMap x.Fr x.Fb)).1 ?_⟩
    rw [← Matrix.charpoly_map]
    exact hs
end
