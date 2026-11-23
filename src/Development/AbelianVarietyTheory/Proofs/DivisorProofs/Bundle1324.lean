module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle002

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Residue

open KaehlerDifferential IsLocalRing Module

theorem exists_basis_D_cons (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra k V] [Algebra.EssFiniteType k V] (n : ℕ) {t : V}
    (w : Fin n → V) (ht : Irreducible t) (hb₀ : Nonempty (Module.Basis (Fin (n + 1)) V Ω[V⁄k]))
    (hw : ∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (algebraMap k V) w P)) :
    ∃ b : Module.Basis (Fin (n + 1)) V Ω[V⁄k], ∀ i, b i = D k V ((Fin.cons t w : Fin (n + 1) → V) i) := by
  obtain ⟨b₀⟩ := hb₀
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)
  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ (algebraMap k V) w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP
  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg

    simp only [map_add (f := _), map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
    Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  exact Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)

theorem residue_dForm : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → ∀ (t f : S.ring) (v w : Fin n → S.ring) (H : L),
  Irreducible t → Irreducible f → TrBasis cK (fun i => ψ (v i)) →
  TrBasis cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
    H • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  ∃ h : S.ring, (h : L) * f = H * t ∧ dForm cK (fun i => ψ (w i)) = ψ h • dForm cK (fun i => ψ (v i)) := by
  intro L K _ _ cL cK n S ψ hψ hc t f v w H ht hf hvK hvL hH
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  letI : Algebra S.ring K := ψ.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : IsScalarTower ℂ S.ring K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hψt : ψ t = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact ht.not_isUnit
  have hb₀ : Nonempty (Module.Basis (Fin (n + 1)) S.ring Ω[S.ring⁄ℂ]) := by
    obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ ht
    have h1 := trdeg_eq_of_basis_kaehler ℂ L b
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hvL
    rw [h1, Cardinal.mk_fin] at h2
    have h3 : n + 1 = m + 1 := by exact_mod_cast h2
    obtain rfl : n = m := by omega
    exact ⟨b⟩
  have hvu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P) := by
    intro P hP
    by_contra hu
    have hm : MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P ∈ RingHom.ker ψ := by
      rw [hker]
      exact hu
    rw [RingHom.mem_ker, MvPolynomial.hom_eval₂, hcomp] at hm
    have hind : AlgebraicIndependent ℂ (fun i => ψ (v i)) := hvK.1
    exact hP ((algebraicIndependent_iff.1 hind) P hm)
  obtain ⟨b, hb⟩ := exists_basis_D_cons ℂ S.ring n v ht hb₀ hvu

  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ ht hf
  set z : Fin (n + 1) → S.ring := Fin.cons t v with hz
  have hω : IsFreeGen S.ring (dForm S.const z) := isFreeGen_dForm z b hb
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) S.ring :=
    Matrix.of fun i j => b.repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i)) j
  have hM : dForm S.const (Fin.cons f w : Fin (n + 1) → S.ring) = M.det • dForm S.const z := by
    refine dForm_eq_det_smul _ _ M fun i => ?_
    change D ℂ S.ring _ = ∑ j, M i j • D ℂ S.ring (z j)
    conv_lhs => rw [← b.sum_repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i))]
    simp only [hb, M, Matrix.of_apply, hz]
  have hcons : ∀ (a : S.ring) (g : Fin n → S.ring),
      (fun i => S.ring.subtype ((Fin.cons a g : Fin (n + 1) → S.ring) i)) =
        (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have htoRat : ∀ (a : S.ring) (g : Fin n → S.ring),
      S.toRat (n + 1) (dForm S.const (Fin.cons a g : Fin (n + 1) → S.ring)) =
        dForm cL (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    exact (formMap_dForm (D := n + 1) S.ring.subtype rfl _).trans (congrArg _ (hcons a g))
  have hML : dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
      (M.det : L) • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) := by
    have := congrArg (S.toRat (n + 1)) hM
    rw [map_smulₛₗ, hz, htoRat, htoRat] at this
    exact this
  have hHM : H = (M.det : L) := by
    have hne := S.toRat_ne_zero hω
    rw [hz, htoRat] at hne
    exact smul_left_injective L hne (hH.symm.trans hML)

  have hmain : M.det * ↑u⁻¹ * f = M.det * t := by
    rw [← hu, mul_comm t, ← mul_assoc, mul_assoc M.det, Units.inv_mul, mul_one]
  refine ⟨M.det * ↑u⁻¹, ?_, ?_⟩
  · rw [hHM]
    exact_mod_cast congrArg Subtype.val hmain
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => ψ (M i.succ j.succ)
  have hN : dForm cK (fun i => ψ (w i)) = N.det • dForm cK (fun i => ψ (v i)) := by
    refine dForm_eq_det_smul _ _ N fun i => ?_
    change D ℂ K (ψ (w i)) = ∑ j, N i j • D ℂ K (ψ (v j))
    have := congrArg (KaehlerDifferential.map ℂ ℂ S.ring K) (b.sum_repr (D ℂ S.ring (w i)))

    rw [map_sum, KaehlerDifferential.map_D, Fin.sum_univ_succ, RingHom.algebraMap_toAlgebra] at this
    rw [← this]
    simp only [map_smul, hb, KaehlerDifferential.map_D, hz, Fin.cons_zero, Fin.cons_succ,
      RingHom.algebraMap_toAlgebra, hψt, map_zero, smul_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K]
    simp [N, M, RingHom.algebraMap_toAlgebra]
  have hDt : D ℂ S.ring t = b 0 := by rw [hb]; rfl
  have hrow : ∀ j, ψ (M 0 j) = ψ (u * Finsupp.single (0 : Fin (n + 1)) (1 : S.ring) j) := by
    intro j
    simp only [M, Matrix.of_apply, Fin.cons_zero]
    rw [← hu, Derivation.leibniz, hDt, map_add (f := _), map_smul, map_smul, b.repr_self]
    rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, map_add (f := _),
      map_mul, hψt, zero_mul, zero_add]
  have hsub : (ψ.mapMatrix M).submatrix Fin.succ Fin.succ = N := Matrix.ext fun _ _ => rfl
  have h0 : ∀ j : Fin n, ψ.mapMatrix M 0 j.succ = 0 := fun j => by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp [Finsupp.single_apply, (Fin.succ_ne_zero j).symm]
  have h00 : ψ.mapMatrix M 0 0 = ψ u := by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp
  have hdet : ψ M.det = ψ u * N.det := by
    rw [RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove_zero, hsub]
    simp only [h0, h00, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
      one_mul]
  rw [hN, map_mul, hdet, mul_comm (ψ u), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

end GlobalTheory.Residue
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair


open IsLocalRing in
theorem exists_residue_coords_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro N r V hC u hx hm hunitP hloc
  classical
  let φ : Q →+* V.ring := Q.subtype.codRestrict V.ring fun q => hC _ q.2
  letI : Algebra ℂ V.ring := V.const.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  letI : Algebra ℂ Q := (c.codRestrict Q hQ.const_mem).toAlgebra
  letI : Algebra Q V.ring := φ.toAlgebra
  haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ Q V.ring := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  haveI : IsLocalHom (algebraMap Q V.ring) := ⟨fun q hq => by
    by_contra hq'
    have hqm : q ∈ maximalIdeal Q := (mem_maximalIdeal _).2 hq'
    exact (mem_maximalIdeal _).1 (hm q hqm) hq⟩
  haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
  obtain ⟨x, hx⟩ := hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [Cardinal.mk_fin] at h2
  have h3 := trdeg_residueField_of_trdeg ℂ V.ring L h2.symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V.ring
  obtain ⟨hN, -⟩ := exists_basis_kaehler_of_trdeg ℂ L h2.symm ht
  let ub : Fin r → ResidueField V.ring := fun i => residue V.ring (u i)
  have key : ∀ P : MvPolynomial (Fin r) Q, residue V.ring (MvPolynomial.eval₂ φ u P) =
      MvPolynomial.aeval ub (P.map (residue Q)) := by
    intro P
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  have hmem : ∀ Pb : MvPolynomial (Fin r) (ResidueField Q),
      MvPolynomial.aeval ub Pb ∈ Algebra.adjoin (ResidueField Q) (Set.range ub) := fun Pb => by
    rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Pb, rfl⟩
  have hind : AlgebraicIndependent (ResidueField Q) ub := by
    rw [algebraicIndependent_iff]
    intro Pb hPb
    by_contra hne
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (residue Q) residue_surjective Pb
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.1 hne
    rw [MvPolynomial.coeff_map] at hα
    have hu := hunitP P ⟨α, fun h => hα ((residue_eq_zero_iff _).2 h)⟩
    rw [← residue_ne_zero_iff_isUnit] at hu
    exact hu ((key P).trans hPb)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (ResidueField Q) (Set.range ub))
      (ResidueField V.ring) := by
    constructor
    intro y
    obtain ⟨f, rfl⟩ := residue_surjective y
    obtain ⟨P, R, hR, hf⟩ := hloc f
    let a : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (P.map (residue Q))⟩
    let b : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (R.map (residue Q))⟩
    have hb : (b : ResidueField V.ring) ≠ 0 := by
      change MvPolynomial.aeval ub (R.map (residue Q)) ≠ 0
      rw [← key]; exact (residue_ne_zero_iff_isUnit _).2 hR
    have hb0 : b ≠ 0 := fun h => hb (by rw [h]; rfl)
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb0 ?_, ?_⟩
    · simpa using congrArg (fun p => p.coeff 1) h
    · have e := congrArg (residue V.ring) hf
      rw [map_mul, key, key] at e
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change (b : ResidueField V.ring) * residue V.ring f - (a : ResidueField V.ring) = 0
      change residue V.ring f * (b : ResidueField V.ring) = (a : ResidueField V.ring) at e
      rw [mul_comm, e, sub_self]
  have hub : IsTranscendenceBasis (ResidueField Q) ub := hind.isTranscendenceBasis_iff_isAlgebraic.2 halg
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  have hB := hT.sumElim_comp hub
  have hc : (r : Cardinal) + Cardinal.mk T = ((N - 1 : ℕ) : Cardinal) := by
    rw [← h3, ← hB.cardinalMk_eq_trdeg, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.mk_fin]
  haveI hfin : Finite T := Cardinal.lt_aleph0_iff_finite.1
    (lt_of_le_of_lt le_add_self (by rw [hc]; exact Cardinal.natCast_lt_aleph0))
  have hcard : r + Nat.card T = N - 1 := by
    rw [← Nat.cast_card (α := T)] at hc
    exact_mod_cast hc
  set j := Nat.card T with hj
  let e : Fin j ≃ T := (Finite.equivFin T).symm
  let s : Fin j → Q := fun i => Function.surjInv residue_surjective ((e i : ResidueField Q))
  have hs : ∀ i, residue Q (s i) = (e i : ResidueField Q) := fun i =>
    Function.surjInv_eq residue_surjective _
  let g : Fin (r + j) → Fin r ⊕ T := fun i => Sum.map id e (finSumFinEquiv.symm i)
  have hg : Function.Injective g :=
    (Sum.map_injective.2 ⟨Function.injective_id, e.injective⟩).comp finSumFinEquiv.symm.injective
  have hind2 := hB.1.comp g hg
  have hv : residue V.ring ∘ (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) =
      Sum.elim ub (algebraMap (ResidueField Q) (ResidueField V.ring) ∘ Subtype.val) ∘ g := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [g, ub, Fin.append_left]
    · simp only [Function.comp_apply, Fin.append_right, g, finSumFinEquiv_symm_apply_natAdd,
        Sum.map_inr, Sum.elim_inr]
      rw [← hs, ResidueField.algebraMap_residue]
      rfl
  refine ⟨j, s, by omega, fun P hP => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
  change MvPolynomial.aeval (residue V.ring ∘ _) P ≠ 0
  rw [hv]
  exact fun h0 => hP (algebraicIndependent_iff.1 hind2 P h0)

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem eq_of_choose_eq_one_of_pos {r D : ℕ} (hD : 0 < D) (h : r.choose D = 1) : D = r := by
  rcases lt_trichotomy D r with hlt | heq | hgt
  · obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.choose_succ_succ] at h
    have h1 := Nat.choose_pos (show d ≤ s by omega)
    have h2 := Nat.choose_pos (show d + 1 ≤ s by omega)
    rw [Nat.succ_eq_add_one] at h
    omega
  · exact heq
  · rw [Nat.choose_eq_zero_of_lt hgt] at h
    exact absurd h zero_ne_one

theorem trBasis_of_isFreeGen_dForm : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  intro L _ cL Q hQ D x hD hx
  letI := cL.toAlgebra
  let c0 : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  letI := c0.toAlgebra
  haveI : IsScalarTower ℂ Q L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing Q L := IsFractionRing.of_field Q L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e]
  haveI : Algebra.FormallyEtale Q L := .of_isLocalization (nonZeroDivisors Q)
  have hL : IsFreeGen L (TopForm.formMap D Q.subtype rfl (dForm c0 x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q L) D)
  rw [TopForm.formMap_dForm] at hL
  change IsFreeGen L (dForm cL fun i => (x i : L)) at hL

  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : Algebra.EssFiniteType Q L := .of_isLocalization L (nonZeroDivisors Q)
  haveI : Algebra.EssFiniteType ℂ L := .comp ℂ Q L
  have h1 : Module.finrank L (Forms cL D) = 1 := by
    have e : L ≃ₗ[L] Forms cL D := LinearEquiv.ofBijective (LinearMap.toSpanSingleton L _ _) hL
    rw [← e.finrank_eq, Module.finrank_self]
  rw [exteriorPower.finrank_eq] at h1
  have hr := eq_of_choose_eq_one_of_pos hD h1

  have hli : LinearIndependent L fun i => KaehlerDifferential.D ℂ L (x i : L) := by
    by_contra hc
    have h0 : dForm cL (fun i => (x i : L)) = 0 := by
      rw [dForm_eq]
      exact (exteriorPower.ιMulti L D).map_linearDependent _ hc
    rw [h0] at hL
    exact one_ne_zero (hL.1 (a₁ := 1) (a₂ := 0) (by simp))
  have hind : AlgebraicIndependent ℂ fun i => (x i : L) :=
    ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence ℂ L D _ hli
  have htr : Algebra.trdeg ℂ L = D := by
    rw [← rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank]
    exact_mod_cast hr.symm
  exact hind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fin])

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
theorem _root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis {k K : Type} [Field k] [CharZero k]
    [Field K] (c : k →+* K) {n : ℕ} {x : Fin n → K} (hx : _root_.GlobalTheory.FieldPair.TrBasis c x) :
    _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) := by
  letI : Algebra k K := c.toAlgebra
  have hb : IsTranscendenceBasis k x := hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K :=
    hb.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hbx⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hb.1
  exact _root_.GlobalTheory.TopForm.isFreeGen_dForm x b (fun i => by rw [hbx i])


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
theorem _root_.GlobalTheory.FieldPair.formOrd_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K]
    (c : k →+* K) (n : ℕ) (x : Fin n → K), _root_.GlobalTheory.FieldPair.TrBasis c x →
  _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) ∧
  ∀ E : _root_.GlobalTheory.FieldPair.Place c,
    (∃ ω : _root_.GlobalTheory.TopForm.Forms E.const n, _root_.GlobalTheory.TopForm.IsFreeGen E.ring ω) ∧
    (∀ η : _root_.GlobalTheory.TopForm.Forms c n, η ≠ 0 → E.IsFormOrd η ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η)) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (f : K), η ≠ 0 → f ≠ 0 →
      (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (f • η) = E.ord f + (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a →
      (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = a) := by
  intro k K _ _ _ c n x hx
  refine ⟨_root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis c hx, fun E => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact E.exists_isFreeGen hx
  · intro η hη
    exact E.isFormOrd_formOrd hx hη
  · intro η f hη hf
    exact E.formOrd_smul hx hη hf
  · intro η a _ h
    exact h.formOrd_eq

end GlobalTheory.FieldPair
end
