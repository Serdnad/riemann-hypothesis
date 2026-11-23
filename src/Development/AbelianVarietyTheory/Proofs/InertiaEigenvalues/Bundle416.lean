module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle286
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle177
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGene
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SelmerSumLargePrime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

open scoped ENNReal

namespace GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

open GlobalTheory.IndefiniteRowSideFullHecke

theorem congBound_of_rational : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  intro D i π ρ hπ hζ h
  classical
  obtain ⟨he0, het⟩ := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i
  refine (GlobalTheory.Proof.QuotientLengthInfimum.conclusion_iff D i π ρ).2 ?_
  by_cases hs : Br.sFin D.loc D.nbr i (fun _ => ρ) π
  swap
  · have h1 : SelmerSumLargePrime.selLen D i ρ π = ⊤ := not_lt_top_iff.mp hs
    rw [h1]; simp
  by_cases hsh : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤
  swap
  · push Not at hsh
    obtain ⟨k, hk, hk'⟩ := hsh
    have h1 : SelmerSumLargePrime.shaSum D i = ⊤ := by
      unfold SelmerSumLargePrime.shaSum
      refine top_le_iff.mp (le_trans hk' ?_)
      exact Finset.single_le_sum (f := fun e : ℕ => Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ))
        (fun _ _ => zero_le) hk
    rw [h1, ENat.mul_top he0]; simp
  have hr := h hs hsh
  have hc : SelmerSumLargePrime.ccLen D i π ≠ ⊤ := by
    unfold SelmerSumLargePrime.ccLen
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.vcc_ne_top _ (D.nd.T_sep i) _ _ hπ
  have hs' : SelmerSumLargePrime.selLen D i ρ π ≠ ⊤ := hs.ne
  have hq : ∀ P ∈ D.nd.Q i,
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1}) ≠ ⊤ := by
    intro P hP
    have h0 : SelmerSumLargePrime.zetaP D i P - 1 ≠ 0 := by
      rw [← GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq, BaseSizes.zetaP_eq D i P hP]
      exact sub_ne_zero.mpr (hζ P hP)
    exact Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero h0))
  have hrow : ∀ k ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) k : ℚ) =
      ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat : ℚ) := fun k hk =>
    D.nd.sha_eq _ k (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2 _
      (ENat.natCast_toNat (hsh k hk).ne).symm
  have hlq : ∀ P ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i P - 1}) =
      ((Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat : ℚ) /
        ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    intro P hP
    rw [← BaseSizes.zetaP_eq D i P hP, GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq]
    rfl
  have hv : D.nd.vcc i π = ((SelmerSumLargePrime.ccLen D i π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  have hsp : Br.sPi D.loc D.nbr i (fun _ => ρ) π =
      ((SelmerSumLargePrime.selLen D i ρ π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  rw [hv, hsp, Finset.sum_congr rfl hrow, Finset.sum_congr rfl hlq, ← Finset.sum_div] at hr
  have hE0 : (0 : ℚ) < ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    have : (SelmerSumLargePrime.ramLen D i).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; tauto
    exact_mod_cast Nat.pos_of_ne_zero this
  set E := (SelmerSumLargePrime.ramLen D i).toNat with hEdef
  set c := (SelmerSumLargePrime.ccLen D i π).toNat
  set s := (SelmerSumLargePrime.selLen D i ρ π).toNat
  set A := ∑ k ∈ Finset.Ioo 0 D.R.t, (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat with hA
  set B := ∑ P ∈ D.nd.Q i,
    (Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat with hB
  set v := padicValNat (D.nd.l i) (hE D.host)
  have key : (c : ℚ) ≤ s + E * A + E * v + D.R.t * B := by
    have h2 : ((s : ℚ) / E + (A : ℚ) + (v : ℚ) + (D.R.t : ℚ) * ((B : ℚ) / E)) * E =
        s + E * A + E * v + D.R.t * B := by
      field_simp
    rw [← h2, ← div_le_iff₀ hE0]
    push_cast [hA, hB]
    exact hr
  have knat : c ≤ s + E * A + E * v + D.R.t * B := by exact_mod_cast key
  have hsum : SelmerSumLargePrime.shaSum D i = (A : ℕ∞) := by
    unfold SelmerSumLargePrime.shaSum
    rw [hA, Nat.cast_sum]
    exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hsh k hk).ne).symm
  have htw : SelmerSumLargePrime.twistLen D i = ((D.R.t * B : ℕ) : ℕ∞) := by
    unfold SelmerSumLargePrime.twistLen
    rw [hB, Nat.cast_mul, Nat.cast_sum]
    exact congrArg _ (Finset.sum_congr rfl fun P hP => (ENat.natCast_toNat (hq P hP)).symm)
  rw [hsum, htw, ← ENat.natCast_toNat hc, ← ENat.natCast_toNat hs', ← ENat.natCast_toNat het]
  exact_mod_cast knat

end GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (TwDatum Twisted SameBelow SamePair LiesUnder TwistedPlaceSettings namedPrimes expDat GoodDatum GoodSystem
  recorded ExistsChoice WithToricIntegralityConstant FamTwGood TwGoodClosed)

namespace GlobalTheory.TwistGoodCompare

variable {D : D7}

def AtPlace (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w, Twisted D w → LiesUnder D (t w).1 w ∨ LiesUnder D (t w).1 (D.what₂.places.conj w)

theorem isUnit_of_toOe (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w))
    (h : IsUnit (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
      (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
        (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))) : IsUnit y := by
  haveI := c.Oe_loc w
  have h1 := (isUnit_map_iff _ _).1 h
  clear h
  generalize c.k' w = k at h1
  generalize c.twI w = i at y k h1
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i _)
  have h2 := (isUnit_map_iff (algebraMap (D.ntw.O i) (D.ntw.Ok i k)) _).1 h1
  by_contra hy
  have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) h0
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 i), map_eq_zero] at this
    exact (D.ntw.lPrime i).out.ne_zero (by exact_mod_cast this)
  have hP : ((IsLocalRing.maximalIdeal (D.ntw.O i)).comap (algebraMap (D.ntw.O0 i) (D.ntw.O i))).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => hl ?_
    rw [← Ideal.mem_bot, ← h0, Ideal.mem_comap, map_natCast]
    exact D.ntw.O_l i
  have hm : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hy
  rw [← IsLocalRing.eq_maximalIdeal hP, Ideal.mem_comap] at hm
  exact hm h2

theorem pos_iff_not_isUnit (c : NChoice D) (w : D.what₂.places.Pl) (x : D.what₂.LL) (z : c.Oe w)
    (h : c.embW w x = algebraMap (c.Oe w) (FractionRing (c.Oe w)) z) :
    0 < D.what₂.places.val w x ↔ ¬ IsUnit z := by
  rcases eq_or_ne x 0 with rfl | h0
  · have : z = 0 := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (by rw [← h, map_zero, map_zero])
    simp [this]
  have hx : 0 ≤ D.what₂.places.val w x := (c.embW_w w x).2 ⟨z, h.symm⟩
  have hmul := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ h0, AddValuation.map_one] at hmul
  have e1 : 0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
    rw [D.val_eq w x h0, D.val_eq w _ (inv_ne_zero h0)] at *
    norm_cast at *
    omega
  rw [e1, c.embW_w, not_iff_not]
  have hz : c.embW w x ≠ 0 := by simpa using h0
  constructor
  · rintro ⟨u, hu⟩
    refine IsUnit.of_mul_eq_one u (IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) ?_)
    rw [map_mul, hu, ← h, map_one, ← map_mul, mul_inv_cancel₀ h0, map_one]
  · rintro ⟨u, rfl⟩
    refine ⟨((u⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    rw [map_inv₀, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ x' : ↥D.LL0, (x' : D.what₂.LL) = star (x : D.what₂.LL) := by
  let σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  exact ⟨σ.restrictNormal ↥D.LL0 x, σ.restrictNormal_commutes ↥D.LL0 x⟩

theorem liesUnder_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) :
    LiesUnder D (c.twI w) (if c.sd w then w else D.what₂.places.conj w) := by
  intro x
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (c.twI w))
      (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have key : ∀ x' : ↥D.LL0, (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x' =
      D.ntw.emb0 (c.twI w) (x : ↥D.LL0) → (0 < D.what₂.places.val w (x' : D.what₂.LL) ↔ ¬ IsUnit y) := by
    intro x' hx'
    have e := h.embedding_baseField_condition w x' y 1 one_ne_zero (by rw [hx', map_one, mul_one, hy])
    simp only [map_one, mul_one] at e
    rw [pos_iff_not_isUnit c w _ _ e, not_iff_not]
    exact ⟨isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩
  rw [hleft]
  cases hs : c.sd w
  · obtain ⟨x', hx'⟩ := exists_star hG (x : ↥D.LL0)
    rw [if_neg (by simp), D.conj_val, ← hx']
    refine (key x' ?_).symm
    rw [hs, if_neg (by simp)]
    exact D.ntw.restX_coefficientEmbedding_conj _ _ _ (by rw [hx', star_star])
  · rw [if_pos rfl]
    exact (key x (by rw [hs, if_pos rfl])).symm

theorem atPlace_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) : AtPlace (recorded c) := by
  intro w _
  have := liesUnder_of_tie hG h w
  split_ifs at this
  exacts [Or.inl this, Or.inr this]

end GlobalTheory.TwistGoodCompare

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.SelmerSameChar

theorem isLocalHom_of_natCast {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing B]
    (f : O →+* B) (l : ℕ) (h0 : (l : O) ≠ 0) (h : ¬ IsUnit (l : B)) : IsLocalHom f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hu : ¬ IsUnit (f ϖ) := fun hu => h (by
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [← map_natCast f, hn, map_mul, map_pow]
    exact (u.isUnit.map f).mul (hu.pow n))
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ IsLocalRing.maximalIdeal O := hn
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, rfl⟩ := hm
  rw [map_mul] at hx
  exact hu (isUnit_of_mul_isUnit_right hx)

theorem isIntegral_of_finite {l₁ l₂ : ℕ} [i₁ : Fact l₁.Prime] [i₂ : Fact l₂.Prime] (h : l₁ = l₂) {O₀ O : Type}
    [CommRing O₀] [Algebra ℤ_[l₁] O₀] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l₂] O]
    [Module.Finite ℤ_[l₂] O] (f : O₀ →+* O) : f.IsIntegral := by
  subst h
  cases Subsingleton.elim i₁ i₂
  refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l₁] O₀) f ?_
  rw [padicInt_hom_ext (natCast_mem_maximalIdeal O) (f.comp (algebraMap ℤ_[l₁] O₀)) (algebraMap ℤ_[l₁] O)]
  exact algebraMap_isIntegral_iff.2 inferInstance

variable (D : D7)

theorem sT_congr (i : D.ntw.Tw) (s : D.ntw.Sig i) (Q : Finset (PlE D.host)) {O : Type} [CommRing O] [IsDomain O]
    {f f' : D.ntw.O0 i →+* O} (hf : Function.Injective f) (hf' : Function.Injective f')
    {ψ ψ' : Formalism.MainNotions.N.GE D.nd →* Oˣ} (h1 : f = f') (h2 : ψ = ψ') :
    sT D.loc D.ntwbr i s Q f hf ψ = sT D.loc D.ntwbr i s Q f' hf' ψ' := by
  subst h1 h2
  rfl

theorem toOk_local (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (toOk D.ntw i k) := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  refine isLocalHom_of_natCast _ (D.ntw.l i) (Nat.cast_ne_zero.2 (D.ntw.lPrime i).out.ne_zero) fun hu => ?_
  have := D.ntw.Ok_fin i k
  have := RingHom.IsIntegral.isLocalHom (f := algebraMap (D.ntw.O i) (D.ntw.Ok i k))
    (algebraMap_isIntegral_iff.2 inferInstance) (D.ntw.Ok_inj i k)
  rw [← map_natCast (algebraMap (D.ntw.O i) (D.ntw.Ok i k))] at hu
  exact D.ntw.O_l i (isUnit_of_map_unit _ _ hu)

theorem sTLoc_eq : ∀ (D : D7) (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok (D.ntw.twOf a) k)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar (D.ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (D.ntw.psiL a) ψ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sTLoc D a s = GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sT D.loc D.ntwbr (D.ntw.twOf a) s (D.nd.Q a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk D.ntw (D.ntw.twOf a) k) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.toOk_inj D.ntw (D.ntw.twOf a) k) ψ := by
  intro D a s k ψ h
  obtain ⟨O₁, _, _, _, f, gA, gB, χ, iA, iB, lA, lB, cA, cB, eA, eB⟩ :=
    GlobalTheory.Proof.dvr_of_reflects_facts.common _ _ _ _ (D.ntw.twist₂ a) (toOk D.ntw _ k) (twO_inj D.ntw a)
      (isIntegral_of_finite (D.ntw.twOf_l a) _) (toOk_inj D.ntw _ k) (toOk_local D _ k) _ _ h
  have hf : Function.Injective f := Function.Injective.of_comp (f := gA) (by
    rw [← RingHom.coe_comp, cA]; exact twO_inj D.ntw a)
  exact (sT_congr D _ s _ _ (iA.comp hf) cA.symm eA.symm).trans
    ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gA iA χ).trans
      ((GlobalTheory.SelmerFlat.sT_map_eq D _ s _ O₁ _ f hf gB iB χ).symm.trans
        (sT_congr D _ s _ (iB.comp hf) _ cB eB)))

end GlobalTheory.SelmerSameChar
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilRestrict

open scoped Pointwise

section

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x), IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem normV_eq_pow_of_isPlaceOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  have hw := comap_eq_of_isPlaceOver h h'
  have : v'.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal v'.asIdeal).symm


variable (K) in
def resG : G L Ω →* G K Ω where
  toFun σ := σ.restrictScalars K
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] theorem resG_apply (σ : G L Ω) (z : Ω) : resG K σ z = σ z := rfl

theorem continuous_resG [Algebra.IsIntegral L Ω] : Continuous (resG (L := L) (Ω := Ω) K) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  let b := Module.finBasis K E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G L Ω) (b i : Ω) : Set (G L Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i =>
    (MulAction.stabilizer (G L Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, g (b i : Ω) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rwa [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)

    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm

  rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, resG_apply, hb]

variable {A : ValuationSubring Ω}

theorem resG_mem_Dec {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) : resG K σ ∈ Dec (F := K) A := by
  have h1 : σ • A = A := hσ
  show (resG K σ) • A = A
  exact h1

theorem resG_mem_Ine {σ : G L Ω} (hσ : σ ∈ Ine (F := L) A) : resG K σ ∈ Ine (F := K) A :=
  ⟨resG_mem_Dec hσ.1, fun x hx => hσ.2 x hx⟩

theorem actsAs_resG {q f a b : ℕ} {σ : G L Ω} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (resG K σ) (f * a) (f * b) := by
  refine ⟨resG_mem_Dec hσ.1, fun x hx => ?_⟩
  have e1 : (q ^ f) ^ b = q ^ (f * b) := (pow_mul q f b).symm
  have e2 : (q ^ f) ^ a = q ^ (f * a) := (pow_mul q f a).symm
  have := hσ.2 x hx
  rw [e1, e2] at this
  exact this

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

def resWeil (h : IsPlaceOver A v) (h' : IsPlaceOver A v') : Weil h' →* Weil h :=
  ((resG K).comp (Weil h').subtype).codRestrict (Weil h) fun σ => by
    obtain ⟨f, hf⟩ := normV_eq_pow_of_isPlaceOver h h'
    obtain ⟨a, b, hab⟩ := (mem_Weil h').1 σ.2
    rw [hf] at hab
    exact (mem_Weil h).2 ⟨_, _, actsAs_resG hab⟩

theorem resWeil_apply (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h') (z : Ω) :
    (resWeil h h' σ : G K Ω) z = (σ : G L Ω) z := rfl

def resIne : Ine (F := L) A → Ine (F := K) A := fun σ => ⟨resG K (σ : G L Ω), resG_mem_Ine (K := K) (L := L) (σ := (σ : G L Ω)) σ.2⟩

theorem continuous_resIne [Algebra.IsIntegral L Ω] : Continuous (resIne (K := K) (L := L) (A := A)) :=
  ((continuous_resG (K := K)).comp continuous_subtype_val).subtype_mk _

theorem isSmooth_comp_resWeil [Algebra.IsIntegral L Ω] (h : IsPlaceOver A v) (h' : IsPlaceOver A v')
    {M : Type*} [Monoid M] {f : Weil h →* M} (hf : IsSmooth f) : IsSmooth (f.comp (resWeil h h')) := by
  have e : {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1} =
      resIne ⁻¹' {τ : Ine (F := K) A | f (ineIncl h τ) = 1} := rfl
  show IsOpen {σ : Ine (F := L) A | (f.comp (resWeil h h')) (ineIncl h' σ) = 1}
  rw [e]
  exact hf.preimage continuous_resIne

end

theorem weil_restrict : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), ∃ r : Weil h' →* Weil h, (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) ∧ ∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h'
  haveI : Algebra.IsIntegral L Ω := (IsAlgClosure.isAlgebraic (R := L) (K := Ω)).isIntegral
  exact ⟨resWeil h h', resWeil_apply h h', fun M _ f hf => isSmooth_comp_resWeil h h' hf⟩

end GlobalTheory.WeilRestrict
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem unr_eq_diag_inv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), y.unr → ∃ α : Fin y.lpDim → ℂˣ, y = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro E Ω _ _ _ _ _ A w h y hy
  obtain ⟨n, c, rfl⟩ := GlobalTheory.WeilDeligne.Unram.exists_diag hy
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by simp
  refine ⟨fun i => (c (Fin.cast hn i))⁻¹, ?_⟩
  simp only [inv_inv]
  refine WD.sound ⟨LinearEquiv.funCongrLeft ℂ ℂ (finCongr hn), fun σ v => funext fun k => ?_,
    fun v => by simp⟩
  simp [LinearEquiv.funCongrLeft_apply]

end GlobalTheory.LocLanglands
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by
  first | exact @GlobalTheory.Cyc.Procyclic.procyclic | exact GlobalTheory.Cyc.Procyclic.procyclic | (intros; apply GlobalTheory.Cyc.Procyclic.procyclic <;> assumption)
end
