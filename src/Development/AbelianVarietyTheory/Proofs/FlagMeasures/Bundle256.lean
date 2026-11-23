module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle070
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle243
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle244
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentAddIsotropicToAnisotropic
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle070
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle245
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL

namespace GlobalTheory.TypeUnifProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem valuation_natCast_prime_eq_one_of_ne_resChar {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {l : ℕ} (hl : l.Prime) (hne : l ≠ Loc.resChar p) : p.valuation F (l : F) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 F) F) l, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hne
  have : p.asIdeal.IsPrime := p.isPrime
  have hz : ((l : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hdvd : ringChar (𝓞 F ⧸ p.asIdeal) ∣ l := (ringChar.spec _ l).1 hz
  rcases (Nat.dvd_prime hl).1 hdvd with h | h
  · exfalso
    have h1 : ((1 : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := (ringChar.spec _ 1).2 (by rw [h])
    simp at h1
  · exact h.symm

private theorem vE_algebraMap_ιF_eq_neg_log_valuation {D : D7} (p : PlF D) (L : Loc.LocE (D.s.atP p).Fp (D.s.atP p).Ep)
    {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) {x : D.host.F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF x)) =
      -WithZero.log (p.valuation D.host.F x) := by
  have := (D.s.atP p).lf
  refine GlobalTheory.ResProd.vE_eq_neg_log p L (D.s.atP p).ιF (D.s.atP p).dense ?_ hϖ hx
  intro a b
  rw [← Valuation.Compatible.vle_iff_le]
  exact (D.s.atP p).val a b

private theorem exists_theta_eq_ιF_valuation_eq_g_mul {D : D7} (Z : LocDat D) (p : PlF D) :
    ∃ t : D.host.F, t ≠ 0 ∧ LocNG.theta (Z.M p) = (D.s.atP p).ιF t ∧
      p.valuation D.host.F t = p.valuation D.host.F ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := Z.agree p
  have hss := D.s_split p
  have hg0 := D.host.g_prime 0
  have hg1 := D.host.g_prime 1
  have hgne := D.host.g_ne
  unfold LocNG.theta
  cases hM : (Z.M p).split with
  | none =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hS] at hss
      have h0 : D.host.g 0 ≠ Loc.resChar p := fun h => by simp [h] at hss
      have h1 : D.host.g 1 ≠ Loc.resChar p := fun h => by simp [h] at hss
      refine ⟨1, one_ne_zero, (map_one _).symm, ?_⟩
      push_cast
      rw [map_mul, valuation_natCast_prime_eq_one_of_ne_resChar p hg0 h0, valuation_natCast_prime_eq_one_of_ne_resChar p hg1 h1, map_one, mul_one]
    | some sg =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
    | some sg =>
      rw [hM, hS] at hsp
      obtain ⟨-, hq⟩ := hsp
      have hl : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
      have hmem : Loc.resChar p = D.host.g 0 ∨ Loc.resChar p = D.host.g 1 := by
        have := hss.1 (by rw [hS]; rfl)
        simpa using this
      refine ⟨(Loc.resChar p : D.host.F), Nat.cast_ne_zero.2 hl.ne_zero, ?_, ?_⟩
      · change ((g.q : (D.s.atP p).Fp)) = _
        rw [hq, sg.q_eq, map_natCast]
      · push_cast
        rw [map_mul]
        rcases hmem with h | h
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg1 (by rw [h]; exact hgne.symm), mul_one, h]
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg0 (by rw [h]; exact hgne), one_mul, h]

theorem modK_theta {D : D7} (Z : LocDat D) (p : PlF D) {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) :
    (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (resQ ϖ : ℝ) ^
      (-(2 * vE (Z.M p).L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))))) := by
  obtain ⟨hOK, -⟩ := Z.agree p
  obtain ⟨t, ht, hθ, hv⟩ := exists_theta_eq_ιF_valuation_eq_g_mul Z p
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  rw [hθ, (GlobalTheory.BaseModule.modK_algebraMap (Z.M p) hOK ϖ hϖ).2 _ ((map_ne_zero _).2 ht),
    vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ ht, vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ hx, hv]

noncomputable def placesOf {D : D7} (Z : LocDat D) : Places D.host.F D.host.E D.conjF where
  quad := D.sp.cm.deg2
  loc := D.s.atP
  L := fun p => (Z.M p).L
  L_cj := Z.hcj

theorem card_infinite (D : D7) :
    Fintype.card (InfinitePlace D.host.E) = Module.finrank ℚ D.host.F := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have : IsTotallyComplex D.host.E := IsCMField.to_isTotallyComplex
  have h1 := IsTotallyComplex.finrank (K := D.host.E)
  have h2 := D.sp.cm.deg2
  have h3 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

theorem main : ∀ (D : D7) (Z : LocDat D), (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧ ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    have := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  obtain ⟨hfin, hprod⟩ := GlobalTheory.ResProd.prod_resQ_zpow (placesOf Z) ϖ hϖ _ hx
  have hfin' : {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
      ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0}.Finite := hfin
  have hprod' : ∏ᶠ p : PlF D, (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp
      (D.s.atP p).Ep ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) =
      |((Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) : ℚ) : ℝ)| := hprod
  have hterm : ∀ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ^ 2)⁻¹ := by
    intro p
    rw [modK_theta Z p (hϖ p), zpow_neg, mul_comm, zpow_mul]
    norm_cast
  have hsub : (Function.mulSupport fun p : PlF D => (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ⊆
      {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0} := by
    intro p hp
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_ofPred_eq] at hp ⊢
    intro h0
    apply hp
    rw [h0, zpow_zero]
  have hfs := hfin'.subset hsub
  simp_rw [hterm]
  refine ⟨hfs.subset ?_, ?_⟩
  · intro p hp
    simp only [Function.mem_mulSupport, ne_eq] at hp ⊢
    intro h1
    apply hp
    rw [h1, one_pow, inv_one]
  · have hn : Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) =
        ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ) ^ Module.finrank ℚ D.host.F := by
      rw [← map_natCast (algebraMap ℚ D.host.F), Algebra.norm_algebraMap]
    rw [finprod_inv_distrib, ← finprod_pow hfs, hprod', card_infinite D, hn]
    push_cast
    rw [abs_of_nonneg (by positivity), ← pow_mul]
    ring

end GlobalTheory.TypeUnifProd
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaces

variable (D : D7)

theorem embS_injective : Function.Injective (embS D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem mem_cm_iff (φ : D.host.E →+* ℂ) :
    φ ∈ D.host.cmType ↔ ∃ τ, embS D τ = φ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 h
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  · rintro ⟨τ, rfl⟩
    exact ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

theorem range_iff (φ : D.host.E →+* ℂ) :
    (∃ τ, embS D τ = φ) ↔ ¬ ∃ τ, embS D τ = ComplexEmbedding.conjugate φ := by
  rw [← mem_cm_iff, ← mem_cm_iff]
  exact D.host.der.cmType.1 φ

theorem ne_conj (τ τ' : D.what₂.Tau) : embS D τ' ≠ ComplexEmbedding.conjugate (embS D τ) :=
  fun h => (range_iff D _).1 ⟨τ, rfl⟩ ⟨τ', h⟩

theorem sum_bijective : Function.Bijective
    (Sum.elim (embS D) (fun τ => ComplexEmbedding.conjugate (embS D τ))) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (embS_injective D h)
    · exact absurd h (ne_conj D _ _)
    · exact absurd h.symm (ne_conj D _ _)
    · exact congrArg _ (embS_injective D (star_injective h))
  · intro φ
    by_cases h : ∃ τ, embS D τ = φ
    · obtain ⟨τ, hτ⟩ := h
      exact ⟨Sum.inl τ, hτ⟩
    · obtain ⟨τ, hτ⟩ := not_not.1 (fun h' => h ((range_iff D φ).2 h'))
      refine ⟨Sum.inr τ, ?_⟩
      show star (embS D τ) = φ
      rw [hτ]
      exact star_star φ

theorem existsUnique_place (w : InfinitePlace D.host.E) :
    ∃! τ, InfinitePlace.mk (embS D τ) = w := by
  have hex : ∃ τ, InfinitePlace.mk (embS D τ) = w := by
    obtain ⟨τ | τ, h⟩ := (sum_bijective D).2 w.embedding
    · exact ⟨τ, by rw [show embS D τ = w.embedding from h, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      rw [← InfinitePlace.mk_conjugate_eq,
        show ComplexEmbedding.conjugate (embS D τ) = w.embedding from h, InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  refine ⟨τ, hτ, fun τ' h' => ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 (h'.trans hτ.symm) with h | h
  · exact embS_injective D h
  · exact absurd h.symm (ne_conj D _ _)

theorem prod_norm (a : D.host.E) :
    ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have hb : Function.Bijective (fun τ => InfinitePlace.mk (embS D τ)) :=
    (Function.bijective_iff_existsUnique _).2 (existsUnique_place D)
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [Rat.cast_abs] at h
  rw [← h, ← hb.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hc : (InfinitePlace.mk (embS D τ)).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff]
    exact fun hr => ne_conj D τ τ (ComplexEmbedding.isReal_iff.1 hr).symm
  rw [hc.mult_eq_two, InfinitePlace.apply]

theorem placeProd_eq (X : (D.host.E →+* ℂ) → ℝ) (h0 : ∀ φ, 0 ≤ X φ)
    (hc : ∀ φ, X (ComplexEmbedding.conjugate φ) = X φ) : placeProd X = ∏ τ, X (embS D τ) := by
  unfold placeProd
  rw [← (sum_bijective D).prod_comp, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hc]
  exact Real.sqrt_mul_self (Finset.prod_nonneg fun τ _ => h0 _)

theorem finrank_E : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
  ring

theorem finrank_F : finrank ℚ D.host.F = D.R.f := by
  have h := finrank_mul_finrank ℚ D.host.F D.host.E
  rw [finrank_E, D.sp.cm.deg2] at h
  omega

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

theorem absNorm_ddS :
    ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  unfold ddS Host.rdE
  rw [FractionalIdeal.coeIdeal_absNorm, h2, ← finrank_E, one_div,
    Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

end GlobalTheory.RealPlaces

theorem GlobalTheory.real_places_facts : ∀ D : D7, Fintype.card D.what₂.Tau = D.R.f ∧ finrank ℚ D.host.E = 2 * D.R.f ∧ finrank ℚ D.host.F = D.R.f ∧ D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.rdE ∧ (∀ τ (a : D.host.E), embS D τ (star a) = starRingEnd ℂ (embS D τ a)) ∧ (∀ a : D.host.E, ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) ∧ (∀ X : (D.host.E →+* ℂ) → ℝ, (∀ φ, 0 ≤ X φ) → (∀ φ, X (NumberField.ComplexEmbedding.conjugate φ) = X φ) → placeProd X = ∏ τ, X (embS D τ)) ∧ ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) ∧ (∀ w : InfinitePlace D.host.E, ∃! τ, InfinitePlace.mk (embS D τ) = w) := by
  intro D
  refine ⟨D.what₂.card_Tau, GlobalTheory.RealPlaces.finrank_E D, GlobalTheory.RealPlaces.finrank_F D, D.R.rS_two.symm,
    GlobalTheory.RealPlaces.one_le_rdE D, fun τ a => D.sp.cm.cmUnram.2.1 _ a, GlobalTheory.RealPlaces.prod_norm D,
    GlobalTheory.RealPlaces.placeProd_eq D, GlobalTheory.RealPlaces.absNorm_ddS D,
    GlobalTheory.RealPlaces.existsUnique_place D⟩
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_inner_lattice_vector_anisotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  first | exact @GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | exact GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' | (intros; apply GlobalTheory.LocOver.InnerDual.exists_inner_lattice_vector_anisotropic' <;> assumption)
end

section

open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.exists_flagStep_locallyStandard_dualCoeff_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r), ∃ v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L), v ∈ Fr.Fj (a.val + 1) ∧ H.h v (Fr.es a) = 1 := by
  first | exact @GlobalTheory.locStd_exists_flag_coef_one | exact GlobalTheory.locStd_exists_flag_coef_one | (intros; apply GlobalTheory.locStd_exists_flag_coef_one <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.StdLat

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr
  obtain ⟨y, hyΛ, hyf⟩ := GlobalTheory.T.exists_dual_family_in_selfDual_lattice M hM H r Fr Λ hSD hFr
  have hy0 : ∀ (a : Fin r) (b : Fin (r + 1)), H.h (y a.castSucc) (Fr.f b) = if b = a.castSucc then 1 else 0 :=
    fun a b => hyf b a.castSucc
  obtain ⟨y', hy'Λ, hy'f, hy'y⟩ := GlobalTheory.T.exists_totallyIsotropic_dual_family_in_lattice M hM H r Fr Λ hSD hFr (fun a : Fin r => y a.castSucc) (fun a : Fin r => hyΛ _) hy0
  obtain ⟨n, hnU, hnf, hnes, hnX⟩ := GlobalTheory.T.exists_unitary_frame_dual' M H r Fr y' hy'f hy'y
  obtain ⟨L, hLset, hLin⟩ := GlobalTheory.T.exists_innerLattice_image_frame_quotient M hM H r Fr Λ hSD hFr y' hy'Λ hy'f
  have heΛ : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => hFr.1.1 _
  refine ⟨L, hLin, hLset, n, ?_, hnf, ?_⟩
  · apply Subgroup.subset_closure
    refine ⟨hnU, ?_, hnX⟩
    intro j _ v hv
    have hle : Fr.Fj j ≤ LinearMap.ker ((n : V →ₗ[E] V) - LinearMap.id) := by
      rw [FrameD.Fj, Submodule.span_le]
      rintro _ ⟨a, _, rfl⟩
      simp [FrameD.e, hnf]
    have h1 := hle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
    rw [show n v - v = 0 from h1]
    exact zero_mem _
  · exact GlobalTheory.T.unitary_image_standardLattice_eq_selfDual_lattice M H r Fr Λ hSD heΛ L hLset n hnU (fun a => hnf _) (fun a => by rw [hnes]; exact hy'Λ a) hnX

end GlobalTheory.StdLat
end

section

open Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.flagStep_locallyStandard_dualCoeff_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) (v : V), v ∈ Fr.Fj (a.val + 1) → v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L) → H.h v (Fr.es a) ∈ M.L.O := by
  first | exact @GlobalTheory.locCoef_integral | exact GlobalTheory.locCoef_integral | (intros; apply GlobalTheory.locCoef_integral <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.unitaryComplement_moves_local_terms_with_data : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  first | exact @GlobalTheory.HL.LocalMove.main | exact GlobalTheory.HL.LocalMove.main | (intros; apply GlobalTheory.HL.LocalMove.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_unipotent_add_isotropic_to_anisotropic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h (Fr.f (Fin.last r)) (y : V) = 1 → (∀ a, H.h (y : V) (Fr.es a) = 0) → ∀ x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc), ∃ n ∈ Fr.N, n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) + x ∧ (∀ w ∈ H.X Fr.f, n w = w) ∧ img n (Fr.LamStd L) = Fr.LamStd L := by
  first | exact @GlobalTheory.LocOver.ZStep.zstep | exact GlobalTheory.LocOver.ZStep.zstep | (intros; apply GlobalTheory.LocOver.ZStep.zstep <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.CellRep

lemma det_upUni {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Formalism.FourierDecayAlt.C2.UTset m) : u.det = 1 := by
  have hb : u.BlockTriangular id := fun i j h => hu.1 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [hu.2]

theorem cell_rep : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ UH (Hpk k r) → IsInCell (ZhatO k r z z' γ) p → ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ g₀ ∈ UH (Hpk k r), γ = n * g₀ * n' ∧ ZhatO k r z z' g₀ = ptMat p := by
  intro k r z z' γ p hz hz' hT hT' hγ ⟨L, U, hL, hU, hZ⟩
  set d : Fin (r + 1) → ℂ := fun b => (-1 : ℂ) ^ (r - b.val) with hd
  have hdd : ∀ b, d b * d b = 1 := fun b => by
    simp only [hd]; rw [← mul_pow]; simp
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal d with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]; simp [hdd]
  have hO : ∀ g, ZhatO k r z z' g = Zhat k r z z' g * D := fun g => by
    ext a b
    rw [hD, Matrix.mul_diagonal, mul_comm]; rfl
  have hLU : Lᴴ ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [Matrix.conjTranspose_apply, (hL j i).1 h],
     fun i => by simp [Matrix.conjTranspose_apply, (hL i i).2 rfl]⟩
  have hUU : U ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) := ⟨fun i j h => (hU i j).1 h, fun i => (hU i i).2 rfl⟩
  have hU' : D * U * D ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i j).1 h],
     fun i => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i i).2 rfl, hdd]⟩
  obtain ⟨ha, -, hau⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z ⟨hz, hT⟩ _ hLU
  obtain ⟨hb, -, hbu⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z' ⟨hz', hT'⟩ _ hU'
  set a := Formalism.FourierDecayAlt.C2.tauM k r z Lᴴ
  set b := Formalism.FourierDecayAlt.C2.tauM k r z' (D * U * D)
  have hS : ∀ (w : Fin (2 * r + k + 1) → ℂ) (n : MatKR k r), n ∈ Nset k r → n ∈ Sset k r w :=
    fun w n hn => ⟨1, ⟨WeylGroupFacts.uh_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩,
      Matrix.one_mulVec _⟩, n, hn, (Matrix.one_mul n).symm⟩
  have hai := WeylGroupFacts.mem_n_inv ha
  have hbi := WeylGroupFacts.mem_n_inv hb
  have hau' : IsUnit a.det := WeylGroupFacts.isUnit_of_uh ha.1
  have hbu' : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
  have hg : a * γ * b⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul ha.1 hγ) hbi.1
  have he : γ = a⁻¹ * (a * γ * b⁻¹) * b := by
    rw [Matrix.mul_assoc a, Matrix.nonsing_inv_mul_cancel_left _ _ hau',
      Matrix.nonsing_inv_mul_cancel_right _ _ hbu']
  refine ⟨a⁻¹, hai, b, hb, a * γ * b⁻¹, hg, he, ?_⟩
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ a (hS z a ha) b (hS z' b hb)
    (a * γ * b⁻¹)
  rw [← he, hau, hbu, Matrix.conjTranspose_conjTranspose] at hE
  have h1 : L * ZhatO k r z z' (a * γ * b⁻¹) * U = L * ptMat p * U := by
    rw [← hZ, hO, hO γ, hE]
    simp only [Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hLu : IsUnit L.det := by
    have := det_upUni hLU
    rw [Matrix.det_conjTranspose] at this
    have h2 : L.det = 1 := by simpa using congrArg star this
    rw [h2]; exact isUnit_one
  have hUu : IsUnit U.det := by rw [det_upUni hUU]; exact isUnit_one
  have h2 := congrArg (fun X => L⁻¹ * (X * U⁻¹)) h1
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hUu, Matrix.nonsing_inv_mul_cancel_left _ _ hLu] using h2

end GlobalTheory.CellRep
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.countParameterConditions_of_sizeHypotheses : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ), 0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl → Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT → AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  first | exact @GlobalTheory.countClauses_of_sizeHyp | exact GlobalTheory.countClauses_of_sizeHyp | (intros; apply GlobalTheory.countClauses_of_sizeHyp <;> assumption)
end
