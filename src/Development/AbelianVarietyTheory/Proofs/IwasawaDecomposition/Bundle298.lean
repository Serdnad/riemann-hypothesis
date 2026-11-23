module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle283
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle107
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InertPlaceConj

open GlobalTheory.SelfDualGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isInertAt_of_not_split (w : HeightOneSpectrum (𝓞 E))
    (hu : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (hs : ¬ IsSplitAt w) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w := by
  classical
  haveI := w.isPrime
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = w.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal).1 hu).2
  have h2 : ¬ (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (w.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = w.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    let u : HeightOneSpectrum (𝓞 E) := ⟨p, hpp, hp0⟩
    have hu' : u.under (𝓞 (maximalRealSubfield E)) = v := by
      ext1
      exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
        (Ideal.map_le_iff_le_comap.1 hpl)).symm
    by_contra hne
    exact hs ⟨u, fun h => hne (congrArg HeightOneSpectrum.asIdeal h), hu'⟩
  obtain ⟨n, hn⟩ : ∃ n, I = w.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact w.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_sub_conj_notMem_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w.asIdeal := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have := v.isPrime
  have := w.isPrime
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E) v.asIdeal w.asIdeal
  have hsq : ¬ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ w.asIdeal ^ 2 := by
    rw [h']
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[maximalRealSubfield E] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff (le_of_eq h')).1 hsq)] at hcard
  by_contra hn
  push_neg at hn
  have hs : IsCMField.complexConj E ∈ w.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) :=
    AddSubgroup.mem_inertia.2 fun x => by
      have := w.asIdeal.neg_mem (hn x)
      rw [neg_sub] at this
      exact this
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact IsCMField.complexConj_ne_one E hs

theorem exists_isUnramInv_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s (Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal) := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w w := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨GlobalTheory.InertConj.conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := GlobalTheory.InertConj.conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv w _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ w.asIdeal ^ 2 := by
    by_contra hn
    push_neg at hn
    have h1 : w.asIdeal ≤ w.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ w.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous w (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2']
  have hres : ∃ x, Valued.v x ≤ 1 ∧ Valued.v ((σ : w.adicCompletion E →+* w.adicCompletion E) x - x) = 1 := by
    obtain ⟨x, hx⟩ := exists_sub_conj_notMem_of_inert w h
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact w.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hx)
  have hfix : (σ : w.adicCompletion E →+* w.adicCompletion E)
      (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) =
      algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) := by
    change σ _ = _
    rw [σ2']
    congr 1
    exact IsCMField.complexConj_apply_eq_self E (s : maximalRealSubfield E)
  have hunif : IsUnifV E w (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) := by
    unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq w hs1 hs2
  refine ⟨σ, _, σ2', hinv, σ3, hfix, hunif, ?_, ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hres
    exact ⟨x, hx1, hx2⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← h', Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue w

theorem exists_conj_isUnramInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  intro E _ _ _ w hu hs
  obtain ⟨s, ϖ, h1, h2⟩ := exists_isUnramInv_of_inert w (isInertAt_of_not_split w hu hs)
  exact ⟨s, ϖ, _, h1, h2⟩

end GlobalTheory.InertPlaceConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.IoCmp

theorem pure_rename {ι ι' κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : ι' → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (e' : κ → ι') (h : ∀ k, A (e k) = A' (e' k)) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g (MvPolynomial.rename e' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial ι' ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), map_mul (MvPolynomial.rename e'), MvPolynomial.rename_X, MvPolynomial.rename_X, hX, hX', hp, h]

theorem aeval_scale {L Y : Type} (f : L → Y) (s : ℂ) {N : ℕ} {Q : MvPolynomial L ℂ} (hQ : Q.IsHomogeneous N) :
    MvPolynomial.aeval (fun ℓ => MvPolynomial.C s * MvPolynomial.X (f ℓ)) Q =
      MvPolynomial.C (s ^ N) * MvPolynomial.rename f Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]

  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = N := by
    have := hQ (MvPolynomial.mem_support_iff.1 hm)
    rwa [Finsupp.degree_eq_weight_one]
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hd]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Function.comp_apply, map_pow,
    Finsupp.degree_apply]
  ring

theorem isHomogeneous_of_span {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop)
    (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k (HHa r n k cc isX a)) :
    P.IsHomogeneous (∑ σ, ∑ i : Fin (r σ), a σ i) := by
  refine (Submodule.span_le (p := MvPolynomial.homogeneousSubmodule _ k _)).2 (fun Q hQ m hm => ?_) hP
  have h := hQ.2.2 m (MvPolynomial.mem_support_iff.2 hm)
  refine Eq.trans (b := m.degree) (by rw [Finsupp.degree_eq_weight_one]; rfl) ?_
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => h σ i

theorem lieFac_eq_pow {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (hx : 0 < xiR D)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    lieFac Dw (xiR D) a = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ ^ (∑ σ, ∑ i : Fin (Dw.mult σ), a (σ, i)) := by
  have h : 0 < 2 * Real.pi * xiR D := by positivity
  have h2 : (Real.sqrt (2 * Real.pi * xiR D))⁻¹ = Real.exp (-(Real.log (2 * Real.pi * xiR D) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  rw [h2, ← Real.exp_nat_mul, lieFac]
  congr 1
  push_cast
  ring

theorem two_div_fockScale (D : D7) (τ : D.what₂.Tau) : 2 / fockScale D τ = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ := by
  rw [fockScale, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq, div_mul_cancel_left₀ two_ne_zero]

theorem unitMap_submatrix {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (π : Fin m → Fin m)
    (c : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap B (B'.submatrix id π) c j = Formalism.IndefR.Datum.unitMap B B' (π c) j := by
  unfold Formalism.IndefR.Datum.unitMap
  congr 1
  ext a b
  by_cases h : b = j
  · subst h
    simp
  · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

theorem pureTensorO_rename {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1)
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (Z Z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (π : D.what₂.Tau → Fin T.rank → Fin T.rank) (hZ : ∀ τ, Z' τ = (Z τ).submatrix id (π τ)) {κ : Type} (ρ : κ → D.what₂.Tau)
    (c : κ → Fin T.rank) (b : κ → Fin S.rank) (Q : MvPolynomial κ ℂ) :
    pureTensorO ψ θ S T (fun _ => 1) s B Z f (MvPolynomial.rename (fun k => (ρ k, π (ρ k) (c k), b k)) Q) =
      pureTensorO ψ θ S T (fun _ => 1) s B Z' f (MvPolynomial.rename (fun k => (ρ k, c k, b k)) Q) := by
  have hX : ∀ B' v Q, pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f Q) := fun B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  refine pure_rename (hX Z) (hX Z') _ _ (fun k => ?_) Q
  simp only [aPlusAll, hZ, unitMap_submatrix]

end GlobalTheory.OneMapRef.IoCmp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  first | exact @GlobalTheory.Mem.LiftModG.exists_lift_mod_g | exact GlobalTheory.Mem.LiftModG.exists_lift_mod_g | (intros; apply GlobalTheory.Mem.LiftModG.exists_lift_mod_g <;> assumption)
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.TameJoint

theorem exists_pow_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  intro E Ω _ _ _ _ _ M _ φ P A L γ π w hA hker hL hγ hw hγL hπ he σ hσ
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hn : 0 < L := Nat.pos_of_ne_zero hL0
  have hLA : ¬ A.valuation (L : Ω) < 1 := by
    intro h
    apply hL
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ L = 1 := by
    rw [hζ, div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
    rw [← he]; exact pow_ne_zero _ hπ
  have hred : ∀ {N : Type} [Monoid N] (x : N), x ^ L = 1 → ∀ a : ℕ, x ^ a = x ^ (a % L) := by
    intro N _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a L, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ L = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he' | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hL0).ne
    · exact he'
    · exact absurd hp (one_lt_pow₀ hg hL0).ne'

  have hfixζ : ∀ τ ∈ ReciprocityTheory.Gal.Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ L = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := GlobalTheory.TameCharDet.eq_of_pow_eq_one_of_val_lt A L hLA h1 (one_pow L) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hopenH : ∀ (H : Subgroup (Formalism.ConjugateSelfDual.G E Ω)), IsOpen (H : Set (Formalism.ConjugateSelfDual.G E Ω)) →
      ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ H, τ * g ∈ U) → IsOpen U := by
    intro H hH U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hH.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hHo _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hfib : ∀ c : M, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | φ τ = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopenH _ hker _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [map_mul, (MonoidHom.mem_ker).1 hg, mul_one]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range L, {τ | φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (hfib _).inter (hloc _)
  let Q : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ ReciprocityTheory.Gal.Ine (F := E) A ∧ ∃ a : ℕ, φ τ = φ γ ^ a ∧ τ π = ζ ^ a * π
  have hQ : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), Q τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A := inv_mem hxI
      have hex : a * (L - 1) + a = a * L := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (L - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγL, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (L - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (L - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (L - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hQ τ hτ
    refine Set.mem_biUnion (x := a % L) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγL a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  simp only [T, Set.mem_iUnion] at hσT
  obtain ⟨a, -, h⟩ := hσT
  exact ⟨a, h⟩

end GlobalTheory.TameJoint
end
