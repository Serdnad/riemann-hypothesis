module

public import Mathlib.FieldTheory.Finite.Basic
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Topology.Instances.Matrix
public import ReciprocityTheory.Automorphisms.Bundle001
public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.WeilDeligne

theorem frobAlg_pow_apply (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (m : ℕ) (a : L) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ m) a = a ^ (Fintype.card K ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply,
      ← pow_mul, pow_succ]

end GlobalTheory.WeilDeligne


open GlobalTheory.WeilDeligne Pointwise in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.WeilDeligne.exists_pow_normV_resPow (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) :
    IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω,
      g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x →
        A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  intro hA L hL g hg
  classical
  set Q := primeBelow (F := E) A with hQ
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) Q
    (by rw [show Ideal.under (𝓞 E) Q = w.asIdeal from under_primeBelow hA]
        exact w.isMaximal)
  letI : Field (IntCl E Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI : Algebra.IsIntegral (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q w.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  have hqc : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  have hq1 : 1 < normV w := one_lt_normV w

  have hgQ : g • Q = Q := by rw [hQ, ← primeBelow_smul, (mem_Dec.mp hg)]
  let ψ := Ideal.Quotient.stabilizerHom Q w.asIdeal (Ω ≃ₐ[E] Ω) ⟨g, hgQ⟩
  have hψ : ∀ b : IntCl E Ω, ψ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g • b) :=
    fun b => Ideal.Quotient.stabilizerHom_apply _ _ _ _ b

  set n := Module.finrank E L with hn
  set M := n.factorial with hM

  have hres : ∀ b : IntCl E Ω, (b : Ω) ∈ L →
      (Ideal.Quotient.mk Q b) ^ (normV w ^ M) = Ideal.Quotient.mk Q b := by
    intro b hbL
    set y := Ideal.Quotient.mk Q b with hy
    have hbi : IsIntegral (𝓞 E) (b : Ω) := b.2
    set f := minpoly (𝓞 E) (b : Ω) with hf
    have hdeg : f.natDegree ≤ n := by
      have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' E hbi
      have h2 : (minpoly E (b : Ω)).natDegree ≤ n := by
        have h3 := minpoly.algebraMap_eq (A := E) (algebraMap L Ω).injective (⟨b, hbL⟩ : L)
        rw [show (b : Ω) = algebraMap L Ω ⟨b, hbL⟩ from rfl, h3]
        exact minpoly.natDegree_le _
      rwa [h1, (minpoly.monic hbi).natDegree_map] at h2
    have hbf : Polynomial.aeval b f = 0 := by
      apply Subtype.ext
      rw [Polynomial.aeval_subalgebra_coe]
      exact minpoly.aeval _ _
    have hy0 : Polynomial.aeval y (f.map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, hy, ← Ideal.Quotient.mkₐ_eq_mk (𝓞 E),
        Polynomial.aeval_algHom_apply, hbf, map_zero]
    have hmon := (minpoly.monic hbi).map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))
    have hyInt : IsIntegral (𝓞 E ⧸ w.asIdeal) y := ⟨_, hmon, hy0⟩
    have hdvd := minpoly.dvd (𝓞 E ⧸ w.asIdeal) y hy0
    have hle : (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree ≤ n := by
      have := Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero
      rw [(minpoly.monic hbi).natDegree_map] at this
      exact this.trans hdeg
    have hpos := minpoly.natDegree_pos hyInt
    set K' := IntermediateField.adjoin (𝓞 E ⧸ w.asIdeal) ({y} : Set (IntCl E Ω ⧸ Q))
    haveI : FiniteDimensional (𝓞 E ⧸ w.asIdeal) K' := IntermediateField.adjoin.finiteDimensional hyInt
    haveI : Finite K' := Module.finite_of_finite (𝓞 E ⧸ w.asIdeal)
    letI : Fintype K' := Fintype.ofFinite _
    have hcard : Fintype.card K' = normV w ^ (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree := by
      rw [Module.card_eq_pow_finrank (K := 𝓞 E ⧸ w.asIdeal), hqc,
        IntermediateField.adjoin.finrank hyInt]
    obtain ⟨m, hm⟩ := Nat.dvd_factorial hpos hle
    have key := FiniteField.pow_card_pow m
      (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : K')
    rw [hcard, ← pow_mul, ← hm] at key
    exact congrArg Subtype.val key

  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q)
  let τ := frob ^ M
  have hτ : ∀ y, τ y = y ^ (normV w ^ M) := fun y => by
    rw [frobAlg_pow_apply, hqc]
  let R := IntermediateField.fixedField (Subgroup.zpowers τ)
  have hmemR : ∀ y, y ∈ R ↔ y ^ (normV w ^ M) = y := by
    intro y
    rw [← hτ]
    constructor
    · intro h; exact (IntermediateField.mem_fixedField_iff _ _).mp h τ (Subgroup.mem_zpowers τ)
    · intro h
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      have hs : τ ∈ MulAction.stabilizer
        ((IntCl E Ω ⧸ Q) ≃ₐ[𝓞 E ⧸ w.asIdeal] (IntCl E Ω ⧸ Q)) y := h
      exact (Subgroup.zpowers_le.mpr hs) hf
  have hqM : 1 < normV w ^ M := Nat.one_lt_pow (Nat.factorial_ne_zero n) hq1
  haveI : Finite R := by
    have hfin := (Polynomial.X ^ (normV w ^ M) - Polynomial.X :
      Polynomial (𝓞 E ⧸ w.asIdeal)).rootSet_finite (IntCl E Ω ⧸ Q)
    refine Set.Finite.to_subtype (hfin.subset fun y hy => ?_)
    rw [Polynomial.mem_rootSet]
    refine ⟨Polynomial.X_pow_sub_X_ne_zero hqM, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X]
    rw [(hmemR y).mp hy, sub_self]

  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 E ⧸ w.asIdeal) R).2 (ψ.restrictNormal R)
  have hj' : FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) R ^ (j : ℕ) =
      ψ.restrictNormal R := hj
  have hψR : ∀ y ∈ R, ψ y = y ^ (normV w ^ (j : ℕ)) := by
    intro y hy
    have h1 := AlgEquiv.restrictNormal_commutes ψ R ⟨y, hy⟩
    rw [← hj', frobAlg_pow_apply, hqc] at h1
    simpa [IntermediateField.algebraMap_apply] using h1.symm

  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero n)
  refine ⟨m * (j : ℕ), fun x hxL hx => ?_⟩
  let b : IntCl E Ω := ⟨x, hx.tower_top⟩
  have hbR : Ideal.Quotient.mk Q b ∈ R := (hmemR _).mpr (hres b hxL)
  have hfix : ∀ t : ℕ, (Ideal.Quotient.mk Q b) ^ (normV w ^ (M * t)) = Ideal.Quotient.mk Q b := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hres b hxL]
  have h2 : (g • b) ^ (normV w ^ (m * (j : ℕ))) - b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← hψ, hψR _ hbR, ← pow_mul, ← pow_add,
      show (j : ℕ) + m * j = M * j by rw [hM, hm, Nat.succ_mul, add_comm], hfix, sub_self]
  exact h2
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem valued_natCast_adicCompletion_le_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ),
    Valued.v ((N : v.adicCompletion F)) ≤ 1 := by
  intro F _ _ v N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (le_of_eq (map_one _))

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem valued_absNorm_lt_one_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by
  have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v
    ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2 (Ideal.absNorm_mem _)
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  convert h using 2
  have : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) := by simp
  rw [this]
  rfl

theorem exists_nat_congruence_le_open_subgroup_GL :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (K : Subgroup (GL (Fin n) (v.adicCompletion F))), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) →
    ∃ M : ℕ, 0 < M ∧ ∀ g : GL (Fin n) (v.adicCompletion F),
      (∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((M : v.adicCompletion F))) →
      (∀ i j, Valued.v (((g⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤ Valued.v ((M : v.adicCompletion F))) → g ∈ K := by
  intro F _ _ v n K hK
  by_contra hcon
  push Not at hcon
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hq0 : 0 < q := lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
  choose g hg1 hg2 hg3 using fun k : ℕ => hcon (q ^ k) (pow_pos hq0 k)
  have hlt : ‖(q : v.adicCompletion F)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.2 (valued_absNorm_lt_one_adicCompletion F v)
  have hpow : Filter.Tendsto (fun k : ℕ => ‖((q ^ k : ℕ) : v.adicCompletion F)‖)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
  have key : ∀ A : ℕ → Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (∀ k i j, Valued.v (A k i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
        Valued.v ((q ^ k : ℕ) : v.adicCompletion F)) →
      Filter.Tendsto A Filter.atTop (nhds 1) := by
    intro A hA
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun k => Valued.toNormedField.norm_le_iff.2 (hA k i j)) hpow
  have hlim : Filter.Tendsto g Filter.atTop (nhds 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds (key _ hg1) ?_
    exact (MulOpposite.continuous_op.tendsto _).comp (key _ hg2)
  obtain ⟨k, hk⟩ := (hlim.eventually (hK.mem_nhds K.one_mem)).exists
  exact hg3 k hk

end GlobalTheory
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct

namespace GlobalTheory.SplitComp

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

theorem exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by
  have h := IsCMField.complexConj_ne_one L
  obtain ⟨x, hx⟩ : ∃ x : L, IsCMField.complexConj L x ≠ x := by
    by_contra hc
    push Not at hc
    exact h (AlgEquiv.ext hc)
  refine ⟨x - IsCMField.complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

theorem exists_real_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (x : L) :
    ∃ a b : maximalRealSubfield L, x = a • (1 : L) + b • θ := by
  have h2 : IsCMField.complexConj L (2 : L) = 2 := map_ofNat _ 2
  have ha : (x + IsCMField.complexConj L x) / 2 ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, h2]
    ring
  have hb : (x - IsCMField.complexConj L x) / (2 * θ) ∈ maximalRealSubfield L := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul,
      IsCMField.complexConj_apply_apply, h2, hθ]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change x = (x + IsCMField.complexConj L x) / 2 * 1 + (x - IsCMField.complexConj L x) / (2 * θ) * θ
  field_simp
  ring

theorem exists_tmul_add (θ : L) (h0 : θ ≠ 0) (hθ : IsCMField.complexConj L θ = -θ) (z : AL L) :
    ∃ a b : AFplus L, z = (1 : L) ⊗ₜ[maximalRealSubfield L] a + θ ⊗ₜ[maximalRealSubfield L] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x c =>
    obtain ⟨a, b, rfl⟩ := exists_real_add L θ h0 hθ x
    exact ⟨a • c, b • c, by rw [add_tmul, smul_tmul, smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩

theorem compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L),
    s.proj z = 0 → s.proj (conjAL L z) = 0 → compAt L s.v z = 0 := by
  intro L _ _ _ s z h1 h2
  obtain ⟨θ, h0, hθ⟩ := exists_imag L
  obtain ⟨a, b, rfl⟩ := exists_tmul_add L θ h0 hθ z
  have e1 : evalAt L s.v a + s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj] using h1
  have e2 : evalAt L s.v a - s.i θ * evalAt L s.v b = 0 := by
    simpa [SplitPlace.proj, conjAL, hθ, neg_tmul, sub_eq_add_neg] using h2
  have hi : s.i θ ≠ 0 := (map_ne_zero s.i).mpr h0
  have : CharZero (s.v.adicCompletion (maximalRealSubfield L)) :=
    algebraRat.charZero _
  have ha : evalAt L s.v a = 0 := by linear_combination (e1 + e2) / 2
  have hb : evalAt L s.v b = 0 := by
    rw [ha, zero_add] at e1
    exact (mul_eq_zero.mp e1).resolve_left hi
  simp [compAt, ha, hb]

end GlobalTheory.SplitComp
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitPlaceExt

variable {L : Type} [Field L] [NumberField L] [IsCMField L]


open NumberField IsDedekindDomain in
variable {L : Type} [Field L] [NumberField L] [IsCMField L] in
theorem _root_.GlobalTheory.SplitPlaceExt.eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : _root_.ReciprocityTheory.Aut.SplitPlace L), s'.w = s.w → s' = s := by
  intro L _ _ _ s s' h
  have hv : s'.v = s.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  obtain rfl : v = v' := hv.symm
  have key : ∀ x : 𝓞 L, Valued.v (i' x) < 1 ↔ Valued.v (i x) < 1 := fun x =>
    Iff.of_eq (congrArg (fun P : HeightOneSpectrum (𝓞 L) => x ∈ P.asIdeal) h)
  obtain ⟨e, he1, he2⟩ := _root_.GlobalTheory.SplitSep.exists_sep (L := L) ⟨v, i⟩
  set c := i.comp (IsCMField.complexConj L).toAlgHom with hc
  have hce : c e = i (IsCMField.complexConj L e) := rfl
  have hic : i ≠ c := by
    intro hi
    have : Valued.v (i e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 this.ne
  have hi'c : i' ≠ c := by
    intro hi
    have : Valued.v (i' e) < 1 := by rw [hi, hce]; exact he2
    exact absurd he1 ((key e).1 this).ne
  by_contra hne
  have hii' : i' ≠ i := fun hh => hne (by rw [hh])
  have hinj : Function.Injective ![i, c, i'] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have h3 : Nat.card (Fin 3) ≤ _ := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  have h2 := card_algHom_le_finrank (maximalRealSubfield L) L
    (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  omega

end GlobalTheory.SplitPlaceExt
end
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem frob_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  intro E Ω _ _ _ _ v A hA τ τ' hτ hτ'
  obtain ⟨hτD, hτF⟩ := hτ
  obtain ⟨hτ'D, hτ'F⟩ := hτ'

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := inferInstance
  letI : Fintype (𝓞 E ⧸ v.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ v.asIdeal) with hpdef
  haveI : CharP (𝓞 E ⧸ v.asIdeal) p := ringChar.charP _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ v.asIdeal) p
  have hq : normV v = p ^ (n : ℕ) := by
    simp only [normV, Nat.card_eq_fintype_card, hcard]

  have hpv : ((p : 𝓞 E)) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hpA : A.valuation (p : Ω) < 1 := by
    have := (hA (p : 𝓞 E)).mpr hpv
    simpa using this

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hpA
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h := CharP.ringChar_of_prime_eq_zero (R := IsLocalRing.ResidueField A) hp hpk
    rw [← h]; exact ringChar.charP _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar (IsLocalRing.ResidueField A) p := ExpChar.prime hp
  refine ⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hτ'D) hτD, fun x hx => ?_⟩
  have hxA : x ∈ A := A.valuation_le_one_iff x |>.mp hx
  set z := (τ'⁻¹ : G E Ω) (τ x) with hz
  have hzA : z ∈ A := by
    rw [hz, apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hτ'D), apply_mem_iff_of_mem_Dec hτD]
    exact hxA
  have hτ'z : τ' z = τ x := mul_inv_apply (τ x)
  have h1 := hτ'F z ((A.valuation_le_one_iff z).mpr hzA)
  rw [hτ'z] at h1
  have h2 := hτF x hx
  have h3 : A.valuation (z ^ normV v - x ^ normV v) < 1 := by
    have e : z ^ normV v - x ^ normV v = (τ x - x ^ normV v) - (τ x - z ^ normV v) := by ring
    rw [e]; exact Valuation.map_sub_lt _ h2 h1

  have hres : IsLocalRing.residue A ⟨z, hzA⟩ ^ (p ^ (n : ℕ)) = IsLocalRing.residue A ⟨x, hxA⟩ ^ (p ^ (n : ℕ)) := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    rw [← hq]
    simpa using h3
  have hinj := iterateFrobenius_inj (IsLocalRing.ResidueField A) p (n : ℕ)
  have heq : IsLocalRing.residue A ⟨z, hzA⟩ = IsLocalRing.residue A ⟨x, hxA⟩ := by
    apply hinj
    rw [iterateFrobenius_def, iterateFrobenius_def]
    exact hres
  have hzx : (⟨z, hzA⟩ - ⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, heq, sub_self]
  have := (ValuationSubring.valuation_lt_one_iff A _).mp hzx
  have e2 : (τ'⁻¹ * τ) x = z := rfl
  rw [e2]
  simpa using this

end GlobalTheory
end
