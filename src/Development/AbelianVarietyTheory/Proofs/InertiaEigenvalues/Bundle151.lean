module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle135
public import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle136
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Field.ProperSpace
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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
public import Mathlib.RingTheory.Norm.Transitivity
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

namespace GlobalTheory.JR.EtFacts

theorem normE [U : Unram F E] (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have := U.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  have h2 := (IsUnit.mk0 (2 : F) two_ne_zero)
  exact (quadratic_star_structure b d hb0 hs hd U.star_fix (IsUnit.mk0 d hd0) h2).2.1 z

theorem free_L_E [Unram F E] (A : Et F E) : Module.Free E A.L := by
  have hbc := A.push.out
  exact Module.Free.of_basis (hbc.basis (Module.Free.chooseBasis F A.K))

theorem free_L_K [Unram F E] (A : Et F E) : Module.Free A.K A.L := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  exact Module.Free.of_basis b

theorem eta_NL [U : Unram F E] (A : Et F E) (y : A.L) : A.etaK (A.NL y) = 1 := by
  have := free_L_E A
  have := free_L_K A
  have h1 : Algebra.norm F (A.NL y) = Algebra.norm F (Algebra.norm E y) := by
    rw [Et.NL, Algebra.norm_norm, Algebra.norm_norm]
  rw [Et.etaK, h1, eta]
  obtain ⟨x, hx⟩ := U.unram (Algebra.norm E y)
  have hx2 : ‖Algebra.norm F (Algebra.norm E y)‖ = ‖x‖ ^ 2 := by
    rw [← norm_algebraMap' E, normE, norm_mul, U.norm_star, hx, sq]
  rw [if_pos ⟨x, hx2⟩]

theorem eta_neg_one [Unram F E] (A : Et F E) : A.etaK (-1) = 1 := by
  rw [Et.etaK, eta]
  refine if_pos ⟨1, ?_⟩
  have h : Algebra.norm F (-1 : A.K) * Algebra.norm F (-1 : A.K) = 1 := by
    rw [← map_mul]; simp
  have h' := congrArg norm h
  rw [norm_mul, norm_one] at h'
  have h0 : 0 ≤ ‖Algebra.norm F (-1 : A.K)‖ := norm_nonneg _
  simp only [norm_one, one_pow]
  nlinarith

end GlobalTheory.JR.EtFacts

namespace GlobalTheory.JR.EtFacts

theorem sq_le_range [Unram F E] (A : Et F E) :
    (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range ≤ (EtMeas.normU A).range := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  rintro _ ⟨k, rfl⟩
  refine ⟨Units.map (algebraMap A.K A.L).toMonoidHom k, Units.ext (hinj ?_)⟩
  rw [EtMeas.normU_val, hN]
  simp [A.star_K, sq]

theorem finite_quot [Unram F E] (A : Et F E) (hsq : Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range)) :
    Finite (A.Kˣ ⧸ (EtMeas.normU A).range) := by
  have : (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have := Subgroup.finiteIndex_of_le (sq_le_range A)
  exact Subgroup.finite_quotient_of_finiteIndex

theorem key_rel (A : Et F E) (a x : A.Kˣ) : (∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y) ↔
    (QuotientGroup.mk x : A.Kˣ ⧸ (EtMeas.normU A).range) = QuotientGroup.mk a := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨hy.unit, Units.ext ?_⟩
    simp [h, Et.NL, EtMeas.normU]
  · rintro ⟨y, h⟩
    refine ⟨y, y.isUnit, ?_⟩
    have := congrArg Units.val h
    simp only [EtMeas.normU, Units.coe_map, Units.val_mul] at this
    rw [Et.NL, this]; simp

theorem finite_reps_exists [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) :
    ∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S := by
  refine ⟨Set.range (Quotient.out : A.Kˣ ⧸ (EtMeas.normU A).range → A.Kˣ), Set.finite_range _, fun a =>
    ⟨Quotient.out (QuotientGroup.mk a : A.Kˣ ⧸ (EtMeas.normU A).range),
    ⟨⟨_, rfl⟩, (key_rel A _ _).2 (QuotientGroup.out_eq' _)⟩, ?_⟩⟩
  rintro _ ⟨⟨q, rfl⟩, h⟩
  rw [← (key_rel A _ _).1 h, QuotientGroup.out_eq']

theorem finite_of_reps [Unram F E] (A : Et F E) (hf : Finite (A.Kˣ ⧸ (EtMeas.normU A).range)) (S : Set A.Kˣ)
    (hS : A.IsReps S) : S.Finite := by
  have hinj : Function.Injective (fun x : S => (QuotientGroup.mk (x : A.Kˣ) : A.Kˣ ⧸ (EtMeas.normU A).range)) := by
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    obtain ⟨z, -, hz⟩ := hS x'
    have e1 := hz x ⟨hx, (key_rel A _ _).2 h⟩
    have e2 := hz x' ⟨hx', (key_rel A _ _).2 rfl⟩
    exact Subtype.ext (e1.trans e2.symm)
  exact Set.finite_coe_iff.1 (Finite.of_injective _ hinj)

end GlobalTheory.JR.EtFacts

namespace GlobalTheory.JR.EtFacts

theorem nonunits_null [U : Unram F E] (A : Et F E) (μ : Measure A.K) (hμ : μ.IsAddHaarMeasure) :
    μ {t | ¬ IsUnit t} = 0 := by
  have := U.lcF
  have : IsArtinianRing A.K := IsArtinianRing.of_finite F A.K
  have hfin := IsArtinianRing.setOfPred_isMaximal_finite A.K
  have hsub : {t : A.K | ¬ IsUnit t} ⊆ ⋃ m ∈ {I : Ideal A.K | I.IsMaximal}, (m : Set A.K) := by
    intro t ht
    obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits (show t ∈ nonunits A.K from ht)
    exact Set.mem_biUnion hm htm
  refine measure_mono_null hsub ((measure_biUnion_null_iff hfin.countable).2 fun m hm => ?_)
  have h := GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology F A.K μ hμ (m.restrictScalars F) (fun h => hm.ne_top ?_)
  · exact h
  · rw [Ideal.eq_top_iff_one]
    have : (1 : A.K) ∈ m.restrictScalars F := h ▸ Submodule.mem_top
    exact this

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (Algebra.traceForm F A.K).Nondegenerate ∧ (∀ y : A.L, IsUnit y → A.etaK (A.NL y) = 1) ∧ A.etaK (-1) = 1 ∧ (∀ᶠ v in 𝓝 (1 : A.K), ∃ s : A.K, s ^ 2 = v) ∧ (∃ S : Set A.Kˣ, S.Finite ∧ A.IsReps S) ∧ (∀ S : Set A.Kˣ, A.IsReps S → S.Finite) ∧ (∀ μ : Measure A.K, μ.IsAddHaarMeasure → μ {t | ¬ IsUnit t} = 0) ∧ IsOpen A.OK ∧ IsCompact A.OK ∧ ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ U A
  have := U.charZero; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  obtain ⟨-, -, hN, htr, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hq := finite_quot A (GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair F E A)
  refine ⟨hN, htr, ⟨fun x hx => ?_, fun x hx => ?_⟩, fun y _ => eta_NL A y, eta_neg_one A,
    (GlobalTheory.isOpenUnits_and_eventually_sq F A.K).2, finite_reps_exists A hq, finite_of_reps A hq,
    nonunits_null A, GlobalTheory.T.isOpen_finiteEtaleHermitianPair_OK F E A, GlobalTheory.T.isCompact_finiteEtaleHermitianPair_OK F E A, GlobalTheory.T.exists_subring_eq_OK F E A⟩
  · exact EtMeas.eq_zero_of_trace F A.K x fun y => by simpa using hx y
  · exact EtMeas.eq_zero_of_trace F A.K x fun y => by simpa [mul_comm] using hx y

end GlobalTheory.JR.EtFacts
end
end

section

open Matrix Polynomial

namespace GlobalTheory.CommSep

theorem commute_aeval_of_commute {E : Type} [Field E] {r : ℕ} {m A : Matrix (Fin r) (Fin r) E}
    (h : Commute m A) (p : E[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

theorem aeval_mulVec_eq_krylov {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (v c : Fin r → E) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i

  simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
  Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
  Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eq_aeval_of_commute_of_separable {E : Type} [Field E] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hs : A.charpoly.Separable) (n : Matrix (Fin r) (Fin r) E)
    (hn : n * A = A * n) : ∃ q : E[X], n = aeval A q := by
  classical
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hs
  set K := GlobalTheory.ClassParam.krylov A v with hK
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.2 hv
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_eq_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval_of_commute (Commute.refl A) _).symm
  have hnA : Commute n A := hn
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) E, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hnA, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

theorem commute_of_commute_separable : ∀ (E : Type) [Field E] (r : ℕ)
    (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E,
    m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  intro E _ r A₀ hs m n hm hn
  obtain ⟨q, rfl⟩ := eq_aeval_of_commute_of_separable A₀ hs n hn
  exact (commute_aeval_of_commute (m := m) hm q).eq

end GlobalTheory.CommSep
end

section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ N : ℕ,
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  first | exact @GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod | exact GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod | (intros; apply GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod <;> assumption)
end

section

open IsDedekindDomain NumberField

namespace GlobalTheory.LocalSpanCriterion

theorem span_local_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module (RingOfIntegers K) V] (w : HeightOneSpectrum (RingOfIntegers K))
    [Module (Formalism.L2.Col.Ow w) V] [IsScalarTower (RingOfIntegers K) (Formalism.L2.Col.Ow w) V]
    (T : Set V) (x : V) :
    x ∈ Submodule.span (Formalism.L2.Col.Ow w) T ↔
      x ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) := by
  have hmem : ∀ y : V, y ∈ Formalism.HermitianLatticesTheory.localization₂ (HeightOneSpectrum.asIdeal w)
        (Submodule.span (RingOfIntegers K) T) ↔
      ∃ s ∈ w.asIdeal.primeCompl, s • y ∈ Submodule.span (RingOfIntegers K) T := fun y => Iff.rfl
  rw [hmem]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using Submodule.subset_span hy⟩
    | zero => exact ⟨1, w.asIdeal.primeCompl.one_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
      have e : (s * t) • (y + z) = t • (s • y) + s • (t • z) := by
        rw [smul_add, mul_smul, smul_comm s t y, mul_smul]
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ t hsy) (Submodule.smul_mem _ s htz)
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl a
      refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs t.2, ?_⟩
      have hspec : (IsLocalization.mk' (Formalism.L2.Col.Ow w) r t) *
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) =
          algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) r := IsLocalization.mk'_spec _ r t
      simp only at hrt
      rw [hrt] at hspec
      have e : (s * (t : RingOfIntegers K)) • (a • y) = r • (s • y) := by
        have ht : (t : RingOfIntegers K) • (a • y) = r • y := by
          rw [← algebraMap_smul (Formalism.L2.Col.Ow w) (t : RingOfIntegers K) (a • y), smul_smul,
            mul_comm, hspec, algebraMap_smul]
        rw [mul_comm, mul_smul, smul_comm (t : RingOfIntegers K) s, ht, smul_comm s r]
      rw [e]
      exact Submodule.smul_mem _ r hsy
  · rintro ⟨s, hs, hsx⟩
    have hu : IsUnit (algebraMap (RingOfIntegers K) (Formalism.L2.Col.Ow w) s) :=
      IsLocalization.map_units (Formalism.L2.Col.Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    have h1 : s • x ∈ Submodule.span (Formalism.L2.Col.Ow w) T := by
      have := Submodule.span_le_restrictScalars (RingOfIntegers K) (Formalism.L2.Col.Ow w) T hsx
      exact this
    rw [← algebraMap_smul (Formalism.L2.Col.Ow w) s x] at h1
    obtain ⟨u, hu'⟩ := hu
    have h2 := Submodule.smul_mem _ (↑u⁻¹ : Formalism.L2.Col.Ow w) h1
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

end GlobalTheory.LocalSpanCriterion
end

section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

open Polynomial Module.End

theorem part_projector_mem_adjoin :
    ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
      [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
      [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) →
      (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) →
      (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) →
      ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) →
      ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S,
        (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧
          ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ S hS hsplit hint L _ _ _ 𝔪
  classical
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨F, hF, -⟩ := NCov.exists_finset_pts hinj hS hsplit hint
  by_cases hA : ∃ ψ0 : Algebra.adjoin O S →ₐ[O] O, NCov.cls ψ0 = 𝔪
  swap
  · push_neg at hA
    refine ⟨0, Subalgebra.zero_mem _, fun x hx => ?_, fun x _ => rfl⟩
    have : NCov.part (Algebra.adjoin O S) 𝔪 = ⊥ := by
      unfold NCov.part
      exact iSup₂_eq_bot.2 fun ψ h => absurd h (hA ψ)
    rw [this, Submodule.mem_bot] at hx
    simp [hx]
  obtain ⟨ψ0, rfl⟩ := hA
  have hmax := NCov.cls_isMaximal ψ0
  have hs : ∀ φ : Algebra.adjoin O S →ₐ[O] O, ∃ s : Algebra.adjoin O S,
      (NCov.cls φ ≠ NCov.cls ψ0 → s ∈ NCov.cls φ) ∧ s ∉ NCov.cls ψ0 := by
    intro φ
    by_cases h : NCov.cls φ = NCov.cls ψ0
    · exact ⟨1, fun h' => absurd h h', fun h1 => hmax.ne_top ((Ideal.eq_top_iff_one _).2 h1)⟩
    · have : ¬ NCov.cls φ ≤ NCov.cls ψ0 := fun hle =>
        h ((NCov.cls_isMaximal φ).eq_of_le hmax.ne_top hle)
      obtain ⟨s, hs1, hs2⟩ := SetLike.not_le_iff_exists.1 this
      exact ⟨s, fun _ => hs1, hs2⟩
  choose s hsin hsout using hs
  set FA := F.filter (fun ψ => NCov.cls ψ = NCov.cls ψ0)
  set FB := F.filter (fun ψ => NCov.cls ψ ≠ NCov.cls ψ0)
  letI : IsMulCommutative (Algebra.adjoin O S) :=
    Algebra.isMulCommutative_adjoin O (fun a ha b hb _ => hS a ha b hb)
  open scoped IsMulCommutative in
  obtain ⟨f, hfdef⟩ : ∃ f : Algebra.adjoin O S, f = ∏ φ ∈ FB, s φ := ⟨_, rfl⟩
  have hres : ∀ ψ : Algebra.adjoin O S →ₐ[O] O, ∀ u, u ∈ NCov.cls ψ ↔ IsLocalRing.residue O (ψ u) = 0 :=
    fun ψ u => Iff.rfl
  have hfA : ∀ ψ, NCov.cls ψ = NCov.cls ψ0 → IsLocalRing.residue O (ψ f) ≠ 0 := by
    intro ψ hψ
    rw [hfdef, map_prod, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun φ _ => ?_
    have := hsout φ
    rw [← hψ, hres] at this
    exact this
  have hfB : ∀ φ ∈ FB, IsLocalRing.residue O (φ f) = 0 := by
    intro φ hφ
    rw [hfdef, map_prod, map_prod]
    exact Finset.prod_eq_zero hφ ((hres φ _).1 (hsin φ (Finset.mem_filter.1 hφ).2))
  let d : (Algebra.adjoin O S →ₐ[O] O) → ℕ := fun ψ =>
    (f : End K V).maxGenEigenspaceIndex (NCov.pt ψ f)
  let g : O[X] := ∏ ψ ∈ FA, (X - C (ψ f)) ^ d ψ
  let h : O[X] := ∏ φ ∈ FB, (X - C (φ f)) ^ d φ
  have hcop : IsCoprime g h := by
    refine IsCoprime.prod_left fun ψ hψ => IsCoprime.prod_right fun φ hφ => IsCoprime.pow ?_
    refine isCoprime_X_sub_C_of_isUnit_sub ?_
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_sub, hfB φ hφ, sub_zero]
    exact hfA ψ (Finset.mem_filter.1 hψ).2
  obtain ⟨p, q, hpq⟩ := hcop
  have hkill : ∀ (G : Finset (Algebra.adjoin O S →ₐ[O] O)) (ψ) (_ : ψ ∈ G) (x : V),
      x ∈ NCov.W _ (NCov.pt ψ) → aeval (f : End K V) (∏ φ ∈ G, (X - C (φ f)) ^ d φ) x = 0 := by
    intro G ψ hψ x hx
    rw [show (∏ φ ∈ G, (X - C (φ f)) ^ d φ) =
        (∏ φ ∈ G.erase ψ, (X - C (φ f)) ^ d φ) * (X - C (ψ f)) ^ d ψ from
      (Finset.prod_erase_mul _ _ hψ).symm]
    rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C]
    rw [NCov.pow_sub_apply_eq_zero ψ f hx, map_zero]
  have hval : ((aeval f (q * h) : Algebra.adjoin O S) : End K V) = aeval (f : End K V) (q * h) := by
    have e := aeval_algHom_apply (Algebra.adjoin O S).val f (q * h)
    simpa using e.symm
  refine ⟨_, (aeval f (q * h)).2, ?_, ?_⟩
  · intro x hx
    rw [hval]
    have hle : NCov.part (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h) - 1) := by
      unfold NCov.part
      refine iSup₂_le fun ψ hψ => ?_
      intro y hy
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      by_cases hW : NCov.W _ (NCov.pt ψ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hψA : ψ ∈ FA := Finset.mem_filter.2 ⟨hF ψ hW, hψ⟩
      have e1 := congrArg (fun P => aeval (f : End K V) P y) hpq
      simp only [map_add (f := _), map_mul, LinearMap.add_apply, Module.End.mul_apply, map_one,
        Module.End.one_apply] at e1
      rw [hkill FA ψ hψA y hy, map_zero, zero_add] at e1
      simpa [map_mul, Module.End.mul_apply] using e1
    have := hle hx
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  · intro x hx
    rw [hval]
    have hle : NCov.off (Algebra.adjoin O S) (NCov.cls ψ0) ≤
        LinearMap.ker (aeval (f : End K V) (q * h)) := by
      unfold NCov.off
      refine iSup₂_le fun φ hφ => ?_
      intro y hy
      rw [LinearMap.mem_ker]
      by_cases hW : NCov.W _ (NCov.pt φ) = ⊥
      · rw [hW, Submodule.mem_bot] at hy
        rw [hy, map_zero]
      have hφB : φ ∈ FB := Finset.mem_filter.2 ⟨hF φ hW, hφ⟩
      rw [map_mul, Module.End.mul_apply, hkill FB φ hφB y hy, map_zero]
    exact hle hx

end GlobalTheory
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)), cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal → (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  first | exact @GlobalTheory.HeckeIdealValue.inv_mem | exact GlobalTheory.HeckeIdealValue.inv_mem | (intros; apply GlobalTheory.HeckeIdealValue.inv_mem <;> assumption)
end

section

open Formalism.RepresentationBoundsCohomology.LOC

theorem _root_.GlobalTheory.T.dualLat_finite_free_of_isLatticeIn : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V'] (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V), IsLatticeIn T → PerfectRight b → Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  first | exact @GlobalTheory.dualLat_finite_free | exact GlobalTheory.dualLat_finite_free | (intros; apply GlobalTheory.dualLat_finite_free <;> assumption)
end
