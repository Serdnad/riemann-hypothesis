module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle301
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle300
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle140
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle172
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)

  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  apply _root_.GlobalTheory.ConjNorm.Inter.lam_mul_mem <;> assumption

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  apply _root_.GlobalTheory.ConjNorm.Inter.klat_gen <;> assumption

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  apply _root_.GlobalTheory.ConjNorm.Inter.klat_rat <;> assumption

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  apply _root_.GlobalTheory.ConjNorm.Inter.klat_mul_mem <;> assumption

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ThetaInter


open GlobalTheory.ThetaInter in
theorem GlobalTheory.theta_translation_intertwiner_unitary : ∀ D : D7, IntertwinerUnitary D := by
  apply _root_.GlobalTheory.ConjNorm.unitary_all <;> assumption
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  first | exact @GlobalTheory.FNRecip.main | exact GlobalTheory.FNRecip.main | (intros; apply GlobalTheory.FNRecip.main <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Nonempty (Frac Ω ε) := by
  first | exact @GlobalTheory.FN.frac_nonempty | exact GlobalTheory.FN.frac_nonempty | (intros; apply GlobalTheory.FN.frac_nonempty <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

noncomputable section

namespace GlobalTheory.PsType

theorem subquotient_prinSeries_of_hasVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → HasVec ψ π → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ Agree ψ ω ∧ IsSubquotient π (prinSeries ω) := by
  intro hBZ k _ _ _ _ n ψ V _ _ π hπ hirr hψ hord hvec
  obtain ⟨v, hv0, hv⟩ := hvec
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  have hx0 : (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) ≠ 0 := by
    intro h
    exact hv0 (GlobalTheory.T.eq_zero_of_mem_twistedJacquetKernel_upperUnitriangular k n ψ V π hπ hψ hord v ((Submodule.Quotient.mk_eq_zero _).1 h) hv)
  have hact : ∀ t ∈ torusO k (Fin n), jacB π t (Submodule.Quotient.mk v) =
      (_root_.GlobalTheory.SmGL.torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet π (unipB k (Fin n))) := by
    intro t ht
    have hgrp : diagT k (Fin n) t ∈ grp ψ := by
      refine ⟨iwahori_le_KO k _ (diagT_mem_iwahori ht), fun i j hij => ?_⟩
      rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne]
      exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
    have hth : theta ψ (diagT k (Fin n) t) = (_root_.GlobalTheory.SmGL.torusChar ψ t : ℂ) := by
      rw [GlobalTheory.T.principalSeriesTypeCharacter_triangular k n ψ (diagT k (Fin n) t) t ht (fun i => by rw [val_diagT, Matrix.diagonal_apply_eq])
        (Or.inr fun i j hij => by rw [val_diagT, Matrix.diagonal_apply_ne _ hij.ne'])]
      simp
    rw [UnramFixed.jacB_apply, jacBU_mk, hv _ hgrp, hth]
    have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
      UnramFixed.deltaHalf_torusO k ht
    rw [this]
    simp
  obtain ⟨ω, l, hl0, hω, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π) (Submodule.Quotient.mk v) ψ
    (isSmooth_jacB hπ) hl hψ hx0 hact
  exact ⟨ω, fun i => GlobalTheory.TameIwahori.isSmoothChar_of_eq_on_units (hψ i) (hu i),
    fun i u hu' => (hu i u hu').symm,
    SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hω⟩

end GlobalTheory.PsType
end
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.FracPrim

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Bd (X : Tower Ω ε) (x : X.K) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp x).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * (X.exp x).coeff r)

theorem bd_one (X : Tower Ω ε) : Bd X 1 := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  rw [map_one, HahnSeries.coeff_one]
  split_ifs
  · exact ⟨one_mem _, by simpa using isIntegral_one⟩
  · exact ⟨zero_mem _, by simpa using isIntegral_zero⟩

theorem bd_mul (X : Tower Ω ε) {x y : X.K} (hx : Bd X x) (hy : Bd X y) : Bd X (x * y) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hx
  obtain ⟨S', D', hD', h'⟩ := hy
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ?_⟩
  have hS : IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left)
  have hS' : IntermediateField.adjoin ℚ (S' : Set Ω) ≤ IntermediateField.adjoin ℚ ((S ∪ S' : Finset Ω) : Set Ω) :=
    IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right)
  rw [map_mul, HahnSeries.coeff_mul]
  refine ⟨sum_mem (fun ij _ => mul_mem (hS (h ij.1).1) (hS' (h' ij.2).1)), ?_⟩
  rw [Finset.mul_sum]
  refine IsIntegral.sum _ (fun ij _ => ?_)
  have := (h ij.1).2.mul (h' ij.2).2
  convert this using 1
  push_cast; ring

theorem bd_prod (X : Tower Ω ε) {ι : Type} (s : Finset ι) (t : ι → X.K) (h : ∀ i ∈ s, Bd X (t i)) :
    Bd X (∏ i ∈ s, t i) :=
  Finset.prod_induction t (Bd X) (fun _ _ => bd_mul X) (bd_one X) h

end GlobalTheory.FracPrim

namespace GlobalTheory

open GlobalTheory.FracPrim

theorem exists_prim_frac_level_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ f : X.K, f ≠ 0 → ∃ (a b : X.K) (κ : Ω) (S : Finset Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) b = b) ∧ ∀ r, (X.exp a).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧ (X.exp b).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) := by
  intro Ω _ _ _ ε X hj l _ A hl f hf
  classical
  obtain ⟨M, hM, hfM⟩ := X.level f
  have hc1 : 1 < 6 * M + 1 := by omega
  have hc6 : Nat.Coprime (6 * M + 1) 6 := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
    simp [Nat.add_mod]
  have hcM : 6 * M + 1 ≡ 1 [MOD M] :=
    ((Nat.modEq_iff_dvd' (by omega)).mpr (by simp)).symm
  have hfG := GlobalTheory.T.principalCongruenceFunction_mem_adjoin_j_siegelUnits ε X hj M (6 * M + 1) hM hc1 hc6 hcM f hfM
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := IntermediateField.mem_adjoin_iff_div.mp hfG
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hPQ)
  have hfQ : f * Q = P := by rw [hPQ, div_mul_cancel₀ _ hQ0]
  obtain ⟨M', hM', hQM'⟩ := X.level Q
  haveI : NeZero M' := ⟨hM'.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M').Normal := CongruenceSubgroup.Gamma_normal M'
  haveI : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M') := Fintype.ofFinite _
  have tq : ∀ g g' : SL(2, ℤ), g⁻¹ * g' ∈ CongruenceSubgroup.Gamma M' → X.sl (ofSL g') Q = X.sl (ofSL g) Q := by
    intro g g' h
    have hc : g * (g⁻¹ * g') * g⁻¹ ∈ CongruenceSubgroup.Gamma M' :=
      (CongruenceSubgroup.Gamma_normal M').conj_mem _ h g
    have e : g' = (g * (g⁻¹ * g') * g⁻¹) * g := by group
    rw [e, map_mul, X.sl_mul, hQM' _ hc]
  set t : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M' → X.K := fun q => X.sl (ofSL q.out) Q with ht
  set b0 : X.K := ∏ q, t q with hb0def
  have hb0 : ∀ δ : SL(2, ℤ), X.sl (ofSL δ) b0 = b0 := by
    intro δ
    rw [hb0def, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (δ : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M')) _ _ (fun q => ?_)
    simp only [ht, Equiv.coe_mulRight]
    rw [← X.sl_mul, ← map_mul]
    symm
    apply tq
    rw [← QuotientGroup.eq]
    simp
  have ht1 : t 1 = Q := by
    simp only [ht]
    rw [tq 1 _ (by rw [← QuotientGroup.eq]; simp), map_one, X.sl_one]
  have hbd : ∀ γ : SL(2, ℤ), Bd X (X.sl (ofSL γ) Q) := fun γ =>
    GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM Q hQ γ
  have hPbd : Bd X P := by
    have := GlobalTheory.T.siegelUnit_jPolynomial_bounded_denominators ε X M (6 * M + 1) hM hc1 hc6 hcM P hP 1
    rwa [map_one, X.sl_one] at this
  set R : X.K := ∏ q ∈ Finset.univ.erase 1, t q with hR
  have hbR : b0 = R * Q := by
    rw [hb0def, hR, ← ht1, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have ha0 : f * b0 = P * R := by rw [hbR, ← hfQ]; ring
  have hb0bd : Bd X b0 := bd_prod X _ _ (fun q _ => hbd _)
  have ha0bd : Bd X (f * b0) := by
    rw [ha0]; exact bd_mul X hPbd (bd_prod X _ _ (fun q _ => hbd _))
  have hb0ne : b0 ≠ 0 := by
    rw [hb0def]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => (map_ne_zero _).mpr hQ0)
  have ha0ne : f * b0 ≠ 0 := mul_ne_zero hf hb0ne
  obtain ⟨κa, hκa, hPa, Sa, hSa⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl (f * b0) ha0ne ha0bd
  obtain ⟨κb, hκb, hPb, Sb, hSb⟩ := GlobalTheory.T.primitive_const_mul_of_bounded_expansion ε X hj l A hl b0 hb0ne hb0bd
  refine ⟨algebraMap Ω X.K κa * (f * b0), algebraMap Ω X.K κb * b0, κb / κa, Sa ∪ Sb, div_ne_zero hκb hκa, ?_, hPa, hPb,
    ?_, fun r => ⟨?_, ?_⟩⟩
  · have e : algebraMap Ω X.K (κb / κa) * algebraMap Ω X.K κa = algebraMap Ω X.K κb := by
      rw [← map_mul, div_mul_cancel₀ _ hκa]
    rw [← mul_assoc (algebraMap Ω X.K (κb / κa)), e]; ring
  · intro γ
    rw [map_mul, AlgEquiv.commutes, hb0]
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_left) (hSa r)
  · exact IntermediateField.adjoin.mono _ _ _ (by rw [Finset.coe_union]; exact Set.subset_union_right) (hSb r)

end GlobalTheory
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumFam

theorem gamma_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem common_level {k : ℕ} (Q : Fin k → ℕ → Prop) (hmono : ∀ i M M', M ∣ M' → Q i M → Q i M')
    (h : ∀ i, ∃ M, 0 < M ∧ Q i M) : ∃ M, 0 < M ∧ ∀ i, Q i M := by
  choose M hM hQ using h
  exact ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i,
    fun i => hmono i _ _ (Finset.dvd_prod_of_mem M (Finset.mem_univ i)) (hQ i)⟩

theorem near_fin {V : Type} {k : ℕ} (φ ψ : Fin k → SL(2, ℤ) → V) (h : ∀ i, Near (φ i) (ψ i)) :
    ∃ M, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ i, φ i δ = ψ i δ := by
  obtain ⟨M, hM, hQ⟩ := common_level (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, φ i δ = ψ i δ)
    (fun _ _ _ hd hq δ hδ => hq δ (gamma_dvd hd hδ)) h
  exact ⟨M, hM, fun δ hδ i => hQ i δ hδ⟩

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ k ∈ s, Kum X l n (x k) (χ k)) : Kum X l n (∑ k ∈ s, x k) (∑ k ∈ s, χ k) := by
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem map_mon {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map f (mon R w i) = mon S w i := by
  simp [mon]

end GlobalTheory.KZ.H3.KumFam


open GlobalTheory.KZ.H3.KumFam in
theorem GlobalTheory.KZ.H3.kum_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  intro Ω _ _ ε X l _ _ hj N w c hA hinv
  choose χ hχ using fun n i => GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule Ω ε X l hj n (c i) (hA i)
  refine ⟨fun n δ => ∑ i, MvPolynomial.C (χ n i δ) * mon (ZMod (l ^ n)) w i, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n δ
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
    have h := (MvPolynomial.isHomogeneous_C (Fin 2) (χ n i δ)).mul ((mon_expand (ZMod (l ^ n)) w).2.2.1 i)
    rwa [zero_add] at h
  · intro n
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.common_level (k := w + 1)
      (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
        χ n i (δ * δ') = χ n i δ + χ n i δ')
      (fun _ _ _ hd hq δ hδ δ' hδ' => hq δ (GlobalTheory.KZ.H3.KumFam.gamma_dvd hd hδ) δ' (GlobalTheory.KZ.H3.KumFam.gamma_dvd hd hδ'))
      (fun i => GlobalTheory.T.kummerCharacter_additive_on_congruence Ω ε X l n (c i) (χ n i) (hχ n i))
    refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQ i δ hδ δ' hδ', map_add (f := _), add_mul]
  · intro n γ hγ
    have hdet : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.det_coe]; exact one_pos
    have hK : ∀ i, Kum X l n (c i)
        (fun δ => ∑ k, ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ) : ZMod (l ^ n)) * χ n k (γ * δ * γ⁻¹)) := by
      intro i
      have hk : ∀ k, Kum X l n ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) •
          X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
          (fun δ => PadicInt.toZModPow n (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) *
            χ n k (cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ)) := by
        intro k
        have h1 := GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n γ (c k) (χ n k) hdet (hχ n k)
        rw [Betti.toGQ_sl] at h1
        exact GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ h1
      have hs := GlobalTheory.KZ.H3.KumFam.kum_sum X l n Finset.univ _ _ (fun k _ => hk k)
      rw [← hinv γ hγ i] at hs
      refine (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.2 _ _ _ hs ⟨1, one_pos, fun δ _ => ?_⟩
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [GlobalTheory.T.integralConjugateSL2Int_laws.2.1, map_intCast]
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.near_fin (k := w + 1) _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _ (hK i) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩

    simp only [map_sum, map_mul, MvPolynomial.algHom_C, (mon_expand (ZMod (l ^ n)) w).1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [← hQ δ hδ i, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.algebraMap_eq]; ring
  · intro n
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.near_fin (k := w + 1) _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _
      (GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce Ω ε X l n (c i) (χ (n + 1) i) (hχ (n + 1) i)) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩

    simp only [map_sum, map_mul, MvPolynomial.map_C, GlobalTheory.KZ.H3.KumFam.map_mon]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hQ δ hδ i]
  · intro n i
    convert hχ n i using 1
    funext δ
    exact MonExp.coeff_sum_mon _ w (fun j => χ n j δ) i
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice : ∀ D : D7, galCurve D := by
  first | exact @GlobalTheory.ConjCurve.galCurve_holds | exact GlobalTheory.ConjCurve.galCurve_holds | (intros; apply GlobalTheory.ConjCurve.galCurve_holds <;> assumption)
end
