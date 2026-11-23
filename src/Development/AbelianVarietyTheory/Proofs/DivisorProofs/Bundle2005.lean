module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle425
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Formalism.LocalToGlobal.ProjectiveLattices.UnifDom
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem completed_eq {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L) {s : ℂ}
    (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) : Λ s = archFactor n s * L s := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hA : ∀ (z : ℂ) i, (2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2))) ≠ 0 := fun z i =>
    mul_ne_zero two_ne_zero (by rw [Ne, Complex.cpow_eq_zero_iff]; tauto)
  let g : ℂ → ℂ := fun z => Λ z * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
    (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹)
  have key : ∀ z : ℂ, (∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) → archFactor n z *
      ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(z + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2))⁻¹) = 1 := fun z hz => by
    unfold archFactor
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [mul_mul_mul_comm, mul_inv_cancel₀ (hA z i), mul_inv_cancel₀ (hz i), one_mul]
  have hg : Differentiable ℂ g := by
    refine h.1.mul (Differentiable.fun_finsetProd fun i _ => ?_)
    refine Differentiable.mul (fun z => ?_) ?_
    · refine DifferentiableAt.inv ?_ (hA z i)
      exact (((differentiableAt_id.add_const _).neg).const_cpow (Or.inl hpi)).const_mul 2
    · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hgL : g = L := entire_eq_of_halfPlane hg hL.1 1 fun z hz => by
    have hz' : ∀ i, Complex.Gamma (z + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => Complex.Gamma_ne_zero_of_re_pos (by
      have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
      simp only [Complex.add_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
      norm_num
      have := abs_nonneg (n i)
      have h2 : (0:ℝ) ≤ |(n i : ℝ)| := abs_nonneg _
      linarith)
    show Λ z * _ = L z
    rw [h.eq_mul hL hz, mul_comm (archFactor n z), mul_assoc, key z hz', mul_one]
  calc Λ s = Λ s * (archFactor n s * ∏ i, ((2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)))⁻¹ *
        (Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))⁻¹)) := by rw [key s hs, mul_one]
    _ = archFactor n s * g s := by ring
    _ = archFactor n s * L s := by rw [hgL]

end GlobalTheory.LValNe

namespace GlobalTheory.LValNe

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem nonempty_of_isCMType {φ : I → E →+* ℂ} (hφ : IsCMType φ) : Nonempty I := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  obtain ⟨i, -⟩ := hφ w.embedding
  exact ⟨i⟩

theorem exists_heckeL [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ)
    (hm : HasInf χ φ m) (hpos : ∀ i, 0 < m i) : ∃ Λ, IsHeckeL χ Λ := by
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  exact GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ m χ hφ hu hm ⟨i₀, (hpos i₀).ne'⟩

theorem gamma_int_ne_zero {k : ℤ} (hk : 0 < k) : Complex.Gamma (k : ℂ) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.intCast_re]; exact_mod_cast hk)

theorem half_abs_two_mul (a : ℤ) (ha : 0 < a) : ((|2 * a| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_of_pos (by omega)]; push_cast; ring

theorem half_abs_neg_two_mul (a : ℤ) (ha : 0 < a) : ((|-(2 * a)| : ℤ) : ℂ) / 2 = (a : ℂ) := by
  rw [abs_neg, half_abs_two_mul a ha]

theorem archFactor_ne_zero {n : I → ℤ} {s : ℂ} (hs : ∀ i, Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) ≠ 0) :
    archFactor n s ≠ 0 := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (hs i)
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto

theorem heckeL_ne_zero_int (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) [IsCMField E]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {χ : HChar E} {m : I → ℤ} (hu : IsUnitary χ) (hm : HasInf χ φ m)
    (hpos : ∀ i, 0 < m i) {L : ℂ → ℂ} (hL : IsHeckeL χ L) (s : ℤ) (hs : ∀ i, 0 < s + m i) : L s ≠ 0 := by
  rcases le_or_gt 1 s with h1 | h1
  · have e : ((s.toNat : ℕ) : ℂ) = (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [← e]
    exact hL.ne_zero_nat hu (by omega)
  obtain ⟨i₀⟩ := nonempty_of_isCMType hφ
  have hn : ∃ i, 2 * m i ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hn' : ∃ i, -(2 * m i) ≠ 0 := ⟨i₀, by have := hpos i₀; omega⟩
  have hm' : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -(2 * m i)) := GlobalTheory.Published.HeckeFEModel.hasInf_inv hm
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hmi : HasInf χ⁻¹ φ (fun i => -m i) := by
    have e : (fun i => 2 * -m i) = fun i => -(2 * m i) := funext fun i => by ring
    show Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => 2 * -m i)
    rw [e]; exact hm'
  obtain ⟨Λ, hΛ, -⟩ := hB E I φ hφ χ (fun i => 2 * m i) hu hm hn
  obtain ⟨Λ', hΛ', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -(2 * m i)) hu' hm' hn'
  obtain ⟨L', hL'⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ (fun i => -m i) χ⁻¹ hφ hu' hmi
    ⟨i₀, by have := hpos i₀; omega⟩

  have g1 : ∀ i, Complex.Gamma ((1 - (s : ℂ)) + ((|-(2 * m i)| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_neg_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (k := 1 - s + m i) (by have := hpos i; omega)
    push_cast at this; exact this
  have e1 := completed_eq hΛ' hL' g1
  have hL1 : L' (1 - (s : ℂ)) ≠ 0 := by
    have e : (((1 - s).toNat : ℕ) : ℂ) = 1 - (s : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [← e]
    exact hL'.ne_zero_nat hu' (by omega)
  have hΛ'1 : Λ' (1 - (s : ℂ)) ≠ 0 := by
    rw [e1]; exact mul_ne_zero (archFactor_ne_zero g1) hL1
  have hΛs : Λ s ≠ 0 := fun h0 =>
    hΛ'1 ((GlobalTheory.Published.HeckeFEModel.zero_iff hFE hφ hu hm hn hΛ hΛ' s).1 h0)

  have g0 : ∀ i, Complex.Gamma ((s : ℂ) + ((|2 * m i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    rw [half_abs_two_mul _ (hpos i)]
    have := gamma_int_ne_zero (hs i)
    push_cast at this; exact this
  rw [completed_eq hΛ hL g0] at hΛs
  exact right_ne_zero_of_mul hΛs

end GlobalTheory.LValNe

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

theorem squareBottomHalfRankDiff_le_halfRank (D : D7) (i j : ℕ) : e0 D i j ≤ halfRank D i j := by
  unfold e0 halfRank botBig botSmall
  omega

theorem lNe_square (hFE : GlobalTheory.Published.HeckeFunctionalEquationAbs) (hB : CompletedLBoundedInStrips) {D : D7} {T : Type}
    {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (i j : Fin D.R.m) :
    (∀ t, ∃ Λ, IsHeckeL (nuH G t i j) Λ ∧ ∀ s : ℤ, 1 - (e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0) ∧
      ∀ c, ∃ Λ, IsHeckeL (fam G μ₀ i j c) Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := by
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  have hpos : ∀ τ, 0 < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := fun τ => by
    have := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).2
    omega
  have fam_ok : ∀ χ : HChar D.host.E, IsValChar (cmPhi D) 0 (kap D sc.cGap i j 0) (condF G.pl) ∅ χ →
      ∃ Λ, IsHeckeL χ Λ ∧ ∀ s : ℕ, 1 ≤ s → Λ s ≠ 0 := fun χ h => by
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ h.1 h.2.2.1 hpos
    exact ⟨Λ, hΛ, fun s hs => hΛ.ne_zero_nat h.1 hs⟩
  refine ⟨fun t => ?_, fun c => ?_⟩
  · have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
      simp only [nuH, hL.xi_base, mul_one]
      exact mul_div_right_comm _ _ _
    obtain ⟨n, hn, hf⟩ := hL.xi_fin t
    have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
    have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
      intro k
      rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (Lc.xiH t) hn hf k, mul_one]
      exact hv.1.2.2.1 k
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.LValNe.exists_heckeL hφ hu hm hpos
    refine ⟨Λ, hΛ, fun s hs1 hs2 => GlobalTheory.LValNe.heckeL_ne_zero_int hFE hB hφ hu hm hpos hΛ s fun τ => ?_⟩
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 := squareBottomHalfRankDiff_le_halfRank D i j
    omega
  · cases c with
    | none => exact fam_ok _ hv.1
    | some c => exact fam_ok _ (hv.2 c)

theorem lNe_of_functionalEquation :
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LNe := by
  intro hFE hB hFD
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, -, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  exact fun i j => lNe_square hFE hB hφ hL G i j

end GlobalTheory.SqTop
end
end

section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem sqAct_sqAct_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g h : GL (Fin n) K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    sqAct K n lam g (sqAct K n lam h f) = sqAct K n lam (g * h) f := by
  unfold sqAct
  have hm := congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n
    ((g : Matrix (Fin n) (Fin n) K)ᵀ) ((h : Matrix (Fin n) (Fin n) K)ᵀ))
  simp only [AlgHom.comp_apply] at hm
  rw [map_smul, hm, smul_smul, ← Matrix.transpose_mul]
  congr 1
  unfold detPow
  rw [map_mul, mul_zpow, Units.val_mul]

theorem sqAct_one_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam 1 f = f := by
  unfold sqAct detPow
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, map_one, one_zpow, Units.val_one, one_smul]
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold Formalism.GradedWeylDivisibility.rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [h1]; rfl

theorem nablaSq_le_span_extremal : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n),
    nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  intro K _ _ n lam
  set M := Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) with hM
  have hanti : Antitone lam.natW := by
    intro i j hij
    have := lam.anti hij
    unfold DomWeight.natW
    omega
  have hext : extremal K n lam ∈ nablaSq K n lam :=
    Formalism.GradedWeylDivisibility.hwMem K n n le_rfl lam.natW hanti
  have hstab : ∀ g : GL (Fin n) K, ∀ f ∈ nablaSq K n lam, sqAct K n lam g f ∈ nablaSq K n lam := by
    intro g f hf
    unfold sqAct
    exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K n n lam.natW _ f hf)
  have hle : M ≤ nablaSq K n lam := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hstab g _ hext
  have hlin : ∀ g : GL (Fin n) K, ∀ (c : K) (f₁ f₂ : MvPolynomial (Fin n × Fin n) K),
      sqAct K n lam g (c • f₁ + f₂) = c • sqAct K n lam g f₁ + sqAct K n lam g f₂ := by
    intro g c f₁ f₂
    unfold sqAct
    rw [map_add (f := _), map_smul, smul_add, smul_comm]
  have hMstab : ∀ g : GL (Fin n) K, ∀ f ∈ M, sqAct K n lam g f ∈ M := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [sqAct_sqAct_nabla]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero =>
      have h0 : sqAct K n lam g 0 = 0 := by unfold sqAct; simp
      rw [h0]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have := hlin g 1 x y
      rw [one_smul, one_smul] at this
      rw [this]; exact M.add_mem hx hy
    | smul c x _ hx =>
      have hs : sqAct K n lam g (c • x) = c • sqAct K n lam g x := by
        unfold sqAct; rw [map_smul, smul_comm]
      rw [hs]; exact M.smul_mem c hx
  rcases GlobalTheory.T.dualWeylModule_simple_charZero K n lam M hle hMstab with h0 | h1
  · exfalso
    have hmem : extremal K n lam ∈ M := by
      have : sqAct K n lam 1 (extremal K n lam) ∈ M := Submodule.subset_span ⟨1, rfl⟩
      rwa [sqAct_one_nabla] at this
    rw [h0, Submodule.mem_bot] at hmem
    exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam.natW hmem
  · rw [h1]

end GlobalTheory
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.HeckeSplitGen

theorem heckeChar_eq_one_of_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 → ν x = 1) →
      ∀ x, ν x = 1 := by
  intro F E _ _ _ _ _ σ hcm ν hν hs
  obtain ⟨N, hN, hA⟩ := GlobalTheory.T.unitaryIdeleChar_trivial_congruentOneModulo F E ν hν.1
  have hH : grpHF σ N ≤ ν.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ((⟨k, rfl⟩ | ⟨e, he, hx⟩) | hx)
    · exact hν.2 k
    · exact hs e he x hx
    · exact hA x hx
  have hcl : closure (grpHF σ N : Set (AF F ⊗[F] E)ˣ) ⊆ ν.ker := by
    refine closure_minimal hH ?_
    have : (ν.ker : Set (AF F ⊗[F] E)ˣ) = ν ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage hν.1
  intro x
  obtain ⟨z, hz, hxz⟩ := GlobalTheory.T.exists_finPart_eq_one_mul_inv_mem_split_congruence_ideles F E σ hcm N hN x
  have h1 : ν (x * z⁻¹) = 1 := hH hxz
  have h2 : ν z = 1 := hcl (GlobalTheory.T.mem_closure_split_congruence_ideles_of_finPart_eq_one F E σ hcm N hN z hz)
  have : x = x * z⁻¹ * z := by group
  rw [this, map_mul, h1, h2, one_mul]

end GlobalTheory.HeckeSplitGen

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhiIndep


open ReciprocityTheory.ChartRestriction.G.FD in
theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)


open ReciprocityTheory.ChartRestriction.G.FD in
theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (hχ : ∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    apply mul_left_cancel₀ (mul_ne_zero (hν g) (bchar_ne_zero (la k) hb))
    rw [mul_zero, Finset.mul_sum, ← h]
    exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]



theorem phiJ_indep (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hd : Dom a n) (m : ℕ) (b : Fin m → T.R j)
    (hs : ∀ k, b k ∈ sec (T.Q.Xo j) T.Q.c a n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun k => T.phiJ j σ a (b k) := by
  obtain ⟨th, hr, -, hD⟩ := h.dictU j hj σ hσ
  have hI := GlobalTheory.rdIndep_of_lawsM D T.toCore h.toLawsM j hj σ hσ a n hd m b hs hb
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along (T.U j σ).X (laU (T.U j σ) a n) (T.dict j σ) hD.2.2.2.2.1 (h.chiTriv j hj σ hσ a n hd)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (T.cE j σ (T.dict j σ g).1 * T.mu j σ g)) ?_
    (fun k => rdU (T.U j σ) (b k)) (fun i k => (h.unf j hj σ hσ).2.2.2.2.1 a n hd _ (hs i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [h.cUnit j hj σ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(h.muUnit j hj σ hσ).2.1]; exact one_ne_zero)
  · intro i g
    simp only [CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

theorem phiC_indep_of (D : D7) (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {m : ℕ} (b : Fin m → T.R j)
    (H : LinearIndependent ℂ fun k => T.phiJ j σ a (b k)) :
    LinearIndependent ℂ fun k => phiC T hV a (b k) := by
  subst hV
  exact H



theorem phiC_indep : ∀ (D : D7) (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → ∀ (i : Fin D.R.m) σ, GoodEmb T.Q.c σ → ∀ (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => phiC T hV (wtA (κ i)) (b k : T.R ((i : ℕ) + 1)) := by
  intro D T κ h i σ hσ hV m b hb
  refine phiC_indep_of D T hV _ (fun k => (b k : T.R ((i : ℕ) + 1))) ?_
  exact phiJ_indep D T h _ (inR i) σ hσ _ (κ i).n (dom_wtA (κ i)) m _
    (fun k => cusp_le_sec _ _ _ _ _ (b k).2)
    (hb.map' (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n).subtype (Submodule.ker_subtype _))

end GlobalTheory.PhiIndep
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.sum_norm_sq_le_of_rootOfUnity_addChar_combination : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  first | exact @GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity | exact GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity | (intros; apply GlobalTheory.ParsevalRootsOfUnity.exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity <;> assumption)
end
