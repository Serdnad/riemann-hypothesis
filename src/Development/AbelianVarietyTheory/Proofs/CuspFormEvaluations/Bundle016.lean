module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TwoMulPowFourDvdCardGeneralLinearGroup
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsHarmonicProdOfDisjointColumns
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007

@[expose] public section

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

theorem poly_ne_zero (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by
  classical
  unfold Bk.poly
  refine pow_ne_zero _ ?_
  intro h
  let v : LtN Dw n → K := fun l => if ∃ a : Fin B.i, l = ⟨B.τ, Fin.castLE B.hi a, B.col a⟩ then 1 else 0
  have h2 := congrArg (MvPolynomial.eval v) h
  rw [RingHom.map_det, map_zero] at h2
  have : (MvPolynomial.eval v).mapMatrix (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X, v, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; rw [if_pos ⟨a, rfl⟩, if_pos rfl]
    · rw [if_neg hab, if_neg]
      rintro ⟨d, hd⟩
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at hd
      have h1 : a = d := Fin.castLE_injective _ hd.1
      have h3 : b = d := B.col_inj hd.2
      exact hab (h1.trans h3.symm)
  rw [this, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem not_isBlockProd_zero (K : Type) [Field K] : ¬ IsBlockProd (0 : MvPolynomial (LtN Dw n) K) := by
  rintro ⟨nb, bs, -, h⟩
  exact Finset.prod_ne_zero_iff.2 (fun j _ => poly_ne_zero Dw n K (bs j)) h.symm

end GlobalTheory.BlockThInhab
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem isNab_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → IsNab Xo c (fun {S} _ _ y k F α => (nab (twPt h y) k F α).val) := by
  intro E _ _ _ H Dw l Xo c ta h _ nab hn
  refine ⟨hn.1, fun S _ _ iQ y => ?_⟩
  letI : Algebra ℚ (Tw ta S) := iQ
  obtain ⟨C, h1, h2⟩ := hn.2 (Tw ta S) (twPt h y)
  exact ⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩,
    ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩

end GlobalTheory.GalTw
end
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.EtaCard

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem nonempty_equiv_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (I : Ideal O) [Finite (O ⧸ I)] (r : ℕ)
    (hr : Module.finrank O M = r) :
    Nonempty ((M ⧸ (I • ⊤ : Submodule O M)) ≃ₗ[O] (Fin r → O ⧸ I)) := by
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ B.equivFun.restrictScalars O⟩

theorem nonempty_aut_equiv (O N : Type) [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (r : ℕ)
    (e : N ≃ₗ[O] (Fin r → O ⧸ I)) : Nonempty ((N ≃ₗ[O] N) ≃ GL (Fin r) (O ⧸ I)) := by
  have hs : Function.Surjective (algebraMap O (O ⧸ I)) := Ideal.Quotient.mk_surjective
  let e1 : (N ≃ₗ[O] N) ≃ ((Fin r → O ⧸ I) ≃ₗ[O ⧸ I] (Fin r → O ⧸ I)) :=
    { toFun := fun g => (e.symm ≪≫ₗ g ≪≫ₗ e).extendScalarsOfSurjective hs
      invFun := fun g => e ≪≫ₗ g.restrictScalars O ≪≫ₗ e.symm
      left_inv := fun g => by ext x; simp
      right_inv := fun g => by ext x; simp }
  exact ⟨e1.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toEquiv.trans
    Matrix.GeneralLinearGroup.toLin.symm.toEquiv)⟩

theorem span_sup_pow (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) (S : Submodule O M)
    (h : S ⊔ Ideal.span {a} • ⊤ = ⊤) (k : ℕ) : S ⊔ Ideal.span {a ^ k} • ⊤ = ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine eq_top_iff.2 (ih.ge.trans (sup_le le_sup_left ?_))
    have h2 := congrArg (fun T : Submodule O M => Ideal.span {a ^ k} • T) h
    simp only [Submodule.smul_sup, ← Submodule.mul_smul, Ideal.span_singleton_mul_span_singleton,
      ← pow_succ] at h2
    exact h2.ge.trans (sup_le_sup_right Submodule.smul_le_right _)

variable (E : Type) [Field E] [NumberField E]

theorem finite_quot (k : ℕ) (hk : k ≠ 0) : Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hk)

theorem card_quot (k : ℕ) : Nat.card (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) = k ^ Module.finrank ℚ E := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem charP_quot (k : ℕ) : CharP (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) k := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h2 := map_dvd (Algebra.norm ℤ) h
  rw [← map_natCast (algebraMap ℤ (𝓞 E)), ← map_natCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap,
    Algebra.norm_algebraMap, Int.pow_dvd_pow_iff Module.finrank_pos.ne'] at h2
  exact_mod_cast h2

theorem finrank_eq [IsCMField E] : Module.finrank ℚ E = 2 * FD.fdeg E := by
  rw [FD.fdeg, IsTotallyComplex.finrank E]
  omega

theorem card_levGrp_and_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (R : ℕ), 1 < R → Finite (LevGrp Dw (R ^ 4)) ∧ Finite (LatMod Dw R) ∧ Nat.card (LatMod Dw R) = R ^ (2 * FD.fdeg E * (Dw.p + Dw.q)) ∧ Nat.card (LevGrp Dw (R ^ 4)) ≤ R ^ (8 * FD.fdeg E * (Dw.p + Dw.q) ^ 2) ∧ (Odd R → 2 ≤ Dw.p + Dw.q → 2 * R ^ 4 ∣ Nat.card (LevGrp Dw (R ^ 4))) ∧ (∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤) ∧ ∀ (n : ℕ) (x₀ : Fin n → Dw.La), Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤ → ∀ (y : Fin n → LatMod Dw R) (g : LevGrp Dw (R ^ 4)), Submodule.span (𝓞 E) (Set.range fun b => g (shiftFam R x₀ y b)) = ⊤ := by
  intro E _ _ _ H Dw R hR
  have := Dw.fin
  have := Dw.proj
  have hR0 : R ≠ 0 := by omega
  have := finite_quot E R hR0
  have := finite_quot E (R ^ 4) (pow_ne_zero _ hR0)
  obtain ⟨e1⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {(R : 𝓞 E)}) _ Dw.rank
  obtain ⟨e4⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {((R ^ 4 : ℕ) : 𝓞 E)}) _ Dw.rank
  obtain ⟨g4⟩ := nonempty_aut_equiv _ _ _ _ e4
  refine ⟨Finite.of_equiv _ g4.symm, Finite.of_equiv _ e1.symm.toEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e1.toEquiv, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul]
  · rw [Nat.card_congr g4]
    refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
    change Nat.card (Fin (Dw.p + Dw.q) → Fin (Dw.p + Dw.q) → _) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · intro ho h2
    rw [Nat.card_congr g4]
    exact two_mul_pow_four_dvd_card_generalLinearGroup _ R ho (charP_quot E _) hR _ h2
  · choose x₀ hx using fun i => Submodule.Quotient.mk_surjective _ (e1.symm (Pi.single i 1))
    refine ⟨x₀, ?_⟩
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, eq_top_iff]
    intro z _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (e1 z i)
    refine ⟨∑ i, c i • x₀ i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), e1.injective ?_⟩

    simp only [map_sum, map_smul, Submodule.mkQ_apply, hx, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp), ← hc]
    simp [Algebra.smul_def]
  · intro n x₀ hx y g
    have h1 : Submodule.span (𝓞 E) (Set.range fun b => x₀ b + R • qRep (y b)) ⊔
        Ideal.span {(R : 𝓞 E)} • ⊤ = ⊤ := by
      refine eq_top_iff.2 (hx.ge.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right))
      rintro _ ⟨b, rfl⟩
      have : x₀ b = (x₀ b + R • qRep (y b)) - (R : 𝓞 E) • qRep (y b) := by
        rw [Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial))
    have h2 := span_sup_pow _ _ _ _ h1 4
    rw [← Nat.cast_pow, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp] at h2
    have h3 := congrArg (Submodule.map g.toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3

end GlobalTheory.EtaCard
end

section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

namespace GlobalTheory.FrameRead

open GlobalTheory.Harm Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)}

noncomputable def IsEnum.idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : Ix :=
  ((h.2 t.1).1 t.2).choose


omit [Fintype Ix] in
theorem IsEnum.pl_idx (h : IsEnum H pl) (t : {τ : E →+* ℂ // InPsi H τ}) : pl (h.idx t) = t.1 :=
  ((h.2 t.1).1 t.2).choose_spec

theorem rename_letAct (h : IsEnum H pl) {K : Type} [Field K] (g : Ix → GL (Fin n) K)
    (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K g P) =
      colSubst (fun t => (g (h.idx t) : Matrix (Fin n) (Fin n) K)ᵀ)
        (fun t => (((g (h.idx t))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ)
        (rename (thetaLetterEquiv Dw n) P) := by
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp (letAct Dw pl K g) =
    (colSubst _ _).comp (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with hτ | ⟨τ, hτ, rfl⟩
  · have h1 : ∃ t, pl t = τ := (h.2 τ).1 hτ

    rw [dite_eq_left h1, thetaLetterEquiv_of_mem Dw hτ, colSubst_X_xVar, xForm_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw hτ]
    rfl
  · have h1 : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun h1 =>
      ((not_mem_hostType_iff H τ).2 ((h.2 _).2 h1)) hτ
    have h2 : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ :=
      ⟨h.idx ⟨τ, hτ⟩, by rw [h.pl_idx]⟩
    have h3 : h2.choose = h.idx ⟨τ, hτ⟩ := h.1 (by
      rw [h.pl_idx]
      exact (ComplexEmbedding.involutive_conjugate E).injective h2.choose_spec)

    rw [dite_eq_right h1, dite_eq_left h2, thetaLetterEquiv_conjugate Dw hτ, colSubst_X_yVar, yForm_apply,
    map_sum, h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw hτ]
    rfl

theorem letAct_mul_one_mem_HHa :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (K : Type) [Field K] [CharZero K] (a : (E →+* ℂ) × ℕ → ℕ), (∀ g g' : Ix → GL (Fin n) K, letAct Dw pl K (g * g') = (letAct Dw pl K g).comp (letAct Dw pl K g')) ∧ letAct Dw pl K (1 : Ix → GL (Fin n) K) = AlgHom.id K _ ∧ ∀ (g : Ix → GL (Fin n) K), ∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), letAct Dw pl K g P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  intro E _ _ _ H Dw n Ix _ pl h _ K _ _ a
  have hinj := rename_injective (R := K) _ (thetaLetterEquiv Dw n).injective
  refine ⟨fun g g' => AlgHom.ext fun P => hinj ?_, AlgHom.ext fun P => hinj ?_, fun g P hP => ?_⟩
  · rw [AlgHom.comp_apply, rename_letAct Dw h, rename_letAct Dw h, rename_letAct Dw h,
      ← AlgHom.comp_apply (colSubst _ _) (colSubst _ _), colSubst_comp]
    simp only [Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, transpose_mul]
  · rw [rename_letAct Dw h]
    simp only [Pi.one_apply, inv_one, Units.val_one, transpose_one, colSubst_one, AlgHom.id_apply]
  · have key := mem_HHa_iff_rename (Ψ := InPsi H) (dim := Dw.mult) (n := n) (K := K)
      (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))
    obtain ⟨h₁, h₂, h₃⟩ := (key P).1 hP
    refine (key _).2 ?_
    have e := rename_letAct Dw h g P
    unfold thetaLetterEquiv at e
    rw [e]
    exact ⟨h₁.colSubst fun t => by rw [← transpose_mul, Units.inv_mul, transpose_one],
      fun t r => colSubst_isWeightedHomogeneous _ _ _ (h₂ t r),
      fun t r r' hr s => by rw [rowAdd_colSubst _ _ t hr.isLeft_eq, h₃ t r r' hr]⟩

end GlobalTheory.FrameRead
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.invariantOperator_value_triangular_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (d : ℕ) (B : Germ.FB S d (𝓞 E)) (hg : Germ.PS S 2 d), B.IsCanonGauge S hg → ∀ (k n : ℕ) (f : Fin n → MvPowerSeries (Fin 1 × Fin d) S) (uvec uvec' : Lt1 Dw → Fin d → S) (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S), (∀ τ i j, i < j → cf τ i j = 0) → (∀ τ i e, uvec' ⟨τ, i⟩ e = ∑ j, cf τ i j * uvec ⟨τ, j⟩ e) → (∀ τ i, IsUnit (cf τ i i)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, B.nabVal S hg H.w0 k (f b) uvec' (MvPolynomial.monomial (colOf m b) 1) = (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, B.nabVal S hg H.w0 k (f b) uvec (MvPolynomial.monomial (colOf m b) 1) := by
  first | exact @GlobalTheory.nabVal_triangular | exact GlobalTheory.nabVal_triangular | (intros; apply GlobalTheory.nabVal_triangular <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.inZh_geoInj_stable_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n : ℕ) (Λ : GenLat E n) (N : ℕ), (∀ (T T' : Over Xo.X) (h : T' ⟶ T) (a : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N (fun b => h ≫ a b)) ∧ (∀ (T : Over Xo.X) (a a' : Fin n → (T ⟶ Xo.univ.t.G)), InZh Xo Λ N a → InZh Xo Λ N a' → InZh Xo Λ N (fun b => a b * a' b)) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (ψ : S →+* T) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ (J : Type) (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)), GeoInj Xo x0 z → GeoInj Xo x1 (fun i b => h ≫ z i b)) ∧ (Λ.TrivAt l.M → ∀ (T : Over Xo.X) (u : Fin n → (T ⟶ Xo.univ.t.G)), (∀ b, u b ^ N = 1 ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (u b)) → InZh Xo Λ N u) := by
  first | exact @GlobalTheory.inZh_geoInj_stable | exact GlobalTheory.inZh_geoInj_stable | (intros; apply GlobalTheory.inZh_geoInj_stable <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.modN_sq_sum_iff_exists_genLat_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) ↔ ∃ (m : ℕ) (x : Fin m → Dw.La) (v : Fin m → Fin n → 𝓞 E), (∀ i, ∃ w ∈ Λ.La, ∀ b, (v i b : E) = (N : E) * w b) ∧ ∀ b, a b = ∑ i, v i b • x i := by
  first | exact @GlobalTheory.modN_sq_iff_exists_genLat_sum | exact GlobalTheory.modN_sq_iff_exists_genLat_sum | (intros; apply GlobalTheory.modN_sq_iff_exists_genLat_sum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sq_dvd_sum_EF_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a a' : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a' j)) → ((N : ℤ) ^ 2) ∣ ∑ b, Dw.EF (a b) (a' b) := by
  intro E _ _ _ H Dw n Λ N hU hN hle a a' ha ha'
  obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a).1 ha
  obtain ⟨m', x', v', hv', hav'⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a').1 ha'
  have key : ∑ b, Dw.EF (a b) (a' b)
      = ∑ i, ∑ j, Dw.EF (x i) ((∑ b, H.bar (v i b) * v' j b) • x' j) := by

    simp only [hav, hav', Finset.sum_smul, map_sum, LinearMap.sum_apply, Dw.adj, mul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    exact Finset.sum_comm
  rw [key]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  obtain ⟨w, hw, hvw⟩ := hv i
  obtain ⟨w', hw', hvw'⟩ := hv' j
  obtain ⟨c, hc⟩ := (hU w).1 hw w' hw'
  have hs : (∑ b, H.bar (v i b) * v' j b) = ((N : ℤ) ^ 2) • c := by
    apply IsFractionRing.injective (𝓞 E) E

    rw [map_sum, map_zsmul, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      hvw, hvw', map_mul, map_natCast, zsmul_eq_mul]
    push_cast
    ring
  rw [hs, smul_assoc, map_zsmul, smul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem betaExists_of_ne_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (c : Coeff l) (n bad : ℕ), bad ≠ 1 → BetaExists (Dw := Dw) c n bad :=
  fun E _ _ _ H Dw l c n bad _ => BetaEx.betaExists E H Dw l c n bad

end GlobalTheory
end
