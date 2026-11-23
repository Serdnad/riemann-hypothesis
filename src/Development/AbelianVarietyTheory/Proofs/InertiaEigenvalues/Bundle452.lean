module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle437
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LocalisationCoefficientExtensionIsWildInertiaCyc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle439
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle441
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem exists_cols_isUnit {F : Type} [CommRing F] (hF : IsField F) {b n : Type} [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (X : Matrix b n F) (Z : Matrix n b F) (h : X * Z = 1) :
    ∃ e : b → n, IsUnit (X.submatrix id e) := by
  letI : Field F := hF.toField
  have h1 : X.rank = Fintype.card b := by
    apply le_antisymm (Matrix.rank_le_card_height X)
    have := Matrix.rank_mul_le_left X Z
    rw [h, Matrix.rank_one] at this
    exact this
  have h2 : Module.finrank F (Submodule.span F (Set.range X.col)) = Fintype.card b := by
    exact (Matrix.finrank_span_range_col X).trans h1
  obtain ⟨κ, e, he, hspan, hli⟩ := exists_linearIndependent' F X.col
  haveI : Finite κ := Finite.of_injective e he
  letI : Fintype κ := Fintype.ofFinite κ
  have h3 : Fintype.card κ = Fintype.card b := by
    rw [← finrank_span_eq_card hli, hspan, h2]
  let τ : b ≃ κ := Fintype.equivOfCardEq h3.symm
  refine ⟨e ∘ τ, ?_⟩
  have h4 : LinearIndependent F (X.submatrix id (e ∘ τ)).col := hli.comp τ τ.injective
  exact Matrix.linearIndependent_cols_iff_isUnit.mp h4

end GlobalTheory.PMon.SubquotientAlgEquiv

end

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem map_mul_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p q s : Type}
    [Fintype q] (M : Matrix p q R) (N : Matrix q s R) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : R →+* R))

theorem map_one_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p : Type}
    [DecidableEq p] : (1 : Matrix p p R).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

end GlobalTheory.PMon.SubquotientAlgEquiv

namespace GlobalTheory.PMon

open scoped Matrix


open SubquotientAlgEquiv in
theorem subQuot : SubQuot := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c _ hblk hdr
  have hF := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1
  have e11 : ∀ m g (i j : a), matD P ρ m g (Sum.inl i) (Sum.inl j) = matD P ρ₁ m g i j := by
    intro m g i j; simp [matD, hblk g]
  have e21 : ∀ m g (i : b) (j : a), matD P ρ m g (Sum.inr i) (Sum.inl j) = 0 := by
    intro m g i j; simp [matD, hblk g]
  have e22 : ∀ m g (i j : b), matD P ρ m g (Sum.inr i) (Sum.inr j) = matD P ρ₂ m g i j := by
    intro m g i j; simp [matD, hblk g]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    have hQiQ : ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.inv_mul Q
    have hinv : ∀ g : ↥(GK K), ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) =
        ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g := by
      intro g
      have hs : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
        rw [← map_mul_algEquiv, hQQi, map_one_algEquiv]
      calc ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))
          = (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQiQ, Matrix.one_mul]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
              (matD P ρ m g * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQ g]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g *
              ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hs, Matrix.mul_one]
    let Y : Matrix (a ⊕ b) a P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inl
    let W : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
    have hWY : W * Y = 1 := by
      rw [show W * Y = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inl Sum.inl from
        (Matrix.submatrix_mul _ _ Sum.inl id Sum.inl Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inl_injective
    have hYW : Yᵀ * Wᵀ = 1 := by rw [← Matrix.transpose_mul, hWY, Matrix.transpose_one]
    obtain ⟨e, he⟩ := exists_cols_isUnit hF Yᵀ Wᵀ hYW
    have hY' : IsUnit (Y.submatrix e id) := by
      have := (Matrix.isUnit_transpose _).2 he
      simpa [Matrix.transpose_submatrix] using this
    have hσY : ∀ g : ↥(GK K), (Y.submatrix e id).map (P.actQdR (g : GQ l)) = Y.submatrix e id * matD P ρ₁ m g := by
      intro g; ext i j
      have := congrFun (congrFun (hinv g) (e i)) (Sum.inl j)
      simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e11, e21, mul_zero,
        Finset.sum_const_zero, add_zero] at this
      simpa [Y, Matrix.mul_apply] using this
    refine ⟨hY'.unit⁻¹, fun g => ?_⟩
    have hu : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) = Y.submatrix e id := hY'.unit_spec
    have hs : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
        ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
      rw [← map_mul_algEquiv, Units.mul_inv, map_one_algEquiv]
    calc matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l))
        = (((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) * ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR)) *
            matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [Units.inv_mul, Matrix.one_mul]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            (((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) * matD P ρ₁ m g) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          simp only [Matrix.mul_assoc]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [hu, hσY g]
      _ = _ := by rw [Matrix.mul_assoc, hs, Matrix.mul_one]
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    let X : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
    let Z : Matrix (a ⊕ b) b P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr
    have hXZ : X * Z = 1 := by
      rw [show X * Z = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inr Sum.inr from
        (Matrix.submatrix_mul _ _ Sum.inr id Sum.inr Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inr_injective
    obtain ⟨e, he⟩ := exists_cols_isUnit hF X Z hXZ
    refine ⟨he.unit, fun g => ?_⟩
    rw [he.unit_spec]
    ext i j
    have := congrFun (congrFun (hQ g) (Sum.inr i)) (e j)
    simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e21, e22, zero_mul,
      Finset.sum_const_zero, zero_add] at this
    simpa [X, Matrix.mul_apply] using this

end GlobalTheory.PMon

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s := by
  first | exact @GlobalTheory.ResRecip.reciprocity | exact GlobalTheory.ResRecip.reciprocity | (intros; apply GlobalTheory.ResRecip.reciprocity <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LiveDescent

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem isLocalHom_of_nonunit {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) {a : A} (ha : a ≠ 0) (hf : f a ∈ IsLocalRing.maximalIdeal B) : IsLocalHom f := by
  have hne : (IsLocalRing.maximalIdeal B).comap f ≠ ⊥ := fun h => ha (by
    have : a ∈ (IsLocalRing.maximalIdeal B).comap f := hf
    rwa [h, Ideal.mem_bot] at this)
  have hm : ((IsLocalRing.maximalIdeal B).comap f).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have : x ∈ (IsLocalRing.maximalIdeal B).comap f := by rw [he]; exact h
  exact this hx

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A →+* B)
    [IsLocalHom f] : Continuous f := by
  have hm : Ideal.map f (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit f x hx
  refine continuous_of_continuousAt_zero f.toAddMonoidHom ?_
  intro s hs
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
  refine Filter.mem_map.2 (Filter.mem_of_superset (((isAdic_iff.1 hA).1 n).mem_nhds (Ideal.zero_mem _))
    fun x hx => hn ?_)
  have h1 : f x ∈ Ideal.map f (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

theorem span_eq_top_of_map {ι k K : Type} [Field k] [Field K] (f : k →+* K) {r : ℕ}
    (M : ι → Matrix (Fin r) (Fin r) k) (h : Submodule.span K (Set.range fun g => (M g).map f) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hexp : ∀ Y : Matrix (Fin r) (Fin r) k, l Y = ∑ p, ∑ q, Y p q * l (Matrix.single p q 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have key : ∀ Y : Matrix (Fin r) (Fin r) K, ∑ p, ∑ q, Y p q * f (l (Matrix.single p q 1)) = 0 := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range fun g => (M g).map f) := h ▸ Submodule.mem_top
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨g, rfl⟩ := hY
      have h0 : l (M g) = 0 := hl (Submodule.subset_span ⟨g, rfl⟩)
      have := congrArg f ((hexp (M g)).symm.trans h0)

      simpa [map_sum] using this
    | zero => simp
    | add Y Z _ _ hY hZ => simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, hY, hZ, add_zero]
    | smul a Y _ hY => simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hY, mul_zero]
  apply hl0
  refine LinearMap.ext fun Y => ?_
  rw [hexp, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  have h1 := key (Matrix.single p q 1)
  rw [Finset.sum_eq_single p (fun a _ ha => by simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]) (by simp),
    Finset.sum_eq_single q (fun a _ ha => by simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm ha)]) (by simp)] at h1
  simp only [Matrix.single_apply_same, one_mul, map_eq_zero] at h1
  rw [h1, mul_zero]

theorem trace_of_isDecomp {Γ A : Type} [Group Γ] [CommRing A] [IsDomain A] [IsLocalRing A] {n r t : ℕ}
    (σ : Γ →* GL (Fin n) A) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (h : ∃ e, IsDecomp (t := t) σ ρ χ e)
    (g : Γ) : (mat σ g).trace = (mat ρ g).trace + ∑ c : Fin t, ((χ ((c : ℕ) + 1) g : Aˣ) : A) := by
  obtain ⟨e, he⟩ := h
  apply IsFractionRing.injective A (FractionRing A)
  let d : Fin t → FractionRing A := fun c => toFr A ((χ ((c : ℕ) + 1) g : Aˣ) : A)
  have h1 : Matrix.toLin' ((mat σ g).map (toFr A)) =
      e.symm.conj ((Matrix.toLin' ((mat ρ g).map (toFr A))).prodMap (Matrix.toLin' (Matrix.diagonal d))) := by
    apply LinearMap.ext
    intro u
    apply e.injective
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    refine (he g u).trans ?_
    ext c
    · rfl
    · simp [Matrix.mulVec_diagonal, d]
  have h2 := congrArg (LinearMap.trace _ _) h1
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq,
    Matrix.trace_toLin'_eq, Matrix.trace_diagonal] at h2

  rw [map_add (f := _), map_sum, AddMonoidHom.map_trace, AddMonoidHom.map_trace]
  exact h2

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem charZero_O (N : NData R H what₂) (A : NAut N) (i : N.Loc) : CharZero (N.O i) :=
  (iotaO N A i).charZero

theorem l_mem_maximalIdeal (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    ((N.l i : ℕ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i) := by
  have hinj : Function.Injective (algebraMap ℤ_[N.l i] (N.O i)) := by
    intro x y h
    have hx := A.iotaQ_alg i x
    rw [h, A.iotaQ_alg i y] at hx
    exact (Subtype.ext ((algebraMap ℚ_[N.l i] (Qbar (N.l i))).injective hx)).symm
  have : FaithfulSMul ℤ_[N.l i] (N.O i) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := PadicInt.p_nonunit
  have := map_nonunit (algebraMap ℤ_[N.l i] (N.O i)) _ h
  rwa [map_natCast] at this

variable {N₀ N₁ : NData R H what₂} {A₀ : NAut N₀} {A₁ : NAut N₁} {i₀ : N₀.Loc} {i₁ : N₁.Loc}

theorem isLocalHom_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : IsLocalHom a.φ := by
  have := charZero_O N₀ A₀ i₀
  have hl : (N₁.l i₁).Prime := Fact.out
  refine isLocalHom_of_nonunit a.φ (a := ((N₁.l i₁ : ℕ) : N₀.O i₀)) (Nat.cast_ne_zero.2 hl.ne_zero) ?_
  rw [map_natCast]
  exact l_mem_maximalIdeal N₁ A₁ i₁

theorem continuous_φ (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) : Continuous a.φ :=
  haveI := isLocalHom_φ a
  continuous_of_isLocalHom (N₀.O_adic i₀) (N₁.O_adic i₁) a.φ

theorem trace_eq (hC : GlobalTheory.TwSys.Cheb) (a : LocExt N₀ N₁ A₀ A₁ i₀ i₁) (x : N₁.X i₁)
    (r₀ : GE N₀ →* GL (Fin R.nV) (N₀.O i₀)) (r₁ : GE N₁ →* GL (Fin R.nV) (N₁.O i₁))
    (h₀ : IsHeckeGalois N₀ i₀ (a.e x) r₀) (h₁ : IsHeckeGalois N₁ i₁ x r₁) (g : GE N₁) :
    a.φ (mat r₀ (a.γ g)).trace = (mat r₁ g).trace := by
  haveI := (N₁.O_complete i₁).toIsHausdorff
  haveI : T2Space (N₁.O i₁) := (N₁.O_adic i₁).isHausdorff_iff.1 inferInstance
  refine congrFun (GlobalTheory.BlockComplement.AE.eq_of_continuous (N := N₁) hC
    (f := fun g => a.φ (mat r₀ (a.γ g)).trace) (f' := fun g => (mat r₁ g).trace)
    ((continuous_φ a).comp (h₀.1.matrix_trace.comp a.γ_cont)) h₁.1.matrix_trace ?_) g
  filter_upwards [GlobalTheory.BlockComplement.eventually_out i₁] with w h hw B σ hB hσ
  obtain ⟨B₀, hB₀, hσ₀⟩ := (a.frob w σ).1 ⟨B, hB, hσ⟩
  have e₀ := h₀.2.2 w ((a.out w).1 (h hw)) B₀ _ hB₀ hσ₀
  have e₁ := h₁.2.2 w (h hw) B σ hB hσ
  rw [GlobalTheory.CoefDuty.Model.heckePol_map a x w (h hw), ← e₀, ← Matrix.charpoly_map] at e₁
  rw [AddMonoidHom.map_trace, Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, e₁]

end Record

theorem live_of_locExt : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N₀ N₁ : NData R H what₂) (A₀ : NAut N₀) (A₁ : NAut N₁) (i₀ : N₀.Loc) (i₁ : N₁.Loc), LocExt N₀ N₁ A₀ A₁ i₀ i₁ → (∃ r, GoodR N₀ i₀ r) → ZDecomp N₀ i₀ → Live N₁ i₁ → Live N₀ i₀ := by
  rintro hC R H what₂ N₀ N₁ A₀ A₁ i₀ i₁ a ⟨r₀, hr₀⟩ hZ ⟨π, hπ, r, ρ, hr, hd, habs⟩
  have hπ₀ := (a.Z π).1 hπ
  obtain ⟨ρ₀, hd₀⟩ := hZ _ hπ₀ _ (hr₀ _)
  refine ⟨_, hπ₀, _, ρ₀, hr₀ _, hd₀, ?_⟩
  have htr : ∀ g, a.φ (mat ρ₀ (a.γ g)).trace = (mat ρ g).trace := by
    intro g
    have h := trace_eq hC a π _ r (hr₀ _) hr g

    rw [trace_of_isDecomp _ _ _ hd₀, trace_of_isDecomp _ _ _ hd, map_add (f := _), map_sum,
    Finset.sum_congr rfl fun (c : Fin R.t) _ => a.chi ((c : ℕ) + 1) (by omega) c.2 g] at h
    exact add_right_cancel h
  haveI := isLocalHom_φ a
  have hpos := pos_of_absIrrSub _ habs
  haveI : Nonempty (Fin R.r) := ⟨⟨0, hpos⟩⟩
  refine absIrrSub_of_span_eq_top hpos _ (span_eq_top_of_map (IsLocalRing.ResidueField.map a.φ) _ ?_)
  have h := span_eq_top_of_trace_eq
    ((mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀)).comp a.γ.toMonoidHom)
    (mapRep (IsLocalRing.residue (N₁.O i₁)) ρ) (fun g => ?_) (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
  · rw [eq_top_iff, ← h]
    refine Submodule.span_mono ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨a.γ g, (mat_mapRep _ _ _).symm⟩
  · change (mat (mapRep (IsLocalRing.ResidueField.map a.φ) (mapRep (IsLocalRing.residue (N₀.O i₀)) ρ₀))
      (a.γ g)).trace = _
    rw [mat_mapRep, mat_mapRep, mat_mapRep, ← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace,
      ← AddMonoidHom.map_trace, ← htr, IsLocalRing.ResidueField.map_residue]

end GlobalTheory.LiveDescent

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.designConditionAll_of_cheb_of_takenAll : GlobalTheory.TwSys.Cheb → ∀ D : D7, TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D := by
  first | exact @GlobalTheory.DesignFromSize.main | exact GlobalTheory.DesignFromSize.main | (intros; apply GlobalTheory.DesignFromSize.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  first | exact @GlobalTheory.OrthogonalDesignFromSize.main | exact GlobalTheory.OrthogonalDesignFromSize.main | (intros; apply GlobalTheory.OrthogonalDesignFromSize.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.torsionExponent_le_of_jumps_at_embeddings_unramified : ∀ (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hs : Good K 1 LL) (h r n : ℕ) (T : LocLat (LocalSituation.sit LT HW l (AI l) K 1 LL hs).G (LocalSituation.sit LT HW l (AI l) K 1 LL hs).Qp (LocalSituation.sit LT HW l (AI l) K 1 LL hs).LL (LocalSituation.sit LT HW l (AI l) K 1 LL hs).O), K.1 ≤ MaximalUnramifiedExtension l → finrank ℚ_[l] ↥K.1 ≤ n → 1 ≤ r → (∀ τ, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧ ∀ a, IsJumpV (LocalSituation.sit LT HW l (AI l) K 1 LL hs).PD T.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset (LocalSituation.sit LT HW l (AI l) K 1 LL hs) T, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ GlobalTheory.HubX.invariantsCountConstant LT HW AI l K 1 LL hs h h T ≤ 5 + Nat.log l (2 * h) + n * r * (4 + 2 * Nat.log l (2 * h)) := by
  first | exact @GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings | exact GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings | (intros; apply GlobalTheory.HubX.cH0all_le_of_jumps_at_embeddings <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.lenUnit_invariants_twistedLattice_le_of_killingExponent : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
    (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) (c : ℕ),
    let S := LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs;
    ∀ T : LocLat S.G S.Qp S.LL S.O, T = GlobalTheory.HubX.wLat D i ρ π u hu hc →
    (∀ x : T.V ⧸ T.L.T, (∀ g, actD T.L g x = x) → ((LocalSituation.ell S : S.O) ^ c) • x = 0) →
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * c := by
  first | exact @GlobalTheory.LengthH0Bound.main | exact GlobalTheory.LengthH0Bound.main | (intros; apply GlobalTheory.LengthH0Bound.main <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem hasSupport_of_isSubquotient_prinSeries :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  intro k _ _ _ _ _ n χ hχ π h

  have hd : ∑ a : Fin n, (IrrGL.ofChar (χ a) (hχ a)).1 = n := by
    simp [IrrGL.ofChar]
  refine hasSupport_of_isSubquotient π.irr (fun a => IrrGL.isCusp_ofChar (χ a) (hχ a)) (hd := hd) ?_
  refine h.trans ((GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ).trans ?_)

  have he : stdBlocks (fun a => (IrrGL.ofChar (χ a) (hχ a)).1) hd =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
    ext ⟨a, i⟩
    rw [stdBlocks_val]
    simp [IrrGL.ofChar, Fin.fin_one_eq_zero i]
    rfl
  unfold prodIrr
  rw [he]

  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin n) (fun _ => Fin 1))
    (fun a => equivRep (IrrRep.det (Fin 1) (χ a) (hχ a)))
  exact IsSubquotient.of_injective φ.toIntertwiningMap (fun u v huv => φ.toLinearEquiv.injective huv)

end GlobalTheory.LocLanglands
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.localCountDirectLifting_proof : StepLocDirect := by
  first | exact @GlobalTheory.Pass.LocDirect.main | exact GlobalTheory.Pass.LocDirect.main | (intros; apply GlobalTheory.Pass.LocDirect.main <;> assumption)
end
