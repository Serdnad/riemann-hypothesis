module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle081
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem sum_map_apply {ι σ : Type} [Fintype ι] (m : ι → σ →₀ ℕ) (i : ι) (x : σ) :
    (∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j)) (i, x) = m i x := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.mk.inj h).2) _ _
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hj (Prod.mk.inj hy).1
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem coeff_prod' {ι σ C : Type} [DecidableEq ι] [DecidableEq σ] [CommRing C] (f : ι → MvPolynomial σ C)
    (d : σ →₀ ℕ) (s : Finset ι) :
    AddMonoidAlgebra.coeff (∏ j ∈ s, f j) d = ∑ l ∈ Finset.finsuppAntidiag s d, ∏ j ∈ s, AddMonoidAlgebra.coeff (f j) (l j) := by
  have h := MvPowerSeries.coeff_prod (fun j => (f j : MvPowerSeries σ C)) d s
  have hp : ((∏ j ∈ s, f j : MvPolynomial σ C) : MvPowerSeries σ C) = ∏ j ∈ s, (f j : MvPowerSeries σ C) :=
    map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := C)) f s
  rw [← hp] at h
  simpa only [MvPolynomial.coeff_coe] using h

private theorem coeff_prod_ren {ι σ C : Type} [Fintype ι] [CommRing C] (m : ι → σ →₀ ℕ)
    (G : ι → MvPolynomial σ C) :
    AddMonoidAlgebra.coeff (∏ j, MvPolynomial.rename (fun v : σ => (j, v)) (G j))
        (∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j)) =
      ∏ j, AddMonoidAlgebra.coeff (G j) (m j) := by
  classical
  set D := ∑ j, Finsupp.mapDomain (fun v : σ => (j, v)) (m j) with hD
  have inj : ∀ j : ι, Function.Injective (fun v : σ => (j, v)) := fun j a b h => (Prod.mk.inj h).2
  rw [coeff_prod', Finset.sum_eq_single
    (Finsupp.equivFunOnFinite.symm fun j => Finsupp.mapDomain (fun v : σ => (j, v)) (m j))]
  · refine Finset.prod_congr rfl fun j _ => ?_
    exact MvPolynomial.coeff_rename_mapDomain _ (inj j) _ _
  · intro l hl hne
    by_contra hprod
    apply hne
    have hu : ∀ k, ∃ u : σ →₀ ℕ, Finsupp.mapDomain (fun v : σ => (k, v)) u = l k := by
      intro k
      by_contra hk
      push_neg at hk
      apply hprod
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      apply MvPolynomial.coeff_rename_eq_zero
      intro u hu'
      exact absurd hu' (hk u)
    choose u hu using hu
    have hsum : ∑ k, Finsupp.mapDomain (fun v : σ => (k, v)) (u k) = D := by
      rw [Finset.mem_finsuppAntidiag] at hl
      simp only [hu]
      exact hl.1
    have hum : u = m := by
      funext k
      ext x
      have hx := congrArg (fun F => F (k, x)) hsum
      simp only [hD, sum_map_apply] at hx
      exact hx
    ext1 k
    show l k = Finsupp.mapDomain (fun v : σ => (k, v)) (m k)
    rw [← hu k, hum]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    show ∑ k ∈ Finset.univ, Finsupp.mapDomain (fun v : σ => (k, v)) (m k) = D
    rw [hD]

private theorem unitri {I P C : Type} [Fintype I] [PartialOrder P] [CommRing C] (S : Subring C) (e : I → P)
    (he : Function.Injective e) (A : I → I → C) (c : I → C) (hA : ∀ i j, A i j ∈ S) (h1 : ∀ i, A i i = 1)
    (hle : ∀ i j, A i j ≠ 0 → e j ≤ e i) (hc : ∀ j, ∑ i, c i * A i j ∈ S) (j : I) : c j ∈ S := by
  classical
  suffices key : ∀ n, ∀ j, (Finset.univ.filter fun i => e j < e i).card = n → c j ∈ S from key _ j rfl
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro j hj
  have hrest : ∀ i ∈ Finset.univ.erase j, c i * A i j ∈ S := by
    intro i hi
    by_cases h0 : A i j = 0
    · rw [h0, mul_zero]
      exact S.zero_mem
    · have hlt : e j < e i :=
        lt_of_le_of_ne (hle i j h0) (fun h => (Finset.ne_of_mem_erase hi) (he h).symm)
      refine S.mul_mem ?_ (hA i j)
      refine ih _ ?_ i rfl
      rw [← hj]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset ?_).mpr ⟨i, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact lt_trans hlt hk
      · simp [hlt]
      · simp
  have hsum := hc j
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, mul_one] at hsum
  have hfin := S.sub_mem hsum (sum_mem hrest)
  simpa using hfin

theorem UpperTheory.WildA.bvvInt :
    ∀ {ι : Type} [Fintype ι] {b : ℕ} (lam : ι → DomWeight b) (v : VV ℂ lam),
      (∀ m, ∃ z : ℤ, AddMonoidAlgebra.coeff (v : Pol ℂ ι b) m = (z : ℂ)) → ∀ i, ∃ z : ℤ, (bVV ℂ lam).repr v i = (z : ℂ) := by
  intro ι _ b lam v hv i
  classical
  let L : VVIdx lam → (ι × Fin b × Fin b →₀ ℕ) := fun j =>
    ∑ τ, Finsupp.mapDomain (fun x : Fin b × Fin b => (τ, x)) ((j τ : Fin b × Fin b →₀ ℕ))
  let A : VVIdx lam → VVIdx lam → ℂ := fun i j => AddMonoidAlgebra.coeff (bVVfun ℂ lam i) (L j)
  let e : VVIdx lam → (ι → (Formalism.GradedWeylDivisibility.colLex b b).syn) := fun i τ =>
    (Formalism.GradedWeylDivisibility.colLex b b).toSyn ((i τ : Fin b × Fin b →₀ ℕ))
  have hspec : ∀ {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν),
      (Formalism.GradedWeylDivisibility.colLex n n).degree (ssB ℂ ν m) = m ∧ (Formalism.GradedWeylDivisibility.colLex n n).leadingCoeff (ssB ℂ ν m) = 1 := by
    intro n ν m
    have h := (Formalism.L2.DIV.ssB._proof_1 ℂ ν).choose_spec.2 m
    exact ⟨h.1, h.2.1⟩
  have hAprod : ∀ i j, A i j =
      ∏ τ, AddMonoidAlgebra.coeff (ssB ℂ (lam τ).natW (i τ)) (j τ : Fin b × Fin b →₀ ℕ) := by
    intro i j
    exact coeff_prod_ren (fun τ => (j τ : Fin b × Fin b →₀ ℕ)) (fun τ => ssB ℂ (lam τ).natW (i τ))
  have hdiag : ∀ i, A i i = 1 := by
    intro i
    rw [hAprod]
    apply Finset.prod_eq_one
    intro τ _
    have h := hspec (lam τ).natW (i τ)
    simpa [MonomialOrder.leadingCoeff, h.1] using h.2
  have hexp : (v : Pol ℂ ι b) = ∑ k ∈ ((bVV ℂ lam).repr v).support,
      ((bVV ℂ lam).repr v k) • bVVfun ℂ lam k := by
    have h0 := (bVV ℂ lam).linearCombination_repr v
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at h0
    conv_lhs => rw [← h0]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, bVV_coe]
  by_cases hi : i ∈ ((bVV ℂ lam).repr v).support
  swap
  · simp only [Finsupp.mem_support_iff, not_not] at hi
    exact ⟨0, by simp [hi]⟩
  have key : (bVV ℂ lam).repr v i ∈ (Int.castRingHom ℂ).range := by
    refine unitri (I := {x // x ∈ ((bVV ℂ lam).repr v).support}) (Int.castRingHom ℂ).range
      (fun x => e x.1) ?_ (fun x y => A x.1 y.1) (fun x => (bVV ℂ lam).repr v x.1) ?_ ?_ ?_ ?_ ⟨i, hi⟩
    · intro x y hxy
      apply Subtype.ext
      funext τ
      apply Subtype.ext
      exact (Formalism.GradedWeylDivisibility.colLex b b).toSyn.injective (congrFun hxy τ)
    · intro x y
      obtain ⟨P, hP⟩ := bVVfun_int ℂ lam x.1
      refine RingHom.mem_range.mpr ⟨AddMonoidAlgebra.coeff P (L y.1), ?_⟩
      show _ = AddMonoidAlgebra.coeff (bVVfun ℂ lam x.1) (L y.1)
      rw [hP, MvPolynomial.coeff_map]
    · intro x
      exact hdiag x.1
    · intro x y hxy τ
      have hne : ∀ τ ∈ Finset.univ,
          AddMonoidAlgebra.coeff (ssB ℂ (lam τ).natW (x.1 τ)) (y.1 τ : Fin b × Fin b →₀ ℕ) ≠ 0 := by
        rw [← Finset.prod_ne_zero_iff, ← hAprod]
        exact hxy
      have hd := (Formalism.GradedWeylDivisibility.colLex b b).le_degree
        (MvPolynomial.mem_support_iff.mpr (hne τ (Finset.mem_univ τ)))
      rw [(hspec (lam τ).natW (x.1 τ)).1] at hd
      exact hd
    · intro j
      have hcoef : AddMonoidAlgebra.coeff (v : Pol ℂ ι b) (L j.1) =
          ∑ x : {x // x ∈ ((bVV ℂ lam).repr v).support}, (bVV ℂ lam).repr v x.1 * A x.1 j.1 := by
        rw [hexp, MvPolynomial.coeff_sum, ← Finset.sum_coe_sort]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [MvPolynomial.coeff_smul, smul_eq_mul] <;> rfl
      show ∑ x : {x // x ∈ ((bVV ℂ lam).repr v).support}, (bVV ℂ lam).repr v x.1 * A x.1 j.1 ∈ _
      rw [← hcoef]
      obtain ⟨z, hz⟩ := hv (L j.1)
      exact RingHom.mem_range.mpr ⟨z, by simp [hz]⟩
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp key
  exact ⟨z, by simpa using hz.symm⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open MvPolynomial Formalism.L2.Ker GlobalTheory.JetDeg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}

private def frW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun k => if k.1 = τ then 1 else 0) fun _ => 0

omit [Fintype ι] in
private theorem subD_hom_fr (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (frW a b τ) (subD K ι a b P) d := by
  have key : ∀ v : ι × Fin a × Fin a,
      IsWeightedHomogeneous (frW a b τ) (subD K ι a b (X v)) (AddMonoidHom.id ℕ (posW a τ v)) := by
    intro v
    simp only [subD, MvPolynomial.aeval_X, AddMonoidHom.id_apply]
    split_ifs with h
    · apply IsWeightedHomogeneous.sum
      intro β _
      have hm := (isWeightedHomogeneous_X K (frW a b τ) (Sum.inl (v.1, β, ⟨v.2.2, h⟩))).mul
        (isWeightedHomogeneous_X K (frW a b τ) (Sum.inr (v.1, β, v.2.1)))
      convert hm using 1
      simp [frW, posW]
    · exact isWeightedHomogeneous_zero K _ _
  simpa using algHom_hom (posW a τ) (frW a b τ) (AddMonoidHom.id ℕ) (subD K ι a b) key hP

private theorem weight_fr (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (posW b τ) (μ.comapDomain Sum.inl Sum.inl_injective.injOn) = Finsupp.weight (frW a b τ) μ := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sum_type]
  simp [frW, posW]

private theorem weight_der (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    ((μ.comapDomain Sum.inr Sum.inr_injective.injOn).sum fun v e => if v.1 = τ then e else 0) =
      Finsupp.weight (derW a b τ) μ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_sum_type]
  simp [derW]

omit [DecidableEq ι] in
private theorem jetLin_eq (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J Q = ∑ μ ∈ Q.support, AddMonoidAlgebra.coeff Q μ • (monomial (μ.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b) := by
  classical

  conv_lhs => rw [Q.as_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : (monomial μ (AddMonoidAlgebra.coeff Q μ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      AddMonoidAlgebra.coeff Q μ • (basisMonomials _ K) μ := by
    rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  simp only [jetLin, Module.Basis.constr_basis]

private theorem jetMap_congr_deg (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (hV : JetInVV K lam lam' n) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = ∑ i, (lam' τ).natW i) → J m = J' m)
    (P : Pol K ι a) (hP : P ∈ Formalism.L2.DIV.VV K lam) : jetMap J n P = jetMap J' n P := by
  set Q := subD K ι a b (GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) with hQ
  have hJ : ∀ J₀ : (DVar ι a b →₀ ℕ) → K, jetMap J₀ n P = jetLin J₀ Q := fun J₀ => rfl
  have hfr : ∀ τ, IsWeightedHomogeneous (frW a b τ) Q (∑ i, (lam τ).natW i + n τ * a) :=
    fun τ => subD_hom_fr τ (sharp_hom n τ (VV_hom lam τ hP))
  have hder : ∀ τ, IsWeightedHomogeneous (derW a b τ) Q (∑ i, (lam τ).natW i + n τ * a) :=
    fun τ => subD_hom τ (sharp_hom n τ (VV_hom lam τ hP))
  have hdeg : ∀ (J₀ : (DVar ι a b →₀ ℕ) → K) τ,
      IsWeightedHomogeneous (posW b τ) (jetLin J₀ Q) (∑ i, (lam τ).natW i + n τ * a) := by
    intro J₀ τ
    rw [jetLin_eq]
    apply IsWeightedHomogeneous.sum
    intro μ hμ
    rw [smul_monomial]
    apply isWeightedHomogeneous_monomial
    rw [weight_fr]
    exact hfr τ (mem_support_iff.mp hμ)
  by_cases hall : ∀ τ, ∑ i, (lam τ).natW i + n τ * a = ∑ i, (lam' τ).natW i
  · rw [hJ, hJ, jetLin_eq, jetLin_eq]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hJJ : J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
        J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn) := by
      apply h
      intro τ
      rw [weight_der, ← hall τ]
      exact hder τ (mem_support_iff.mp hμ)
    rw [hJJ]
  · push_neg at hall
    obtain ⟨τ, hτ⟩ := hall
    have hz : ∀ J₀ : (DVar ι a b →₀ ℕ) → K, jetMap J₀ n P = 0 := by
      intro J₀
      by_contra hne
      have h1 := VV_hom lam' τ (hV J₀ P hP)
      have h2 := hdeg J₀ τ
      rw [← hJ] at h2
      exact hτ (IsWeightedHomogeneous.inj_right hne h2 h1)
    rw [hz J, hz J']

end SlopeTestRemainingChoices

theorem UpperTheory.WildA.jetDeg :
    ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ),
      Formalism.L2.Ker.JetInVV K lam lam' n → ∀ J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K,
      (∀ m : Formalism.L2.Ker.DVar ι a b →₀ ℕ, (∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = ∑ i, (lam' τ).natW i) → J m = J' m) →
      Formalism.L2.Ker.jetOp lam lam' J n = Formalism.L2.Ker.jetOp lam lam' J' n := by
  intro K _ _ ι _ _ a b lam lam' n hV J J' h
  refine LinearMap.ext fun P => ?_
  show Formalism.L2.Ker.retrVV K lam' (Formalism.L2.Ker.jetMap J n P.1) = Formalism.L2.Ker.retrVV K lam' (Formalism.L2.Ker.jetMap J' n P.1)
  rw [jetMap_congr_deg lam lam' n hV J J' h P.1 P.2]
end
