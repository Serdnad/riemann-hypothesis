module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle011
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle003
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace FunctionFieldFinite

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

def chartGens (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    Set (FractionRing (MRing ι F ⧸ P)) :=
  Set.range fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))


omit [Fintype K] [DecidableEq K] in
theorem range_chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartMap P u).range = Algebra.adjoin F (chartGens P u) :=
  aeval_range _

theorem homFracDegZero_eq (hD : MChartDehomog.Statement.{u}) (P : Ideal (MRing ι F)) [P.IsPrime]
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    homFracDegZero P = IntermediateField.adjoin F (chartGens P u) := by
  apply le_antisymm
  · unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, f, g, hf, hg, -, rfl⟩
    have hm : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
      rw [chartMonomial, map_prod, map_prod]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
      rw [map_pow, map_pow]
      refine pow_ne_zero _ ?_
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    have hr : ∀ p, chartMap P u p ∈ IntermediateField.adjoin F (chartGens P u) := fun p =>
      IntermediateField.algebra_adjoin_le_adjoin F _ (by rw [← range_chartMap]; exact ⟨p, rfl⟩)
    have key := div_mem (hr f) (hr g)
    rwa [hD F K ι P u hu f b hf, hD F K ι P u hu g b hg, div_div_div_cancel_right₀ hm] at key
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨blockWeight ι v, X v, X ⟨v.1, u v.1⟩,
      isWeightedHomogeneous_X _ _ _, isWeightedHomogeneous_X _ _ _, hu v.1, rfl⟩


open IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_homFracDegZero (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.trdeg F (homFracDegZero P) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P) := by
  haveI : Algebra.FiniteType F (Algebra.adjoin F (chartGens P u)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  rw [← hT F K ι P hP u hu, homFracDegZero_eq hD P u hu,
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F)
      (A := Algebra.adjoin F (chartGens P u)), ← range_chartMap]
  exact congrArg (· + _) (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq.symm

theorem relDim_eq_trdeg (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiProjPrime P) :
    ∃ n : ℕ, Algebra.trdeg F (homFracDegZero P) = n ∧
      relDim P = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  choose u hu using hP.relevant
  have h1 := trdeg_homFracDegZero hD hT P hP.multiHomog u hu
  obtain ⟨m, hdim, htr⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MRing ι F ⧸ P)
  rw [htr] at h1
  have hlt : Algebra.trdeg F (homFracDegZero P) < Cardinal.aleph0 :=
    lt_of_le_of_lt (h1 ▸ self_le_add_right _ _) (Cardinal.natCast_lt_aleph0 (n := m))
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hn] at h1
  have hnm : n + Fintype.card K = m := by exact_mod_cast h1
  refine ⟨n, hn, ?_⟩
  have hz : (((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) = n := by push_cast; ring
  rw [relDim, hdim, ← hnm, ← hz]
  rfl

end FunctionFieldFinite


open FunctionFieldFinite in
theorem FunctionFieldFinite.proof (hD : MChartDehomog.Statement.{u})
    (hT : MChartTrdeg.Statement.{u}) : FunctionFieldFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hrel
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  obtain ⟨n, hn, hrn⟩ := relDim_eq_trdeg hD hT (contractPrime j P') hP
  obtain ⟨n', hn', hrn'⟩ := relDim_eq_trdeg hD hT P' hP'
  have hnn : n = n' := by
    rw [hrel, hrn'] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  set E := (homFracDegZero (contractPrime j P')).map (contractFracMap j P')
  set κ' := homFracDegZero P'
  have h : E ≤ κ' := map_homFracDegZero_le j ι' P'
  have hE : Algebra.trdeg F E = n :=
    (IntermediateField.equivMap _ (contractFracMap j P')).trdeg_eq.symm.trans hn
  let _ : Algebra E κ' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E κ' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul E κ' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IntermediateField.inclusion h).injective
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  have htow := trdeg_add_eq F E (A := κ')
  rw [hE, hn', ← hnn] at htow
  have hlt : Algebra.trdeg E κ' < Cardinal.aleph0 :=
    lt_of_le_of_lt (htow ▸ self_le_add_left _ _) (Cardinal.natCast_lt_aleph0 (n := n))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at htow
  have hm0 : m = 0 := by
    have : n + m = n := by exact_mod_cast htow
    omega
  have : Algebra.IsAlgebraic E κ' := trdeg_eq_zero_iff.mp (by rw [hm, hm0]; rfl)
  let g : κ' →ₐ[E] FractionRing (MRing ι' F ⧸ P') :=
    { (κ'.val : κ' →+* FractionRing (MRing ι' F ⧸ P')) with commutes' := fun _ => rfl }
  choose u hu using hP'.relevant
  have hκ' : κ' = IntermediateField.adjoin F (chartGens P' u) := homFracDegZero_eq hD P' u hu
  have hint : ∀ x ∈ chartGens P' u, IsIntegral E x := by
    intro x hx
    have hx' : x ∈ κ' := hκ' ▸ IntermediateField.subset_adjoin F _ hx
    have hy : IsAlgebraic E (⟨x, hx'⟩ : κ') := Algebra.IsAlgebraic.isAlgebraic _
    exact IsIntegral.map g hy.isIntegral
  have : Finite (chartGens P' u) := (Set.finite_range _).to_subtype
  have := IntermediateField.finiteDimensional_adjoin hint
  show IntermediateField.relfinrank E κ' ≠ 0
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  have hext : IntermediateField.extendScalars h = IntermediateField.adjoin E (chartGens P' u) := by
    rw [← IntermediateField.extendScalars_adjoin (h.trans hκ'.le)]
    exact IntermediateField.ext fun x =>
      show x ∈ κ' ↔ x ∈ IntermediateField.adjoin F (chartGens P' u) by rw [hκ']
  rw [hext]
  exact Module.finrank_pos.ne'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem exists_form_not_mem {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u}
    [Field F] {W : Ideal (MRing ι F)} (hW : IsMultiProjPrime W) (c : K → ℕ) :
    ∃ h : MRing ι F, IsMultiHomog h c ∧ h ∉ W := by
  choose v hv using hW.relevant
  have := hW.isPrime
  refine ⟨∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (c k))
    have hc : (∑ k, c k • blockWeight ι ⟨k, v k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem this _ hk)

theorem DivPushForwardLocal.proof (h1 : DivCycleMinimal.Statement.{u})
    (h2 : ConeLocalLength.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : SemilocalFiniteRank.Statement.{u}) (h5 : SemilocalLength.Statement.{u}) :
    DivPushForwardLocal.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hdim hdimP c a ha haP W hW hWd M hM1 hM0
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  by_cases hPW : contractPrime j P' ⊔ Ideal.span {a} ≤ W
  · have := hW.isPrime
    have hPle : contractPrime j P' ≤ W := le_trans le_sup_left hPW
    obtain ⟨h, hh, hhW⟩ := exists_form_not_mem hW c
    let α : degZeroLoc (contractPrime j P') {W} := ⟨_, div_mem_degZeroLoc _ _ ha hh
      (fun hm => hhW (hPle hm)) (fun W₁ h₁ => (Set.mem_singleton_iff.mp h₁) ▸ hhW)⟩
    have hα0 : α ≠ 0 := by
      intro h0
      have h0' := congrArg Subtype.val h0
      rcases div_eq_zero_iff.mp h0' with h' | h' <;>
        rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h'
      · exact haP h'
      · exact hhW (hPle h')
    obtain ⟨⟨hNo, hLo⟩, hdA⟩ := h3 F K _ _ hP W hW hPle
    obtain ⟨hfin, htf, hrk⟩ := h4 F K K' j ι' P' hP' n hdim hdimP W hW hWd hPle
    have key := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula _ (degZeroLoc P' (fibrePrimes j P' W)) α
      (hdA n hdimP hWd) hα0
    obtain ⟨N, hN, hMN⟩ := h5 F K K' j ι' P' hP' n hdim hdimP c a h ha hh haP W hW hWd hPle hhW
      M hM1 hM0 α rfl
    obtain ⟨hmin, hfinm⟩ := h1 F K _ _ hP.isPrime n hdimP a haP W hW.isPrime hWd hPW
    have hcone := h2 F K _ _ hP W hW hPle c a h ha hh hhW α rfl
    have hdc : divCycle (contractPrime j P') a W =
        ((multAt (contractPrime j P' ⊔ Ideal.span {a}) W).toNat : ℤ) := by
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hW.relevant⟩]
    rw [hMN, hdc]
    rw [hN, hrk, ← hcone] at key
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinm
    rw [← hm] at key ⊢
    have hNm : N = relDeg j P' * m := by exact_mod_cast key
    rw [hNm, ENat.toNat_natCast]
    push_cast
    rfl
  · have hR : divCycle (contractPrime j P') a W = 0 := by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, -⟩
      exact hPW h.1.2
    rw [hR, mul_zero]
    unfold cycEval
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    by_cases hD : divCycle P' (rename (blockIncl j ι') a) W' = 0
    · rw [hD, zero_mul]
    · refine mul_eq_zero_of_right _ (hM0 W' fun hc => hPW ?_)
      unfold divCycle at hD
      split_ifs at hD with hm
      · rw [← hc]
        refine sup_le (Ideal.comap_mono (le_trans le_sup_left hm.1.1.2)) ?_
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hm.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      · exact absurd rfl hD

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocNoetherian.proof (h : DegZeroLocQuot.Statement.{u}) :
    DegZeroLocNoetherian.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  let φ : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    (IsScalarTower.toAlgHom F (MRing ι F ⧸ P) _).comp (Ideal.Quotient.mkₐ F P)
  have hφ : ∀ f, f ∉ P → φ f ≠ 0 := fun f hf h0 => hf (by
    rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0)
  choose v hv using hW.relevant
  let e : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    aeval fun x => φ (X x) / φ (X ⟨x.1, v x.1⟩)
  let c : (K → ℕ) → MRing ι F := fun b => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ b k
  have hcW : ∀ b, c b ∉ W := by
    intro b
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)
  have hc : ∀ b, IsMultiHomog (c b) b := by
    intro b
    have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (b k))
    have hb : (∑ k, b k • blockWeight ι ⟨k, v k⟩) = b := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hb] at hprod
    exact hprod
  have hcadd : ∀ b b', c (b + b') = c b * c b' := fun b b' => by
    simp only [c, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hmono : ∀ m : (Σ k, ι k) →₀ ℕ,
      φ (monomial m 1) = e (monomial m 1) * φ (c (Finsupp.weight (blockWeight ι) m)) := by
    intro m
    refine Finsupp.induction m ?_ ?_
    · simp [c]
    · intro x n m _ _ ih
      have hs : φ (monomial (Finsupp.single x n) 1) = e (monomial (Finsupp.single x n) 1) *
          φ (c (Finsupp.weight (blockWeight ι) (Finsupp.single x n))) := by
        rw [Finsupp.weight_single, ← X_pow_eq_monomial, map_pow, map_pow, aeval_X]
        have hcs : c (n • blockWeight ι x) = (X ⟨x.1, v x.1⟩ : MRing ι F) ^ n := by
          simp only [c, blockWeight]
          rw [Finset.prod_eq_single x.1]
          · simp
          · intro k _ hk
            simp [hk]
          · simp
        rw [hcs, map_pow, ← mul_pow, div_mul_cancel₀ _ (hφ _ fun hm => hv x.1 (hPW hm))]
      rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, ih, map_add (f := _), hcadd, map_mul, hs]
      ring

  have hhom : ∀ (b : K → ℕ) (f : MRing ι F), IsMultiHomog f b → φ f = e f * φ (c b) := by
    intro b f hf
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]

    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (blockWeight ι) m = b := hf (mem_support_iff.mp hm)
    have hmon : monomial m (AddMonoidAlgebra.coeff f m) = AddMonoidAlgebra.coeff f m • monomial m (1 : F) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, map_smul, hmono, hw, smul_mul_assoc]
  have hle : e.range ≤ degZeroLoc P {W} := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) x)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨x.1, v x.1⟩) (fun hm => hv x.1 (hPW hm))
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hv x.1)
  have : Algebra.FiniteType F e.range :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have _ : IsNoetherianRing e.range := Algebra.FiniteType.isNoetherianRing F e.range
  let _ : Algebra e.range (degZeroLoc P {W}) := (Subalgebra.inclusion hle).toAlgebra
  let M : Submonoid e.range :=
    (IsUnit.submonoid (degZeroLoc P {W})).comap (algebraMap e.range (degZeroLoc P {W}))
  have hloc : IsLocalization M (degZeroLoc P {W}) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_,
      fun {x y} hxy => ⟨1, by rw [Subalgebra.inclusion_injective hle hxy]⟩⟩
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hz⟩ := h F K ι P {W}
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) z.1 z.2
    have hgW' : g ∉ W := hgW W rfl
    have hcb : φ (c b) ≠ 0 := hφ _ fun hm => hcW b (hPW hm)
    have hz' : (z : FractionRing (MRing ι F ⧸ P)) = φ f / φ g := hz
    have heg : e g ≠ 0 := by
      intro h0
      apply hφ g hgP
      rw [hhom b g hg, h0, zero_mul]
    have hinv : (e g)⁻¹ ∈ degZeroLoc P {W} := by
      have hq : (e g)⁻¹ = φ (c b) / φ g := by
        rw [hhom b g hg]
        field_simp
      rw [hq]
      exact div_mem_degZeroLoc P {W} (hc b) hg hgP
        (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hgW')
    have hunit : (⟨e g, g, rfl⟩ : e.range) ∈ M :=
      isUnit_iff_exists_inv.mpr ⟨⟨(e g)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ heg)⟩
    refine ⟨(⟨e f, f, rfl⟩, ⟨⟨e g, g, rfl⟩, hunit⟩), Subtype.ext ?_⟩
    change (z : FractionRing (MRing ι F ⧸ P)) * e g = e f
    rw [hz', hhom b f hf, hhom b g hg]
    field_simp
  exact IsLocalization.isNoetherianRing M _ inferInstance

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ringKrullDim_eq_of_relDim {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {F : Type u} [Field F] {Q : Ideal (MRing ι F)} {m : ℕ} (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have hm : ((m : ℕ) : WithBot (WithTop ℤ)) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  unfold relDim at h
  rw [hm] at h
  cases hd : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [hd] at h
    exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      exact absurd h (WithTop.top_ne_coe)
    | coe D =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      change (((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) at h
      have h := WithTop.coe_inj.mp h
      have : D = m + Fintype.card K := by omega
      rw [this]
      rfl

theorem DegZeroLocalRing.proof (h1 : DegZeroLocLocal.Statement.{u})
    (h2 : DegZeroLocNoetherian.Statement.{u}) (h3 : DegZeroLocDim.Statement.{u}) :
    DegZeroLocalRing.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  refine ⟨⟨h2 F K ι P hP W hW hPW, h1 F K ι P hP W hW hPW⟩, fun n hn1 hn => ?_⟩
  have e := h3 F K ι P hP W hW hPW
  rw [ringKrullDim_eq_of_relDim hn1, ringKrullDim_eq_of_relDim hn] at e
  revert e
  generalize ringKrullDim (degZeroLoc P {W}) = d
  intro e
  cases d with
  | bot =>
    rw [WithBot.bot_add] at e
    exact absurd e WithBot.bot_ne_coe
  | coe d =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at e
    induction d using ENat.recTopCoe with
    | top =>
      rw [top_add] at e
      exact absurd e.symm (ENat.natCast_ne_top _)
    | coe d =>
      rw [← Nat.cast_add, Nat.cast_inj] at e
      have : d = 1 := by omega
      rw [this]
      rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
