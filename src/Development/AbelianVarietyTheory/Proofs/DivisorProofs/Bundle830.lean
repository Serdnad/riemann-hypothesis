module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.constantCoeff_pIterate_invariantDerivation_coord : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (l : MvPowerSeries (Fin d) Q) (j : Fin d), QL μ ⊤ l → In (RingHom.ker θ) (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ c : Fin d → B, (∀ i, algebraMap B Q (c i) = (p : Q) * coeff (Finsupp.single i p) l) → ∀ u : Fin d → B, constantCoeff ((invDer μ u)^[p] (X j)) - ∑ i, c i * u i ^ p ∈ RingHom.ker θ ⊔ Ideal.span {(p : B)} := by
  first | exact @GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem | exact GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem | (intros; apply GlobalTheory.FrobIter.constantCoeff_iterate_invDer_X_sub_mem <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.TangentComb

theorem in_top_add_smul {O Q σ : Type} [CommRing O] [CommRing Q] [Algebra O Q]
    {f g : MvPowerSeries σ Q} (hf : In (⊤ : Ideal O) f) (hg : In (⊤ : Ideal O) g) (a : O) :
    In (⊤ : Ideal O) (f + algebraMap O Q a • g) := by
  intro α
  obtain ⟨b, -, hb⟩ := hf α
  obtain ⟨b', -, hb'⟩ := hg α
  refine ⟨b + a * b', trivial, ?_⟩
  rw [map_add (f := _), map_smul, hb, hb', map_add (f := _), map_mul, smul_eq_mul]

theorem ql_add_smul {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) :
    QL μ ⊤ (f + algebraMap O Q a • g) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add (f := _), map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨b, -, hb⟩ := hf.2.1 i
    obtain ⟨b', -, hb'⟩ := hg.2.1 i
    refine ⟨b + a * b', trivial, ?_⟩
    simp only [lin] at hb hb' ⊢
    rw [map_add (f := _), map_smul, hb, hb', map_add (f := _), map_mul, smul_eq_mul]
  · rw [formalCoboundary_add hμ', formalCoboundary_smul hμ']
    exact in_top_add_smul hf.2.2 hg.2.2 a

theorem ql_zero {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) :
    QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  have h0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0 := by
    have := formalCoboundary_smul hμ' (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    rwa [zero_smul, zero_smul] at this
  refine ⟨map_zero _, fun i => ⟨0, trivial, ?_⟩, ?_⟩
  · simp [lin]
  · rw [h0]
    exact In.top_iff.2 ⟨0, map_zero _⟩

end GlobalTheory.TangentComb

open GlobalTheory.TangentComb in
theorem GlobalTheory.TangentComb.main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) C), (∀ m, QL c.μ ⊤ (e m)) → ∀ (L : ι → G.dual.Lie), (∀ m, c.IsLie (e m) (L m)) → ∀ (g : MvPowerSeries (Fin d) C), QL c.μ ⊤ g → ∀ (a : ι → O), In (⊤ : Ideal O) (g - comb a e) → c.IsLie g (∑ m, a m • L m) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c ι _ e he L hL g hg a hint
  classical
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have lin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF
  have hμ := c.isLaw.const

  have key : ∀ s : Finset ι, QL c.μ ⊤ (∑ m ∈ s, algebraMap O C (a m) • e m) ∧
      c.IsLie (∑ m ∈ s, algebraMap O C (a m) • e m) (∑ m ∈ s, a m • L m) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨ql_zero hμ, c.isLie_zero hF.inj⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, add_comm, add_comm (a j • L j)]
      exact ⟨ql_add_smul hμ ih.1 (he j) (a j),
        (lin _ _ _ _ (a j) ih.2 (hL j)).1 ih.1 (he j)⟩
  obtain ⟨hQ, hI⟩ := key Finset.univ
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF g hg
  have h1 := (lin g (comb a e) l (∑ m, a m • L m) (-1) hl hI).1 hg hQ
  have hser : g + algebraMap O C (-1) • comb a e = g - comb a e := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [hser] at h1
  obtain ⟨s, hs⟩ := In.top_iff.1 hint
  have h0 := (lin _ (comb a e) _ (∑ m, a m • L m) 0 h1 hI).2.1 ⟨s, hs.symm⟩
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0 ▸ hl
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pAdicEvaluation_subst_compatible_thickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q) (q : Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → HasVal p (fun j => E (u j)) f q → HasVal p z (subst (up Q u) f) q := by
  first | exact @GlobalTheory.QLog.hasVal_subst | exact GlobalTheory.QLog.hasVal_subst | (intros; apply GlobalTheory.QLog.hasVal_subst <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.tangent_coords_nonunit_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∀ (b : Fin k → O) (s : MvPowerSeries (Fin d) O), (∀ α, ∃ o : O, ¬IsUnit o ∧ coeff α (cob1 (up E c.μ) (comb (Sum.elim 0 b) e) - map (algebraMap O E) (cob1 c.μ s)) = algebraMap O E o) → ∀ j, ¬IsUnit (b j) := by
  first | exact @GlobalTheory.TangentIndep.tangent_coords_nonunit | exact GlobalTheory.TangentIndep.tangent_coords_nonunit | (intros; apply GlobalTheory.TangentIndep.tangent_coords_nonunit <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.logarithm_integers_adapted_basis_no_lie_components : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  first | exact @GlobalTheory.QLog.RedO.main | exact GlobalTheory.QLog.RedO.main | (intros; apply GlobalTheory.QLog.RedO.main <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.GlVec

theorem isSmoothFun_and_rightDeriv_eq_vecF : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) ∧ ∀ X : glL E a, ContDiffOn ℝ ∞ (vecF E a (toL X.1) f) (invSet E a) ∧ (glH E a).rightDeriv X (fun y : glG E a => f (toL y.1.val)) = fun y : glG E a => vecF E a (toL X.1) f (toL y.1.val) := by
  intro E _ _ _ a f hf
  let Tl : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a :=
    { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap Tl
  have hT : ∀ x, T x = toL x := fun _ => rfl
  have hval : ∀ (g : glG E a) (Y : glL E a), ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      = (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro g Y; rfl
  have hsm : (glH E a).IsSmoothFun (fun y : glG E a => f (toL y.1.val)) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hin : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((GroundTheory.Automorphic.contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    have := hf.comp_contDiff hin (fun Y => by
      rw [hT, ← hval g Y]; exact val_mem_invSet _)
    have e : (fun Y : glL E a => f (toL ((g * (glH E a).expG Y : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val)) =
        f ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
          NormedSpace.exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) := by
      funext Y; simp only [Function.comp_apply, hT, hval]
    rw [e]
    exact this
  refine ⟨hsm, fun X => ⟨?_, ?_⟩⟩
  · exact (hf.fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul (toL X.1)).contDiff.contDiffOn
  · funext y
    have h1 := IsExpLieAlgebra.hasDerivAt_rightDeriv (glH E a) hsm X y
    have hy : toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val ∈ invSet E a := val_mem_invSet _
    have hfd : HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) :=
      ((hf.contDiffAt (isOpen_invSet.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E)))))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * (X : Matrix (Fin a) (Fin a) (Cinf E)))) 0 := by
      have h2 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)).const_mul
        (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val
      simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
    have hc' : HasDerivAt (fun t : ℝ => T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val *
        NormedSpace.exp (t • (X : Matrix (Fin a) (Fin a) (Cinf E))))) _ 0 := hc
    have h3 := (show HasFDerivAt f (fderiv ℝ f (toL (y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val))
        (T ((y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * NormedSpace.exp ((0:ℝ) • (X : Matrix (Fin a) (Fin a) (Cinf E))))) by
          simpa [hT] using hfd).comp_hasDerivAt (0 : ℝ) hc'
    exact h1.unique h3

end GlobalTheory.GlVec
end

section

open IsLocalRing GlobalTheory.Toroidal Polynomial

namespace GlobalTheory

theorem exists_monic_simple_root_generator_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R']
    [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' →
    ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' →
    ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧
      (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧
      ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  intro O R' Ω _ _ _ _ _ φ u hφ hur hker
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : φ a ∈ maximalIdeal R' := hmax ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  have hcomp : (ResidueField.map φ).comp (residue O) = (residue R').comp φ :=
    ResidueField.map_comp_residue φ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← hcomp] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField O) (ResidueField R') := hfin'
  haveI : Algebra.FormallyUnramified (ResidueField O) (ResidueField R') := hur'
  haveI : Algebra.IsSeparable (ResidueField O) (ResidueField R') :=
    Algebra.FormallyUnramified.isSeparable _ _
  let ι : ResidueField R' →+* Ω := Ideal.Quotient.lift (maximalIdeal R') u
    (fun a ha => by rwa [← RingHom.mem_ker, hker])
  have hι : ∀ r, ι (residue R' r) = u r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hres : ∀ (P : O[X]) (x : ResidueField R'),
      (P.map (u.comp φ)).eval (ι x) = ι (aeval x (P.map (residue O))) := by
    intro P x
    rw [aeval_def, hom_eval₂, eval₂_map, eval_map]
    congr 1
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField O) (ResidueField R')
  have hint : IsIntegral (ResidueField O) α := Algebra.IsIntegral.isIntegral α
  have hpm : (minpoly (ResidueField O) α).Monic := minpoly.monic hint
  have hlift : minpoly (ResidueField O) α ∈ lifts (residue O) :=
    (lifts_iff_coeff_lifts _).2 fun n => residue_surjective _
  obtain ⟨G, hGmap, -, hGm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  refine ⟨G, ι α, hGm, ?_, ?_, ?_⟩
  · rw [hres, hGmap, minpoly.aeval, map_zero]
  · rw [derivative_map, hres, ← derivative_map, hGmap]
    refine (map_ne_zero ι).2 ?_
    exact (Algebra.IsSeparable.isSeparable (ResidueField O) α).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · intro r
    have hr : residue R' r ∈ Algebra.adjoin (ResidueField O) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue O) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [hres, hP, ← hι]
    exact congrArg ι hpb.symm

end GlobalTheory
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedUniq

theorem op_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))),
    (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) →
    ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  intro Q q _ hq i ρ ρ' h E n x
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ
  obtain ⟨u', hu'⟩ := GlobalTheory.T.exists_factor_through_extendScalars_zmod Q q hq _ _ ρ'
  have e1 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ u hu).1 E n x
  have e2 := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective _ _ (extπ (ZMod.castHom hq (ZMod q)) (res _ (tw Q i))) ρ' u' hu').1 E n x
  have hε := GlobalTheory.T.extendScalars_tateTwistResolution_hom_ext_augmentation Q q hq i _ u u' (fun U ζ => by rw [← hu, ← hu', h])
  haveI := GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation Q q hq i
  haveI : (res (ZMod q) (tw q i)).IsKInjective :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsKInjective)
  haveI : (res (ZMod q) (tw q i)).IsStrictlyGE 0 :=
    inferInstanceAs ((injectiveResolution (tw q i)).cochainComplex.IsStrictlyGE 0)
  obtain ⟨H⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) _ _ (res _ (tw q i)) (extAug (ZMod.castHom hq (ZMod q)) (tw Q i))).2 u u' hε
  have e3 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)).2.2.2.2 u u' ⟨H⟩ ((chains (ZMod q)).obj E) n).2
  rw [e1, e2, e3]

end GlobalTheory.EtC.RedUniq

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.pullbackLAdicRationalCohomology_galoisCover_invariants : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id) := by
  exact @GlobalTheory.pullHQ_galoisCover_inv
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MVEtale

theorem mv_etale_mid : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  intro q A A' _ _ _ _ f h1 h2 n i x y hxy
  obtain ⟨w, hS⟩ := chains_shortExact (ZMod q) A A' f h1 h2
  obtain ⟨d, hd, -⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)).2.1
  obtain ⟨e1, -, -⟩ := hd _ hS n
  have hb := cpull_biprod_bijective (ZMod q) ((chains (ZMod q)).obj (sp (Localization.Away f)))
    ((chains (ZMod q)).obj (sp A')) (res (ZMod q) (tw q i))
  obtain ⟨P, hP⟩ := (hb n).2 (x, y)
  have h0 : cpull (biprod.lift ((chains (ZMod q)).map (spMap (Localization.awayMap (algebraMap A A') f)))
      (-(chains (ZMod q)).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (res (ZMod q) (tw q i)) n P = 0 := by
    rw [cpull_lift_neg]
    have hP1 := congrArg Prod.fst hP
    have hP2 := congrArg Prod.snd hP
    simp only at hP1 hP2
    rw [hP1, hP2]
    exact sub_eq_zero.2 hxy
  obtain ⟨b, hb'⟩ := (e1 P).1 h0
  refine ⟨b, ?_, ?_⟩
  · have := congrArg Prod.fst (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.fst hP)
  · have := congrArg Prod.snd (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.snd hP)

end GlobalTheory.EtC.MVEtale
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem baseChange_sub_counit_mem (p : ℕ) (k k' : Type) [Field k] [Field k'] [Algebra k k']
    (G : PDivGroup p k) (n : ℕ) (x : (G.baseChange k').A n) :
    x - algebraMap k' _ (Coalgebra.counit (R := k') x) ∈
      Ideal.map (Algebra.TensorProduct.includeRight : G.A n →ₐ[k] k' ⊗[k] G.A n)
        (augIdeal k (G.A n)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b a =>
    have hc : Coalgebra.counit (R := k') (b ⊗ₜ[k] a : (G.baseChange k').A n) =
        b * algebraMap k k' (Coalgebra.counit (R := k) a) := by
      simp [Algebra.smul_def, mul_comm]
    have ha : a - algebraMap k (G.A n) (Coalgebra.counit (R := k) a) ∈ augIdeal k (G.A n) := by
      simp [RingHom.mem_ker]
    have he : (b ⊗ₜ[k] a : k' ⊗[k] G.A n) - algebraMap k' (k' ⊗[k] G.A n)
        (b * algebraMap k k' (Coalgebra.counit (R := k) a)) =
        (b ⊗ₜ[k] (1 : G.A n)) * Algebra.TensorProduct.includeRight
          (a - algebraMap k (G.A n) (Coalgebra.counit (R := k) a)) := by
      rw [map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
        mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one]
      congr 1
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := G.A n),
        one_mul, tmul_smul, smul_tmul', Algebra.algebraMap_self, RingHom.id_apply, Algebra.smul_def,
        mul_comm]
    rw [hc]
    exact he ▸ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)
  | add x y hx hy =>
    have : x + y - algebraMap k' ((G.baseChange k').A n) (Coalgebra.counit (R := k') (x + y)) =
        (x - algebraMap k' _ (Coalgebra.counit (R := k') x)) +
          (y - algebraMap k' _ (Coalgebra.counit (R := k') y)) := by
      rw [map_add (f := _), map_add (f := _)]; abel
    rw [this]
    exact add_mem hx hy

theorem baseChange_isConn_isEt : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k), (G.IsConn → (G.baseChange k').IsConn) ∧ (G.IsEt → (G.baseChange k').IsEt) := by
  intro p _ k k' _ _ _ _ _ _ _ G
  refine ⟨fun hG n x hx => ?_, fun hG n => ?_⟩
  · have h0 : Coalgebra.counit (R := k') x = 0 := hx
    have hmem := baseChange_sub_counit_mem p k k' G n x
    rw [h0, map_zero, sub_zero] at hmem
    have hle : Ideal.map (Algebra.TensorProduct.includeRight : G.A n →ₐ[k] k' ⊗[k] G.A n)
        (augIdeal k (G.A n)) ≤ nilradical (k' ⊗[k] G.A n) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact (hG n a ha).map _
    exact hle hmem
  · haveI : PerfectField k := PerfectRing.toPerfectField k p
    haveI : IsReduced (G.A n) := hG n
    exact GlobalTheory.ReducedAlg.isReduced_field_tensor k' (G.A n)

end GlobalTheory.Dieu
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G),
      g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  intro p _ R _ G H f g hgf a ha
  have hle : kerIdeal (f.app 1) ≤ RingHom.ker (g.app 1 : G.A 1 →ₐ[R] H.A 1) := by
    rw [kerIdeal, Ideal.map_le_iff_le_comap]
    intro c hc
    have hc' : counit (R := R) c = 0 := hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e : g.app 1 (f.app 1 c) = Hom.app (g ≫ f) 1 c := rfl
    change g.app 1 (f.app 1 c) = 0
    rw [e, hgf, prime_smul_id_app]
    have h1 := H.mulBy_pow_self 1 c
    rw [pow_one] at h1
    rw [h1, hc', map_zero]
  exact hle ha

end GlobalTheory.PDivGroup
end
