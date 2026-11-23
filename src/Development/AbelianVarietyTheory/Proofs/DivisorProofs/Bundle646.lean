module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle602
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle553
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle605
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem restrict_pull2_bijective_of_basis (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (C' : Type) [Category.{0} C'] [Quiver.IsThin C'] (G : C' ⥤ AffOp X)
    (h1 : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : C', x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U)
    (h2 : ∀ (t₁ t₂ : C') (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 →
      x ∈ (G.obj t₂).unop.1 → ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧
        x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U) :
    Function.Bijective (CoefMap.restrict (OAff s) G).pull2 := by
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let B : Set Γ(X, T.unop.1) :=
      {f | ∃ t : C', X.basicOpen f ≤ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ T.unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t, hxt, htT⟩ := h1 x T.unop.1 hx
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := (G.obj t).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨t, hf, htT⟩⟩, hxf⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, T.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S u hu
      obtain ⟨t, hft, htT⟩ := hFB (F.equivFin.symm i).2
      set f : Γ(X, T.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op f) at hu
      have hSf : S.unop.1 ≤ X.basicOpen f := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      refine ⟨t, (homOfLE (show (G.obj t).unop ≤ T.unop from htT)).op,
        (homOfLE (show S.unop ≤ (G.obj t).unop from hSf.trans hft)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : C') (S : AffOp X), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS : IsAffineOpen S.unop.1 := S.unop.2
    have hS₁ : S.unop.1 ≤ (G.obj t₁).unop.1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G.obj t₂).unop.1 := leOfHom a₂.unop
    let B : Set Γ(X, S.unop.1) :=
      {g | ∃ t₃ : C', Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ X.basicOpen g ≤ (G.obj t₃).unop.1}
    have hB : Ideal.span B = ⊤ := by
      rw [← hS.self_le_iSup_basicOpen_iff]
      intro x hx
      obtain ⟨t₃, e₁, e₂, hxt, -⟩ := h2 t₁ t₂ x S.unop.1 hx (hS₁ hx) (hS₂ hx)
      obtain ⟨g, hg, hxg⟩ := hS.exists_basicOpen_le (V := (G.obj t₃).unop.1) ⟨x, hxt⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ⟨t₃, e₁, e₂, hg⟩⟩, hxg⟩
    obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hB
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hsp : Ideal.span (Set.range fun i ↦ ((F.equivFin.symm i).1 : Γ(X, S.unop.1))) = ⊤ := by
        rw [eq_top_iff, ← hF]
        exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩
      exact hsp
    · intro i S' u hu
      obtain ⟨t₃, e₁, e₂, hgt⟩ := hFB (F.equivFin.symm i).2
      set g : Γ(X, S.unop.1) := (F.equivFin.symm i).1
      change IsUnit (X.presheaf.map (homOfLE (show S'.unop.1 ≤ S.unop.1 from leOfHom u.unop)).op g) at hu
      have hS'g : S'.unop.1 ≤ X.basicOpen g := by
        have := Scheme.basicOpen_of_isUnit X hu
        rw [Scheme.basicOpen_res] at this
        rw [← this]; exact inf_le_right
      exact ⟨t₃, e₁, e₂, ⟨(homOfLE (show S'.unop ≤ (G.obj t₃).unop from hS'g.trans hgt)).op⟩⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) G H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) G H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) G H hcov hdir
  exact ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩

end GlobalTheory.AbCoh
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.mayerVietoris_equivalence_of_cover : GlobalTheory.EtC.A4 := by
  first | (exact @GlobalTheory.MayerVietorisEqv.a4) | (exact GlobalTheory.MayerVietorisEqv.a4) | (intros; apply GlobalTheory.MayerVietorisEqv.a4  <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ : Type) (h : MvPowerSeries σ B), constantCoeff h = 1 → (∀ α, coeff α (h - 1) ∈ J) → In J (formalLog (map (algebraMap B Q) h)) := by
  first | exact @GlobalTheory.DPLog.formalLog_in_of_sub_one_mem | exact GlobalTheory.DPLog.formalLog_in_of_sub_one_mem | (intros; apply GlobalTheory.DPLog.formalLog_in_of_sub_one_mem <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct


theorem _root_.GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) ∈ m := by
  intro p O _ G d c n m hp u φ hφ ψ H
  have hCoeff (T : MvPowerSeries (Fin d ⊕ Fin d) O) (i : Fin d) (α : Fin d →₀ ℕ) :
      coeff α (atZero (pderiv (R := O) (Sum.inr i) T)) =
        coeff (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) T := by
    rw [atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    simp
  have hMonomial (α β : Fin d →₀ ℕ) (i : Fin d) :
      atZero (pderiv (R := O) (Sum.inr i) (monomial (α.sumElim β) (1 : O))) =
        lin (monomial β (1 : O)) i • monomial α (1 : O) := by
    classical
    ext γ
    rw [hCoeff, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]
    have hγ : γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 =
        γ.sumElim (Finsupp.single i 1) := by
      rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]
    rw [hγ]
    have h : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔
        γ = α ∧ Finsupp.single i 1 = β := by
      constructor
      · intro h
        exact ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
          Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [h]
    by_cases hα : γ = α <;> by_cases hβ : Finsupp.single i 1 = β <;> simp [hα, hβ]
  obtain ⟨N₁, h₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, h₂⟩ := (c.isEval₂ n).2 1
  have hs : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)
  let D : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] MvPowerSeries (Fin d) O :=
    ∑ i, u i • ((substAlgHom hs).toLinearMap ∘ₗ (pderiv (R := O) (Sum.inr i)).toLinearMap)
  have hD : ∀ H, D H = ∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H) := fun H => by
    simp [D, atZero, LinearMap.sum_apply, coe_substAlgHom]
  let P : G.A n ⊗[O] G.A n →ₗ[O] O := LinearMap.mul' O O ∘ₗ TensorProduct.map ψ φ.ofConv
  let L : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] O :=
    P ∘ₗ (c.ev₂ n).toLinearMap - ψ ∘ₗ (c.ev n).toLinearMap ∘ₗ D
  have hL : ∀ H, L H = P (c.ev₂ n H) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) :=
    fun H => by rw [← hD]; rfl
  have key := GlobalTheory.PairingEv.mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H
  · rw [Submodule.mem_comap, hL] at key
    exact key
  · intro γ
    rw [Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]
    generalize Finsupp.comapDomain Sum.inl γ _ = α
    generalize Finsupp.comapDomain Sum.inr γ _ = β
    rw [GlobalTheory.PairingEv.chart_ev₂_monomial]
    simp only [hMonomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]
    have := m.mul_mem_left (ψ (c.ev n (monomial α 1))) (hφ (monomial β 1))
    convert this using 1
    have e : P (c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1)) =
        ψ (c.ev n (monomial α 1)) * φ (c.ev n (monomial β 1)) := by
      simp only [P, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [e]; ring
  · intro T hT
    rw [Submodule.mem_comap, hL]
    obtain ⟨a, ha⟩ := h₂ T fun α hα => hT α (by omega)
    obtain ⟨b, hb⟩ := h₁ (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) T)) fun α hα => by

      rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, hCoeff, hT, smul_zero]
      rw [map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single]
      omega
    rw [ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul]
    exact m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariantDerivation_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), In N (cob1 (up Q μ) l) → lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((invDer (up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  first | exact @GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem | exact GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem | (intros; apply GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

open TensorProduct WithConv Coalgebra

namespace GlobalTheory.NMul

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

end GlobalTheory.NMul

namespace GlobalTheory.NMul

theorem ev_nmul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n k : ℕ) (i : Fin d),
      c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)
  have hsucc : ∀ (k : ℕ) (j : Fin d), nmul c.μ (k + 1) j =
      subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ j) := by
    intro k j
    simp only [nmul, Function.iterate_succ_apply']
    rfl
  have hmul : ∀ (j : ℕ) (a : G.A n),
      PDiv.mulBy O (G.A n) j a = (toConv (AlgHom.id O (G.A n)) ^ j).ofConv a := fun j a =>
    DFunLike.congr_fun (PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) j) a
  induction k with
  | zero =>
    intro i
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    have hu : ∀ s, constantCoeff
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s) = 0 := by
      have hc : ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul c.μ k j) = 0 := by
        intro k
        induction k with
        | zero => intro j; rfl
        | succ k ihk =>
          intro j
          rw [hsucc]
          refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_
            (c.isLaw.const j) <;>
          · rintro (l | l)
            · simpa using ihk l
            · simp
      rintro (l | l)
      · simpa using hc k l
      · simp
    let ψ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n :=
      (Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _).comp (c.ev₂ n)
    have hψ : IsEval p (fun s => c.ev n
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s)) ψ := by
      constructor
      · rintro (l | l)
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl l), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one, ih]
          rfl
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr l), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 l]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        obtain ⟨y, hy⟩ := hN f hf
        refine ⟨(Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
          (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _) y, ?_⟩
        simp only [ψ, AlgHom.comp_apply, hy, map_mul, map_pow, map_natCast]
    rw [hsucc, hT.1 _ _ ψ hu hψ (c.μ i)]
    simp only [ψ, AlgHom.comp_apply, c.comul n i]
    rw [hmul (k + 1), pow_succ, AlgHom.convMul_apply]
    have e : (toConv (AlgHom.id O (G.A n)) ^ k).ofConv =
        (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) := by
      ext a; exact (hmul k a).symm
    simp only [e]

end GlobalTheory.NMul
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ}

theorem res_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    G.res n (c.ev (n + 1) f) = c.ev n f := by
  haveI : IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval (n + 1)) (G.res n : G.A (n + 1) →ₐ[O] G.A n)
  have h' : IsEval p (c.x n) ((G.res n : G.A (n + 1) →ₐ[O] G.A n).comp (c.ev (n + 1))) := by
    convert h using 2 with i
    exact (c.res n i).symm
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] G.A n => E f)
    (GlobalTheory.CEval.eval_unique p (c.x n) _ _ h' (c.isEval n))

theorem counit_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f := by
  let E₂ : MvPowerSeries (Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d) O →+* O) with
      commutes' := fun r => by
        show constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r) = r
        rw [← c_eq_algebraMap]; simp }
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval n) (Bialgebra.counitAlgHom O (G.A n))
  have h₁ : IsEval p (fun _ : Fin d => (0 : O))
      ((Bialgebra.counitAlgHom O (G.A n)).comp (c.ev n)) := by
    convert h using 2 with i
    exact (c.aug n i).symm
  have h₂ : IsEval p (fun _ : Fin d => (0 : O)) E₂ := by
    refine ⟨fun i => by simp [E₂], fun m => ⟨1, fun g hg => ?_⟩⟩
    have : constantCoeff g = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hg 0 (by simp)
    show (p : O) ^ m ∣ constantCoeff g
    rw [this]
    exact dvd_zero _
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] O => E f)
    (GlobalTheory.CEval.eval_unique p (fun _ => (0 : O)) _ _ h₁ h₂)

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog

theorem exists_charSeries : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate), ∃ u : MvPowerSeries (Fin d) O, constantCoeff u = 1 ∧ ∀ n, c.ev n u = charElem χ n := by
  intro p _ O _ _ _ G d c χ
  haveI : ∀ n, IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) := fun n =>
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  obtain ⟨u, hu⟩ := (GlobalTheory.Limits.exists_unique_of_compatible p O (Fin d) G.A
    (fun n => (G.res n : G.A (n + 1) →ₐ[O] G.A n)) c.x c.ev c.isEval
    (fun n f => c.res_ev n f) c.ker).2 c.surj (charElem χ) (fun n => res_charElem χ n)
  refine ⟨u, ?_, hu⟩
  rw [← c.counit_ev 0 u, hu 0]
  exact (isGroupLikeElem_charElem χ 0).counit_eq_one

end GlobalTheory.QLog
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst_poly : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ g : MvPolynomial τ Q, HasVal p z (subst (up Q u) (g : MvPowerSeries τ Q)) (MvPolynomial.eval (fun j => algebraMap B Q (E (u j))) g) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u hu g
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  induction g using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [MvPolynomial.coe_monomial, subst_monomial ha, MvPolynomial.eval_monomial]
    have hprod : α.prod (fun s n => (up Q u s) ^ n) = map (algebraMap B Q) (α.prod fun s n => (u s) ^ n) := by
      simp [up, Finsupp.prod, map_prod, map_pow]
    have hEp : E (α.prod fun s n => (u s) ^ n) = α.prod fun s n => (E (u s)) ^ n := by
      simp [Finsupp.prod, map_prod, map_pow]
    have hv := GlobalTheory.T.hasPAdicPowerSeriesValue_map_of_continuousEvaluation p B O Q θ hF σ z hz E hE (α.prod fun s n => (u s) ^ n)
    have hs := (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ 0 _ 0 hv).2.1 c
    rw [hprod]
    convert hs using 1
    · rw [MvPowerSeries.smul_eq_C_mul]; rfl
    · rw [hEp]; simp [Finsupp.prod, map_prod, map_pow]
  | add f g hf hg =>
    rw [MvPolynomial.coe_add, subst_add ha, map_add (f := _)]
    exact (GlobalTheory.T.hasPAdicPowerSeriesValue_add_smul_map p B O Q θ hF σ z _ _ _ _ hf).1 hg

end GlobalTheory.QLog
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.eq_zero_of_lin_zero_cob1_zero : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E, lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  first | exact @GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions | exact GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions | (intros; apply GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_formalGroupLawLift_of_surjective : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  first | exact @GlobalTheory.LiftLaw.exists_isLift | exact GlobalTheory.LiftLaw.exists_isLift | (intros; apply GlobalTheory.LiftLaw.exists_isLift <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.formalChart_presents_levels_mod_ideal : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i), (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n) (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧ Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  first | exact @GlobalTheory.QLog.Chart.presents_quotient | exact GlobalTheory.QLog.Chart.presents_quotient | (intros; apply GlobalTheory.QLog.Chart.presents_quotient <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  first | exact @GlobalTheory.QLogDefect.constantCoeff_defect | exact GlobalTheory.QLogDefect.constantCoeff_defect | (intros; apply GlobalTheory.QLogDefect.constantCoeff_defect <;> assumption)
end
