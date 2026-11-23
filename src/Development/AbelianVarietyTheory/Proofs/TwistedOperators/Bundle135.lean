module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle129
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle133
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
open scoped TensorProduct

namespace GlobalTheory.SegmentClass

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def rangeEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : ρ.Equiv f.range.toRepresentation :=
  .mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g =>
    LinearMap.ext fun v => Subtype.ext (by change f (ρ g v) = σ g (f v); rw [f.isIntertwining])

def subIncl {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Function.Injective (subIncl S) := Subtype.val_injective

theorem nonempty_equiv_of_eq {ρ : Representation ℂ G V} {S T : Subrepresentation ρ} (h : S = T) :
    Nonempty (S.toRepresentation.Equiv T.toRepresentation) := by
  subst h; exact ⟨.refl _⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cuspRep (Δ : Segment k) : IrrRep (GL (Fin Δ.d) k) := Δ.cusp.choose

theorem cuspRep_cl (Δ : Segment k) : (cuspRep Δ).cl = Δ.start := Δ.cusp.choose_spec.1

theorem cuspRep_isCuspidal (Δ : Segment k) : IsCuspidal (cuspRep Δ).ρ := Δ.cusp.choose_spec.2

theorem nonempty_prod_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) :
    Nonempty ((multiProd e (segTerm σ.ρ Δ.len)).Equiv
      (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (hσ.trans (cuspRep_cl Δ).symm)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
    (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).1 (piTensor (segTerm (cuspRep Δ).ρ Δ.len))
  exact ⟨(GlobalTheory.LocGL.multiProdEquiv e (π := segTerm σ.ρ Δ.len) (σ := segTerm (cuspRep Δ).ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _).trans ψ⟩

theorem nonempty_piTensor_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start) :
    Nonempty ((piTensor (segTerm (cuspRep Δ).ρ Δ.len)).Equiv (piTensor (segTerm σ.ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 ((cuspRep_cl Δ).trans hσ.symm)
  exact ⟨GlobalTheory.LocGL.piTensorEquiv (ρ := segTerm (cuspRep Δ).ρ Δ.len) (σ := segTerm σ.ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _⟩

section Published

variable (h : GlobalTheory.Published.SegmentRepresentation)
include h

def segSub (Δ : Segment k) :
    Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose

theorem segSub_spec (Δ : Segment k) :
    (segSub h Δ).toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)),
        S'.toRepresentation.IsIrreducible → S' = segSub h Δ) ∧
      Nonempty ((_root_.GlobalTheory.SmGL.jac (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segSub h Δ).toRepresentation).Equiv
        (piTensor (segTerm (cuspRep Δ).ρ Δ.len))) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose_spec

def segIrr (Δ : Segment k) : IrrRep (GL (Fin (Δ.len * Δ.d)) k) where
  V := (segSub h Δ).toSubmodule
  ρ := (segSub h Δ).toRepresentation
  smooth := IsSubquotient.isSmooth ⟨segSub h Δ, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  irr := (segSub_spec h Δ).1

theorem embeds_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    (∃ φ : π.ρ.IntertwiningMap (multiProd e (segTerm σ.ρ Δ.len)), Function.Injective φ) ↔
      Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  obtain ⟨Φ⟩ := nonempty_prod_equiv Δ σ hσ e
  constructor
  · rintro ⟨φ, hφ⟩
    let f := Φ.toIntertwiningMap.comp φ
    have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp hφ
    have hR : f.range.toRepresentation.IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (rangeEquiv f hf) π.irr
    obtain ⟨ψ⟩ := nonempty_equiv_of_eq ((segSub_spec h Δ).2.1 _ hR)
    exact ⟨(rangeEquiv f hf).trans ψ⟩
  · rintro ⟨ψ⟩
    exact ⟨Φ.symm.toIntertwiningMap.comp ((subIncl (segSub h Δ)).comp ψ.toIntertwiningMap),
      Φ.symm.toLinearEquiv.injective.comp ((subIncl_injective _).comp ψ.toLinearEquiv.injective)⟩

theorem jac_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    Nonempty ((_root_.GlobalTheory.SmGL.jac e π.ρ).Equiv (piTensor (segTerm σ.ρ Δ.len))) ↔ Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  constructor
  · rintro ⟨ψ⟩
    obtain ⟨f, hf⟩ := (Model.evalOne_bijective e π.smooth (piTensor (segTerm σ.ρ Δ.len))).2
      ψ.toIntertwiningMap
    refine (embeds_iff h Δ σ hσ e π).1 ⟨f, ?_⟩
    haveI := π.irr
    refine (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right fun h0 => ?_
    haveI : Nontrivial (⨂[ℂ] _ : Fin Δ.len, σ.V) :=
      GlobalTheory.ProdSupport.nontrivial_piTensor _ fun _ => Model.nontrivial_of_isIrreducible σ.irr
    obtain ⟨y, hy⟩ := exists_ne (0 : ⨂[ℂ] _ : Fin Δ.len, σ.V)
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (ψ.symm y)
    have h1 : ψ (Submodule.Quotient.mk v) = (f v).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk v)) hf).symm
    rw [h0, hv] at h1
    exact hy ((ψ.apply_symm_apply y).symm.trans h1)
  · rintro ⟨ψ⟩
    obtain ⟨A⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
      (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).2 (segSub h Δ).toRepresentation
    obtain ⟨B⟩ := (segSub_spec h Δ).2.2
    obtain ⟨C⟩ := nonempty_piTensor_equiv Δ σ hσ
    exact ⟨(Exponents.jacEquiv e ψ).trans (A.trans (B.trans C))⟩

theorem exists_isSegmentClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  intro k _ _ _ _
  refine ⟨fun Δ => (segIrr h Δ).cl, fun Δ σ hσ e π => ⟨?_, ?_⟩⟩
  · rw [IrrRep.cl_eq_iff]; exact (embeds_iff h Δ σ hσ e π).symm
  · rw [IrrRep.cl_eq_iff]; exact (jac_iff h Δ σ hσ e π).symm

end Published

end GlobalTheory.SegmentClass

theorem GlobalTheory.segmentClass_exists : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z :=
  fun h => GlobalTheory.SegmentClass.exists_isSegmentClass h

end
end

section

noncomputable section

open Classical

namespace GlobalTheory.LevelVecNorm

def locH {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP.1))) (PP : Formalism.L2.DIV.Pl E) :
    Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP)) :=
  if h : PP ∈ Pg then Hl ⟨PP, h⟩ else ⊤


open Classical in
def suppInd {k : Type} [CommRing k] (r : ℕ) {b a : ℕ} (H : Subgroup (GL (Fin r) k)) (z : Matrix (Fin b) (Fin a) k) : ℝ :=
  if Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z then 1 else 0

end GlobalTheory.LevelVecNorm

end
end

section

open MeasureTheory Formalism.IndefR

namespace GlobalTheory.ThetaIntegralLinear

theorem exists_isThetaP_of_integrable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by

  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν)
    ?_ ?_ ?_ ?_, hint, ?_⟩
  · intro f₁ f₂ e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    exact integral_add (hint f₁ e g) (hint f₂ e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e₁ e₂
    funext g
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    exact integral_add (hint f e₁ g) (hint f e₂ g)
  · intro c f e
    funext g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e g
    rfl

end GlobalTheory.ThetaIntegralLinear
end

section

open NumberField IsDedekindDomain Formalism.L2.Host

theorem _root_.GlobalTheory.T.exists_numberField_valuesIn_etaChar_halfTwist : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  first | exact @GlobalTheory.EtaValsNumberField.etaVals | exact GlobalTheory.EtaValsNumberField.etaVals | (intros; apply GlobalTheory.EtaValsNumberField.etaVals <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.exists_isometric_tensor_embedding_intertwining : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (πU : URep T) (v : D.HK.V), ‖D.ι v‖ = 1 → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : K →ₗᵢ[ℂ] πU.H), (∀ g y y', inner ℂ (j y) (πU.π g (j y')) = mcoef D v g * inner ℂ y y') → (∀ y, ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = j y) → ∃ Tm : D.U.H →L[ℂ] K →L[ℂ] πU.H, (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧ (∀ y, Tm (D.ι v) y = j y) ∧ (∀ g x y, πU.π g (Tm x y) = Tm (D.U.π g x) y) ∧ ∀ (R : πU.H →L[ℂ] πU.H) (S : K →L[ℂ] K), (∀ g z, R (πU.π g z) = πU.π g (R z)) → (∀ y, R (j y) = j (S y)) → ∀ x y, R (Tm x y) = Tm x (S y) := by
  first | exact @GlobalTheory.FockTensor.exists_tensor_embedding | exact GlobalTheory.FockTensor.exists_tensor_embedding | (intros; apply GlobalTheory.FockTensor.exists_tensor_embedding <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.exists_norm_eq_mul_of_finrank_hwSub_eq_one : ∀ (p q : ℕ) (M : GKMod p q) (Λ : Ix p q → ℚ) (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (E₁ : M.V →ₗ[ℂ] H₁) (E₂ : M.V →ₗ[ℂ] H₂), IrrGK M → Module.finrank ℂ ↥(hwSub M.act Λ) = 1 → Function.Injective E₁ → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₁ y) = inner ℂ (E₁ x) (E₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₂ (M.act Z x)) (E₂ y) = inner ℂ (E₂ x) (E₂ (M.act (adjZ Z) y))) → ∃ c : ℝ, ∀ y, ‖E₂ y‖ = c * ‖E₁ y‖ := by
  first | exact @GlobalTheory.FockTensor.norm_proportional_of_irreducible | exact GlobalTheory.FockTensor.norm_proportional_of_irreducible | (intros; apply GlobalTheory.FockTensor.norm_proportional_of_irreducible <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierInversion_zero_compactQuotient_summable : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ) → ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ = Φ 0 := by
  first | exact @GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero | exact GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero | (intros; apply GlobalTheory.SeparatingCharacters.tsum_coefficients_eq_value_zero <;> assumption)
end
