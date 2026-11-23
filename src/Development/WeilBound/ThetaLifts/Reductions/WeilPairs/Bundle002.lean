module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRealSpanEqConjFixedPrimeMulRelNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareOfApproximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.NumberTheory.NumberField.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end PositivityTheory.ThKW.LagrangianIntegralFactorisation

end
end

section

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.AutEtaA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ev


variable (F E) in
def ev (Q : HeightOneSpectrum (𝓞 E)) : AEF F E →+* Q.adicCompletion E :=
  ((evalV E Q).toRingHom.comp (GlobalTheory.LFun.finAdEquiv F E).toRingHom).comp (finPartF F E)

theorem ev_tmul (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : E) :
    ev F E Q (a ⊗ₜ[F] x) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) * algebraMap E _ x := rfl

theorem ev_inc (Q : HeightOneSpectrum (𝓞 E)) (x : E) : ev F E Q (incAF F E x) = algebraMap E _ x := by
  have : incAF F E x = (1 : AF F) ⊗ₜ[F] x := rfl
  rw [this, ev_tmul, map_one]
  erw [map_one, one_mul]

theorem ev_alg (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) :
    ev F E Q (algebraMap (AF F) (AEF F E) a) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, ev_tmul, map_one, mul_one]


variable (F E) in
def wv (Q : HeightOneSpectrum (𝓞 E)) : (AEF F E)ˣ →* WithZero (Multiplicative ℤ) :=
  ((Valued.v (R := Q.adicCompletion E)).toMonoidWithZeroHom.toMonoidHom.comp (ev F E Q).toMonoidHom).comp
    (Units.coeHom _)

theorem wv_apply (Q : HeightOneSpectrum (𝓞 E)) (y : (AEF F E)ˣ) : wv F E Q y = Valued.v (ev F E Q y) := rfl

theorem wv_inc (Q : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    wv F E Q (Units.map (incAF F E).toMonoidHom k) = Q.valuation E (k : E) := by
  rw [wv_apply]
  change Valued.v (ev F E Q (incAF F E (k : E))) = _
  rw [ev_inc]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : E)

theorem int_iff (y : AEF F E) : finPartF F E y ∈ intAEF F E ↔ ∀ Q, Valued.v (ev F E Q y) ≤ 1 :=
  GlobalTheory.LFun.mem_int_iff (finPartF F E y)

end Ev

section Fix

variable {σ : E →ₐ[F] E}


variable (σ) in
def Fx (Q : HeightOneSpectrum (𝓞 E)) : Prop := ∀ r ∈ Q.asIdeal, sgOF σ r ∈ Q.asIdeal

theorem sgOF_sgOF (h : IsCMExt F E σ) (x : 𝓞 E) : sgOF σ (sgOF σ x) = x :=
  RingOfIntegers.ext (GlobalTheory.SplitDetCharF.sig_invol h (x : E))

theorem sgOF_alg (a : 𝓞 F) : sgOF σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a :=
  RingOfIntegers.ext (σ.commutes (a : F))

theorem isSplit_of_not_fx (h : IsCMExt F E σ) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Fx σ Q) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (Q.under (𝓞 F)) := by
  have hne : Q.asIdeal.comap (sgOF σ) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    intro hb
    have : sgOF σ x ∈ Q.asIdeal.comap (sgOF σ) := by
      show sgOF σ (sgOF σ x) ∈ Q.asIdeal
      rw [sgOF_sgOF h]; exact hx
    rw [hb, Ideal.mem_bot] at this
    exact hx0 (by rw [← sgOF_sgOF h x, this, map_zero])
  let Q' : HeightOneSpectrum (𝓞 E) := ⟨Q.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, hne⟩
  refine GlobalTheory.LFun.isSplit_iff.2 ⟨Q', Q, fun e => hQ fun r hr => ?_, ?_, rfl⟩
  · have : r ∈ Q'.asIdeal := by rw [e]; exact hr
    exact this
  · refine HeightOneSpectrum.ext ?_
    show (Q.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext sgOF_alg

theorem isQuad (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) :
    GlobalTheory.QNorm.IsQuad (d : F) θ
      (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))) := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, map_eq_zero] at hθθ
    exact hd0 hθθ
  refine ⟨fun ⟨r, hr⟩ => ?_, by rw [pow_two, hθθ], hσθ, fun x => ?_⟩
  · have h1 : θ * θ = algebraMap F E r * algebraMap F E r := by rw [hθθ, hr, map_mul]
    rcases mul_self_eq_mul_self_iff.1 h1 with h2 | h2
    · have := hσθ
      rw [h2, AlgHom.commutes] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (h2.trans h3)
    · have := hσθ
      rw [h2, map_neg, AlgHom.commutes, neg_neg] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination -this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (by rw [h2, h3, neg_zero])
  · obtain ⟨u, w, e⟩ := hdec x
    exact ⟨u, w, by rw [e, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

theorem not_sq_of_fx (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Fx σ Q) : ¬ IsSquare (algebraMap F (Fv F (Q.under (𝓞 F))) (d : F)) := by
  let σe : E ≃ₐ[F] E :=
    AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (σe : E ≃+* E)
  have hs : ∀ x, ((s x : 𝓞 E) : E) = σe x := fun _ => rfl
  have hsg : ∀ x, s x = sgOF σ x := fun _ => rfl
  refine GlobalTheory.FixedPrimeNorm.not_isSquare_of_fixed (isQuad h hd0 hσθ hθθ hdec) s hs Q (le_antisymm ?_ ?_)
  · refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    show s r ∈ Q.asIdeal
    rw [hsg]; exact hQ r hr
  · intro x hx
    have : x = s (sgOF σ x) := by rw [hsg, sgOF_sgOF h]
    rw [this]
    exact Ideal.mem_map_of_mem _ (hQ x hx)

theorem sq_of_split (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) (d : F)) :=
  _root_.UpperTheory.Reformulated.B.SquareOfApproximation.main h hd0 hσθ hθθ hdec hv

end Fix

end PositivityTheory.ThKW.AutEtaA

end
end

section

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.Dbl

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
  {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

theorem topR_add (x y : WOF F E nS (nT + nT)) : topR (x + y) = topR x + topR y := rfl
theorem botR_add (x y : WOF F E nS (nT + nT)) : botR (x + y) = botR x + botR y := rfl

theorem continuous_topR : Continuous (topR : WOF F E nS (nT + nT) → WOF F E nS nT) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_botR : Continuous (botR : WOF F E nS (nT + nT) → WOF F E nS nT) :=
  continuous_id.matrix_submatrix _ _

theorem hOF_dbl (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (botR x) (botR y) := by
  simp only [hOF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_sub_distrib]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => ?_ <;>
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] <;>
    simp only [dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, topR, botR,
      Function.comp_apply, id] <;> simp [dbl]

theorem symplOF_dbl (x y : WOF F E nS (nT + nT)) :
    symplOF σ JS (dblG JT) ξ₀ x y = symplOF σ JS JT ξ₀ (topR x) (topR y) - symplOF σ JS JT ξ₀ (botR x) (botR y) := by
  simp only [symplOF, hOF_dbl, mul_sub, map_sub]

theorem symplOHF_dbl (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y = symplOHF σ JS JT ξ₀ (topR x) (topR y) - symplOHF σ JS JT ξ₀ (botR x) (botR y) := by
  simp only [symplOHF, symplOF_dbl, mul_sub]

theorem symplOHF_neg_neg (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ (-x) (-y) = symplOHF σ JS JT ξ₀ x y := by
  simp [symplOHF, symplOF, hOF]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ t)]

theorem heis_delta {ψ : AddChar (AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (w : WOF F E nS (nT + nT))
    (f₁ f₂ : WOF F E nS nT → ℂ) :
    heisOF σ JS (dblG JT) ξ₀ ψ w (deltaT f₁ f₂) =
      deltaT (heisOF σ JS JT ξ₀ ψ (topR w) f₁) (heisOF σ JS JT ξ₀ ψ (-botR w) f₂) := by
  funext x
  simp only [heisOF, deltaT_apply, symplOHF_dbl, symplOHF_neg_neg, map_mul, conj_psi hψ, topR_add, botR_add, neg_add,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem theta_delta {ψ : AddChar (AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {f₁ f₂ : WOF F E nS nT → ℂ}
    (h₁ : IsThetaFunOF σ JS JT ξ₀ ψ f₁) (h₂ : IsThetaFunOF σ JS JT ξ₀ ψ f₂) :
    IsThetaFunOF σ JS (dblG JT) ξ₀ ψ (deltaT f₁ f₂) := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let tA : WOF F E nS (nT + nT) →+ WOF F E nS nT := ⟨⟨topR, rfl⟩, fun _ _ => rfl⟩
  let bA : WOF F E nS (nT + nT) →+ WOF F E nS nT := -⟨⟨botR, rfl⟩, fun _ _ => rfl⟩
  have htA : Continuous tA := continuous_topR
  have hbA : Continuous bA := continuous_botR.neg
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e1 : topR (ratWF (F := F) γ) = ratWF (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
    have e2 : -botR (ratWF (F := F) γ) = ratWF (-γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := by
      ext i j; simp [ratWF, botR]
    simp only [deltaT_apply, topR_add, botR_add, neg_add, symplOHF_dbl]
    rw [← symplOHF_neg_neg (botR _), e1, e2, h₁.quasi, h₂.quasi, map_mul, conj_psi hψ, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, hf₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, hf₂⟩ := h₂.level
    refine ⟨U₁.comap tA ⊓ U₂.comap bA, (hU₁.preimage htA).inter (hU₂.preimage hbA), fun u hu h0 => ?_⟩
    rw [heis_delta hψ, hf₁ (topR u) hu.1, hf₂ (-botR u) hu.2]
    · ext i j
      have := congrFun (congrFun h0 (finSumFinEquiv (Sum.inr i))) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      show infPartF F E (-(u (finSumFinEquiv (Sum.inr i)) j)) = 0
      rw [map_neg, show infPartF F E (u (finSumFinEquiv (Sum.inr i)) j) = 0 from this, neg_zero]
    · ext i j
      exact congrFun (congrFun h0 (finSumFinEquiv (Sum.inl i))) j
  · exact (h₁.cont.comp htA).mul (Complex.continuous_conj.comp (h₂.cont.comp hbA))
  · have a1 := h₁.smooth k (tA.comp L) (htA.comp hL) (fun t => by
      ext i j
      exact congrFun (congrFun (h0 t) (finSumFinEquiv (Sum.inl i))) j) (topR w)
    have a2 := h₂.smooth k (bA.comp L) (hbA.comp hL) (fun t => by
      ext i j
      have := congrFun (congrFun (h0 t) (finSumFinEquiv (Sum.inr i))) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      show finPartF F E (-(L t (finSumFinEquiv (Sum.inr i)) j)) = 0
      rw [map_neg, this, neg_zero]) (-botR w)
    have a3 := a1.mul (Complex.conjCLE.contDiff.comp a2)
    refine (show (fun t => deltaT f₁ f₂ (w + L t)) = _ from funext fun t => ?_) ▸ a3
    simp only [deltaT_apply, topR_add, botR_add, neg_add]
    rfl

end PositivityTheory.ThKW.Dbl
end
end

section

open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

section aux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hOF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (a b : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) (dC F E nT * a) (dC F E nT * b) = 0 := by
  have ha : dC F E nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq a
  have hb : dC F E nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    GlobalTheory.LagrThetaInv.dC_mul_eq b
  rw [ha, hb]
  unfold hOF
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem symplOHF_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (a b : WOF F E nS nT) :
    symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC F E nT * a) (dC F E nT * b) = 0 := by
  simp only [symplOHF, symplOF, hOF_dC, mul_zero, map_zero]

theorem dC_mul_ratWF {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    (dC F E nT * (ratWF γ : WOF F E nS nT) : WOF F E nS (nT + nT)) = ratWF (GlobalTheory.LagrThetaInv.dC E nT * γ) :=
  GlobalTheory.LagrThetaInv.dC_mul_rat γ

theorem setIntegral_add_right {nS nT : ℕ} (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    [ν.IsAddHaarMeasure] (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (g : WOF F E nS nT → ℂ)
    (h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v) (u : WOF F E nS nT) :
    ∫ v in 𝓕, g (v + u) ∂ν = ∫ v in 𝓕, g v ∂ν := by
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2

end aux

theorem lagrInt_heis_dC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f → ∀ v : WOF F E nS nT,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT)
                     (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * v) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ ν 𝓕 _ h𝓕 f hf u
  set g : WOF F E nS nT → ℂ := fun v => f (dC F E nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC F E nT * u) f
      (dC F E nT * v) = g (v + u) := by
    intro v
    simp only [hg, heisOF]
    rw [symplOHF_dC, AddChar.map_zero_eq_one, one_mul, Matrix.mul_add]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    show f (dC F E nT * ((ratWF γ : WOF F E nS nT) + v)) = f (dC F E nT * v)
    have hq := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * v)
    rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at hq
    rw [Matrix.mul_add, hq]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  exact setIntegral_add_right ν 𝓕 h𝓕 g h2 u

end GlobalTheory.SplitLagrF

end
end
