module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle444
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEval
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle431
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle025
public import Formalism.LocalToGlobal.Divisibility.TupUsed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.LiftCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.RealWeil GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem actO_inv_cancel {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  have a : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have b : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, a, Matrix.one_mul, Matrix.mul_assoc, b, Matrix.mul_one]

theorem eq_smul_of_inv_mul {G H M : Type} [Group G] [Group H] [AddCommGroup M] [Module ℂ M]
    (om : G × H →* Module.End ℂ M) (A : Module.End ℂ M) (g : G) (k : H) {c : ℂ} (hc : c ≠ 0) (f : M)
    (e : (om (g⁻¹, k⁻¹) * A) f = c • f) : om (g, k) f = c⁻¹ • A f := by
  have e := congrArg (om (g, k)) e
  rw [← Module.End.mul_apply, ← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel,
    Prod.mk_one_one, map_one, one_mul, map_smul] at e
  rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem weil_eq_smul_osc : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ Ω : GA D S × GA D T → GlobalTheory.RealWeil.BB ψ S T → GlobalTheory.RealWeil.BB ψ S T, GlobalTheory.RealWeil.IsOsc (GlobalTheory.RealWeil.rhoV hψ σ S T) (fun p v => GlobalTheory.RealWeil.mM θ S T p *ᵥ v) Ω → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → om (g, h) F.1 = c • ((Ω (g, h) F).1 : WO S T → ℂ) := by
  intro D θ σ h ψ hψ S T om hw Ω hΩ g hg k hk
  unfold IsOsc at hΩ
  obtain ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩ := hΩ
  have hθ := h.inf
  have sm := sm_of_theta (S := S) (T := T) h hψ
  have hfin : ∀ p {u : WO S T}, u.map (infPart D) = 0 → ∀ F, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) F →
      Ω p (rhoB hψ u F) = rhoB hψ u (Ω p F) := fun p u hu F hF => hcomm p _ (rhoB_comm h hψ hu) F hF
  have hth : ∀ p F, IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (Ω p F).1 := by
    intro p F hF
    obtain ⟨U, hU, hl⟩ := hF.level
    refine theta_of_sm h hψ _ (hsm p F (sm F hF)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoB hψ u F = F := QB_ext fun x => by rw [coe_rhoB, hl u hu h0]
    rw [← coe_rhoB hψ, ← hfin p h0 F (sm F hF), e]
  obtain ⟨om', hom⟩ := exists_hom hψ Ω hth (fun p F F' h1 h2 => hadd p F F' (sm F h1) (sm F' h2))
    (fun p a F h1 => hsmul p a F (sm F h1)) (fun F h1 => hone F (sm F h1)) fun p p' F h1 => hmul p p' F (sm F h1)
  have lift : ∀ f, IsThetaFunO ψ S T f → ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f :=
    fun f hf => ⟨toB hψ f hf, coe_toB hψ f hf⟩
  have pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om' p f) := by
    intro p f hf
    obtain ⟨F, rfl⟩ := lift f hf
    rw [hom p F hf]
    exact hth p F hf
  have Heisenberg₂ : ∀ w f, IsThetaFunO ψ S T f →
      om' (g, k) (heisO ψ S T w f) = heisO ψ S T (actO S T g k w) (om' (g, k) f) := by
    intro w f hf
    obtain ⟨F, rfl⟩ := lift f hf
    obtain ⟨u, v, hu, rfl⟩ := exists_parts h w
    have h1 : IsThetaFunO ψ S T (rhoV hψ σ S T v F).1 := by
      rw [coe_rhoV]
      exact theta_heisO_real hθ hψ (real_iotaV h v) hf
    have h2 : IsThetaFunO ψ S T (rhoB hψ u (rhoV hψ σ S T v F)).1 := by
      rw [coe_rhoB]
      exact GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h1 hu
    have e1 : actO S T g k (u + iotaV σ S T v) = u + iotaV σ S T (mM θ S T (g, k) *ᵥ v) := by
      rw [GlobalTheory.WeilVacMove.actO_add, actO_fin h hg hk hu, actO_iotaV h]
    rw [hom _ F hf, e1, ← coe_rhoB hψ _ F, ← coe_rhoB hψ _ (Ω (g, k) F), rhoB_add h hψ hu v F,
      rhoB_add h hψ hu _ (Ω (g, k) F), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm F hf)]
  obtain ⟨c, hc, hM⟩ := GlobalTheory.T.schur_lemma_thetaFunctions_from_matrixCoefficients D ψ hψ S T (om (g⁻¹, k⁻¹) * om' (g, k))
    (fun f hf => hw.om_pres _ _ (pres _ f hf))
    (fun w f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, Heisenberg₂ w f hf, hw.om_heis _ _ _ _ (pres _ f hf),
        actO_inv_cancel])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hw.om_unit μ 𝓕 hμ h𝓕 _ _ (pres _ f hf)]
      obtain ⟨F, rfl⟩ := lift f hf
      rw [hom _ F hf]
      exact lintegral_eq_of_norms hψ μ 𝓕 hμ h𝓕 fun H _ _ _ Φ hΦ =>
        hunit H Φ (fun v => hΦ _) _ F (sm F hf))
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun F hF => ?_⟩
  rw [← hom _ F hF]
  exact eq_smul_of_inv_mul om _ g k hc0 _ (hM F.1 hF)

end GlobalTheory.Mem.LiftCmp

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AtMember



theorem conj_gen_mem_frame : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  intro B f T w Z t k
  have hpi : (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG := by
    have h5 : (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = (t.C.herm.levelZeroCompatibility (w.D Z).u₀).piG :=
      congrArg (fun X : Formalism.L2.Herm.ColsHermS (w.D Z) => (X.levelZeroCompatibility (w.D Z).u₀).piG) t.full.2
    exact h5.trans ((t.C.piG (w.D Z).u₀).symm.trans (t.std (w.D Z).u₀).gl.piG)
  show barE (w.D Z) ((Formalism.L2.Herm.toErrXS t.full.1).piG k) ∈
    Ideal.map (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)) ((Fr.at (w.st Z) f).P.pb k).asIdeal
  rw [hpi]
  have hP : (Fr.at (w.st Z) f).P = w.I.C.P := by rw [w.C_eq]; rfl
  rw [hP]
  have hdiv := w.ok.pibar k
  set π : 𝓞 (w.D Z).host.E := w.px.piG k with hπdef
  set b : 𝓞 (w.D Z).host.E := barE (w.D Z) π with hbdef
  have hbc : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) = (w.D Z).host.conj (π : (w.D Z).host.E) := barE_eq_conj _ _
  have hprod : π * b = (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) := by
    apply RingOfIntegers.ext
    show ((π : (w.D Z).host.E) * (b : (w.D Z).host.E)) = algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E)
    rw [map_natCast, hbc]
    exact w.px.piG_norm k
  have hg0 : (((w.D Z).host.g k : ℕ) : 𝓞 (w.D Z).host.E) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact ((w.D Z).host.g_prime k).ne_zero h'
  have hπ0 : π ≠ 0 := fun h => hg0 (by rw [← hprod, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hg0 (by rw [← hprod, h, mul_zero])
  have hbK : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ∈ (w.D Z).host.K := by
    have hπE : ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) ≠ 0 := fun h => hπ0 (RingOfIntegers.ext (h.trans (map_zero (algebraMap (𝓞 (w.D Z).host.E) (w.D Z).host.E)).symm))
    have e : ((b : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) =
        ((w.D Z).host.g k : (w.D Z).host.E) / ((π : 𝓞 (w.D Z).host.E) : (w.D Z).host.E) := by
      rw [eq_div_iff hπE, mul_comm, hbc]
      exact w.px.piG_norm k
    rw [e]
    exact div_mem (natCast_mem _ _) (w.px.piG_K k)
  set y : 𝓞 (w.D Z).host.K := toOK b hbK with hydef
  have hy : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y = b := algebraMap_toOK b hbK
  rw [← hy]
  apply Ideal.mem_map_of_mem

  have iI : Algebra.IsIntegral (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hPk : ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)).IsPrime := (w.I.C.P.pb k).isPrime
  obtain ⟨Q, -, hQp, hQ⟩ := @Ideal.exists_ideal_over_prime_of_isIntegral (𝓞 (w.D Z).host.K) _ (𝓞 (w.D Z).host.E) _
    (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)).toAlgebra iI
    ((w.I.C.P.pb k).asIdeal : Ideal (𝓞 (w.D Z).host.K)) hPk ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have : x = 0 := FaithfulSMul.algebraMap_injective (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) (hx.trans (map_zero _).symm)
      rw [this]; exact Ideal.zero_mem _)
  have hgQ : π * b ∈ Q := by
    rw [hprod, ← map_natCast (algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E)), ← Ideal.mem_comap]
    change _ ∈ Ideal.under (𝓞 (w.D Z).host.K) Q
    rw [hQ]
    exact w.I.C.P.pb_over k
  rcases hQp.mem_or_mem hgQ with hπQ | hbQ
  ·
    have hQ'p : (Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E)).IsPrime := Ideal.comap_isPrime _ _
    have hbQ' : b ∈ Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E) := by
      rw [Ideal.mem_comap]
      show barE (w.D Z) (barE (w.D Z) π) ∈ Q
      rw [barE_barE]; exact hπQ
    let Q' : HeightOneSpectrum (𝓞 (w.D Z).host.E) :=
      ⟨Q.comap (barE (w.D Z) : 𝓞 (w.D Z).host.E →+* 𝓞 (w.D Z).host.E), hQ'p, fun h => hb0 (by rw [h] at hbQ'; exact (Ideal.mem_bot).1 hbQ')⟩
    have hmem : Q' ∈ (B.primes w.px).vG k := (Formalism.L2.Col.mem_divs hb0 Q').2 hbQ'
    have hd := (hdiv Q').1 hmem
    have hu : y ∈ (HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q').asIdeal := by
      show algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q'.asIdeal
      rw [hy]; exact hbQ'
    have hd' : HeightOneSpectrum.under (𝓞 (w.D Z).host.K) Q' = w.I.C.P.pb k := hd
    rw [hd'] at hu
    exact hu
  · rw [← hQ]
    have h' : algebraMap (𝓞 (w.D Z).host.K) (𝓞 (w.D Z).host.E) y ∈ Q := hy.symm ▸ hbQ
    exact h'

end GlobalTheory.AtMember
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_localizedWeylLattice_iff_detTwisted_eval : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  first | exact @GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | exact GlobalTheory.Mem.LocDictT.mem_locW_iff_delW | (intros; apply GlobalTheory.Mem.LocDictT.mem_locW_iff_delW <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  first | exact @GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | exact GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | (intros; apply GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem SecondG.sAnd_of_largeBase : ∀ (KP : GroupRetwisting.BaseP) (Q Q' R : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.LargeBaseConditionG KP Q R → GroupRetwisting.SecondG KP Q Q' →
    GroupRetwisting.SecondG KP Q (sAnd Q' R) := by
  intro KP Q Q' R hK hR hS
  refine (EvG.inter hR hS).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨S₁r, P₁r, Ar, S₂r, r1, r2, hr⟩, ⟨S₁s, P₁s, As, S₂s, s1, s2, hs⟩⟩ := H
  refine ⟨fun P g F => S₁s P g F ∪ S₁r P g F, fun P g F F₀ => P₁s P g F F₀ ∪ P₁r P g F F₀, As, S₂s, ?_, s2, ?_⟩
  · intro P g F z hz
    rcases Finset.mem_union.1 hz with h | h
    exacts [s1 _ _ _ z h, r1 _ _ _ z h]
  · intro B f T hO hH hP hA hKP hT C W V S N G c hQ hX A S₂ hS₂
    have hH' : Has₂ B (S₁s B.toPre f B.KsC) (S₂s B.toPre f B.KsC B.fixedCoefficientFieldInComplex (T.set f)) :=
      ⟨fun z hz => hH.1 z (Finset.mem_union_left _ hz), hH.2⟩
    obtain ⟨B', f', T', hEnl, hf', hpl, hAv, hS', C', W', V', S', N', G', c', hQ', hTw, hQ''⟩ :=
      hs B f T hO hH' (fun x hx => hP (Finset.mem_union_left _ hx)) hA hKP hT C W V S N G c hQ hX
        (fun l => A l ∪ Ar B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂r P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
        (by
          intro P g Ξ z hz
          rcases Finset.mem_union.1 hz with h | h
          exacts [hS₂ _ _ _ z h, r2 _ _ _ _ _ z h])
    have hP' : B'.toPre = B.toPre := hEnl.1
    have cf : ∀ {α : Type} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {x : Fr P} {y : Fr P'}, P = P' → HEq x y → g P x = g P' y := by
      intro α g P P' x y h hxy
      subst h
      rw [eq_of_heq hxy]
    have hk : B'.KsC = B.KsC := hEnl.KsC_eq
    have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := hEnl.fixedCoefficientField_eq
    have hRc : R K ⟨B', C', W', V', S', N', G'⟩ f' T' c' :=
      hr B' f' T' (hP' ▸ hO)
        ⟨by rw [hk, hl, cf S₁r hP' hf']; exact fun z hz => hH.1 z (Finset.mem_union_right _ hz),
          by rw [hk, hl]; exact fun z hz => hS' z (Finset.mem_union_right _ hz)⟩
        (by rw [hk, hl, cf P₁r hP' hf', hpl]; exact fun x hx => hP (Finset.mem_union_right _ hx))
        (by
          rw [hk, hl, cf Ar hP' hf']
          exact fun w v hv h => hAv w v hv (Finset.mem_union_right _ h))
        (hK.enl B B' f f' hEnl hf' hKP) C' W' V' S' N' G' c' hQ'
    exact ⟨B', f', T', hEnl, hf', hpl, fun w v hv h => hAv w v hv (Finset.mem_union_left _ h),
      fun z hz => hS' z (Finset.mem_union_left _ hz), C', W', V', S', N', G', c', hQ', hTw, hQ'', hRc⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.existsLayeredData_of_goodScaleContexts : StandardLattice.SiegelMassRatioCM → ∀ (Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop), RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) → (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) → RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) := by
  first | exact @GlobalTheory.Fc.recExP_of_recAtG | exact GlobalTheory.Fc.recExP_of_recAtG | (intros; apply GlobalTheory.Fc.recExP_of_recAtG <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def CrdOver {L L' : Type} [Field L] [Field L'] (ι : L →+* L') {n n' : ℕ} (x : Fin n → L) (x' : Fin n' → L') : Prop :=
  n = n' ∧ ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = ι (x k)



def RSideW (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  HEq R'.ψ z.R.ψ ∧ HEq R'.θ z.R.θ ∧ HEq R'.βW z.R.βW ∧ HEq R'.βY z.R.βY ∧ HEq R'.ΛY z.R.ΛY ∧ HEq R'.nW z.R.nW ∧ HEq R'.βV z.R.βV ∧
  HEq R'.ΛV z.R.ΛV ∧ HEq R'.ΛW z.R.ΛW ∧ HEq R'.Pg z.R.Pg ∧ HEq R'.eG z.R.eG ∧ HEq R'.Sb z.R.Sb ∧
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.cV i').W (z.R.cV i).W ∧ HEq (R'.cV i').ρ (z.R.cV i).ρ ∧ HEq (R'.cV i').nW (z.R.cV i).nW ∧
    HEq (R'.cV i').iW (z.R.cV i).iW ∧ HEq (R'.vacP i') (z.R.vacP i) ∧ HEq (R'.ioP i') (z.R.ioP i) ∧
    HEq (R'.BV i') (z.R.BV i) ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧
    HEq (R'.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (R'.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (R'.νW i') (z.R.νW i) ∧ HEq (R'.fdW i') (z.R.fdW i) ∧
    ∀ (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL),
      (∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x) →
      (∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
        (HEq (R'.MW i' σ').H (z.R.MW i (σ'.comp ι)).H ∧
          HEq (R'.MW i' σ').nacg (z.R.MW i (σ'.comp ι)).nacg ∧
          HEq (R'.MW i' σ').ips (z.R.MW i (σ'.comp ι)).ips ∧
          HEq (R'.MW i' σ').σ (z.R.MW i (σ'.comp ι)).σ ∧
          HEq (R'.MW i' σ').lam (z.R.MW i (σ'.comp ι)).lam ∧
          HEq (R'.MW i' σ').ε (z.R.MW i (σ'.comp ι)).ε ∧
          HEq (R'.MW i' σ').fr (z.R.MW i (σ'.comp ι)).fr ∧
          HEq (R'.MW i' σ').enum (z.R.MW i (σ'.comp ι)).enum) ∧
        HEq (R'.HW i' σ') (z.R.HW i (σ'.comp ι)) ∧
        HEq (R'.gW i' σ') (z.R.gW i (σ'.comp ι)) ∧
        ∀ x x', CrdOver ι x x' → HEq ((R'.FW i').j σ' x') ((z.R.FW i).j (σ'.comp ι) x)) ∧
      ((∀ x x', CrdOver ι x x' → (x' ∈ (R'.FW i').WK ↔ x ∈ (z.R.FW i).WK)) ∧
        ∀ x' ∈ (R'.FW i').WK, ∃ x : Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL, CrdOver ι x x') ∧
      (∀ g' g, HEq g' g → (((R'.FW i').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) =
        ι (((z.R.FW i).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) ∧
      (∀ g' g, HEq g' g → ∀ x x', CrdOver ι x x' → CrdOver ι ((z.R.FW i).ρ g x) ((R'.FW i').ρ g' x')) ∧
      HEq (R'.FW i').Pt (z.R.FW i).Pt ∧
      (∀ lp' lp, HEq lp' lp → ∀ y' y, HEq y' y → ∀ (φ' : (R'.FW i').WK) (φ : (z.R.FW i).WK), CrdOver ι φ.1 φ'.1 →
        (R'.FW i').nrm lp' y' φ' = (z.R.FW i).nrm lp y φ)) ∧
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))



def RSide (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  RSideW z Wt' R' ∧ ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (R'.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (R'.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))))

end GlobalTheory.Mem.R3.Rw

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.columnFaceLevels_baseLevel_symmetricLevel : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → Formalism.IndefR.Seed.LevelsL (famR X I hX U Xg tr) L eG (face0 X I hX U Xg tr).lv2 := by
  first | exact @GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 | exact GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 | (intros; apply GlobalTheory.Mem.R3.LevelsFace.levelsL_face0 <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl


theorem ColW.cf_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    Fr.at (w.st Z) f = TC.cf w.I w.l Z := by
  have h := w.C_eq
  have : Fr.at (w.st Z) w.I.C = TC.cf w.I w.l Z := rfl
  rw [← this, h]


end GlobalTheory.Mem.Top.Bl
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr



theorem std_copy (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt) : z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std := by
  intro hXg htr hR hc hs
  cases z' with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le' ks' =>
  dsimp only at hXg htr hR hc ⊢
  subst hXg htr
  obtain rfl := eq_of_heq hc
  change BrgStd (w.st Z') w.I hX (usedOf w.I T Wt) z.Xg z.tr R'.toRealDat
  change HEq R' _ at hR
  have e : alg' = alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.st Z').B.embLL.injective
    rw [alg_eq']
    exact (z.alg_eq y).symm
  clear cG' geo' pins' lev' idG' good' mu' le' ks' alg_eq' hc
  subst e
  obtain rfl := eq_of_heq hR
  exact (by with_unfolding_all exact (hs :))

end GlobalTheory.Mem.R3.Rw.StdTr
end

section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3



theorem rowConditions_at_companion_from_readings : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) , (Lam3 x.Z → RowsHoldLam3 (divisionPairOfAdelicFormsFaceColumnsData x)) ∧ RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) ∧ DcPtG (divisionPairOfAdelicFormsFaceColumnsData x) ∧ (DivRows3 D x.A3 x.F.P0 x.F.ψ0 x.F.P1 x.F.ψ1 (zsOf x.R x.F) (s0Of x.R x.F) (s1Of x.R x.F) ex.p0 (colOf x.R x.F x.sEE) x.C.NuC (idsOf x.cG x.Z x.C) → DivRows3G (divisionPairOfAdelicFormsFaceColumnsData x)) := by
  intro D L hT Gi Gl K Yd cX ex x
  have hD : RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) := fun u t y F => x.C.pt u t y F
  exact ⟨fun h => h, hD, dcPtG_of hD, fun h => DivRows3.toG (P := divisionPairOfAdelicFormsFaceColumnsData x) h⟩

end GlobalTheory.Mem.R3
end
