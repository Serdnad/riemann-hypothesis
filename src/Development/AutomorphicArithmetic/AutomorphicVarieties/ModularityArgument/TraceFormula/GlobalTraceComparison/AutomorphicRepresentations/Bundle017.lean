module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle690
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.EopW
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem twist_loc (w : Pl E) (g : GLw n (GlobalTheory.EulerTw.cPl E w)) :
    thF E n (locGL E n (GlobalTheory.EulerTw.cPl E w) g) = locGL E n w (thetaGL n (RingHom.id _)
      (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g)) := by
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [GlobalTheory.EulerTwU.pc_thF]
  by_cases h : v = w
  · subst h
    rw [pLoc_locGL, pLoc_locGL]
  · have h' : GlobalTheory.EulerTw.cPl E v ≠ GlobalTheory.EulerTw.cPl E w := fun e =>
      h (by rw [← GlobalTheory.EulerTwU.cPl_cPl v, e, GlobalTheory.EulerTwU.cPl_cPl])
    rw [pLoc_locGL_of_ne h', pLoc_locGL_of_ne h]
    exact (congrArg (thetaGL n (RingHom.id _)) (map_one _)).trans (map_one _)

private theorem twist_conj (w : Pl E) (g : GLw n (GlobalTheory.ThetaSatake.cw w)) :
    thF E n (locGL E n w (PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹)) =
      locGL E n (GlobalTheory.ThetaSatake.cw w) g := by
  have e : thetaGL n (RingHom.id _) (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) =
      PhiU n (w.adicCompletion E) * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * (PhiU n (w.adicCompletion E))⁻¹ := by
    rw [GlobalTheory.CompanionTheory.ConjSat.flipGL_eq]
    rfl
  rw [← e, ← twist_loc w g, GlobalTheory.EulerTwU.thF_thF]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.satAll_pf :
    SatAll := by
  intro E _ _ _ n π w B y hy h0
  have hne : (⟨y, hy⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine ⟨fun hB hf => ?_, fun hB hf => ?_⟩
  · rw [CG.hasSat_mk] at hB
    have hx : (⟨y, hy⟩ : π.V) ∈ fixed (π.locRep w) (KGL w (n := n)) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
    exact (hB.2 _ hx hne).map (ρ' := rw' n w false) π.V.subtype (fun _ _ => rfl) h0
  · rw [CG.hasSat_mk] at hB
    let σ : Representation ℂ (GLw n w) π.V := π.finPart.comp (jw n w true)
    let k := PhiU n (w.adicCompletion E)
    let T : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinear (σ k⁻¹) (σ k)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    have hs : HasSatGL w σ (B.map (·⁻¹)) :=
      GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w) (conjLoc_spec _ w).2.2
        (GlobalTheory.ThetaSatake.absNorm_cw w).symm T (fun g x => ?_) hB
    · have hx : (⟨y, hy⟩ : π.V) ∈ fixed σ (KGL w (n := n)) :=
        GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf k hk)
      exact (hs.2 _ hx hne).map (ρ' := rw' n w true) π.V.subtype (fun _ _ => rfl) h0
    · have e : π.locRep (GlobalTheory.ThetaSatake.cw w) g = σ (k * GlobalTheory.CompanionTheory.ConjSat.flipGL w g * k⁻¹) := by
        change π.finPart (locGL E n (GlobalTheory.ThetaSatake.cw w) g) = π.finPart (thF E n (locGL E n w _))
        rw [twist_conj]
      change σ (GlobalTheory.CompanionTheory.ConjSat.flipGL w g) (σ k⁻¹ x) = σ k⁻¹ (π.locRep (GlobalTheory.ThetaSatake.cw w) g x)
      rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open PositivityTheory.Rg.BcB.E.E3.fintype in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piAdm_pf :
    PiAdm := by
  intro E _ _ _ n _ π _ K W hK hW
  have hs : ∀ (τ : E →+* ℂ) (z : ℂ), ∃ c : ℂ, ∀ φ ∈ π.V, cap τ z φ = c • φ := fun τ z =>
    π.exists_scalar (Algebra.subset_adjoin ⟨τ, z, rfl⟩) (by
      rintro (k | k | X)
      exacts [commute_cap_finRep τ z k, GlobalTheory.CapAdInv.cap_commute_rt_infGL E n τ z _, commute_cap_lie τ z X])
  choose c hc using hs
  haveI := wl_fin W
  haveI hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n K hK _ (sig W) (sig_cont W) c
  refine ⟨π.V ⊓ Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c), inf_le_left,
    Submodule.finiteDimensional_inf_right _ _, fun ψ hψ ht => ⟨hψ, Submodule.subset_span
      ⟨(π.cusp ψ hψ).1, fun k hk => Subtype.ext (funext fun g => ht.1 k hk g),
        coeff_mem W ψ ht.2, fun τ z => hc τ z ψ hψ⟩⟩⟩
end
