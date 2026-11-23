module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutTraceA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle142
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle045
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle060
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle058
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle078
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle079
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle004
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle081
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle080
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle007
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1591

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem gauss_mul_integral_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ :=
  _root_.PositivityTheory.ThKW.Trc.gauss_mul_integral_A_k C hG hR hO hs ha hb hbij hF κ hκ n t ht hu
end PositivityTheory.ThKW
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.ThetaOntoF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
theorem exists_thV_eqF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd N e he hrat f hf
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, hcs, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points F E nS nT N e
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR B.ψ hψ N (half F N) half_ne_zero
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, 𝓓, -, hD, h1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  have hsymm : ∀ (u : VA F N) (g : WOF F E nS nT → ℂ),
      heisV B.ψ u (g ∘ e.symm) = heisOF σ JS JT ξ₀ B.ψ (e.symm u) g ∘ e.symm :=
    fun u g => heisV_comp_symm B.ψ he u g
  have hquasi : ∀ g, IsThetaFunOF σ JS JT ξ₀ B.ψ g → QuasiV B.ψ (g ∘ e.symm) := by
    intro g hg a b w
    obtain ⟨x, hx⟩ := GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM F E nS nT N e hrat a b
    have hx' : e.symm (rat a, rat b) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    simp only [Function.comp_apply, map_add (f := _), hx', hg.quasi, symplOHF, he, hx, LinearEquiv.apply_symm_apply,
      algebraMap_half]
  have hbdd : ∀ g : VA F N → ℂ, Continuous g → QuasiV B.ψ g → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    intro g hg hq
    obtain ⟨C, hC'⟩ := (hK.prod hK).exists_bound_of_continuousOn hg.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨a, ha⟩ := hKc w.1
    obtain ⟨b, hb⟩ := hKc w.2
    have e1 : w = (rat a, rat b) + (w.1 - rat a, w.2 - rat b) :=
      Prod.ext (by simp) (by simp)
    rw [e1, hq, norm_mul, hψ.2.1, one_mul]
    exact hC' _ ⟨ha, hb⟩
  let 𝒱 : Set (VA F N → ℂ) := {g | ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ g = f ∘ e.symm}
  have hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV B.ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg.cont.comp hcs, hquasi g hg, hbdd _ (hg.cont.comp hcs) (hquasi g hg)⟩
  have hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV B.ψ ν 𝓓 (heisV B.ψ (M t) g) x) (invV B.ψ ν 𝓓 g' x) 0 := by
    rintro _ ⟨g, hg, rfl⟩ M hM
    let L : ℝ →+ WOF F E nS nT := e.symm.toLinearMap.toAddMonoidHom.comp M
    have hL : Continuous L := hcs.comp hM.1
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => (hfin _).2 (by
      have : e (L t) = M t := e.apply_symm_apply _
      rw [this]; exact hM.2 t)
    let g' : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) 0
    have hlev' : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u g' = g' := by
      obtain ⟨U, hUo, hU⟩ := hg.level
      exact ⟨U, hUo, fun u hu h0 =>
        _root_.GlobalTheory.T.theta_function_rapid_decay F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g L hL hL0 u h0 (hU u hu h0)⟩
    have hsm' := _root_.GlobalTheory.T.theta_function_integrable F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0
    have hg' : IsThetaFunOF σ JS JT ξ₀ B.ψ g' :=
      ⟨_root_.GlobalTheory.T.theta_function_moderate_growth F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0, hlev',
        _root_.GlobalTheory.T.theta_integral_unfolding F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g' hlev' hsm', hsm'⟩
    have hds : ∀ w s, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w)
        (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) s := by
      intro w s
      have h1' : HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
          (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) 0 := by
        have e2 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w) = fun t =>
            B.ψ (symplOHF σ JS JT ξ₀ w (L s)) * heisOF σ JS JT ξ₀ B.ψ (L t) g (w + L s) :=
          funext fun t => _root_.GlobalTheory.T.theta_integral_additive_family F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd L hL hL0 g w s t
        rw [e2]
        exact ((_root_.GlobalTheory.T.theta_function_smooth_vectors F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0 (w + L s)).hasDerivAt).const_mul _
      have h2 := HasDerivAt.comp_sub_const s s (by rwa [sub_self])
        (f := fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
      have e3 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) =
          fun x => heisOF σ JS JT ξ₀ B.ψ (L (s + (x - s))) g w := by
        funext x; rw [add_sub_cancel]
      rw [e3]
      exact h2
    refine ⟨_, ⟨g', hg', rfl⟩, ?_⟩
    obtain ⟨c1, -, C₁, hC₁⟩ := hV _ ⟨g, hg, rfl⟩
    obtain ⟨c2, -, C₂, hC₂⟩ := hV _ ⟨g', hg', rfl⟩
    refine GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam F N B.ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _))
      (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_
    simp only [hsymm, Function.comp_apply]
    exact hds (e.symm w) s
  have hmem : f ∘ e.symm ∈ 𝒱 := ⟨f, hf, rfl⟩
  have hlev : LevelV B.ψ (f ∘ e.symm) := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hcs, fun u hu h0 h0' => ?_⟩
    rw [hsymm, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]
  obtain ⟨hl, hs⟩ := GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev
  have hS : invV B.ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA F (Fin N) :=
    GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz F N _ hl hs (GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates F N B.ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
      (GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay F N B.ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV g hg).2) hder) _ hmem)
  refine ⟨_, hS, ?_⟩
  rw [GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N _ hS)]
  funext w
  simp
end GlobalTheory.ThetaOntoF
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

theorem _root_.GlobalTheory.T.weil_datum_splitting_characters : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT νS νT : (AF F ⊗[F] E)ˣ →* Circle) ω,
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        IsHeckeCharF νS → IsHeckeCharF νT → ResEtaF νS 0 → ResEtaF νT 0 →
        ∃ ω', IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (χS * νS) (χT * νT) ω' := by
  first | exact @_root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | exact _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k | (intros; apply _root_.GlobalTheory.WeilTwistF.exists_weilDatumOF_twist_k <;> assumption)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
open GlobalTheory.SplitInvFormF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
open GlobalTheory.SplitInvFormF
theorem exists_vac_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  classical
  have he' := isSplitIdemF_conj he
  let Y := conjHalf σ e nS nT
  let X := conjHalf σ (cAF σ e) nS nT
  obtain ⟨U, hU, hUf⟩ := hf₀.level
  obtain ⟨G, hGX, hGU⟩ := _root_.PositivityTheory.ThKW.exists_finite_open_subgroup_split F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  have hGX' : ∀ g ∈ G, g ∈ X := fun g hg => mem_conjHalf_conj he (hGX g hg)
  let YK : AddSubgroup (WOF F E nS nT) :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1}
      add_mem' := fun {a b} ha hb => ⟨Y.add_mem ha.1 hb.1, fun k hk hkf => by
        rw [commF_add_right, ha.2 k hk hkf, hb.2 k hk hkf, one_mul]⟩
      zero_mem' := ⟨Y.zero_mem, fun k _ _ => commF_zero_right k⟩
      neg_mem' := fun {a} ha => ⟨Y.neg_mem ha.1, fun k hk hkf => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) k a
        rwa [ha.2 k hk hkf, mul_one] at this⟩ }
  let Q : AddSubgroup YK :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hQfix : ∀ q ∈ Q, heisOF σ JS JT ξ₀ B.ψ (q : WOF F E nS nT) f₀ = f₀ := fun q hq =>
    hUf _ (hGU _ q.2.1 hq) (fin_of_mem he q.2.1)
  have hN : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT ξ₀ B.ψ (k • g) f₀ = f₀ := fun g hg => exists_nsmul_fix he' (hGX' g hg) hf₀
  choose! Ng hNg0 hNg using hN
  set N := ∏ g ∈ G, Ng g with hNdef
  have hN0 : 0 < N := Finset.prod_pos fun g hg => hNg0 g hg
  have hpowN : ∀ g ∈ G, ∀ y : YK, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) ^ N = 1 := by
    intro g hg y
    obtain ⟨m, hm⟩ : Ng g ∣ N := Finset.dvd_prod_of_mem _ hg
    rw [← commF_nsmul_left]
    refine y.2.2 _ (nsmul_mem (hGX' g hg) N) ?_
    rw [hm, mul_nsmul]
    exact heisOF_nsmul_fix he' (nsmul_mem (hGX' g hg) _) (hNg g hg) m
  haveI : Finite (YK ⧸ Q) := by
    let S := (Polynomial.nthRoots N (1 : ℂ)).toFinset
    refine Finite.of_injective (β := G → S) (fun a g => ⟨commF σ JS JT ξ₀ B.ψ g (Quotient.out a : YK), ?_⟩) ?_
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN0]
      exact hpowN g g.2 _
    · intro a b hab
      rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq]
      intro g hg
      have h1 := congrArg Subtype.val (congrFun hab ⟨g, hg⟩)
      simp only at h1
      show commF σ JS JT ξ₀ B.ψ g ((-Quotient.out a + Quotient.out b : YK) : WOF F E nS nT) = 1
      rw [AddSubgroup.coe_add, commF_add_right, ← h1, AddSubgroup.coe_neg, commF_neg_right]
  let Ch : Set (YK → ℂ) := {χ | ∃ x ∈ X, (∀ q ∈ Q, commF σ JS JT ξ₀ B.ψ x (q : WOF F E nS nT) = 1) ∧ χ = fun y : YK => commF σ JS JT ξ₀ B.ψ x (y : WOF F E nS nT)}
  obtain ⟨χ, ⟨x, hxX, -, rfl⟩, w, hwspan, hw0, hweig⟩ := exists_eigen_of_sep
    (fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT))
    (fun a b f => heisOF_add_half he a.2.1 b.2.1 f) Q f₀ hf₀0 hQfix Ch
    (by rintro _ ⟨x, -, -, rfl⟩ a b; exact commF_add_right x a b)
    (by rintro _ ⟨x, -, hx, rfl⟩ q hq; exact hx q hq)
    (by
      rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨x', hx', hxQ', rfl⟩
      refine ⟨x + x', X.add_mem hx hx', fun q hq => by rw [commF_add_left, hxQ q hq, hxQ' q hq, one_mul], ?_⟩
      funext y
      simp only [Pi.mul_apply, commF_add_left])
    ⟨0, X.zero_mem, fun q _ => commF_zero_left _, by funext y; simp only [Pi.one_apply, commF_zero_left]⟩
    (fun y hy => by
      have hy' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1 := hy
      push_neg at hy'
      obtain ⟨g, hg, hne⟩ := hy'
      exact ⟨_, ⟨g, hGX' g hg, fun q hq => hq g hg, rfl⟩, hne⟩)
  have hspan_theta : Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    exact _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hf₀)
  have hspan_fix : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      LinearMap.eqLocus (heisL σ JS JT ξ₀ B.ψ k) LinearMap.id := fun k hk hkf => Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    show heisOF σ JS JT ξ₀ B.ψ k (heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) = heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀
    rw [heisOF_comm, y.2.2 k hk hkf, one_smul, hkf])
  have hwθ : IsThetaFunOF σ JS JT ξ₀ B.ψ w := hspan_theta hwspan
  refine ⟨heisOF σ JS JT ξ₀ B.ψ (-x) w, _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hwθ, ?_, ?_⟩
  · intro h0
    apply hw0
    have := heisOF_add_half (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) he' hxX (X.neg_mem hxX) w
    rw [add_neg_cancel, heisOF_zero] at this
    rw [this, show heisOF σ JS JT ξ₀ B.ψ (-x) w = 0 from h0]
    exact map_zero (heisL σ JS JT ξ₀ B.ψ x)
  · intro y hy
    by_cases hyK : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1
    · left
      have hyy : y ∈ YK := ⟨hy, hyK⟩
      have h1 := hweig ⟨y, hyy⟩
      change commF σ JS JT ξ₀ B.ψ x y • heisOF σ JS JT ξ₀ B.ψ y w = w at h1
      rw [heisOF_comm, commF_swap]
      conv_rhs => rw [← h1]
      exact (GlobalTheory.WeilPartsF.heisOF_smul _ _ _).symm
    · right
      push_neg at hyK
      obtain ⟨k, hk, hkf, hne⟩ := hyK
      refine ⟨k, ?_, hne⟩
      rw [heisOF_comm, commF_half he' hk (X.neg_mem hxX), one_smul]
      congr 1
      exact hspan_fix k hk hkf hwspan
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fam_eq_L_pf_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    L (a s) (fP 1) = fun v => fam d.m X s v := by
  obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
  set A : Matrix (Fin d.n) (Fin d.n) ℂ := diagonal fun j => (Real.exp (s * X j) : ℂ) with hA
  have hdet : A.det = ((Real.exp (∑ j, s * X j) : ℝ) : ℂ) := by
    rw [hA, det_diagonal, Real.exp_sum, Complex.ofReal_prod]
  have hpos : 0 < Real.exp (∑ j, s * X j) := Real.exp_pos _
  have hunit : IsUnit A.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hpos.ne')
  have hinv : (Aᴴ)⁻¹ = diagonal fun j => (Real.exp (-(s * X j)) : ℂ) := by
    rw [hA, diagonal_conjTranspose]
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  have hy : mR (a s) = mLoc A := by
    rw [show mR (a s) = _ from ha s, mLoc, hinv]
  rw [hk (a s) A hunit hy (fP 1) (hFP d.m d.n 1)]
  funext v
  have hn : ‖A.det‖ = Real.exp (∑ j, s * X j) := by
    rw [hdet, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [hn, ← hdet, div_self hunit.ne_zero, _root_.one_zpow, one_mul, hdet]
  simp only [fam, fP, evX, map_one, one_mul, gs]
  congr 1
  · rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · congr 1
    push_cast
    rw [neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
    have he : (Matrix.of v * A) b j = v b j * ((Real.exp (s * X j) : ℝ) : ℂ) := by
      rw [hA, Matrix.mul_diagonal]
      rfl
    erw [he]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.ofReal_mul, mul_pow,
      Complex.ofReal_exp, ← Complex.exp_nat_mul, mul_comm]
    congr 2
    push_cast
    ring
theorem fam_eq_L_closed_k : type_of% @_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_pf_k := @_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_eq_L_pf_k
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelExists_of_smallness (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_wired_k _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sDarb_k partCharInv _root_.PositivityTheory.SiegelWeilFormula.Ald.chartFacts_k hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section



section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem siegelSmall_of_slice_k (hF : SliceFacts) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_k hF Ldx.adaptedChar
end PositivityTheory.SiegelWeilFormula.Ald
end
end

section



section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem smallS_of'_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k → SliceFacts → _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k := fun hC hF => _root_.PositivityTheory.SiegelWeilFormula.Ald.smallS_of_k hC hF (subSplit_of hF) haarLc
end PositivityTheory.SiegelWeilFormula.Ald
end
end
