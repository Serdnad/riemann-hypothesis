module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle296
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle021
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle257
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle052
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle019
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle064
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MinimalParabolicUnipotentLeviDecomp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle005
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle053
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.CuspEmbed

def piTensorMap {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) : (piTensor ρ).IntertwiningMap (piTensor σ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact (f a).isIntertwining _ _ _ _

theorem piTensorMap_injective {α : Type} [Fintype α] [DecidableEq α] {Γ Y Z : α → Type}
    [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) (hf : ∀ a, Function.Injective (f a)) :
    Function.Injective (piTensorMap f) :=
  GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective ℂ α Y Z (fun a => (f a).toLinearMap) hf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_injective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {σ : Representation ℂ (Levi k m) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Injective (parIndMap e f) := fun x y h =>
  Subtype.ext (Subtype.ext (funext fun g => hf
    (congrArg (fun z : IndSp e σ => z.1.1 g) h)))

def Embeds (N : ℕ) (Q : Irr k N) : Prop :=
  ∃ (s : ℕ) (u : Fin s → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin N),
    (∀ a, (u a).IsCusp) ∧ ∃ φ : Q.π.IntertwiningMap (multiProd e fun a => (u a).rep),
      Function.Injective φ

theorem intertw_of_subsingleton {G V W : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W)
    (g : G) : f ∘ₗ ρ g = σ g ∘ₗ f := by
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

theorem embeds_zero (Q : Irr k 0) : Embeds 0 Q := by
  have hQ := Q.irr
  have := nontrivial_of_irreducible hQ
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Q.V)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ Q.V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hker : Function.Injective f := by
    let S : Subrepresentation Q.π := ⟨LinearMap.ker f, fun g x hx => by
      rw [Subsingleton.elim g 1, map_one]
      exact hx⟩
    rcases eq_bot_or_eq_top S with h | h
    · have h' : LinearMap.ker f = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 h'
    · have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact absurd (LinearMap.ker_eq_top.1 h' ▸ rfl : f v = 0) hf
  let u : Fin 0 → IrrGL (k := k) := fun a => a.elim0
  haveI : IsEmpty (Σ a, Fin (u a).1) := ⟨fun x => x.1.elim0⟩
  let e : (Σ a, Fin (u a).1) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let L := GlobalTheory.EmptyProd.lineEquiv (k := k) e fun a => (u a).rep
  exact ⟨0, u, e, fun a => a.elim0,
    ⟨L.symm.toLinearMap ∘ₗ f, intertw_of_subsingleton _ _ _⟩, L.symm.injective.comp hker⟩

theorem embeds_cusp (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) : Embeds n π := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  let x : IrrGL (k := k) := IrrGL.of π.π π.smooth π.irr
  let ψ := multiProdEquiv e fun _ : Fin 1 => IrrGL.equivOf π.π π.smooth π.irr
  refine ⟨1, fun _ => x, e, fun _ => (IrrGL.isCusp_of.2 ⟨hn, hc⟩), (φ.trans ψ).toIntertwiningMap,
    (φ.trans ψ).toLinearEquiv.injective⟩

theorem reduce_embed (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hGL : GlobalTheory.Published.GeometricLemma) (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ ∃ φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π),
        Function.Injective φ := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := GlobalTheory.CuspSupportExist.L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := GlobalTheory.CuspSupportExist.L_tens hGL k n π s d e Y τ hτi hτq
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k (Fin s) (fun a => Fin (d a)) fun a => (σ a).toIrrRep
  obtain ⟨ε⟩ := hσ.nonempty_equiv hτi hirr
  let ψ := parIndEquiv e ε.symm
  exact ⟨s, d, e, σ, GlobalTheory.CuspSupportExist.L_lt k n s d e hne,
    ψ.toIntertwiningMap.comp φ, ψ.toLinearEquiv.injective.comp hφ⟩

theorem glue_embed (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π))
    (hφ : Function.Injective φ) (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k))
    (e' : ∀ a, (Σ b, Fin (u a b).1) ≃ Fin (d a)) (hu : ∀ a b, (u a b).IsCusp)
    (ψ : ∀ a, (σ a).π.IntertwiningMap (multiProd (e' a) fun b => (u a b).rep))
    (hψ : ∀ a, Function.Injective (ψ a)) : Embeds n π := by
  obtain ⟨E0, ⟨χ⟩⟩ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e'
    (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a),
      Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0
  obtain ⟨ω⟩ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  let Ψ := parIndMap e (piTensorMap ψ)
  have hΨ : Function.Injective Ψ := parIndMap_injective e _ (piTensorMap_injective ψ hψ)
  exact ⟨∑ a, t a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E,
    fun c => hu _ _, (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ),
    (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ)⟩

theorem embeds (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma)
    (N : ℕ) (Q : Irr k N) : Embeds N Q := by
  induction N using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact embeds_zero Q
  by_cases hc : IsCuspidal Q.π
  · exact embeds_cusp n hn Q hc
  · have hr := reduce_embed hBZ hGL n Q hc
    obtain ⟨s, d, e, σ, hlt, hr⟩ := hr
    obtain ⟨φ, hφ⟩ := hr
    have h : ∀ a, Embeds (d a) (σ a) := fun a => ih (d a) (hlt a) (σ a)
    unfold Embeds at h
    choose t u e' hu ψ hψ using h
    exact glue_embed n Q s d e σ φ hφ t u e' hu ψ hψ

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (Q : GlobalTheory.SplitRead.Irr k N),
      ∃ (s : ℕ) (u : Fin s → GlobalTheory.LocGL.IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin N),
        (∀ a, (u a).IsCusp) ∧
          ∃ φ : Q.π.IntertwiningMap (GlobalTheory.SmGL.multiProd e fun a => (u a).rep),
            Function.Injective φ :=
  fun hBZ hGL _ _ _ _ _ N Q => embeds hBZ hGL N Q

end GlobalTheory.CompanionTheory.CuspEmbed
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.adelic_annihilator_box_product : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin

theorem _root_.GlobalTheory.T.archimedean_iwasawa_minimal_parabolic : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ g ∈ GinfC V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.ArchIwasawa.exists_archIwasawa <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.Transl

open GlobalTheory.AutomorphicL2Unitary

theorem enorm_sub_sq_le {c f : ℝ → ℂ} (hf : Continuous f) (hd : ∀ t, HasDerivAt c (f t) t) :
    ‖c 1 - c 0‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
  have e : c 1 - c 0 = ∫ t in (0 : ℝ)..1, f t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hf.intervalIntegrable _ _)).symm
  have n1 : ‖c 1 - c 0‖ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ := by
    rw [e]
    exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hn : Continuous fun t => ‖f t‖ := hf.norm
  set A := ∫ t in (0 : ℝ)..1, ‖f t‖ with hA
  set B := ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2 with hB
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hAB : A ^ 2 ≤ B := by
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (‖f t‖ - A) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun _ _ => sq_nonneg _
    have h1 : (∫ t in (0 : ℝ)..1, (‖f t‖ - A) ^ 2) = B - 2 * A * A + A ^ 2 := by
      have : ∀ t, (‖f t‖ - A) ^ 2 = ‖f t‖ ^ 2 - 2 * A * ‖f t‖ + A ^ 2 := fun t => by ring
      simp only [this]
      have i1 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume 0 1 := (hn.pow 2).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun t => 2 * A * ‖f t‖) volume 0 1 :=
        (continuous_const.mul hn).intervalIntegrable _ _
      rw [intervalIntegral.integral_add (f := fun t => ‖f t‖ ^ 2 - 2 * A * ‖f t‖) (g := fun _ => A ^ 2) (i1.sub i2)
        (continuous_const.intervalIntegrable _ _),
        intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul]
      simp [← hA, ← hB]
    nlinarith
  have hle : ‖c 1 - c 0‖ ^ 2 ≤ B := (pow_le_pow_left₀ (norm_nonneg _) n1 2).trans hAB
  have hBi : B = ∫ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ ^ 2 := intervalIntegral.integral_of_le zero_le_one
  have hint : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    ((hn.pow 2).intervalIntegrable 0 1).1
  have hL : ENNReal.ofReal B = ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
    rw [hBi, ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_ofNat]
  rw [← hL, ENNReal.rpow_ofNat, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
  {φ ψ : G → ℂ}

theorem ofReal_norm_sq (h : MemL2Quotient Γ μ φ) :
    ENNReal.ofReal (‖h.toL2‖ ^ 2) = ∫⁻ g in stdDom Γ, ‖φ g‖ₑ ^ (2 : ℝ) ∂μ := by
  have hE : eLpNorm (descend Γ φ) 2 (AutomorphicL2Unitary.quotMeasure Γ μ) ≠ ⊤ := h.2.ne
  have h1 : ‖h.toL2‖ = (eLpNorm (descend Γ φ) 2 (AutomorphicL2Unitary.quotMeasure Γ μ)).toReal := Lp.norm_toLp _ _
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := descend Γ φ) (μ := AutomorphicL2Unitary.quotMeasure Γ μ) (p := 2) (by norm_num) h.2.aestronglyMeasurable
  have h3 := lintegral_quotMeasure (isFundamentalDomain_stdDom Γ μ) (fun q => ‖descend Γ φ q‖ₑ ^ (2 : ℝ))
  simp only [h.1.descend_mk] at h3
  rw [← h3, h1, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hE]
  simpa using h2

theorem memL2_sub (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : MemL2Quotient Γ μ fun x => φ x - ψ x := by
  have hd := isFundamentalDomain_stdDom Γ μ
  exact (memL2_iff_fundamental_domain hd).2 ⟨fun γ hγ g => by simp only [h.1 γ hγ, h'.1 γ hγ], ((memL2_iff_fundamental_domain hd).1 h).2.sub ((memL2_iff_fundamental_domain hd).1 h').2⟩

theorem toL2_sub (h : MemL2Quotient Γ μ φ) (h' : MemL2Quotient Γ μ ψ) : (memL2_sub h h').toL2 = h.toL2 - h'.toL2 := by
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e1 := (memL2_sub h h').lift_toL2_ae_eq
  have e2 : lift Γ (h.toL2 - h'.toL2) =ᵐ[μ] lift Γ h.toL2 - lift Γ h'.toL2 :=
    ae_quotMeasure_iff.1 (Lp.coeFn_sub h.toL2 h'.toL2)
  exact e1.trans ((h.lift_toL2_ae_eq.sub h'.lift_toL2_ae_eq).symm.trans e2.symm)

variable [μ.IsMulRightInvariant]

theorem norm_R_sub_le [SFinite μ] {a : ℝ → G} {u : G} (ha : Continuous a) (h0 : a 0 = 1) (h1 : a 1 = u) (hφ : MemL2Quotient Γ μ φ) (hψ : MemL2Quotient Γ μ ψ)
    (hψc : Continuous ψ) (hd : ∀ g t, HasDerivAt (fun s => φ (g * a s)) (ψ (g * a t)) t) :
    ‖R Γ μ u hφ.toL2 - hφ.toL2‖ ≤ ‖hψ.toL2‖ := by
  subst h1
  have hm := hφ.mul_right (a 1)
  have hs := memL2_sub hm hφ
  rw [right_translate_toL2, ← toL2_sub hm hφ]
  have key : ∫⁻ g in stdDom Γ, ‖φ (g * a 1) - φ g‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ g in stdDom Γ, ‖ψ g‖ₑ ^ (2 : ℝ) ∂μ := by
    have hpt : ∀ g, ‖φ (g * a 1) - φ g‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ) := fun g => by
      have := enorm_sub_sq_le (c := fun s => φ (g * a s)) (f := fun t => ψ (g * a t)) (by fun_prop) (hd g)
      simpa [h0] using this
    have hmeas : Measurable fun p : G × ℝ => ‖ψ (p.1 * a p.2)‖ₑ ^ (2 : ℝ) :=
      (Continuous.measurable (by fun_prop : Continuous fun p : G × ℝ => ψ (p.1 * a p.2))).enorm.pow_const _
    calc _ ≤ ∫⁻ g in stdDom Γ, (∫⁻ t in Set.Ioc (0 : ℝ) 1, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ)) ∂μ := lintegral_mono hpt
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (∫⁻ g in stdDom Γ, ‖ψ (g * a t)‖ₑ ^ (2 : ℝ) ∂μ) :=
        lintegral_lintegral_swap hmeas.aemeasurable
      _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (∫⁻ g in stdDom Γ, ‖ψ g‖ₑ ^ (2 : ℝ) ∂μ) := by
        refine lintegral_congr fun t => ?_
        rw [← ofReal_norm_sq (hψ.mul_right (a t)), ← ofReal_norm_sq hψ, ← right_translate_toL2, norm_R]
      _ = _ := by simp
  have h1 := (ofReal_norm_sq hs).le.trans (key.trans (ofReal_norm_sq hψ).ge)
  have h2 : ‖hs.toL2‖ ^ 2 ≤ ‖hψ.toL2‖ ^ 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

end Abstract

end GlobalTheory.CompanionTheory.HCCusp.Transl

namespace GlobalTheory.CompanionTheory.HCCusp.Transl

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.SmoothForms

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem coe_derInf (hθ : IsInfFam θ) (X : LieN V) (φ : Mc θ V) :
    (derInf hθ X φ : GA D V → ℂ) = Der (expInf θ V) X φ.1 := by
  have R := (RealPts.realPoints D).2 θ hθ V
  have hs : Sm (expInf θ V) φ.1 := (smooth_iff R φ.1).1 (mem_Mc_iff.1 φ.2).1.smooth
  funext g
  have e1 : (derInf hθ X φ : GA D V → ℂ) g = ∑ τ, Rder θ V τ (X τ).1 φ.1 g := by
    simp only [derInf, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun τ _ => rfl
  rw [e1]
  have e2 : ∀ τ, Rder θ V τ (X τ).1 φ.1 g = Der (expInf θ V) (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ)) φ.1 g := fun τ =>
    congrFun (Rder_eq R τ (X τ) φ.1) g
  have hX : ∑ τ, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ) : LieN V) = X := sum_atPlace X
  rw [Finset.sum_congr rfl fun τ _ => (e2 τ).trans (DerLinear.der_eq_fderiv hs _ g), DerLinear.der_eq_fderiv hs X g]
  exact (map_sum (fderiv ℝ (fun Z : LieN V => φ.1 (g * expInf θ V Z)) 0) (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ (X τ) : LieN V))
    Finset.univ).symm.trans (congrArg _ hX)

end GlobalTheory.CompanionTheory.HCCusp.Transl

theorem GlobalTheory.CompanionTheory.HCCusp.norm_Rcusp_expInf_sub_le : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D) (hθ : IsInfFam θ) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.SmoothForms.LieN V) (φ : GlobalTheory.CompanionTheory.HCCusp.Mc θ V), ‖GlobalTheory.Cusp.Rcusp V μ (GlobalTheory.SmoothForms.expInf θ V X) (GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ) - GlobalTheory.CompanionTheory.HCCusp.io μ hθ φ‖ ≤ ‖GlobalTheory.CompanionTheory.HCCusp.io μ hθ (GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ)‖ := by
  intro D θ hθ V μ _ _ X φ
  have R := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  let a : ℝ → GA D V := fun t => GlobalTheory.SmoothForms.expInf θ V (t • X)
  have ha : Continuous a := (GlobalTheory.CuspGeo.MeanValue.continuous_expInf hθ R).comp (continuous_id.smul continuous_const)
  have h0 : a 0 = 1 := by
    simpa [a] using GlobalTheory.CuspGeo.MeanValue.expInf_zero R
  have h1 : a 1 = GlobalTheory.SmoothForms.expInf θ V X := by simp [a]
  have hP := GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound
  have hφc := (GlobalTheory.Cusp.mem_cuspForms.1 φ.2).1
  set ψ := GlobalTheory.CompanionTheory.HCCusp.derInf hθ X φ with hψdef
  have hψf := (GlobalTheory.Cusp.mem_cuspForms.1 ψ.2).1
  have hs : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ V) φ.1 :=
    (GlobalTheory.SmoothForms.smooth_iff R φ.1).1 (GlobalTheory.CompanionTheory.HCCusp.mem_Mc_iff.1 φ.2).1.smooth
  have d0 : ∀ h, HasDerivAt (fun t : ℝ => φ.1 (h * a t)) (ψ.1 h) 0 := fun h => by
    rw [hψdef, GlobalTheory.CompanionTheory.HCCusp.Transl.coe_derInf]
    exact DifferentiableAt.hasDerivAt
      ((((hs h).differentiable (by simp)).comp (differentiable_id.smul_const X)) 0)
  have hd : ∀ g t, HasDerivAt (fun s => φ.1 (g * a s)) (ψ.1 (g * a t)) t := fun g t => by
    have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact d0 (g * a t))
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [a, mul_assoc, ← GlobalTheory.CuspGeo.MeanValue.expInf_add R, add_sub_cancel]
  have := GlobalTheory.CompanionTheory.HCCusp.Transl.norm_R_sub_le ha h0 h1 (GlobalTheory.Cusp.memL2_of_cusp_form (μ := μ) hP hθ hφc)
    (GlobalTheory.Cusp.memL2_of_cusp_form (μ := μ) hP hθ hψf) hψf.1.cont hd
  exact this

end
end
