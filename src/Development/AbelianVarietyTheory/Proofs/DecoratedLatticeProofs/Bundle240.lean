module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle223
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle725
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle205
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem holValueAt_npow_sub_mul : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c →
    (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  intro h h' s₀ c r σ hr hh e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (GlobalTheory.Cont.rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := GlobalTheory.Cont.holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp [npow_eq_exp hr]
  have hm := hg.mul hh
  simp only [h1, one_mul] at hm
  exact hm.congr ⟨σ, fun s hs => (e s hs).symm⟩

end GlobalTheory.StdUnn
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isParamVec_of_injective_equivariant {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : GlobalTheory.LFun.IsParamVec σ J L h ρ' (f x) B) : GlobalTheory.LFun.IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, GlobalTheory.LFun.IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, GlobalTheory.LFun.IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem thetaKO_om_apply {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g a : GA D S)
    (x a' : GA D T) (u : WO S T → ℂ) : thetaKO om g x (om (a, a') u) = thetaKO om (g * a) (x * a') u := by
  simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem thetaKO_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {u : WO S T → ℂ}
    (hu : IsThetaFunO ψ S T u) (γ : GA D S) (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) :
    thetaKO om (γ * g) x u = thetaKO om g x u := by
  have e : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  simp only [thetaKO, e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hu)

theorem thetaIntegral_param : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  intro hP D hT ψ θ S T χS χT om hθ hW t ht ν 𝓕 hν h𝓕 v hunr w h f hf y B hy hc hB hne
  let U : Submodule ℂ (WO S T → ℂ) := by
    exact {
    carrier := {f | IsThetaFunO ψ S T f}
    add_mem' {f g} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) := by
      have h : IsThetaFunO ψ S T (f + g) := {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, hfix⟩ := hf.level
          obtain ⟨V, hV, hfix'⟩ := hg.level
          refine ⟨U ⊓ V, hU.inter hV, fun u hu hfin => ?_⟩
          funext w
          have ef := congrFun (hfix u hu.1 hfin) w
          have eg := congrFun (hfix' u hu.2 hfin) w
          unfold heisO at ef eg ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, ef, eg]
        cont := hf.cont.add hg.cont
        smooth k L hL hreal w := (hf.smooth k L hL hreal w).add (hg.smooth k L hL hreal w) }
      exact h
    zero_mem' := by
      have h : IsThetaFunO ψ S T 0 := {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const }
      exact h
    smul_mem' c f (hf : IsThetaFunO ψ S T f) := by
      have h : IsThetaFunO ψ S T (c • f) := {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, hfix⟩ := hf.level
          refine ⟨U, hU, fun u hu hfin => ?_⟩
          funext w
          have ef := congrFun (hfix u hu hfin) w
          unfold heisO at ef ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, ef]
        cont := hf.cont.const_smul c
        smooth k L hL hreal w := contDiff_const.mul (hf.smooth k L hL hreal w) }
      exact h
    }
  have hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U := fun a a' u hu => hW.om_pres _ u hu
  let ρ0 : Representation ℂ (Gv S v) (GA D S → ℂ) := (rightReg ℂ (GA D S) ℂ).comp (embV S v)
  have hρ0 : ∀ a (z : GA D S → ℂ) g, ρ0 a z g = z (g * embV S v a) := fun _ _ _ => rfl
  let cy : GA D S → ℂ := fun g => conj (y g)
  let X : Submodule ℂ (GA D S → ℂ) := Submodule.span ℂ (Set.range fun a : Gv S v => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (Gv S v) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u, IsThetaFunO ψ S T u → ∀ x, IntegrableOn (fun g => thetaKO om g x u * z g) 𝓕 ν) ∧
      (∀ γ ∈ GQ S, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u hu x => GlobalTheory.T.thetaKernel_mul_conj_cuspForm_integrableOn hP D ψ S T χS χT om hW θ hθ ν 𝓕 hν h𝓕 u y hu hy hc (embV S v a) x,
        fun γ hγ g => ?_⟩
      show conj (y (γ * g * embV S v a)) = conj (y (g * embV S v a))
      rw [mul_assoc, hy.left γ hγ]
    | zero => exact ⟨fun u _ x => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (z + z') g) = fun g => thetaKO om g x u * z g + thetaKO om g x u * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u hu x).add (h2.1 u hu x)
    | smul c z _ h1 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (c • z) g) = fun g => c * (thetaKO om g x u * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u hu x).const_mul c
  let bf : U → X → GA D T → ℂ := fun u z x => ∫ g in 𝓕, thetaKO om g x (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
  let b : U →ₗ[ℂ] X →ₗ[ℂ] (GA D T → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u u' z => by
      funext x
      show _ = bf u z x + bf u' z x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z z.2).1 u' u'.2 x)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u z z' => by
      funext x
      show _ = bf u z x + bf u z' x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z' z'.2).1 u u.2 x)]
      congr 1; funext g
      simp [mul_add])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ a a' (u : U) (z : X), b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a z) =
      (rightReg ℂ (GA D T) ℂ).comp (embV T v) a' (b u z) := by
    intro a a' u z
    funext x
    show ∫ g in 𝓕, thetaKO om g x (om (embV S v a, embV T v a') u) * (z : GA D S → ℂ) (g * embV S v a) ∂ν =
      ∫ g in 𝓕, thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D S ν 𝓕 hν h𝓕 (fun g => thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hW u.2 γ hγ, (hXp z z.2).2 γ hγ]) (embV S v a)
  have hx : GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ ⟨cy, hcy⟩ B :=
    isParamVec_of_injective_equivariant X.subtype (fun _ _ => rfl) Subtype.val_injective hB
  exact hT ψ S T χS χT om hW t ht v trivial hunr w h U hU ⟨f, hf.1⟩ hf X ρ ⟨cy, hcy⟩ B hx (GA D T → ℂ)
    ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) b hb hne

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.DownLift.DefiniteComp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_mul_inf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (h * k) = (R.cV i).ρ k⁻¹ (R.extV i t y h) := by
  have hr : (finHom (Vc D i)).rangeRestrict (h * k) = (finHom (Vc D i)).rangeRestrict h := by
    apply Subtype.ext
    simp [MonoidHom.mem_ker.1 hk]
  show (R.cV i).ρ (h * k)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * k))) =
    (R.cV i).ρ k⁻¹ ((R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)))
  refine (congrArg ((R.cV i).ρ (h * k)⁻¹) (congrArg ((R.HV i t).e y) hr)).trans ?_
  have e : (R.cV i).ρ (h * k)⁻¹ = (R.cV i).ρ k⁻¹ * (R.cV i).ρ h⁻¹ := by rw [_root_.mul_inv_rev, map_mul]
  exact congrArg (fun f : Module.End ℂ (R.cV i).W => f ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))) e

theorem extV_mul_Kg (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i))
    (hK : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = R.extV i t y h := by
  have h2 : Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) ≤
      lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i t)) :=
    Kg_le_lev (D := flag1L (R.datVt i t)) Finset.subset_union_left Finset.subset_union_right
  have hlev : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := mem_levA.2 ⟨hκ, h2 hK⟩
  have hred : ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := fun PP hP =>
    (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hK.2 PP) hP)).2
  have hfn : levFn (R.βV i) (flag1L (R.datVt i t)) (finE (Vc D i) κ) = 1 :=
    GlobalTheory.ThetaIntegrand.levFn_eq_one (R.βV i) _ (flag1L (R.datVt i t))
      (fun PP hP => hred PP (Finset.mem_union_left _ hP)) (fun PP hP => hred PP (Finset.mem_union_right _ hP))
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = 1 :=
    (congrArg (fun u : ℂˣ => (u : ℂ)) hfn).trans Units.val_one
  exact (GlobalTheory.DownLift.GenFinite.extV_type R hM i t y κ hlev h).trans (by simp only [hchi, one_smul])

def compL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ((R.cV i).W →ₗ[ℂ] ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  LinearMap.pi fun g => LinearMap.applyₗ (R := ℂ) (R.extV i t y g)

theorem mul_inf_mem_range (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) :
    (fun g => l (R.extV i t y (g * k))) ∈ LinearMap.range (compL R i t y) :=
  ⟨l ∘ₗ (R.cV i).ρ k⁻¹, funext fun g => (congrArg l (extV_mul_inf R i t y hk g)).symm⟩

theorem definiteScalarComponent_isCusp_and_congruence_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t cA a hd y l
  have hM : R.IsModels := hG.core.models
  have hf : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hcont : Continuous fun g => l (R.extV i t y g) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hM.cV i) (R.βV i) (R.datVt i t) hf)
  have hleft : ∀ γ ∈ GQ (Vc D i), ∀ g, l (R.extV i t y (γ * g)) = l (R.extV i t y g) := fun γ hγ g =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hf γ hγ g)
  have hlevel : ∃ U : Subgroup (GA D (Vc D i)), IsOpen (U : Set (GA D (Vc D i))) ∧
      ∀ k ∈ U, k ∈ GfC (Vc D i) → ∀ g, l (R.extV i t y (g * k)) = l (R.extV i t y g) :=
    ⟨_, GlobalTheory.DefiniteEnd.isOpen_Kg (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), fun k hk hkf g =>
      congrArg l (extV_mul_Kg R hM i t y hkf hk g)⟩
  have hkfin : FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D (Vc D i) → ℂ |
      ∃ k ∈ GinfC (Vc D i), ψ = rTr (Vc D i) k fun g => l (R.extV i t y g)}) :=
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact mul_inf_mem_range R i t y l hk))
  have hdef : IsAutFunDef (Vc D i) fun g => l (R.extV i t y g) := ⟨⟨hleft, hlevel, hcont⟩, hkfin⟩
  have hdefn : (Vc D i).IsDefinite := fun τ => Or.inl (hd.pos τ)
  have hsm := ((GlobalTheory.DefiniteForms.autFunDefIffSm D) R.θ hd.inf (Vc D i) hd.sig hdefn _).1 hdef
  have hcusp : IsCuspFun (Vc D i) fun g => l (R.extV i t y g) := fun r C hC =>
    absurd hC (GlobalTheory.Per.isAniso_of_posDef hd.sig hd.pos r C)
  have hK : GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf R.θ (Vc D i) cA) fun g => l (R.extV i t y g) :=
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨LinearMap.range (compL R i t y), inferInstance, fun k hk =>
      mul_inf_mem_range R i t y l (GlobalTheory.Cusp.Kinf_le hk)⟩
  refine ⟨GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hsm, hcusp⟩, hK⟩, fun κ hκ g => ?_⟩
  have h1 := mem_levA.1 hκ
  have h2 : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) :=
    (Model.lev_prinDat (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) ▸ h1.2
  exact congrArg l (extV_mul_Kg R hM i t y h1.1 h2 g)

end GlobalTheory.DownLift.DefiniteComp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.PlacesDistinct

variable {D : D7}

theorem placeIdem_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  congr 1
  refine RestrictedProduct.ext _ _ fun u => ?_
  by_cases hu : u = v
  · subst hu
    exact h1.trans h1'.symm
  · exact (h2 u hu).trans (h2' u hu).symm

theorem finPart_idem_int {e : AE D} {w : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w) :
    finPart D e ∈ intAE D := by
  have h1 := (h.2 1 one_ne_zero).not
  have hw : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have := not_not.1 (h1.1 hw)
  simpa using this

theorem conj_mem_of {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {x x' : 𝓞 D.host.E} (hx' : (x' : D.host.E) = star (x : D.host.E))
    (hx0 : x ≠ 0) (hxw : x ∈ w.asIdeal) (hxw' : x ∉ w'.asIdeal) : x' ∈ w'.asIdeal := by
  have hx'0 : x' ≠ 0 := by
    intro h0
    apply hx0
    have : star (x : D.host.E) = 0 := by rw [← hx', h0]; rfl
    exact RingOfIntegers.coe_eq_zero_iff.mp (star_eq_zero.mp this)
  have hN : finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := (h.2 x hx0).1 hxw
  have hI' : finPart D (e' * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := not_not.1 (mt (h'.2 x hx0).2 hxw')
  have he := finPart_idem_int h
  have hee : e = e * e' + e * cA D e' := by
    rw [← mul_add, ← hsum, mul_add, h.1.1, h.1.2.1, add_zero]
  have hsplit : e * incA D ((x : D.host.E)⁻¹) =
      e * (e' * incA D ((x : D.host.E)⁻¹)) + e * (cA D e' * incA D ((x : D.host.E)⁻¹)) := by
    conv_lhs => rw [hee]
    ring
  have hA : finPart D (e * (e' * incA D ((x : D.host.E)⁻¹))) ∈ intAE D := by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hI'
  have hB : finPart D (cA D e' * incA D ((x : D.host.E)⁻¹)) ∉ intAE D := by
    intro hB
    apply hN
    rw [hsplit, map_add (f := _)]
    refine add_mem hA ?_
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE he hB
  have hC : cA D e' * incA D ((x : D.host.E)⁻¹) = cA D (e' * incA D ((x' : D.host.E)⁻¹)) := by
    rw [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA, hx', star_inv₀, star_star]
  rw [hC, GlobalTheory.FinPl.FrameLat.cA_int_iff] at hB
  exact (h'.2 x' hx'0).2 hB

theorem prime_eq {e e' : AE D} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') (hsum : e + cA D e = e' + cA D e') {π π' : 𝓞 D.host.E}
    (hπ' : (π' : D.host.E) = star (π : D.host.E)) (hw : π ∈ w.asIdeal) (hw' : π ∈ w'.asIdeal)
    (hc : π' ∉ w'.asIdeal) : w = w' := by
  by_contra hne
  have hnle : ¬ w.asIdeal ≤ w'.asIdeal := by
    intro hle
    apply hne
    exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)
  obtain ⟨x₀, hx₀w, hx₀w'⟩ := Set.not_subset.1 hnle
  have hx₀0 : x₀ ≠ 0 := fun h0 => hx₀w' (h0 ▸ w'.asIdeal.zero_mem)
  have hy : π + x₀ ∉ w'.asIdeal := fun hm => hx₀w' (by simpa using w'.asIdeal.sub_mem hm hw')
  have hy0 : π + x₀ ≠ 0 := fun h0 => hy (h0 ▸ w'.asIdeal.zero_mem)
  obtain ⟨c₀, hc₀⟩ : ∃ c : 𝓞 D.host.E, (c : D.host.E) = star (x₀ : D.host.E) :=
    ⟨⟨star (x₀ : D.host.E), (x₀.2).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩
  have h1 : c₀ ∈ w'.asIdeal := conj_mem_of h h' hsum hc₀ hx₀0 hx₀w hx₀w'
  have h2 : π' + c₀ ∈ w'.asIdeal :=
    conj_mem_of h h' hsum (x := π + x₀) (by push_cast; rw [star_add]; exact congrArg₂ (· + ·) hπ' hc₀) hy0 (w.asIdeal.add_mem hw hx₀w) hy
  exact hc (by simpa using w'.asIdeal.sub_mem h2 h1)

end GlobalTheory.AdForm.PlacesDistinct


open GlobalTheory.AdForm.PlacesDistinct in
theorem GlobalTheory.AdForm.StdT.places_injective : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → Function.Injective fun i => (p i).v := by
  intro B X I _ _ l Z u k _ _ _ _ ι p β Q L hS
  obtain ⟨⟨e, he⟩, -⟩ := hS
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  intro i i' hv
  have hv : (p i).v = (p i').v := hv
  apply e.injective
  apply Subtype.ext
  have hmem : ∀ j, X.piT u ∈ (e j).1.asIdeal := fun j => (Formalism.L2.Col.mem_divs hne _).1 (e j).2
  obtain ⟨ε, hε, hε'⟩ := (p i).above
  obtain ⟨ε', hε2, hε2'⟩ := (p i').above
  rw [hv] at hε
  have hsum : (p i).e + cA (I.rec7 l Z) (p i).e = (p i').e + cA (I.rec7 l Z) (p i').e := by
    rw [hε', hε2', placeIdem_unique hε hε2]
  refine prime_eq (he i) (he i') hsum (π := X.piT u) (π' := B.fields.conjO (X.piT u)) rfl (hmem i) (hmem i') ?_
  intro hc
  obtain ⟨a, b, hab⟩ := hcop
  exact (e i').1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ (e i').1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i')) (Ideal.mul_mem_left _ b hc)))

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaChainStage_wittIndex_lt_and_places_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split | exact GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split | (intros; apply GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split <;> assumption)
end
