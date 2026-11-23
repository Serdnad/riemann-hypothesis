module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.KeyFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DerCurve
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle006
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ProdBd
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem mc_fix {G V H : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] (ι : H →* G)
    (hsm : ∀ f, ∀ᶠ h in 𝓝 (1 : H), ρ (ι h) f = f) {c : G → ℂ} (hc : c ∈ I.MC ρ)
    (hinv : ∀ g h, c (g * ι h) = c g) :
    c ∈ Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), (∀ h, ρ (ι h) f = f) ∧ c = fun x => Λ (ρ x f)} := by
  obtain ⟨n, a, b, hab⟩ := Submodule.mem_span_set'.1 hc
  choose Λ f hb using fun i => (b i).2
  have hval : ∀ x, c x = ∑ i, a i * Λ i (ρ x (f i)) := by
    intro x
    rw [← hab]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]
  let R : H →* Module.End ℂ (Fin n → V) :=
    { toFun := fun h => LinearMap.pi fun i => (ρ (ι h)).comp (LinearMap.proj i)
      map_one' := LinearMap.ext fun x => funext fun i => by simp
      map_mul' := fun p q => LinearMap.ext fun x => funext fun i => by simp }
  have hR : ∀ h (x : Fin n → V) i, R h x i = ρ (ι h) (x i) := fun _ _ _ => rfl
  obtain ⟨s, hs, hfix⟩ := UpperTheory.ConvolutionTheory.R2.H.avg H (Fin n → V) R f (by
    have : ∀ᶠ h in 𝓝 (1 : H), ∀ i, ρ (ι h) (f i) = f i := Filter.eventually_all.2 fun i => hsm (f i)
    filter_upwards [this] with h hh
    funext i
    exact hh i)
  let S : Fin n → V := ∑ k ∈ s, R k f
  have hS : ∀ i, S i = ∑ k ∈ s, ρ (ι k) (f i) := fun i => by
    simp only [S, Finset.sum_apply, hR]
  have hcard : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hs)
  have key : c = (s.card : ℂ)⁻¹ • ∑ i, a i • fun x => Λ i (ρ x (S i)) := by
    funext x
    have h1 : (s.card : ℂ) * c x = ∑ k ∈ s, c (x * ι k) := by
      simp only [hinv, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ k ∈ s, c (x * ι k) = ∑ i, a i * Λ i (ρ x (S i)) := by

      simp only [hval, hS, map_sum, map_mul, Module.End.mul_apply, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [← h2, ← h1, inv_mul_cancel_left₀ hcard]
  rw [key]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Λ i, S i, fun h => ?_, rfl⟩))
  have := congrFun (hfix h) i
  exact this

private theorem tj_fin {K : Type} [Field K] [NumberField K] (w : P K) (n : ℕ) {ϖ : Kv w} (hϖ : Formalism.UG.IsUnifV K w ϖ) (j : ℕ) :
    (Function.support fun c : GL (Fin n) (Kv w) ⧸ GlobalTheory.LFun.KGL w (n := n) => Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out).Finite := by
  have := GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm K w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j)
    (1 : Representation ℂ (GL (Fin n) (Kv w)) ℂ) (1 : ℂ)
  simpa using this

private theorem tj_sum {K : Type} [Field K] [NumberField K] (w : P K) (n : ℕ) {ϖ : Kv w} (hϖ : Formalism.UG.IsUnifV K w ϖ) (j : ℕ)
    (W : GL (Fin n) (Kv w) → ℂ) (g : GL (Fin n) (Kv w)) :
    ∑ᶠ c : GL (Fin n) (Kv w) ⧸ GlobalTheory.LFun.KGL w (n := n), Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * W (g * c.out) =
      ∑ c ∈ (tj_fin w n hϖ j).toFinset, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * W (g * c.out) := by
  refine finsum_eq_sum_of_support_subset _ fun c hc => ?_
  simp only [Set.Finite.coe_toFinset, Function.mem_support] at hc ⊢
  exact left_ne_zero_of_mul hc

private theorem eig_span {K : Type} [Field K] [NumberField K] (w : P K) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Kv w)) V) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w ρ B)
    {c : GL (Fin n) (Kv w) → ℂ}
    (hc : c ∈ Submodule.span ℂ {c | ∃ (Λ : V →ₗ[ℂ] ℂ) (f : V), (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ρ k f = f) ∧ c = fun x => Λ (ρ x f)}) :
    Eig w B c := by
  induction hc using Submodule.span_induction with
  | mem c h =>
    obtain ⟨Λ, f, hf, rfl⟩ := h
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · rw [map_mul, Module.End.mul_apply, hf k hk]
    · by_cases h0 : f = 0
      · subst h0
        simp
      have he := (hB.2 f (GlobalTheory.LGrp.mem_fixed.2 hf) h0).2.2.2 ϖ hϖ j hj
      let L : V →+ ℂ := (Λ.comp (ρ g)).toAddMonoidHom
      have hs := L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm K w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ f)
      refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg L he).trans ?_))
      · simp [L, map_mul]
      · simp [L]
  | zero => exact ⟨hB.card, by simp, by simp⟩
  | add a b _ _ ha hb =>
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · simp only [Pi.add_apply, ha.inv g k hk, hb.inv g k hk]
    · have e1 := ha.eig ϖ hϖ j hj g
      have e2 := hb.eig ϖ hϖ j hj g
      rw [tj_sum w n hϖ j] at e1 e2 ⊢
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, e1, e2]
  | smul z a _ ha =>
    refine ⟨hB.card, fun g k hk => ?_, fun ϖ hϖ j hj g => ?_⟩
    · simp only [Pi.smul_apply, ha.inv g k hk]
    · have e1 := ha.eig ϖ hϖ j hj g
      rw [tj_sum w n hϖ j] at e1 ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      calc _ = z * ∑ c ∈ (tj_fin w n hϖ j).toFinset, Formalism.UG.Tj ℂ n (Formalism.UG.Ov K w) ϖ j c.out * a (g * c.out) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _
        _ = _ := by rw [e1, mul_left_comm]

private theorem kgl_map {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] {n : ℕ} {v : P K} {w : P M}
    (c : Kv v ≃+* Kv w) (hc : ∀ x, Valued.v (c x) = Valued.v x) (g : GL (Fin n) (Kv v)) :
    g ∈ GlobalTheory.LFun.KGL v (n := n) ↔ Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hO : ∀ x, c x ∈ Formalism.UG.Ov M w ↔ x ∈ Formalism.UG.Ov K v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hGv : ∀ (g : GL (Fin n) (Kv v)) i j, (Matrix.GeneralLinearGroup.map c.toRingHom g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  simp only [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.splitEig :
    SplitEig := by
  intro E _ _ _ D W M N P π Φ hΦ v w hs B hB hFix g
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  obtain ⟨θ, hθ⟩ := UpperTheory.ConvolutionTheory.R2.I.splt ℚ E D v w i hc hx
  have hmc := UpperTheory.ConvolutionTheory.R2.I.key ℚ E D W M π v θ _ hθ Φ hΦ g
  let gm : GL (Fin 2) (Kv v) →* GL (Fin 2) (Kv w) := Matrix.GeneralLinearGroup.map i.toRingHom
  let gi : GL (Fin 2) (Kv w) →* GL (Fin 2) (Kv v) := Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hgm : ∀ y, gm (gi y) = y := fun y => by
    ext a b
    simp [gm, gi]
  have hgi : ∀ y, gi (gm y) = y := fun y => by
    ext a b
    simp [gm, gi]
  let c : GL (Fin 2) (Kv v) → ℂ := fun x => WE D Φ.1 (g * lc w (gm x))
  have hinv : ∀ x (k : GlobalTheory.LFun.KGL v (n := 2)), c (x * (GlobalTheory.LFun.KGL v (n := 2)).subtype k) = c x := by
    intro x k
    have hk : gm k.1 ∈ GlobalTheory.LFun.KGL w (n := 2) := (kgl_map i hv k.1).1 k.2
    change WE D Φ.1 (g * lc w (gm (x * k.1))) = WE D Φ.1 (g * lc w (gm x))
    unfold WE
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [map_mul, map_mul, ← mul_assoc g, ← mul_assoc _ _ (lc w (gm k.1)), hFix _ _ hk]
  haveI : CompactSpace (GlobalTheory.LFun.KGL v (n := 2)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v 2).2
  have hsm : ∀ f, ∀ᶠ h in 𝓝 (1 : GlobalTheory.LFun.KGL v (n := 2)), π.locRep v ((GlobalTheory.LFun.KGL v (n := 2)).subtype h) f = f := fun f =>
    (continuous_subtype_val.tendsto (1 : GlobalTheory.LFun.KGL v (n := 2))).eventually
      (((UpperTheory.ConvolutionTheory.R2.I.locSm ℚ π v).1 f).mem_nhds (by simp))
  have h1 := mc_fix (π.locRep v) (GlobalTheory.LFun.KGL v (n := 2)).subtype hsm hmc hinv
  let ρ' : Representation ℂ (GL (Fin 2) (Kv w)) π.V := (π.locRep v).comp gi
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV ℚ v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have hB' : GlobalTheory.LFun.HasSatGL w ρ' B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' (LinearEquiv.refl ℂ _) (fun x f => by
      change π.locRep v (gi (gm x)) f = π.locRep v x f
      rw [hgi]) hB
  have e : (fun y => WE D Φ.1 (g * finGL E 2 (locGL E 2 w y))) = LinearMap.funLeft ℂ ℂ gi c := by
    funext y
    change _ = WE D Φ.1 (g * lc w (gm (gi y)))
    rw [hgm]
    rfl
  rw [e]
  refine eig_span w ρ' hB' ((Submodule.map_span_le _ _ _).2 ?_ (Submodule.mem_map_of_mem h1))
  rintro _ ⟨Λ, f, hf, rfl⟩
  refine Submodule.subset_span ⟨Λ, f, fun k hk => ?_, rfl⟩
  have : gi k ∈ GlobalTheory.LFun.KGL v (n := 2) := (kgl_map i hv (gi k)).2 (by rwa [hgm])
  exact hf ⟨gi k, this⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem bd_zero : Bd (fun _ : GL (Fin 2) (A E) => (0 : ℂ)) :=
  ⟨continuous_const, fun _ _ => rfl, fun _ _ => ⟨0, fun _ _ _ => by simp⟩⟩

private theorem ii_zero (N : MeasE E) : II N (fun _ => 0) = 0 := by
  simp [II, UI, mean]

private theorem ii_add (N : MeasE E) {Ψ Ψ' : GL (Fin 2) (A E) → ℂ} (h : Bd Ψ) (h' : Bd Ψ') :
    (II N fun x => Ψ x + Ψ' x) = II N Ψ + II N Ψ' := by
  simpa using (iiLaws E N Ψ h).1 Ψ' h' 1

private theorem ii_smul (N : MeasE E) {Ψ : GL (Fin 2) (A E) → ℂ} (h : Bd Ψ) (c : ℂ) :
    (II N fun x => c * Ψ x) = c * II N Ψ := by
  simpa [ii_zero] using (iiLaws E N _ bd_zero).1 Ψ h c

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.pairEx :
    PairEx := by
  intro E _ _ _ D W M N P hn π hπ
  have hb : ∀ (x : span W M π) (y : P.V), Bd fun g => x.1.1 g * y.1.1 g :=
    fun x y => (prodBd E D W M N P π x.1 x.2 y.1 y.2).1
  have hc : ∀ (x : span W M π) (y : P.V), PosC fun g => x.1.1 g * y.1.1 g :=
    fun x y => (prodBd E D W M N P π x.1 x.2 y.1 y.2).2 hπ hn
  have st : IsStable (span W M π) := UpperTheory.ConvolutionTheory.R2.stable ℚ E D W M π
  let B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun x y => II N fun g => x.1.1 g * y.1.1 g)
    (fun x x' y => (congrArg (II N) (funext fun g => add_mul (x.1.1 g) (x'.1.1 g) (y.1.1 g))).trans
      (ii_add N (hb x y) (hb x' y)))
    (fun c x y => (congrArg (II N) (funext fun g => mul_assoc c (x.1.1 g) (y.1.1 g))).trans
      (ii_smul N (hb x y) c))
    (fun x y y' => (congrArg (II N) (funext fun g => mul_add (x.1.1 g) (y.1.1 g) (y'.1.1 g))).trans
      (ii_add N (hb x y) (hb x y')))
    (fun c x y => (congrArg (II N) (funext fun g => mul_left_comm (x.1.1 g) c (y.1.1 g))).trans
      (ii_smul N (hb x y) c))
  have hB : ∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g := fun _ _ => rfl
  refine ⟨B, ⟨st, P.stable, fun k x y => ?_, fun k x y => ?_, fun X x y => ?_⟩, hB, fun x hx => ?_⟩
  · exact (iiLaws E N _ (hb x y)).2 (hc x y) (finGL E 2 k)
  · exact (iiLaws E N _ (hb x y)).2 (hc x y) (infGL E 2 (Unitary.toUnits k))
  · exact iiLie E N x.1 y.1 X (hb x y) (hc x y) (hb ⟨_, st (.lie X) _ x.2⟩ y) (hb x ⟨_, P.stable (.lie X) _ y.2⟩)
  · refine LinearMap.ext fun y => ?_
    have hcx := UpperTheory.ConvolutionTheory.R2.H.spanCont ℚ E D W M π x.1 x.2
    have hk := killW E D x.1.1 hcx.1 hcx.2 hx
    have h0 : ∀ t : (A E)ˣ, (mean N fun g => x.1.1 (g * aE t) * y.1.1 (g * aE t)) = 0 := by
      intro t
      have e : ∫ h in N.D, y.1.1 (gl h * aE t) ∂N.μ = 0 := meanZero decE E D W M N P y.1 y.2 (aE t)
      show ∫ h in N.D, x.1.1 (gl h * aE t) * y.1.1 (gl h * aE t) ∂N.μ = 0
      simp only [hk]
      rw [integral_const_mul, e, mul_zero]
    show (II N fun g => x.1.1 g * y.1.1 g) = 0
    simp [II, UI, h0]
end
