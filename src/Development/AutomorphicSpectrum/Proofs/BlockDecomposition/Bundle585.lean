module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle344
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle048
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle553
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle575
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle568
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle565
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle508
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle574
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.DualQuot

theorem exists_subquotient_dual_nu : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (S : IrrRep (GL (Fin n) k))
    (A' : Representation ℂ (GL (Fin n) k) V'), IsSmooth A' → ∀ B : S.V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ g w w', B (S.ρ g w) (A' g w') = ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B w w') → B ≠ 0 →
    ∃ Q : IrrRep (GL (Fin n) k), IsSubquotient Q.ρ A' ∧
      IrrGL.of Q.ρ Q.smooth Q.irr = (dualCl (IrrGL.of S.ρ S.smooth S.irr)).nu (s : ℂ) := by
  intro k _ _ _ _ n s V' _ _ S A' hA' B hB hB0
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hAd : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have hχ : IsSmoothChar (absPow k (s : ℂ)) := isSmoothChar_absPow _
  have hχ' : IsSmoothChar (absPow k (-(s : ℂ))) := isSmoothChar_absPow _
  have hprod : ∀ g : GL (Fin n) k, ((detChar (Fin n) (absPow k (-(s : ℂ))) g : ℂˣ) : ℂ) *
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) = 1 := by
    intro g
    rw [absPow_neg, detChar_apply, detChar_apply, MonoidHom.inv_apply]
    simp
  have hT := isSmooth_twist hA' hχ'.detChar
  have hBT : ∀ g a b, B (S.ρ g a) (_root_.GlobalTheory.SmGL.twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g b) = B a b := by
    intro g a b
    rw [twist_apply, map_smul, hB, smul_eq_mul, ← mul_assoc, hprod, one_mul]
  let f := GlobalTheory.InvPairing.pairMap S.ρ hT B hBT
  have hc := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hAd S.ρ S.smooth S.irr
  have hsurj : Function.Surjective f := by
    let R : Subrepresentation (contra S.ρ) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨_root_.GlobalTheory.SmGL.twist A' (detChar (Fin n) (absPow k (-(s : ℂ)))) g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hc.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (GlobalTheory.InvPairing.eq_zero_of_pairMap S.ρ hT B hBT fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩
  let F : A'.IntertwiningMap (_root_.GlobalTheory.SmGL.twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ)))) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun g => by
        refine LinearMap.ext fun w => ?_
        have h := LinearMap.congr_fun (f.isIntertwining' g) w
        simp only [LinearMap.comp_apply, twist_apply, map_smul] at h ⊢
        rw [← h, smul_smul, mul_comm, hprod, one_smul] }
  refine ⟨⟨_, _root_.GlobalTheory.SmGL.twist (contra S.ρ) (detChar (Fin n) (absPow k (s : ℂ))),
    isSmooth_twist (isSmooth_contra _) hχ.detChar, isIrreducible_twist hc _⟩,
    IsSubquotient.of_surjective F hsurj, ?_⟩
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hAd, IrrGL.nu, IrrGL.tw_of]
  exact IrrGL.of_eq_of.2
    ⟨(twistEquiv (GlobalTheory.ContraRefl.contraEquiv (IrrGL.equivOf S.ρ S.smooth S.irr)) _).symm⟩

end GlobalTheory.CompanionTheory.DualQuot

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinTestTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC GlobalTheory.CompanionTheory.FinLevelTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem exists_lift (Y : ∀ w : Pl E, GLw n w) (hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w (n := n)) :
    ∃ x : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) x = Y w := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun w => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem eventually_mem_KGL (g : GL (Fin n) (Af E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem coe_pair_compact_subgroup (a b : ℕ) (w : Pl E) : (K2 a b w : Set (GLw a w × GLw b w)) =
    (GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)) := Subgroup.coe_prod _ _

theorem mem_prod_Kf {x : Gf E a b} :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ w : Pl E, atHom a b w x ∈ K2 a b w := by
  simp only [Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap, forall_and]
  rfl

theorem isRestrW (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (atHom (E := E) a b) (K2 a b) := by
  have hset : {x : Gf E a b | ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
      (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
    Set.ext fun x => (mem_prod_Kf (x := x)).symm.trans Subgroup.mem_prod
  refine ⟨fun w => w.elim, continuous_atHom, fun w => ?_, fun w => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  · exact Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.fst (H w))
      (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.snd (H w))
  · filter_upwards [eventually_mem_KGL x.1, eventually_mem_KGL x.2] with w h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun w => (y w).1) (hy.mono fun w h => h.1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun w => (y w).2) (hy.mono fun w h => h.2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun w => Prod.ext (h₁ w) (h₂ w)⟩
  · rw [hset]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← hset]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf

theorem eventually_eq_indicator {φ : Fam E a b} (h : IsTestP φ) :
    ∀ᶠ w : Pl E in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact h.2

theorem hasCompactSupport_loc {φ : Fam E a b} (h : IsTestP φ) (w : Pl E) : HasCompactSupport (φ w) := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact (h.1 w).1

theorem factors_ne_zero {S : Set (Pl E)} {φ₁ φ₂ : Fam E a b} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) {y : Gf E a b}
    (hy : finFn S φ₁ φ₂ y ≠ 0) (w : Pl E) (hw : w ∈ S) :
    φ₁ w (atW w y) ≠ 0 ∧ (IsSplitAt w → φ₂ w (atW w (thP E a b y)) ≠ 0) := by
  set g : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg
  have hone : ∀ᶠ w in cofinite, g w = 1 := by
    filter_upwards [eventually_eq_indicator h₁, eventually_eq_indicator h₂, (isRestrW a b).eventually_mem y,
      (isRestrW a b).eventually_mem (thP E a b y)] with w e₁ e₂ m₁ m₂
    have m₁' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₁
    have m₂' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₂
    simp only [hg]
    rw [e₁, e₂, Set.indicator_of_mem m₁', Set.indicator_of_mem m₂']
    simp
  have hfin : (S ∩ Function.mulSupport g).Finite :=
    (eventually_cofinite.1 hone).subset fun w hw => hw.2
  have hz : g w ≠ 0 := by
    intro h0
    apply hy
    change ∏ᶠ w ∈ S, g w = 0
    rw [finprod_mem_eq_prod g hfin]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 ⟨hw, by simp [Function.mem_mulSupport, h0]⟩) h0
  refine ⟨left_ne_zero_of_mul hz, fun hs => ?_⟩
  have hz' := right_ne_zero_of_mul hz
  rwa [if_pos hs] at hz'

end GlobalTheory.CompanionTheory.FinTestTw

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeAct

theorem hint_mul_const {H : Type} [Group H] (K : Subgroup H) (v : H → ℂ) (c : ℂ) :
    hint K (fun z => v z * c) = hint K v * c := by
  by_cases hc : c = 0
  · subst hc
    simp [hint]
  have hS : rStab (fun z => v z * c) = rStab v := by
    ext k
    constructor
    · intro hk z
      exact mul_right_cancel₀ hc (hk z)
    · intro hk z
      show v (z * k) * c = v z * c
      rw [hk z]
  unfold hint
  rw [hS, mul_assoc]
  congr 1
  have e := smul_finsum c (fun q : H ⧸ rStab v ⊓ K => v q.out)
  simp only [smul_eq_mul] at e
  rw [mul_comm, e]
  exact finsum_congr fun q => mul_comm _ _

theorem relIndex_eq_card {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') : K'.relIndex K = X.card := by
  let φ : {x // x ∈ X} → K ⧸ K'.subgroupOf K := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ K'.subgroupOf K)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxy)
      exact Subtype.ext ((hX y.1 (hXK _ y.2)).unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  show Nat.card (K ⧸ K'.subgroupOf K) = _
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem finsum_left {G : Type} [Group G] (K' : Subgroup G) (φ : G → ℂ) (hφ : ∀ g, ∀ k ∈ K', φ (g * k) = φ g) (x : G) :
    ∑ᶠ q : G ⧸ K', φ (x * q.out) = ∑ᶠ q : G ⧸ K', φ q.out := by
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (G ⧸ K')))
  refine finsum_congr fun q => ?_
  have e : (MulAction.toPerm x : Equiv.Perm (G ⧸ K')) q = ((x * q.out : G) : G ⧸ K') := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [e]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (x * q.out)
  show φ (x * q.out) = φ ((x * q.out : G) : G ⧸ K').out
  rw [hs, hφ _ _ s.2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ind_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GLw a w × GLw b w) W)
    (u : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom))
    (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (g : GLw n w) :
    u.1.1 (blk h w m Y * g) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) • ρ m (u.1.1 g) := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) (GlobalTheory.LeviFubini.levH_blk h w m Y)
    simpa [GlobalTheory.LeviFubini.levH] using this
  have := GlobalTheory.SmGL.parInd_law _ _ u ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ g
  rw [hl] at this
  rw [GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w m]
  simpa using this

theorem hk_ind_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W), ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X, ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y)) := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX W _ _ ρ f hf u hu x hx lw
  have hfr : ∀ g, ∀ k ∈ K', f (g * k) = f g := fun g k hk => by
    simpa using hf.2.2.2 1 K'.one_mem k hk g
  have hur : ∀ g, ∀ k ∈ K', u.1.1 (g * k) = u.1.1 g := fun g k hk => by
    have h1 : GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ k u = u := (hu ⟨k, hk⟩).trans (one_smul ℂ u)
    exact congrArg (fun v : GlobalTheory.SmGL.IndSp _ _ => v.1.1 g) h1

  set φ : GLw n w → ℂ := fun g => f (x⁻¹ * g) * lw (u.1.1 g) with hφdef
  have hφr : ∀ g, ∀ k ∈ K', φ (g * k) = φ g := fun g k hk => by
    simp only [hφdef]
    rw [← mul_assoc, hfr _ k hk, hur g k hk]
  have hφc : HasCompactSupport φ := by
    have h1 : HasCompactSupport fun g => f (x⁻¹ * g) := hf.2.2.1.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    exact h1.mul_right
  have hcard : K'.relIndex (GlobalTheory.LFun.KGL w (n := n)) = X.card := relIndex_eq_card _ K' X hXK hX
  have hX0 : X.card ≠ 0 := by
    obtain ⟨z, ⟨hz, -⟩, -⟩ := hX 1 (GlobalTheory.LFun.KGL w (n := n)).one_mem
    exact (Finset.card_pos.2 ⟨z, hz⟩).ne'
  have hX0' : (X.card : ℂ) ≠ 0 := by exact_mod_cast hX0

  let Ψ : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] ℂ :=
    { toFun := fun v => lw (v.1.1 x)
      map_add' := fun v v' => map_add lw _ _
      map_smul' := fun c v => map_smul lw c _ }
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen f hf.2.2.1
  have e1 : lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ᶠ q : GLw n w ⧸ K', φ (x * q.out) := by
    show Ψ (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u) = _
    unfold hk
    refine (Ψ.toAddMonoidHom.map_finsum (hfin.subset fun q hq h0 => hq (by
      have h0' : f q.out = 0 := h0
      show f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u = 0
      rw [h0', zero_smul]))).trans ?_
    refine finsum_congr fun q => ?_
    show Ψ (f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u) = _
    rw [map_smul]
    simp only [hφdef, inv_mul_cancel_left]
    rfl
  have e2 := GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le (GlobalTheory.LFun.KGL w (n := n)) K' φ hle (fun k hk g => hφr g k hk)
    (by rw [hcard]; exact hX0) (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen φ hφc)
  have e3 := GlobalTheory.T.hecke_coset_sum_compact E n a b h w K' hopen hle hnorm X hXK hX φ hφr hφc
  rw [hcard] at e2
  have e4 : ∑ᶠ q : GLw n w ⧸ K', φ q.out =
      ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) fun m =>
        hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
    have := e2.symm.trans e3
    exact mul_left_cancel₀ (inv_ne_zero hX0') this
  rw [e1, finsum_left K' φ hφr x, e4]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  funext m
  have e5 : (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      φ (blk h w m (Multiplicative.toAdd Y) * y)) = fun Y =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y) *
        (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * lw (ρ m (u.1.1 y))) := by
    funext Y
    simp only [hφdef]
    rw [ind_blk h w ρ u m _ y, map_smul, smul_eq_mul, mul_assoc]
  rw [e5, hint_mul_const]
  unfold phi3
  ring

end GlobalTheory.CompanionTheory.HeckeAct
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.RegroupFin

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp [PhiU, GlobalTheory.Tw.Phi, GeneralLinearGroup.map, apply_ite f]

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  have h1 : ∀ x : GL (Fin n) R, GeneralLinearGroup.map f (invT n R x) = invT n S (GeneralLinearGroup.map f x) := by
    intro x
    apply Units.ext
    ext i j
    have e : (GeneralLinearGroup.map f x)⁻¹ = GeneralLinearGroup.map f x⁻¹ := (map_inv _ x).symm
    simp only [invT, MonoidHom.coe_mk, OneHom.coe_mk, e]
    rfl
  have h2 : GeneralLinearGroup.map f (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map f g) := by
    apply Units.ext
    ext i j
    exact h _
  have h3 : ∀ (T : Type) [CommRing T] (d : T →+* T) (x : GL (Fin n) T),
      thetaGL n d x = PhiU n T * invT n T (GeneralLinearGroup.map d x) * (PhiU n T)⁻¹ := fun _ _ _ _ => rfl
  rw [h3, h3, map_mul, map_mul, map_inv, map_phiU, h1, h2]

theorem evw_pv (v : PlF E) (w : Above v) (y : Gf E a b) : evw w (pv a b v y) = atW w.1 y := by
  refine Prod.ext ?_ ?_ <;> · apply Units.ext; ext i j; rfl

theorem cjv_spec (hc : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hc E v
  unfold cjv
  rw [dite_eq_left h]
  exact h.choose_spec.2 x

theorem pv_thP (hc : CjEx) (v : PlF E) (y : Gf E a b) : pv a b v (thP E a b y) = thv a b v (pv a b v y) :=
  Prod.ext (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) a y.1) (map_thetaGL (projv v) _ (cjv v) (cjv_spec hc v) b y.2)

theorem finprod_fibres {X Y : Type} (u : X → Y) (S : Set X) (hu : Set.InjOn u S) (F : X → ℂ) :
    ∏ᶠ w ∈ S, F w = ∏ᶠ v : Y, ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 := by
  set G : Y → ℂ := fun v => ∏ᶠ (w : {w : X // u w = v}) (_ : w.1 ∈ S), F w.1 with hG
  have hone : ∀ v, v ∉ u '' S → G v = 1 := by
    intro v hv
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have hw : w.1 ∉ S := fun hw => hv ⟨w.1, hw, w.2⟩
    simp [hw]
  have hval : ∀ w ∈ S, G (u w) = F w := by
    intro w hw
    have hs : {i : {x : X // u x = u w} | i.1 ∈ S} = {⟨w, rfl⟩} := by
      ext i
      change i.1 ∈ S ↔ i = ⟨w, rfl⟩
      constructor
      · intro hi
        exact Subtype.ext (hu hi hw i.2)
      · rintro rfl
        exact hw
    have : G (u w) = ∏ᶠ i ∈ {i : {x : X // u x = u w} | i.1 ∈ S}, F i.1 := rfl
    rw [this, hs, finprod_mem_singleton]
  have h1 : ∏ᶠ v, G v = ∏ᶠ v ∈ u '' S, G v := by
    rw [← finprod_mem_univ]
    refine finprod_mem_inter_mulSupport_eq' _ _ _ fun v hv => ?_
    simp only [Set.mem_univ, true_iff]
    by_contra hn
    exact hv (hone v hn)
  rw [h1, finprod_mem_image hu]
  exact (finprod_mem_congr rfl hval).symm

theorem regroup_of_cjEx (hc : CjEx) : Regroup := by
  intro E _ _ _ a b S hS φ₁ φ₂ _ _ y
  have hinj : Set.InjOn (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) S := by
    intro u hu u' hu' h
    obtain ⟨x, -, hx⟩ := hS u
    exact (hx u ⟨hu, rfl⟩).trans (hx u' ⟨hu', h.symm⟩).symm
  unfold finFn
  rw [finprod_fibres _ S hinj]
  refine finprod_congr fun v => ?_
  unfold fv
  refine finprod_congr fun w => finprod_congr fun _ => ?_
  rw [evw_pv, ← pv_thP hc, evw_pv]

theorem regroup : Regroup := regroup_of_cjEx GlobalTheory.CompanionTheory.CjEx.cjEx

end GlobalTheory.CompanionTheory.RegroupFin

end
end
