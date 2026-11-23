module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle114
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityUnramifiedOfJetIntegralit
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfB
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.CuspEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem hermC_of_isom (G : Matrix (Fin r) (Fin r) E) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm G v w)
    (τ : E →+* ℂ) (v w : Fin r → ℂ) :
    hermC τ G ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E).map τ *ᵥ w) = hermC τ G v w := by
  rw [GlobalTheory.LevelCusp.hermC_of_herm (ε := 1) (fun v w => by rw [hγ, one_mul]), map_one, one_mul]

theorem lact_mem_dom_of_isom (M : TwoLevels E r U C) {γ : GL (Fin r) E}
    (hγ : ∀ v w, herm M.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = herm M.Gm v w)
    {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact γ x ∈ M.dom := fun τ => by
  have hd : ∀ i, dmin M.Gm (lact γ x) τ i = dmin M.Gm x τ i := fun i => by
    unfold dmin
    congr 1
    ext p q
    exact hermC_of_isom M.Gm hγ τ.1 (col (mat x τ) p) (col (mat x τ) q)
  refine ⟨?_, fun i => by rw [hd]; exact (hx τ).2 i⟩
  have e : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx τ).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem lact_tr_mem (M : TwoLevels E r U C) (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    lact (M.tr u c) x ∈ M.dom :=
  lact_mem_dom_of_isom M (M.tr_herm u c) hx

def Lmap (M : TwoLevels E r U C) (u : U) (c : C) (x : M.dom) : M.dom :=
  ⟨lact (M.tr u c) x.1, lact_tr_mem M u c x.2⟩

def pb (M : TwoLevels E r U C) (u : U) : (C → M.dom → ℂ) →ₐ[ℂ] (C → M.dom → ℂ) where
  toFun f := fun c x => f (u • c) (Lmap M u c x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pb_apply (M : TwoLevels E r U C) (u : U) (f : C → M.dom → ℂ) (c : C) (x : M.dom) :
    pb M u f c x = f (u • c) (Lmap M u c x) := rfl

def IsHol (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∃ G : Frame M.Ψ r → ℂ, DifferentiableOn ℂ G M.dom ∧ ∀ x : M.dom, f c x = G x.1

def IsInv (M : TwoLevels E r U C) (f : C → M.dom → ℂ) : Prop :=
  ∀ c, ∀ γ ∈ (M.comp c).Γ, ∀ (x : M.dom) (hx : lact γ x.1 ∈ M.dom), f c ⟨lact γ x.1, hx⟩ = f c x

def HA (M : TwoLevels E r U C) : Subalgebra ℂ (C → M.dom → ℂ) where
  carrier := {f | IsHol M f ∧ IsInv M f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F * G, hF.mul hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.mul_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
    · obtain ⟨F, hF, hF'⟩ := hf c
      obtain ⟨G, hG, hG'⟩ := hg c
      exact ⟨F + G, hF.add hG, fun x => by simp [hF', hG']⟩
    · simp only [Pi.add_apply]
      rw [hf' c γ hγ x hx, hg' c γ hγ x hx]
  algebraMap_mem' := by
    intro z
    refine ⟨fun c => ⟨fun _ => z, differentiableOn_const z, fun x => rfl⟩, fun c γ hγ x hx => rfl⟩

theorem pb_mem (M : TwoLevels E r U C) (u : U) {f : C → M.dom → ℂ} (hf : f ∈ HA M) : pb M u f ∈ HA M := by
  obtain ⟨hf, hf'⟩ := hf
  refine ⟨fun c => ?_, fun c γ hγ x hx => ?_⟩
  · obtain ⟨G, hG, hG'⟩ := hf (u • c)
    refine ⟨fun y => G (lact (M.tr u c) y),
      hG.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiable_lact _).differentiableOn (fun y hy => lact_tr_mem M u c hy),
      fun x => ?_⟩
    rw [pb_apply, hG']
    rfl
  · have hδ : M.tr u c * γ * (M.tr u c)⁻¹ ∈ (M.comp (u • c)).Γ := (M.tr_conj u c γ).1 hγ
    have e : lact (M.tr u c) (lact γ x.1) = lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) := by
      simp only [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul, ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr u c)⁻¹ (M.tr u c),
        inv_mul_cancel, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_one]
    have hy : lact (M.tr u c * γ * (M.tr u c)⁻¹) (Lmap M u c x).1 ∈ M.dom := by
      show lact (M.tr u c * γ * (M.tr u c)⁻¹) (lact (M.tr u c) x.1) ∈ M.dom
      rw [← e]; exact lact_tr_mem M u c hx
    rw [pb_apply, pb_apply, ← hf' (u • c) _ hδ (Lmap M u c x) hy]
    congr 1
    exact Subtype.ext e

def pbA (M : TwoLevels E r U C) (u : U) : HA M →ₐ[ℂ] HA M where
  toFun f := ⟨pb M u f, pb_mem M u f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def cst (M : TwoLevels E r U C) (a : C → ℂ) : HA M :=
  ⟨fun c _ => a c, fun c => ⟨fun _ => a c, differentiableOn_const _, fun _ => rfl⟩, fun _ _ _ _ _ => rfl⟩

def tw (M : TwoLevels E r U C) (a : C → ℂ) (u : U) : Polynomial (HA M) →ₐ[ℂ] Polynomial (HA M) :=
  { Polynomial.eval₂RingHom (Polynomial.C.comp (pbA M u).toRingHom) (Polynomial.C (cst M a) * Polynomial.X) with
    commutes' := fun z => by
      show Polynomial.eval₂ _ _ (algebraMap ℂ (Polynomial (HA M)) z) = _
      rw [Polynomial.algebraMap_apply, Polynomial.eval₂_C]
      simp }

theorem tw_C (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.C f) = Polynomial.C (pbA M u f) := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_C]
  rfl

theorem tw_X (M : TwoLevels E r U C) (a : C → ℂ) (u : U) :
    tw M a u Polynomial.X = Polynomial.C (cst M a) * Polynomial.X := by
  show Polynomial.eval₂ _ _ _ = _
  rw [Polynomial.eval₂_X]

theorem tw_monomial_one (M : TwoLevels E r U C) (a : C → ℂ) (u : U) (f : HA M) :
    tw M a u (Polynomial.monomial 1 f) = Polynomial.monomial 1 (cst M a * pbA M u f) := by
  rw [← Polynomial.C_mul_X_eq_monomial, map_mul, tw_C, tw_X, ← mul_assoc, ← Polynomial.C_mul, mul_comm (pbA M u f),
    Polynomial.C_mul_X_eq_monomial]

end GlobalTheory.CuspEmb

end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.CancelPow

variable {X Y : Scheme.{0}}

theorem pw_tw (M H : LB X) (t a : ℤ) : AbLaw.pw (tw M H t) a = tw (AbLaw.pw M a) H (t * a) := by
  have : (AbLaw.pw (tw M H t) a).g = (tw (AbLaw.pw M a) H (t * a)).g := by
    funext p q
    change (res _ (M.g p.1 q.1) * (res _ (H.g p.2 q.2 ^ (-t)))⁻¹) ^ a =
      res _ (M.g p.1 q.1 ^ a) * (res _ (H.g p.2 q.2 ^ (-(t * a))))⁻¹
    simp only [map_zpow, map_inv, zpow_neg, inv_inv, zpow_mul]
    exact mul_zpow _ _ _
  exact congrArg (fun g => (⟨(tw M H t).ι, (tw M H t).U, g⟩ : LB X)) this

theorem lbIso_tw_congr_right {A H H' : LB X} (hA : A.IsLB) (t : ℤ) (h : LBIso H H') :
    LBIso (tw A H t) (tw A H' t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ A.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (A.ι × H'.ι) × (A.ι × H.ι), (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 ≤ H'.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (A.ι × H'.ι) × (A.ι × H.ι)), x ∈ (tw A H' t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1 p.2.1) * gm (𝟙 X) x (H'.U p.1.2 ⊓ H.U p.2.2) (w.s (p.1.2, p.2.2)) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine GlobalTheory.LBAlg.lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1 p.2.1) * res (l₂ p) (w.s (p.1.2, p.2.2)) ^ t)
    ?_
  intro x p q h₁ h₂ h₃ h₄
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (GlobalTheory.LBAlg.gm_tw A H' t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (GlobalTheory.LBAlg.gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [GlobalTheory.LBAlg.germs_of_isGen hw x (p.1.2, p.2.2) (q.1.2, q.2.2) h₁.2 h₂.2 h₃.2 h₄.2,
    ← gm_cocycle hA (𝟙 X) x h₁.1 h₂.1 h₃.1, ← gm_cocycle hA (𝟙 X) x h₂.1 h₃.1 h₄.1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem cancel_pw : (∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (H M : LB X) (N : LB Y) (a : ℤ), H.IsLB → M.IsLB → N.IsLB → LBIso (GlobalTheory.AbLaw.pw N a) (H.pull b) → LBIso (GlobalTheory.AbLaw.pw N (a + 1)) (M.pull b) → LBIso N ((GlobalTheory.AbLaw.tw M H (-1)).pull b)) ∧ ∀ (X : Scheme.{0}) (H M : LB X) (a : ℤ), H.IsLB → M.IsLB → LBIso (GlobalTheory.AbLaw.pw H (a + 1)) (GlobalTheory.AbLaw.pw M a) → LBIso H (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M H (-1)) a) := by
  refine ⟨fun X Y b H M N a hH hM hN e₁ e₂ => ?_, fun X H M a hH hM e => ?_⟩
  · have hP : (M.pull b).IsLB := pull_isLB hM b
    have hQ : (H.pull b).IsLB := pull_isLB hH b
    have k₁ : LBIso N (tw (tw N (H.pull b) 1) (H.pull b) (-1)) := GlobalTheory.LBAlg.lbIso_tw_tw hN hQ 1
    have k₂ : LBIso (tw N (H.pull b) 1) (tw N (AbLaw.pw N a) 1) := lbIso_tw_congr_right hN 1 e₁.symm
    have k₃ : tw N (AbLaw.pw N a) 1 = tw N N a := by
      simp only [tw, GlobalTheory.Algebraise.pw_pw]
      congr 2
      ring
    have k₄ : LBIso (tw N N a) (M.pull b) :=
      LBIso.trans (isLB_tw hN hN a) (isLB_pw hN (a + 1)) hP (GlobalTheory.Algebraise.lbIso_tw hN a).symm e₂
    have k₅ : LBIso (tw N (H.pull b) 1) (M.pull b) :=
      LBIso.trans (isLB_tw hN hQ 1) (isLB_tw hN (isLB_pw hN a) 1) hP k₂ (k₃ ▸ k₄)
    have k₆ : LBIso (tw (tw N (H.pull b) 1) (H.pull b) (-1)) (tw (M.pull b) (H.pull b) (-1)) :=
      GlobalTheory.LBAlg.lbIso_tw_congr hQ (-1) k₅
    have k₇ : LBIso (tw (M.pull b) (H.pull b) (-1)) ((tw M H (-1)).pull b) :=
      LBIso.chartPull (GlobalTheory.LBAlg.chartPullTw (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M b b rfl)
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull H b b rfl) (-1))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (tw M H (-1)) b b rfl) (GlobalTheory.LBAlg.lbIso_self (isLB_tw hM hH (-1)))
    exact LBIso.trans hN (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₁
      (LBIso.trans (isLB_tw (isLB_tw hN hQ 1) hQ (-1)) (isLB_tw hP hQ (-1)) (pull_isLB (isLB_tw hM hH (-1)) b) k₆ k₇)
  · have h₁ : LBIso (tw H H a) (AbLaw.pw M a) :=
      LBIso.trans (isLB_tw hH hH a) (isLB_pw hH (a + 1)) (isLB_pw hM a) (GlobalTheory.Algebraise.lbIso_tw hH a).symm e
    have h₂ : LBIso (tw (tw H H a) H (-a)) (tw (AbLaw.pw M a) H (-a)) := GlobalTheory.LBAlg.lbIso_tw_congr hH (-a) h₁
    have h₃ : AbLaw.pw (tw M H (-1)) a = tw (AbLaw.pw M a) H (-a) := by
      rw [pw_tw]
      congr 1
      ring
    rw [h₃]
    exact LBIso.trans hH (isLB_tw (isLB_tw hH hH a) hH (-a)) (isLB_tw (isLB_pw hM a) hH (-a))
      (GlobalTheory.LBAlg.lbIso_tw_tw hH hH a) h₂

end GlobalTheory.CancelPow
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.CrossIso

variable {X Y Z : Scheme.{0}}

theorem gm_pw_g (L : LB X) (t : ℤ) (f : Y ⟶ X) (y : Y) (i j : L.ι) :
    gm f y ((GlobalTheory.AbLaw.pw L t).U i ⊓ (GlobalTheory.AbLaw.pw L t).U j) ((GlobalTheory.AbLaw.pw L t).g i j) =
      gm f y (L.U i ⊓ L.U j) (L.g i j) ^ t :=
  map_zpow (gm f y (L.U i ⊓ L.U j)) (L.g i j) t

theorem gm_pull_g (L : LB X) (F : Y ⟶ X) (f : Z ⟶ Y) (z : Z) (J J' : PUnit → L.ι)
    (hj : F (f z) ∈ L.U (J PUnit.unit)) (hj' : F (f z) ∈ L.U (J' PUnit.unit)) :
    gm f z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f z ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f z _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f z _ hp _).trans
    (gm_pull f F z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem gw_chart {b : Y ⟶ X} {A : LB X} {N : LB Y} {p : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) (k k' : A.ι) (l l' : N.ι) (hk : b (r z) ∈ A.U k) (hk' : b (r z) ∈ A.U k')
    (hl : r z ∈ N.U l) (hl' : r z ∈ N.U l') :
    gw w r z k l = gm (r ≫ b) z _ (A.g k k') * (gm r z _ (N.g l l') ^ p)⁻¹ * gw w r z k' l' := by
  have := (isGen_iff w).1 hw Z r z k k' l l' hk hk' hl hl'
  rw [gm_pw_g] at this
  exact this

theorem cross_alg {G : Type} [CommGroup G] (p q : ℤ) (a a' n u u' : G) :
    (a' * (n ^ q)⁻¹ * u') ^ p * ((a * (n ^ p)⁻¹ * u) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ * (u' ^ p * (u ^ q)⁻¹) := by
  simp only [mul_zpow, inv_zpow, ← zpow_mul, mul_comm q p, mul_inv, inv_inv]
  generalize n ^ (p * q) = m
  generalize a' ^ p = A'
  generalize a ^ q = A
  generalize u' ^ p = U'
  generalize u ^ q = U
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cross_chart {b : Y ⟶ X} {A A' : LB X} {N : LB Y} {p q : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)) (hw : w.IsGen) (hw' : w'.IsGen) (r : Z ⟶ Y) (z : Z)
    (k₁ k₂ : A.ι) (j₁ j₂ : A'.ι) (l₁ l₂ : N.ι) (hk₁ : b (r z) ∈ A.U k₁) (hk₂ : b (r z) ∈ A.U k₂)
    (hj₁ : b (r z) ∈ A'.U j₁) (hj₂ : b (r z) ∈ A'.U j₂) (hl₁ : r z ∈ N.U l₁) (hl₂ : r z ∈ N.U l₂) :
    gw w' r z j₁ l₁ ^ p * (gw w r z k₁ l₁ ^ q)⁻¹ =
      gm (r ≫ b) z _ (A'.g j₁ j₂) ^ p * (gm (r ≫ b) z _ (A.g k₁ k₂) ^ q)⁻¹ *
        (gw w' r z j₂ l₂ ^ p * (gw w r z k₂ l₂ ^ q)⁻¹) := by
  rw [gw_chart w hw r z k₁ k₂ l₁ l₂ hk₁ hk₂ hl₁ hl₂, gw_chart w' hw' r z j₁ j₂ l₁ l₂ hj₁ hj₂ hl₁ hl₂]
  exact cross_alg _ _ _ _ _ _ _

end GlobalTheory.FormalAlg.CrossIso

namespace GlobalTheory.FormalAlg
open CrossIso

theorem exists_crossIso : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  intro X Y b A A' N p q w w' hA hA' hN hw hw'
  have glue : ∀ (j : A'.ι) (k : A.ι), ∃ s : Γ(Y, ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
      ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U j → r z ∈ N.U l →
        gm r z _ s = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ l x, x ∈ W l ↔ b x ∈ A.U k ∧ b x ∈ A'.U j ∧ x ∈ N.U l :=
      ⟨fun l => b ⁻¹ᵁ A.U k ⊓ (b ⁻¹ᵁ A'.U j ⊓ N.U l), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ l, W l ≤ ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
        ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k) := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, mem_pull.2 ((hW l x).1 hx).1⟩
    have l₁ : ∀ l, W l ≤ (A'.pull b).U (fun _ => j) ⊓ (GlobalTheory.AbLaw.pw N q).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, ((hW l x).1 hx).2.2⟩
    have l₂ : ∀ l, W l ≤ (A.pull b).U (fun _ => k) ⊓ (GlobalTheory.AbLaw.pw N p).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).1, ((hW l x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), r z ∈ W l →
        gm r z (W l) (u l) = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ :=
      ⟨fun l => res (l₁ l) (w'.s (fun _ => j, l)) ^ p * (res (l₂ l) (w.s (fun _ => k, l)) ^ q)⁻¹,
        fun Z r z l hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((map_zpow _ _ _).trans (congrArg (· ^ p) (gm_res r z (l₁ l) hy _)))
          ((map_inv _ _).trans (congrArg (·⁻¹)
            ((map_zpow _ _ _).trans (congrArg (· ^ q) (gm_res r z (l₂ l) hy _))))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨l, hl⟩ := exists_chart hN x
        exact Opens.mem_iSup.2 ⟨l, (hW l x).2 ⟨mem_pull.1 hx.2, mem_pull.1 hx.1, hl⟩⟩) u (fun l l' x hx => by
        have h₁ := (hW l x).1 hx.1
        have h₂ := (hW l' x).1 hx.2
        have e := cross_chart w w' hw hw' (𝟙 Y) x k k j j l l' h₁.1 h₁.1 h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hA (𝟙 Y ≫ b) x h₁.1, gm_self hA' (𝟙 Y ≫ b) x h₁.2.1, one_zpow, one_zpow, inv_one, one_mul,
          one_mul] at e
        exact (hu _ (𝟙 Y) x l hx.1).trans (e.trans (hu _ (𝟙 Y) x l' hx.2).symm))
    refine ⟨s, fun Z r z l hk hj hl => ?_⟩
    have hy := (hW l (r z)).2 ⟨hk, hj, hl⟩
    exact (gm_res r z (l₀ l) hy s).symm.trans ((congrArg (gm r z (W l)) (hs l)).trans (hu Z r z l hy))
  choose s hs using glue
  let c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b) :=
    ⟨fun P => s (P.1 PUnit.unit) (P.2 PUnit.unit)⟩
  have hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (K : PUnit → A.ι) (j : A'.ι) (l : N.ι),
      b (r z) ∈ A.U (K PUnit.unit) → b (r z) ∈ A'.U j → r z ∈ N.U l →
      gw c r z j K = gw w' r z j l ^ p * (gw w r z (K PUnit.unit) l ^ q)⁻¹ :=
    fun Z r z K j l hk hj hl => hs j (K PUnit.unit) Z r z l hk hj hl
  refine ⟨c, (isGen_iff c).2 ?_, fun Z r z k j l hk hj hl => hc Z r z (fun _ => k) j l hk hj hl⟩
  intro Z r z j j' K K' hj hj' hK hK'
  obtain ⟨l, hl⟩ := exists_chart hN (r z)
  have hk := mem_pull.1 hK
  have hk' := mem_pull.1 hK'
  have e := cross_chart w w' hw hw' r z (K PUnit.unit) (K' PUnit.unit) j j' l l hk hk' hj hj' hl hl
  refine (hc Z r z K j l hk hj hl).trans (e.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw_g A' p _ z j j').symm (congrArg (·⁻¹) ?_))
    (hc Z r z K' j' l hk' hj' hl).symm
  exact ((gm_pull_g (GlobalTheory.AbLaw.pw A q) b r z K K' hk hk').trans (gm_pw_g A q _ z _ _)).symm

end GlobalTheory.FormalAlg
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_normOne_of_strongApproximation : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  first | exact @GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | exact GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion | (intros; apply GlobalTheory.QSA.DivAssembly.strongApproximation_normOne_divisionQuaternion <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)) (α : G ⟶ G), IsExp y e → IsExp y e' → IsMonHom α → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = e z ≫ α := by
  first | exact @GlobalTheory.ExpLin.existsUnique_linear_lift | exact GlobalTheory.ExpLin.existsUnique_linear_lift | (intros; apply GlobalTheory.ExpLin.existsUnique_linear_lift <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem Charts.tower_preimage_germ : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  intro R _ I Y β n C γ h0 hγ e
  induction e with
  | zero =>
    intro i
    subst_vars
    refine ⟨?_, fun j z _ => ?_⟩
    · rw [h0]; rfl
    · rw [h0]
  | succ e ih =>
    intro i
    obtain ⟨hpre, hgerm⟩ := ih i
    have hp : γ (e + 1) ⁻¹ᵁ C.D (e + 1) i = C.D 0 i := by
      rw [← hγ e, Scheme.Hom.comp_preimage, C.pre, hpre]
    refine ⟨hp, fun j z hz => ?_⟩
    have hz' : γ e z ∈ C.D e i := by rw [← hpre] at hz; exact hz
    have hz'' : β e (γ e z) ∈ C.D (e + 1) i := by
      have : γ e z ∈ β e ⁻¹ᵁ C.D (e + 1) i := by rw [C.pre]; exact hz'
      exact this
    rw [← hgerm j z hz, ← C.ρ_pull e i j, ← hγ e, ← gs_pull (γ e) (β e) z _ hz'',
      ← gs_res (γ e) z (C.pre e i).ge hz']
    rfl

end GlobalTheory.FormalAlg
end

section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne
    (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h₁ : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (h₂ : q' ≫ q = (p : ℤ_[p]) • 𝟙 H)
    (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1)) (he : GlobalTheory.Dieu.HasLogDeg q e) :
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
      e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) :=
  GlobalTheory.Dieu.le_colength_of_htOne p T k G H q q' e h₁ h₂ hF he
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_spherical_cuspForm_whittaker_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  first | exact @GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | exact GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero | (intros; apply GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero <;> assumption)
end

section

open GlobalTheory.LatVal GlobalTheory.LatJet

theorem _root_.GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetInt → LatIntUnr := by
  first | exact @GlobalTheory.LatValUnr.latIntUnr | exact GlobalTheory.LatValUnr.latIntUnr | (intros; apply GlobalTheory.LatValUnr.latIntUnr <;> assumption)
end
