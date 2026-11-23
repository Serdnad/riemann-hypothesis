module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle023
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut Formalism.L2.SG.Pf.BridgeRat

namespace Formalism.L2.SG.Pf.BridgeAR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_of_coprime {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {c : ℕ}
    (hc : Nat.Coprime c X.B.g) (hZ : ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t)) :
    ZMod' X.B.I X.B.g t := by
  obtain ⟨s, hs, hcs⟩ := hZ
  have hb := Nat.gcd_eq_gcd_ab c X.B.g
  rw [hc.gcd_eq_one, Nat.cast_one] at hb
  have hb' : (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    have h1 := congrArg (Int.cast : ℤ → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) hb
    push_cast at h1
    exact h1
  refine ⟨(Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s +
    (Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t, ?_, ?_⟩
  · exact (IntAf X.B.I.F X.B.I.E).add_mem
      ((IntAf X.B.I.F X.B.I.E).mul_mem (intCast_mem _ _) hs)
      ((IntAf X.B.I.F X.B.I.E).mul_mem (intCast_mem _ _) ht)
  · calc t = 1 * t := (one_mul t).symm
      _ = ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) * (Nat.gcdA c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
            ((Nat.gcdB c X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) := by
        rw [hb']
        ring
      _ = _ := by
        rw [hcs]
        ring

end Formalism.L2.SG.Pf.BridgeAR

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.BridgeAR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaBridgeARC_holds : IotaBridgeARC := by
  intro D X Y u Λ hΛ β b hb hK hN hT x hx
  set A : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) * X.xu u with hAdef
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf := fun y => by
    have := (Y.cs u).lat_eq ((Y.cs u).base Λ) y
    rw [hbl] at this
    exact this
  have hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)) := fun a => by
    unfold hat
    exact fixes_inv X (fixes_mul X (((Y.cs u).h ((Y.cs u).base Λ)).2 _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      ((X.xu_fix u a).1))
  have hTF : ∀ a, (X.Fu u).e a = X.eX a := (Formalism.L2.SG.Full.Full.frameTie (X := X) u u).1
  have hFC : IsFixedConv Λ (gS D) (lf D (X.Fu u)) := ((Y.rowsOK u).1 Λ hΛ).2.1.2.2.2
  refine ratFromAd X A hlat hfixE hFC hTF ?_
  rw [hat_sub, hat_ratLink X A hb, show X.B.I.fmat (A⁻¹ * b.2 * A) *ᵥ hat X A x - hat X A x =
    (X.B.I.fmat (A⁻¹ * b.2 * A) - 1) *ᵥ hat X A x by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
  have hxΛ : x ∈ Λ := hx.1
  have hw : hat X A x ∈ X.B.I.Lf := (hlat x).1 hxΛ
  refine Formalism.L2.SG.Pf.BridgeAd.adFull_of_adTriv Y.TR hK hN hT hw (fun a => ?_)

  have hxo : x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := hx.2
  have h0 : (VS D).hT (X.eX a) x = 0 := by
    have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
      rw [← hTF a]
      exact Submodule.subset_span ⟨a, rfl⟩
    have := (Submodule.mem_iInf _).1 hxo (X.eX a)
    exact (Submodule.mem_iInf _).1 this hmem
  have hE0 : hA X.B.I (incl X.B.I (X.crd (X.eX a))) (hat X A x) = 0 := by
    rw [← hfixE a, hA_hat, h0, map_zero, map_zero]
  obtain ⟨c, hc, hcd⟩ := (X.basisApprox a).1
  have hint : hA X.B.I (X.e0 a) (hat X A x) ∈ IntAf X.B.I.F X.B.I.E := hA_int X.B.I (X.vectorsInLattice.1 a).1 hw
  refine Z_of_coprime X hint hc ?_
  have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 a) (hat X A x) =
      hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.crd (X.eX a)))) (hat X A x) := by
    rw [hA_smul_left, hA_sub_left, hE0, sub_zero, map_natCast]
  rw [e]
  exact Z_hA_mL X hcd hw

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFrameIota

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Proj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_span_zero (e : Fin r → S.V) (v : S.V) (h : ∀ b, S.hT (e b) v = 0) :
    ∀ x ∈ Submodule.span E (Set.range e), S.hT x v = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem proj_exists (Λ : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {T' : E} (F' : LFlag S r T') :
    ∃ u : Fin r → S.V, ∀ l ∈ Λ, l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ Lrep Λ F' := by
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (Xsp F')
  have li := F'.fl.e_indep
  have hmem : ∀ y : Λ, ((ρ y : Λ) : S.V) ∈ Submodule.span E (Set.range F'.fl.e) := fun y => hρX y

  let co : Fin r → Λ →ₗ[𝓞 E] E := fun a =>
    { toFun := fun y => li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a
      map_add' := fun y y' => by
        have e : (⟨((ρ (y + y') : Λ) : S.V), hmem (y + y')⟩ : Submodule.span E (Set.range F'.fl.e)) =
            ⟨((ρ y : Λ) : S.V), hmem y⟩ + ⟨((ρ y' : Λ) : S.V), hmem y'⟩ :=
          Subtype.ext (by simp only [map_add (f := _), Submodule.coe_add])
        rw [e, map_add (f := _), Finsupp.add_apply]
      map_smul' := fun c y => by
        have e : (⟨((ρ (c • y) : Λ) : S.V), hmem (c • y)⟩ : Submodule.span E (Set.range F'.fl.e)) =
            (algebraMap (𝓞 E) E c) • ⟨((ρ y : Λ) : S.V), hmem y⟩ :=
          Subtype.ext (by
            show ((ρ (c • y) : Λ) : S.V) = (algebraMap (𝓞 E) E c) • ((ρ y : Λ) : S.V)
            rw [LinearMap.map_smul, Submodule.coe_smul, algebraMap_smul])
        rw [e, LinearMap.map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  have hco : ∀ a y, co a y = li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a := fun _ _ => rfl
  have hexp : ∀ y : Λ, ((ρ y : Λ) : S.V) = ∑ a, co a y • F'.fl.e a := by
    intro y
    have h := li.linearCombination_repr ⟨((ρ y : Λ) : S.V), hmem y⟩
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ (fun i (c : E) => c • F'.fl.e i) (fun i => zero_smul E _)] at h
    rw [← h]
    rfl
  have hR := fun a => PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top (co a)
  choose u hu using hR

  have hdual : ∀ a b, S.hT (F'.fl.e b) (u a) = if a = b then 1 else 0 := by
    intro a b
    obtain ⟨d, hd0, hdΛ⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hL.span_eq_top (F'.fl.e b)
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
    have hdX : d • F'.fl.e b ∈ Xsp F' := by
      rw [← algebraMap_smul E d]
      exact (Xsp F').smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
    have hρd : ρ ⟨d • F'.fl.e b, hdΛ⟩ = ⟨d • F'.fl.e b, hdΛ⟩ := hρid _ hdX
    have hrep : co a ⟨d • F'.fl.e b, hdΛ⟩ = (d : E) * (if b = a then 1 else 0) := by
      rw [hco]
      have e : (⟨((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V), hmem _⟩ : Submodule.span E (Set.range F'.fl.e)) =
          ((d : 𝓞 E) : E) • ⟨F'.fl.e b, Submodule.subset_span ⟨b, rfl⟩⟩ :=
        Subtype.ext (by
          show ((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V) = ((d : 𝓞 E) : E) • F'.fl.e b
          rw [hρd]
          exact (algebraMap_smul E d _).symm)
      rw [e, LinearMap.map_smul, li.repr_eq_single b _ rfl, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
    have h1 := hu a (d • F'.fl.e b) hdΛ
    rw [hrep, ← algebraMap_smul E d, LinearMap.map_smul, smul_eq_mul] at h1
    have h2 : S.hT (u a) (F'.fl.e b) = if b = a then 1 else 0 := mul_left_cancel₀ hdE h1
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'', h2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]
  refine ⟨u, fun l hl => ⟨?_, ?_⟩⟩
  ·
    refine Λ.sub_mem hl ?_
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hval : S.hT y (∑ a, S.hT (F'.fl.e a) l • u a) = S.hT ((ρ ⟨y, hy⟩ : Λ) : S.V) l := by

      rw [hexp, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (u a) y, hu a y hy, starRingEnd_apply, mul_comm]
    rw [hval]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val hU (ρ ⟨y, hy⟩).2 hl
    rw [← ho, Submodule.mem_one]
    exact ⟨o, rfl⟩
  ·
    show l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ orth S (Xsp F')
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
    refine hT_span_zero F'.fl.e _ fun b => ?_

    rw [map_sub, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]

end Proj

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glob_beta {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hc' : IsFixedConv Λ (gS D) F') (hc'' : IsFixedConv Λ (gS D) F'')
    (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) :
    ∀ w ∈ Lrep Λ F', β w - w ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
  intro w hw
  have hg : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨l, hl, hlw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_gen Λ hF.1 hF.2.1 (gS D) hg F F' hF.2.2.2 ha' w hw
  have h2 := (hP.2.2.2 w hw l hl).1 hlw
  have hle : ∀ F₁ : LFlag (D.sp.Y 0) D.R.rS T', IsAdmissible Λ (gS D) F F₁ → IsFixedConv Λ (gS D) F₁ →
      NgX Λ (gS D) F F₁ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
    intro F₁ ha hc
    unfold NgX
    exact sup_le le_rfl (Formalism.L2.SG.Pf.Act.xlam_le Λ (gS D) ha hF.2.2.2 hc)
  have e : β w - w = (l - w) - (l - β w) := by abel
  rw [e]
  exact Submodule.sub_mem _ (hle F' ha' hc' hlw) (hle F'' ha'' hc'' h2)

end D7

end Formalism.L2.SG.Pf.ScalarFrameIota
end
end
