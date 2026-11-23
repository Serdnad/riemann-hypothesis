module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.DensLow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDeg
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle009
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows

@[expose] public section

section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem sm_stable_uh (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  obtain ⟨gg, rfl⟩ := Formalism.IndefR.Eqv.KerDiag.gt_of_uh τ M hg
  exact Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ gg hw

abbrev comp (a : GA D V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (Formalism.IndefR.Eqv.thetaC D τ) a


open Classical in
def translS (a : GA D V) (s : Finset D.what₂.Tau) (v : M.Vec) : M.Vec := fun τ =>
  if τ ∈ s then ⟨M.rep τ (comp a τ) (v τ), sm_stable_uh M τ (Formalism.IndefR.Eqv.infMat_unitary' D V a τ) (v τ).2⟩
  else v τ

def transl (a : GA D V) (v : M.Vec) : M.Vec := translS M a Finset.univ v

theorem transl_apply (a : GA D V) (v : M.Vec) (τ : D.what₂.Tau) :
    (transl M a v τ : M.H τ) = M.rep τ (comp a τ) (v τ) := by
  simp [transl, translS]

variable {M}

theorem equiv_ginf {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {T : MMap M}
    (hT : Formalism.IndefR.AutomorphicEvaluation.EqCont θ M T) {a : GA D V} (ha : a ∈ GinfC V) (v : M.Vec) (y : GA D V) :
    T v (y * a) = T (transl M a v) y := by
  classical
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => comp a τ with hgsd
  have hgs : Formalism.IndefR.Eqv.IsUnitFam D V gs := Formalism.IndefR.Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Formalism.IndefR.Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, ∀ y, T v (y * Formalism.IndefR.Eqv.famH D V _ (hu s)) = T (translS M a s v) y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu ∅) = 1 := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_one]
        convert Formalism.IndefR.Eqv.famM_one D V using 2
        funext τ
        simp
      have e2 : translS M a ∅ v = v := by
        funext τ; simp [translS]
      rw [e, mul_one, e2]
    | insert τ0 s hτ0 ih =>
      intro y
      have e : Formalism.IndefR.Eqv.famH D V _ (hu (insert τ0 s)) =
          Formalism.IndefR.Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Formalism.IndefR.Eqv.famH D V _ (hu s) := by
        apply Formalism.IndefR.Eqv.matA_inj D V
        rw [Formalism.IndefR.Eqv.matA_famH, Formalism.IndefR.Eqv.matA_mul, Formalism.IndefR.Eqv.matA_atH, Formalism.IndefR.Eqv.matA_famH]
        apply Formalism.IndefR.Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Formalism.IndefR.Eqv.psi_famM, Formalism.IndefR.Eqv.psi_atM, Formalism.IndefR.Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Formalism.IndefR.Eqv.fin_famM, Formalism.IndefR.Eqv.fin_atM, Formalism.IndefR.Eqv.fin_famM,
            Matrix.one_mul]
      rw [e, ← mul_assoc, ih]
      have hw : M.rep τ0 (gs τ0) ((translS M a s v τ0 : M.H τ0)) ∈ M.sm τ0 :=
        sm_stable_uh M τ0 (hgs τ0) (translS M a s v τ0).2
      have hq := hT.equiv τ0 (gs τ0) (hgs τ0) (translS M a s v) ⟨_, hw⟩ rfl
      have hq' := congrFun hq y
      simp only [rTr] at hq'
      rw [Formalism.IndefR.Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)] at hq'
      rw [← hq']
      refine congrFun (congrArg T ?_) y
      funext τ
      by_cases h : τ = τ0
      · subst h
        rw [Function.update_self]
        apply Subtype.ext
        simp [translS, hτ0, hgsd]
      · rw [Function.update_of_ne h]
        simp [translS, h]
  have e : a = Formalism.IndefR.Eqv.famH D V _ (hu Finset.univ) :=
    Formalism.IndefR.Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  conv_lhs => rw [e]
  exact key Finset.univ y

section Read

variable {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}
  {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Read

end Formalism.L2.SG.EvalTEquiv

end
end

section

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates

namespace Formalism.L2.SG.EvalTOntoRep

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def IsContRep (f : L2X X) (φ : X.B.I.GA → ℂ) : Prop :=
  Continuous φ ∧ (∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y) ∧ ((f : X.B.I.GA → ℂ) =ᵐ[muX X] φ)

theorem eq_zero_of_ae (ψ : X.B.I.GA → ℂ) (hc : Continuous ψ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, ψ (γ * y) = ψ y)
    (h0 : ψ =ᵐ[muX X] 0) : ψ = 0 := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Count.muA_isHaar X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  set N : Set X.B.I.GA := {y | ψ y ≠ 0} with hNd
  have hN : IsOpen N := isOpen_ne_fun hc continuous_const
  have hfm : MeasurableSet X.B.fund := X.B.fund_spec.1
  have h1 : X.B.I.muA X.B.μf (N ∩ X.B.fund) = 0 := by
    have h0' : ∀ᵐ y ∂(X.B.I.muA X.B.μf), y ∈ X.B.fund → ψ y = 0 := by
      rw [← ae_restrict_iff' hfm]
      exact h0
    rw [ae_iff] at h0'
    refine measure_mono_null (fun y hy => ?_) h0'
    simp only [Set.mem_setOf_eq, Classical.not_imp]
    exact ⟨hy.2, hy.1⟩
  have hsub : N ⊆ ⋃ γ : rr_GF X.B.I, (fun y => (γ : X.B.I.GA) * y) ⁻¹' (N ∩ X.B.fund) := by
    intro y hy
    obtain ⟨γ, hγ, hγy⟩ := X.B.fund_spec.2.1 y
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
    refine ⟨?_, hγy⟩
    show ψ (γ * y) ≠ 0
    rw [hinv γ hγ y]
    exact hy
  have h2 : X.B.I.muA X.B.μf N = 0 := by
    refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
    rw [measure_preimage_mul]
    exact h1
  have h3 : N = ∅ := (hN.measure_eq_zero_iff (X.B.I.muA X.B.μf)).1 h2
  funext y
  by_contra hne
  have : y ∈ N := hne
  rw [h3] at this
  exact this

theorem contRep_unique {f : L2X X} {φ φ' : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X f φ') : φ = φ' := by
  have e := eq_zero_of_ae X (fun y => φ y - φ' y) (h.1.sub h'.1)
    (fun γ hγ y => by simp only [h.2.1 γ hγ y, h'.2.1 γ hγ y])
    ((h.2.2.symm.trans h'.2.2).mono fun y hy => by simp [hy])
  funext y
  exact sub_eq_zero.1 (congrFun e y)

theorem contRep_add {f g : L2X X} {φ ψ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X g ψ) :
    IsContRep X (f + g) (φ + ψ) :=
  ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y],
    (Lp.coeFn_add f g).trans (h.2.2.add h'.2.2)⟩

theorem contRep_smul (a : ℂ) {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) :
    IsContRep X (a • f) (a • φ) :=
  ⟨h.1.const_smul a, fun γ hγ y => by simp [h.2.1 γ hγ y], (Lp.coeFn_smul a f).trans (h.2.2.const_smul a)⟩

theorem contRep_zero : IsContRep X 0 0 :=
  ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero ℂ 2 (muX X)⟩

theorem contRep_reg {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (y : X.B.I.GA) :
    IsContRep X (X.B.R y f) (fun x => φ (x * y)) := by
  have hm : MemLp φ 2 (muX X) := (Lp.memLp f).ae_eq h.2.2
  have ef : f = hm.toLp φ := Lp.ext (h.2.2.trans hm.coeFn_toLp.symm)
  refine ⟨h.1.comp (continuous_mul_const y), fun γ hγ x => by simp only [mul_assoc, h.2.1 γ hγ], ?_⟩
  rw [ef]
  exact Formalism.L2.SG.EvalTReg.reg_toLp_X X φ h.2.1 hm y

end Formalism.L2.SG.EvalTOntoRep

end
end

section

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Formalism.L2.SG.RowsU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure UC where
  c3 : ℝ
  cH : ℝ
  cV : ℝ
  cS : ℝ
  c4 : ℝ
  CaF : ℝ → ℝ
  secondOrderBound : ℝ → ℝ
  ChF : ℝ → ℝ

def c0ND (CT A C0 : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2))

def degenerateConstant (CT : ℝ) (U : UC) : ℝ :=
  let c := max (max (max U.c3 (max (max 1 CT) (|U.cH| + 2))) 1) (max (|U.cH| + 2) (|U.cV| + 2))
  max (max c (4 + (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (6 * c + 2)))
    (max (2 * U.secondOrderBound (9 * c + 3)) |U.CaF (9 * c + 3)|)

def corankOneConstant (CT A C0 CGam : ℝ) (U : UC) : ℝ :=
  let c := max (max U.c3 1) (max (max (|U.cH| + 2) (|U.cV| + 2)) (max (|U.cS| + 2) (|U.c4| + 2)))
  max (max (4 * Real.sqrt A) (2 * Real.sqrt (2 * C0) * c))
    (max (CGam + U.secondOrderBound (9 * c + 3)) (4 + 2 * (c ^ 2 + 2 * max (U.ChF (9 * c + 3) - c) 0) * (c + 1)))

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)
  (Cg cb Cu cT CT C0 A : ℝ)

def UAdm (U : UC) : Prop :=
  (∀ C ≥ U.c3, OwnEv Fm fun C' Cl x i => ∀ u u',
    VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cH) ∧
  (OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
    VanishingOnXAndXPlus.TermVolumeSmallCellBound (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1 (Y x hx i u u') C' Cl Cg cb Cu cT CT C0 A U.cV) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.cS) ∧
  (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A U.c4) ∧
  ∀ Cpr : ℝ, 0 ≤ U.ChF Cpr ∧ 0 ≤ U.CaF Cpr ∧ ∀ δ > 0, OwnEv Fm fun C' Cl x i =>
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr (U.CaF Cpr) (U.secondOrderBound Cpr) (U.ChF Cpr) δ

theorem rowsKBU (U : UC) (hU : UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U) :
    ∀ c ≥ max (max 1 CT) (|U.cH| + 2), OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u',
      Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → rows_KBound (Y x hx i u u') c := by
  intro c hc
  obtain ⟨_, h27, _⟩ := hU
  refine OwnEv.mono ?_ h27
  intro C' Cl x i h hx u u' hH
  have hc1 : 1 ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc
  have hCT : CT ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc
  have hcH : |U.cH| + 2 ≤ c := le_trans (le_max_right _ _) hc
  exact rows_KBound_of (Y x hx i u u') hH (rows_stHH_mono (by linarith [le_abs_self U.cH])
    (by linarith [neg_abs_le U.cH]) (h u u')) hc1 hCT

def c0U (CT A C0 CGam : ℝ) (U : UC) : ℝ := max (c0ND CT A C0 U) (max (degenerateConstant CT U) (corankOneConstant CT A C0 CGam U))

end Fam

end Formalism.L2.SG.RowsU
end
end
