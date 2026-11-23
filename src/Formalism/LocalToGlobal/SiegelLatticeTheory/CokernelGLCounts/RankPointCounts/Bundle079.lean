module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle075
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiberCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle041
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmRepPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle053
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle077

@[expose] public section

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLz_nonempty {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (autLz D F0 Λ).Nonempty := by
  have h1 : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := ⟨one_mem _, fun j => kmap_one _, rfl⟩
  exact ⟨ind F0 h1, (autLz_iff F0 Λ _).2 ⟨1, h1, gmap_one' Λ, rfl⟩⟩

theorem massRows_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  have hne : (Y.what₂ u).Nonempty := ⟨_, (cls_spec (Y.rowsOK u) (latRowLat X u) 1).1⟩
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_pos (fun Λ hΛ => ?_) hne
  haveI := Formalism.L2.SG.Pf.FibreCounting.autLz_finite (Y := Y) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) hΛ
  have hpos : 0 < Nat.card ↥(autLz D (X.Fu u) Λ) := by
    obtain ⟨φ, hφ⟩ := autLz_nonempty (X.Fu u) Λ
    haveI : Nonempty ↥(autLz D (X.Fu u) Λ) := ⟨⟨φ, hφ⟩⟩
    exact Nat.card_pos
  unfold Formalism.MainNotions.S.wRow
  exact inv_pos.2 (Nat.cast_pos.2 hpos)

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_closed {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u)
    (Formalism.L2.SG.Pf.latSurj X u)

end Formalism.L2.SG.MassDataConc
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Code

theorem relIndex_ne_zero_of_code {G : Type*} [Group G] (H A : Subgroup G) {Q : Type*} [Finite Q] (φ : A → Q)
    (hφ : ∀ k k' : A, φ k = φ k' → ((k⁻¹ * k' : A) : G) ∈ H) : H.relIndex A ≠ 0 := by
  classical
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    choose rep hrep using fun v : Set.range φ => v.2
    refine Finite.of_surjective (fun v : Set.range φ => (QuotientGroup.mk (rep v) : A ⧸ H.subgroupOf A)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      refine ⟨⟨φ k, k, rfl⟩, ?_⟩
      show (QuotientGroup.mk (rep ⟨φ k, k, rfl⟩) : A ⧸ H.subgroupOf A) = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hφ _ _ (hrep _)
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

end Code

section Fin

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem R_sub_O {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ (M p).R) : x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  revert hx
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R → _
  rcases hM : (M p).split with _ | g
  · intro hx
    have : x ∈ (M p).L.O := hx
    rwa [hO] at this
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      intro hx
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split] at hx
      rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1]
      exact ⟨hx.1, hx.2.1⟩

def dO {p : PlF D} (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).O :=
  ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c, alg_mem_O hc⟩

theorem finite_quot {p : PlF D} (hA : Agree δ M p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    Finite ((D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) := by
  obtain ⟨hOK, -, -, hO, -, -⟩ := hA
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  obtain ⟨hOo, hOc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top (M p).L
  rw [hO] at hOo hOc
  have : CompactSpace (D.s.atP p).O := isCompact_iff_compactSpace.1 hOc
  have hc' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hopen : IsOpen (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) := by
    have h1 : (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) =
        (fun y : (D.s.atP p).O => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep)) ⁻¹'
          ((D.s.atP p).O : Set (D.s.atP p).Ep) := by
      ext y
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
      rw [Ideal.mem_span_singleton']
      constructor
      · rintro ⟨z, rfl⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * ((z : (D.s.atP p).Ep) * algebraMap _ _ c) ∈ (D.s.atP p).O
        rw [mul_comm (z : (D.s.atP p).Ep), ← mul_assoc, hc', one_mul]
        exact z.2
      · intro hy
        refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep) * algebraMap _ _ c = y
        rw [mul_comm, ← mul_assoc, mul_comm (algebraMap _ _ c), hc', one_mul]
    rw [h1]
    exact hOo.preimage (by fun_prop)
  exact AddSubgroup.quotient_finite_of_isOpen _ hopen

theorem quot_eq {p : PlF D} {c : (D.s.atP p).Fp} {hc : c ∈ 𝒪[(D.s.atP p).Fp]} {x y : (D.s.atP p).O}
    (h : (QuotientAddGroup.mk x : (D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) = QuotientAddGroup.mk y) :
    (y : (D.s.atP p).Ep) - x ∈ latS (D.s.atP p) c := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  refine mem_latS.2 ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_neg] at this
  rw [show (y : (D.s.atP p).Ep) - x = -x + y by ring, ← this]
  show (z : (D.s.atP p).Ep) * algebraMap _ _ c = _
  ring

theorem entIn_int_mul {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (B * X) :=
  entIn_mul (J1 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => O_mul_latS hx hy) (fun i j => hB i j) hX

theorem entIn_mul_int {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (X * B) :=
  entIn_mul (J2 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => by rw [mul_comm]; exact O_mul_latS hy hx) hX
    (fun i j => hB i j)

end Fin

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vector_eq_zero_of_orbital_zero {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (h : OOt t = 0) : (Y.tO u u).vec t = 0 := by
  unfold Full.tO tOf
  dsimp only
  unfold vec ampN
  rw [h]
  simp only [map_zero, smul_zero, ite_self]
  first
    | rfl
    | simp

theorem irrVec_nohyp {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (t : GTu Y u) (ht : ¬ t.relevant) :
    (Y.tO u u).vec t = 0 :=
  vector_eq_zero_of_orbital_zero Y t
    (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
      Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht)

theorem IrrVecC_holds : IrrVecC := by
  intro D X Y u _ _ t _ ht
  exact irrVec_nohyp Y u t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def PhaseAtRep : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)).Finite ∧
    PairVal.phasePair (gS D) L U = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

def PhaseLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U → ∀ p : PlF D,
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E))))

end Steps


variable (D : Formalism.BasicNotions.D7) in
def PsiProdE : Prop :=
  ∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem trace_neg_div (E : Type) [Field E] [NumberField E] (s : E) (g : ℕ) :
    Algebra.trace ℚ E (-(s / (g : E))) = -(Algebra.trace ℚ E s / (g : ℚ)) := by
  have hg : ((g : ℕ) : E) = algebraMap ℚ E (g : ℚ) := by simp
  rw [hg, div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_neg, LinearMap.map_smul, smul_eq_mul]
  ring

theorem phaseAtRep_of (hL : PhaseLoc M δ u u' F0 what₂) (hP : PsiProdE D) : PhaseAtRep M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN
  have hfun : (fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)) = fun p =>
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))) :=
    funext (hL γ w F' L U hrel hgen hN)
  rw [hfun]
  obtain ⟨hf, hp⟩ := hP (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))
  refine ⟨hf, ?_⟩
  rw [hp, trace_neg_div, map_add (f := _)]
  unfold PairVal.phasePair PairVal.psiInf
  rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseProd_of (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hW : PairVal.PhaseWellDef D u u' F0 what₂) (hR : PhaseAtRep M δ u u' F0 what₂) : PhaseProd M δ u u' F0 what₂ := by
  intro γ w hγ
  have hrel := PCount.eligRel_holds γ w hγ
  have hex := normRepElig_of hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  have hpt : ptT γ = hex.choose.1 := by
    unfold ptT nrep
    rw [dite_eq_left hex]
  have hw : hex.choose.1 = w := hpt.symm.trans (FCount.ptT_eq hN hrows hγ hrel)
  have h0 : PairVal.NormRep γ w hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 := by
    have := hex.choose_spec
    rw [hw] at this
    exact this
  obtain ⟨hf, hp⟩ := hR γ w _ _ _ hrel hγ.1.1 h0
  have hyT : ∀ p, yT M δ u u' F0 what₂ γ p =
      CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) hex.choose.2.1) * sgnP p := fun p => by
    unfold yT; rw [hz]
  simp only [hyT]
  refine ⟨hf, ?_⟩
  refine Eq.trans ?_ hp
  have hex1 : ∃ x : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) × PairVal.MatR D × PairVal.MatR D,
      PairVal.NormRep γ w x.1 x.2.1 x.2.2 := ⟨(hex.choose.2.1, hex.choose.2.2.1, hex.choose.2.2.2), h0⟩
  unfold PairVal.phaseAt
  rw [dite_eq_left hex1]
  exact hW γ w hrel _ _ _ _ _ _ hex1.choose_spec h0

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.LiftCellVolume

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem lemmaVLiftC_of (hRC : Formalism.L2.SG.TermOp.Vanish.RCocompactC) {D : D7} (X : HidaSetting D)
    (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ := by
  intro R ρ s hs
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds hRC Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y s.1 hs

theorem LemmaVLiftC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ :=
  lemmaVLiftC_of Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds X Y u u' κ

end Formalism.L2.SG.Pf.LiftCellVolume
end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem omega_part_holds : OmPart Zd u u' F0 what₂ :=
  omPart_of Zd (modeMatrixDet_eq_adjointDet Zd u u' F0 what₂) (omega_local_holds Zd u u' F0 what₂) (omega_representative_holds u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem localSign_sq (p : PlF D) (a : Fin (D.R.rS + 1)) : TermLoc.sgnP D p a * TermLoc.sgnP D p a = 1 := by
  unfold TermLoc.sgnP
  split
  · rename_i sg _
    rw [← map_mul, Prod.mk_mul_mk, Formalism.L2.SG.Pf.FibD.neg_one_pow_sq, one_mul]
    exact map_one sg.e.symm
  · exact one_mul 1

theorem hu_all (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) :=
  IsUnit.mul ⟨Units.mkOfMulEqOne _ _ (localSign_sq p a), rfl⟩
    (Formalism.L2.SG.Pf.StabShape.frFac_unit Zd.δ Zd.M (Zd.agree p) a)

theorem frame_mem_UUE {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (G : LFlag (D.sp.Y 0) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    frame G b ∈ UUE Λ F (liftF G) := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_lastG]
    apply Submodule.subset_span
    show G.fl.z ∈ (UU Λ F (liftF G) : Set (VS D).V)
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  | cast i =>
    rw [frame_csG]
    haveI := hΛ
    obtain ⟨s, hs, hsv⟩ := Formalism.L2.SG.Pf.exists_smul_mem Λ (G.fl.e i)
    have hX : s • G.fl.e i ∈ UU Λ F (liftF G) := by
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hsv, ?_⟩)
      show s • G.fl.e i ∈ (Xsp (liftF G) : Set (VS D).V)
      exact Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : ((s : D.host.E)) ≠ 0 := by exact_mod_cast hs
    have e : G.fl.e i = ((s : D.host.E))⁻¹ • (s • G.fl.e i) := by
      rw [← algebraMap_smul (R := 𝓞 D.host.E) D.host.E s (G.fl.e i), smul_smul]
      show G.fl.e i = (((s : D.host.E))⁻¹ * algebraMap (𝓞 D.host.E) D.host.E s) • G.fl.e i
      rw [show algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) from rfl, inv_mul_cancel₀ hs', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end
