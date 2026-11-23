module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.Unfold.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gmap_one (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) Λ = Λ := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul (a b : GV D) (Λ : LV D) : Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem adapt_one {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Adapt (1 : GV D) F F :=
  ⟨Subgroup.one_mem _, fun a => by simp⟩

theorem unitriangular_lattice_stabiliser_sub_frame_automorphisms {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : LV D) : NLam Λ F ⊆ Aut0 F Λ := by
  rintro n ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨⟨h1, fun a => ?_⟩, h2⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, frame, FlagG.fvec, Fin.snoc_last, LinearMap.mem_ker]
      intro x hx
      refine Submodule.span_induction (p := fun x _ => (VS D).hT x F.fl.z = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨a, rfl⟩; exact F.fl.z_orth a
      · simp
      · intro x y _ _ a b; simp [a, b]
      · intro c x _ a; simp [a]
    have := h4 _ hz
    have e : Xflag F (Fin.last D.R.rS).val = Xsp F := by
      simp only [Xflag, FlagG.Xa, Xsp, FlagG.X, Fin.val_last]
      congr 1; ext v; simp
    rwa [e]
  · apply h3
    apply Submodule.subset_span
    exact ⟨i, by simp, by simp [frame, FlagG.fvec]⟩

section
variable {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

theorem mem_gmap (h : GV D) (Λ : LV D) (x) : x ∈ Formalism.HermitianLatticesTheory.gmap h Λ ↔ h.symm x ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro hx; exact ⟨_, hx, by simp⟩

theorem gmap_sup (h : GV D) (A B : LV D) : Formalism.HermitianLatticesTheory.gmap h (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap h A ⊔ Formalism.HermitianLatticesTheory.gmap h B :=
  Submodule.map_sup _ _ _

variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}

theorem h_add_right (p : PlF D) (x y y' : Vp D p) : (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _ + LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]

theorem h_smul_right (p : PlF D) (c) (x y : Vp D p) : (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  show LocFacts₂ _ _ _ _ = _ * LocFacts₂ _ _ _ _
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_unitary {p : PlF D} {h : GV D} (hh : h ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {g} (hg : Ext p h g) :
    LocNG.IsUnitary (locH Z p) g := by
  have key : ∀ a b, (locH Z p).h (g (baseChange₂ D p a)) (g (baseChange₂ D p b)) = (locH Z p).h (baseChange₂ D p a) (baseChange₂ D p b) := by
    intro a b
    rw [hg, hg]
    show LocFacts₂ _ _ _ _ = LocFacts₂ _ _ _ _
    rw [baseChangeAt_form _ _ (Z.hcj p), baseChangeAt_form _ _ (Z.hcj p)]
    simp only [brS]; rw [hh]
  have z1 : ∀ y, (locH Z p).h 0 y = 0 := fun y => by
    have := (locH Z p).h_smul_left 0 0 y; simpa using this
  have z2 : ∀ x, (locH Z p).h x 0 = 0 := fun x => by
    have := h_smul_right (Z := Z) p 0 x 0; simpa using this
  intro x y
  have hx : x ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  have hy : y ∈ Submodule.span (D.s.atP p).Ep (Set.range (baseChange₂ D p)) := by rw [span_baseChange_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | zero => rw [map_zero, z1, z1]
  | add a b _ _ ha hb => rw [map_add (f := _), (locH Z p).h_add_left, (locH Z p).h_add_left, ha, hb]
  | smul c a _ ha => rw [map_smul, (locH Z p).h_smul_left, (locH Z p).h_smul_left, ha]
  | mem a ha =>
    obtain ⟨a, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | zero => rw [map_zero, z2, z2]
    | add a b _ _ ha hb => rw [map_add (f := _), h_add_right, h_add_right, ha, hb]
    | smul c a _ ha => rw [map_smul, h_smul_right, h_smul_right, ha]
    | mem b hb => obtain ⟨b, rfl⟩ := hb; exact key a b

end

section
variable {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {Tn T'n : ℕ}
  {F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)} {F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)}

end

section
variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

end

end GlobalTheory.Unfold.Model
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampQ {Cl Nu : Type} (Q : Prop → Prop) (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ :=
  haveI := L.fP
  ∑ A ∈ L.Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then L.aN p (d p) else L.aZ p (d p))

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def setQ (Q : Prop → Prop) : Set (TauC Y u u') := {t | (Y.tO u u').G t ≠ 0 ∧ Q (¬ (Y.tO u u').gener t)}

def FamQ {Cl : Type} (Q : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) : Prop :=
  TS = setQ Y u u' Q ∧ GlobalTheory.Unfold.ClsRow TS cls ∧
    ∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t'

def HasPt (TS : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) : Prop :=
  ∃ t ∈ TS, (Y.tO u u').vec t ≠ 0 ∧ ptPN t = γ

def grpF {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :=
  ∑' t : TauC Y u u', (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν}).indicator (Y.tO u u').vec t

def a2F {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) : ℝ :=
  ‖grpF Y u u' TS cls c γ ν‖ ^ 2 / J2of Y u u' νq γ

def gCls (t : TauC Y u u') : Set (TauC Y u u') :=
  {t' | t' ∈ (Y.tO u u').genSet ∧ (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t ∧ (Y.tO u u').s0 t t' = 1 ∧
    (Y.tO u u').scal t t'}

end GlobalTheory.SnFam
end
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver

namespace GlobalTheory.GenMass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {T T' : D.host.E}

def tm (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T')
    (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) : Loc.Term (Vp D p) (Z.M p) D.R.rS :=
  ⟨Λ, scaled Z p (frame G), scaled Z p (frame G'), (FP p).A.T, (FP p).B.T⟩

def locSet (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T') (p : PlF D) (d : LocNG.Datum (FP p)) :
    Set (Submodule (Z.M p).L.O (Vp D p)) :=
  {Λ | LocNG.IsTermOver (FP p) d (tm FP G G' p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p Λ)}

def locSum (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T') (p : PlF D) (R : LocNG.Reps (FP p))
    (d0 : LocNG.Datum (FP p)) : ℝ≥0∞ :=
  ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ((locSet G G' p d.1).encard : ℝ≥0∞)

def globSet (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T') (y : Dat Z FP) : Set (LV D) :=
  {Λ | Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ ∈ locSet G G' p (y p)}

def StdOff (Z : LocDat D) (P : Finset (PlF D)) (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  Tri D.host.E (frame F) (frame G) ∧ Tri D.host.E (frame F') (frame G') ∧ G.zt = G.fl.z ∧ G'.zt = G'.fl.z ∧
  ∀ p, p ∉ P → ∃ A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, Uni A ∧ Uni A' ∧
    (∀ a b, A a b ∈ (Z.M p).L.O ∧ A' a b ∈ (Z.M p).L.O) ∧
    Chg (scaled Z p (frame F)) A (scaled Z p (frame G)) ∧ Chg (scaled Z p (frame F')) A' (scaled Z p (frame G'))

def BaseOK (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (P : Finset (PlF D)) (d0 : Dat Z FP) : Prop :=
  Based Z FP Tn T'n F F' ∧ (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) ∧ (∀ p, p ∉ P → (FP p).PrimeTo) ∧
  (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) ∧
  ∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ P → LocNG.IsTermOver (FP p) (d0 p) (tm FP F F' p (lattice₂ D Z.M p Λ₀))

def MassLaw (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (P : Finset (PlF D)) (d0 : Dat Z FP) (V : ℝ) : Prop :=
  ∀ d : Dat Z FP, (∀ p, p ∉ P → d p = d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) →
    massA F F' d = ENNReal.ofReal (V * ∏ p ∈ P, LocNG.Datum.wt (d0 p) (d p))

def glueSum (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T') (s : Finset (LV D)) : ℝ :=
  ∑ Λ ∈ s, ((Nat.card (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') Λ) : ℕ) : ℝ)⁻¹

def Glue (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T') (s : Finset (LV D)) : Prop :=
  Formalism.L2.SG.Pf.Cnt.IsGlueReps (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') s

end GlobalTheory.GenMass
end
end
