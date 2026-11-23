module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaFIntMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MulConjApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starFrame (γ : TermDef.Term D u u' F0 what₂) : Fin (D.R.rS + 1) → (VS D).V :=
  frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹

def starZh (f f' : Fin (D.R.rS + 1) → (VS D).V) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  fun a b => brS (VS D) (f' b) (f a)

def starOm (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ b, (starZh f f').adjugate b (Fin.last D.R.rS) • f' b

def starCompat (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
      leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) (D.R.rS + 1) =
    leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) D.R.rS *
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) (D.R.rS + 1) ∧
  leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) (D.R.rS + 1) • starOm (frame (lf D F0)) (starFrame γ) -
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) (D.R.rS + 1) • starOm (frame (lf D F0)) (frame F'₂) ∈
    Xsp (lf D F0)

variable (u u' F0 what₂)

def StarGenLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂)
  (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))

include hu in
theorem baseChangeAt_frame_eq (a : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame (lf D F0) a) = ((hu a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) • (tLoc Zd p γ).f a := by
  rw [tf, Units.smul_def, smul_smul, (hu a).val_inv_mul, one_smul]

include hu in
theorem bcP_X {x : (VS D).V} (hx : x ∈ Xsp (lf D F0)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f := by
  change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_cs, baseChangeAt_frame_eq Zd p γ hu, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [(baseChange₂ D p).map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChange_mem_perp_sup {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp (lf D F0))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f, (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf, frame_cs, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

theorem h_X_perp {w v : Vp D p} (hw : w ∈ (locH Zd p).X (tLoc Zd p γ).f)
    (hv : v ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f)) : (locH Zd p).h w v = 0 := by
  rw [(locH Zd p).h_herm v w, (show (locH Zd p).h v w = 0 from hv w hw), map_zero]

end Place

theorem pair_int (γ : TermDef.Term D u u' F0 what₂) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hSD₁ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₁))
    (hL : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f ⊆
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₁) (tLoc Zd p γ).f)
    {x m : (VS D).V} (hx : x ∈ Λ₂) (hxo : x ∈ orth (VS D) (Xsp (lf D F0))) (hm : m ∈ Λ₁)
    (hmo : m ∈ orth (VS D) (Xsp (lf D F0))) : IsIntegral ℤ ((VS D).hT m x) := by
  refine int_of_loc Zd fun p => ?_
  rw [← localForm_baseChange]
  have hv := baseChange_mem_perp_sup Zd p γ hxo
  have hmem : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p x, hv⟩ ∈
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := ⟨⟨baseChange₂ D p x, hv⟩, baseChange_mem_localLattice Zd hx p, rfl⟩
  obtain ⟨x'', hx''Λ, hx''eq⟩ := hL p hmem
  have hdiff : (baseChange₂ D p x) - (x'' : Vp D p) ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := (Submodule.Quotient.eq _).1 hx''eq.symm
    simpa using this
  have e : baseChange₂ D p x = (x'' : Vp D p) + ((baseChange₂ D p x) - (x'' : Vp D p)) := by abel
  rw [e, (locH Zd p).h_add_left, h_X_perp Zd p γ hdiff (baseChange_mem_perp_sup Zd p γ hmo), add_zero]
  exact ((hSD₁ p).2.2 x'').1 hx''Λ (baseChange₂ D p m) (baseChange_mem_localLattice Zd hm p)

theorem memX (γ : TermDef.Term D u u' F0 what₂) {Λa Λb : Submodule (𝓞 D.host.E) (VS D).V}
    (ha : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λa) (tLoc Zd p γ).f)
    (hb : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λb) (tLoc Zd p γ).f) (hΛb : Submodule.IsFullLattice D.host.E Λb)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) {x : (VS D).V} (hx : x ∈ Xsp (lf D F0))
    (hxa : x ∈ Λa) : x ∈ Λb := by
  refine mem_of_bcP Zd hΛb fun p => ?_
  have h1 : baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) (bcP_X Zd p γ (hu p) hx)
  have h2 := (ha p).2.2 _ (baseChange_mem_localLattice Zd hxa p) h1
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun a => (hb p).1 a) h2

theorem z_mem (γ : TermDef.Term D u u' F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (tLoc Zd p γ).f) :
    F0.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← tf_last Zd p γ]; exact (h p).1 _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def LocRealAt (p : PlF D) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)), IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w O →
    ∃ (Lp Up : MatP D p) (c : 𝓞 D.host.F), c ≠ 0 ∧ IsLo Lp ∧ IsUp Up ∧
      ∀ L U : PairVal.MatR D, IsLo L → IsUp U →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (L a b) - Lp a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (U a b) - Up a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        tupZ M δ u u' (L * ptMat w * U * Sg D.host.E D.R.rS) p = O

variable {M δ}

theorem locRealAt_ord (hA : ∀ p, Agree δ M p) (p : PlF D) (hM : (M p).split = none) : LocRealAt M δ u u' p :=
  fun w O hO => locReal_ord hA u u' w p hM O hO

theorem adj_mem {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} {l : Matrix (Fin n) (Fin n) R}
    (hl : ∀ a b, l a b ∈ S) (a b : Fin n) : l.adjugate a b ∈ S := by
  let lR : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, hl a b⟩
  have h1 : lR.map S.subtype = l := by ext a b; rfl
  have h2 := congrFun (congrFun (RingHom.map_adjugate S.subtype lR) a) b
  rw [← h1, show lR.map S.subtype = S.subtype.mapMatrix lR from rfl, ← h2]
  exact (lR.adjugate a b).2

theorem congr_dvd {p : PlF D} {y : (D.s.atP p).Ep} {c c' r : 𝓞 D.host.F} (hc : c = c' * r)
    (h : ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) :
    ∃ o ∈ (D.s.atP p).O, y =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c')) * o := by
  obtain ⟨o, ho, rfl⟩ := h
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F r)) * o,
    Subring.mul_mem _ (alg_mem_O (fun q => D.s.atP q) p (iotaF_int_mem (fun q => D.s.atP q) p r)) ho, ?_⟩
  rw [hc, map_mul, map_mul, map_mul, mul_assoc]

theorem exist_of (hA : ∀ p, Agree δ M p) (hTy : ∀ p, (M p).split ≠ none → LocRealAt M δ u u' p) :
    Exist M δ u u' := by
  intro w' _ x hx
  have hLR : ∀ p, LocRealAt M δ u u' p := fun p => by
    by_cases h : (M p).split = none
    · exact locRealAt_ord u u' hA p h
    · exact hTy p h
  have hloc := fun p => hLR p w' (x.1 p) (hx p)
  choose Lp Up cp hcp0 hLp hUp hreal using hloc
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA ∅
  have hBad := Filter.eventually_cofinite.1 hgood
  set S : Finset (PlF D) := x.2.toFinset ∪ hBad.toFinset with hS
  set c : 𝓞 D.host.F := ∏ p ∈ S, cp p with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hcp0 p
  obtain ⟨L, hL1, hL0, hLS, hLO⟩ := approx_lo (fun q => D.s.atP q) S c hc0 (fun p => Lp p)
    (fun p _ a => (hLp p).1 a) (fun p _ a b hab => (hLp p).2 a b hab)
  obtain ⟨U, hU1, hU0, hUS, hUO⟩ := approx_up (fun q => D.s.atP q) S c hc0 (fun p => Up p)
    (fun p _ a => (hUp p).1 a) (fun p _ a b hab => (hUp p).2 b a hab)
  have hLlo : IsLo L := ⟨hL1, hL0⟩
  have hUup : IsUp U := ⟨hU1, fun a b hab => hU0 b a hab⟩
  have hZ : (L * ptMat w' * U * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w' * U := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  refine ⟨L * ptMat w' * U * Sg D.host.E D.R.rS, ⟨L, U, fun i j => ⟨hL0 i j, fun h => h ▸ hL1 i⟩,
    fun i j => ⟨hU0 i j, fun h => h ▸ hU1 i⟩, by rw [zhatOM_eq]; exact hZ⟩, ?_⟩
  funext p
  by_cases hp : p ∈ S
  · have hsplit : c = cp p * ∏ q ∈ S.erase p, cp q := (Finset.mul_prod_erase S cp hp).symm
    exact hreal p L U hLlo hUup (fun a b => congr_dvd hsplit (hLS p hp a b))
      (fun a b => congr_dvd hsplit (hUS p hp a b))
  · have hpx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_left _ (x.2.mem_toFinset.2 h))
    have hpg : (M p).split = none ∧ (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
        ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
          (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
        ∀ t ∈ (∅ : Finset D.host.E), ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
          (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
            (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O := by
      by_contra h
      exact hp (Finset.mem_union_right _ (hBad.mem_toFinset.2 h))
    have hentL : ∀ a b, (D.s.atP p).ιE (L a b) ∈ (D.s.atP p).O := hLO p hp
    have hentU : ∀ a b, (D.s.atP p).ιE (U a b) ∈ (D.s.atP p).O := hUO p hp
    have hLd : L.det = 1 := det_lo' hLlo
    have hUd : U.det = 1 := det_up' hUup
    have hinv : ∀ (X : PairVal.MatR D), X.det = 1 → (∀ a b, (D.s.atP p).ιE (X a b) ∈ (D.s.atP p).O) →
        ∀ a b, (D.s.atP p).ιE (X⁻¹ a b) ∈ (D.s.atP p).O := by
      intro X hX hXe a b
      rw [Matrix.inv_def, hX, Ring.inverse_one, one_smul]
      have h2 := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE X) a) b
      rw [show ((D.s.atP p).ιE.mapMatrix X.adjugate) a b = (D.s.atP p).ιE (X.adjugate a b) from rfl] at h2
      rw [h2]
      exact adj_mem (D.s.atP p).O (fun a b => hXe a b) a b
    rw [hpx]
    exact tupZ_eq_x0L_at hA u u' hLlo hUup hZ p hpg.1 hpg.2.1.1 hpg.2.1.2 hpg.2.2.1.1 hpg.2.2.1.2
      (fun a b => ⟨hentL a b, hentU a b, hinv L hLd hentL a b, hinv U hUd hentU a b⟩)

end Assembly

end Formalism.L2.SG.Pf.PCountEx
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem rowsSum_of_val (vR : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) (nc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hA : (Y.tO u u').AbsConv)
    (hL : TermOp.LiftOnto X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hAV : Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC X Y u u' vR i0 i0' νq)
    (hAF : PairVal.AutFin D (X.Fu u) (Y.what₂ u)) (hAF' : PairVal.AutFin D (X.Fu u') (Y.what₂ u')) (hnc : 0 < nc) :
    DataInst.RowsSum vR κ nc (RealObj.VtPt X u u' 1 i0 i0' FdN FdN' νq) := by
  intro ρ
  obtain ⟨c, hc, hcv⟩ := hAV
  obtain ⟨C, hC⟩ := Formalism.L2.SG.WConst.weightBound_holds X Y u u' hnc
  obtain ⟨m, hm0, hmle⟩ := Formalism.L2.SG.RowsAbsX.exists_wRow_lb u (X.Fu u) (Y.what₂ u) hAF
  obtain ⟨m', hm0', hmle'⟩ := Formalism.L2.SG.RowsAbsX.exists_wRow_lb u' (X.Fu u') (Y.what₂ u') hAF'
  have hwm : 0 < Real.sqrt (m * m') := Real.sqrt_pos.2 (mul_pos hm0 hm0')
  have hcw : 0 < c * Real.sqrt (m * m') := mul_pos hc hwm
  let Mm : ℝ := ∑ Λ ∈ Y.what₂ u, |PairVal.massRow D (X.Fu u) (Y.what₂ u) Λ|
  let τ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
    fun t => (hL t).choose
  have hτ : ∀ t, (τ t).toTerm = t := fun t => (hL t).choose_spec
  have hτi : Function.Injective τ := fun a b h => by rw [← hτ a, ← hτ b, h]
  let C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  let K0 : ℝ := C' * Real.sqrt Mm / (c * Real.sqrt (m * m'))
  have hK0n : 0 ≤ K0 := div_nonneg (mul_nonneg hC'0 (Real.sqrt_nonneg _)) hcw.le
  let g : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ := fun t => K0 * ‖(Y.tO u u').vec (τ t)‖
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg hK0n (norm_nonneg _)
  have hg : Summable g := (hA.2.1.comp_injective hτi).mul_left K0
  let A : TB.Pt D.host.E → TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → Prop := fun p t =>
    DataInst.Elig t ∧ κ t = ρ ∧ ∃ w, DataInst.ptOfList (D.R.rS + 1) p = some w ∧ t.atPt w
  have hAu : ∀ p p' t, A p t → A p' t → p = p' := by
    rintro p p' t ⟨-, -, w, hw, ht⟩ ⟨-, -, w', hw', ht'⟩
    obtain rfl := Formalism.L2.SG.RowsAbsX.ptUniq_holds X Y u u' t w w' ht ht'
    exact ptOfList_inj hw hw'
  refine summable_of_fibre_bound A hAu g hg0 hg _ (fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro p
  have hS0 : 0 ≤ ∑' t : {t // A p t}, g t := tsum_nonneg fun t => hg0 t
  rcases hp : DataInst.ptOfList (D.R.rS + 1) p with _ | w
  · have h0 : DataInst.rowVec (vR) κ nc ρ p = 0 := by
      simp [DataInst.rowVec, hp]
    rw [h0, norm_zero, zero_mul]
    exact hS0

  have hA' : ∀ t, A p t ↔ (DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w) := by
    intro t
    simp only [A, hp, Option.some.injEq, exists_eq_left']
  let Sw := {t : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) // DataInst.Elig t ∧ κ t = ρ ∧ t.atPt w}
  have hsum : ∑' t : {t // A p t}, g t = ∑' t : Sw, g t.1 := by
    rw [← (Equiv.subtypeEquivRight hA').tsum_eq (fun t : Sw => g t.1)]
    rfl
  rw [hsum]
  have hgS : Summable (fun t : Sw => g t.1) := hg.comp_injective Subtype.val_injective
  let f : Sw → ℂ := fun t =>
    ((Real.sqrt (PairVal.massTerm t.1) : ℝ) : ℂ) * PairVal.cAt (vR) t.1 w
  let Dn : ℝ := Real.sqrt (n0 nc (D.mem u).A.T (D.mem u').A.T w) * DataInst.phi (D.R.rS + 1) p
  let V : ℝ := ‖PackageTie.hsEmb (RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w)‖
  let N : ℝ := Real.sqrt (RealObj.nW X u u' w)
  have hrow : DataInst.rowVec (vR) κ nc ρ p = (∑' t : Sw, f t) / (Dn : ℂ) := by
    simp only [DataInst.rowVec, hp]
    rfl
  have hvt : RealObj.VtPt X u u' 1 i0 i0' FdN FdN' νq p =
      ((N : ℝ) : ℂ) • PackageTie.hsEmb (RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w) := by
    simp only [RealObj.VtPt, RealObj.ptOfL, hp] <;> rfl
  have hnv : ‖RealObj.VtPt X u u' 1 i0 i0' FdN FdN' νq p‖ = N * V := by
    rw [hvt, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnr : ‖DataInst.rowVec (vR) κ nc ρ p‖ = ‖∑' t : Sw, f t‖ / |Dn| := by
    rw [hrow, norm_div, Complex.norm_real, Real.norm_eq_abs]
  rw [hnv, hnr]
  have hgS0 : 0 ≤ ∑' t : Sw, g t.1 := tsum_nonneg fun t => hg0 t.1

  by_cases hreal : ∃ γ, RealObj.IsPtRep X u u' w γ
  swap
  · have hV : V = 0 := by
      have : RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq w = 0 := by simp [RealObj.unscaledOperatorAtPointRepresentative, hreal]
      simp only [V, this, map_zero, norm_zero]
    rw [hV, mul_zero, mul_zero]
    exact hgS0

  by_cases hne : Nonempty Sw
  swap
  · haveI : IsEmpty Sw := not_nonempty_iff.1 hne
    rw [tsum_empty, norm_zero, zero_div, zero_mul]
    exact hgS0
  obtain ⟨t0⟩ := hne
  have hNC : N ≤ C' * |Dn| :=
    (hC p w hp hreal ⟨t0.1, t0.2.1.2, t0.2.2.2⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

  have hterm : ∀ t : Sw, ‖f t‖ * (C' * V) ≤ g t.1 := by
    intro t
    have hat : t.1.atPt w := t.2.2.2
    have huq : ∀ w₁ w₂, t.1.atPt w₁ → t.1.atPt w₂ → w₁ = w₂ :=
      fun w₁ w₂ h h' => Formalism.L2.SG.RowsAbsX.atPt_uniq _ _ _ t.1.cls w₁ w₂ h h'
    have hpt : PairVal.ptOf t.1 = w := by
      have hrel := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' (X.Fu u) (Y.what₂ u) t.1 w hat
      exact huq _ _ (PairVal.ptOf_spec t.1 ⟨w, hat, hrel⟩) hat
    have hcT : PairVal.cTerm vR t.1 = PairVal.cAt vR t.1 w :=
      PairVal.cTerm_of_atPt vR t.1 hat (fun w' h' => huq w' w h' hat)
    have h1 := hcv (τ t.1) (by rw [hτ]; exact t.2.1.1) (by rw [hτ]; exact t.2.1.2)
    rw [hτ, hpt, hcT] at h1
    have h2 := Formalism.L2.SG.Pf.RowForm.ClassAbs.vec_norm_ge X Y u u' (τ t.1)
    have hwt : Real.sqrt (m * m') ≤ Formalism.L2.SG.TermOp.wt (τ t.1) := by
      unfold Formalism.L2.SG.TermOp.wt
      exact Real.sqrt_le_sqrt (mul_le_mul (hmle _ (τ t.1).mem) (hmle' _ (τ t.1).mem') hm0'.le
        (hm0.le.trans (hmle _ (τ t.1).mem)))
    have hm : Real.sqrt (PairVal.massTerm t.1) ≤ Real.sqrt Mm := Real.sqrt_le_sqrt (massTerm_le t.1)
    have hf : ‖f t‖ = Real.sqrt (PairVal.massTerm t.1) * ‖PairVal.cAt vR t.1 w‖ := by
      simp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hV0 : 0 ≤ V := norm_nonneg _
    have hamp0 : 0 ≤ ‖PackageTie.hsEmb (TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (τ t.1))‖ := norm_nonneg _
    have e3 : ‖PairVal.cAt vR t.1 w‖ * V ≤ ‖(Y.tO u u').vec (τ t.1)‖ / (c * Real.sqrt (m * m')) := by
      rw [le_div_iff₀ hcw]
      have k1 : Real.sqrt (m * m') * ‖PackageTie.hsEmb (TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (τ t.1))‖ ≤
          ‖(Y.tO u u').vec (τ t.1)‖ := (mul_le_mul_of_nonneg_right hwt hamp0).trans h2
      nlinarith [mul_le_mul_of_nonneg_left h1 hwm.le]
    have e4 : 0 ≤ ‖PairVal.cAt (vR) t.1 w‖ * V :=
      mul_nonneg (norm_nonneg _) hV0
    calc ‖f t‖ * (C' * V)
        = C' * (Real.sqrt (PairVal.massTerm t.1) *
            (‖PairVal.cAt (vR) t.1 w‖ * V)) := by rw [hf]; ring
      _ ≤ C' * (Real.sqrt Mm * (‖(Y.tO u u').vec (τ t.1)‖ / (c * Real.sqrt (m * m')))) := by
          apply mul_le_mul_of_nonneg_left _ hC'0
          exact mul_le_mul hm e3 e4 (Real.sqrt_nonneg _)
      _ = g t.1 := by simp only [g, K0]; ring

  have hlhs : ‖∑' t : Sw, f t‖ / |Dn| * (N * V) ≤ ‖∑' t : Sw, f t‖ * (C' * V) := by
    rcases (abs_nonneg Dn).eq_or_lt with hD | hD
    · rw [← hD, div_zero, zero_mul]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg hC'0 (norm_nonneg _))
    · rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      have : N * V ≤ C' * |Dn| * V := mul_le_mul_of_nonneg_right hNC (norm_nonneg _)
      calc ‖∑' t : Sw, f t‖ * (N * V) ≤ ‖∑' t : Sw, f t‖ * (C' * |Dn| * V) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖∑' t : Sw, f t‖ * (C' * V) * |Dn| := by ring
  refine hlhs.trans ?_
  rcases (mul_nonneg hC'0 (norm_nonneg _) : 0 ≤ C' * V).eq_or_lt with hK | hK
  · rw [← hK, mul_zero]
    exact hgS0
  · have hfb : ∀ t : Sw, ‖f t‖ ≤ g t.1 / (C' * V) := fun t => by
      rw [le_div_iff₀ hK]; exact hterm t
    have hsn : Summable (fun t : Sw => ‖f t‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfb (hgS.div_const _)
    calc ‖∑' t : Sw, f t‖ * (C' * V) ≤ (∑' t : Sw, ‖f t‖) * (C' * V) :=
          mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsn) hK.le
      _ = ∑' t : Sw, ‖f t‖ * (C' * V) := (tsum_mul_right).symm
      _ ≤ ∑' t : Sw, g t.1 := Summable.tsum_le_tsum hterm (hsn.mul_right _) hgS

end Formalism.L2.SG.RowsAbsX
end
end
