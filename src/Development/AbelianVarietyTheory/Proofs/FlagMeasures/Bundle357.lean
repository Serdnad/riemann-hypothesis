module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle010
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle310
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle343
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatTransport

variable {D : D7}

theorem mem_gmap_inv (g : GV D) (Λ : LV D) (x : (VS D).V) : x ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ↔ g x ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g x, h, by simp⟩

variable {T : D.host.E} {F0 G' : FlagG (VS D) D.R.rS T} {g : GV D}

theorem e_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (a : Fin D.R.rS) : g (F0.e a) = G'.e a := by
  have h := hfr a.castSucc
  simpa [FlagG.fvec, Fin.snoc_castSucc] using h

theorem z_eq (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) : g F0.z = G'.z := by
  have h := hfr (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using h

theorem map_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) :
    F0.X.map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = G'.X := by
  unfold FlagG.X
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  exact e_eq hfr a

theorem mem_X (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ F0.X ↔ g v ∈ G'.X := by
  rw [← map_X hfr]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_orth (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) :
    v ∈ orth (VS D) F0.X ↔ g v ∈ orth (VS D) G'.X := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ F0.X := by
      rw [mem_X hfr]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h x hx
    rw [← hiso]
    exact h _ ((mem_X hfr x).1 hx)

theorem mem_XS (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (v : (VS D).V) : v ∈ XS D F0 ↔ g v ∈ XS D G' := by
  have hmap : (XS D F0).map ((g : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = XS D G' := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      refine ⟨a, x, hx, ?_⟩
      simp [e_eq hfr a]
    · rintro ⟨a, x, hx, rfl⟩
      refine ⟨x • F0.e a, ⟨a, x, hx, rfl⟩, ?_⟩
      simp [e_eq hfr a]
  rw [← hmap]
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := g.injective hwv
    exact this ▸ hw

theorem mem_dual (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ↔ g x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
  have hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]
  constructor
  · intro h y hy
    have hy' : g.symm y ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
      rw [mem_gmap_inv]
      simpa using hy
    have := h _ hy'
    rw [← hiso] at this
    simpa using this
  · intro h y hy
    rw [← hiso]
    exact h _ ((mem_gmap_inv g Λ y).1 hy)

theorem isLattice_inv (g : GV D) {Λ : LV D} (hL : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
  exact Submodule.IsLattice.of_fg D.host.E (hL.fg.map _)

theorem mem_Lsub (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfr : ∀ a, g (F0.fvec a) = G'.fvec a) (Λ : LV D)
    (v : (VS D).V) (hv : v ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0)) : g v ∈ Lsub Λ (lf D G') := by
  obtain ⟨hs, ho⟩ := hv
  refine ⟨?_, (mem_orth hg hfr v).1 ho⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨hyΛ, hyo⟩ := hy
  rw [map_add (f := _)]
  refine Submodule.add_mem_sup ⟨(mem_gmap_inv g Λ y).1 hyΛ, (mem_orth hg hfr y).1 hyo⟩ ?_
  exact (mem_X hfr w).1 hw

end GlobalTheory.RowLatTransport

namespace GlobalTheory.RowLatTransport

theorem rowLat_transport : ∀ (D : D7) (T : D.host.E) (F0 G' : FlagG (VS D) D.R.rS T) (g : GV D), g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, g (F0.fvec a) = G'.fvec a) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → G'.z ∈ Λ → XLam Λ (lf D G') = XS D G' → (∀ c : D.host.E, c • G'.z ∈ Lsub Λ (lf D G') → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) → Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 ∧ Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) ∧ F0.z ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ∧ XLam (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) = XS D F0 ∧ (∀ c : D.host.E, c • F0.z ∈ Lsub (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c) := by
  intro D T F0 G' g hg hfr Λ hL hU hz hX hprim
  have hL' := isLattice_inv g hL
  have hU' : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) := by
    unfold Formalism.HermitianLatticesTheory.IsUnimodular
    ext x
    rw [mem_dual hg, mem_gmap_inv]
    have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hU
    rw [hU0]
  refine ⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D.sp.cm (VS D) _ hL' hU',
    hL', hU', ?_, ?_, ?_⟩
  · rw [mem_gmap_inv, z_eq hfr]
    exact hz
  · ext v
    change v ∈ Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ ⊓ toO (VS D) F0.X ↔ v ∈ XS D F0
    rw [mem_XS hfr, ← hX]
    change _ ↔ g v ∈ Λ ⊓ toO (VS D) G'.X
    simp only [Submodule.mem_inf, toO, Submodule.restrictScalars_mem]
    rw [mem_gmap_inv, mem_X hfr]
  · intro c hc
    apply hprim c
    have := mem_Lsub hg hfr Λ _ hc
    rw [map_smul, z_eq hfr] at this
    exact this

end GlobalTheory.RowLatTransport
end
end

section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7}

theorem mem_orth_iff {U : Submodule D.host.E (VS D).V} {v : (VS D).V} :
    v ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem sup_span_add {P : Submodule D.host.E (VS D).V} {x d : (VS D).V} (hd : d ∈ P) :
    P ⊔ Submodule.span D.host.E {x + d} = P ⊔ Submodule.span D.host.E {x} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_left hd)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have h2 : x + d ∈ P ⊔ Submodule.span D.host.E {x + d} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self (x + d))
    have h3 : d ∈ P ⊔ Submodule.span D.host.E {x + d} := Submodule.mem_sup_left hd
    have h1 := Submodule.sub_mem _ h2 h3
    simpa using h1

variable {T : D.host.E}

theorem xflag_succ (A : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) (hj : j < D.R.rS) :
    Xflag A (j + 1) = Xflag A j ⊔ Submodule.span D.host.E {A.fl.e ⟨j, hj⟩} := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j + 1}) = Submodule.span _ (A.fl.e '' {i | i.1 < j}) ⊔ _
  rw [← Set.image_singleton, ← Submodule.span_union, ← Set.image_union]
  congr 2
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
  omega

theorem xflag_ge (A : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) (hj : D.R.rS ≤ j) : Xflag A j = Xflag A D.R.rS := by
  show Submodule.span _ (A.fl.e '' {i | i.1 < j}) = Submodule.span _ (A.fl.e '' {i | i.1 < D.R.rS})
  congr 2
  ext i
  simp only [Set.mem_setOf_eq]
  omega

theorem frame_castSucc (A : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_last (A : LFlag (D.sp.Y 0) D.R.rS T) : frame A (Fin.last _) = A.fl.z := by
  simp [frame, FlagG.fvec]

theorem adapt_xflag {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (h : Adapt a A B) (j : ℕ) :
    (Xflag A j).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag B j := by
  induction j with
  | zero => rw [xflag_zero, xflag_zero, Submodule.map_bot]
  | succ j ih =>
    by_cases hj : j < D.R.rS
    · rw [xflag_succ A j hj, xflag_succ B j hj, Submodule.map_sup, ih, Submodule.map_span, Set.image_singleton]
      have hd := h.2 (Fin.castSucc ⟨j, hj⟩)
      rw [frame_castSucc, frame_castSucc, Fin.coe_castSucc] at hd
      have e : (a : (VS D).V →ₗ[D.host.E] (VS D).V) (A.fl.e ⟨j, hj⟩) = B.fl.e ⟨j, hj⟩ + (a (A.fl.e ⟨j, hj⟩) - B.fl.e ⟨j, hj⟩) := by
        simp
      rw [e, sup_span_add hd]
    · rw [xflag_ge A (j + 1) (by omega), xflag_ge B (j + 1) (by omega), ← xflag_ge A j (by omega),
        ← xflag_ge B j (by omega), ih]

theorem adapt_xsp {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (Xsp A).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp B := by
  rw [xsp_eq, xsp_eq, adapt_xflag h]

theorem orth_map_isom {a : GV D} (ha : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') :
    (orth (VS D) U).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) U' := by
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_orth_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ x' hx'
    rw [← hU] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    simp only [LinearEquiv.coe_coe]
    rw [ha]; exact hv x hx
  · intro hw
    refine ⟨a.symm w, fun x hx => ?_, by simp⟩
    have := hw (a x) (hU ▸ Submodule.mem_map_of_mem hx)
    have e : (VS D).hT (a x) (a (a.symm w)) = (VS D).hT x (a.symm w) := ha _ _
    simp only [LinearEquiv.apply_symm_apply] at e
    rw [← e]; exact this

theorem adapt_orth {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (h : Adapt a A B) :
    (orth (VS D) (Xsp A)).map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = orth (VS D) (Xsp B) :=
  orth_map_isom h.1 (adapt_xsp h)

theorem mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {x : (VS D).V} (hx : x ∈ U) : a x ∈ U' := by
  rw [← hU]; exact Submodule.mem_map_of_mem hx

theorem symm_mem_of_map_eq {a : GV D} {U U' : Submodule D.host.E (VS D).V}
    (hU : U.map (a : (VS D).V →ₗ[D.host.E] (VS D).V) = U') {y : (VS D).V} (hy : y ∈ U') : a.symm y ∈ U := by
  rw [← hU] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using hx

theorem adapt_mul {A B C : LFlag (D.sp.Y 0) D.R.rS T} {a b : GV D} (ha : Adapt a A B) (hb : Adapt b B C) :
    Adapt (b * a) A C := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hb.1 ha.1, fun k => ?_⟩
  have e : (b * a) (frame A k) - frame C k = b (a (frame A k) - frame B k) + (b (frame B k) - frame C k) := by
    rw [le_mul_app, map_sub]; abel
  rw [e]
  exact add_mem (mem_of_map_eq (adapt_xflag hb _) (ha.2 k)) (hb.2 k)

theorem adapt_inv {A B : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (ha : Adapt a A B) : Adapt a⁻¹ B A := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1, fun k => ?_⟩
  have e : a⁻¹ (frame B k) - frame A k = -(a.symm (a (frame A k) - frame B k)) := by
    rw [le_inv_app, map_sub]; simp
  rw [e]
  exact neg_mem (symm_mem_of_map_eq (adapt_xflag ha _) (ha.2 k))

theorem z_mem_orth (A : LFlag (D.sp.Y 0) D.R.rS T) : A.fl.z ∈ orth (VS D) (Xsp A) := by
  rw [mem_orth_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact A.fl.z_orth i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem adapt_nrat {A : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} (hn : n ∈ NRat A) : Adapt n A A := by
  refine ⟨hn.1, fun k => ?_⟩
  induction k using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, ← xsp_eq]
    exact hn.2.2 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.coe_castSucc]
    apply hn.2.1 i.1
    show A.fl.e i ∈ Submodule.span _ (A.fl.e '' {k | k.1 < i.1 + 1})
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩

theorem frameAdaptedIsometry_of_fixing_both_frames {T' : D.host.E} {A : LFlag (D.sp.Y 0) D.R.rS T} {A' : LFlag (D.sp.Y 0) D.R.rS T'} {h : GV D}
    (hh : h ∈ H0 A A') : Adapt h A A ∧ Adapt h A' A' :=
  ⟨⟨hh.1, fun k => by rw [hh.2.1 k, sub_self]; exact zero_mem _⟩,
   ⟨hh.1, fun k => by rw [hh.2.2 k, sub_self]; exact zero_mem _⟩⟩

theorem adapt_mapLF {A : LFlag (D.sp.Y 0) D.R.rS T} {γ : GV D} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    Adapt γ A (mapLF γ A) := by
  refine ⟨hγ, fun k => ?_⟩
  have : frame (mapLF γ A) k = γ (frame A k) := by
    simp only [mapLF, dif_pos hγ, frame]
    rw [fvec_mapFlag]
  rw [this, sub_self]; exact zero_mem _

theorem nrat_conj {A B : LFlag (D.sp.Y 0) D.R.rS T} {a n : GV D} (ha : Adapt a A B) (hn : n ∈ NRat A) :
    a * n * a⁻¹ ∈ NRat B := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ((Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem ha.1 hn.1)
    ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem ha.1), fun j x hx => ?_, fun x hx => ?_⟩
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xflag ha j) (hn.2.1 j _ (symm_mem_of_map_eq (adapt_xflag ha _) hx))
  · have e : (a * n * a⁻¹) x - x = a (n (a.symm x) - a.symm x) := by
      rw [le_mul_app, le_mul_app, le_inv_app, map_sub]; simp
    rw [e]
    exact mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ (symm_mem_of_map_eq (adapt_orth ha) hx))

theorem nrat_eq_nlam (A : LFlag (D.sp.Y 0) D.R.rS T) : NRat A = NLam ⊤ A := by
  ext n
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, ?_⟩, h2, h3⟩
    rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_top, LinearMap.range_eq_top]
    exact n.surjective
  · rintro ⟨⟨h1, _⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩

def NRatSub (A : LFlag (D.sp.Y 0) D.R.rS T) : Subgroup (GV D) := NLamSub ⊤ A

theorem mem_nratSub {A : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} : n ∈ NRatSub A ↔ n ∈ NRat A := by
  rw [nrat_eq_nlam]; rfl

theorem nrat_mul {A : LFlag (D.sp.Y 0) D.R.rS T} {a b : GV D} (ha : a ∈ NRat A) (hb : b ∈ NRat A) : a * b ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).mul_mem (mem_nratSub.2 ha) (mem_nratSub.2 hb))

theorem nrat_inv {A : LFlag (D.sp.Y 0) D.R.rS T} {a : GV D} (ha : a ∈ NRat A) : a⁻¹ ∈ NRat A :=
  mem_nratSub.1 ((NRatSub A).inv_mem (mem_nratSub.2 ha))

theorem nrat_one (A : LFlag (D.sp.Y 0) D.R.rS T) : (1 : GV D) ∈ NRat A :=
  mem_nratSub.1 (NRatSub A).one_mem

section Defs

variable {T T' : D.host.E}

def InB (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (lam lam' : LV D) (γ : GV D)
    (b : GV D × GV D) : Prop :=
  b.1 ∈ Aut0 F0 lam ∧ b.2 ∈ Aut0 F0' lam' ∧ KeyEq F0 F0' lam γ (b.1 * γ * b.2⁻¹)

def Corr (F0 F : LFlag (D.sp.Y 0) D.R.rS T) (F0' F' : LFlag (D.sp.Y 0) D.R.rS T') (γ g : GV D) (b : GV D × GV D)
    (h : GV D) : Prop :=
  h ∈ H0 F F' ∧ ∃ n ∈ NRat F0, ∃ n' ∈ NRat F0', b.1 * γ * b.2⁻¹ = n * γ * n' ∧
    h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F ∧ h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F'

end Defs

end GlobalTheory.StabCnt
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedRowLattice_term_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  first | exact @GlobalTheory.HL.term_lat_isLattice | exact GlobalTheory.HL.term_lat_isLattice | (intros; apply GlobalTheory.HL.term_lat_isLattice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopVol

private theorem hJ_smul_right_flag_measures {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem ratCoord_conj_eq_stCoord : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (q : GlobalTheory.LoopV.roots (ptMat w)) (p : Formalism.L2.SG.RealObj.FreeE w), p.1 = q.1 → GlobalTheory.LoopVol.ratCoord X u' w γ s (s * y * s⁻¹) τ q = ((D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1))⁻¹ * Formalism.L2.SG.RealObj.stCoord X u' w γ y (X.pl.symm τ) p := by
  intro D X u' w γ s y τ q p hpq
  obtain ⟨pq, hp⟩ := p
  obtain ⟨qq, hq⟩ := q
  simp only at hpq
  subst hpq

  have hconj : s⁻¹ * (s * y * s⁻¹) * s = y := by group
  have hab : pq.1.val < pq.2.val := hp.1
  have hbr : pq.2.val ≤ D.R.rS := Nat.lt_succ_iff.mp pq.2.isLt
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have h1 := GlobalTheory.RealPlaces.one_le_rdE D
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  unfold GlobalTheory.LoopVol.ratCoord Formalism.L2.SG.RealObj.stCoord
  rw [hconj]
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Matrix.mulVec_smul, hJ_smul_right_flag_measures]

  have hsplit : D.R.rS - pq.1.val = (pq.2.val - pq.1.val) + (D.R.rS - pq.2.val) := by omega
  rw [hsplit, pow_add]
  field_simp

end GlobalTheory.LoopVol
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.anisotropicOrthogonal_isometric_definiteModel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (GlobalTheory.TypeAsm.F0 X u) HW W.subtype → ∃ e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W, (∀ x y, HW.B.flip (e x) (e y) = GlobalTheory.RowsOrb.hU X u x y) ∧ ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X := by
  first | exact @GlobalTheory.RowsOrb.ub_equiv_model | exact GlobalTheory.RowsOrb.ub_equiv_model | (intros; apply GlobalTheory.RowsOrb.ub_equiv_model <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.anisotropicOrthogonal_totallyPositiveDefinite : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  first | exact @GlobalTheory.RowsOrb.pd_hU | exact GlobalTheory.RowsOrb.pd_hU | (intros; apply GlobalTheory.RowsOrb.pd_hU <;> assumption)
end
