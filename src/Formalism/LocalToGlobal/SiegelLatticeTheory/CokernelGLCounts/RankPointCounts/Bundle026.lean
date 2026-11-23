module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXFinsetSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.NlamFrameMem
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
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7}

theorem LprExistA_iso_span {s : Set (VS D).V} (h : ∀ x ∈ s, ∀ y ∈ s, (VS D).hT x y = 0) :
    ∀ x ∈ Submodule.span D.host.E s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
  have h1 : ∀ x ∈ s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
    intro x hx y hy
    have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT x) := by
      rw [Submodule.span_le]
      intro y' hy'
      exact h x hx y' hy'
    exact hle hy
  intro x hx y hy
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip y) := by
    rw [Submodule.span_le]
    intro x' hx'
    show (VS D).hT.flip y x' = 0
    rw [LinearMap.flip_apply]
    exact h1 x' hx' y hy
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem LprExistA_orth_span {s : Set (VS D).V} {x : (VS D).V} (h : ∀ v ∈ s, (VS D).hT v x = 0) :
    ∀ v ∈ Submodule.span D.host.E s, (VS D).hT v x = 0 := by
  intro v hv
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip x) := by
    rw [Submodule.span_le]
    intro v' hv'
    show (VS D).hT.flip x v' = 0
    rw [LinearMap.flip_apply]
    exact h v' hv'
  have := hle hv
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem gfacts_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hG : GFacts Λ f g1 g2' β)
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (hsp : Submodule.span D.host.E (Set.range g2') = Submodule.span D.host.E (Set.range g2))
    (hz : g2' (Fin.last _) - g2 (Fin.last _) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (ht : GDl f g2' (D.R.rS + 1) = GDl f g2 (D.R.rS + 1)) (hr : GDl f g2' D.R.rS = GDl f g2 D.R.rS)
    (ho' : Gom' f g2' = Gom' f g2) (ho : Gom f g2' = Gom f g2) : GFacts Λ f g1 g2 β := by
  have hmap : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) ≤
      (Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => g1 a.castSucc)).comap
        β.symm.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact hG.xmap' b
  refine
    { iso := hG.iso
      lam := hG.lam
      lam' := hG.lam'
      xmap := fun a => hX ▸ hG.xmap a
      xmap' := fun a => ?_
      zmap := ?_
      fiso := hG.fiso
      g2iso := fun a b => ?_
      proj := hG.proj
      gram := hG.gram
      theta := fun x1 hx1 => ?_
      ratio := ?_
      omp := ?_
      om := ?_ }
  · have h : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact hmap h
  · have h1 := hG.zmap
    rw [hX] at h1
    have h3 := Submodule.add_mem _ h1 hz
    rwa [sub_add_sub_cancel] at h3
  · have hiso : ∀ x ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc),
        ∀ y ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc), (VS D).hT x y = 0 := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hG.g2iso i j
    have ha : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    have hb : g2 b.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨b, rfl⟩
    exact LprExistA_iso_span hiso _ ha _ hb
  · obtain ⟨x2, h1, h2, h3⟩ := hG.theta x1 hx1
    refine ⟨x2, fun i => ?_, h2, hX ▸ h3⟩
    rcases i with a | b
    · exact h1 (Sum.inl a)
    · have horth : ∀ v ∈ Set.range g2', (VS D).hT v x2 = 0 := by
        rintro _ ⟨c, rfl⟩
        exact h1 (Sum.inr c)
      have hb : g2 b ∈ Submodule.span D.host.E (Set.range g2') := by
        rw [hsp]; exact Submodule.subset_span ⟨b, rfl⟩
      exact LprExistA_orth_span horth _ hb
  · rw [← ht, ← hr]; exact hG.ratio
  · rw [← ht, ← ho']; exact hG.omp
  · rw [← ht, ← ho, ← hX]; exact hG.om

theorem gfacts_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hG : GFacts Λ f g1 (frameAct h ξ⁻¹) β) :
    GFacts Λ f g1 h β := by
  have hη := inv_unitri ξ h1 h2
  refine gfacts_move hG (Xs_frameAct_inv h ξ h1 h2) (span_frameAct_inv h ξ h1 h2) ?_
    (GDl_frameAct_top f h ξ⁻¹ hη.1 hη.2) (GDl_frameAct_r f h ξ⁻¹ hη.1 hη.2)
    (Gom'_frameAct f h ξ⁻¹ hη.1 hη.2) (Gom_frameAct f h ξ⁻¹ hη.1 hη.2)
  exact frameAct_last_sub h ξ⁻¹ (hη.2 _)

end Glob

section LocIota

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem iotaG_congr {q : E} {abelian₂ : Submodule M.L.O V} {r : ℕ} {f₀ f₁ f₂ f₂' : Fin (r + 1) → V} {e : V ≃ₗ[E] V}
    (hX : H.X f₂ = H.X f₂') (h : IotaG H q abelian₂ f₀ f₁ f₂ e) : IotaG H q abelian₂ f₀ f₁ f₂' e := by
  unfold IotaG at h ⊢
  rw [← hX]
  exact h

end LocIota

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locX_eq {g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)) :
    (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2' b)) = (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  apply le_antisymm
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2' a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc) := by
      rw [← hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hm)
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2' (sF' Z p) (isUnit_sF' Z p) hm)

theorem iotaEl_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hI : IotaEl Z p Λ f g1 (frameAct h ξ⁻¹) β) :
    IotaEl Z p Λ f g1 h β := by
  intro gg hgg
  exact iotaG_congr (locH Z p) (locX_eq Z p (Xs_frameAct_inv h ξ h1 h2)) (hI gg hgg)

end Loc

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

def frq (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) :=
  mapLF q.1.2 (lf D (X.Fu u'))

def fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Submodule D.host.E (VS D).V :=
  (lf D (X.Fu u)).fl.Xplus ⊔ (frq X q).fl.Xplus

def pointwiseStabilizerInfinite (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Set X.B.I.Ginf :=
  Hset X.B.I (X.crd '' (fixedSubspaceOfRepresentative X q : Set (VS D).V))

end Defs

def RelRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    t.relevant → t.G = 0 →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl ∧ Gval (lf D (X.Fu u)) (frq X t.rep) = 0

def CovRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl →
    ∀ Ω : Set X.B.I.Ginf, IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' q.1.2) Ω →
    OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1 →
    ∀ h ∈ pointwiseStabilizerInfinite X q,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       (X.piU u h).comp (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1) =
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1).comp
          (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1)))

def SchurNFC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    (∀ τ, uS D u τ ≠ uS D u' τ) →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ P : X.Vpi u' →L[ℂ] X.Vpi u,
      (∀ h ∈ pointwiseStabilizerInfinite X q, (X.piU u h).comp P = P.comp (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1))) → P = 0

section Asm

variable {D : D7} {X : HidaSetting D}

theorem words_differ {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) {u u' : D.what₂.Word} (huu : u ≠ u') :
    ∀ τ, uS D u τ ≠ uS D u' τ := by
  exact h.1.2.1.2.2.2.2.2.2.2.1 u u' huu

theorem aTerm_eq_zero_of_OOt {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    (t : GTerm X u u' F0 F0' what₂ rows') (h : OOt t = 0) : aTerm cs cs' FdN FdN' t = 0 := by
  have hb : ∀ ρ ρ', blk cs cs' FdN FdN' t ρ ρ' = 0 := by
    intro ρ ρ'
    simp [blk, h]
  ext φ : 1
  simp [aTerm, aTermL, hb]
  try rfl

theorem fundOf_spec {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hF : FundExists X u u' F0 F0' what₂ rows') (t : GTerm X u u' F0 F0' what₂ rows') :
    IsSFund X.B.I (ROinf t) (FundOf t) := by
  unfold FundOf
  split_ifs with h0
  · exact h0.choose_spec
  · exact absurd (hF t) h0

end Asm

end Formalism.L2.SG.KappaOffDiagonal
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.PairValDefs PI.NRCW IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable (D : D7)

theorem intP_fmat (P : HeightOneSpectrum (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E}
    (G : LFlag (D.sp.Y 0) D.R.rS T) (m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hm : m ∈ NLam Λ G)
    (hC : IsFixedConv Λ (gS D) G) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (hz : G.fl.z ∈ Λ)
    (c b : Fin (D.R.rS + 1)) : IntP P (fmat D G m c b) := by
  have hfLP : ∀ c, frame G c ∈ LP P Λ := by
    intro c
    induction c using Fin.lastCases with
    | last => rw [frame_last]; exact mem_localization_of_mem₃ P hz
    | cast i => rw [frame_castSucc]; exact e_mem_LP P hC hP i
  have hmLP : m (frame G b) - frame G b ∈ LP P Λ :=
    sub_mem_localization P (LP_map P (m : (VS D).V →ₗ[D.host.E] (VS D).V) (fun v hv => nlam_mem hm hv) (hfLP b)) (hfLP b)
  have h01 : ∀ (t : Prop) [Decidable t], IntP P (if t then (1 : D.host.E) else 0) := by
    intro t _
    split_ifs
    · simpa using intP_O P 1
    · simpa using intP_O P 0
  unfold fmat
  apply intP_add P (h01 _)
  split_ifs with h
  · exact coef_intP P hC hP hmLP (frame_d_mem G hm b) _
  · simpa using intP_O P 0

theorem frame_nm (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (b : Fin (D.R.rS + 1)) :
    n (m (frame G₁ b)) = ∑ d, (fmat D G n * fmat D G₁ m) d b • frame G d +
      n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
  rw [(stepExp D Λ G₁ m hm).2 b]
  have e1 : ∑ c, fmat D G₁ m c b • frame G₁ c =
      ∑ c, fmat D G₁ m c b • frame G c + ∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [← smul_add, add_sub_cancel]
  rw [e1, map_add (f := _)]
  congr 1

  rw [map_sum]
  simp only [map_smul, (stepExp D Λ G n hn).2, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ => ?_))
  rw [mul_comm]

theorem cong_at (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (G₁ G₂ : LFlag (D.sp.Y 0) D.R.rS T') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ NLam Λ G)
    (hm : m ∈ NLam Λ G₁) (hfr : ∀ a, frame G₂ a = n (m (frame G₁ a))) (hC : IsFixedConv Λ (gS D) G)
    (hC₁ : IsFixedConv Λ (gS D) G₁) (hA1 : AdmWit Λ (gS D) G G₁ 1) (hA2 : AdmWit Λ (gS D) G G₂ 1)
    (hz₁ : G₁.fl.z ∈ Λ) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (hg : ((gS D : ℕ) : D.host.E) ≠ 0) (d : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    IntP P ((fmat D G n * fmat D G₁ m - 1) d.castSucc b / (gS D : D.host.E)) := by
  have hw : ∀ c, frame G₁ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA1.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hw2 : ∀ c, frame G₂ c - frame G c ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    intro c
    have := hA2.2.2 c P hP
    rw [frameAct_one] at this
    exact this
  have hNU := (stepExp D Λ G n hn).1
  have hMU := (stepExp D Λ G₁ m hm).1

  set Y := ∑ d', (fmat D G n * fmat D G₁ m - 1) d' b • frame G d' with hYdef
  have hYeq : Y = (frame G₂ b - frame G b) - n (∑ c, fmat D G₁ m c b • (frame G₁ c - frame G c)) := by
    rw [hfr b, frame_nm D Λ G G₁ n m hn hm b, hYdef]
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]
    have e1 : ∑ d', (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) d' b • frame G d' = frame G b := by
      simp [Matrix.one_apply]
    rw [e1]
    abel
  have hYLg : Y ∈ LP P (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
    rw [hYeq]
    refine sub_mem (hw2 b) ?_
    exact LP_map P (n : (VS D).V →ₗ[D.host.E] (VS D).V) (nlam_gLam hn _)
      (LP_sum P _ _ fun c _ => smul_mem_localization P (intP_fmat D P Λ G₁ m hm hC₁ hP hz₁ c b) (hw c))

  have hlast : (fmat D G n * fmat D G₁ m - 1) (Fin.last D.R.rS) b = 0 := by
    rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.last D.R.rS)]
    · rw [(hNU _ _).2 rfl, one_mul, Matrix.one_apply]
      by_cases hb : Fin.last D.R.rS = b
      · rw [(hMU _ _).2 hb, if_pos hb, sub_self]
      · have hlt : b < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last b) (Ne.symm hb)
        rw [(hMU _ _).1 hlt, if_neg hb, sub_self]
    · intro c _ hc
      have hlt : c < Fin.last D.R.rS := lt_of_le_of_ne (Fin.le_last c) hc
      rw [(hNU _ _).1 hlt, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hYsum : Y = ∑ d' : Fin D.R.rS, (fmat D G n * fmat D G₁ m - 1) d'.castSucc b • G.fl.e d' := by
    rw [hYdef, Fin.sum_univ_castSucc, hlast, zero_smul, add_zero]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    rw [frame_castSucc]
  have hYX : Y ∈ G.fl.X := by
    rw [hYsum]
    exact Submodule.sum_mem _ fun d' _ => Submodule.smul_mem _ _ (e_mem_X _ d')
  have hcoef := coef_intP_g P hC hP hg hYLg hYX d
  have hYd : G.fl.coefX Y d = (fmat D G n * fmat D G₁ m - 1) d.castSucc b := by
    rw [hYsum, coefX_finset_sum _ _ _ (fun d' => Submodule.smul_mem _ _ (e_mem_X _ d'))]
    simp only [coefX_smul_e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hYd] at hcoef
  exact hcoef

end Cong

end Formalism.L2.SG.Pf.FibQ
end
end
