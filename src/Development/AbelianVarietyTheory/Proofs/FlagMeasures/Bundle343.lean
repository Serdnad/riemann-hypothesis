module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle334
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle335
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle336
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ScWlocExists
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle332
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle007

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL

theorem isLattice_map_equiv {E : Type} [Field E] [NumberField E] {V W : Type} [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (e : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map (((e : V →ₗ[E] W)).restrictScalars (𝓞 E))) := by
  exact Submodule.IsLattice.of_fg E (hΛ.fg.map _)

theorem term_lat_isLattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (t : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V), Submodule.IsLattice D.host.E (c.lat ρ t.lam) := by
  intro D X Y u u' Z T T' F0 F0' FP G c t ρ
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hL : Submodule.IsLattice D.host.E t.lam := hrow.1.1.toIsLattice
  exact isLattice_map_equiv (ρ.trans c.e) t.lam hL

end GlobalTheory.HL
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_castSucc_eq_hyperbolic (a : Fin D.R.rS) : (GlobalTheory.TypeAsm.F0 X u).e a.castSucc = X.eX a := by
  show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
  rw [GlobalTheory.TypeAsm.fv_cast]
  exact congrFun (X.Fu_e u) a

theorem fixedFrameOfWord_last_eq_anisotropic : (GlobalTheory.TypeAsm.F0 X u).e (Fin.last _) = X.zu u := by
  show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
  rw [GlobalTheory.TypeAsm.fv_last]
  exact X.flagZVector u

theorem fixedFrameOfWord_isotropicSpan_eq : (GlobalTheory.TypeAsm.F0 X u).X = Submodule.span D.host.E (Set.range X.eX) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, fixedFrameOfWord_castSucc_eq_hyperbolic]
  exact ⟨fun ⟨b, _, h⟩ => ⟨b, h⟩, fun ⟨b, h⟩ => ⟨b, b.isLt, h⟩⟩

theorem hT_span_left {v : (VS D).V} (hv : ∀ a, (VS D).hT (X.eX a) v = 0) {y : (VS D).V}
    (hy : y ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy

  simp [map_sum, hv]

theorem hT_span_span {y y' : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range X.eX))
    (hy' : y' ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y y' = 0 := by
  refine hT_span_left X (fun a => ?_) hy
  exact p_symm_zero (VS D) (hT_span_left X (fun b => X.ee b a) hy')

theorem hT_f_e (a b : Fin D.R.rS) : (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
  rw [a_herm (S := VS D) (X.eX a) (X.fY b), X.ef a b]
  split_ifs <;> simp

theorem span_eq_zero {d : (VS D).V} (hd : d ∈ Submodule.span D.host.E (Set.range X.eX))
    (h : ∀ b, (VS D).hT (X.fY b) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hd
  have hc : ∀ b, c b = 0 := by
    intro b
    have := h b

    simpa [map_sum, hT_f_e] using this
  simp [hc]

end GlobalTheory.RowsOrb.ModelIso

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def corr (W : Submodule D.host.E (VS D).V) : W →ₗ[D.host.E] (VS D).V :=
  ∑ a, LinearMap.smulRight (((VS D).hT (X.fY a)).comp W.subtype) (X.eX a)

theorem corr_apply (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w = ∑ a, (VS D).hT (X.fY a) (w : (VS D).V) • X.eX a := by
  simp [corr, LinearMap.sum_apply]

theorem corr_mem (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w ∈ Submodule.span D.host.E (Set.range X.eX) := by
  rw [corr_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.RowsOrb.ModelIso


open GlobalTheory.RowsOrb.ModelIso in
theorem GlobalTheory.RowsOrb.ub_equiv_model : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (GlobalTheory.TypeAsm.F0 X u) HW W.subtype →
    ∃ e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W, (∀ x y, HW.B.flip (e x) (e y) = GlobalTheory.RowsOrb.hU X u x y) ∧
      ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X := by
  intro D X u W HW hE

  have hWe : ∀ (w : W) a, (VS D).hT (X.eX a) (w : (VS D).V) = 0 := by
    intro w a
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) a.castSucc
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e a.castSucc) = 0 at h
    rw [fixedFrameOfWord_castSucc_eq_hyperbolic] at h
    exact p_symm_zero (VS D) h
  have hWz : ∀ w : W, (VS D).hT (X.zu u) (w : (VS D).V) = 0 := by
    intro w
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) (Fin.last _)
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e (Fin.last _)) = 0 at h
    rw [fixedFrameOfWord_last_eq_anisotropic] at h
    exact p_symm_zero (VS D) h
  have hXW : ∀ (w : W) {y : (VS D).V}, y ∈ Submodule.span D.host.E (Set.range X.eX) →
      (VS D).hT y (w : (VS D).V) = 0 ∧ (VS D).hT (w : (VS D).V) y = 0 := by
    intro w y hy
    have h := hT_span_left X (hWe w) hy
    exact ⟨h, p_symm_zero (VS D) h⟩
  have hBW : ∀ x y : W, HW.B x y = (VS D).hT (y : (VS D).V) (x : (VS D).V) := fun x y => (hE.1 x y).symm

  have hmWb : ∀ w : W, (w : (VS D).V) - corr X W w ∈ GlobalTheory.RowsOrb.Wb X := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Wb]
    intro b
    have hc := corr_mem X W w
    refine ⟨?_, ?_⟩
    · rw [map_sub, hWe w b, zero_sub, neg_eq_zero]
      exact p_symm_zero (VS D) (hT_span_left X (fun a => X.ee a b) hc)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, corr_apply, map_sum]
        simp only [map_smul, hT_f_e, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, sub_self]
  have hmUb : ∀ w : W, (⟨(w : (VS D).V) - corr X W w, hmWb w⟩ : GlobalTheory.RowsOrb.Wb X) ∈ GlobalTheory.RowsOrb.Ub X u := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Ub]
    change (VS D).hT (X.zu u) ((w : (VS D).V) - corr X W w) = 0
    rw [map_sub, hWz w, zero_sub, neg_eq_zero]
    refine p_symm_zero (VS D) (hT_span_left X (fun a => (X.zu_orth u a).1) (corr_mem X W w))
  let g : W →ₗ[D.host.E] GlobalTheory.RowsOrb.Ub X u :=
    { toFun := fun w => ⟨⟨(w : (VS D).V) - corr X W w, hmWb w⟩, hmUb w⟩
      map_add' := fun x y => by ext; simp only [Submodule.coe_add, map_add (f := _)]; abel
      map_smul' := fun c x => by ext; simp [smul_sub] }
  have hg : ∀ w, (((g w : GlobalTheory.RowsOrb.Wb X)) : (VS D).V) = (w : (VS D).V) - corr X W w := fun _ => rfl
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : (w : (VS D).V) = corr X W w := by
      have := congrArg (fun x : GlobalTheory.RowsOrb.Ub X u => ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V)) hw
      simp only [hg, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.1 this
    have hmem : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := h0 ▸ corr_mem X W w
    exact HW.nondeg w fun y => by rw [hBW]; exact (hXW y hmem).2
  have hsurj : Function.Surjective g := by
    intro x
    have hv : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      intro a
      change (VS D).hT _ ((GlobalTheory.TypeAsm.F0 X u).e a) = 0
      refine Fin.lastCases ?_ (fun b => ?_) a
      · rw [fixedFrameOfWord_last_eq_anisotropic]; exact p_symm_zero (VS D) ((GlobalTheory.RowsOrb.mem_Ub X u _).1 x.2)
      · rw [fixedFrameOfWord_castSucc_eq_hyperbolic]; exact p_symm_zero (VS D) ((((x : GlobalTheory.RowsOrb.Wb X)).2 b).1)
    obtain ⟨y, ⟨w, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 ((hE.2 _).1 hv)
    refine ⟨w, ?_⟩
    rw [fixedFrameOfWord_isotropicSpan_eq] at hz
    have hd : ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) - ((g w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      apply span_eq_zero X
      · rw [hg, ← hyz]
        have : (W.subtype w + z) - ((w : (VS D).V) - corr X W w) = z + corr X W w := by
          simp only [Submodule.subtype_apply]; abel
        rw [this]
        exact Submodule.add_mem _ hz (corr_mem X W w)
      · intro b
        exact ((Submodule.sub_mem _ (x : GlobalTheory.RowsOrb.Wb X).2 (g w : GlobalTheory.RowsOrb.Wb X).2) b).2
    ext
    exact (sub_eq_zero.1 hd).symm
  let e := (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).symm
  have hge : ∀ x, g (e x) = x := fun x => (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).apply_symm_apply x
  have hxe : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = ((e x : W) : (VS D).V) - corr X W (e x) := by
    intro x
    rw [← hg (e x), hge x]
  refine ⟨e, fun x y => ?_, fun x => ?_⟩
  · rw [LinearMap.flip_apply, hBW, GlobalTheory.RowsOrb.hU_apply, hxe x, hxe y]
    have h1 := (hXW (e y) (corr_mem X W (e x))).1
    have h2 := (hXW (e x) (corr_mem X W (e y))).2
    have h3 := hT_span_span X (corr_mem X W (e x)) (corr_mem X W (e y))
    simp only [map_sub, LinearMap.sub_apply, h1, h2, h3, sub_zero]
  · rw [hxe x, sub_sub_cancel, fixedFrameOfWord_isotropicSpan_eq]
    exact corr_mem X W (e x)
end
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Glue

open GlobalTheory.LoopC.RowGlue

theorem glue_isLattice_unimodular : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D), GlobalTheory.TypeAsm.Std D large₂ → ∀ L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X), Submodule.IsLattice D.host.E L → Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L → Submodule.IsLattice D.host.E (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) := by
  intro D large₂ X _ L hL hU
  have H : IsHypFrame (VS D).hT X.eX X.fY := ⟨(VS D).herm, X.ee, X.ff, X.ef⟩
  have h0 : ∀ a, aaD D a ≠ 0 := fun a => zpow_ne_zero _ (ddS_ne_zero D)
  have hs : ∀ a, StarStable (aaD D a) := fun a => (ddS_stable D).zpow (ddS_ne_zero D) _
  have hmid : ∀ w ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)),
      Mid (VS D).hT X.eX X.fY w := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  refine ⟨Submodule.IsLattice.of_fg D.host.E (((sumS_fg _ _).sup (hL.fg.map _)).sup (sumS_fg _ _)), (H.unimodular_iff (A := fun a => aaD D a) (B := fun a => (aaD D a)⁻¹) hmid
      (fun a => inv_ne_zero (h0 a)) (fun a => (hs a).inv (h0 a)) (fun a => (inv_inv _).symm)).2 ?_⟩
  · intro w hw
    have key : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L ↔
        (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) ∈ L := by
      rw [show Formalism.HermitianLatticesTheory.dual (GlobalTheory.RowsOrb.hb X) L = L from hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at key ⊢
    constructor
    · intro h
      exact ⟨⟨w, hw⟩, key.1 fun y hy => h y ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w', hw', e⟩ _ ⟨y, hy, rfl⟩
      have e' : (⟨w, hw⟩ : GlobalTheory.RowsOrb.Wb X) = w' := Subtype.ext e.symm
      exact key.2 (e' ▸ hw') y hy

end GlobalTheory.RowsOrb.Glue
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb

variable {D : D7}

theorem eq_zero_of_mem_span_eX (X : HidaSetting D) (w : (VS D).V)
    (hw : w ∈ Submodule.span D.host.E (Set.range X.eX)) (hf : ∀ b, (VS D).hT (X.fY b) w = 0) : w = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hw
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := hf b

    simp only [map_sum, map_smul, smul_eq_mul] at h
    have hfe : ∀ a, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
      intro a
      rw [a_herm, X.ef a b]
      split_ifs <;> simp
    simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  simp [hc]

theorem pd_hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  intro D X u τ x hx
  have hpos : (GlobalTheory.TypeAsm.F0 X u).PosDefAt τ :=
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (GlobalTheory.TypeAsm.tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) τ
  set w : (VS D).V := ((x : Wb X) : (VS D).V) with hwdef
  have hWb := (mem_Wb X _).1 (x : Wb X).2
  have hUb := (mem_Ub X u _).1 x.2
  have hw0 : w ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext (Subtype.ext h)
  have h1 : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) w = 0 := by
    intro a
    change (VS D).hT w ((X.Fu u).fvec a) = 0
    induction a using Fin.lastCases with
    | last =>
      rw [FlagG.fvec, Fin.snoc_last, X.flagZVector]
      exact p_symm_zero (VS D) hUb
    | cast b =>
      rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
      exact p_symm_zero (VS D) (hWb b).1
  have h2 : w ∉ (GlobalTheory.TypeAsm.F0 X u).X := by
    intro hX
    apply hw0
    refine eq_zero_of_mem_span_eX X w ?_ (fun b => (hWb b).2)
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨b, -, rfl⟩
    change (X.Fu u).fvec b.castSucc ∈ _
    rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
    exact Submodule.subset_span ⟨b, rfl⟩
  have := hpos w h1 h2
  rw [hU_apply]
  exact this

end GlobalTheory.RowsOrb
end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

private theorem host_star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := D.host.φ₀) (x := x)
  have h2 : D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) := by
    rw [← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
  rw [h1, h2]

theorem mem_UJ_gramN_iff_map_symm : ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin (D.R.N 0)) D.host.E), g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ↔ (((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm).map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm := by
  intro D X g

  have hc : ∀ y : D.host.E, X.ιE.symm ((Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) y) =
      starRingEnd X.B.I.E (X.ιE.symm y) := by
    intro y
    apply X.ιE.injective
    rw [starRingEnd_apply, X.ιE_conj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact host_star_eq_conj D y
  have hm : ∀ A B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A * B).map X.ιE.symm = A.map X.ιE.symm * B.map X.ιE.symm := by
    intro A B
    ext i j

    simp [Matrix.mul_apply, map_sum]
  have hb : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      (A.map X.ιE.symm).map (starRingEnd X.B.I.E) =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)).map X.ιE.symm := by
    intro A
    ext i j
    exact (hc (A i j)).symm
  have hT : ∀ A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E,
      Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) A =
        (A.map (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E))ᵀ := by
    intro A
    unfold Formalism.UG.cT
    first
      | rfl
      | (ext i j; rfl)
  have hinj : Function.Injective
      (fun A : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E => A.map X.ιE.symm) :=
    Matrix.map_injective X.ιE.symm.injective
  refine Iff.trans (Iff.rfl : _ ↔ Formalism.UG.cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E)
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) * Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) *
      (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ?_
  rw [hT, hb, ← Matrix.transpose_map (f := ⇑X.ιE.symm), ← hm, ← hm]
  exact hinj.eq_iff.symm

end GlobalTheory.St
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_inv_pow_different_iff_local : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E, y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  first | exact @GlobalTheory.DiffLoc.mem_ddPow_neg_iff | exact GlobalTheory.DiffLoc.mem_ddPow_neg_iff | (intros; apply GlobalTheory.DiffLoc.mem_ddPow_neg_iff <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.frame_factors_local_units_almost_all : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  first | exact @GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite | exact GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite | (intros; apply GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite <;> assumption)
end

section

open NumberField Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc

theorem _root_.GlobalTheory.T.gram_invariant_pow_le_haar_weight : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (r k TT : ℕ) (rd H : ℝ) (γ : PN.Pts E r), 0 < rd → (∀ a, 1 ≤ ∏ v : InfinitePlace E, (rd ^ (2 * (endIdx γ a * (2 * r + 1 - endIdx γ a))))⁻¹ * v (endMin γ a) ^ 2) → NDPt rd γ ≤ H → NGPt rd TT γ ^ (k - 1) ≤ H ^ (6 * (2 * r + 2)) * nPt rd k TT γ := by
  first | exact @GlobalTheory.HaarWeight.gram_pow_le_haar | exact GlobalTheory.HaarWeight.gram_pow_le_haar | (intros; apply GlobalTheory.HaarWeight.gram_pow_le_haar <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  first | exact @GlobalTheory.St.G.midLat_selfDual_pairing | exact GlobalTheory.St.G.midLat_selfDual_pairing | (intros; apply GlobalTheory.St.G.midLat_selfDual_pairing <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moved_type_vectors_span_fixed_lattice_vector_mod_level : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  first | exact @GlobalTheory.St.G.SpanMoved.span_moved | exact GlobalTheory.St.G.SpanMoved.span_moved | (intros; apply GlobalTheory.St.G.SpanMoved.span_moved <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem wlocExists_real : WlocExists :=
  scWlocExists Formalism.L2.SG.HCReprodM.hcReprodDSm

end GlobalTheory
end

section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.haar_volume_thin_tube_unitary_product_asymptotic : ∀ (k : ℕ) (η : ℝ), 1 ≤ k → (η = 1 ∨ η = -1) → ∀ (μ : Measure (PI.MtM (k + 1))) (μ₀ : Measure (PI.MtM k)) (c c₀ : ℝ), 0 < c → 0 < c₀ → PI.IsHaarOnM (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ → HasDens (UH (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then (η : ℂ) else 1)) μ (ENNReal.ofReal c) → PI.IsHaarOnM (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ → μ₀ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin k) (Fin k) ℂ)) μ₀ (ENNReal.ofReal c₀) → Tendsto (fun t : ℝ => μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  first | exact @GlobalTheory.Tube.thin_tube | exact GlobalTheory.Tube.thin_tube | (intros; apply GlobalTheory.Tube.thin_tube <;> assumption)
end
