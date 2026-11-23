module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameStep

theorem frame_mapLF {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) :
    frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem upUni_of_uni {N : ℕ} {K : Type} [Field K] {A : Matrix (Fin N) (Fin N) K} (h : GlobalTheory.LocOver.Uni A) :
    IsUpUni A := fun i j => ⟨fun hij => h.1 i j hij, fun hij => by subst hij; exact h.2 i⟩

theorem upUni_mul {N : ℕ} {K : Type} [Field K] {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A)
    (hB : IsUpUni B) : IsUpUni (A * B) := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentMulFlagMeasures.isUpUni_mul ..)

theorem unip_tri {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : ∃ A : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧
      ∀ b, n (frame F b) = ∑ a, A a b • frame F a := by
  have hmap : ∀ a, (mapFlag n hn.1 F.fl).fvec a = n (F.fl.fvec a) := by
    intro a
    induction a using Fin.lastCases with
    | last => simp [FlagG.fvec, mapFlag]
    | cast i => simp [FlagG.fvec, mapFlag]
  obtain ⟨A, hA, hc⟩ := GlobalTheory.FlagChange.tri_of_unip F.fl (mapFlag n hn.1 F.fl) n hn.2.1 hn.2.2 hmap
  refine ⟨A, upUni_of_uni hA, fun b => ?_⟩
  rw [← hmap b]
  exact hc b

theorem sum_change {D : D7} (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U A : Formalism.L2.SG.PairVal.MatR D) (hU : ∀ b, g (f b) = ∑ a, U a b • f0 a) (b : Fin (D.R.rS + 1)) :
    g (∑ a, A a b • f a) = ∑ c, (U * A) c b • f0 c := by

  simp only [map_sum, map_smul, hU, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

theorem step : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' F00 F'0 t₀ ρ U U' hM t n m ⟨hn, hm, ht⟩
  obtain ⟨hρ, hU, hU', hf, hf'⟩ := hM
  obtain ⟨A, hA, hnA⟩ := unip_tri _ n hn
  obtain ⟨A', hA', hmA'⟩ := unip_tri _ m hm
  have ht0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have ht1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  refine ⟨A, A', hA, hA', hnA, hmA', Subgroup.mul_mem _ hρ hn.1, upUni_mul hU hA, upUni_mul hU' hA', ?_, ?_⟩
  · intro b
    rw [LinearEquiv.mul_apply]
    exact (congrArg ρ (hnA b)).trans (sum_change ρ _ _ U A hf b)
  · intro b
    have h0 : ∀ a, (ρ * t₀.lin) (frame (lf D (X.Fu u')) a) = ∑ c, U' c a • frame F'0 c := by
      intro a
      rw [LinearEquiv.mul_apply, ← hf' a]
      show _ = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) a)
      rw [frame_mapLF _ ht0]
    have e1 : frame t.frame b = t.lin (frame (lf D (X.Fu u')) b) := frame_mapLF _ ht1 _ b
    rw [e1, ht]
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
    have hinv : ∀ x, n (n⁻¹ x) = x := fun x => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [hinv, hmA' b]
    have := sum_change (ρ * t₀.lin) _ _ U' A' h0 b
    simpa only [LinearEquiv.mul_apply] using this

end GlobalTheory.FrameStep
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocReflect

variable {D : D7}

theorem mem_of_baseChange_mem_span (p : PlF D) (W : Submodule D.host.E (VS D).V) {y : (VS D).V}
    (hy : baseChange₂ D p y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V))) : y ∈ W := by
  by_contra hyW
  obtain ⟨φ, hφy, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyW inferInstance
  let ψ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep :=
    { toFun := fun v => ∑ i, (D.s.atP p).ιE (φ ((VS D).frame i)) * v i
      map_add' := fun v w => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  have hψ : ∀ x, ψ (baseChange₂ D p x) = (D.s.atP p).ιE (φ x) := by
    intro x
    show ∑ i, (D.s.atP p).ιE (φ ((VS D).frame i)) * (D.s.atP p).ιE ((VS D).frame.repr x i) = _
    conv_rhs => rw [← (VS D).frame.sum_repr x]

    simp only [map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hle : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V)) ≤ LinearMap.ker ψ := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    show ψ (baseChange₂ D p w) = 0
    rw [hψ]
    have : φ w ∈ W.map φ := Submodule.mem_map_of_mem hw
    rw [hφW, Submodule.mem_bot] at this
    rw [this, map_zero]
  have h0 : ψ (baseChange₂ D p y) = 0 := hle hy
  rw [hψ] at h0
  exact hφy ((map_eq_zero_iff _ (RingHom.injective (D.s.atP p).ιE)).1 h0)

theorem span_scaled_le (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (S : Set (Fin D.R.rS)) :
    Submodule.span (D.s.atP p).Ep ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' S) ≤
      Submodule.span (D.s.atP p).Ep
        (baseChange₂ D p '' ((Submodule.span D.host.E (F.fl.e '' S) : Submodule D.host.E (VS D).V) : Set (VS D).V)) := by
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  show frFac Z.δ p b.castSucc • baseChange₂ D p (frame F b.castSucc) ∈ _
  rw [GlobalTheory.LocExt.frame_castSucc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨b, hb, rfl⟩, rfl⟩)

theorem mem_nrat_of_ext : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p),
    GlobalTheory.LocOver.Ext p γ g → g ∈ NU (locH Z p) (scaled Z p (frame F)) → γ ∈ NRat F := by
  intro D Z p T F γ g hE hN
  obtain ⟨hU, hfl, hperp⟩ := hN
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    apply RingHom.injective (D.s.atP p).ιE
    show (D.s.atP p).ιE (brS (VS D) (γ y) (γ x)) = (D.s.atP p).ιE (brS (VS D) y x)
    rw [← baseChangeAt_form Z.M p (Z.hcj p), ← baseChangeAt_form Z.M p (Z.hcj p), ← hE, ← hE]
    exact hU (baseChange₂ D p y) (baseChange₂ D p x)
  · intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : a.1 < j + 1 := ha
      have h1 := hfl a
      have e : g (scaled Z p (frame F) a.castSucc) - scaled Z p (frame F) a.castSucc =
          frFac Z.δ p a.castSucc • baseChange₂ D p (γ (F.fl.e a) - F.fl.e a) := by
        simp only [scaled, GlobalTheory.LocExt.frame_castSucc, map_smul, hE (F.fl.e a), map_sub, smul_sub]
      rw [e] at h1
      obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a.castSucc
      have h2 := Submodule.smul_mem _ ((u⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) (span_scaled_le Z p F {b | b < a} h1)
      rw [← hu, smul_smul, Units.inv_mul, one_smul] at h2
      have h3 := mem_of_baseChange_mem_span p _ h2
      exact GlobalTheory.FlagChange.Xa_mono F.fl (Nat.lt_succ_iff.1 ha') h3
    | zero => simp
    | add x y _ _ ihx ihy =>
      have e : γ (x + y) - (x + y) = (γ x - x) + (γ y - y) := by rw [map_add (f := _)]; abel
      rw [e]; exact Submodule.add_mem _ ihx ihy
    | smul c x _ ih =>
      rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ ih
  · intro x hx
    have hb : baseChange₂ D p x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨a, rfl⟩ := hu
        show (locH Z p).h (baseChange₂ D p x) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame F a.castSucc)) = 0
        rw [(locH Z p).h_herm, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm]
        have h0 : (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p (frame F a.castSucc)) = 0 := by
          show LocFacts₂ Z.M p (baseChange₂ D p x) (baseChange₂ D p (frame F a.castSucc)) = 0
          rw [baseChangeAt_form Z.M p (Z.hcj p), GlobalTheory.LocExt.frame_castSucc]
          show (D.s.atP p).ιE ((VS D).hT (F.fl.e a) x) = 0
          rw [GlobalTheory.FlagChange.mem_orth_X.1 hx (F.fl.e a) (GlobalTheory.FlagChange.e_mem_X F.fl a), map_zero]
        rw [h0, mul_zero]
      | zero =>
        rw [(locH Z p).h_herm, (locH Z p).h_zero_left, map_zero]
      | add u v _ _ ihu ihv =>
        rw [(locH Z p).h_herm, (locH Z p).h_add_left, map_add (f := _), ← (locH Z p).h_herm, ← (locH Z p).h_herm, ihu, ihv,
          add_zero]
      | smul c u _ ih =>
        rw [(locH Z p).h_herm, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm, ih, mul_zero]
    have h2 := hperp _ hb
    rw [hE, ← map_sub] at h2
    have h3 : baseChange₂ D p (γ x - x) ∈ Submodule.span (D.s.atP p).Ep
        ((fun b : Fin D.R.rS => scaled Z p (frame F) b.castSucc) '' Set.univ) := by
      rw [Set.image_univ]; exact h2
    have h4 := mem_of_baseChange_mem_span p _ (span_scaled_le Z p F Set.univ h3)
    rw [Set.image_univ] at h4
    exact h4

end GlobalTheory.LocReflect
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.CoverAct

theorem ratLink_mem_ROinf : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  intro D X Y W u u' s n hn
  obtain ⟨h1, h2⟩ := hn
  have hδ := W.isom u
  have hm1 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam (lf D (X.Fu u)) := by
    rw [← Formalism.L2.SG.TermTieOf.mapL_lf W u] at h1
    exact (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h1
  have hm2 : (W.δ u)⁻¹ * n * W.δ u ∈ NLam s.lam s.frame :=
    (Formalism.L2.SG.Pf.mem_NLam_map (W.δ u) hδ _ _ _).1 h2
  have hiso : (W.δ u)⁻¹ * n * W.δ u ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    mul_mem (mul_mem (inv_mem hδ) h1.1.1) hδ
  have hlin : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hlam : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hfr : s.frame = Formalism.L2.SG.Saturated.mapL s.lin hlin (lf D (X.Fu u')) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hlin]
    rfl
  rw [hfr, ← hlam] at hm2
  have hm3 := (Formalism.L2.SG.Pf.mem_NLam_map s.lin hlin _ _ _).1 hm2
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X _ hiso
  exact ⟨x, hx, x, _, hx, rfl, hm1, hm3⟩

end GlobalTheory.CoverAct
end
