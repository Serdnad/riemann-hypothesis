module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle339
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle340
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → gS D ≠ 0 ∧ ∀ p, (G.c p : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) * (gS D : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp) = (show ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp from Y.δ p) * (G.S p).th := by
  first | exact @GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | exact GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta | (intros; apply GlobalTheory.HL.GCoord.c_mul_gS_eq_delta_theta <;> assumption)
end

section

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.GluingNum

variable (D : D7)

abbrev jz (z : (VS D).V) : ((D.sp.X 0).V × D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
  ((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V z)).restrictScalars (𝓞 D.host.E)

theorem jz_apply (z : (VS D).V) (p : (D.sp.X 0).V × D.host.E) :
    jz D z p = D.sp.iXY 0 p.1 + p.2 • z := rfl

theorem mem_Wb (v : (hS D).V) : v ∈ Wb D ↔
    (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ ∀ a, (hS D).hT (D.sp.hypF a) v = 0 := by
  apply _root_.GlobalTheory.LoopC.GlueCount.mem_Wb <;> assumption

theorem eq_zero_of_mem_X {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE)
    {x : (hS D).V} (hx : x ∈ F0.X) (hw : x ∈ Wb D) : x = 0 := by
  apply _root_.GlobalTheory.LoopC.GlueCount.eq_zero_of_mem_X <;> assumption

theorem iXY_mem_Wb (w : (D.sp.X 0).V) : D.sp.iXY 0 w ∈ Wb D :=
  (mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2⟩

theorem zmOf_mem_Wb (u : D.what₂.Word) : D.zmOf u ∈ Wb D :=
  Submodule.smul_mem _ _ ((mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2⟩)

theorem jz_mem_Wb (u : D.what₂.Word) (p : (D.sp.X 0).V × D.host.E) : jz D (D.zmOf u) p ∈ Wb D := by
  rw [jz_apply]
  exact (Wb D).add_mem (iXY_mem_Wb D _) ((Wb D).smul_mem _ (zmOf_mem_Wb D u))

theorem exists_jz (u : D.what₂.Word) (F0 : Fb D u) (hT : Tu D u ≠ 0) (he : F0.e = D.sp.hypE)
    (hz : F0.z = D.zmOf u) {v : (hS D).V} (hv : v ∈ Wb D) : ∃ p, jz D (D.zmOf u) p = v := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  set c : D.host.E := -((hS D).hT F0.z v) / ((Tu D u : ℕ) : D.host.E) with hc
  have hvz : v - c • D.zmOf u ∈ Wb D := (Wb D).sub_mem hv ((Wb D).smul_mem _ (zmOf_mem_Wb D u))
  have h1 : v - c • D.zmOf u ∈ orth (hS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
    · rw [he]; exact ((mem_Wb D _).1 hvz).1 a
    · rw [← hz, map_sub, map_smul, F0.z_norm, smul_eq_mul, hc]
      field_simp
      ring
  rw [← hW] at h1
  obtain ⟨_, ⟨w, rfl⟩, x, hx, hs⟩ := Submodule.mem_sup.1 h1
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = (v - c • D.zmOf u) - D.sp.iXY 0 w := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem hvz (iXY_mem_Wb D w)
  refine ⟨(w, c), ?_⟩
  rw [hx0, add_zero] at hs
  rw [jz_apply, hs]
  simp

theorem comap_sup_X (u : D.what₂.Word) (F0 : Fb D u) (he : F0.e = D.sp.hypE)
    (L : LatV D) (hL : L ≤ toO (hS D) (Wb D)) :
    (L ⊔ toO (hS D) F0.X).comap (jz D (D.zmOf u)) = L.comap (jz D (D.zmOf u)) := by
  apply le_antisymm _ (Submodule.comap_mono le_sup_left)
  intro p hp
  obtain ⟨l, hl, x, hx, hs⟩ := Submodule.mem_sup.1 hp
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = jz D (D.zmOf u) p - l := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem (jz_mem_Wb D u p) (hL hl)
  rw [hx0, add_zero] at hs
  change jz D (D.zmOf u) p ∈ L
  rw [← hs]; exact hl

theorem mem_Lsub {T : D.host.E} (F : Fg D T) (Λ : LatV D) (v : (hS D).V) :
    v ∈ Lsub Λ F ↔ v ∈ orth (hS D) (Xsp F) ∧
      ∃ l ∈ Λ, l ∈ orth (hS D) (Xsp F) ∧ v - l ∈ Xsp F := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨l, hl, x, hx, hs⟩ := Submodule.mem_sup.1 h1
    refine ⟨h2, l, hl.1, hl.2, ?_⟩
    rw [← hs]; simpa using hx
  · rintro ⟨h2, l, hl, hl', hx⟩
    refine ⟨Submodule.mem_sup.2 ⟨l, ⟨hl, hl'⟩, v - l, hx, by abel⟩, h2⟩

theorem Lsub_gmap {T : D.host.E} (F : Fg D T) (Λ : LatV D) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hn : FixFr D F n) : Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  obtain ⟨h1, h2, h3⟩ := hn
  have key : ∀ l, n l ∈ orth (hS D) (Xsp F) ↔ l ∈ orth (hS D) (Xsp F) := by
    intro l
    have he : ∀ a, (hS D).hT (F.fl.e a) (n l) = (hS D).hT (F.fl.e a) l := by
      intro a
      have := h2 a.castSucc
      simp only [frame, FlagG.fvec, Fin.snoc_castSucc] at this
      conv_lhs => rw [← this]
      exact h1 _ _
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h
      exact Formalism.MainNotions.hT_zero_of_mem_X F.fl (fun a => by
        rw [← he]; exact h _ (Submodule.subset_span ⟨a, rfl⟩))
    · intro h
      exact Formalism.MainNotions.hT_zero_of_mem_X F.fl (fun a => by
        rw [he]; exact h _ (Submodule.subset_span ⟨a, rfl⟩))
  ext v
  rw [mem_Lsub, mem_Lsub]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro ⟨_, ⟨l, hl, rfl⟩, hl', hx⟩
    have hl2 : l ∈ orth (hS D) (Xsp F) := (key l).1 hl'
    refine ⟨l, hl, hl2, ?_⟩
    have := (Xsp F).add_mem hx (h3 l hl2)
    convert this using 1
    change v - l = v - n l + (n l - l)
    abel
  · rintro ⟨l, hl, hl', hx⟩
    refine ⟨n l, ⟨l, hl, rfl⟩, (key l).2 hl', ?_⟩
    have := (Xsp F).sub_mem hx (h3 l hl')
    convert this using 1
    abel

theorem le_Wb_of_mem (u : D.what₂.Word) {M : LatW D} {L : LatV D} (hL : L ∈ glueSet D u M) :
    L ≤ toO (hS D) (Wb D) := by
  intro x hx
  change x ∈ Wb D
  rw [← hL.2.1]
  exact Submodule.subset_span hx

theorem comap_jz_inl (z : (VS D).V) (L : LatV D) :
    (L.comap (jz D z)).comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) =
      L.comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) := by
  ext w
  change jz D z (w, 0) ∈ L ↔ D.sp.iXY 0 w ∈ L
  rw [jz_apply]
  simp

theorem gluingNum : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  intro D u hp h3 hs F0 he hz Λ hΛ M hM
  have hB : IsBase D u F0 := ⟨he, hz⟩
  have h1 : 1 ≤ Tu D u := by omega
  rw [← (GlobalTheory.T.ncard_gluedMiddleLattices_eq_pow_prime_sub_one D u F0 Λ hp h3 hs hB hΛ M hM).2]
  have hinj : Set.InjOn (fun L : LatV D => L.comap (jz D (D.zmOf u))) (glueSet D u M) := by
    have aux : ∀ L₁ ∈ glueSet D u M, ∀ L₂ : LatV D,
        L₁.comap (jz D (D.zmOf u)) = L₂.comap (jz D (D.zmOf u)) → L₁ ≤ L₂ := by
      intro L₁ h₁ L₂ h x hx
      obtain ⟨p, rfl⟩ := exists_jz D u F0 hp.ne_zero he hz (le_Wb_of_mem D u h₁ hx)
      have : p ∈ L₁.comap (jz D (D.zmOf u)) := hx
      rw [h] at this
      exact this
    intro L₁ h₁ L₂ h₂ h
    exact le_antisymm (aux L₁ h₁ L₂ h) (aux L₂ h₂ L₁ h.symm)
  rw [← hinj.ncard_image]
  congr 1
  ext 𝓛
  rw [hz]
  constructor
  · rintro ⟨⟨Λ', hΛ', rfl⟩, hc⟩
    obtain ⟨n, hn, hsp, hrow⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ' hB hΛ' h1
    obtain ⟨hg, hL⟩ := (GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 _ h1 hB hrow).1 hsp
    have e : (Lsub Λ' (lf D F0)).comap (jz D (D.zmOf u)) =
        (Formalism.HermitianLatticesTheory.gmap n Λ' ⊓ toO (hS D) (Wb D)).comap (jz D (D.zmOf u)) := by
      rw [← Lsub_gmap D (lf D F0) Λ' n hn, hL, comap_sup_X D u F0 he _ inf_le_right]
    refine ⟨Formalism.HermitianLatticesTheory.gmap n Λ' ⊓ toO (hS D) (Wb D),
      ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, ?_⟩, e.symm⟩
    rw [← comap_jz_inl D (D.zmOf u), ← e]
    exact hc
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨hrow, hsp, hW⟩ := (GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ h1 hB hΛ).2 M L hL
    have hL' := ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 _ h1 hB hrow).1 hsp).2
    refine ⟨⟨_, hrow, ?_⟩, ?_⟩
    · rw [hL', hW]
      exact comap_sup_X D u F0 he L (le_Wb_of_mem D u hL)
    · exact (comap_jz_inl D (D.zmOf u) L).trans hL.2.2.2.2.2

end GlobalTheory.LoopC.GluingNum

end
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

theorem rowsLift_mem_orth {U : Submodule E S.V} {x : S.V} :
    x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem rowsLift_fix_span {ι : Type} (v : ι → S.V) (s : Set ι) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ a, n (v a) = v a) : ∀ x ∈ Submodule.span E (v '' s), n x = x := by
  intro x hx
  have hle : Submodule.span E (v '' s) ≤ LinearMap.eqLocus (n : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_eqLocus]
    simpa using hn a
  have h := hle hx
  rw [LinearMap.mem_eqLocus] at h
  simpa using h

theorem rowsLift_map_eq (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hn : ∀ x ∈ U, n x = x) :
    U.map (n : S.V →ₗ[E] S.V) = U := by
  ext y
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hn x hx]
  · intro hy
    exact ⟨y, hy, hn y hy⟩

theorem rowsLift_orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  have hi' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hi
  rw [rowsLift_mem_orth, rowsLift_mem_orth]
  refine forall₂_congr fun y hy => ?_
  have h := hi' y x
  rw [hn y hy] at h
  rw [h]

theorem rowsLift_Lsub_gmap (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  ext y
  unfold Lsub Lrep
  constructor
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨ha1, haO⟩ := Submodule.mem_inf.mp ha
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp ha1
    have hlO : l ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn l).mp haO
    have hd : n l - l ∈ Xsp F := hq l hlO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨l, Submodule.mem_inf.mpr ⟨hl, hlO⟩, (n l - l) + b, (toO S (Xsp F)).add_mem hd hb, ?_⟩, hyO⟩
    show l + (n l - l + b) = n l + b
    abel
  · intro hy
    obtain ⟨hy1, hyO⟩ := Submodule.mem_inf.mp hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy1
    obtain ⟨hl, haO⟩ := Submodule.mem_inf.mp ha
    have hnO : n a ∈ orth S (Xsp F) := (rowsLift_orth_iff _ n hi hn a).mpr haO
    have hd : n a - a ∈ Xsp F := hq a haO
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_sup.mpr
      ⟨n a, Submodule.mem_inf.mpr ⟨Submodule.mem_map.mpr ⟨a, hl, rfl⟩, hnO⟩, b - (n a - a),
        (toO S (Xsp F)).sub_mem hb hd, ?_⟩, hyO⟩
    abel

theorem rowsLift_cancel (X W : Submodule E S.V) (hXW : ∀ x ∈ X, x ∈ W → x = 0)
    (A B : Submodule (𝓞 E) S.V) (h : (A ⊓ toO S W) ⊔ toO S X = (B ⊓ toO S W) ⊔ toO S X) :
    A ⊓ toO S W ≤ B ⊓ toO S W := by
  intro y hy
  have h1 : y ∈ (A ⊓ toO S W) ⊔ toO S X := Submodule.mem_sup_left hy
  rw [h] at h1
  obtain ⟨b, hb, x, hx, rfl⟩ := Submodule.mem_sup.mp h1
  have hxW : x ∈ W := by
    have h2 : b + x - b ∈ W := W.sub_mem (Submodule.mem_inf.mp hy).2 (Submodule.mem_inf.mp hb).2
    simpa using h2
  rw [hXW x hx hxW, add_zero]
  exact hb

end Generic

theorem rowsLift_X_inf_Wb (D : D7) (x : (hS D).V)
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) (hW : x ∈ Wb D) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).mp hx
  have hW' : (∑ i, c i • D.sp.hypE i) ∈ orth (hS D)
      (Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF)) := hW
  have hc : ∀ j, c j = 0 := by
    intro j
    have h1 : (hS D).hT (D.sp.hypF j) (∑ i, c i • D.sp.hypE i) = 0 :=
      (rowsLift_mem_orth.mp hW') _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
    have hs : ∀ i, (hS D).hT (D.sp.hypF j) (D.sp.hypE i) = if i = j then 1 else 0 := by
      intro i
      rw [← (hS D).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
      split_ifs <;> simp

    rw [map_sum] at h1
    simpa [hs] using h1
  simp [hc]

theorem rowsLift_fixX {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {n : (hS D).V ≃ₗ[D.host.E] (hS D).V} (hn : FixFr D (lf D F0) n) :
    (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z ∧ ∀ x ∈ F0.X, n x = x := by
  obtain ⟨-, hfr, -⟩ := hn
  have he : ∀ a, n (F0.e a) = F0.e a := by
    intro a
    have h := hfr (Fin.castSucc a)
    simpa [frame, FlagG.fvec, lf] using h
  have hz : n F0.z = F0.z := by
    have h := hfr (Fin.last _)
    simpa [frame, FlagG.fvec, lf] using h
  refine ⟨he, hz, ?_⟩
  intro x hx
  rw [FlagG.X, ← Set.image_univ] at hx
  exact rowsLift_fix_span F0.e Set.univ n he x hx

theorem rowsLift : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ → Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) → ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₂ := by
  intro D u _ hT3 _ F0 he hz Λ₁ Λ₂ h₁ h₂ hL
  have hT1 : 1 ≤ Tu D u := by omega
  have hB : IsBase D u F0 := ⟨he, hz⟩
  obtain ⟨n₁, hf₁, hs₁, hr₁⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₁ hB h₁ hT1
  obtain ⟨n₂, hf₂, hs₂, hr₂⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ₂ hB h₂ hT1
  have hfx₁ := rowsLift_fixX hf₁
  have hfx₂ := rowsLift_fixX hf₂
  have hLs : ∀ (n : (hS D).V ≃ₗ[D.host.E] (hS D).V) (Λ : LatV D), FixFr D (lf D F0) n →
      Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) (lf D F0) = Lsub Λ (lf D F0) := by
    intro n Λ hf
    have hX := (rowsLift_fixX hf).2.2
    obtain ⟨hi, -, hq⟩ := hf
    exact rowsLift_Lsub_gmap (lf D F0) Λ n hi hX hq
  have hW : ∀ Λ : LatV D, IsRowLat D F0 Λ → IsSplit D F0 Λ →
      Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X := fun Λ hr hs =>
    ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ hT1 hB hr).1 hs).2
  have heq : (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X =
      (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X :=
    (hW _ hr₁ hs₁).symm.trans
      (((hLs n₁ Λ₁ hf₁).trans (hL.trans (hLs n₂ Λ₂ hf₂).symm)).trans (hW _ hr₂ hs₂))
  have hXW : ∀ x ∈ F0.X, x ∈ Wb D → x = 0 := fun x hx hw =>
    rowsLift_X_inf_Wb D x (by rw [← he]; exact hx) hw
  have hM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D) = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D) :=
    le_antisymm (rowsLift_cancel _ _ hXW _ _ heq) (rowsLift_cancel _ _ hXW _ _ heq.symm)
  have e₁ : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₁
  have e₂ : Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ = XS D F0 ⊔ (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ ⊓ toO (hS D) (Wb D)) ⊔ YS D := hs₂
  have hMM : Formalism.HermitianLatticesTheory.gmap n₁ Λ₁ = Formalism.HermitianLatticesTheory.gmap n₂ Λ₂ := by
    rw [e₁, e₂, hM]
  have hfix : ∀ v, n₁ v = v → n₂ v = v → (n₁.trans n₂.symm) v = v := by
    intro v h1 h2
    rw [LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_eq, h2]
  obtain ⟨hi₁, -, hq₁⟩ := hf₁
  obtain ⟨hi₂, -, hq₂⟩ := hf₂
  have hmem : n₁.trans n₂.symm ∈ stabF D F0 := by
    simp only [stabF, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hi₂) hi₁
    · intro j
      exact rowsLift_map_eq (F0.Xa j) (n₁.trans n₂.symm) (fun x hx =>
        rowsLift_fix_span F0.e _ _ (fun a => hfix _ (hfx₁.1 a) (hfx₂.1 a)) x hx)
    · exact hfix _ hfx₁.2.1 hfx₂.2.1
  refine ⟨n₁.trans n₂.symm, hmem, ?_, ?_⟩
  · intro x hx
    have hy : n₁ x ∈ orth (hS D) F0.X := (rowsLift_orth_iff F0.X n₁ hi₁ hfx₁.2.2 x).mpr hx
    obtain ⟨w, hw⟩ : ∃ w, w = n₂.symm (n₁ x) := ⟨_, rfl⟩
    have hnw : n₂ w = n₁ x := by rw [hw, LinearEquiv.apply_symm_apply]
    have hwO : w ∈ orth (hS D) F0.X :=
      (rowsLift_orth_iff F0.X n₂ hi₂ hfx₂.2.2 w).mp (by rw [hnw]; exact hy)
    have h1 : n₁ x - x ∈ F0.X := hq₁ x hx
    have h2 : n₂ w - w ∈ F0.X := hq₂ w hwO
    rw [hnw] at h2
    have h3 : (n₁.trans n₂.symm) x - x = (n₁ x - x) - (n₁ x - w) := by
      rw [LinearEquiv.trans_apply, ← hw]
      abel
    rw [h3]
    exact F0.X.sub_mem h1 h2
  · have hcomp : Formalism.HermitianLatticesTheory.gmap (n₁.trans n₂.symm) Λ₁ =
        Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₁ Λ₁) := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    have hback : Formalism.HermitianLatticesTheory.gmap n₂.symm (Formalism.HermitianLatticesTheory.gmap n₂ Λ₂) = Λ₂ := by
      ext y
      simp [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    rw [hcomp, hMM, hback]

end GlobalTheory.LoopC

end
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  first | exact @GlobalTheory.St.repF_of_rational | exact GlobalTheory.St.repF_of_rational | (intros; apply GlobalTheory.St.repF_of_rational <;> assumption)
end

section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

def FlagPairStabilizer {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Subgroup (GV D) where
  carrier := H0 F F'
  one_mem' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun i => ?_, fun i => ?_⟩
    · show a (b _) = _
      rw [hb1, ha1]
    · show a (b _) = _
      rw [hb2, ha2]
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨Subgroup.inv_mem _ ha, fun i => ?_, fun i => ?_⟩
    · conv_lhs => rw [← ha1 i]
      show a.symm (a _) = _
      simp
    · conv_lhs => rw [← ha2 i]
      show a.symm (a _) = _
      simp

theorem mem_H0sub {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : GV D) : h ∈ FlagPairStabilizer F F' ↔ h ∈ H0 F F' := Iff.rfl

end GlobalTheory.Unfold
end
end
