module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle317
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle327
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle229
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle328
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_orthonormal_cuspidal_isometric_intertwiners : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  first | exact @GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame | exact GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame | (intros; apply GlobalTheory.Dec.CuspFrameOneType.cuspidal_frame <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) := by
  first | exact @GlobalTheory.CovDomGrp.isUn_iff_mem_isom | exact GlobalTheory.CovDomGrp.isUn_iff_mem_isom | (intros; apply GlobalTheory.CovDomGrp.isUn_iff_mem_isom <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 → ∃ c, γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) ↔ ∀ x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))), n x - x ∈ Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))) := by
  first | exact @GlobalTheory.CovDomGrp.orth_cond_iff_coord | exact GlobalTheory.CovDomGrp.orth_cond_iff_coord | (intros; apply GlobalTheory.CovDomGrp.orth_cond_iff_coord <;> assumption)
end

section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔ ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  first | exact @GlobalTheory.CovDomGrp.flag_iff | exact GlobalTheory.CovDomGrp.flag_iff | (intros; apply GlobalTheory.CovDomGrp.flag_iff <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.mass_bound_low_types : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  first | exact @GlobalTheory.MomProdPart.product_moment_first | exact GlobalTheory.MomProdPart.product_moment_first | (intros; apply GlobalTheory.MomProdPart.product_moment_first <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.MoveBB

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

theorem mem_span_range_comp {R W ι : Type} [Semiring R] [AddCommGroup W] [Module R W] (e : W ≃ₗ[R] W)
    (m : ι → W) (w : W) :
    e w ∈ Submodule.span R (Set.range (fun i => e (m i))) ↔ w ∈ Submodule.span R (Set.range m) := by
  have hr : Set.range (fun i => e (m i)) = (e : W →ₗ[R] W) '' Set.range m := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image]
  constructor
  · rintro ⟨y, hy, hyw⟩
    have : y = w := e.injective hyw
    exact this ▸ hy
  · intro h
    exact ⟨w, h, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem MMfam_move (H : HermSp M V) (g : V ≃ₗ[E] V) (t : Term V M r) (x : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam (move g t) x = g (H.MMfam t x) := by
  unfold HermSp.MMfam
  rcases hs : M.split with _ | s
  · rcases x with a | a <;> rfl
  · rcases x with a | a
    · rfl
    · show algebraMap F E ((s.q : F)⁻¹) • (g (t.f' a) - g (t.f a)) =
        g (algebraMap F E ((s.q : F)⁻¹) • (t.f' a - t.f a))
      rw [map_smul, map_sub]

end GlobalTheory.LocOver.MoveBB

namespace GlobalTheory.LocOver

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver.MoveBB

theorem bbne_move : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), LocNG.BBne (H := H) (move g t) ↔ LocNG.BBne (H := H) t := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r g t
  have hfam : H.MMfam (move g t) = fun x => g (H.MMfam t x) := funext (MMfam_move H g t)
  let gO : V ≃ₗ[M.L.O] V := g.restrictScalars M.L.O
  have hE : ∀ w, g w ∈ Submodule.span E (Set.range (H.MMfam (move g t))) ↔
      w ∈ Submodule.span E (Set.range (H.MMfam t)) := fun w => by
    rw [hfam]; exact mem_span_range_comp g _ w
  have hO : ∀ w, g w ∈ Submodule.span M.L.O (Set.range (H.MMfam (move g t))) ↔
      w ∈ Submodule.span M.L.O (Set.range (H.MMfam t)) := fun w => by
    rw [hfam]; exact mem_span_range_comp gO _ w
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    exact ⟨w, hw, (hE w).1 h1, fun h => h2 ((hO w).2 h)⟩
  · rintro ⟨w, hw, h1, h2⟩
    exact ⟨g w, Submodule.mem_map_of_mem hw, (hE w).2 h1, fun h => h2 ((hO w).1 h)⟩

end GlobalTheory.LocOver
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.HL.placesLat_gcoordLat_eq : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (𝓞 D.host.E) (VS D).V), GlobalTheory.LocOver.Ext p σ g → (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) g (lattice₂ D Z.M p Λ)) := by
  intro D Z T T' F0 F0' FP G c σ p g Λ hE
  unfold GlobalTheory.HL.GCoord.lat GlobalTheory.HL.Places.lat GlobalTheory.HL.WCoord.lat Formalism.MainNotions.S.LocNG.img Formalism.L2.SG.TermLoc.lattice₂
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g (baseChange₂ D p x), ⟨baseChange₂ D p x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    show (c.c p).e (g (baseChange₂ D p x)) = (placesOf Z).bc p (c.e (σ x))
    rw [hE x, c.compat p (σ x)]
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨c.e (σ x), ⟨x, hx, rfl⟩, ?_⟩
    show (placesOf Z).bc p (c.e (σ x)) = (c.c p).e (g (baseChange₂ D p x))
    rw [hE x, c.compat p (σ x)]
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.NUTransport

section Lin
variable {E V W : Type} [CommRing E] [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

abbrev As {r : ℕ} (f : Fin (r + 1) → V) (j : ℕ) : Submodule E V := Submodule.span E (f '' {i | (i : ℕ) < j})

theorem As_mono {r : ℕ} (f : Fin (r + 1) → V) {i j : ℕ} (h : i ≤ j) : (As (E := E) f i) ≤ As (E := E) f j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem As_zero {r : ℕ} (f : Fin (r + 1) → V) : (As (E := E) f 0) = ⊥ := by
  simp [As]

theorem unip_iff (e : V ≃ₗ[E] W) (g : V ≃ₗ[E] V) (A B : Submodule E V) :
    ((∀ x, ((e.symm.trans g).trans e) x ∈ A.map (e : V →ₗ[E] W) ↔ x ∈ A.map (e : V →ₗ[E] W)) ∧
      ∀ x ∈ A.map (e : V →ₗ[E] W), ((e.symm.trans g).trans e) x - x ∈ B.map (e : V →ₗ[E] W)) ↔
    ((∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B) := by
  simp only [Submodule.mem_map_equiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_sub]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => by simpa using h1 (e v), fun v hv => by simpa using h2 (e v) (by simpa using hv)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 _, fun x hx => h2 _ hx⟩

variable {r : ℕ} (g : V ≃ₗ[E] V) (f : Fin (r + 1) → V)

theorem step (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m + 1 ≤ r) : ∀ v ∈ As (E := E) f (m + 1), g v - v ∈ As (E := E) f m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < r := lt_of_lt_of_le hi hm
    have hc : i = (⟨i, hi'⟩ : Fin r).castSucc := Fin.ext rfl
    have := hN ⟨i, hi'⟩
    rw [← hc] at this
    exact As_mono f (Nat.lt_succ_iff.mp hi) this
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), add_sub_add_comm]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ a hx

theorem fwd (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m ≤ r) : ∀ v ∈ As (E := E) f m, g v ∈ As (E := E) f m := by
  intro v hv
  cases m with
  | zero => rw [As_zero] at hv ⊢; rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  | succ m =>
    have h := step g f hN m hm v hv
    have : g v = v + (g v - v) := by abel
    rw [this]; exact Submodule.add_mem _ hv (As_mono f (Nat.le_succ m) h)

theorem bwd (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a) :
    ∀ m : ℕ, m ≤ r → ∀ v ∈ As (E := E) f m, g.symm v ∈ As (E := E) f m := by
  intro m
  induction m with
  | zero => intro _ v hv; rw [As_zero] at hv ⊢; rw [Submodule.mem_bot] at hv ⊢; simp [hv]
  | succ m ih =>
    intro hm v hv
    have h := step g f hN m hm v hv
    have h2 := ih (Nat.le_of_succ_le hm) _ h
    have : g.symm v = v - g.symm (g v - v) := by simp
    rw [this]; exact Submodule.sub_mem _ hv (As_mono f (Nat.le_succ m) h2)

theorem iff_of (hN : ∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈ As (E := E) f a)
    (m : ℕ) (hm : m ≤ r) (v : V) : g v ∈ As (E := E) f m ↔ v ∈ As (E := E) f m :=
  ⟨fun h => by simpa using bwd g f hN m hm _ h, fun h => fwd g f hN m hm v h⟩

end Lin

section Loc
open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}

theorem X_eq (f : Fin (r + 1) → V) : H.X f = As (E := E) f r := by
  unfold HermSp.X As
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a.castSucc, a.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, congrArg f (Fin.ext rfl)⟩

theorem flag_eq (f : Fin (r + 1) → V) (a : Fin r) :
    Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a}) = As (E := E) f a := by
  unfold As
  congr 1
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b.castSucc, (Fin.lt_def.mp hb : (b : ℕ) < a), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < r := lt_trans hi a.isLt
    exact ⟨⟨i, hi'⟩, Fin.lt_def.mpr hi, congrArg f (Fin.ext rfl)⟩

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)

theorem spanTo_eq (f : Fin (r + 1) → V) (j : ℕ) :
    S.spanTo (fun a => c.e (f a)) j = (As (E := E) f j).map (c.e : V →ₗ[E] S.V) := by
  unfold Frames.spanTo As
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem perp_eq (A : Submodule E V) :
    perp M.L S.Hm (A.map (c.e : V →ₗ[E] S.V)) = (H.perp A).map (c.e : V →ₗ[E] S.V) := by
  have hh : ∀ x y, hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq
  ext x
  rw [Submodule.mem_map_equiv]
  show (∀ y ∈ A.map (c.e : V →ₗ[E] S.V), hf M.L S.Hm x y = 0) ↔ ∀ y ∈ A, H.h (c.e.symm x) y = 0
  constructor
  · intro hx y hy
    rw [← hh, LinearEquiv.apply_symm_apply]
    exact hx _ (Submodule.mem_map_of_mem hy)
  · intro hx y hy
    rw [Submodule.mem_map_equiv] at hy
    have := hx _ hy
    rwa [← hh, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this

end Loc

end GlobalTheory.HL.NUTransport

namespace GlobalTheory.HL.NUTransport

section Main
open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ}

theorem mem_unipOn_iff {n : ℕ} (A B : Submodule E (Fin n → E)) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B := Iff.rfl

theorem mem_hperp_iff (A : Submodule E V) (v : V) : v ∈ H.perp A ↔ ∀ x ∈ A, H.h v x = 0 := Iff.rfl

theorem mem_NU_iff_mem_Nof {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S)
    (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) :
    g ∈ NU H f ↔ (c.e.symm.trans g).trans c.e ∈ S.Nof (fun a => c.e (f a)) := by
  have hh : ∀ x y, hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq
  have hU : (c.e.symm.trans g).trans c.e ∈ isomG M.L S.Hm ↔ LocNG.IsUnitary H g := by
    show (∀ x y, hf M.L S.Hm _ _ = hf M.L S.Hm x y) ↔ ∀ x y, H.h (g x) (g y) = H.h x y
    constructor
    · intro h x y
      have := h (c.e x) (c.e y)
      simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hh] at this
      exact this
    · intro h x y
      have h1 := hh (g (c.e.symm x)) (g (c.e.symm y))
      have h2 := hh (c.e.symm x) (c.e.symm y)
      simp only [LinearEquiv.apply_symm_apply] at h2
      simp only [LinearEquiv.trans_apply]
      rw [h1, h2, h]
  have hN : ∀ n, n ∈ S.Nof (fun a => c.e (f a)) ↔ n ∈ isomG M.L S.Hm ∧
      (∀ j : Fin r, n ∈ unipOn (S.spanTo (fun a => c.e (f a)) ((j : ℕ) + 1)) (S.spanTo (fun a => c.e (f a)) j)) ∧
      n ∈ unipOn (perp M.L S.Hm (S.spanTo (fun a => c.e (f a)) r)) (S.spanTo (fun a => c.e (f a)) r) := by
    intro n
    simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, and_assoc]
  rw [hN, hU]
  simp only [spanTo_eq c f, perp_eq c, mem_unipOn_iff, unip_iff]
  show (LocNG.IsUnitary H g ∧ (∀ a : Fin r, g (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
      ∀ v ∈ H.perp (H.X f), g v - v ∈ H.X f) ↔ _
  simp only [flag_eq, X_eq]
  constructor
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨hu, fun j => ⟨iff_of g f hfl _ j.isLt, step g f hfl j j.isLt⟩, ⟨fun v => ?_, hp⟩⟩
    rw [mem_hperp_iff, mem_hperp_iff]
    constructor
    · intro h x hx
      have := h (g x) ((iff_of g f hfl r le_rfl x).2 hx)
      rwa [hu] at this
    · intro h x hx
      have h1 := h (g.symm x) (bwd g f hfl r le_rfl x hx)
      rw [← hu v (g.symm x), LinearEquiv.apply_symm_apply] at h1
      exact h1
  · rintro ⟨hu, hj, -, hp⟩
    refine ⟨hu, fun a => (hj a).2 _ (Submodule.subset_span ⟨a.castSucc, ?_, rfl⟩), hp⟩
    show (a : ℕ) < (a : ℕ) + 1
    omega

end Main

end GlobalTheory.HL.NUTransport
end
end

section

noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrCoord

theorem frFac_mul_c {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (b : Fin (D.R.rS + 1)) :
    (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) * algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) = 1 := by
  have hu : IsUnit (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) :=
    ((G.c p).isUnit.pow _).map _
  have he : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) =
      Ring.inverse (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ)))) := by
    rw [map_pow]
    exact congrArg (fun x => Ring.inverse (x ^ (D.R.rS - (b : ℕ)))) (c.c_eq p).symm
  rw [he]
  exact Ring.inverse_mul_cancel _ hu

theorem step {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T}
    {F0' : LFlag (D.sp.Y 0) D.R.rS T'} {FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS}
    {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV)
    (hm : (placesOf Z).Ext p N m) (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (v : Fin (D.R.rS + 1) → (VS D).V) (g : Fin (D.R.rS + 1) → G.V) (gl : Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ a, g a = c.e (v a))
    (hgl : ∀ a : Fin (D.R.rS + 1), algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (a : ℕ))) • gl a =
      (placesOf Z).bc p (g a))
    (hN : ∀ b, N (g b) = ∑ a, B a b • g a) (b : Fin (D.R.rS + 1)) :
    (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) = m (gl b) := by
  have h1 : c.e (∑ a, B a b • v a) = N (g b) := by

    rw [hN b, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hg a]
  have h2 : (c.c p).e (scaled Z p (fun b => ∑ a, B a b • v a) b) =
      frFac Z.δ p b • (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) := (c.c p).e.map_smul _ _
  have h3 : m ((placesOf Z).bc p (g b)) = (placesOf Z).bc p (N (g b)) := hm (g b)
  have h4 : m (algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • gl b) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) := m.map_smul _ _
  have h5 : (c.c p).e (baseChange₂ D p (∑ a, B a b • v a)) =
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) :=
    (c.compat p _).trans ((congrArg ((placesOf Z).bc p) h1).trans
      (h3.symm.trans ((congrArg m (hgl b).symm).trans h4)))
  have h6 : (show ((placesOf Z).loc p).Ep from frFac Z.δ p b) •
      algebraMap ((placesOf Z).loc p).Fp ((placesOf Z).loc p).Ep ((G.c p).val ^ (D.R.rS - (b : ℕ))) • m (gl b) =
      m (gl b) := by
    rw [smul_smul, frFac_mul_c c p b, one_smul]
  rw [h2, h5]
  exact h6

theorem scaled_coord : ∀ (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G) (p : PlF D) (N : G.GLV) (m : (G.S p).GLV), (placesOf Z).Ext p N m → ∀ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0 a) b) = m ((G.S p).f b)) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → ∀ b, (c.c p).e (scaled Z p (fun b => ∑ a, B a b • frame F0' a) b) = m ((G.S p).f' b)) := by
  intro D Z T T' F0 F0' FP G c p N m hm B
  exact ⟨fun hN b => step c p N m hm B (frame F0) G.f (G.S p).f c.f_eq (G.f_eq p) hN b,
    fun hN b => step c p N m hm B (frame F0') G.f' (G.S p).f' c.f'_eq (G.f'_eq p) hN b⟩

end GlobalTheory.FrCoord
end
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LocOver.isTerm_move_unitary : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (t : Formalism.MainNotions.S.Loc.Term V M r), H.IsTerm t → H.IsTerm (move g t) :=
  fun H _ g hg t ht => GlobalTheory.LocOver.isTerm_move_of_unitary H g t hg ht
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isTerm_unitary_move_localTerm : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) (r : ℕ) (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), Formalism.MainNotions.S.LocNG.IsUnitary H g → H.IsTerm t → H.IsTerm (GlobalTheory.LocOver.move g t) := by
  first | exact @GlobalTheory.LocOver.isTerm_unitary_move | exact GlobalTheory.LocOver.isTerm_unitary_move | (intros; apply GlobalTheory.LocOver.isTerm_unitary_move <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.localised_base_frames_leading_minor_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS),
    AtBase Z p F F' Tn T'n P → ∀ l : ℕ, P.Dm l =
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  first | exact @GlobalTheory.LocMinor.leadMinor_atBase | exact GlobalTheory.LocMinor.leadMinor_atBase | (intros; apply GlobalTheory.LocMinor.leadMinor_atBase <;> assumption)
end
