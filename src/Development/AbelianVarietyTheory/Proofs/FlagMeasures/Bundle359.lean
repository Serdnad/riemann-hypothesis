module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsEqOfStabilizerConjugateLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeUnimodularAndPrimitive
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle140
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle160
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle343
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
public import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle346
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

@[expose] public section

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.Parts
open GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

theorem lsS_le {r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (v : Fin r → (VS D).V) {y : (VS D).V} (hy : y ∈ latSpanS aa v) :
    y ∈ Submodule.span D.host.E (Set.range v) := by
  have hle : latSpanS aa v ≤ (Submodule.span D.host.E (Set.range v)).restrictScalars (𝓞 D.host.E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)
  exact hle hy

theorem Xsp_eq (u : D.what₂.Word) : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem XS_eq (u : D.what₂.Word) : XS D (X.Fu u) = latSpanS (fun a => aaD D a) X.eX := by
  simp only [XS, latSpanS, aaD, X.Fu_e]

theorem xlam_split (u : D.what₂.Word) (M : Submodule (𝓞 D.host.E) (VS D).V)
    (hM : ∀ x ∈ M, ∀ a, (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0) :
    XLam (latSpanS (fun a => aaD D a) X.eX ⊔ M ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) =
      XS D (X.Fu u) := by
  rw [XS_eq]
  show _ ⊓ toO (VS D) (Xsp (lf D (X.Fu u))) = _
  rw [Xsp_eq]
  refine le_antisymm ?_ (le_inf (le_sup_left.trans le_sup_left) fun y hy => lsS_le _ _ hy)
  rintro y ⟨hyΛ, hyX⟩
  have hyX' : y ∈ Submodule.span D.host.E (Set.range X.eX) := hyX
  obtain ⟨y1, hy1, b, hb, rfl⟩ := Submodule.mem_sup.mp hyΛ
  obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hy1
  have haX := lsS_le _ _ ha
  have hbY := lsS_le _ _ hb

  have hb0 : b = 0 := by
    have hpair : ∀ c, (VS D).hT (X.eX c) b = 0 := by
      intro c
      have h1 := orth_span (fun d => X.ee c d) hyX'
      have h2 := orth_span (fun d => X.ee c d) haX
      rw [map_add (f := _), map_add (f := _), h2, (hM m hm c).1, zero_add, zero_add] at h1
      exact h1
    rw [coord X.ef hbY]
    simp [hpair]
  subst hb0
  rw [add_zero] at hyX' ⊢

  have hmX : m ∈ Submodule.span D.host.E (Set.range X.eX) := by
    have := Submodule.sub_mem _ hyX' haX
    rwa [add_sub_cancel_left] at this
  have hm0 : m = 0 := by
    rw [coord (dual_symm GlobalTheory.RowsOrb.Uniq.hh X.ef) hmX]
    simp [(hM m hm _).2]
  rw [hm0, add_zero]
  exact ha

theorem map_perp (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    ∀ x ∈ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)), ∀ a,
      (VS D).hT (X.eX a) x = 0 ∧ (VS D).hT (X.fY a) x = 0 := by
  intro x hx a
  obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hx
  exact (GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 a

theorem lmap_eq (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)) :
    GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L := by
  ext w
  rw [lmap_char X u (latSpanS (fun a => aaD D a) X.eX ⊔
      L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
      latSpanS (fun a => (aaD D a)⁻¹) X.fY) (fun a => aaD D a) (fun a => (aaD D a)⁻¹) X.ef (map_perp X L)
      rfl w]
  constructor
  · rintro ⟨l, hl, hP⟩
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.mp hl
    have hfix : P (VS D).hT X.eX X.fY (w' : (VS D).V) = w' := by
      rw [P_apply]
      simp [((GlobalTheory.RowsOrb.mem_Wb X (w' : (VS D).V)).mp w'.2 _).2]
    have : w' = w := Subtype.ext (hfix.symm.trans hP)
    exact this ▸ hw'
  · intro hw
    refine ⟨(w : (VS D).V), Submodule.mem_map_of_mem hw, ?_⟩
    rw [P_apply]
    simp [((GlobalTheory.RowsOrb.mem_Wb X (w : (VS D).V)).mp w.2 _).2]

end GlobalTheory.RowsOrb.Parts


open GlobalTheory.RowsOrb.Parts in
theorem GlobalTheory.RowsOrb.parts_of_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), XLam (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) = XS D (X.Fu u) ∧ XLam (VS D).L0 (lf D (X.Fu u)) = XS D (X.Fu u) ∧ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) = L ∧ ∀ w : GlobalTheory.RowsOrb.Wb X, (w : (VS D).V) ∈ Lsub (latSpanS (fun a => aaD D a) X.eX ⊔ L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔ latSpanS (fun a => (aaD D a)⁻¹) X.fY) (lf D (X.Fu u)) → w ∈ L := by
  intro D X u L
  refine ⟨xlam_split X u _ (map_perp X L), ?_, lmap_eq X u L, ?_⟩
  · rw [X.Lam_split]
    exact xlam_split X u X.Lb X.Lb_perp
  · intro w hw
    rw [Lsub, Submodule.mem_inf] at hw
    have hX : toO (VS D) (Xsp (lf D (X.Fu u))) =
        GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
      rw [GlobalTheory.RowsOrb.Uniq.fixedFrameOfWord_isotropicSpan_eq, Xsp_eq]
    have hmem : w ∈ GlobalTheory.RowsOrb.Lmap X u (latSpanS (fun a => aaD D a) X.eX ⊔
        L.map ((GlobalTheory.RowsOrb.Wb X).subtype.restrictScalars (𝓞 D.host.E)) ⊔
        latSpanS (fun a => (aaD D a)⁻¹) X.fY) :=
      (GlobalTheory.RowsOrb.mem_Lmap X u _ w).mpr ((sup_le_sup inf_le_left hX.le) hw.1)
    rwa [lmap_eq X u L] at hmem
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.StabAct

open GlobalTheory.RowsOrb GlobalTheory.RowsOrb.Uniq

variable {D : D7} (X : HidaSetting D)

abbrev Xs : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX)

theorem P_X {x : (VS D).V} (hx : x ∈ Xs X) : P (VS D).hT X.eX X.fY x = 0 := by
  have hdY := dual_symm hh X.ef
  rw [P_apply, ← coord hdY hx, sub_self]

theorem P_Wb {w : (VS D).V} (hw : w ∈ Wb X) : P (VS D).hT X.eX X.fY w = w := by
  rw [P_apply]; simp [((mem_Wb X w).1 hw _).2]

theorem sub_proj_mem₂ (v : (VS D).V) : v - P (VS D).hT X.eX X.fY v ∈ Xs X := by
  rw [P_apply, sub_sub_cancel]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem orth_e (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hδ : ∀ x y, (VS D).hT (δ x) (δ y) = (VS D).hT x y)
    (hX : ∀ x ∈ Xs X, δ.symm x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) (a : Fin D.R.rS) :
    (VS D).hT (X.eX a) (δ w) = 0 := by
  rw [← δ.apply_symm_apply (X.eX a), hδ]
  exact GlobalTheory.RowsOrb.Basic.hT_span_left X.eX w (fun b => ((mem_Wb X w).1 hw b).1)
    (hX _ (Submodule.subset_span ⟨a, rfl⟩))

variable (X)

def gl (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hS : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (δ w) = 0) :
    Wb X →ₗ[D.host.E] Wb X :=
  LinearMap.codRestrict (Wb X) (P (VS D).hT X.eX X.fY ∘ₗ δ ∘ₗ (Wb X).subtype)
    (fun w a => P_mem X.ee (dual_symm hh X.ef) (hS _ w.2) a)

theorem gl_inv (δ ε : (VS D).V →ₗ[D.host.E] (VS D).V) (hεδ : ∀ v, ε (δ v) = v)
    (hε : ∀ x ∈ Xs X, ε x ∈ Xs X) {w : (VS D).V} (hw : w ∈ Wb X) :
    P (VS D).hT X.eX X.fY (ε (P (VS D).hT X.eX X.fY (δ w))) = w := by
  have e : P (VS D).hT X.eX X.fY (δ w) = δ w - (δ w - P (VS D).hT X.eX X.fY (δ w)) := by abel
  rw [e, map_sub, hεδ, map_sub, P_X X (hε _ (sub_proj_mem₂ X _)), sub_zero, P_Wb X hw]

def ge (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (h1 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ w) = 0)
    (h2 : ∀ w ∈ Wb X, ∀ a, (VS D).hT (X.eX a) (γ.symm w) = 0)
    (hX : ∀ x ∈ Xs X, γ x ∈ Xs X) (hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X) : Wb X ≃ₗ[D.host.E] Wb X :=
  LinearEquiv.ofLinear (gl X (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1)
    (gl X ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) h2)
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.apply_symm_apply v) hX w.2))
    (LinearMap.ext fun w => Subtype.ext (gl_inv X _ _ (fun v => γ.symm_apply_apply v) hX' w.2))

theorem transport (u : D.what₂.Word) (δ : (VS D).V →ₗ[D.host.E] (VS D).V) (hX : ∀ x ∈ Xs X, δ x ∈ Xs X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {v : (VS D).V}
    (hv : v ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X) :
    P (VS D).hT X.eX X.fY (δ v) ∈
      Λ.map (δ.restrictScalars (𝓞 D.host.E)) ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := by
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv
  rw [GlobalTheory.RowsOrb.Basic.mem_XO] at hx
  refine Submodule.mem_sup.2 ⟨δ l, Submodule.mem_map_of_mem hl,
    δ x - (δ (l + x) - P (VS D).hT X.eX X.fY (δ (l + x))), ?_, ?_⟩
  · rw [GlobalTheory.RowsOrb.Basic.mem_XO]
    exact Submodule.sub_mem _ (hX x hx) (sub_proj_mem₂ X _)
  · rw [map_add (f := _)]; abel

end GlobalTheory.RowsOrb.StabAct


open GlobalTheory.RowsOrb.StabAct GlobalTheory.RowsOrb.Uniq in
theorem GlobalTheory.RowsOrb.exists_gz_lmap : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∀ γ ∈ stabF D (X.Fu u),
    ∃ g : GlobalTheory.RowsOrb.Gz X u, ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V,
      g • GlobalTheory.RowsOrb.Lmap X u Λ = GlobalTheory.RowsOrb.Lmap X u (Formalism.HermitianLatticesTheory.gmap γ Λ) := by
  intro D X u γ hγ
  obtain ⟨hiso, hXa, hz⟩ := hγ
  have hδ : ∀ x y, (VS D).hT (γ x) (γ y) = (VS D).hT x y := hiso
  have hδ' : ∀ x y, (VS D).hT (γ.symm x) (γ.symm y) = (VS D).hT x y := fun x y => by
    rw [← hδ, γ.apply_symm_apply, γ.apply_symm_apply]
  have hXr : (X.Fu u).Xa D.R.rS = Xs X := by
    simp only [FlagG.Xa, HidaSetting.Fu_e]
    congr 1
    ext v
    simp
  have hmap := hXa D.R.rS
  rw [hXr] at hmap
  have hX : ∀ x ∈ Xs X, γ x ∈ Xs X := fun x hx => by
    rw [← hmap]; exact Submodule.mem_map_of_mem hx
  have hX' : ∀ x ∈ Xs X, γ.symm x ∈ Xs X := fun x hx => by
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have h1 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ hδ hX' hw a
  have h2 := fun w (hw : w ∈ GlobalTheory.RowsOrb.Wb X) a => orth_e γ.symm hδ' (fun x hx => by simpa using hX x hx) hw a
  have hz' : γ (X.zu u) = X.zu u := by rw [← HidaSetting.flagZVector]; exact hz
  let e := ge X γ h1 h2 hX hX'
  have he : ∀ w, ((e w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ w) := fun w => rfl
  have he' : ∀ w, ((e.symm w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = P (VS D).hT X.eX X.fY (γ.symm w) := fun w => rfl
  have hi : e ∈ Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X) := by
    intro x y
    rw [GlobalTheory.RowsOrb.hb_apply, GlobalTheory.RowsOrb.hb_apply, he, he, P_apply, P_apply,
      P_iso hh X.ee (orth_e γ hδ hX' x.2) (orth_e γ hδ hX' y.2), hδ]
  have hs : (⟨e, hi⟩ : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hb X)) ∈ GlobalTheory.RowsOrb.Gz X u := by
    rw [MulAction.mem_stabilizer_iff]
    show e (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u
    apply Subtype.ext
    rw [he, GlobalTheory.RowsOrb.zb_coe, hz']
    exact P_Wb X (GlobalTheory.RowsOrb.zb X u).2
  refine ⟨⟨⟨e, hi⟩, hs⟩, fun Λ => ?_⟩
  have hback : (Formalism.HermitianLatticesTheory.gmap γ Λ).map
      (((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars
        (𝓞 D.host.E)) = Λ := by
    ext v
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hv
      exact ⟨γ v, ⟨v, hv, rfl⟩, by simp⟩
  show Formalism.HermitianLatticesTheory.gmap e (GlobalTheory.RowsOrb.Lmap X u Λ) = _
  ext w'
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := transport X u (γ : (VS D).V →ₗ[D.host.E] (VS D).V) hX Λ ((GlobalTheory.RowsOrb.mem_Lmap X u Λ w).1 hw)
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
  · intro hw'
    refine ⟨e.symm w', ?_, e.apply_symm_apply w'⟩
    have h := transport X u ((γ.symm : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) hX'
      (Formalism.HermitianLatticesTheory.gmap γ Λ) ((GlobalTheory.RowsOrb.mem_Lmap X u _ w').1 hw')
    rw [hback] at h
    exact (GlobalTheory.RowsOrb.mem_Lmap X u _ _).2 h
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.AbsVol

theorem fDeg_congr {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) :
    Formalism.HermitianLatticesTheory.fDeg K = Formalism.HermitianLatticesTheory.fDeg L := by
  unfold Formalism.HermitianLatticesTheory.fDeg
  refine Fintype.card_congr
    { toFun := fun w => w.comap (e.symm : L →+* K)
      invFun := fun w => w.comap (e : K →+* L)
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · ext x
    simp
  · ext x
    simp

theorem vInv_congr {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) :
    Formalism.HermitianLatticesTheory.vInv K = Formalism.HermitianLatticesTheory.vInv L := by
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [fDeg_congr e, NumberField.discr_eq_discr_of_ringEquiv K e]

theorem volU_nonneg (i : ℕ) : 0 ≤ volU i := by
  unfold volU sphV
  positivity

theorem absoluteVolume_of_volumeStep : VolumeStep → AbsoluteVolume := by
  intro hstep I p q hsig hq hn X hX hrd hfrd c μf _ _ hc
  obtain ⟨hf, hv, -, -, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq' := hpq p q hsig
  have hp : 2 ≤ p := by
    by_contra h
    have h1 : 7 ≤ q := by omega
    have h2 : 7 * q ≤ q ^ 2 := by nlinarith
    omega
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hrat⟩ :=
    GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q 2 0 hsig hp (Nat.zero_le _) le_rfl
  obtain ⟨μ₀, hH, hS⟩ := GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary I₀
  choose c₀ _ hc₀ _ using fun v : InfinitePlace I₀.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  have hg₀ : IsGaugeAll I₀ c₀ := hc₀
  have hE := hrat I₀ hsame hsig₀ c μf c₀ μ₀ hc hg₀
  have hD := GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite I₀ 2 hsig₀ c₀ μ₀ hg₀
  have hV := GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound I₀.E I₀.cm.cmUnram
  obtain ⟨e, -⟩ := hsame
  obtain ⟨hf₀, -, -, -, -, -⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I₀
  rw [← hf₀, fDeg_congr e] at hD
  rw [fDeg_congr e, vInv_congr e] at hV
  have hA := GlobalTheory.T.absolute_hermitian_volume_bound_arith I.E I.cm.cmUnram I.n X hn hX (hv ▸ hrd) (by rw [hf, hv]; exact hfrd)
  have hv0 : 0 ≤ 2 * Formalism.HermitianLatticesTheory.vInv I.E := by
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  have hv1 : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv I.E := hv ▸ (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).2.2.1
  have hlog : 0 ≤ Real.log (2 * Formalism.HermitianLatticesTheory.vInv I.E) := Real.log_nonneg hv1
  have hU : 0 ≤ volU 2 ^ Formalism.HermitianLatticesTheory.fDeg I.E := pow_nonneg (volU_nonneg 2) _
  rw [hE, hpq', ← hf]
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal hA)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hU]
  gcongr
  exact hD.trans (by gcongr)

end GlobalTheory.FlagMeas.AbsVol
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem fundDom_volume_pos_lt_top : VolumeStep → ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf]
    [μf.IsHaarMeasure] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ p q : ℕ, HasSig I p q → 2 ≤ p →
    0 < I.muA μf fund ∧ I.muA μf fund < ⊤ := by
  intro hstep I μf _ _ fund hfund p q hsig hp
  obtain ⟨hcov, hpos⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)
  rw [Set.univ_inter] at hcov
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hratio⟩ := GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q 2 0 hsig hp (Nat.zero_le _) le_rfl
  choose c hc using fun v : InfinitePlace I.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I.n (I.ε v)
  choose c₀ hc₀ using fun v : InfinitePlace I₀.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  obtain ⟨-, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I₀
  obtain ⟨-, -, -, hK, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hg : IsGaugeAll I c := fun v => (hc v).2.1
  have hg₀ : IsGaugeAll I₀ c₀ := fun v => (hc₀ v).2.1
  let μ₀ : Measure I₀.Gf := Measure.haar
  have heq := hratio I₀ hsame hsig₀ c μf c₀ μ₀ hg hg₀
  have hdef := GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite I₀ 2 hsig₀ c₀ μ₀ hg₀
  have hcl := GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound I₀.E I₀.cm.cmUnram
  have h₀ : gaugeVol I₀ c₀ μ₀ < ⊤ :=
    hdef.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hcl.trans_lt ENNReal.ofReal_lt_top))
  have hfin : gaugeVol I c μf < ⊤ := by
    rw [heq]
    exact ENNReal.mul_lt_top h₀ ENNReal.ofReal_lt_top
  rw [gaugeVol, hcov] at hfin
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hcpos : ENNReal.ofReal (∏ v, c v) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Finset.prod_pos fun v _ => (hc v).1)).ne'
  rw [htop, ENNReal.mul_top hcpos, ENNReal.top_div_of_ne_top hK.measure_lt_top.ne] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.FlagMeas
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm : ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin (D.R.N 0)) D.host.E), g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ↔ (((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm).map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm := by
  first | exact @GlobalTheory.St.mem_UJ_gramN_iff_map_symm | exact GlobalTheory.St.mem_UJ_gramN_iff_map_symm | (intros; apply GlobalTheory.St.mem_UJ_gramN_iff_map_symm <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_scale_normalised_localReading : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), ∃ s : X.B.I.Ginf → NNReal, (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧ (∀ γ, s γ ≤ 1) ∧ ∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) := by
  first | exact @GlobalTheory.PinScale.scale_pin | exact GlobalTheory.PinScale.scale_pin | (intros; apply GlobalTheory.PinScale.scale_pin <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integralRowFrame_map_isometry : ∀ (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ → ∀ (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T), FrameOK D Λ₁ F → FrameOK D Λ₂ (mapLF γ F) := by
  first | exact @GlobalTheory.FrameIsom.frameOK_mapLF | exact GlobalTheory.FrameIsom.frameOK_mapLF | (intros; apply GlobalTheory.FrameIsom.frameOK_mapLF <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem rowDict_goodOp_nonempty :
    ∀ (D : D7) (X : HidaSetting D), Nonempty (Formalism.L2.SG.RowDict.GoodOp X) :=
  fun _ X => Formalism.L2.SG.Pf.rowDictGoodOp_exists X

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem local_nongeneric_bound_record_family :
    ∀ (C : ℝ), 39 ≤ C → (∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C) ∧
      (∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C ∧ Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBoundOfLargeRank D C ∧ Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C) ∧
      ∀ {eps : ℝ} (Fm : FamP eps), Formalism.MainNotions.NonGenericAndKTwoTheorems.FamilyNonGenericLocalBound Fm C ∧ Formalism.MainNotions.UniformConstantsAndStatements.admF5 Fm C := by
  intro C hC
  have h1 : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C := by
    intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP
    exact GlobalTheory.T.hermitianDoubleCoset_amplitude_bound_local C hC M hM H r k P hk hV hP
  have h2 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D C := fun D hk => h1 _ _ hk
  have h3 : ∀ D : D7, Formalism.MainNotions.UniformConstantsAndStatements.adm5 D C := fun D => h2 D
  exact ⟨h1, fun D => ⟨h2 D, h2 D, h3 D⟩, fun Fm => ⟨fun x i => h2 _, fun x i => h3 _⟩⟩

end GlobalTheory
end
