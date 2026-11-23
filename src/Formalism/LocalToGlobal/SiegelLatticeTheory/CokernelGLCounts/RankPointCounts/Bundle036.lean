module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle034
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LinearAdelicActionFixedIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

@[expose] public section

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev FI : Type := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

def qq : Ideal (𝓞 D.host.E) := Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}

def ddPow (k : ℕ) : FI D := ddS D ^ (-(k : ℤ))

def qdPow (k : ℕ) : FI D := (qq D : FI D) * ddPow D k

def bt (b : MatR D) (i j : Fin (D.R.rS + 1)) : D.host.E :=
  (-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val)

def EntryShape (a b : MatR D) : Prop :=
  ∀ i j : Fin (D.R.rS + 1), j < i →
    a i j ∈ ddPow D (i.val - j.val) ∧ bt D b j i ∈ ddPow D (i.val - j.val) ∧
      a i j - D.conjF (bt D b j i) ∈ qdPow D (i.val - j.val)

def LocMem (p : PlF D) (I : FI D) (x : D.host.E) : Prop :=
  (D.s.atP p).ιE x ∈ Submodule.span (D.s.atP p).O ((D.s.atP p).ιE '' (I : Set D.host.E))

def LocEntryShape (p : PlF D) (a b : MatR D) : Prop :=
  ∀ i j : Fin (D.R.rS + 1), j < i →
    LocMem D p (ddPow D (i.val - j.val)) (a i j) ∧ LocMem D p (ddPow D (i.val - j.val)) (bt D b j i) ∧
      LocMem D p (qdPow D (i.val - j.val)) (a i j - D.conjF (bt D b j i))

def LocShapeL : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D),
    (∀ q, Agree δ M q) → (M p).split = none → ∀ a b : MatR D, IsLoUni a → IsUpUni b →
      (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
        LocEntryShape D p a b)

def LocShapeG : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D),
    (∀ q, Agree δ M q) → (M p).split.isSome → ∀ a b : MatR D, IsLoUni a → IsUpUni b →
      (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
        LocEntryShape D p a b)

def LocGlob : Prop :=
  ∀ I : FI D, I ≠ 0 → ∀ x : D.host.E, (∀ p, LocMem D p I x) ↔ x ∈ I

def ShapeNZ : Prop := (∀ k, ddPow D k ≠ 0) ∧ ∀ k, qdPow D k ≠ 0

def StabIntShapeC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (a : GLR D),
      a ∈ stabInt D u u' δ M w ↔ IsLoUni (a : MatR D) ∧ ∃ b : MatR D, IsUpUni b ∧
        (a : MatR D) * ptMat w * b = ptMat w ∧ EntryShape D a (b)

variable {D}

theorem loc_iff (hL : LocShapeL D) (hG : LocShapeG D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D} (hA : ∀ q, Agree δ M q) {a b : MatR D}
    (ha : IsLoUni a) (hb : IsUpUni b) :
    (Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      LocEntryShape D p a b) := by
  cases h : (M p).split with
  | none => exact hL δ M p hA h a b ha hb
  | some g => exact hG δ M p hA (by simp [h]) a b ha hb

theorem glob_iff (hLG : LocGlob D) (hNZ : ShapeNZ D) (a b : MatR D) :
    (∀ p, LocEntryShape D p a b) ↔ EntryShape D a b := by
  constructor
  · intro h i j hij
    exact ⟨(hLG _ (hNZ.1 _) _).1 fun p => (h p i j hij).1, (hLG _ (hNZ.1 _) _).1 fun p => (h p i j hij).2.1,
      (hLG _ (hNZ.2 _) _).1 fun p => (h p i j hij).2.2⟩
  · intro h p i j hij
    exact ⟨(hLG _ (hNZ.1 _) _).2 (h i j hij).1 p, (hLG _ (hNZ.1 _) _).2 (h i j hij).2.1 p,
      (hLG _ (hNZ.2 _) _).2 (h i j hij).2.2 p⟩

theorem stabIntShape_of (hL : LocShapeL D) (hG : LocShapeG D) (hLG : LocGlob D) (hNZ : ShapeNZ D) :
    StabIntShapeC D := by
  intro δ M hA u u' w a
  rw [StabIntGrp.mem_stabInt_iff, StabShape.mem_stabIntSet_iff δ M u u' hA w a]
  constructor
  · rintro ⟨ha, b, hb, hW, hp⟩
    exact ⟨ha, b, hb, hW, (glob_iff hLG hNZ a b).1 fun p => (loc_iff hL hG (p := p) hA ha hb).1 (hp p)⟩
  · rintro ⟨ha, b, hb, hW, he⟩
    exact ⟨ha, b, hb, hW, fun p => (loc_iff hL hG (p := p) hA ha hb).2 ((glob_iff hLG hNZ a b).2 he p)⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Kset

variable (I : Formalism.MainNotions.S.AutInst)

theorem kset_inv' {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset :=
  (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem kset_mul' {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset :=
  (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem kset_act {k : I.Gf} (hk : k ∈ I.Kset) (w : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    I.fmat k *ᵥ w ∈ I.Lf ↔ w ∈ I.Lf := (hk w).symm

theorem fmat_mul' (x y : I.Gf) : I.fmat (x * y) = I.fmat x * I.fmat y := rfl

theorem fmat_inv_mul' (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [Formalism.MainNotions.S.AutInst.fmat]

end Kset

section Lat

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def lat (h : Hfin X u) : Submodule (𝓞 D.host.E) (VS D).V := Classical.choose (latSub X u h)

theorem lat_coe (h : Hfin X u) : (lat X u h : Set (VS D).V) = latOf X u h :=
  Classical.choose_spec (latSub X u h)

theorem mem_lat (h : Hfin X u) (y : (VS D).V) :
    y ∈ lat X u h ↔ X.B.I.fmat ((h : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  rw [← SetLike.mem_coe, lat_coe]
  show X.B.I.fmat (((h : X.B.I.Gf)) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
  rw [_root_.mul_inv_rev, fmat_mul', ← Matrix.mulVec_mulVec, kset_act X.B.I (kset_inv' X.B.I (X.xu_K u))]

theorem matE_fix (M : GL (Fin X.B.I.n) X.B.I.E)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ
      incl X.B.I y = incl X.B.I y) (y : (VS D).V) (hy : X.crd y ∈ fixSet X u) : matE X M y = y := by
  have h1 : incl X.B.I (X.crd (matE X M y)) = incl X.B.I (X.crd y) := by
    rw [matE_incl]
    exact hfix _ hy
  apply X.bas.equivFun.injective
  funext i
  exact X.ιE.symm.injective (inclInj_holds X (congrFun h1 i))

theorem matE_stab (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J)
    (hfix : ∀ y ∈ fixSet X u, (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) *ᵥ
      incl X.B.I y = incl X.B.I y) : matE X M ∈ stabF D (X.Fu u) := by
  refine ⟨matE_isom X M hM, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact matE_fix X u M hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · show matE X M (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact matE_fix X u M hfix _ (Or.inr rfl)

theorem hfin_fix (g : Hfin X u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    X.B.I.fmat (g : X.B.I.Gf) *ᵥ incl X.B.I y = incl X.B.I y := g.2 y hy

theorem mem_gmap (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (y : (VS D).V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap γ Λ ↔ γ.symm y ∈ Λ := by
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨γ.symm y, hy, by simp⟩

theorem lat_act (g h k : Hfin X u) (M : GL (Fin X.B.I.n) X.B.I.E)
    (hM : X.B.I.fmat (g : X.B.I.Gf) = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)))
    (hk : (k : X.B.I.Gf) ∈ X.B.I.Kset) :
    lat X u (g * h * k) = Formalism.HermitianLatticesTheory.gmap (matE X M) (lat X u h) := by
  ext y
  rw [mem_gmap, mem_lat, mem_lat]
  have hinc : incl X.B.I (X.crd ((matE X M).symm y)) = X.B.I.fmat ((g : X.B.I.Gf))⁻¹ *ᵥ incl X.B.I (X.crd y) := by
    have h1 := matE_incl X M ((matE X M).symm y)
    rw [LinearEquiv.apply_symm_apply, ← hM] at h1
    rw [h1, Matrix.mulVec_mulVec, fmat_inv_mul', Matrix.one_mulVec]
  rw [hinc, Matrix.mulVec_mulVec]
  show X.B.I.fmat (((g : X.B.I.Gf) * (h : X.B.I.Gf) * (k : X.B.I.Gf)))⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf ↔ _
  rw [_root_.mul_inv_rev, fmat_mul', ← Matrix.mulVec_mulVec, kset_act X.B.I (kset_inv' X.B.I hk), _root_.mul_inv_rev, fmat_mul']

end Lat

section Cls

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def cls (h : Hfin X u) : Submodule (𝓞 D.host.E) (VS D).V :=
  if hh : ∃ Λ', Λ' ∈ what₂ ∧ Eqv X u Λ' (lat X u h) then Classical.choose hh else ⊥

variable {X u what₂}

theorem cls_spec (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (h : Hfin X u) :
    cls X u what₂ h ∈ what₂ ∧ Eqv X u (cls X u what₂ h) (lat X u h) := by
  have hex : ∃ Λ', Λ' ∈ what₂ ∧ Eqv X u Λ' (lat X u h) :=
    (hR.2 (lat X u h) (hL h (lat X u h) (lat_coe X u h))).exists
  unfold cls
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

theorem cls_eq (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) {h : Hfin X u}
    {Λ' : Submodule (𝓞 D.host.E) (VS D).V} (h1 : Λ' ∈ what₂) (h2 : Eqv X u Λ' (lat X u h)) :
    cls X u what₂ h = Λ' :=
  (hR.2 (lat X u h) (hL h (lat X u h) (lat_coe X u h))).unique (cls_spec hR hL h) ⟨h1, h2⟩

theorem gamR_mat {g : Hfin X u} (hg : g ∈ gamR X u) :
    ∃ M : GL (Fin X.B.I.n) X.B.I.E, M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧
      X.B.I.fmat (g : X.B.I.Gf) = (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) :=
  (mem_gamR_iff X u g).1 hg

theorem cls_rel (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hI : LatInj X u) (h h' : Hfin X u) :
    cls X u what₂ h = cls X u what₂ h' ↔ ∃ g ∈ gamR X u, ∃ k ∈ kR X u, h' = g * h * k := by
  constructor
  · intro hc
    have e1 := (cls_spec hR hL h).2
    have e2 := (cls_spec hR hL h').2
    rw [hc] at e1
    have e3 : Eqv X u (lat X u h) (lat X u h') := (eqvEquiv X u).trans ((eqvEquiv X u).symm e1) e2
    obtain ⟨g, k, hh', hkl⟩ := hI h h' (lat X u h) (lat X u h') (lat_coe X u h) (lat_coe X u h') e3
    refine ⟨iotaF X u g, ?_, k, ?_, hh'⟩
    · rw [mem_gamR_iff]
      obtain ⟨hGF, -⟩ := Subgroup.mem_inf.1 g.2
      have hGF' : (g : X.B.I.GA) ∈ X.B.I.GFset := hGF
      obtain ⟨M, hM, -, hf⟩ := hGF'
      exact ⟨M, hM, hf⟩
    · rw [mem_kR_iff]
      have hK := Formalism.L2.SG.Pf.LatDictK.dict_K X ((h : X.B.I.Gf) * X.xu u) ((h : X.B.I.Gf) * (k : X.B.I.Gf) * X.xu u)
        (latOf X u h) (fun y => Iff.rfl) (fun y => by rw [← hkl]; exact Iff.rfl)
      have e4 : ((h : X.B.I.Gf) * X.xu u)⁻¹ * ((h : X.B.I.Gf) * (k : X.B.I.Gf) * X.xu u) =
          (X.xu u)⁻¹ * (k : X.B.I.Gf) * X.xu u := by group
      rw [e4] at hK
      have e5 : (k : X.B.I.Gf) = X.xu u * ((X.xu u)⁻¹ * (k : X.B.I.Gf) * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e5]
      exact kset_mul' X.B.I (kset_mul' X.B.I (X.xu_K u) hK) (kset_inv' X.B.I (X.xu_K u))
  · rintro ⟨g, hg, k, hk, rfl⟩
    obtain ⟨M, hM, hMf⟩ := gamR_mat hg
    have hst : matE X M ∈ stabF D (X.Fu u) := matE_stab X u M hM (fun y hy => by
      rw [← hMf]; exact hfin_fix X u g y hy)
    have e1 := (cls_spec hR hL h).2
    have e2 : Eqv X u (lat X u h) (lat X u (g * h * k)) :=
      ⟨matE X M, hst, (lat_act X u g h k M hMf ((mem_kR_iff X u k).1 hk)).symm⟩
    exact (cls_eq hR hL (cls_spec hR hL h).1 ((eqvEquiv X u).trans e1 e2)).symm

theorem cls_surj (hR : IsRowReps D (X.Fu u) what₂) (hL : LatRowLat X u) (hS : LatSurj X u)
    (s : Submodule (𝓞 D.host.E) (VS D).V) (hs : s ∈ what₂) : ∃ h, cls X u what₂ h = s := by
  obtain ⟨h, Λ', hΛ', he⟩ := hS s (hR.1 s hs)
  have e1 : Λ' = lat X u h := SetLike.coe_injective (hΛ'.trans (lat_coe X u h).symm)
  rw [e1] at he
  exact ⟨h, cls_eq hR hL hs ((eqvEquiv X u).symm he)⟩

end Cls

end Formalism.L2.SG.RhoPf
end
end

section

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {D : D7} (X : HidaSetting D)

def matOf (γ : (VS D).V →ₗ[D.host.E] (VS D).V) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (LinearMap.toMatrix X.bas X.bas γ).map X.ιE.symm

theorem matOf_comp (γ δ : (VS D).V →ₗ[D.host.E] (VS D).V) : matOf X (γ ∘ₗ δ) = matOf X γ * matOf X δ := by
  unfold matOf
  rw [LinearMap.toMatrix_comp X.bas X.bas X.bas]
  simpa using map_mul X.ιE.symm.mapMatrix (LinearMap.toMatrix X.bas X.bas γ) (LinearMap.toMatrix X.bas X.bas δ)

theorem matOf_id : matOf X LinearMap.id = 1 := by
  unfold matOf
  rw [LinearMap.toMatrix_id]
  simp

theorem crd_apply (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (γ y) = matOf X γ *ᵥ X.crd y := by
  funext i
  show X.ιE.symm (X.bas.repr (γ y) i) = _
  rw [← LinearMap.toMatrix_mulVec_repr X.bas X.bas γ y]
  exact RingHom.map_mulVec (X.ιE.symm : D.host.E →+* X.B.I.E) _ _ i

theorem crd_inj : Function.Injective (X.crd) := fun _ _ h =>
  X.bas.repr.injective (Finsupp.ext fun i => X.ιE.symm.injective (congrFun h i))

def glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : GL (Fin X.B.I.n) X.B.I.E where
  val := matOf X γ.toLinearMap
  inv := matOf X γ.symm.toLinearMap
  val_inv := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp
  inv_val := by
    rw [← matOf_comp, ← matOf_id X]
    congr 1
    exact LinearMap.ext fun x => by simp

theorem matE_glOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : matE X (glOf X γ) = γ := by
  apply LinearEquiv.ext
  intro y
  apply crd_inj X
  rw [matE_crd]
  exact (crd_apply X γ.toLinearMap y).symm

theorem matE_inj {M M' : GL (Fin X.B.I.n) X.B.I.E} (h : matE X M = matE X M') : M = M' := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← LatDictK.crd_vOf X x, ← matE_crd, ← matE_crd, h]

theorem hT_coord (x y : (VS D).V) :
    (VS D).hT x y = star (X.bas.equivFun x) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun y) := by
  rw [hT_expand X x y]
  simp only [← X.J_eq]
  rw [qform]

theorem form_ext {m : Type} [Fintype m] [DecidableEq m] {P Q : Matrix m m D.host.E}
    (h : ∀ a c : m → D.host.E, star a ⬝ᵥ (P *ᵥ c) = star a ⬝ᵥ (Q *ᵥ c)) : P = Q := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  have hs : star (Pi.single i (1 : D.host.E) : m → D.host.E) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  rw [hs] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem mapM_cT (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) M) = (mapM X M)ᴴ := by
  ext i j
  simp only [mapM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT,
    Matrix.transpose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]

theorem glOf_unitary (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    glOf X γ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  set A := mapM X ((glOf X γ : GL _ _) : Matrix _ _ _) with hA
  have hrep : ∀ y, X.bas.equivFun (γ y) = A *ᵥ X.bas.equivFun y := by
    intro y
    rw [hA, ← matE_repr, matE_glOf]
  have key : Aᴴ * mapM X X.B.I.J * A = mapM X X.B.I.J := by
    apply form_ext
    intro a c
    have h1 := hγ (X.bas.equivFun.symm a) (X.bas.equivFun.symm c)
    rw [hT_coord, hT_coord, hrep, hrep, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    rw [← h1, Matrix.star_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  show Formalism.UG.cT (starRingEnd X.B.I.E) ((glOf X γ : GL _ _) : Matrix _ _ _) * X.B.I.J * ((glOf X γ : GL _ _) : Matrix _ _ _) =
    X.B.I.J
  apply Matrix.map_injective X.ιE.injective
  show mapM X _ = mapM X _
  rw [map_mul, map_mul, mapM_cT]
  exact key

end Mat

section UJ

theorem uj_bc {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m]
    (φ : A →+* B) (σA : A →+* A) (σB : B →+* B) (hσ : ∀ a, φ (σA a) = σB (φ a)) (JA : Matrix m m A)
    (g : GL m A) (hg : g ∈ Formalism.UG.UJ σA JA) : Formalism.UG.bc φ g ∈ Formalism.UG.UJ σB (JA.map φ) := by
  have hg' : Formalism.UG.cT σA (g : Matrix m m A) * JA * (g : Matrix m m A) = JA := hg
  show Formalism.UG.cT σB ((g : Matrix m m A).map φ) * JA.map φ * (g : Matrix m m A).map φ = JA.map φ
  have hc : Formalism.UG.cT σB ((g : Matrix m m A).map φ) = (Formalism.UG.cT σA (g : Matrix m m A)).map φ := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end UJ

section AH

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def AH (Λ : Submodule (𝓞 D.host.E) (VS D).V) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {γ | γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, γ (X.eX a) = X.eX a) ∧ (∀ a, γ (X.fY a) = X.fY a) ∧
    γ (X.zu u) = X.zu u ∧ Formalism.HermitianLatticesTheory.gmap γ Λ = Λ}

theorem crd_fix_of (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (he : ∀ a, γ (X.eX a) = X.eX a)
    (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) (y : Fin X.B.I.n → X.B.I.E) (hy : y ∈ fixSet X u) :
    (glOf X γ : Matrix _ _ _) *ᵥ y = y := by
  have hc : ∀ v, γ v = v → (glOf X γ : Matrix _ _ _) *ᵥ X.crd v = X.crd v := fun v hv => by
    rw [← matE_crd, matE_glOf, hv]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz'
  · exact hc _ (he a)
  · exact hc _ (hf a)
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz']
    exact hc _ hz

def gOf (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (he : ∀ a, γ (X.eX a) = X.eX a) (hf : ∀ a, γ (X.fY a) = X.fY a) (hz : γ (X.zu u) = X.zu u) : Hfin X u :=
  ⟨⟨Formalism.UG.bc (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ),
    uj_bc _ _ _ (fun a => by simp [Formalism.UG.sigR, Formalism.UG.inclE]; rfl) X.B.I.J _ (glOf_unitary X γ hγ)⟩,
    fun y hy => by
      show ((glOf X γ : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F))) *ᵥ incl X.B.I y =
        incl X.B.I y
      funext i
      have := (RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (glOf X γ : Matrix _ _ _) y i).symm
      rw [crd_fix_of X u γ he hf hz y hy] at this
      exact this⟩

end AH

end Formalism.L2.SG.RhoPf
end
end
