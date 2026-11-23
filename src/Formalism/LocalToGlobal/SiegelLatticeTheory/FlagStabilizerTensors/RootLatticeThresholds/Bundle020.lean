module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle017
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.SpectralTiesReal

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj

def CarrierSideBoundPositive (Cb : ℝ) : Prop :=
  ∀ C₆ Cc : ℝ, 0 < C₆ → ∃ CA₀ : ℝ, ∀ CA : ℝ, CA₀ ≤ CA → 1 ≤ CA →
    ∀ C0 CG CDel cT Cb' : ℝ, 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb' → 1 < cT * Cb' →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
      (τ : D.what₂.Tau) (Cp Th' : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
      {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
      (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
      Formalism.BasicNotions.Ties D → u ≠ u' → k0 ≤ (gOf D e).k → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
        (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.CarrierT.CarrierDataBound T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq
        (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).IntN CA (gOf D e) (deOf D τ u) (deOf D τ u')
        (lOf D (deOf D τ u) (deOf D τ u')) C₆ Cc Cb

end Formalism.L2.SG.SpectralTiesReal
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def nfE (D : D7) : ℕ := Fintype.card (InfinitePlace D.host.E)

def plE (D : D7) : Fin (nfE D) ≃ InfinitePlace D.host.E := (Fintype.equivFin _).symm

def tauE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Fin (nfE D) ≃ InfinitePlace X.B.I.F :=
  (plE D).trans (e.trans X.pl.symm)

def embE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (j : Fin (nfE D)) : D.host.E →+* ℂ :=
  (X.B.I.φ (tauE X e j)).comp X.ιE.symm.toRingHom

def PlaceTie (e : InfinitePlace D.host.E ≃ D.what₂.Tau) : Prop :=
  ∀ x : InfinitePlace D.host.E, InfinitePlace.mk ((X.B.I.φ (X.pl.symm (e x))).comp X.ιE.symm.toRingHom) = x

theorem hembE (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (h : PlaceTie X e) (j : Fin (nfE D)) :
    InfinitePlace.mk (embE X e j) = plE D j := h (plE D j)

def castLoc (u : D.what₂.Word) {v w : InfinitePlace X.B.I.F} (h : v = w) : X.Vloc u v ≃ₗᵢ[ℂ] X.Vloc u w := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

theorem tauE_symm (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (v : InfinitePlace X.B.I.F) :
    X.pl.symm (e (plE D ((tauE X e).symm v))) = v := by
  simp [tauE]

def carrierInOf (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ) :
    CarrierIn X u u' where
  Wp := fun x => X.Vloc u (X.pl.symm (e x))
  Wq := fun x => X.Vloc u' (X.pl.symm (e x))
  nf := nfE D
  pl := plE D
  emb := embE X e
  hemb := hembE X e he
  G := Formalism.L2.SG.SpectralTiesReal.gOf D e
  CA := CA
  de := de
  de' := de'
  l := l
  grid := grid
  grid1 := grid1
  hv := hv
  T := T
  hT := hT
  fc := fc
  χ := χ
  sg := sg
  ν' := ν'
  m₀ := m₀
  top := top
  A₀ := A₀
  τ := tauE X e
  Q := fun v => Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)
  Qi := fun v => Formalism.L2.SG.LocWSOf.Qics C (X.pl v)
  eP := fun v => castLoc X u (tauE_symm X e v)
  eQ := fun v => castLoc X u' (tauE_symm X e v)

end Formalism.L2.SG.Pf.Carrier
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section LocRel

variable {n r : ℕ} (ε : Fin n → Bool)

theorem relA_loc (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hfz' : ∀ a, hJ ε (f a) z' = 0) (S Si G T : Matrix (Fin n) (Fin n) ℂ)
    (hSi : InS e z Si) (hT : InS e z' T) (hadj : ∀ x y, hJ ε x (S *ᵥ y) = hJ ε (Si *ᵥ x) y)
    (hrel : S * G = G * T) (a b : Fin (r + 1)) :
    (∑ c : Fin r, if c.castSucc < a then conj (hJ ε (f c) (Si *ᵥ fam e z a)) *
        RealObj.Zhat ε (fam e z) (fam e z') G c.castSucc b else 0) =
      ∑ c : Fin r, if c.castSucc < b then hJ ε (f c) (T *ᵥ fam e z' b) *
        RealObj.Zhat ε (fam e z) (fam e z') G a c.castSucc else 0 := by
  have L : hJ ε (fam e z a) ((S * G) *ᵥ fam e z' b) = hJ ε (fam e z a) ((G * T) *ᵥ fam e z' b) := by
    rw [hrel]
  rw [← Matrix.mulVec_mulVec, hadj, flag_expand ε e f z hfe hfz Si hSi a, hJ_sum_l'] at L
  rw [← Matrix.mulVec_mulVec, flag_expand ε e f z' hfe hfz' T hT b, Matrix.mulVec_add, Matrix.mulVec_sum] at L
  simp only [Matrix.mulVec_smul] at L
  rw [hJ_add_r', hJ_sum_r'] at L
  have L2 := add_left_cancel L
  calc _ = ∑ c : Fin r, conj (if c.castSucc < a then hJ ε (f c) (Si *ᵥ fam e z a) else 0) *
        hJ ε (e c) (G *ᵥ fam e z' b) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp only [RealObj.Zhat, fam_castSucc]
        · simp
    _ = ∑ c : Fin r, (if c.castSucc < b then hJ ε (f c) (T *ᵥ fam e z' b) else 0) *
        hJ ε (fam e z a) (G *ᵥ e c) := L2
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp only [RealObj.Zhat, fam_castSucc]
        · simp

theorem rootCoord_one (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0) (a : Fin r) :
    rootCoord ε e f z 1 a = 0 := by
  unfold rootCoord nxt
  rw [Matrix.one_mulVec]
  split_ifs with hlt
  · rw [hfe, if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp at this
  · exact hfz a

theorem rel_loc (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ)
    (hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hfz' : ∀ a, hJ ε (f a) z' = 0) (S Si G T : Matrix (Fin n) (Fin n) ℂ)
    (hS : InS e z S) (hSi : InS e z Si) (hSiS : Si * S = 1) (hT : InS e z' T)
    (hadj : ∀ x y, hJ ε x (S *ᵥ y) = hJ ε (Si *ᵥ x) y) (hrel : S * G = G * T)
    (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hP2 : ∀ k : Fin r, ((π k.succ).val + 1 = (π k.castSucc).val ∧
        RealObj.Zhat ε (fam e z) (fam e z') G (π k.succ) k.succ = - RealObj.Zhat ε (fam e z) (fam e z') G (π k.castSucc) k.castSucc) ∨
        (π k.castSucc).val < (π k.succ).val) :
    ∑ k : Fin r, (rootCoord ε e f z' T k).re = ∑ k : Fin r, (rootCoord ε e f z S k).re := by
  have h := relAlg (RealObj.Zhat ε (fam e z) (fam e z') G) π hπ hP1 hP2
    (fun c a => hJ ε (f c) (Si *ᵥ fam e z a)) (fun c b => hJ ε (f c) (T *ᵥ fam e z' b))
    (relA_loc ε e f z z' hfe hfz hfz' S Si G T hSi hT hadj hrel)
  have hU : ∀ k : Fin r, rootCoord ε e f z' T k = hJ ε (f k) (T *ᵥ fam e z' k.succ) := by
    intro k; unfold rootCoord; rw [nxt_eq_fam]
  have hm : ∀ k : Fin r, hJ ε (f k) (Si *ᵥ fam e z k.succ) = - rootCoord ε e f z S k := by
    intro k
    have h1 := Formalism.L2.SG.Pf.Vanish2.rootCoord_mul ε e f z hfe hfz hSi hS k
    rw [hSiS, rootCoord_one ε e f z hfe hfz] at h1
    have h2 : rootCoord ε e f z Si k = hJ ε (f k) (Si *ᵥ fam e z k.succ) := by
      unfold rootCoord; rw [nxt_eq_fam]
    rw [← h2]; linear_combination -h1
  simp only [hU]
  rw [h]
  simp only [hm, Complex.neg_re, Finset.sum_neg_distrib, neg_neg]

theorem sum_add_star {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    ∑ a, (x a + star (x a)) = ((2 * ∑ a, (x a).re : ℝ) : ℂ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.add_conj]
  push_cast
  ring

theorem psiR_eq_of (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (S T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∑ k : Fin r, (rootCoord ε e f z' T k).re = ∑ k : Fin r, (rootCoord ε e f z S k).re) :
    psiR ε gg e f z S = psiR ε gg e f z' T := by
  unfold psiR
  rw [sum_add_star, sum_add_star, h]

theorem psiR_mul_star (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (S : Matrix (Fin n) (Fin n) ℂ) :
    psiR ε gg e f z S * star (psiR ε gg e f z S) = 1 := by
  unfold psiR
  rw [sum_add_star, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  ring

end LocRel

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a; simp [famSc]

theorem stRel_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StRel X u u' := by
  intro w hw s hs
  set γ := gamW X u u' w with hγdef
  have hγ : IsPtRep X u u' w γ := by
    rw [hγdef, gamW, dite_eq_left hw.1]; exact hw.1.choose_spec
  unfold psiU psiInf
  rw [Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [← Complex.star_def]
  set ε := X.B.I.ε v
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.eR a)
  set f : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => rv X.B.I v (X.fR a)
  set z := rv X.B.I v (X.zR u)
  set z' := rv X.B.I v (X.zR u')
  have hfe : ∀ a b, hJ ε (f a) (e b) = if b = a then 1 else 0 := by
    intro a b
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hE_f_e]
    split_ifs <;> simp
  have hfz : ∀ (u : D.what₂.Word) a, hJ ε (f a) (rv X.B.I v (X.zR u)) = 0 := by
    intro u a
    rw [Formalism.L2.SG.Pf.Level.hJ_rv, Formalism.L2.SG.Pf.Vanish2.hermitian_f_z_zero, map_zero]
  have hS : InS e z (uMat (s v)) := (hs.1 v).1
  have hT : InS e z' (uMat ((γ⁻¹ * s * γ) v)) := (hs.2 v).1
  have hSiS : uMat (s v)⁻¹ * uMat (s v) = 1 := Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' (s v)
  have hSi : InS e z (uMat (s v)⁻¹) := Formalism.L2.SG.RealObj.InfCut.inS_inv e z _ _ hSiS hS
  have hrel : uMat (s v) * uMat (γ v) = uMat (γ v) * uMat ((γ⁻¹ * s * γ) v) := by
    have e1 : s v * γ v = γ v * (γ⁻¹ * s * γ) v := by
      simp only [Pi.mul_apply, Pi.inv_apply]; group
    have e2 : uMat (s v * γ v) = uMat (γ v * (γ⁻¹ * s * γ) v) := by rw [e1]
    simpa [uMat] using e2

  have hZ : ZX X u u' 1 γ v = RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) := by
    simp only [ZX, frm, famSc_one]; rfl
  have hO := hγ v
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hZe : ∀ c b : Fin (D.R.rS + 1), RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) c b =
      (-1 : ℂ) ^ (D.R.rS - b.1) * X.B.I.φ v (X.ιE.symm (if c.val = ptPar w.1 b.val then ptSc w.1 b.val else 0)) := by
    intro c b
    have h1 := congrFun (congrFun hO c) b
    simp only [RealObj.ZhatO, ptC, Matrix.map_apply, ptMat, hZ] at h1
    rw [← ptEntry_eq w.1 c.val b.val (by rw [hsum]; exact b.2), ← h1, ← mul_assoc, ← mul_pow]
    norm_num
  have hne : ∀ b : ℕ, b < D.R.rS + 1 → X.B.I.φ v (X.ιE.symm (ptSc w.1 b)) ≠ 0 := by
    intro b hb
    rw [map_ne_zero, map_ne_zero]
    exact ptSc_ne w.1 w.2.1 b (by rw [hsum]; exact hb)
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [hsum]; exact b.2)) hsum⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.val (by rw [hsum]; exact a.2))
  have hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    rw [hZe]
    by_cases h : c.val = ptPar w.1 b.val
    · rw [if_pos h]
      refine ⟨fun _ => Fin.ext h, fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne b.val b.2)⟩
    · rw [if_neg h, map_zero, map_zero, mul_zero]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (congrArg Fin.val h') h⟩
  have hP2 : ∀ k : Fin D.R.rS, ((π k.succ).val + 1 = (π k.castSucc).val ∧
      RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) (π k.succ) k.succ =
        - RealObj.Zhat ε (fam e z) (fam e z') (uMat (γ v)) (π k.castSucc) k.castSucc) ∨
      (π k.castSucc).val < (π k.succ).val := by
    intro k
    have hsz : ∀ b ∈ w.1, 1 ≤ b.2 := fun b hb => (w.2.1 b hb).2
    rcases ptPar_consec w.1 hsz k.val (by rw [hsum]; omega) with h3 | h3
    · left
      refine ⟨h3.1, ?_⟩
      rw [hZe, hZe, if_pos rfl, if_pos rfl]
      simp only [Fin.val_succ, Fin.val_castSucc]
      rw [h3.2]
      have hk : D.R.rS - k.val = (D.R.rS - (k.val + 1)) + 1 := by omega
      rw [hk, pow_succ]; ring
    · right; exact h3
  have hR := rel_loc ε e f z z' hfe (hfz u) (hfz u') (uMat (s v)) (uMat (s v)⁻¹) (uMat (γ v))
    (uMat ((γ⁻¹ * s * γ) v)) hS hSi hSiS hT (fun x y => Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (s v) x y)
    hrel π hπ hP1 hP2
  rw [psiR_eq_of ε X.B.g e f z z' _ _ hR]
  exact psiR_mul_star ε X.B.g e f z' _

end Glob

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem intN_massDataY : (massDataY X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).IntN = IntNX X u u' ψ := rfl

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end
