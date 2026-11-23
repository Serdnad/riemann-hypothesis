module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle009
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle026
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellFrames

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Tri

variable {K : Type} [Field K] {m : ℕ}

theorem lowerTri_inv (A : Matrix (Fin m) (Fin m) K) (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, A i i ≠ 0) :
    (∀ i j, i < j → A⁻¹ i j = 0) ∧ ∀ i, A⁻¹ i i * A i i = 1 := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h), fun i => ?_⟩
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul A hdet) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at e
  · exact e
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA j i h, mul_zero]
    · rw [hB' (OrderDual.toDual_lt_toDual.2 h), zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem frVec_of_comb {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) (e : P'.x = P.x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (cf : Fin (Dw.mult σ) → S) (h3 : IsCombAt P.x (P.u σ) cf (P'.u σ i)) :
    frVec Y P' hx' σ i = ∑ j, cf j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1 h3
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4

  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end GlobalTheory.LogPole.CellFrames

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cellFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (Q : FrPt Xo c K), TF.X.F.ChartFr k (z ≫ inc₀ TF.X Z) hk Q → ∃ (P₀ P : FrPt Xo c K) (t : Ix Dw → Kˣ) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), FrBor t Q P ∧ (∀ σ i, (t (some ⟨σ, i⟩) : K) * ev z W hz (L σ i i) = 1) ∧ GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P ∧ IsBaseFrame TF U e v P₀ hU := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC K _ _ z hz hk Q hQ
  obtain ⟨-, hWU, -, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun p hp => hWU (hz hp)
  have hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z := Category.assoc _ _ _
  have hQx : frX Q ≫ TF.Y.j = z ≫ toBase TF Z := hQ.over.trans hx
  have hvT : ∀ m, IsTanAtG TF.Y.t (z ≫ toBase TF Z) (spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hU) (hv.1 m)
  set Lz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (L σ).map (ev z W hz) with hLzd
  set Nz : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K := fun σ => (N σ).map (ev z W hz) with hNzd
  have hLd : ∀ σ i, Lz σ i i ≠ 0 := fun σ i => ((hLu σ i).map (ev z W hz)).ne_zero
  have hLt : ∀ σ i j, i < j → Lz σ i j = 0 := fun σ i j h => by
    show ev z W hz (L σ i j) = 0
    rw [hLz σ i j h, map_zero]
  have hLinv := fun σ => CellFrames.lowerTri_inv (Lz σ) (hLt σ) (hLd σ)
  have hNdet : ∀ σ, IsUnit (Nz σ).det := fun σ => by
    rw [Matrix.det_of_upperTriangular (M := Nz σ) (fun i j h => by
      show ev z W hz (N σ i j) = 0
      rw [hNz σ i j h, map_zero])]
    refine IsUnit.prod_univ_iff.2 fun i => ?_
    show IsUnit (ev z W hz (N σ i i))
    rw [hN1, map_one]; exact isUnit_one
  have hLdet : ∀ σ, IsUnit (Lz σ).det := fun σ => by
    rw [Matrix.det_of_lowerTriangular (Lz σ) (fun i j h => hLt σ i j (OrderDual.toDual_lt_toDual.1 h))]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hLd σ i)
  have hAdet : ∀ σ, IsUnit (Lz σ * Nz σ).det := fun σ => by
    rw [Matrix.det_mul]; exact (hLdet σ).mul (hNdet σ)
  have hA : ∀ σ, Lz σ * Nz σ = (L σ * N σ).map (ev z W hz) := fun σ => Matrix.map_mul.symm
  have hvec : ∀ σ i, frVec TF.Y Q hQx σ i =
      ∑ j, (Lz σ * Nz σ) i j • GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩)) := fun σ i => by
    rw [hQ.frVec_eq hx hQx σ]
    have h1 := hcomb K z hz hU hk hx σ i
    have h2 := (GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))) _ _).1 h1
    rw [h2, hA]
    rfl
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K Q (fun σ => (Lz σ * Nz σ)⁻¹) 1
    (fun σ => (Matrix.isUnit_nonsing_inv_det_iff).2 (hAdet σ))
  obtain ⟨P, hP, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K P₀ Nz 1 hNdet
  rw [Units.val_one] at hP₀ hP
  have hQP := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c K).1 _ _ _ _ _ _ _ hP₀).1 hP
  have hg : (fun σ => Nz σ * (Lz σ * Nz σ)⁻¹) = fun σ => (Lz σ)⁻¹ := funext fun σ => by
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hNdet σ), Matrix.one_mul]
  rw [hg, _root_.mul_one] at hQP
  let t : Ix Dw → Kˣ := fun ix => Option.elim ix 1 fun p => Units.mk0 ((Lz p.1 p.2 p.2)⁻¹) (inv_ne_zero (hLd _ _))
  have hP₀x : frX P₀ ≫ TF.Y.j = z ≫ toBase TF Z := by
    rw [eq_frX Q ((frX_fst P₀).trans hP₀.1) (frX_snd P₀)]; exact hQx
  have hU' : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1 := hP₀x ▸ hU
  refine ⟨P₀, P, t, hU', ?_, fun σ i => ?_, hP, fun σ i => ?_⟩
  · refine (GlobalTheory.Frames.frBor_iff_frChg Q P t).2 ⟨fun σ => (Lz σ)⁻¹, fun σ i j h => (hLinv σ).1 i j h,
      fun σ i => eq_inv_of_mul_eq_one_left ((hLinv σ).2 i), ?_⟩
    show GlobalTheory.Frames.FrChg _ ((1 : Kˣ) : K) Q P
    rw [Units.val_one]
    exact hQP
  · show (Lz σ i i)⁻¹ * Lz σ i i = 1
    exact inv_mul_cancel₀ (hLd σ i)
  · have h0 := CellFrames.frVec_of_comb (TF.X.F.inM hk hx) hQx hP₀x hP₀.1 σ i _ (hP₀.2.1 σ i)
    have hI := Matrix.nonsing_inv_mul _ (hAdet σ)
    have key : frVec TF.Y P₀ hP₀x σ i = GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, i⟩)) := by
      rw [h0]
      simp only [hvec, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      have e2 : ∀ l, (∑ j, (Lz σ * Nz σ)⁻¹ i j * (Lz σ * Nz σ) j l) = (1 : Matrix _ _ K) i l := fun l => by
        rw [← hI, Matrix.mul_apply]
      simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : (tv (frVec TF.Y P₀ rfl σ i)).left = (tv (frVec TF.Y P₀ hP₀x σ i)).left := rfl
    rw [e1, key, GlobalTheory.LieMet.left_tanOf, ev_congr hP₀x U.1 hU' hU]

end GlobalTheory.LogPole
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_eigComb_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC S _ zw hzw x hx hUx σ a b w' ha hb
  subst hx
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (hzw hp)
  have hxx : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hvT : ∀ m, IsTanAtG TF.Y.t (zw ≫ toBase TF Z) (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hUx) (hv.1 m)
  let f : Fin (Dw.mult σ) → TanM (zw ≫ toBase TF Z) TF.Y.t.G := fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))
  have uniq : ∀ {w₁ w₂ : Sp (DualNumber S) ⟶ TF.Y.t.G.left} (cf : Fin (Dw.mult σ) → S),
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₁ →
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₂ → w₁ = w₂ := by
    intro w₁ w₂ cf h₁ h₂
    obtain ⟨u₁, hu₁, hw₁⟩ := h₁
    obtain ⟨u₂, hu₂, hw₂⟩ := h₂
    have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
    rw [← hw₁, ← hw₂, hu]
  have hsum : ∀ cf : Fin (Dw.mult σ) → S,
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf (tv (∑ j, cf j • f j)).left :=
    fun cf => (GlobalTheory.LieMet.isComb_iff f cf _).2 rfl
  have hab : ∑ j, a j • f j = ∑ j, b j • f j :=
    GlobalTheory.LieMet.tan_ext ((uniq a (hsum a) ha).trans (uniq b (hsum b) hb).symm)
  let V := TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxx σ
  let C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := (L σ * N σ).map (ev zw W hzw)
  have hV : ∀ i, V i = ∑ j, C i j • f j := fun i =>
    (GlobalTheory.LieMet.isComb_iff f _ _).1 (hcomb S zw hzw hUx hk hxx σ i)
  have hCdet : IsUnit C.det := by
    have hm : C = (L σ).map (ev zw W hzw) * (N σ).map (ev zw W hzw) := Matrix.map_mul
    rw [hm, Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => by
        show ev zw W hzw (L σ i j) = 0
        rw [hLz σ i j (OrderDual.toDual_lt_toDual.1 h), map_zero])]
      exact IsUnit.prod_univ_iff.2 fun i => (hLu σ i).map (ev zw W hzw)
    · rw [Matrix.det_of_upperTriangular (M := (N σ).map (ev zw W hzw)) (fun i j h => by
        show ev zw W hzw (N σ i j) = 0
        rw [hNz σ i j h, map_zero])]
      refine IsUnit.prod_univ_iff.2 fun i => ?_
      show IsUnit (ev zw W hzw (N σ i i))
      rw [hN1, map_one]; exact isUnit_one
  have hf' : ∀ j, f j = ∑ i, C⁻¹ j i • V i := fun j => by
    simp only [hV, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have e2 : ∀ l, (∑ i, C⁻¹ j i * C i l) = (1 : Matrix _ _ S) j l := fun l => by
      rw [← Matrix.nonsing_inv_mul _ hCdet, Matrix.mul_apply]
    simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • f j = ∑ i, Matrix.vecMul cf C⁻¹ i • V i := fun cf => by
    simp only [hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.vecMul, dotProduct]
  have hg : Matrix.vecMul a C⁻¹ = Matrix.vecMul b C⁻¹ := funext
    (Fintype.linearIndependent_iffₛ.1 (TF.X.F.linearIndependent_vecAt k _ hk hxx σ) _ _
      (by rw [← key, ← key, hab]))
  calc a = Matrix.vecMul (Matrix.vecMul a C⁻¹) C := by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul b C⁻¹) C := by rw [hg]
    _ = b := by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]

end GlobalTheory.LogPole
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.LogPole.frVec_cell_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h S _ _ w zw hzw x hx hUx hpt
  have hl : TF.X.F.Lies (zw ≫ inc₀ TF.X Z) w := hpt ▸ TF.X.lies_ptY w
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map _ h.2.2.1 hzw
  have hxz' : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hxz : zw ≫ toBase TF Z = x := hxz'.symm.trans (hl.1.trans hx)
  subst hxz
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd w) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  choose b hb hdiag hsum using fun σ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (TF.X.F.M k).toMChart) (TF.X.F.inM hk hxz') (hQ.over.trans hxz') hx ht σ
  refine ⟨fun σ i j => b σ j i, fun σ i j hij => hb σ hij, fun σ i => by show IsUnit (b σ i i); rw [hdiag]; exact Units.isUnit _,
    fun σ i => ?_⟩
  have hv' : ∀ j, IsTanAtG TF.Y.t (zw ≫ toBase TF Z)
      (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v j) := by
    intro j
    have h0 := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (zw ≫ toBase TF Z) U.1 hUx) (hv.1 j)
    rwa [LogKS.chart, GlobalTheory.FlagMod.spMap_ev _ U.2 hUx] at h0
  have hcell := h.2.2.2.2.2.2.2 S zw hzw hUx hk hxz' σ
  have h2 : IsCombAtG TF.Y.t (zw ≫ toBase TF Z)
      (fun j => (tv (TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxz' σ j)).left) (fun j => b σ j i)
      (tv (frVec TF.Y w hx σ i)).left := by
    rw [GlobalTheory.LieMet.isComb_iff, hsum σ i, hQ.frVec_eq hxz' (hQ.over.trans hxz') σ]
  have h3 := GlobalTheory.TangentLinear.isCombAtG_mulVec _ (fun j => hv' (e ⟨σ, j⟩)) _
    (Matrix.of fun m j => ev zw W hzw ((L σ * N σ) j m)) (fun j => b σ j i) _ (fun j => hcell j) h2
  convert h3 using 1
  funext m
  show ∑ j, b σ j i * ev zw W hzw ((L σ * N σ) j m) = ∑ j, ev zw W hzw ((L σ * N σ) j m) * b σ j i
  exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellMono

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem initSpan_eq_of_lowerTri {R : Type} [CommRing R] {m : ℕ} {M : Type} [AddCommGroup M] [Module R M]
    {A : Matrix (Fin m) (Fin m) R} (hA : ∀ i j, i < j → A i j = 0) (hd : ∀ i, IsUnit (A i i)) {u w : Fin m → M}
    (e : ∀ i, u i = ∑ j, A i j • w j) (k : ℕ) : initSpan R u k = initSpan R w k := by
  have hB : A.BlockTriangular OrderDual.toDual := fun i j h => hA i j (OrderDual.toDual_lt_toDual.1 h)
  have hdet : IsUnit A.det := by
    rw [Matrix.det_of_lowerTriangular A hB]
    exact IsUnit.prod_univ_iff.2 hd
  have : Invertible A := Matrix.invertibleOfIsUnitDet A hdet
  have hB' := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine le_antisymm (initSpan_le_of_tri (B := A.transpose) (fun i j h => hA j i h) e k)
    (initSpan_le_of_tri (B := A⁻¹.transpose) (fun i j h => hB' (OrderDual.toDual_lt_toDual.2 h)) (fun i => ?_) k)
  simp only [e, Finset.smul_sum, smul_smul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have e2 : ∀ l, (∑ j, A⁻¹ i j * A j l) = (1 : Matrix _ _ R) i l := fun l => by
    rw [← Matrix.nonsing_inv_mul A hdet, Matrix.mul_apply]
  simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S : Type} [CommRing S] [Algebra c.F S]

theorem eq_of_initSpan_eq (X : FlagCover Y) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) {x : Sp S ⟶ Y.X} (hxy : x = y ≫ Y.j) {z z' : Sp S ⟶ X.YY}
    (hx : z ≫ X.π = x) (hx' : z' ≫ X.π = x) {k k' : X.F.J} (hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k')
    (h : ∀ σ i, initSpan S (X.F.vecAt k' z' hz' hx' σ) i = initSpan S (X.F.vecAt k z hz hx σ) i) : z = z' := by
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy (hx.trans hxy) k hz
  obtain ⟨P, hP⟩ := X.top.exists_chartFr hy (hx'.trans hxy) k' hz'
  have hQx := hQ.over.trans hx
  have hPx := hP.over.trans hx'
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y P hPx σ i = ∑ j, b j i • frVec Y Q hQx σ j := fun σ => by
    rw [hQ.frVec_eq hx, hP.frVec_eq hx']
    exact exists_tri_of_eq (X.F.linearIndependent_vecAt k z hz hx σ) (h σ)
  choose b hb hu hv using ex
  have e : P.x = Q.x := by
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd P) (frX_snd Q) (hPx.trans hQx.symm)]
  have hB : ∃ t, FrBor t Q P := by
    obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P
    dsimp only at e
    subst e
    obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
    exact ⟨_, frBor_of_frVec (X.F.inM hz hx) hQx hPx
      (fun ix => match ix with | none => u0 | some p => (hu p.1 p.2).unit) b hb (fun _ _ => rfl) hv fun _ => hu0⟩
  obtain ⟨t, ht⟩ := hB
  exact (X.rep S P).unique (hQ.lies.frBor ht) hP.lies

end GlobalTheory.LogPole.CellMono

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem eq_of_cellCoord_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (S : Type) [CommRing S] (z₁ z₂ : Sp S ⟶ Y₀ TF.X Z) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W), ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z → ⊤ ≤ z₂ ⁻¹ᵁ U₀ TF.X Z → (∀ r, ev z₁ W h₁ (((toBase TF Z).appLE U.1 W h.2.1).hom r) = ev z₂ W h₂ (((toBase TF Z).appLE U.1 W h.2.1).hom r)) → (∀ i, ev z₁ W h₁ (cellCoord N i) = ev z₂ W h₂ (cellCoord N i)) → z₁ = z₂ := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N hC S _ z₁ z₂ h₁ h₂ o₁ _ hr hN
  have hU : ∀ {z : Sp S ⟶ Y₀ TF.X Z}, ⊤ ≤ z ⁻¹ᵁ W → ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1 := fun hz p hp => hC.2.1 (hz hp)
  have hb : z₂ ≫ toBase TF Z = z₁ ≫ toBase TF Z := by
    rw [← spMap_ev _ U.2 (hU h₁), ← spMap_ev _ U.2 (hU h₂)]
    congr 2
    ext r
    exact (ev_appLE z₂ _ hC.2.1 h₂ (hU h₂) r).symm.trans ((hr r).symm.trans (ev_appLE z₁ _ hC.2.1 h₁ (hU h₁) r))
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hNN : ∀ σ i j, ev z₂ W h₂ (N σ i j) = ev z₁ W h₁ (N σ i j) := fun σ i j => by
    rcases lt_trichotomy i j with h | rfl | h
    · exact (hN ⟨σ, ⟨(i, j), h⟩⟩).symm
    · rw [hN1, map_one, map_one]
    · rw [hNz σ i j h, map_zero, map_zero]
  have hvT : ∀ m, IsTanAtG TF.Y.t (z₁ ≫ toBase TF Z) (spMap (dualMap (ev (z₁ ≫ toBase TF Z) U.1 (hU h₁))) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 (hU h₁)) (hv.1 m)
  have key : ∀ (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k)
      (x : Sp S ⟶ TF.Y.X) (hxU : ⊤ ≤ x ⁻¹ᵁ U.1) (hT : ∀ m, IsTanAtG TF.Y.t x (spMap (dualMap (ev x U.1 hxU)) ≫ v m))
      (_ : z ≫ toBase TF Z = x) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x) σ i,
      initSpan S (TF.X.F.vecAt k _ hk hx σ) i = initSpan S
        (fun a => ∑ j, ev z W hz (N σ a j) • GlobalTheory.LieMet.tanOf (hT (e ⟨σ, j⟩))) i := by
    rintro z hz hk _ hxU hT rfl hx σ
    refine CellMono.initSpan_eq_of_lowerTri (A := (L σ).map (ev z W hz)) (fun i j h => ?_)
      (fun i => (hLu σ i).map (ev z W hz)) fun i => ?_
    · show ev z W hz (L σ i j) = 0
      rw [hLz σ i j h, map_zero]
    · rw [(GlobalTheory.LieMet.isComb_iff (fun j => GlobalTheory.LieMet.tanOf (hT (e ⟨σ, j⟩))) _ _).1 (hcomb S z hz hxU hk hx σ i)]

      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
      exact Finset.sum_comm
  have hrg : Set.range (z₁ ≫ inc₀ TF.X Z) ⊆ Set.range TF.X.inc := by
    rintro _ ⟨s, rfl⟩; exact (opensRange_inc TF.X).ge (o₁ (Set.mem_univ s))
  obtain ⟨w, hw⟩ : ∃ w, w ≫ TF.X.inc = z₁ ≫ inc₀ TF.X Z := ⟨_, IsOpenImmersion.lift_fac TF.X.inc _ hrg⟩
  letI : Algebra c.F S := ((ev (w ≫ pullback.snd TF.X.π TF.Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  have hy : (w ≫ pullback.snd TF.X.π TF.Y.j) ≫ pullback.snd _ _ = spMap (algebraMap c.F S) :=
    (Category.assoc _ _ _).trans (spMap_ev_top _).symm
  have hx₁ : (z₁ ≫ inc₀ TF.X Z) ≫ TF.X.π = z₁ ≫ toBase TF Z := Category.assoc _ _ _
  have hx₂ : (z₂ ≫ inc₀ TF.X Z) ≫ TF.X.π = z₁ ≫ toBase TF Z := (Category.assoc _ _ _).trans hb
  have hxy : z₁ ≫ toBase TF Z = (w ≫ pullback.snd TF.X.π TF.Y.j) ≫ TF.Y.j := by
    rw [← hx₁, ← hw, Category.assoc, Category.assoc, pullback.condition]
  have hk₁ : ⊤ ≤ (z₁ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (h₁ hp)
  have hk₂ : ⊤ ≤ (z₂ ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (h₂ hp)
  rw [← cancel_mono (inc₀ TF.X Z)]
  refine CellMono.eq_of_initSpan_eq TF.X hy hxy hx₁ hx₂ hk₁ hk₂ fun σ i => ?_
  rw [key z₁ h₁ hk₁ _ (hU h₁) hvT rfl hx₁, key z₂ h₂ hk₂ _ (hU h₁) hvT hb hx₂]
  simp only [hNN]

end GlobalTheory.LogPole
end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

theorem _root_.GlobalTheory.T.theta_lift_darboux_adelic_symplectic : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGen τ C γ Y → ∀ (T : Tens F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRep.archRep | exact GlobalTheory.ArchRep.archRep | (intros; apply GlobalTheory.ArchRep.archRep <;> assumption)
end
