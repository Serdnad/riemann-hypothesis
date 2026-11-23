module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle064
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsomHTSymm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle076
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle077
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018

@[expose] public section

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Sandwich

variable {K : Type*} [CommRing K] {r : ℕ}

theorem corner_sandwich (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hA : ∀ i, A i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hB : ∀ j, B (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : K) :
    A * cornerM (r := r) c * B = cornerM c := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [hA, hB]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    have h0 : ∀ k, (A i k * if k = Fin.last r ∧ l = Fin.last r then c else 0) = 0 := by
      intro k
      simp [hl]
    simp [h0]
  · simp

theorem Ec_eq_cornerM : (Ec (K := K) r) = cornerM 1 := rfl

end Sandwich

section Comp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L)

def π1 : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def π2 : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

theorem π1_apply (x : E) : π1 M g x = (g.e x).1 := rfl
theorem π2_apply (x : E) : π2 M g x = (g.e x).2 := rfl

variable {r : ℕ}

def mmG (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun i j => g.e.symm ((g.e (P i j)).2, (g.e (L j i)).1)

def uuG (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun i j => g.e.symm ((g.e (P i j)).1, (g.e (L j i)).2)

theorem middleMatrix_map_firstComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (mmG M g L P).map (π1 M g) = P.map (π2 M g) := by
  ext i j
  simp [mmG, π1_apply, π2_apply]
theorem middleMatrix_map_secondComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (mmG M g L P).map (π2 M g) = (L.map (π1 M g))ᵀ := by
  ext i j
  simp [mmG, π1_apply, π2_apply]
theorem unipotentMatrix_map_firstComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (uuG M g L P).map (π1 M g) = P.map (π1 M g) := by
  ext i j
  simp [uuG, π1_apply, π2_apply]
theorem unipotentMatrix_map_secondComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (uuG M g L P).map (π2 M g) = (L.map (π2 M g))ᵀ := by
  ext i j
  simp [uuG, π1_apply, π2_apply]

theorem zzPlus_map_firstComponent (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Zh T T').map (π1 M g) =
      ((g.q : F))⁻¹ • Zh.map (π1 M g) + (T / (g.q : F)) • Ec r := by
  ext a b
  simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  rw [Ec_eq_cornerM]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [h, cornerM, π1_apply]
    ring
  · simp [h, cornerM, π1_apply]
    ring

theorem zzPlus_map_secondComponent (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Zh T T').map (π2 M g) =
      (-((g.q : F))⁻¹) • (Zh.map (π2 M g))ᵀ + (-(T' / (g.q : F))) • Ec r := by
  ext a b
  simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  rw [Ec_eq_cornerM]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [h, cornerM, π2_apply]
    ring
  · simp [h, cornerM, π2_apply]
    ring

end Comp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocVol

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem three_dvd_cubic (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by

  obtain ⟨k, hk | hk | hk⟩ : ∃ k, r = 3 * k ∨ r = 3 * k + 1 ∨ r = 3 * k + 2 := ⟨r / 3, by omega⟩
  · subst hk
    exact ⟨(3 * k + 1) * (6 * k + 1) * (4 * k + 1), by ring⟩
  · subst hk
    exact ⟨(3 * k + 2) * (2 * k + 1) * (12 * k + 7), by ring⟩
  · subst hk
    exact ⟨(k + 1) * (8 * (3 * k + 2) ^ 2 + 10 * (3 * k + 2) + 3), by ring⟩

variable {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
  (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem frameVolAt_of (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) (hP : ProdConv X u u' ψ) :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq := by
  have hMS := Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds X u u' ψ hψ hstd hP
  have hZZ : 0 < (locOf X u u' ψ).volZZ := hP.2.2.2.2.2.2.1
  unfold Formalism.L2.SG.NGAnalytic.MassDataLemmas.FrameVolAt
  show ((locOf X u u' ψ).localVolumeArchimedean * ∏ p, (locOf X u u' ψ).localVolumeAtPlace p) / (locOf X u u' ψ).volZZ = _
  unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.LemmaMS at hMS
  rw [hMS, mul_div_assoc, div_self hZZ.ne', mul_one]
  have hv : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  have he : (((D.R.f * (D.R.rS + 1) * (8 * D.R.rS ^ 2 + 10 * D.R.rS + 3) : ℕ) : ℝ) / 3) =
      ((D.R.f * Formalism.L2.SG.Pf.Carrier.EnergyConst.e1 D : ℕ) : ℝ) := by
    unfold Formalism.L2.SG.Pf.Carrier.EnergyConst.e1
    obtain ⟨c, hc⟩ := three_dvd_cubic D.R.rS
    rw [mul_assoc, hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
    push_cast
    ring
  have hg : (X.B.g : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) := by rw [X.g_eq]; simp [Formalism.MainNotions.S.Lat.gS]
  rw [hv, he, Real.rpow_natCast, hg, mul_assoc D.R.f]

end Formalism.L2.SG.Pf.MassDataX
end
end

section

noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem coef_zero {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {c : ι → E}
    (h0 : ∀ i, H.h (∑ j, c j • v j) (v i) = 0) : c = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  have hG : H.gram v *ᵥ c = 0 := by
    funext i
    have h := h0 i

    rw [← hL_apply, map_sum] at h
    simp only [map_smul, hL_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h := congrArg (fun x => N *ᵥ x) hG
  simp only [Matrix.mulVec_mulVec, hNG, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

theorem linInd_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) :
    LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := coef_zero hN (c := g) (fun k => by rw [hg]; exact H.h_zero_left _)
  exact congrFun h i

theorem prim_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {Λ : Submodule M.L.O V} (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) : H.Prim Λ v := by
  refine ⟨hv, linInd_of_gramInv hN, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hw0 : x - ∑ j, c j • v j = 0 := eq_zero_of_orth hN (Submodule.sub_mem _ hxs (comb_mem_span v c)) hw
  rw [sub_eq_zero.1 hw0]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range v)).smul_mem (⟨c j, hc j⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

theorem prim_inr {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {a : ι₁ → V}
    {b : ι₂ → V} (hN : GramInv H (Sum.elim a b)) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ k, Sum.elim a b k ∈ Λ) : H.Prim Λ b := by
  refine ⟨fun j => hv (Sum.inr j), (linInd_of_gramInv hN).comp Sum.inr Sum.inr_injective, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hsp : Submodule.span E (Set.range b) ≤ Submodule.span E (Set.range (Sum.elim a b)) :=
    Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inr j, rfl⟩)
  have hw0 : x - ∑ k, c k • Sum.elim a b k = 0 :=
    eq_zero_of_orth hN (Submodule.sub_mem _ (hsp hxs) (comb_mem_span _ c)) hw
  have hx' : x = ∑ k, c k • Sum.elim a b k := sub_eq_zero.1 hw0
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have hsum : ∑ k, Sum.elim (0 : ι₁ → E) e k • Sum.elim a b k = x := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
    exact he
  have hz : ∑ k, (c k - Sum.elim (0 : ι₁ → E) e k) • Sum.elim a b k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hsum, ← hx', sub_self]
  have hce := Fintype.linearIndependent_iff.1 (linInd_of_gramInv hN) _ hz
  have hl : ∀ i, c (Sum.inl i) = 0 := fun i => by
    have h := hce (Sum.inl i)
    simpa using h
  have hx2 : x = ∑ j, c (Sum.inr j) • b j := by
    conv_lhs => rw [hx']
    rw [Fintype.sum_sum_type]
    simp [hl]
  rw [hx2]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range b)).smul_mem (⟨c (Sum.inr j), hc _⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq {p : PlF D} (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) := by
  unfold vP Formalism.MainNotions.S.Loc.HermSp.MMfam
  rw [hs]
  rfl

variable (u u' F0 what₂)

def CohInt : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ b, locF' Zd p F'₂ b ∈ lattice₂ D Zd.M p γ.lam}.Finite

def CohDG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) ∧
      (locH Zd p).Gdet (tLoc Zd p γ).f (locF' Zd p F'₂) (tLoc Zd p γ).T (tLoc Zd p γ).T' ≠ 0)}.Finite

variable {u u' F0 what₂}

theorem cohGen_of (hInt : CohInt Zd u u' F0 what₂) (hDG : CohDG Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CohGen Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  refine (((hInt hP γ Z F'₂ φ' hH).union (hDG hP γ Z F'₂ φ' hH)).union
    ((hGood hP γ Z F'₂ φ' hH).union (split_finite Zd))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hi, hdg⟩, hN, hs⟩ := hn
  have hsn : (Zd.M p).split = none := Option.not_isSome_iff_eq_none.1 hs
  apply hp
  have T1 := hH.2.2.2 p
  have sd := T1.1.1.1
  have frf := T1.1.1.2.1
  have frf' := T1.1.1.2.2.1
  have hI : ∀ x ∈ lattice₂ D Zd.M p γ.lam, ∀ y ∈ lattice₂ D Zd.M p γ.lam, (locH Zd p).h x y ∈ (Zd.M p).L.O :=
    fun x hx => (sd.2.2 x).1 hx
  have hv' : ∀ k, Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) k ∈ lattice₂ D Zd.M p γ.lam := by
    intro k
    cases k with
    | inl a => exact frf.1.1 a
    | inr b => exact hi b
  have hN' := hN
  rw [vP_eq Zd γ F'₂ hsn] at hN'
  have hv : ∀ k, vP Zd p γ F'₂ k ∈ lattice₂ D Zd.M p γ.lam := by
    rw [vP_eq Zd γ F'₂ hsn]
    exact hv'
  have hfr2 : (locH Zd p).IsFrame (lattice₂ D Zd.M p γ.lam) D.R.rS (locF' Zd p F'₂) (tLoc Zd p γ).T' :=
    ⟨Formalism.MainNotions.S.Loc.HermSp.CohU.prim_inr hN' hI hv', T1.2.2.1.1, T1.2.2.1.2, frf'.2.2.2.1, frf'.2.2.2.2⟩
  refine ⟨⟨sd, frf, hfr2, hdg.1, hdg.2, fun g hg => ?_⟩, ?_⟩
  · rw [hsn] at hg
    cases hg
  · exact Formalism.MainNotions.S.Loc.HermSp.CohU.prim_of_gramInv hN hI hv

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp



namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frame_fvec (t : TauC Y u u') (b : Fin (D.R.rS + 1)) : t.frame.fl.fvec b = t.lin ((X.Fu u').fvec b) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (mapLF t.lin (lf D (X.Fu u'))).fl.fvec b = _
  rw [mapLF_fl hγ, fvec_mapFlag]

theorem frame_z_eq_lin_zu (t : TauC Y u u') : t.frame.fl.z = t.lin (X.Fu u').z := by
  have := frame_fvec Y t (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using this

theorem mem_frameX (t : TauC Y u u') (x : (VS D).V) : x ∈ t.frame.fl.X ↔ t.lin.symm x ∈ (X.Fu u').X :=
  CorankRelation.mem_Xsp_mapLF t.lin t.rep.2.2.1 (lf D (X.Fu u')) x

theorem omp_terms (t1 t2 : TauC Y u u') (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u'))) (he : t2.lin = σ * t1.lin * s') :
    omp (X.Fu u) t2.frame.fl = σ (omp (X.Fu u) t1.frame.fl) ∧
    Dl (X.Fu u) t2.frame.fl (D.R.rS + 1) = Dl (X.Fu u) t1.frame.fl (D.R.rS + 1) ∧
    omp t2.frame.fl (X.Fu u) = σ (omp t1.frame.fl (X.Fu u)) ∧
    Dl t2.frame.fl (X.Fu u) (D.R.rS + 1) = Dl t1.frame.fl (X.Fu u) (D.R.rS + 1) := by
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  obtain ⟨hσi, -, -⟩ := hσ
  obtain ⟨hσi', hσf', hσz'⟩ := hσ'
  obtain ⟨-, hsf, hsz⟩ := hs'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hγ2 : σ * t1.lin * s' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := he ▸ t2.rep.2.2.1
  obtain ⟨o1, o2, o3, o4⟩ := omp_coset (X.Fu u) (X.Fu u') σ t1.lin s' hσi hσi' hγ1 hγ2 hσf' hσz' hsf hsz
  have hF1 : t1.frame.fl = mapFlag t1.lin hγ1 (X.Fu u') := mapLF_fl hγ1 (lf D (X.Fu u'))
  have hF2 : ∀ b, t2.frame.fl.fvec b = (mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')).fvec b := fun b => by
    rw [frame_fvec, fvec_mapFlag, he]
  have hrefl : ∀ b, (X.Fu u).fvec b = (X.Fu u).fvec b := fun b => rfl
  obtain ⟨k1, k2⟩ := omp_congr (F := X.Fu u) (G := X.Fu u) hrefl hF2
  obtain ⟨k3, k4⟩ := omp_congr (F := t2.frame.fl) (G := mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')) hF2 hrefl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact k1.trans (o1.trans (congrArg (fun G => σ (omp (X.Fu u) G)) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k2).trans (o2.trans (congrArg (fun G => (Zhat (X.Fu u) G).det) hF1.symm))
  · exact k3.trans (o3.trans (congrArg (fun G => σ (omp G (X.Fu u))) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k4).trans (o4.trans (congrArg (fun G => (Zhat G (X.Fu u)).det) hF1.symm))

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S.LocalSplitGroups

theorem densTh_of_ga {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : Formalism.L2.SG.CntLocal.LocSp D M} {u u' : D.what₂.Word}
    (hG : GaPlusTh M δ u u') : FCount.DensTh M δ L u u' :=
  densTh_of Formalism.L2.SG.Pf.density_congruence_holds hG

end Formalism.L2.SG.Pf.Coef
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem repG_holds : RepG u u' F0 what₂ := by
  intro hC γ Z hZ
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  obtain ⟨⟨hPD, hmk⟩, -⟩ := hex.choose_spec
  refine ⟨⟨hex.choose.2.1, hPD⟩, hrep.symm, hmk, ?_⟩
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hrow
  have hrel := (hEq ⟨hex.choose.2.1, hPD⟩ (Quot.out γ.cls)).1 (hmk.trans (Quot.out_eq γ.cls).symm)
  have e := Formalism.L2.SG.Pf.g_value_function _ _ _ _ _ hrel
  exact fun h0 => hG (e.symm.trans h0)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
