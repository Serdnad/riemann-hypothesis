module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zhat_int {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) :
    ∃ FinalForm : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      Zhat F F' = FinalForm.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  have hmem : ∀ a b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = Zhat F F' a b := by
    intro a b
    have hx : F'.fvec b ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
      rw [show Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ from hun]
      exact hF' b
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
    have h1 := (Submodule.mem_iInf _).mp hx (F.fvec a)
    have h2 := (Submodule.mem_iInf _).mp h1 (hF a)
    rw [Submodule.mem_comap] at h2
    exact Submodule.mem_one.mp h2
  choose FinalForm hZo using hmem
  exact ⟨Matrix.of FinalForm, by ext a b; exact (hZo a b).symm⟩

theorem yv_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (n : ℕ) {T' : D.host.E} (F : FlagG (VS D) D.R.rS (n : D.host.E)) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) : NormalVectorPairings.yv F F' ∈ Λ := by
  obtain ⟨FinalForm, hZo⟩ := zhat_int hun F F' hF hF'
  have hadj : (Zhat F F').adjugate = FinalForm.adjugate.map (algebraMap (𝓞 D.host.E) D.host.E) := by
    rw [hZo]
    exact (RingHom.map_adjugate _ _).symm
  have hD : Dl F F' (D.R.rS + 1) = algebraMap (𝓞 D.host.E) D.host.E
      ((FinalForm.submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl)).det) := by
    unfold Dl leadMinorE
    rw [dite_eq_left le_rfl, hZo, Matrix.submatrix_map, RingHom.map_det]
    rfl
  unfold NormalVectorPairings.yv NormalVectorPairings.omp
  refine Λ.add_mem ?_ ?_
  · rw [Nat.cast_smul_eq_nsmul]
    refine nsmul_mem (Λ.sum_mem fun b _ => ?_) n
    rw [hadj, Matrix.map_apply, algebraMap_smul]
    exact Λ.smul_mem _ (hF' b)
  · rw [hD, algebraMap_smul]
    have hz : F.z = F.fvec (Fin.last _) := by simp [FlagG.fvec]
    rw [hz]
    exact Λ.smul_mem _ (hF _)

theorem yv_orth_X {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') :
    ∀ x ∈ F.X, brS (VS D) (NormalVectorPairings.yv F F') x = 0 := by
  have key : ∀ a : Fin D.R.rS, (VS D).hT (F.e a) (NormalVectorPairings.yv F F') = 0 := by
    intro a
    have hz : ∀ b, (VS D).hT (F.e a) (F'.fvec b) = Zhat F F' a.castSucc b := by
      intro b
      simp [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc]
    have hm := congrFun (congrFun (Matrix.mul_adjugate (Zhat F F')) a.castSucc) (Fin.last _)
    rw [Matrix.mul_apply] at hm
    simp only [Matrix.smul_apply, Matrix.one_apply, Fin.castSucc_ne_last, if_false, smul_zero] at hm
    unfold NormalVectorPairings.yv NormalVectorPairings.omp

    rw [map_add (f := _), map_smul, map_smul, F.z_orth a, smul_zero, add_zero, map_sum]
    simp only [map_smul, smul_eq_mul, hz]
    rw [show ∑ b, (Zhat F F').adjugate b (Fin.last D.R.rS) * Zhat F F' a.castSucc b =
        ∑ b, Zhat F F' a.castSucc b * (Zhat F F').adjugate b (Fin.last D.R.rS) from
      Finset.sum_congr rfl fun b _ => mul_comm _ _, hm, mul_zero]
  intro x hx
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y (NormalVectorPairings.yv F F') = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    exact key a
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem X_iso {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : ∀ x ∈ F.X, ∀ x' ∈ F.X, brS (VS D) x x' = 0 := by
  intro x hx x' hx'
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨b, rfl⟩
    refine Submodule.span_induction (p := fun y _ => (VS D).hT (F.e b) y = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact F.e_iso b a
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro c y _ hy
      simp [hy]
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem abs_norm_TG (n : ℕ) (g : D.host.E) :
    |((Algebra.norm ℚ ((n : D.host.E) * g) : ℚ) : ℝ)| =
      (n : ℝ) ^ (2 * D.R.f) * (∏ w : InfinitePlace D.host.E, w g) ^ 2 := by
  have hc : ∀ w : InfinitePlace D.host.E, w.mult = 2 := by
    intro w
    have hnr : ¬ w.IsReal := by
      intro hw
      have hr := InfinitePlace.isReal_iff.mp hw
      have h2 : starRingEnd ℂ (w.embedding D.host.sqq) = w.embedding D.host.sqq :=
        RingHom.congr_fun hr _
      have h1 : w.embedding D.host.sqq ^ 2 = w.embedding (-(D.host.q : D.host.E)) := by
        rw [← map_pow, D.host.sqq_sq]
      have h3 := Complex.conj_eq_iff_re.mp h2
      rw [← h3, map_neg, map_natCast] at h1
      have h4 := congrArg Complex.re h1
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re, Complex.natCast_re] at h4
      have hq0 : 0 < D.host.q := by have := D.host.qd_big.1; omega
      have hq : (0 : ℝ) < D.host.q := by exact_mod_cast hq0
      nlinarith [mul_self_nonneg (w.embedding D.host.sqq).re]
    simp [InfinitePlace.mult, hnr]
  have hprod := InfinitePlace.prod_eq_abs_norm g
  simp only [hc, Finset.prod_pow] at hprod
  rw [← map_natCast (algebraMap ℚ D.host.E) n, map_mul, Algebra.norm_algebraMap,
    Formalism.MainNotions.BridgeLemma.szf_finrankE D, hprod]
  push_cast
  rw [abs_mul, abs_pow, Nat.abs_cast]

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

section

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal PI.SchurPlaces.LeviLA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frameAt (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
      (X.wfr u v) :=
  { ee := fun a b => by
      simp only [HidaSetting.eR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ee, map_zero]
    ef := fun a b => by
      simp only [HidaSetting.eR, HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ef]; split_ifs <;> simp
    ff := fun a b => by
      simp only [HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ff, map_zero]
    ez := fun a => by
      simp only [HidaSetting.eR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).1, map_zero]
    fz := fun a => by
      simp only [HidaSetting.fR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2, map_zero]
    ew := fun a b => ((X.wfr_perp u v b).1 a).1
    fw := fun a b => ((X.wfr_perp u v b).1 a).2
    zw := fun b => (X.wfr_perp u v b).2
    ww := X.wfr_on u v
    zz := by
      simp only [HidaSetting.zR]
      rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.zu_norm, map_neg, map_natCast]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
    card := by
      have h1 := X.n_eq; have h2 := D.R.r_eq; have h3 := D.R.rS_two; omega }

theorem wfrSpan : WfrSpan := by
  intro D X u v y hef hz
  exact perp_efz (frameAt X u v) y hef hz

theorem leviTens : LeviTens := by
  intro D X u h hh x
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (h v)) := hh
  choose V hVu hVe hVf hVz hVw hVN using fun v =>
    levi_place (frameAt X u v) ((h v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
      (h v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hn : ∀ v, uMat ((s0⁻¹ * h) v) =
      (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        uMat (h v) := fun v => rfl
  have hs0S : s0 ∈ X.SinfU u := by
    intro v
    refine ⟨fun a => ?_, ?_⟩
    · rw [hs0, sub_mulVec, one_mulVec, hVe v a, sub_self]; exact zero_mem _
    · rw [hs0, sub_mulVec, one_mulVec, hVz v, sub_self]; exact zero_mem _
  have hnN : s0⁻¹ * h ∈ X.NinfU u := fun v => by rw [show uMat ((s0⁻¹ * h) v) = _ from hn v]; exact hVN v
  have hnS : s0⁻¹ * h ∈ X.SinfU u := fun v => (hnN v).1
  have hsplit : h = s0 * (s0⁻¹ * h) := by rw [mul_inv_cancel_left]
  have hpi : X.piU u h = X.piU u s0 := by
    rw [hsplit, (X.piU_rep u).2.1 s0 hs0S _ hnS, (X.piU_rep u).2.2.2.1 _ hnN, mul_one]
  have hs0H : s0 ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp; subst hp; exact hVz v
  have hmat : ∀ v, matW X.B.I (X.wfr u v) v s0 = matW X.B.I (X.wfr u v) v h := fun v => by
    ext a b; exact hVw v a b
  rw [hpi, X.tensU_equiv u s0 hs0H x]
  simp only [hmat]

end PI.SchurPlaces
end
end

section

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_add_r {n : ℕ} (ε : Fin n → Bool) (a y z : Fin n → ℂ) : hJ ε a (y + z) = hJ ε a y + hJ ε a z := by
  unfold hJ
  rw [Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (a y : Fin n → ℂ) (c : ℂ) : hJ ε a (c • y) = c * hJ ε a y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero_r {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℂ) : hJ ε a 0 = 0 := by
  unfold hJ
  rw [Matrix.mulVec_zero, dotProduct_zero]

theorem hJ_sum_r {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (a : Fin n → ℂ) (c : ι → ℂ)
    (y : ι → Fin n → ℂ) : hJ ε a (∑ i, c i • y i) = ∑ i, c i * hJ ε a (y i) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section Pts

variable {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

abbrev psiV (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem psiV_add (p q : (VS D).V) : psiV X v (p + q) = psiV X v p + psiV X v q := by
  simp only [psiV, rv]
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [HidaSetting.crd, crdOf]

theorem psiV_smul (c : D.host.E) (p : (VS D).V) : psiV X v (c • p) = embS D (X.pl v) c • psiV X v p := by
  unfold psiV rv HidaSetting.crd crdOf
  rw [← Matrix.mulVec_smul]; congr 1; funext i
  simp [X.φ_eq]

def psiHom : (VS D).V →+ (Fin X.B.I.n → ℂ) := AddMonoidHom.mk' (psiV X v) (psiV_add X v)

theorem psiV_sum {ι : Type} (J : Finset ι) (f : ι → (VS D).V) : psiV X v (∑ i ∈ J, f i) = ∑ i ∈ J, psiV X v (f i) := by exact map_sum (psiHom X v) f J

theorem psiV_zero : psiV X v 0 = 0 := by exact map_zero (psiHom X v)

theorem hJ_psiV (p q : (VS D).V) :
    hJ (X.B.I.ε v) (psiV X v p) (psiV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

theorem psiV_span (y : Fin X.B.I.n → ℂ) : ∃ c : Fin X.B.I.n → ℂ, y = ∑ i, c i • psiV X v (X.bas i) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  refine ⟨X.B.I.P v *ᵥ y, ?_⟩
  have h1 : ∀ i, psiV X v (X.bas i) = (X.B.I.P v)⁻¹ *ᵥ (fun k => if i = k then (1 : ℂ) else 0) := by
    intro i
    unfold psiV rv HidaSetting.crd crdOf
    congr 1
    funext k
    by_cases h : i = k <;> simp [h]
  simp only [h1, ← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu,
    Matrix.one_mulVec]

theorem cplx_comb {ι : Type} [Fintype ι] (g : ι → (VS D).V) (U : Submodule D.host.E (VS D).V) (c : ι → ℂ)
    (hc : ∀ p ∈ U, ∑ i, c i * embS D (X.pl v) ((VS D).hT p (g i)) = 0) :
    ∑ i, c i • psiV X v (g i) ∈ spanAt X v (perpS (VS D) U ⊓ Submodule.span D.host.E (Set.range g)) := by
  letI : Algebra D.host.E ℂ := (embS D (X.pl v)).toAlgebra
  let b := Module.Basis.ofVectorSpace D.host.E ℂ
  let J := Finset.univ.biUnion (fun i : ι => (b.repr (c i)).support)
  let s : Module.Basis.ofVectorSpaceIndex D.host.E ℂ → ι → D.host.E := fun j i => b.repr (c i) j
  let w : Module.Basis.ofVectorSpaceIndex D.host.E ℂ → (VS D).V := fun j => ∑ i, s j i • g i
  have hw : ∀ j, w j ∈ perpS (VS D) U ⊓ Submodule.span D.host.E (Set.range g) := by
    intro j
    refine ⟨fun p hp => ?_,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
    have h1 : ∑ i, (VS D).hT p (g i) • c i = 0 := by
      rw [← hc p hp]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    have h2 := congrArg (fun z => b.repr z j) h1

    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    show (VS D).hT p (w j) = 0

    simp only [w, map_sum, map_smul, smul_eq_mul]
    rw [← h2]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [s]; ring
  have hc' : ∀ i, c i = ∑ j ∈ J, embS D (X.pl v) (s j i) * b j := by
    intro i
    conv_lhs => rw [← b.linearCombination_repr (c i)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (b.repr (c i)).support) (Finset.mem_univ i))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · intro j _; simp
  have hsum : ∑ i, c i • psiV X v (g i) = ∑ j ∈ J, b j • psiV X v (w j) := by
    simp only [w, psiV_sum, psiV_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc' i, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w j, hw j, rfl⟩)

theorem spanAt_mono {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') : spanAt X v U ≤ spanAt X v U' := by
  unfold spanAt
  exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr h))

theorem cplx_part1 {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) (V0 : Submodule D.host.E (VS D).V)
    (hsup : perpS (VS D) V0 ⊔ F.X = F.XplusPerp) (y : Fin X.B.I.n → ℂ)
    (hy : ∀ p ∈ F.Xplus, hJ (X.B.I.ε v) (psiV X v p) y = 0) :
    ∃ x ∈ spanAt X v F.X, ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) (y - x) = 0 := by
  obtain ⟨c, rfl⟩ := psiV_span X v y
  have hmem := cplx_comb X v X.bas F.Xplus c (fun p hp => by
    rw [← hy p hp, hJ_sum_r]
    exact Finset.sum_congr rfl fun i _ => by rw [hJ_psiV])
  have hmem' := spanAt_mono X v (inf_le_left.trans (le_of_eq rfl) :
    perpS (VS D) F.Xplus ⊓ Submodule.span D.host.E (Set.range X.bas) ≤ F.XplusPerp) hmem
  rw [← hsup] at hmem'
  refine Submodule.span_induction (p := fun y _ => ∃ x ∈ spanAt X v F.X,
      ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) (y - x) = 0) ?_ ?_ ?_ ?_ hmem'
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.1 hw
    refine ⟨psiV X v x, Submodule.subset_span ⟨x, hx, rfl⟩, fun p hp => ?_⟩
    show hJ (X.B.I.ε v) (psiV X v p) (psiV X v (a + x) - psiV X v x) = 0
    rw [psiV_add, add_sub_cancel_right, hJ_psiV, ha p hp, map_zero]
  · exact ⟨0, Submodule.zero_mem _, fun p _ => by rw [sub_zero, hJ_zero_r]⟩
  · rintro y1 y2 - - ⟨x1, hx1, h1⟩ ⟨x2, hx2, h2⟩
    refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, fun p hp => ?_⟩
    rw [show y1 + y2 - (x1 + x2) = (y1 - x1) + (y2 - x2) by abel, hJ_add_r, h1 p hp, h2 p hp, add_zero]
  · rintro a y1 - ⟨x1, hx1, h1⟩
    refine ⟨a • x1, Submodule.smul_mem _ _ hx1, fun p hp => ?_⟩
    rw [← smul_sub, hJ_smul_r, h1 p hp, mul_zero]

theorem cplx_part3 {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) (V0 I : Submodule D.host.E (VS D).V)
    (hinf : perpS (VS D) V0 ⊓ F.X = I) (y : Fin X.B.I.n → ℂ) (hyX : y ∈ spanAt X v F.X)
    (hy : ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) y = 0) : y ∈ spanAt X v I := by
  have hle : spanAt X v F.X ≤ Submodule.span ℂ (Set.range fun a => psiV X v (F.e a)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, hp, rfl⟩
    refine Submodule.span_induction (p := fun p _ => psiV X v p ∈
      Submodule.span ℂ (Set.range fun a => psiV X v (F.e a))) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a, rfl⟩; exact Submodule.subset_span ⟨a, rfl⟩
    · rw [psiV_zero]; exact Submodule.zero_mem _
    · intro x1 x2 _ _ h1 h2; rw [psiV_add]; exact Submodule.add_mem _ h1 h2
    · intro a x1 _ h1; rw [psiV_smul]; exact Submodule.smul_mem _ _ h1
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hyX)
  have hmem := cplx_comb X v F.e V0 c (fun p hp => by
    rw [← hy p hp, hJ_sum_r]
    exact Finset.sum_congr rfl fun i _ => by rw [hJ_psiV])
  rw [← hinf]
  exact hmem

end Pts

def NFRat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊓ (lf D (X.Fu u)).fl.X = Isp (lf D (X.Fu u)).fl (frq X q).fl ∧
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊔ (lf D (X.Fu u)).fl.X = (lf D (X.Fu u)).fl.XplusPerp ∧
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊔ (frq X q).fl.X = (frq X q).fl.XplusPerp

theorem cplxNF_of (h : NFRat) : CplxNF := by
  intro D X u u' Λ Λ' q hrel hG v
  obtain ⟨h1, h2, h3⟩ := h D X u u' Λ Λ' q hrel hG
  exact ⟨cplx_part1 X v _ _ h2, cplx_part1 X v _ _ h3, cplx_part3 X v _ _ _ h1⟩

end PI.SchurPlaces
end
end
