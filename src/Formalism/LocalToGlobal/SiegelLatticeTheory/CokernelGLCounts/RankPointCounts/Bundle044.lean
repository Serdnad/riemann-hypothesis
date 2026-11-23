module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle041
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameEntry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle042
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type*} [CommRing K]

theorem sum_castLE {N l : ℕ} (h : l ≤ N) (f : Fin N → K) (hf : ∀ k : Fin N, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k' : Fin l, f (Fin.castLE h k') := by
  have hsub : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb h) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (fun k _ hk => ?_), Finset.sum_map]
  · rfl
  · apply hf
    by_contra hlt
    push_neg at hlt
    exact hk (Finset.mem_map.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_loUni_mul {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L)
    (hU : IsUpUni U) :
    (L * A * U).submatrix (Fin.castLE h) (Fin.castLE h) =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        U.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hin : ∀ m : Fin N, ∑ k, L (Fin.castLE h i) k * A k m =
      ∑ k' : Fin l, L (Fin.castLE h i) (Fin.castLE h k') * A (Fin.castLE h k') m := fun m =>
    sum_castLE h _ fun k hk => by
      rw [(hL _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using i.isLt) hk)), zero_mul]
  simp only [hin]
  exact sum_castLE h _ fun m hm => by
    rw [(hU _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using j.isLt) hm)), mul_zero]

theorem det_sub_loUni {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * A * U).submatrix (Fin.castLE h) (Fin.castLE h)).det = (A.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [submatrix_loUni_mul h L A U hL hU, Matrix.det_mul, Matrix.det_mul]
  have h1 : (L.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (L.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular OrderDual.toDual := by
      intro i j hij
      exact (hL _ _).1 (Fin.lt_iff_val_lt_val.2 (by
        simpa using Fin.lt_iff_val_lt_val.1 (OrderDual.toDual_lt_toDual.1 hij)))
    rw [Matrix.det_of_lowerTriangular _ hb]
    exact Finset.prod_eq_one fun i _ => (hL _ _).2 rfl
  have h2 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro i j hij
      exact (hU _ _).1 (Fin.lt_iff_val_lt_val.2 (by simpa using Fin.lt_iff_val_lt_val.1 hij))
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_one fun i _ => (hU _ _).2 rfl
  rw [h1, h2, one_mul, mul_one]

theorem det_sub_ZhatOM {r l : ℕ} (h : l ≤ r + 1) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ((ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ b : Fin l, ((-1 : K) ^ (r - b.val))) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * Matrix.diagonal fun b : Fin l => (-1 : K) ^ (r - b.val) := by
    ext a b
    simp [ZhatOM, Matrix.mul_diagonal, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

end Minors

theorem conjF_eq_star {D : Formalism.BasicNotions.D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem atPtG_holds {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : AtPtG u u' F0 what₂ := by
  intro γ w hat
  obtain ⟨F', -, hG, L, U, hL, hU, hZ⟩ := hat
  have N_eq : ∀ (l : ℕ) (h : l ≤ D.R.rS + 1),
      leadMinorE (ZhatL (lf D F0) F') l * star (leadMinorE (ZhatL (lf D F0) F') l) =
        Dmin w l * D.conjF (Dmin w l) := by
    intro l h
    have e1 : ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det =
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
          ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      rw [← det_sub_loUni h L (ptMat w) U hL hU, ← hZ]
      exact det_sub_ZhatOM h _
    have hss : (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun b _ => by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hst : star (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) =
        ∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val)) := by
      rw [star_prod]
      exact Finset.prod_congr rfl fun b _ => by rw [star_pow, star_neg, star_one]
    have hD : Dmin w l = ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold Dmin
      rw [dite_eq_left h]
    have hM : leadMinorE (ZhatL (lf D F0) F') l =
        ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold leadMinorE
      rw [dite_eq_left h]
    rw [hD, hM, conjF_eq_star, e1, star_mul', hst]
    linear_combination (-(((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det *
      star ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det)) * hss
  have key : Gval (lf D F0) F' = Gpt (D.mem u).A.T (D.mem u').A.T w := by
    rw [CntLocal.gz_eq]
    unfold CntLocal.GZ Gpt
    rw [N_eq (D.R.rS + 1) le_rfl, N_eq D.R.rS (Nat.le_succ _)]
  rw [← key]
  exact hG

theorem dnInDens_of {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hN : NormRepElig u u' F0 what₂) (hrows : IsRowReps D F0 what₂) :
    DnInDens u u' F0 what₂ := by
  intro γ w hγ
  have hex := hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  obtain ⟨⟨hPD, hmk⟩, hadm, -, -, -⟩ := hex.choose_spec
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := TermDef.Gt_mk hTF.1 ⟨_, hPD⟩
  have hGen := TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨_, hPD⟩
  rw [hmk] at hGt hGen
  refine ⟨γ.lam, γ.mem, hex.choose.2.1, ⟨hPD.1, hPD.2.1, ?_⟩, hadm, hGen.1 hγ.1.1, hPD.2.2, hz.symm⟩
  exact fun h => hγ.1.2 (hGt.trans h)

end Formalism.L2.SG.LsDatumB
end
end

section

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Tup

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {T T' : ℕ}

theorem fL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    fL M δ T T' p w τ O = hL M δ T T' p w O * kL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;> simp [fL, hL, kL, h1]

theorem gL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    gL M δ T T' p w τ O = hL M δ T T' p w O * eL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;>
    by_cases h2 : thL M δ T T' p w (repL M δ T T' p w O) = τ <;> simp [gL, hL, eL, h1, h2]

theorem eL_zero_or_one (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS))
    (O : Set (MatP D p)) : eL M δ T T' p w τ O = 0 ∨ eL M δ T T' p w τ O = 1 := by
  unfold eL
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem base_factors {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {θ : Option ((M p).Cls D.R.rS)}
    (hf : ∀ τ O, fL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0)
    (hg : ∀ τ O, gL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0) :
    hL M δ T T' p w (x0L M δ T T' p w) = 1 ∧ kL M δ T T' p w θ (x0L M δ T T' p w) = 1 ∧
      eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
  have g1 := hg θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, gL_eq] at g1
  have he : eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
    rcases eL_zero_or_one (M := M) (δ := δ) (T := T) (T' := T') p w θ (x0L M δ T T' p w) with h | h
    · rw [h, mul_zero] at g1
      exact absurd g1 zero_ne_one
    · exact h
  rw [he, mul_one] at g1
  have f1 := hf θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, fL_eq, g1, one_mul] at f1
  exact ⟨g1, f1, he⟩

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem partnerTupleSum_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : PartnerCount M δ u u' F0 what₂) : PartnerTupleSum M δ u u' F0 what₂ := by
  intro γ w hγ w' hG' hk
  obtain ⟨hres, hcnt⟩ := hN γ w hγ w' hG' hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w' hG'
  have hRf := hR γ w hγ
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p) = 1 ∧
        kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.1⟩
  have hfunc : (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
        PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w') =
      fun γ' => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) := by
    funext γ'
    rw [hC γ'.1 w' γ'.2.1.2, γ'.2.2]
  rw [hfunc]
  have hv : (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) := by
    rw [← finprod_mul_distrib]
    · exact finprod_congr fun p => fL_eq p w' _ _
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).1
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).2
  rw [hv]
  exact (hcnt x).mul_left _

theorem fiberTupleSum_of {L : CntLocal.LocSp D M} {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : FiberCount M δ L u u' F0 what₂) : FiberTupleSum M δ L u u' F0 what₂ := by
  intro nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  obtain ⟨hres, hcnt⟩ := hN nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w hG
  have hRf := hR γ₀ w₀ hγ₀
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p) = 1 ∧
        eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ₀ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.2⟩
  have hfunc : (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
      (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
        (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w) =
      fun γ => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ)) := by
    funext γ
    rw [hC γ.1 w γ.2.1.1, γ.2.2]
    ring
  rw [hfunc]
  have hv : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
      (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) := by
    rw [show (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
        (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) from by
      rw [← finprod_mul_distrib]
      · exact finprod_congr fun p => gL_eq p w _ _
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).1
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).2]
    ring
  rw [hv]
  exact (hcnt x).mul_left _

end Tup

end Formalism.L2.SG.LsDatumB
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix IsDedekindDomain
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_locP {W : Type*} [AddCommGroup W] [Module (𝓞 D.host.E) W] (p : Ideal (𝓞 D.host.E)) [p.IsPrime]
    (L : Submodule (𝓞 D.host.E) W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ t : 𝓞 D.host.E, t ∉ p ∧ t • x ∈ L := Iff.rfl

theorem smul_O (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : 𝓞 D.host.E) (x : (VS D).V) : s (t • x) = t • s x := by
  rw [← algebraMap_smul D.host.E t x, LinearEquiv.map_smul, algebraMap_smul]

theorem conv_at {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (P : HeightOneSpectrum (𝓞 D.host.E)) (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  congr 2
  ext v
  simp [hc1 hgP]

theorem int_at {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hc : IsFixedConv Λ (Lat.gS D) F) (hz : F.fl.z ∈ Λ) (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hs : ∀ v ∈ Λ, s v ∈ Λ)
    (uu : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (huu : IsUpUni uu)
    (hfr : ∀ b, s (F.fl.fvec b) = ∑ c, uu c b • F.fl.fvec c) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hgP : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (c i : Fin (D.R.rS + 1)) :
    ∃ t : 𝓞 D.host.E, t ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (t : D.host.E) * uu c i = o := by
  have hP := P.isPrime
  have hconv := conv_at F Λ hc P hgP
  rcases lt_trichotomy c i with hci | hci | hci
  · have hcr : (c : ℕ) < D.R.rS := lt_of_lt_of_le hci (Nat.lt_succ_iff.1 i.2)
    obtain ⟨a, rfl⟩ : ∃ a : Fin D.R.rS, c = Fin.castSucc a := ⟨⟨c, hcr⟩, rfl⟩
    have hXmem : ∀ y : Fin D.R.rS → D.host.E, (∑ a, y a • F.fl.e a) ∈ Λ → (∑ a, y a • F.fl.e a) ∈ XLam Λ F := by
      intro y hy
      refine Submodule.mem_inf.2 ⟨hy, ?_⟩
      show (∑ a, y a • F.fl.e a) ∈ F.fl.X
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    induction i using Fin.lastCases with
    | last =>
      have hv : s F.fl.z - F.fl.z = ∑ a', uu (Fin.castSucc a') (Fin.last _) • F.fl.e a' := by
        have h := hfr (Fin.last _)
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_last] at h
        rw [h, (huu _ _).2 rfl, one_smul, add_sub_cancel_right]
      have hmem : s F.fl.z - F.fl.z ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact Λ.sub_mem (hs _ hz) hz
      have hloc : s F.fl.z - F.fl.z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t, ht, htv⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t • (s F.fl.z - F.fl.z) = ∑ a', ((t : D.host.E) * uu (Fin.castSucc a') (Fin.last _)) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl htv _ hv2 a
      exact ⟨t, ht, o, ho.symm⟩
    | cast i' =>
      have he : F.fl.e i' ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
        rw [hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨i', rfl⟩⟩
      obtain ⟨t1, ht1, ht1e⟩ := (mem_locP P.asIdeal _ _).1 he
      have hv : s (t1 • F.fl.e i') = ∑ a', ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i')) • F.fl.e a' := by
        have h := hfr (Fin.castSucc i')
        rw [sum_fvec] at h
        simp only [FlagG.fvec, Fin.snoc_castSucc] at h
        rw [smul_O, h, (huu _ _).1 (Fin.castSucc_lt_last i'), zero_smul, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t1, smul_smul]
      have hmem : s (t1 • F.fl.e i') ∈ XLam Λ F := by
        rw [hv]
        apply hXmem
        rw [← hv]
        exact hs _ (Submodule.mem_inf.1 ht1e).1
      have hloc : s (t1 • F.fl.e i') ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range F.fl.e)) := by
        rw [← hconv]
        exact ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hmem⟩
      obtain ⟨t2, ht2, ht2v⟩ := (mem_locP P.asIdeal _ _).1 hloc
      have hv2 : t2 • s (t1 • F.fl.e i') =
          ∑ a', ((t2 : D.host.E) * ((t1 : D.host.E) * uu (Fin.castSucc a') (Fin.castSucc i'))) • F.fl.e a' := by
        rw [hv, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [← algebraMap_smul D.host.E t2, smul_smul]
      obtain ⟨o, ho⟩ := coef_spanO F.fl ht2v _ hv2 a
      refine ⟨t2 * t1, fun h => (hP.mem_or_mem h).elim ht2 ht1, o, ?_⟩
      rw [ho]
      push_cast
      ring
  · subst hci
    exact ⟨1, P.asIdeal.primeCompl.one_mem, 1, by rw [(huu c c).2 rfl]; simp⟩
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by rw [(huu c i).1 hci]; simp⟩

end Formalism.L2.SG.Pf.ZsVolLat

end
end
