module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle213
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

namespace RowSB

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

theorem isHalf_add_of {e : AE D} {a b : ℕ} {x y : Mx D a b} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_nsmul_of {e : AE D} {a b : ℕ} {x : Mx D a b} (hx : IsHalf e x) (m : ℕ) : IsHalf e (m • x) := by
  intro i j
  rw [show (m • x) i j = m • x i j from rfl, nsmul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_of_add {e : AE D} {a b : ℕ} {x y : Mx D a b} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := by
  intro i j
  have h := hxy i j
  rw [Matrix.add_apply, mul_add, hy i j] at h
  exact add_right_cancel h

theorem isHalf_resT_symm_pair {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {e : AE D} {a : WO T A} {b : WO T L}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resT T).symm (a, b)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, hb]

theorem zrow_add' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x y : WO T L) :
    zrow β ζ (x + y) = zrow β ζ x + zrow β ζ y := by
  simp only [zrow, Matrix.vecMul_add, Pi.add_apply, map_add (f := _)]
  rw [← smul_add, ← Matrix.add_vecMul]
  rfl

def zrowHom {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : WO T L →+ (n → k) :=
  AddMonoidHom.mk' (zrow β ζ) (zrow_add' β ζ)

theorem zrow_nsmul' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (m : ℕ) (x : WO T L) :
    zrow β ζ (m • x) = m • zrow β ζ x :=
  map_nsmul (zrowHom β ζ) m x

theorem inDual_add' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η + ξ) := fun y hy => by
  rw [add_dotProduct]; exact add_mem (h y hy) (h' y hy)

theorem inDual_sub' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η - ξ) := fun y hy => by
  rw [sub_dotProduct]; exact sub_mem (h y hy) (h' y hy)

theorem inDual_nsmul' {Λ : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual Λ η) (m : ℕ) :
    InDual Λ (m • η) := fun y hy => by
  rw [smul_dotProduct]; exact nsmul_mem (h y hy) m

theorem rowFun_dualInd_ne_zero {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (h : rowFun β ζ (dualInd ΛT) y ≠ 0) :
    IsHalf p.e y ∧ InDual ΛT (zrow β ζ y) := by
  unfold rowFun dualInd at h
  by_cases hy : IsHalf p.e y
  · rw [if_pos hy] at h
    by_cases hd : InDual ΛT (zrow β ζ y)
    · exact ⟨hy, hd⟩
    · rw [if_neg hd] at h; exact absurd rfl h
  · rw [if_neg hy] at h; exact absurd rfl h

theorem rowFun_dualInd_eq_one {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) :
    rowFun β ζ (dualInd ΛT) y = 1 := by
  unfold rowFun dualInd
  rw [if_pos hy, if_pos hd]

theorem rowFun_dualInd_add_nsmul {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) (m : ℕ)
    (x : WO T L) : rowFun β ζ (dualInd ΛT) (x + m • y) = rowFun β ζ (dualInd ΛT) x := by
  have hz : zrow β ζ (x + m • y) = zrow β ζ x + m • zrow β ζ y := by
    rw [zrow_add', zrow_nsmul']
  have hm := inDual_nsmul' hd m
  unfold rowFun dualInd
  by_cases hx : IsHalf p.e x
  · rw [if_pos (isHalf_add_of hx (isHalf_nsmul_of hy m)), if_pos hx, hz]
    have hiff : InDual ΛT (zrow β ζ x + m • zrow β ζ y) ↔ InDual ΛT (zrow β ζ x) :=
      ⟨fun h => by simpa using inDual_sub' h hm, fun h => inDual_add' h hm⟩
    by_cases hd' : InDual ΛT (zrow β ζ x)
    · rw [if_pos hd', if_pos (hiff.2 hd')]
    · rw [if_neg hd', if_neg (fun h => hd' (hiff.1 h))]
  · rw [if_neg hx, if_neg (fun h => hx (isHalf_of_add h (isHalf_nsmul_of hy m)))]

theorem halfInd_eq_one_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t = 1 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

theorem halfInd_ne_zero_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

end RowSB

open RowSB

theorem isSBHalf_boxT_rowFun_dualInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (o.boxT T Φ (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT))) := by
  intro D k _ _ _ _ p n _ _ S A L T o ζ β LA LS LT ΛT H Φ hΦ
  obtain ⟨hsupp, m, hm, hinv, hlat⟩ := hΦ
  have hH : ∀ w, halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) w =
      halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) (o.resT T w).1 *
        rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => congrFun H w
  have hbox : ∀ w, o.boxT T Φ (rowFun β ζ (dualInd ΛT)) w =
      Φ (o.resT T w).1 * rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => rfl
  refine ⟨fun t ht => ?_, m, hm, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [hbox] at ht
    have h1 := hsupp _ (left_ne_zero_of_mul ht)
    have h2 := (rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)).1
    have := isHalf_resT_symm_pair o T h1 h2
    rwa [Prod.mk.eta, AddEquiv.symm_apply_apply] at this
  · have hu1 : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) u = 1 :=
      (halfInd_eq_one_iff' _ _).2 ⟨hu, hhu⟩
    rw [hH] at hu1
    have hA := (halfInd_ne_zero_iff' _ _).1 (left_ne_zero_of_mul_eq_one hu1)
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul_eq_one hu1)
    rw [hbox, hbox, map_add (f := _), map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      hinv _ hA.1 hA.2, rowFun_dualInd_add_nsmul β ζ ΛT hR.1 hR.2]
  · rw [hbox] at ht
    have hΦt := left_ne_zero_of_mul ht
    have h1 := hsupp _ hΦt
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)
    have hmt : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (m • t) = 1 := by
      rw [hH, map_nsmul, Prod.smul_fst, Prod.smul_snd,
        (halfInd_eq_one_iff' _ _).2 ⟨hlat _ hΦt, isHalf_nsmul_of h1 m⟩,
        rowFun_dualInd_eq_one β ζ ΛT (isHalf_nsmul_of hR.1 m) (by rw [zrow_nsmul']; exact inDual_nsmul' hR.2 m),
        one_mul]
    exact ((halfInd_eq_one_iff' _ _).1 hmt).1

end GlobalTheory.FinPl.ExtZero

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7}

theorem isHalf_mul {e : AE D} {l m n : ℕ} (M : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem isHalf_add {e : AE D} {m n : ℕ} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_resT_iff {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} (t : WO T S) :
    IsHalf e t ↔ IsHalf e (o.pA ⬝ t) ∧ IsHalf e (o.pB ⬝ t) := by
  refine ⟨fun h => ⟨isHalf_mul _ h, isHalf_mul _ h⟩, fun h => ?_⟩
  have := (o.resT T).symm_apply_apply t
  rw [← this, OrthDec.resT_symm_apply, OrthDec.resT_apply]
  exact isHalf_add (isHalf_mul _ h.1) (isHalf_mul _ h.2)

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_rat_pr {l m : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) : (rat M).map p.pr = M.map (p.pr.comp (incA D)) := by
  rw [rat, Matrix.map_map]; rfl

theorem sumFrame_b' {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (hs : IsSumFrame o ζ α α₀) :
    α₀.b' = fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) ((p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
        ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) := by
  set ι : D.host.E →+* k := p.pr.comp (incA D) with hι
  have hinj : Function.Injective ι := ι.injective
  set c := p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply hζ.2
    apply hinj
    rw [map_zero]; exact h
  set M := fromRows (α.b' * o.pA.map p.pr)
      (replicateRow (Fin 1) (c⁻¹ • ((fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* o.pB.map p.pr))) with hM
  have hcol : (fun i => p.pr (ratV (vecB o ζ) i)) = o.iB.map ι *ᵥ fun j => ι (ζ j) := by
    funext i
    simp only [ratV, vecB]
    exact (RingHom.map_mulVec ι o.iB ζ i)
  have hpA : o.pA.map p.pr = o.qA.map ι := map_rat_pr _
  have hpB : o.pB.map p.pr = o.qB.map ι := map_rat_pr _
  have hjA : o.jA.map p.pr = o.iA.map ι := map_rat_pr _
  have key : M * α₀.b = 1 := by
    rw [hs, hM, Matrix.fromRows_mul, Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_fromCols_eq_fromBlocks,
      ← Matrix.fromBlocks_one]
    have eA : o.qA.map ι * o.iA.map ι = 1 := by rw [← Matrix.map_mul, o.qA_iA]; simp
    have eAB : o.qA.map ι * o.iB.map ι = 0 := by rw [← Matrix.map_mul, o.qA_iB]; simp
    have eBA : o.qB.map ι * o.iA.map ι = 0 := by rw [← Matrix.map_mul, o.qB_iA]; simp
    have eB : o.qB.map ι * o.iB.map ι = 1 := by rw [← Matrix.map_mul, o.qB_iB]; simp
    have hu : (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) = fun j => ι ((star ζ ᵥ* L.gram) j) := rfl
    have hdot : (fun j => ι ((star ζ ᵥ* L.gram) j)) ⬝ᵥ (fun j => ι (ζ j)) = c := by
      rw [hc, Matrix.dotProduct_mulVec, ← RingHom.comp_apply, ← hι, RingHom.map_dotProduct]; rfl
    rw [hcol, hpA, hpB, hjA, hu, ← Matrix.smul_vecMul, Matrix.replicateRow_vecMul, Matrix.replicateCol_mulVec]
    congr 1
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eA, Matrix.one_mul, α.b'b]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qA.map ι), eAB, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eBA, Matrix.zero_mul, Matrix.mul_zero]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (o.qB.map ι), eB, Matrix.one_mul, Matrix.replicateRow_mul_replicateCol]
      ext i j
      simp only [Matrix.of_apply, smul_dotProduct, hdot, smul_eq_mul, inv_mul_cancel₀ hc0]
      fin_cases i; fin_cases j; simp
  calc α₀.b' = (M * α₀.b) * α₀.b' := by rw [key, Matrix.one_mul]
    _ = M := by rw [Matrix.mul_assoc, α₀.bb', Matrix.mul_one]

theorem rd_sumFrame {S A L T : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ)
    (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (t : WO T S) :
    rd β α₀ t = fromRows (rd β α (o.pA ⬝ t)) (replicateRow (Fin 1) (zrow β ζ (o.pB ⬝ t))) := by
  rw [rd, sumFrame_b' o ζ hζ α α₀ hs, Matrix.fromRows_mul, Matrix.fromRows_mul]
  congr 1
  · rw [rd, Matrix.map_mul, Matrix.mul_assoc α.b']
  · rw [← Matrix.replicateRow_vecMul, ← Matrix.replicateRow_vecMul]
    congr 1
    have hv : (fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* (o.pB ⬝ t)) i)) =
        (fun j => p.pr (incA D ((star ζ ᵥ* L.gram) j))) ᵥ* (o.pB ⬝ t).map p.pr := by
      funext i; exact RingHom.map_vecMul p.pr _ _ i
    rw [zrow, hv, Matrix.map_mul]
    simp only [Matrix.smul_vecMul, Matrix.vecMul_vecMul]

theorem extFun_tensRow (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D)
    (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (hζ : IsLineVec L ζ) (α : Frame p A n')
    (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n) (hs : IsSumFrame o ζ α α₀) (Ψ : Matrix n' n k → ℂ)
    (b : (n → k) → ℂ) :
    extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  funext t
  simp only [OrthDec.boxT, extFun, rowFun]
  rw [OrthDec.resT_apply]
  by_cases h : IsHalf p.e t
  · have h' := (isHalf_resT_iff o t).1 h
    rw [if_pos h, if_pos h'.1, if_pos h'.2, rd_sumFrame o ζ hζ α α₀ β hs t]
    rfl
  · rw [if_neg h]
    by_cases hA : IsHalf p.e (o.pA ⬝ t)
    · rw [if_neg fun hB => h ((isHalf_resT_iff o t).2 ⟨hA, hB⟩), mul_zero]
    · rw [if_neg hA, zero_mul]

end Frames

end GlobalTheory.FinPl.ExtZero

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero.SBBox

variable {D : D7}

theorem half_add {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u + t) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hu, ht]

theorem half_sub {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u - t) := by
  intro i j
  rw [Matrix.sub_apply, mul_sub, hu, ht]

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  induction N with
  | zero => intro i j; rw [zero_smul, Matrix.zero_apply, mul_zero]
  | succ N ih => rw [succ_nsmul]; exact half_add ih hu

theorem half_mul {m n l : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (x : Mx D n l) :
    IsHalf e (u * x : Mx D m l) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [← mul_assoc, hu]

theorem half_of_res {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {t : WO S T}
    (h1 : IsHalf e (o.resS T t).1) (h2 : IsHalf e (o.resS T t).2) : IsHalf e t := by
  rw [← (o.resS T).symm_apply_apply t]
  exact half_add (half_mul h1 _) (half_mul h2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem zcol_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y y' : WO L T) :
    zcol β ζ (y + y') = zcol β ζ y + zcol β ζ y' := by
  unfold zcol
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  rw [Matrix.add_mulVec, Pi.add_apply, map_add (f := _)]; rfl

theorem zcol_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : zcol β ζ 0 = 0 := by
  have := zcol_add β ζ 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem zcol_nsmul (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) (N : ℕ) :
    zcol β ζ (N • y) = N • zcol β ζ y := by
  induction N with
  | zero => rw [zero_smul, zero_smul, zcol_zero]
  | succ N ih => rw [succ_nsmul, succ_nsmul, zcol_add, ih]

theorem colFun_ne_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y : WO L T) :
    colFun β ζ (vecInd Λ) y ≠ 0 ↔ IsHalf p.e y ∧ zcol β ζ y ∈ Λ := by
  unfold colFun vecInd
  by_cases h : IsHalf p.e y <;> by_cases h' : zcol β ζ y ∈ Λ <;> simp [h, h']

theorem colFun_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y u : WO L T)
    (hu : IsHalf p.e u) (hu' : zcol β ζ u ∈ Λ) :
    colFun β ζ (vecInd Λ) (y + u) = colFun β ζ (vecInd Λ) y := by
  have h1 : IsHalf p.e (y + u) ↔ IsHalf p.e y :=
    ⟨fun h => by simpa using half_sub h hu, fun h => half_add h hu⟩
  have h2 : zcol β ζ (y + u) ∈ Λ ↔ zcol β ζ y ∈ Λ := by
    rw [zcol_add]; exact Λ.add_mem_iff_left hu'
  unfold colFun vecInd
  rw [propext h1, propext h2]

theorem halfInd_ne_zero {m l : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m l)) (t : Mx D m l) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  by_cases h : t ∈ Λ ∧ IsHalf e t <;> simp [h]

theorem isSBHalf_boxS_gen {S A : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n)
    (ΛA : AddSubgroup (WO A T)) (ΛS : AddSubgroup (WO S T)) (ΛT : Submodule 𝒪[k] (n → k))
    (hf : halfInd p.e ΛS = o.boxS T (halfInd p.e ΛA) (colFun β ζ (vecInd ΛT)))
    (Φ : WO A T → ℂ) (hΦ : IsSBHalf p.e ΛA Φ) :
    IsSBHalf p.e ΛS (o.boxS T Φ (colFun β ζ (vecInd ΛT))) := by
  have key : ∀ u : WO S T, (u ∈ ΛS ∧ IsHalf p.e u) ↔
      (((o.resS T u).1 ∈ ΛA ∧ IsHalf p.e (o.resS T u).1) ∧
        (IsHalf p.e (o.resS T u).2 ∧ zcol β ζ (o.resS T u).2 ∈ ΛT)) := by
    intro u
    rw [← halfInd_ne_zero, ← halfInd_ne_zero, ← colFun_ne_zero, hf, ← mul_ne_zero_iff]
    rfl
  obtain ⟨hs, N, hN, hinv, hsup⟩ := hΦ
  have hne : ∀ t, o.boxS T Φ (colFun β ζ (vecInd ΛT)) t ≠ 0 →
      Φ (o.resS T t).1 ≠ 0 ∧ IsHalf p.e (o.resS T t).2 ∧ zcol β ζ (o.resS T t).2 ∈ ΛT := by
    intro t ht
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 ht
    exact ⟨h1, (colFun_ne_zero β ζ ΛT _).1 h2⟩
  refine ⟨fun t ht => half_of_res o (hs _ (hne t ht).1) (hne t ht).2.1, N, hN, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (key u).1 ⟨hu, hu'⟩
    unfold OrthDec.boxS
    rw [map_add (f := _), map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hinv _ h1 h2,
      colFun_add β ζ ΛT _ _ (half_nsmul h3 N) (by rw [zcol_nsmul]; exact nsmul_mem h4 N)]
  · obtain ⟨h1, h2, h3⟩ := hne t ht
    refine ((key (N • t)).2 ?_).1
    rw [map_nsmul, Prod.smul_fst, Prod.smul_snd]
    exact ⟨⟨hsup _ h1, half_nsmul (hs _ h1) N⟩, half_nsmul h2 N, by rw [zcol_nsmul]; exact nsmul_mem h3 N⟩

theorem isSBHalf_boxS : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (o.boxS T Φ (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT))) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ o ζ β _ _ _ ΛT hf Φ hΦ => isSBHalf_boxS_gen o ζ β _ _ ΛT hf Φ hΦ

end GlobalTheory.FinPl.ExtZero.SBBox

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.PutIn

theorem datJ_cons : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι), i ∉ J → (∀ j ∈ J, (p i).e * (p j).e = 0) → GlobalTheory.FinPl.PutIn.datJ p α β Ψ (i :: J) = GlobalTheory.FinPl.PutIn.tens (p i).e (GlobalTheory.FinPl.PutIn.datJ p α β Ψ J) (extFun (α i) (β i) (Ψ i)) := by
  intro D k _ _ _ _ ι p n n' _ _ _ _ S T α β Ψ i J _ horth
  funext t
  have he : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact horth j hj
  have hii : (p i).e * (p i).e = (p i).e := (p i).split.1

  have hhalf : IsHalf (eSum p (i :: J)) t ↔ IsHalf (eSum p J) (t - (p i).e • t) := by
    rw [eSum_cons]
    constructor
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero]
      linear_combination this
    · intro h a b
      have := h a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_sub, ← mul_assoc, he, zero_mul, sub_zero] at this
      linear_combination this
  have hself : IsHalf (p i).e ((p i).e • t) := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hii]
  have hrdi : rd (α i) (β i) ((p i).e • t) = rd (α i) (β i) t := by
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, pr_e]
  have hrdj : ∀ j ∈ J, rd (α j) (β j) (t - (p i).e • t) = rd (α j) (β j) t := by
    intro j hj
    have h0 : (p j).pr (p i).e = 0 := pr_of_mul_eq_zero (p j) (by rw [mul_comm]; exact horth j hj)
    unfold rd
    congr 2
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_sub, h0]
  have hprod : (J.map fun j => Ψ j (rd (α j) (β j) (t - (p i).e • t))).prod = (J.map fun j => Ψ j (rd (α j) (β j) t)).prod := by
    congr 1
    exact List.map_congr_left fun j hj => by rw [hrdj j hj]
  simp only [datJ, tens, extFun, if_pos hself, hrdi, List.map_cons, List.prod_cons]
  by_cases h : IsHalf (eSum p J) (t - (p i).e • t)
  · rw [if_pos (hhalf.2 h), if_pos h, hprod, mul_comm]
  · rw [if_neg (fun h' => h (hhalf.1 h')), if_neg h, zero_mul]

end GlobalTheory.FinPl.PutIn
end
end
