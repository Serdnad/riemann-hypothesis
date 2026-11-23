module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependenceAlgebra
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle048
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HsymmShiftProof

open NumericalSegreProof

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [Fintype K] [DecidableEq K] in
theorem length_rootList {n : ℕ} (x : Fin n → K → ℤ) (α : Fin n → ℕ) :
    (rootList x α).length = ∑ i, α i := by
  unfold rootList
  simp [List.length_flatMap, Fin.sum_univ_def]

theorem cons_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F W ((c + c') :: l) = intNumL F W (c :: l) + intNumL F W (c' :: l) := by
  have key : ∀ e, Function.update (c :: l).get (0 : Fin (l.length + 1)) e = (e :: l).get := by
    intro e
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := FieldNumbers.IntNumAdd.full.{u} F K ι W hW.multiHomog hW.relevant (l.length + 1) hd
    ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

theorem replicate_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W)
    (z s : K → ℤ) : ∀ (n : ℕ) (L : List (K → ℤ)),
    FieldNumbers.relDim W = ((n + L.length : ℕ) : WithBot (WithTop ℤ)) →
    intNumL F W (List.replicate n (z + s) ++ L) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) *
        intNumL F W (List.replicate (n - k) z ++ List.replicate k s ++ L)
  | 0, L, _ => by simp
  | n + 1, L, hd => by
    have hd' : ∀ c : K → ℤ,
        FieldNumbers.relDim W = ((n + (c :: L).length : ℕ) : WithBot (WithTop ℤ)) := by
      intro c
      rw [hd, List.length_cons, Nat.add_right_comm, Nat.add_assoc]
    rw [List.replicate_succ, List.cons_append,
      cons_add W hW _ (by rw [hd, List.length_append, List.length_replicate]; congr 1; omega) z s,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s))).symm,
      intNumL_perm F W (List.perm_middle (l₁ := List.replicate n (z + s)) (a := s)).symm,
      replicate_add W hW z s n (z :: L) (hd' z), replicate_add W hW z s n (s :: L) (hd' s),
      ProjectiveBundleNumbers.sum_choose_succ n (fun k => intNumL F W (List.replicate (n + 1 - k) z ++ List.replicate k s ++ L))]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      congr 1
      refine intNumL_perm F W ?_
      rw [show n + 1 - k = (n - k) + 1 by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]
      exact List.Perm.append_left _ List.perm_middle
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [show n + 1 - (k + 1) = n - k by omega, List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

def H (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ) (L : List (K → ℤ)) : ℤ :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple n c, intNumL F W (rootList x α ++ L)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_zero (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (L : List (K → ℤ)) :
    H W x 0 L = intNumL F W L := by
  simp [H, Finset.Nat.antidiagonalTuple_zero_right, rootList_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_one (W : Ideal (MRing ι F)) (x : Fin 1 → K → ℤ) (c : ℕ) (L : List (K → ℤ)) :
    H W x c L = intNumL F W (List.replicate c (x 0) ++ L) := by
  unfold H
  rw [Finset.Nat.antidiagonalTuple_one, Finset.sum_singleton, rootList_succ]
  simp [rootList]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_perm (W : Ideal (MRing ι F)) {n : ℕ} (x : Fin n → K → ℤ) (c : ℕ)
    {L L' : List (K → ℤ)} (h : L.Perm L') : H W x c L = H W x c L' :=
  Finset.sum_congr rfl fun _ _ => intNumL_perm F W (h.append_left _)

theorem H_add (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) {n : ℕ} (x : Fin n → K → ℤ)
    (c : ℕ) (L : List (K → ℤ))
    (hd : FieldNumbers.relDim W = ((c + 1 + L.length : ℕ) : WithBot (WithTop ℤ))) (a b : K → ℤ) :
    H W x c ((a + b) :: L) = H W x c (a :: L) + H W x c (b :: L) := by
  unfold H
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlen : (rootList x α).length = c := by
    rw [length_rootList]
    exact Finset.Nat.mem_antidiagonalTuple.mp hα
  rw [intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a + b)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := a)),
    intNumL_perm F W (List.perm_middle (l₁ := rootList x α) (a := b))]
  exact cons_add W hW _
    (by rw [hd, List.length_append, hlen, show c + 1 + L.length = c + L.length + 1 by omega]) a b


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem H_succ (W : Ideal (MRing ι F)) {i : ℕ} (x : Fin (i + 1) → K → ℤ) (c : ℕ)
    (L : List (K → ℤ)) :
    H W x (c + 1) L = H W (fun j => x (Fin.castSucc j)) (c + 1) L + H W x c (x (Fin.last i) :: L) := by
  unfold H
  rw [sum_antidiagonalTuple_succ]
  congr 1
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [rootList_snoc_zero]
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [rootList_update_last, List.append_assoc, List.singleton_append]

theorem sum_choose_pascal (M r : ℕ) (f : ℕ → ℤ) :
    ∑ k ∈ Finset.range (r + 1 + 1), ((M + 1).choose k : ℤ) * f k =
      ∑ k ∈ Finset.range (r + 1 + 1), (M.choose k : ℤ) * f k +
        ∑ k ∈ Finset.range (r + 1), (M.choose k : ℤ) * f (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (M.choose k : ℤ) * f k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  ring

theorem main (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (s : K → ℤ) :
    ∀ (N : ℕ) (x : Fin (N + 1) → K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
    FieldNumbers.relDim W = ((r + Y.length : ℕ) : WithBot (WithTop ℤ)) →
    H W (fun i => x i + s) r Y =
      ∑ k ∈ Finset.range (r + 1), ((N + r).choose k : ℤ) * H W x (r - k) (List.replicate k s ++ Y)
  | 0, x, r, Y, hd => by
    rw [H_one, replicate_add W hW (x 0) s r Y hd]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [H_one, List.append_assoc, show 0 + r = r from Nat.zero_add r]
  | N + 1, x, r, Y, hd => by
    induction r generalizing Y with
    | zero => simp [H_zero]
    | succ r ih =>
      have e1 := main W hW s N (fun j => x (Fin.castSucc j)) (r + 1) Y hd
      have e2 := ih (x (Fin.last (N + 1)) :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have e3 := ih (s :: Y)
        (by rw [hd, List.length_cons, show r + 1 + Y.length = r + (Y.length + 1) by omega])
      have hadd := H_add W hW (fun i => x i + s) r Y hd (x (Fin.last (N + 1))) s
      have hAB : ∑ k ∈ Finset.range (r + 1 + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - k) (List.replicate k s ++ Y) =
          ∑ k ∈ Finset.range (r + 1 + 1), ((N + (r + 1)).choose k : ℤ) *
              H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y) +
            ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
              H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y) := by
        rw [show N + (r + 1) = N + 1 + r by omega, Finset.sum_range_succ,
          Finset.sum_range_succ (fun k => ((N + 1 + r).choose k : ℤ) *
            H W (fun j => x (Fin.castSucc j)) (r + 1 - k) (List.replicate k s ++ Y)),
          Nat.sub_self, H_zero, H_zero,
          add_right_comm _ _ (∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ x (Fin.last (N + 1)) :: Y)),
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [show r + 1 - k = (r - k) + 1 by omega, H_succ W x (r - k) (List.replicate k s ++ Y),
          ← mul_add, H_perm W x (r - k) (List.perm_middle (l₁ := List.replicate k s)).symm]
      have hC : ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r + 1 - (k + 1)) (List.replicate (k + 1) s ++ Y) =
          ∑ k ∈ Finset.range (r + 1), ((N + 1 + r).choose k : ℤ) *
            H W x (r - k) (List.replicate k s ++ s :: Y) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Nat.add_sub_add_right, List.replicate_succ', List.append_assoc, List.singleton_append]
      rw [H_succ W (fun i => x i + s) r Y]
      beta_reduce at e1 ⊢
      rw [e1, hadd, e2, e3, show N + 1 + (r + 1) = N + 1 + r + 1 by omega,
        sum_choose_pascal (N + 1 + r) r (fun k => H W x (r + 1 - k) (List.replicate k s ++ Y)), hAB, hC]
      ring

end HsymmShiftProof

theorem HsymmShift.proof : HsymmShift.Statement.{u} := by
  intro F _ K _ _ ι _ W hW d hd N hN x s r Y hrY
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := HsymmShiftProof.main W hW s M x r Y (by rw [hd, ← hrY])
  simp only [HsymmShiftProof.H] at h
  rw [h, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.append_assoc]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleLineBaseProof

theorem intNum_eq_intNumL {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F P bs = intNumL F P (List.ofFn bs) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem pullDeg_some {K : Type*} (c : K → ℤ) :
    FieldNumbers.pullDeg (Function.Embedding.some : K ↪ Option K) c = liftDeg c := by
  funext o
  cases o with
  | none =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨k, hk⟩
      exact Option.some_ne_none k hk
  | some k =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    exact (Option.some_injective K).extend_apply c 0 k

theorem relDim_of_krull {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type)
    [Field F] (I : Ideal (MRing ι F)) (e : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff I e).2 h

theorem contractPrime_projIdeal {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] {N M : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (F : Type)
    [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K) (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (Option.some : K → Option K)).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (MvPolynomial.map_injective _ (algebraMap Ω Φ).injective)
  unfold FieldNumbers.contractPrime projIdeal pointIdeal
  have hcomp : (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1)).comp
      (rename (FieldNumbers.blockIncl (Function.Embedding.some : K ↪ Option K)
        (bundleIdx ι M))).toRingHom = ψ.comp (pointConeMap (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k))
        F y).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
    · rintro ⟨k, i⟩
      simp [ψ, pointConeMap, FieldNumbers.blockIncl, projCoord]
      rfl
  exact (RingHom.comap_ker _ _).trans
    ((congrArg RingHom.ker hcomp).trans (RingHom.ker_comp_of_injective _ hψ))

theorem replace_zeta {K : Type} [Fintype K] [DecidableEq K] {ι' : Option K → Type}
    [∀ o, Fintype (ι' o)] (F : Type) [Field F] (P : Ideal (MRing ι' F)) (hP : IsMultiProjPrime P)
    (e : ℕ) (hd : FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ))) (c : K → ℤ)
    (bf bg : Option K → ℕ) (f g : MRing ι' F) (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (hfP : f ∉ P) (hgP : g ∉ P) (hfg : (fun o => (bf o : ℤ) - bg o) = zetaDeg - liftDeg c)
    (hdiv : ratDiv P f g = 0) :
    ∀ (n : ℕ) (Y : List (K → ℤ)), n + Y.length = e →
      intNumL F P (List.replicate n zetaDeg ++ Y.map liftDeg) =
        intNumL F P ((List.replicate n c ++ Y).map liftDeg) := by
  intro n
  induction n with
  | zero => intro Y _; simp
  | succ m ih =>
    intro Y hY
    set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
    have hlen : l.length + 1 = e := by simp [hl]; omega
    have hdl : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [hlen]; exact hd
    have hsplit : (zetaDeg : Option K → ℤ) = liftDeg c + (zetaDeg - liftDeg c) := by abel
    rw [List.replicate_succ, List.cons_append, ← hl, hsplit,
      NumericalSegreProof.intNumL_cons_add FieldNumbers.IntNumAdd.full F P hP l hdl]
    have hzero : intNumL F P ((zetaDeg - liftDeg c) :: l) = 0 := by
      rw [NumericalSegreProof.intNumL_perm F P (List.perm_append_singleton _ _).symm]
      have hcut := FieldNumbers.CutRational.full F (Option K) ι' P hP l.length hdl bf bg f g hf hg
        hfP hgP l.get
      rw [hfg, hdiv, intNum_eq_intNumL, List.ofFn_succ', List.concat_eq_append] at hcut
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get] at hcut
      rw [hcut]
      simp [cycEval]
    rw [hzero, add_zero]
    have hperm : (liftDeg c :: l).Perm
        (List.replicate m zetaDeg ++ (c :: Y).map liftDeg) := by
      rw [hl, List.map_cons]
      exact List.perm_middle.symm
    rw [NumericalSegreProof.intNumL_perm F P hperm, ih (c :: Y) (by simp; omega)]
    congr 1
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

end FlagBundleLineBaseProof


open FlagBundleLineBaseProof in
theorem FlagBundleLineBase.proof (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{0}) :
    FlagBundleLineBase.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht h0 n Y hnY
  obtain ⟨hP, hPd⟩ := hdim F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht 1 le_rfl h0
  rw [show e + 1 - 1 = e by omega] at hPd
  obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hfg, hdiv⟩ :=
    hsec F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0
  rw [replace_zeta F _ hP e hPd (a - b ⟨0, h0⟩) bf bg f g hf hg hfP hgP hfg hdiv n Y hnY]
  set L := List.replicate n (a - b ⟨0, h0⟩) ++ Y with hL
  have hLlen : L.length = e := by simp [hL]; omega
  have hcon := contractPrime_projIdeal (K := K) F y w φ (truncCoord t 1)
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) = ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]
    exact (congrArg FieldNumbers.relDim hcon).trans (relDim_of_krull F (pointIdeal F y) e hdimV)
  have hPd' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t 1)) =
      ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]; exact hPd
  have h := (hpf F K (Option K) Function.Embedding.some (bundleIdx ι M) _ hP L.length hPd' hcd
    L.get).2
  have h2 : intNum F (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) L.get = intNum F (pointIdeal F y) L.get :=
    congrArg (fun I => intNum F I L.get) hcon
  rw [hdeg F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0, Nat.cast_one, one_mul,
    h2] at h
  simp only [pullDeg_some] at h
  rw [intNum_eq_intNumL, intNum_eq_intNumL, List.ofFn_get] at h
  have hmap : List.ofFn (fun i => liftDeg (L.get i)) = L.map liftDeg := by
    apply List.ext_get <;> simp
  rw [hmap] at h
  exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace RootPolynomialNumber

variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_rename_mul {N q : ℕ} (x : Fin N → K → ℤ) (L : Fin q → K → ℤ)
    (G : MvPolynomial (Fin N) ℤ) (Q : MvPolynomial (Fin q) ℤ) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x L) (rename Sum.inl G * rename Sum.inr Q) [] W =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
  classical
  have hQ : rename Sum.inl G * rename Sum.inr Q =
      ∑ μ ∈ Q.support, Q.coeff μ •
        (rename Sum.inl G * monomial (Finsupp.mapDomain Sum.inr μ) (1 : ℤ)) := by
    conv_lhs => rw [Q.as_sum]

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [rename_monomial, ← C_mul', ← mul_one (Q.coeff μ), ← C_mul_monomial, mul_one]
    ring
  change classNumAddHom (Sum.elim x L) [] W _ = _

  rw [hQ, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, smul_eq_mul]
  congr 1
  change classNum (Sum.elim x L) _ [] W = _
  rw [plainPairNumber.classNum_mul_monomial, plainPairNumber.classNum_rename _ Sum.inl_injective,
    classList_mapDomain, List.append_nil, Sum.elim_comp_inl, Sum.elim_comp_inr]

end RootPolynomialNumber

theorem RootPolynomialNumber.proof : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  classical
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q).IsHomogeneous d := by
    have h := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h
  have hcls : Sum.elim x L ∘ (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) =
      Fin.append x L := by
    funext i
    induction i using Fin.addCases <;> simp
  have hren : rename (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        rename Sum.inl G * rename Sum.inr Q := by
    have e1 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.castAdd q = Sum.inl := by
      funext i
      simp
    have e2 : (finSumFinEquiv.symm : Fin (N + q) ≃ Fin N ⊕ Fin q) ∘ Fin.natAdd N = Sum.inr := by
      funext i
      simp
    rw [map_mul, rename_rename, rename_rename, e1, e2]
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hW : ∀ W : Ideal (MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
                                (specialIdeal W) d (Fin.append x L) (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
        ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) finSumFinEquiv.symm (Sum.elim x L) hcls hH W,
      hren, RootPolynomialNumber.classNum_rename_mul]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [hW]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ, Finsupp.fun_support_eq]
    exact Finset.finite_toSet _
  rw [cycEval_eq_sum hfin]
  simp only [cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end
