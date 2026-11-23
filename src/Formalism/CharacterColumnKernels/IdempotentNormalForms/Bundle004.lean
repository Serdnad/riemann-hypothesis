module

public import Formalism.CharacterColumnKernels.Bundle002
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange
public import Formalism.CharacterColumnKernels.Bundle003
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle003
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle001
public import Formalism.CharacterColumnKernels.Bundle004
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Finset

noncomputable section

namespace Formalism.NG

namespace TrivialCharacterBlockLength

section Triv

variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

lemma length_mid_zero {H : Type*} [AddCommGroup H] [Module O H] (ρM : Representation O G M)
    (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  have hz : ∀ z : ↥(LinearMap.range Ψ ⊓
      LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ), z = 0 := by
    rintro ⟨z, hz⟩
    obtain ⟨-, hz2⟩ := Submodule.mem_inf.mp hz
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply] at hz2
    have h0 := hB _ hz2
    exact Subtype.ext (Subtype.ext h0)
  rw [hz a, hz b]

end Triv

lemma blockTrivAbs {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
    {H : Type*} [AddCommGroup H] [Module O H]
    (ρM : Representation O G M) (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM)
    {ι : Type*} [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
    (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
    (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞)
    (hrows : ∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))),
      F w ≤ A ∧ Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A)
    (hcols : ∀ w ∈ cols, ∀ h : H,
      resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w)
    (hQ : ∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q)
    (hsel : Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols,
      (F w).comap (resH1 ρM (D w))) ≤ s) :
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) + (s + ∑ w ∈ what₂, lenRow w) := by
  classical
  let A : ∀ w, Submodule O (H1z (resRep ρM (D w))) := fun w =>
    if hw : w ∈ what₂ then Classical.choose (hrows w hw) else F w
  have hA : ∀ w (hw : w ∈ what₂), A w = Classical.choose (hrows w hw) := fun w hw => dif_pos hw
  have hA' : ∀ w, w ∉ what₂ → A w = F w := fun w hw => dif_neg hw
  have hFA : ∀ w, F w ≤ A w := by
    intro w
    by_cases hw : w ∈ what₂
    · rw [hA w hw]; exact (Classical.choose_spec (hrows w hw)).1
    · rw [hA' w hw]
  let S : Submodule O (H1z ρM) := Q ⊓ ⨅ w ∈ what₂ ∪ cols, (A w).comap (resH1 ρM (D w))
  have hS : LinearMap.range ((Submodule.mkQ ((coB1 ρM).comap (coZ1s ρM).subtype)) ∘ₗ Ψ) ≤ S := by
    rintro _ ⟨h, rfl⟩
    refine (IdempotentNormalFormsRhoFacts.mem_sel (what₂ ∪ cols) (fun w => resH1 ρM (D w)) A Q _).mpr
      ⟨hQ h, fun w hw => ?_⟩
    by_cases hwr : w ∈ what₂
    · rw [hA w hwr]; exact (Classical.choose_spec (hrows w hwr)).2.2 h
    · rw [hA' w hwr]
      exact hcols w ((Finset.mem_union.mp hw).resolve_left hwr) h
  have hchain := lenChain O H (coZ1s ρM) (H1z ρM) Ψ _ S hS
  rw [length_mid_zero ρM hB Ψ, add_zero] at hchain
  have hSel : Module.length O S ≤ s + ∑ w ∈ what₂, lenRow w := by
    have h2 := selRelax O (H1z ρM) ι (what₂ ∪ cols) (fun w => H1z (resRep ρM (D w)))
      (fun w => resH1 ρM (D w)) F A Q hFA
    have hterm : ∀ w ∈ what₂ ∪ cols, Module.length O (A w ⧸ (F w).comap (A w).subtype) ≤
        if w ∈ what₂ then lenRow w else 0 := by
      intro w _
      by_cases hwr : w ∈ what₂
      · rw [if_pos hwr, hA w hwr]
        exact (Classical.choose_spec (hrows w hwr)).2.1
      · rw [if_neg hwr, hA' w hwr, Submodule.comap_subtype_self, Module.length_eq_zero]
    calc Module.length O S ≤ _ := h2
      _ ≤ s + ∑ w ∈ what₂ ∪ cols, (if w ∈ what₂ then lenRow w else 0) :=
          add_le_add hsel (Finset.sum_le_sum hterm)
      _ = s + ∑ w ∈ what₂, lenRow w := by
          rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  exact hchain.trans (add_le_add le_rfl hSel)

lemma final_arith (k X c vδ s R1 R2 : ℕ∞) (hk : k ≤ X + c * vδ) :
    k + (s + (R1 + R2)) ≤ s + X + R1 + 4 * (c + 1) * vδ + R2 := by
  calc k + (s + (R1 + R2)) ≤ (X + c * vδ) + (s + (R1 + R2)) := add_le_add hk le_rfl
    _ ≤ (X + c * vδ) + (s + (R1 + R2)) + (3 * c * vδ + 4 * vδ) := le_self_add
    _ = s + X + R1 + 4 * (c + 1) * vδ + R2 := by ring

end TrivialCharacterBlockLength

end Formalism.NG
end
end

section

open Finset

noncomputable section

namespace Formalism.NG

namespace GlobalDeterminantRelations

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')

lemma evalSp_smul (r : R') (v : EvalSp O d R' x') (a : d) :
    (r • v : d → FractionRing O) a =
      ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b := rfl

instance : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') where
  smul_comm r c v := by
    funext a
    change (∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (c * (v : d → FractionRing O) b)) =
      c * ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

instance : FiniteDimensional (FractionRing O) (EvalSp O d R' x') :=
  inferInstanceAs (FiniteDimensional (FractionRing O) (d → FractionRing O))

def curryE (g : Type) : (g × d → FractionRing O) ≃ₗ[FractionRing O] (g → EvalSp O d R' x') where
  toFun v i a := v (i, a)
  invFun w q := (w q.1 : d → FractionRing O) q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma det_relMap_eq (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R') :
    LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') Θ) =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det := by
  have hconj := LinearMap.det_conj (relMap (FractionRing O) (EvalSp O d R' x') Θ) (curryE R' x' g).symm
  rw [← hconj, ← LinearMap.det_toLin']
  congr 1
  apply LinearMap.ext
  intro v
  funext p
  obtain ⟨i, a⟩ := p
  let ev : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => (w : d → FractionRing O) a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  show ev (∑ j, Θ i j • (curryE R' x' g v) j) =
    Matrix.mulVec (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ) v (i, a)

  rw [map_sum]
  have hev : ∀ j, ev (Θ i j • (curryE R' x' g v) j) =
      ∑ b, (Θ i j : X' → Matrix d d (FractionRing O)) x' a b * v (j, b) := fun j =>
    evalSp_smul R' x' (Θ i j) ((curryE R' x' g v) j) a
  rw [Finset.sum_congr rfl (fun j _ => hev j), Matrix.mulVec]
  first
    | (rw [dotProduct, Fintype.sum_prod_type]; rfl)
    | (rw [Matrix.dotProduct, Fintype.sum_prod_type]; rfl)
    | (simp only [dotProduct, Fintype.sum_prod_type]; rfl)

end GlobalDeterminantRelations

universe u v w

open GlobalDeterminantRelations in
theorem globalConcrete_of (hD : StatDescent.{u, v, w}) (hV : StatVccSpan.{u, v}) :
    CharacterColumnGlobal.{u, v, w} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ α _ _ bl hbl ρk
    hsurj hblk hcard
  classical
  obtain ⟨C, hC⟩ := genericFin R' O m g α (fun k => {a // bl a = k}) hcard ρk hsurj P
  obtain ⟨f, hfT, hf⟩ := hdet (C * P)
  have hcomp : ∀ (x' : X') (v : g → EvalSp O d R' x'),
      relMap (FractionRing O) (EvalSp O d R' x') (C * P) v =
        relMap (FractionRing O) (EvalSp O d R' x') C (relMap (FractionRing O) (EvalSp O d R' x') P v) := by
    intro x' v
    funext i
    show ∑ j, (C * P) i j • v j = ∑ l, C i l • ∑ j, P l j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hvanish : ∀ x', p x' ∉ Z → f x' = 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    let e := (homEquiv P : (Coker P →ₗ[R'] EvalSp O d R' x') ≃ₗ[FractionRing O]
      LinearMap.ker (relMap (FractionRing O) (EvalSp O d R' x') P))
    have hne : e φ ≠ 0 := fun h => hφ0 (e.injective (h.trans (map_zero e).symm))
    have hv0 : ((e φ : LinearMap.ker _) : g → EvalSp O d R' x') ≠ 0 := fun h => hne (Subtype.ext h)
    have hvk := LinearMap.mem_ker.mp (e φ).2
    have hnot : ¬ Function.Injective (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) := by
      intro hinj
      apply hv0
      apply hinj
      rw [hcomp, hvk, map_zero, map_zero]
    have hdet0 : LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) = 0 := by
      by_contra hne'
      apply hnot
      have hu : IsUnit (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne')
      exact ((Module.End.isUnit_iff _).mp hu).injective
    rw [GlobalDeterminantRelations.det_relMap_eq] at hdet0
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf x', hdet0, map_zero]
  have hspan := hD O X X' T T' Z p q b hT hZ f hfT hvanish π'
  refine (hV O X T Z (p π') (f π') hspan).trans (le_of_eq ?_)
  have hfπ : f π' = (bigMat (fun r : R' => ρπ r) (C * P)).det := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf π', RingHom.map_det]
    congr 1
    refine Matrix.ext fun x y => ?_
    simp [bigMat, RingHom.mapMatrix_apply, ← hρπ]
  rcases isEmpty_or_nonempty g with hg | hg
  · have h1 : f π' = 1 := by
      rw [hfπ]
      exact Matrix.det_isEmpty
    rw [h1, IsDiscreteValuationRing.addVal_one]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hBT : (bigMat (fun r : R' => ρπ r) (C * P)).BlockTriangular (fun x : g × d => bl x.2) := by
    intro x y hxy
    exact hbl _ hxy
  have himage : (Finset.univ.image fun x : g × d => bl x.2) = Finset.univ.image bl := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨(Classical.arbitrary g, a), ha⟩
  have hprod : ∀ (s : Finset α) (F : α → O), IsDiscreteValuationRing.addVal O (∏ k ∈ s, F k) =
      ∑ k ∈ s, IsDiscreteValuationRing.addVal O (F k) := by
    intro s F
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]
  have hblock : ∀ k, ((bigMat (fun r : R' => ρπ r) (C * P)).toSquareBlock
      (fun x : g × d => bl x.2) k).det = (bigMat (fun r : R' => ρk k r) (C * P)).det := by
    intro k
    let eK : g × {a // bl a = k} ≃ {x : g × d // bl x.2 = k} :=
      { toFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        invFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Matrix.det_reindex_self eK.symm]
    congr 1
    refine Matrix.ext fun x y => ?_
    obtain ⟨pp, i⟩ := x
    obtain ⟨qq, j⟩ := y
    show _ = (ρk k) ((C * P) pp qq) i j
    rw [← hblk]
    rfl
  rw [hfπ, hBT.det, hprod, himage]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hblock k, ← (lenKer : StatLenKer) O _ (bigMat (fun r : R' => ρk k r) (C * P))]
  exact hC k

theorem globalConcrete : CharacterColumnGlobal := globalConcrete_of descent vccSpan

end Formalism.NG
end
end

section

open Finset

noncomputable section

namespace Formalism.NG

theorem mem_ccIdeal_iff_forall {O : Type*} [CommRing O] {X : Type*} (T : Subalgebra O (X → O))
    (Z : Set X) (c : T) : c ∈ ccIdeal T Z ↔ ∀ x ∉ Z, (c : X → O) x = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [resOff] using this
  · intro h
    funext x
    simp [resOff, h x.1 x.2]

theorem vccBaseChange : StatVccBaseChange := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X T T' hT' Z x
  classical
  set b := Module.Free.chooseBasis O O' with hb
  set φ : (X → O) → (X → O') := fun f => algebraMap O O' ∘ f with hφ
  have hdec : ∀ f ∈ Submodule.span O' (φ '' (T : Set (X → O))),
      ∃ g : Module.Free.ChooseBasisIndex O O' → (X → O), (∀ j, g j ∈ T) ∧ f = ∑ j, b j • φ (g j) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨t, ht, rfl⟩ := hf
      refine ⟨fun j => b.repr 1 j • t, fun j => T.smul_mem ht _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      calc algebraMap O O' (t x') = algebraMap O O' (t x') * ∑ j, b.repr 1 j • b j := by
            rw [b.sum_repr, mul_one]
        _ = ∑ j, b j * algebraMap O O' (b.repr 1 j * t x') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, map_mul]
            ring
    | zero =>
      refine ⟨0, fun j => T.zero_mem, ?_⟩
      funext x'
      simp [hφ]
    | add f f' _ _ hf hf' =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g', hg', rfl⟩ := hf'
      refine ⟨g + g', fun j => T.add_mem (hg j) (hg' j), ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        map_add, mul_add, Finset.sum_add_distrib]
    | smul o f _ hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      refine ⟨fun k => ∑ j, b.repr (o * b j) k • g j, fun k => T.sum_mem fun j _ => T.smul_mem (hg j) _, ?_⟩
      funext x'

      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_sum, map_mul]
      calc o * ∑ j, b j * algebraMap O O' (g j x') = ∑ j, (o * b j) * algebraMap O O' (g j x') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (∑ k, b.repr (o * b j) k • b k) * algebraMap O O' (g j x') := by
            simp_rw [b.sum_repr]
        _ = ∑ k, b k * ∑ j, algebraMap O O' (b.repr (o * b j) k) * algebraMap O O' (g j x') := by
            simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hvan : ∀ (g : Module.Free.ChooseBasisIndex O O' → X → O) (x' : X),
      ∑ j, b j * algebraMap O O' (g j x') = 0 → ∀ j, g j x' = 0 := by
    intro g x' h
    have h2 : ∑ j, g j x' • b j = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ h2
  apply le_antisymm
  · have hne : ((fun c : T => IsDiscreteValuationRing.addVal O ((c : X → O) x)) ''
        (ccIdeal T Z : Set T)).Nonempty := ⟨_, 0, (ccIdeal T Z).zero_mem, rfl⟩
    obtain ⟨c0, hc0, hc0eq⟩ := csInf_mem hne
    have hvcc : vcc T Z x = IsDiscreteValuationRing.addVal O ((c0 : X → O) x) := by
      rw [show IsDiscreteValuationRing.addVal O ((c0 : X → O) x) = _ from hc0eq, sInf_image]
      rfl
    rw [hvcc, ← he]
    have hmem : φ (c0 : X → O) ∈ T' := by
      have h1 : φ (c0 : X → O) ∈ (T' : Set (X → O')) := by
        rw [hT']
        exact Submodule.subset_span ⟨c0, c0.2, rfl⟩
      exact h1
    have hc0' : (⟨φ (c0 : X → O), hmem⟩ : T') ∈ ccIdeal T' Z := by
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T Z c0).mp hc0 x' hx'
      simp [hφ, h0]
    exact iInf₂_le _ hc0'
  · unfold vcc
    refine le_iInf₂ fun c' hc' => ?_
    have hc'span : (c' : X → O') ∈ Submodule.span O' (φ '' (T : Set (X → O))) := by
      have h1 : (c' : X → O') ∈ (T' : Set (X → O')) := c'.2
      rw [hT'] at h1
      exact h1
    obtain ⟨g, hg, hgeq⟩ := hdec _ hc'span
    have hgZ : ∀ j, (⟨g j, hg j⟩ : T) ∈ ccIdeal T Z := by
      intro j
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T' Z c').mp hc' x' hx'
      rw [hgeq] at h0
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h0
      exact hvan g x' h0 j
    rw [hgeq]
    simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    refine AddValuation.map_le_sum _ fun j _ => ?_
    rw [AddValuation.map_mul, he]
    refine le_trans ?_ le_add_self
    exact mul_le_mul_of_nonneg_left (iInf₂_le (⟨g j, hg j⟩ : T) (hgZ j)) (zero_le)

end Formalism.NG
end
end

section

open Finset

noncomputable section

namespace Formalism.NG

theorem etaBound : LocalSubalgebraEtaBound := by
  intro O _ _ _ X _ T _ hsep V _ _ _ _ _ act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB
    B hB
  refine (congBoundGood O X T hsep V act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG
    haB).trans ?_
  refine sum_le_sum fun x hx => ?_
  gcongr
  exact hB x hx

end Formalism.NG
end
end
