module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolynomialEqAevalPairings
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle013
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} (ε : Fin m → Bool)

abbrev VV (ι : Type) (n : ℕ) := (ι × Fin n) ⊕ (ι × Fin n)

abbrev Rw (β : Bool) := {a : Fin m // ε a = β}

def jv (β : Bool) : VV (Rw ε β) n → Fin m × Fin n × Bool :=
  Sum.elim (fun x => (x.1.1, x.2, false)) (fun x => (x.1.1, x.2, true))

def emb (β : Bool) : PV (Rw ε β) (Fin n) (Fin n) →ₐ[ℂ] PX m n := rename (jv ε β)

def act (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
    else ∑ b, C (u k.1 b) * X (b, k.2.1, false))

def blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) : Matrix (Fin m) (Fin m) ℂ := fun a b =>
  if ha : ε a = β then (if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0) else (if a = b then 1 else 0)

variable {ε}

theorem sum_rw {R : Type*} [AddCommMonoid R] (β : Bool) (F : Rw ε β → R) :
    ∑ b : Fin m, (if h : ε b = β then F ⟨b, h⟩ else 0) = ∑ b : Rw ε β, F b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun b : Fin m => ε b = β)]
  have h2 : ∑ b : {b : Fin m // ¬ ε b = β}, (if h : ε b.1 = β then F ⟨b.1, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero (fun b _ => dif_neg b.2)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl (fun b _ => by rw [dite_eq_left b.2])

theorem blk_block (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a b : Fin m) (h : ε a ≠ ε b) : blk ε β v a b = 0 := by
  unfold blk
  by_cases ha : ε a = β
  · rw [dite_eq_left ha, dif_neg (fun hb => h (ha.trans hb.symm))]
  · rw [dif_neg ha, if_neg (fun e : a = b => h (congrArg ε e))]

theorem blk_of (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ε a = β) (b : Fin m) :
    blk ε β v a b = if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0 := by
  unfold blk; rw [dite_eq_left ha]

theorem blk_of_not (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (b : Fin m) :
    blk ε β v a b = if a = b then 1 else 0 := by
  unfold blk; rw [dif_neg ha]

theorem blk_unitary (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (hv : v ∈ Matrix.unitaryGroup (Rw ε β) ℂ) :
    blk ε β v ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hv ⊢
  ext a c
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply]
  by_cases ha : ε a = β
  · by_cases hc : ε c = β
    · have key := congrFun (congrFun hv ⟨a, ha⟩) ⟨c, hc⟩
      rw [Matrix.mul_apply, Matrix.one_apply] at key
      simp only [Matrix.star_apply] at key
      have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) =
          if h : ε b = β then v ⟨a, ha⟩ ⟨b, h⟩ * star (v ⟨c, hc⟩ ⟨b, h⟩) else 0 := by
        intro b
        rw [blk_of β v ha, blk_of β v hc]
        by_cases hb : ε b = β
        · rw [dite_eq_left hb, dite_eq_left hb, dite_eq_left hb]
        · rw [dif_neg hb, dif_neg hb, dif_neg hb, zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), sum_rw β (fun j => v ⟨a, ha⟩ j * star (v ⟨c, hc⟩ j)), key]
      by_cases hac : a = c
      · subst hac; simp
      · rw [if_neg (fun h => hac (congrArg Subtype.val h)), if_neg hac]
    · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if c = b then blk ε β v a b else 0 := by
        intro b
        rw [blk_of_not β v hc b]
        by_cases hcb : c = b
        · rw [if_pos hcb, if_pos hcb, star_one, mul_one]
        · rw [if_neg hcb, if_neg hcb, star_zero, mul_zero]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [blk_block β v a c (by rw [ha]; exact fun h => hc h.symm), if_neg (by rintro rfl; exact hc ha)]
  · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if a = b then star (blk ε β v c b) else 0 := by
      intro b
      rw [blk_of_not β v ha b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, one_mul]
      · rw [if_neg hab, if_neg hab, zero_mul]
    rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases hc : ε c = β
    · rw [blk_block β v c a (by rw [hc]; exact fun h => ha h.symm), star_zero,
        if_neg (by rintro rfl; exact ha hc)]
    · rw [blk_of_not β v hc a]
      by_cases hca : c = a
      · subst hca; simp
      · rw [if_neg hca, star_zero, if_neg (fun h => hca h.symm)]

end PositivityTheory.Rg.Sw.FFTSteps.CycF
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

theorem stable_eval_sub {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (Sum.elim (fun x : ι × A => ∑ j, g x.1 j * z (Sum.inl (j, x.2)))
      (fun y : ι × B => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, sub, aeval_X, eval_X]
    congr 1
    rcases v with x | y <;> simp [map_sum]

theorem stable : Stable := by
  intro ι A B _ _ _ _ hA hB p hp
  classical
  set n := Fintype.card ι
  let eι : ι ≃ Fin n := Fintype.equivFin ι
  let eA : A ↪ Fin n := (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb hA)
  let eB : B ↪ Fin n := (Fintype.equivFin B).toEmbedding.trans (Fin.castLEEmb hB)
  let f : (ι × A) ⊕ (ι × B) → Unit × Bool × Fin n × Fin n :=
    Sum.elim (fun x => ((), true, eι x.1, eA x.2)) (fun y => ((), false, eι y.1, eB y.2))
  set q : MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ := rename f p with hq
  have hinv : ∀ u : Unit → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z : Unit × Bool × Fin n × Fin n → ℂ, eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l
        else (starRingEnd ℂ) (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) q = eval z q := by
    intro u hu z
    let u' : Matrix ι ι ℂ := (u ()).submatrix eι eι
    have hu' : u' ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      have h1 := Matrix.mem_unitaryGroup_iff.1 (hu ())
      simp only [u', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
      rw [Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, h1, Matrix.submatrix_one_equiv]
    rw [hq, eval_rename, eval_rename]
    have := congrArg (eval (z ∘ f)) (hp u' hu')
    rw [stable_eval_sub] at this
    rw [← this]
    refine congrArg (fun w => eval w p) ?_
    funext v
    rcases v with ⟨i, a⟩ | ⟨i, b⟩
    · simp only [Function.comp, f, Sum.elim_inl, if_true, u', Matrix.submatrix_apply]
      exact (Equiv.sum_comp eι (fun l => u () (eι i) l * z ((), true, l, eA a))).symm
    · simp only [Function.comp, f, Sum.elim_inr, Bool.false_eq_true, if_false, u', Matrix.submatrix_apply,
        Matrix.map_apply]
      exact (Equiv.sum_comp eι (fun l => (starRingEnd ℂ) (u () (eι i) l) * z ((), false, l, eB b))).symm
  obtain ⟨s, hs⟩ := GlobalTheory.invariant_polynomial_eq_aeval_pairings Unit n n le_rfl q hinv
  let ψF : Unit × Bool × Fin n × Fin n → PV ι A B := fun v =>
    if v.2.1 then (if h : ∃ a, eA a = v.2.2.2 then X (Sum.inl (eι.symm v.2.2.1, h.choose)) else 0)
    else (if h : ∃ b, eB b = v.2.2.2 then X (Sum.inr (eι.symm v.2.2.1, h.choose)) else 0)
  have hψf : ∀ w, ψF (f w) = X w := by
    rintro (⟨i, a⟩ | ⟨i, b⟩)
    · have h : ∃ a', eA a' = eA a := ⟨a, rfl⟩
      simp only [f, Sum.elim_inl, ψF, if_true, dif_pos h, Equiv.symm_apply_apply]
      rw [eA.injective h.choose_spec]
    · have h : ∃ b', eB b' = eB b := ⟨b, rfl⟩
      simp only [f, Sum.elim_inr, ψF, Bool.false_eq_true, if_false, dif_pos h, Equiv.symm_apply_apply]
      rw [eB.injective h.choose_spec]
  have hp' : p = aeval ψF q := by
    rw [hq, aeval_rename]
    have : (ψF ∘ f) = X := funext hψf
    rw [this, aeval_X_left_apply]
  have hgen : ∀ v : Unit × Fin n × Fin n, aeval ψF (∑ k, (X (v.1, false, k, v.2.1) * X (v.1, true, k, v.2.2) :
      MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ)) ∈ pairAlg ι A B := by
    rintro ⟨t, a', b'⟩

    simp only [map_sum, map_mul, aeval_X, ψF, Bool.false_eq_true, if_false, if_true]
    by_cases hb : ∃ b, eB b = a'
    · by_cases ha : ∃ a, eA a = b'
      · simp only [dif_pos hb, dif_pos ha]
        have : (∑ k : Fin n, (X (Sum.inr (eι.symm k, hb.choose)) : PV ι A B) * X (Sum.inl (eι.symm k, ha.choose))) =
            ∑ i, (X (Sum.inl (i, ha.choose)) : PV ι A B) * X (Sum.inr (i, hb.choose)) := by
          rw [← Equiv.sum_comp eι]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Equiv.symm_apply_apply, mul_comm]
        rw [this]
        exact Algebra.subset_adjoin ⟨(ha.choose, hb.choose), rfl⟩
      · simp only [dif_neg ha, mul_zero, Finset.sum_const_zero]
        exact Subalgebra.zero_mem _
    · simp only [dif_neg hb, zero_mul, Finset.sum_const_zero]
      exact Subalgebra.zero_mem _
  rw [hp', hs, ← AlgHom.comp_apply, comp_aeval]
  clear hs hp'
  induction s using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add x y hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul_X x v hx => rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hx (hgen v)

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section

noncomputable section

open MeasureTheory MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace AvgPf

section
variable {ι A B : Type} [Fintype ι]

def actP (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (actP g h z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p s hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    rcases s with x | y

    · simp [sub, actP, map_sum]

    · simp [sub, actP, map_sum]

theorem actP_actP (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actP g h (actP g' h' z) = actP (g * g') (h * h') z := by
  funext s
  rcases s with x | y
  · simp only [actP, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [actP, Sum.elim_inr, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem totalDegree_sub_le (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree :=
  _root_.UpperTheory.Reformulated.B.TotalDegreeLinear.main g h p

theorem continuous_coeff_sub {K : Type} [TopologicalSpace K] (g h : K → Matrix ι ι ℂ) (hg : Continuous g)
    (hh : Continuous h) (p : PV ι A B) : ∀ m, Continuous fun k => AddMonoidAlgebra.coeff (sub (g k) (h k) p) m := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => intro m; simp only [sub, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro m; simp only [map_add (f := _), MvPolynomial.coeff_add]; exact (hp m).add (hq m)
  | mul_X p s hp =>
    intro m
    rcases s with x | y
    · have e : ∀ k, AddMonoidAlgebra.coeff (sub (g k) (h k) (p * X (Sum.inl x))) m =
          ∑ j, g k x.1 j * AddMonoidAlgebra.coeff (sub (g k) (h k) p * X (Sum.inl (j, x.2))) m := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inl, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply x.1).comp hg))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const
    · have e : ∀ k, AddMonoidAlgebra.coeff (sub (g k) (h k) (p * X (Sum.inr y))) m =
          ∑ j, h k y.1 j * AddMonoidAlgebra.coeff (sub (g k) (h k) p * X (Sum.inr (j, y.2))) m := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inr, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply y.1).comp hh))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const

end

abbrev εT (N : ℕ) : Fin N → Bool := fun _ => true

theorem continuous_toMK (N : ℕ) : Continuous fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k :=
  (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val

theorem toMK_mul (N : ℕ) (k k' : Formalism.REAL.KG (εT N)) :
    Formalism.REAL.toMK (k * k') = Formalism.REAL.toMK k * Formalism.REAL.toMK k' := rfl

theorem map_star_mul {N : ℕ} (a b : Matrix (Fin N) (Fin N) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp [Matrix.mul_apply]

theorem exists_toMK (N : ℕ) (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ k : Formalism.REAL.KG (εT N), Formalism.REAL.toMK k = u := by
  have hJ : Formalism.REAL.Jm (εT N) = 1 := by
    simp [Formalism.REAL.Jm, εT, Matrix.diagonal_one]
  have : u ∈ Formalism.REAL.Kset (εT N) := ⟨hu, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  rw [← Formalism.REAL.range_toMK] at this
  exact this

theorem isEmbedding_toMK (N : ℕ) : Topology.IsEmbedding (fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k) :=
  (Formalism.REAL.isClosedEmbeddingMatrix N (εT N)).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal

instance instSCKG (N : ℕ) : SecondCountableTopology (Formalism.REAL.KG (εT N)) := by
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  exact (isEmbedding_toMK N).isInducing.secondCountableTopology

theorem muK_univ (N : ℕ) : Formalism.REAL.muK (εT N) Set.univ = 1 := by
  have := Measure.haarMeasure_self (G := Formalism.REAL.KG (εT N)) (K₀ := ⊤)
  rw [TopologicalSpace.PositiveCompacts.coe_top] at this
  exact this

theorem map_mul_right_muK (N : ℕ) (g : Formalism.REAL.KG (εT N)) :
    Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N)) = Formalism.REAL.muK (εT N) := by
  have : (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))).IsHaarMeasure :=
    Measure.isHaarMeasure_map_mul_right (Formalism.REAL.muK (εT N)) g
  have h := Measure.haarMeasure_unique (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))) ⊤
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
    Set.preimage_univ, muK_univ, one_smul]
  rfl

instance (N : ℕ) : (Formalism.REAL.muK (εT N)).IsMulRightInvariant := ⟨fun g => map_mul_right_muK N g⟩

end AvgPf

open AvgPf in
theorem avg : Avg := by
  classical
  intro N A B _ _ p
  set μ := Formalism.REAL.muK (εT N)
  let F : Formalism.REAL.KG (εT N) → PV (Fin N) A B := fun k =>
    sub (Formalism.REAL.toMK k) ((Formalism.REAL.toMK k).map star) p
  set d := p.totalDegree
  let S : Finset ((Fin N × A) ⊕ (Fin N × B) →₀ ℕ) :=
    ((Finset.univ : Finset ((Fin N × A) ⊕ (Fin N × B) → Fin (d + 1))).image
      (fun f => Finsupp.equivFunOnFinite.symm (fun s => (f s : ℕ)))).filter (fun m => (m.sum fun _ e => e) ≤ d)
  have hsupp : ∀ k, (F k).support ⊆ S := by
    intro k m hm
    have hdeg : (m.sum fun _ e => e) ≤ d := (le_totalDegree hm).trans (totalDegree_sub_le _ _ _)
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun s => ⟨m s, Nat.lt_succ_of_le ?_⟩, Finset.mem_univ _, ?_⟩, hdeg⟩
    · exact (Finsupp.le_degree ..).trans hdeg
    · ext s; simp
  have hcont : ∀ m, Continuous fun k => AddMonoidAlgebra.coeff (F k) m := fun m =>
    continuous_coeff_sub _ _ (continuous_toMK N)
      (continuous_pi fun i => continuous_pi fun j => continuous_star.comp
        ((continuous_apply j).comp ((continuous_apply i).comp (continuous_toMK N)))) p m
  have hint : ∀ m, Integrable (fun k => AddMonoidAlgebra.coeff (F k) m) μ := fun m =>
    integrableOn_univ.1 ((hcont m).continuousOn.integrableOn_compact isCompact_univ)
  let P : PV (Fin N) A B := ∑ m ∈ S, monomial m (∫ k, AddMonoidAlgebra.coeff (F k) m ∂μ)
  have hF : ∀ k, F k = ∑ m ∈ S, monomial m (AddMonoidAlgebra.coeff (F k) m) := by
    intro k
    conv_lhs => rw [(F k).as_sum]
    exact Finset.sum_subset (hsupp k) fun m _ hm => by rw [notMem_support_iff.1 hm, monomial_zero]
  have heval : ∀ z, eval z P = ∫ k, eval z (F k) ∂μ := by
    intro z
    have e : ∀ k, eval z (F k) = ∑ m ∈ S, AddMonoidAlgebra.coeff (F k) m * (m.prod fun n e => z n ^ e) := by
      intro k
      conv_lhs => rw [hF k]

      simp only [map_sum, eval_monomial]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_finsetSum _ (fun m _ => (hint m).mul_const _)]

    simp only [P, map_sum, eval_monomial, integral_mul_const]
  refine ⟨P, ?_, ?_, heval⟩
  · intro u hu
    obtain ⟨ku, hku⟩ := exists_toMK N u hu
    refine MvPolynomial.funext fun z => ?_
    rw [AvgPf.eval_sub, heval, heval]
    have e2 : ∀ k, eval (actP u (u.map star) z) (F k) = eval z (F (k * ku)) := by
      intro k
      simp only [F]
      rw [AvgPf.eval_sub, actP_actP, ← AvgPf.eval_sub, toMK_mul, hku, map_star_mul]
    simp only [e2]
    exact integral_mul_right_eq_self (fun k => eval z (F k)) ku
  · refine totalDegree_finsetSum_le fun m hm => (totalDegree_monomial_le _ _).trans ?_
    exact (Finset.mem_filter.1 hm).2

end PositivityTheory.Rg.Sw.FFTSteps
end
end
