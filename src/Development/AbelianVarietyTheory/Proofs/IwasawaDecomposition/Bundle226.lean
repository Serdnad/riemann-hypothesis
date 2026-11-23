module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle010
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.DualLattices.Bundle001
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Formalism.LocalToGlobal.Divisibility.Bundle002
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

namespace TopRename

variable {p q : ℕ} (hc : Fintype.card (Unit × Fin p × Fin q) = p * q)

def idx : Fin p × Fin q ≃ Fin (p * q) :=
  (Equiv.punitProd (Fin p × Fin q)).symm.trans (Fintype.equivFinOfCardEq hc)

theorem blockEmb_eq (x : Fin q × Fin p × Fin p) :
    blockEmb hc x = (idx hc (x.2.1, x.1), idx hc (x.2.2, x.1)) := rfl

theorem blockEmb_injective : Function.Injective (blockEmb hc) := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ h
  simp only [blockEmb_eq, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, -⟩⟩ := h
  subst e1 e2 e3
  rfl

def permOf (τ : Fin q → Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p * q)) :=
  (idx hc).permCongr (Equiv.prodCongrLeft fun b => (τ b)⁻¹)

theorem permOf_apply' (τ : Fin q → Equiv.Perm (Fin p)) (j : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (j, b)) = idx hc ((τ b)⁻¹ j, b) := by
  simp [permOf, Equiv.permCongr_apply]

theorem permOf_apply (τ : Fin q → Equiv.Perm (Fin p)) (i : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (τ b i, b)) = idx hc (i, b) := by
  rw [permOf_apply']
  simp

theorem sign_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permOf hc τ) : ℤˣ) : ℤ) = sgnProd τ := by
  simp [permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]

theorem permOf_injective : Function.Injective (permOf hc) := by
  intro τ τ' e
  funext b
  have h : ∀ j, (τ b)⁻¹ j = (τ' b)⁻¹ j := by
    intro j
    have := congrArg (fun w : Equiv.Perm (Fin (p * q)) => w (idx hc (j, b))) e
    simp only [permOf_apply'] at this
    exact congrArg Prod.fst ((idx hc).injective this)
  exact inv_inj.mp (Equiv.ext h)

theorem graph_apply' {n : ℕ} (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    (∑ a, Finsupp.single (a, permOf hc τ a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) =
      (blockGraph τ).mapDomain (blockEmb hc) := by
  rw [blockGraph, Finsupp.mapDomain_finsetSum]
  simp_rw [Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single, blockEmb_eq]
  rw [← (idx hc).sum_comp, ← (Equiv.prodCongrLeft fun b => τ b).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  simp [permOf_apply]

theorem mem_range_of_graph (w : Equiv.Perm (Fin (p * q))) (u : Fin q × Fin p × Fin p →₀ ℕ)
    (h : u.mapDomain (blockEmb hc) = ∑ a, Finsupp.single (a, w a) 1) : ∃ τ, permOf hc τ = w := by
  have hr : ∀ x : Fin p × Fin q, ((idx hc).symm (w (idx hc x))).2 = x.2 := by
    intro x
    have h0 : (∑ a, Finsupp.single (a, w a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) (idx hc x, w (idx hc x)) ≠ 0 := by
      rw [graph_apply' (fun a => w a)]
      simp
    rw [← h] at h0
    by_contra hne
    apply h0
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨b, i, j⟩, hy⟩
    rw [blockEmb_eq, Prod.mk.injEq] at hy
    apply hne
    have hx : x = (i, b) := ((idx hc).injective hy.1).symm
    rw [← hy.2, Equiv.symm_apply_apply, hx]
  let f : Fin q → Fin p → Fin p := fun b i => ((idx hc).symm (w (idx hc (i, b)))).1
  have hf : ∀ b, Function.Injective (f b) := by
    intro b i i' e
    have : (idx hc).symm (w (idx hc (i, b))) = (idx hc).symm (w (idx hc (i', b))) :=
      Prod.ext e ((hr (i, b)).trans (hr (i', b)).symm)
    simpa using this
  let σ : Fin q → Equiv.Perm (Fin p) := fun b => Equiv.ofBijective (f b) (Finite.injective_iff_bijective.mp (hf b))
  refine ⟨fun b => (σ b)⁻¹, ?_⟩
  ext1 a
  obtain ⟨⟨i, b⟩, rfl⟩ := (idx hc).surjective a
  rw [permOf_apply', inv_inv, ← (idx hc).apply_symm_apply (w (idx hc (i, b)))]
  congr 1
  exact Prod.ext rfl (hr (i, b)).symm

end TopRename


open TopRename in
theorem topCoeff_rename_blockEmb : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q)
    (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) =
      ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff G (blockGraph τ) := by
  intro p q h1 G
  rw [GlobalTheory.GoodMetric.topCoeff]
  symm
  refine Fintype.sum_of_injective (permOf h1) (permOf_injective h1) _ _ ?_ ?_
  · intro w hw
    rw [coeff_rename_eq_zero, mul_zero]
    intro u hu
    obtain ⟨τ, rfl⟩ := mem_range_of_graph h1 w u hu
    exact absurd ⟨τ, rfl⟩ hw
  · intro τ
    rw [graph_permOf, coeff_rename_mapDomain _ (blockEmb_injective h1), ← sign_permOf h1]

end GlobalTheory.CayleyBlock
end
end

section

noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.TopRead

variable {n : ℕ}

theorem list_prod_gen {m : ℕ} (x : Fin m → Fin n × Fin n) :
    (List.ofFn fun j => gen n (x j)).prod =
      (List.ofFn fun j => vec n (x j).1).prod ⊗ₜ (List.ofFn fun j => vec n (x j).2).prod := by
  induction m with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ)]
    simp only [List.ofFn_succ, List.prod_cons, gen, Algebra.TensorProduct.tmul_mul_tmul]

theorem topBig_toEven_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    topBig n ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  have h1 : ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) = (List.ofFn fun j => gen n (x j)).prod := by
    rw [map_prod, ← List.prod_ofFn, ← Subalgebra.coe_val, map_list_prod, List.map_ofFn]
    congr 1
    exact congrArg List.ofFn (funext fun j => by simp [toEven, aeval_X])
  rw [h1, list_prod_gen, topBig_tmul]
  simp only [topExt, vec]
  rw [← ExteriorAlgebra.ιMulti_apply, ← ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.liftAlternating_apply_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem toMultiset_sum_single {α : Type*} [DecidableEq α] {m : ℕ} (x : Fin m → α) :
    Finsupp.toMultiset (∑ j, Finsupp.single (x j) 1) = Finset.univ.val.map x := by

  rw [map_sum, Finset.sum_eq_multiset_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  have : (fun j => ({x j} : Multiset α)) = (fun a => ({a} : Multiset α)) ∘ x := rfl
  rw [this, ← Multiset.map_map, Multiset.sum_map_singleton]

theorem toMultiset_injective' {α : Type*} [DecidableEq α] :
    Function.Injective (Finsupp.toMultiset : (α →₀ ℕ) → Multiset α) := fun f g h => by
  rw [← Finsupp.toMultiset_toFinsupp f, h, Finsupp.toMultiset_toFinsupp]

theorem coeff_prod_X {m : ℕ} (x : Fin m → Fin n × Fin n) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) d =
      if Finset.univ.val.map x = Finsupp.toMultiset d then 1 else 0 := by
  classical
  have e : (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (x j) 1) 1 :=
    (monomial_sum_one _ _).symm
  rw [e, coeff_monomial, ← toMultiset_sum_single]
  simp only [toMultiset_injective'.eq_iff]

theorem topForm_self (v : Fin n → Fin n → ℂ) : topForm n n v = (Pi.basisFun ℂ (Fin n)).det v := by
  simp [topForm]

theorem det_single_perm (π : Equiv.Perm (Fin n)) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (π j) 1) = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  have : (fun j => (Pi.single (π j) 1 : Fin n → ℂ)) = (Pi.basisFun ℂ (Fin n)) ∘ π := by
    funext j; simp
  rw [this, AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]

theorem det_single_not_inj (a : Fin n → Fin n) (ha : ¬ Function.Injective a) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (a j) 1) = 0 := by
  refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => ha fun i j hij => h ?_
  simp [hij]


open Classical in
theorem topCoeff_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    GlobalTheory.GoodMetric.topCoeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  unfold GlobalTheory.GoodMetric.topCoeff
  simp_rw [coeff_prod_X, toMultiset_sum_single]
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro heq
    have := congrArg Multiset.card heq
    simp at this
    exact hm this
  subst hm
  rw [topForm_self, topForm_self]
  set a : Fin m → Fin m := fun j => (x j).1 with ha_def
  set b : Fin m → Fin m := fun j => (x j).2 with hb_def

  have hcond : ∀ w : Equiv.Perm (Fin m),
      Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, w c)) →
        Function.Injective a ∧ Function.Injective b := by
    intro w heq
    have h1 := congrArg (Multiset.map Prod.fst) heq
    have h2 := congrArg (Multiset.map Prod.snd) heq
    simp only [Multiset.map_map] at h1 h2
    have e1 : Multiset.map (Prod.fst ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simp
    have e2 : Multiset.map (Prod.snd ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simpa using Multiset.map_univ_val_equiv w
    rw [e1] at h1
    rw [e2] at h2
    constructor
    · have hn : (Multiset.map (Prod.fst ∘ x) Finset.univ.val).Nodup := by rw [h1]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
    · have hn : (Multiset.map (Prod.snd ∘ x) Finset.univ.val).Nodup := by rw [h2]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
  by_cases hab : Function.Injective a ∧ Function.Injective b
  swap
  · have : (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).1 1) *
        (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).2 1) = 0 := by
      rcases not_and_or.mp hab with h | h
      · rw [det_single_not_inj a h, zero_mul]
      · rw [det_single_not_inj b h, mul_zero]
    rw [this]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    exact fun heq => hab (hcond w heq)
  obtain ⟨ha, hb⟩ := hab
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective a (Finite.injective_iff_bijective.mp ha)
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have hτ : ∀ j, (x j).2 = τ j := fun j => rfl
  simp_rw [hπ, hτ, det_single_perm]
  have hx : x = (fun c => (c, (τ * π⁻¹) c)) ∘ π := by
    funext j
    simp [Prod.ext_iff, hπ, hτ]
  have hmap : Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
    rw [hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [Finset.sum_eq_single (τ * π⁻¹)]
  · rw [if_pos hmap, mul_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  · intro w _ hw
    rw [if_neg, mul_zero]
    intro heq
    apply hw
    ext c
    have hc : (c, w c) ∈ Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
      rw [← hmap, heq]; simp
    obtain ⟨c', _, hc'⟩ := Multiset.mem_map.mp hc
    simp only [Prod.mk.injEq] at hc'
    obtain ⟨rfl, h⟩ := hc'
    exact congrArg Fin.val h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem topCoeff_eq_topBig (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    GlobalTheory.GoodMetric.topCoeff P = topBig n (toEven n P : Big n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, map_smul, smul_eq_mul, topBig_toEven_prod, ← topCoeff_prod]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add (f := _), Subalgebra.coe_add, map_add (f := _), ← hp, ← hq]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.GrassModel.TopRead
end
end

section

set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial Filter Topology ComplexConjugate
open GlobalTheory.HermFrame

namespace GlobalTheory.DomainDens

variable {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)

def flatCoordinateMatrixBlock (u : ReciprocityTheory.L2DbarEstimates.V n) : Matrix (Fin p) (Fin q) ℂ :=
  Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ

theorem block_reshape_apply (u : ReciprocityTheory.L2DbarEstimates.V n) (i : Fin p) (b : Fin q) :
    flatCoordinateMatrixBlock h τ u i b = u (Fintype.equivFinOfCardEq h (τ, i, b)) := rfl

theorem flatCoordinateMatrixBlock_entry_eq_proj (i : Fin p) (b : Fin q) :
    (fun u => flatCoordinateMatrixBlock h τ u i b) = fun u => EuclideanSpace.proj (𝕜 := ℂ) (Fintype.equivFinOfCardEq h (τ, i, b)) u :=
  rfl

theorem flatCoordinateMatrixBlock_at_zero : flatCoordinateMatrixBlock h τ 0 = 0 := by
  ext i b; simp [block_reshape_apply]

theorem matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (flatCoordinateMatrixBlock h τ) x ξ = flatCoordinateMatrixBlock h τ ξ := by
  ext i b
  rw [mdel_apply, flatCoordinateMatrixBlock_entry_eq_proj, del_eq_fderiv (ContinuousLinearMap.differentiableAt _),
    ContinuousLinearMap.fderiv]
  rfl

theorem matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (flatCoordinateMatrixBlock h τ) x η = 0 := by
  ext i b
  rw [mdbar_apply, flatCoordinateMatrixBlock_entry_eq_proj, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem matrixEntriesContDiffAt_flatCoordinateMatrixBlock {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) : MContDiffAt k (flatCoordinateMatrixBlock h τ) x :=
  fun i b => by
    rw [flatCoordinateMatrixBlock_entry_eq_proj]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℂ) (n := k)
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) (Fintype.equivFinOfCardEq h (τ, i, b)) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ)).restrict_scalars ℝ |>.contDiffAt

theorem mContDiffAt_hP {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x := by
  unfold Formalism.DegreeFormula.hP
  exact (mContDiffAt_const 1).sub ((matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).mul (matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x).conjTranspose)

theorem mdel_hP (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) x ξ = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ) := by
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) x := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ x
  have e : (fun u => Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u)) =
      fun u => (fun _ => (1 : Matrix (Fin p) (Fin p) ℂ)) u + -(flatCoordinateMatrixBlock h τ u * (flatCoordinateMatrixBlock h τ u)ᴴ) := by
    funext u; simp [Formalism.DegreeFormula.hP, sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (hz.mul hz.conjTranspose).neg, mdel_const, mdel_neg,
    mdel_mul hz hz.conjTranspose, mdel_conjTranspose, matrixAntiholomorphicPartialDeriv_flatCoordinateMatrixBlock, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock]
  simp

theorem hP_zero : Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0) = 1 := by simp [Formalism.DegreeFormula.hP, flatCoordinateMatrixBlock_at_zero]

theorem conn_model (x ξ : ReciprocityTheory.L2DbarEstimates.V n) (hu : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x)).det) :
    conn (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) x ξ =
      flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ x)ᴴ * (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ x))⁻¹ := by
  rw [conn, transpose_transpose, mdel_transpose (fun u => (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹), transpose_transpose,
    mdel_inv (mContDiffAt_hP h τ x) hu, nonsing_inv_nonsing_inv _ hu, mdel_hP]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

theorem curv_model (ξ η : ReciprocityTheory.L2DbarEstimates.V n) :
    curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 ξ η = -(flatCoordinateMatrixBlock h τ ξ * (flatCoordinateMatrixBlock h τ η)ᴴ) := by
  have hu0 : IsUnit (Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ 0)).det := by simp [hP_zero]
  have hev := (mContDiffAt_hP (k := 1) h τ 0).eventually_isUnit hu0
  have hz : MContDiffAt 1 (flatCoordinateMatrixBlock h τ) 0 := matrixEntriesContDiffAt_flatCoordinateMatrixBlock h τ 0
  rw [curv, mdbar_congr (hev.mono fun x hx => conn_model h τ x ξ hx),
    mdbar_mul ((mContDiffAt_const _).mul hz.conjTranspose) ((mContDiffAt_hP h τ 0).inv hu0),
    mdbar_mul (mContDiffAt_const _) hz.conjTranspose, mdbar_conjTranspose, matrixHolomorphicPartialDeriv_flatCoordinateMatrixBlock, mdbar_const, hP_zero,
    flatCoordinateMatrixBlock_at_zero]
  simp

theorem curvPoly_model_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι),
    GlobalTheory.GoodMetric.curvPoly
      (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 =
      -GlobalTheory.DomainDens.blockSym h τ := by
  intro ι _ p q n h τ
  have e2 : ∀ (a c : Fin n) (i j : Fin p),
      curv (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)
        0 (GlobalTheory.GoodMetric.coordVec a) (GlobalTheory.GoodMetric.coordVec c) i j =
      -∑ b : Fin q, (if Fintype.equivFinOfCardEq h (τ, i, b) = a then 1 else 0) *
        (if Fintype.equivFinOfCardEq h (τ, j, b) = c then 1 else 0) := by
    intro a c i j
    change curv (fun u => ((Formalism.DegreeFormula.hP (flatCoordinateMatrixBlock h τ u))⁻¹)ᵀ) 0 _ _ i j = _
    rw [curv_model h τ, Matrix.neg_apply, Matrix.mul_apply]
    simp [block_reshape_apply, PiLp.single_apply]
  refine Matrix.ext fun i j => ?_
  simp only [GlobalTheory.GoodMetric.curvPoly, of_apply, e2, Matrix.neg_apply, blockSym_apply]

  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, neg_inj, map_sum, Finset.sum_mul, mul_ite, ite_mul, one_mul,
  zero_mul, mul_zero, apply_ite (C : ℂ → MvPolynomial (Fin n × Fin n) ℂ), map_one, map_zero]
  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [Finset.sum_ite_eq]

end GlobalTheory.DomainDens
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain

namespace GlobalTheory.Chain.InnerSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem theta_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1 (fun k f hf => ⟨?_, rfl⟩) f hf P).1
  obtain ⟨τ, i, j⟩ := k
  exact GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.Chain.InnerSteps

end
end
