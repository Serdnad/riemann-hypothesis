module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

@[expose] public section

section

open Polynomial

namespace GlobalTheory.TraceAeval

open Module

theorem trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl g).pow_left k) h
      rw [pow_succ, Module.End.mul_eq_comp, this, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq, eval_add]; ring
  | monomial k a =>
    rw [aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]; ring

theorem coe_aeval_restrict {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (p : ℂ[X]) (x : N) :
    ((aeval (f.restrict hf) p x : N) : V) = aeval f p x := by
  have hk : ∀ (k : ℕ) (x : N), ((((f.restrict hf) ^ k) x : N) : V) = (f ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; simp [pow_succ, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a => simp [aeval_monomial, hk]

theorem trace_aeval_end {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := by
    intro μ x hx
    rw [show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]
    exact Subtype.mem _
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]
  have h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict
        (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      ext x
      rfl
    rw [e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]
  simp_rw [h1]
  rw [Finset.sum_multiset_map_count]
  have hs : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]

theorem trace_aeval_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm

noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i

open Polynomial in
open Module in
theorem _root_.GlobalTheory.TraceAeval.powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]

theorem charpoly_powMat {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ := by
    rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]
    simp
  rw [h2] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext i j
  refine Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm
  have h3 := (AdjoinRoot.powerBasis' h).basis_eq_pow j
  refine Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr
    ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm
  simp only [← pow_succ']
  change _ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk]
  rfl

end GlobalTheory.TraceAeval
end

section

namespace GlobalTheory.NormDetIndex

open Module Submodule

theorem norm_card_quotient_span (l : ℕ) [Fact (Nat.Prime l)] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span ({x} : Set ℤ_[l]) = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hx, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hx).symm
  have h2 : Function.Surjective (PadicInt.toZModPow (p := l) x.valuation) :=
    ZMod.ringHom_surjective _
  rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective h2).toEquiv, Nat.card_zmod,
    PadicInt.norm_eq_zpow_neg_valuation hx, Nat.cast_pow, Padic.norm_p_pow]

theorem norm_eq_of_associated (l : ℕ) [Fact (Nat.Prime l)] {x y : ℤ_[l]} (h : Associated x y) :
    ‖x‖ = ‖y‖ := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]

theorem norm_det_eq_norm_index (l : ℕ) [Fact (Nat.Prime l)] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℚ_[l])‖ := by
  set N := LinearMap.range M.mulVecLin with hN
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hv
  let e : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective _ hinj
  let b : Basis κ ℤ_[l] (κ → ℤ_[l]) := Pi.basisFun _ _
  have h : finrank ℤ_[l] N = finrank ℤ_[l] (κ → ℤ_[l]) := e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  let e' : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have h1 : M.det = LinearMap.det (N.subtype ∘ₗ (e : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) := by
    rw [← LinearMap.det_toLin' M]
    rfl
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    have ha : (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) (b' j) = a j • b' j := by
      change ((b'.equiv ab (Equiv.refl _) (b' j) : N) : κ → ℤ_[l]) = _
      rw [b'.equiv_apply, Equiv.refl_apply]
      exact smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have h3 : N.toAddSubgroup.index
      = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span ({a i} : Set ℤ_[l])) := by
    change Nat.card ((κ → ℤ_[l]) ⧸ N) = _
    rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [h1, norm_eq_of_associated l (LinearMap.associated_det_comp_equiv N.subtype e e'), h2, h3,
    Nat.cast_prod, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ =>
    (norm_card_quotient_span l (smithNormalFormCoeffs_ne_zero b h i)).symm

end GlobalTheory.NormDetIndex
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem det_updateRow_single_mul_sub_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (i j : Fin g) :
    x j * (m.updateRow p (Pi.single i 1)).det - x i * (m.updateRow p (Pi.single j 1)).det ∈ I := by
  set m' := m.updateRow p (Pi.single i 1) with hm'
  have h1 : m'.adjugate.mulVec (m'.mulVec x) = m'.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : ∑ q, m'.adjugate j q * m'.mulVec x q = m'.det * x j := by
    have := congrFun h1 j
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at h2
  have h3 : m'.adjugate j p = (m.updateRow p (Pi.single j 1)).det := by
    rw [Matrix.adjugate_apply, hm', Matrix.updateRow_idem]
  have h4 : m'.mulVec x p = x i := by
    simp [hm', Matrix.mulVec]
  rw [h3, h4] at h2
  have h5 : ∑ q ∈ Finset.univ.erase p, m'.adjugate j q * m'.mulVec x q ∈ I := by
    refine I.sum_mem fun q hq => I.mul_mem_left _ ?_
    have hq' : q ≠ p := Finset.ne_of_mem_erase hq
    have : m'.mulVec x q = m.mulVec x q := by
      simp [hm', Matrix.mulVec, Matrix.updateRow_ne hq']
    rw [this]
    exact hm q hq'
  convert h5 using 1
  linear_combination -h2

theorem det_updateRow_alternating_mulVec_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (s : Matrix (Fin g) (Fin g) T)
    (hs : s.transpose = -s) (hd : ∀ i, s i i = 0) :
    (m.updateRow p (s.mulVec x)).det ∈ I := by
  have h1 : (m.updateRow p (s.mulVec x)).det
      = ∑ ij : Fin g × Fin g,
          s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det) := by
    have e : ∀ v : Fin g → T, (m.updateRow p v).det
        = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det := by
      intro v
      have := Matrix.cramer_transpose_apply m v p
      rw [← this, Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

  rw [h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · rintro ⟨i, j⟩
    rw [← map_add (f := _), Ideal.Quotient.eq_zero_iff_mem]
    have hji : s j i = - s i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have := I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)
    convert this using 1
    simp only [Prod.fst_swap, Prod.snd_swap, hji]
    ring
  · rintro ⟨i, j⟩ h e
    apply h
    have : j = i := congrArg Prod.fst e
    subst this
    simp [hd]

theorem det_sub_det_mem_span_of_mulVec_eq :
    ∀ (T : Type) [CommRing T] (g : ℕ) (x : Fin g → T), (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) → ∀ c c' : Matrix (Fin g) (Fin g) T, c.mulVec x = c'.mulVec x → c.det - c'.det ∈ Ideal.span (Set.range (c.mulVec x)) := by
  intro T _ g x hx c c' hc
  set I := Ideal.span (Set.range (c.mulVec x)) with hI
  let M : Finset (Fin g) → Matrix (Fin g) (Fin g) T :=
    fun S => Matrix.of fun i => if i ∈ S then c' i else c i
  have hM : ∀ S q, (M S).mulVec x q = c.mulVec x q := by
    intro S q
    by_cases h : q ∈ S
    · rw [hc]; simp [M, Matrix.mulVec, h]
    · simp [M, Matrix.mulVec, h]
  have key : ∀ S : Finset (Fin g), c.det - (M S).det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : M ∅ = c := by ext i j; simp [M]
      simp [this]
    | insert p S hp ih =>
      obtain ⟨s, hs, hd, hr⟩ := hx (c p - c' p) (by
        have := congrFun hc p
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr this)
      have h1 := det_updateRow_alternating_mulVec_mem x I (M S) p
        (fun q _ => by rw [hM]; exact Ideal.subset_span ⟨q, rfl⟩) s hs hd
      rw [← hr] at h1
      have e1 : (M S).updateRow p (c' p) = M (insert p S) := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M]
        · simp [M, Matrix.updateRow_ne h, h]
      have e2 : (M S).updateRow p (c p) = M S := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M, hp]
        · simp [Matrix.updateRow_ne h]
      have e3 := Matrix.det_updateRow_add (M S) p (c p - c' p) (c' p)
      rw [sub_add_cancel, e1, e2] at e3
      have := I.add_mem ih h1
      convert this using 1
      linear_combination e3
  have := key Finset.univ
  have e : M Finset.univ = c' := by ext i j; simp [M]
  rwa [e] at this

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem mem_map_ker_of_one_tmul_eq_zero_of_flat (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by
  classical
  set I : Ideal B := RingHom.ker (algebraMap B k) with hI
  let f : (B ⧸ I) →ₗ[B] k :=
    Submodule.liftQ I (Algebra.linearMap B k) (fun a ha => by simpa [hI] using ha)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun a ha => by simpa [hI] using ha)
  have hinj : Function.Injective (f.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hx : (Ideal.Quotient.mk I 1) ⊗ₜ[B] c = 0 := by
    apply hinj
    have h1 : f (Ideal.Quotient.mk I 1) = 1 := by
      show Submodule.liftQ I (Algebra.linearMap B k) _ (Submodule.Quotient.mk 1) = 1
      rw [Submodule.liftQ_apply, Algebra.linearMap_apply, map_one]
    rw [LinearMap.rTensor_tmul, map_zero, h1]
    exact h
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul C I) hx
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul,
    Submodule.Quotient.mk_eq_zero] at hq
  rw [Ideal.smul_top_eq_map] at hq
  exact hq

end GlobalTheory
end
