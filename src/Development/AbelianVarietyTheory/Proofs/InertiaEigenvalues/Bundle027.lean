module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.GroupTheory.Index
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Discriminant
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

section

open Polynomial

namespace GlobalTheory.GalDisj

section
variable {k M F D : Type*} [Field k] [Field M] [Field F] [Field D] [Algebra k M] [Algebra k F]
  [Algebra k D] [Algebra M D] [Algebra F D] [IsScalarTower k M D] [IsScalarTower k F D]

end

open Polynomial in
private theorem natDegree_minpoly_le_natDegree_minpoly_map {k Ω D : Type} [Field k] [Field Ω] [Field D]
    [Algebra k Ω] (o : Ω →+* D) (F : Subfield D)
    (hF : ∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) (α : Ω) (hα : IsIntegral k α)
    (hsplit : ((minpoly k α).map (algebraMap k Ω)).Splits) :
    (minpoly k α).natDegree ≤ (minpoly F (o α)).natDegree := by
  set ψ : k →+* F := (o.comp (algebraMap k Ω)).codRestrict F (fun c => (hF _).2 ⟨c, rfl⟩)
  have hcomp : F.subtype.comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hcomp' : (algebraMap F D).comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hmon : ((minpoly k α).map ψ).Monic := (minpoly.monic hα).map ψ
  have hroot : aeval (o α) ((minpoly k α).map ψ) = 0 := by
    rw [aeval_def, eval₂_map, hcomp', ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hβ : IsIntegral F (o α) := ⟨_, hmon, hroot⟩
  have hdvd : minpoly F (o α) ∣ (minpoly k α).map ψ := minpoly.dvd F _ hroot
  have hP : ((minpoly k α).map ψ).map F.subtype = ((minpoly k α).map (algebraMap k Ω)).map o := by
    rw [map_map, map_map, hcomp]
  have hP0 : ((minpoly k α).map ψ).map F.subtype ≠ 0 := (hmon.map _).ne_zero
  have hGdvd : (minpoly F (o α)).map F.subtype ∣ ((minpoly k α).map ψ).map F.subtype :=
    Polynomial.map_dvd _ hdvd
  have hGs : ((minpoly F (o α)).map F.subtype).Splits := by
    refine Splits.of_dvd ?_ hP0 hGdvd
    rw [hP]
    exact hsplit.map o
  have hGm : ((minpoly F (o α)).map F.subtype).Monic := (minpoly.monic hβ).map _
  have hlift : (minpoly F (o α)).map F.subtype ∈ lifts o := by
    refine hGs.mem_lift_of_roots_mem_range hGm o fun a ha => ?_
    have h1 := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hP0 hGdvd) ha
    rw [hP, hsplit.roots_map o] at h1
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h1
    exact ⟨r, rfl⟩
  have hlift' : (minpoly F (o α)).map F.subtype ∈ lifts (o.comp (algebraMap k Ω)) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨y, hy⟩ := hlift n
    have hyF : o y ∈ F := by
      rw [hy, coeff_map]
      exact ((minpoly F (o α)).coeff n).2
    obtain ⟨c, rfl⟩ := (hF y).1 hyF
    exact ⟨c, hy⟩
  obtain ⟨g, hg⟩ := (mem_lifts _).1 hlift'
  have hinj : Function.Injective (o.comp (algebraMap k Ω)) := RingHom.injective _
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hg
    exact hGm.ne_zero hg.symm
  have hgα : aeval α g = 0 := by
    apply o.injective
    rw [map_zero, aeval_def, hom_eval₂, ← eval_map, hg, eval_map]
    exact minpoly.aeval F (o α)
  calc (minpoly k α).natDegree ≤ g.natDegree := natDegree_le_of_dvd (minpoly.dvd k α hgα) hg0
    _ = ((minpoly F (o α)).map F.subtype).natDegree := by
        rw [← hg, natDegree_map_eq_of_injective hinj]
    _ = (minpoly F (o α)).natDegree := natDegree_map_eq_of_injective (RingHom.injective _) _


open Polynomial in
theorem _root_.GlobalTheory.GalDisj.galois_linearDisjoint : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  intro k Ω D _ _ _ _ _ o F hF m x hx b hb hsum
  classical
  set M := IntermediateField.adjoin k (Set.range x)
  haveI : FiniteDimensional k M :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  obtain ⟨α', hα'⟩ := Field.exists_primitive_element k M
  set α : Ω := (α' : Ω) with hαdef
  have hxα : ∀ i, x i ∈ IntermediateField.adjoin k {α} := by
    intro i
    have h1 : (IntermediateField.adjoin k {α'}).map M.val = IntermediateField.adjoin k {α} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [← h1, hα']
    exact ⟨⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩, trivial, rfl⟩
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim ≤ (minpoly F (o α)).natDegree := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    exact natDegree_minpoly_le_natDegree_minpoly_map o F hF α hint (IsGalois.splits k α)
  have hli : LinearIndependent F (fun j : Fin pb.dim => o α ^ (j : ℕ)) :=
    (linearIndependent_pow (o α)).comp (Fin.castLE hdim) (Fin.castLE_injective hdim)
  set c : Fin m → Fin pb.dim → k := fun i j => pb.basis.repr ⟨x i, hxα i⟩ j
  have hexp : ∀ i, x i = ∑ j, c i j • α ^ (j : ℕ) := by
    intro i
    have h := congrArg Subtype.val (pb.basis.sum_repr ⟨x i, hxα i⟩)
    refine h.symm.trans ?_
    simp [c, pb, IntermediateField.adjoin.powerBasis_gen]
  have hd : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i = 0 := by
    have hmem : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i ∈ F := fun j =>
      F.sum_mem fun i _ => F.mul_mem ((hF _).2 ⟨_, rfl⟩) (hb i)
    intro j
    have := Fintype.linearIndependent_iff.1 hli (fun j => ⟨_, hmem j⟩) ?_ j
    · exact congrArg Subtype.val this
    rw [← hsum]

    simp only [hexp, Subfield.smul_def, map_sum, map_smul, Algebra.smul_def, map_mul, map_pow,
    Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (∑ i, o (algebraMap k Ω (c i j)) * b i) * o α ^ (j : ℕ) = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hx.repr
  have hgx : ∀ i, g (x i) = Finsupp.single i 1 := by
    intro i
    have := LinearMap.congr_fun hg ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hx.repr_eq_single i _ rfl]
  intro l
  calc b l = ∑ i, o (algebraMap k Ω (g (x i) l)) * b i := by
        simp [hgx, Finsupp.single_apply]
    _ = ∑ j : Fin pb.dim, o (algebraMap k Ω (g (α ^ (j : ℕ)) l)) *
          ∑ i, o (algebraMap k Ω (c i j)) * b i := by

        simp only [hexp, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by simp [hd]

end GlobalTheory.GalDisj
end

section

namespace GlobalTheory


open Module in
theorem eq_zero_of_sum_mul_embeddings_eq_zero (F Ω L : Type) [Field F] [CharZero F] [Field Ω]
    [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ)
    (e : Fin m → Ω) (he : LinearIndependent F e) (_halg : ∀ t, IsAlgebraic F (e t))
    (a : Fin m → L) (h : ∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F L
  let ε : Fin (Module.finrank F L) ≃ (L →ₐ[F] Ω) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card F L Ω, Fintype.card_fin])
  let E := Algebra.embeddingsMatrixReindex F Ω b ε
  have hE : E.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F Ω b ε
    rw [show (Algebra.embeddingsMatrixReindex F Ω b ε).det = 0 from h0] at h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact Algebra.discr_not_zero_of_basis F b ((map_eq_zero _).mp h1)
  have hEa : ∀ i k, E i k = ε k (b i) := by
    intro i k
    simp [E, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  let v : Fin (Module.finrank F L) → Ω := fun i => ∑ t, (b.repr (a t) i) • e t
  have hv : Matrix.vecMul v E = 0 := by
    funext k
    rw [Matrix.vecMul, dotProduct]
    simp only [Pi.zero_apply, hEa, v]
    have hk := h (ε k)
    rw [← hk]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)

    conv_rhs => rw [← b.sum_repr (a t), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  have hv0 : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hE hv
  have hc : ∀ t i, b.repr (a t) i = 0 := by
    intro t i
    have := congrFun hv0 i
    exact (Fintype.linearIndependent_iff.mp he) (fun t => b.repr (a t) i) this t
  funext t
  rw [Pi.zero_apply, ← b.sum_repr (a t)]
  simp [hc]

end GlobalTheory
end

section

namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues

open Module

theorem exists_common_eigenvector {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : ι → Module.End k V)
    (hcomm : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, (f i : V → V) w ∈ W) →
        ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ i, ∃ c : k, (f i : V → V) x = c • x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hinv
  by_cases hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    let g : Module.End k W := (f i).restrict (fun w hw => hinv i w hw)
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hgv : g v = c • v := hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'
    have hvW' : (v : V) ∈ W' := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hgv
      simpa [g] using this
    have hW'ne : W' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hvW'
      exact hv0 (Subtype.ext hvW')
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      obtain ⟨w, hw, hne⟩ := hi c
      have : w ∈ W' := h ▸ hw
      exact hne ((Module.End.mem_eigenspace_iff).mp this.2)
    have hdlt : Module.finrank k W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W' := by
      intro j w hw
      refine ⟨hinv j w hw.1, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h1 : f i w = c • w := (Module.End.mem_eigenspace_iff).mp hw.2
      have h2 := congrArg (fun F : Module.End k V => F w) (hcomm i j)
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨x, hx, hx0, hxe⟩ := ih _ hdlt W' rfl hW'ne hinv'
    exact ⟨x, hx.1, hx0, hxe⟩

theorem target : ∀ {k ι V : Type} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [FiniteDimensional k V] (f : ι → Module.End k V), (∀ (i j : ι), f i * f j = f j * f i) → ∀ (d : ℕ) (W : Submodule k V), Module.finrank k ↥W = d → W ≠ ⊥ → (∀ (i : ι), ∀ w ∈ W, (f i : V → V) w ∈ W) → ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : k), (f i : V → V) x = c • x :=
  fun f hc => exists_common_eigenvector f hc

end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
end

section

open scoped BigOperators

namespace GlobalTheory.CentralIdemIntegral

theorem isIntegral_trace_of_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι L) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical
  rw [Matrix.trace_eq_sum_roots_charpoly]
  refine Multiset.sum_induction (IsIntegral ℤ) _ (fun a b ha hb => ha.add hb) isIntegral_zero ?_
  intro μ hμ

  have hroot := Polynomial.isRoot_of_mem_roots hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : Matrix.mulVec A v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

  have hpowv : ∀ k : ℕ, Matrix.mulVec (A ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hμpow : μ ^ (n + 1) = μ := by
    have h1 := hpowv (n + 1)
    rw [hA, hAv] at h1
    have h2 : (μ ^ (n + 1) - μ) • v = 0 := by rw [sub_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0

  refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
  · rw [Polynomial.degree_X]
    exact_mod_cast (show 1 < n + 1 by omega)
  · simp [hμpow]

theorem isIntegral_trace {K ι : Type} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by
  classical

  set φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hφ
  have h := isIntegral_trace_of_algClosed (A.map φ) hn (by rw [← Matrix.map_pow, hA])
  rw [← AddMonoidHom.map_trace] at h
  exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h

theorem trace_leftMulMatrix {G K : Type} [Group G] [Fintype G] [DecidableEq G] [Field K]
    (x : MonoidAlgebra K G) :
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)).trace = (Fintype.card G : K) * x.coeff 1 := by

  have hdiag : ∀ g : G, (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)) g g = x.coeff 1 := by
    intro g
    rw [LinearMap.toMatrixAlgEquiv_apply]
    change (x * MonoidAlgebra.single g 1).coeff g = x.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem isIntegral_card_mul_coeff {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K]
    (e : MonoidAlgebra K G) (he : e * e = e) (hc : ∀ x, e * x = x * e) (g : G) :
    IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) := by
  classical

  set y : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hy
  have hcoeff : y.coeff 1 = e.coeff g := by
    rw [hy, MonoidAlgebra.coeff_mul_single_apply, one_mul, inv_inv, mul_one]
  have hidem : IsIdempotentElem e := he
  have hypow : y ^ (Fintype.card G + 1) = y := by
    rw [hy, (show Commute e (MonoidAlgebra.single g⁻¹ 1) from hc _).mul_pow, hidem.pow_succ_eq,
      MonoidAlgebra.single_pow, one_pow, pow_succ, pow_card_eq_one, one_mul]
  have hM := isIntegral_trace
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K) (Algebra.lmul K (MonoidAlgebra K G) y))
    (n := Fintype.card G) Fintype.card_ne_zero (by rw [← map_pow, ← map_pow, hypow])
  rw [trace_leftMulMatrix, hcoeff] at hM
  exact hM

theorem card_mul_coeff_mem :
    ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  intro G O K _ _ _ _ _ _ _ _ _ e he hc g
  exact (IsIntegrallyClosed.isIntegral_iff (R := O)).1
    (isIntegral_card_mul_coeff e he hc g).tower_top

end GlobalTheory.CentralIdemIntegral
end

section

open scoped NNReal

namespace GlobalTheory

theorem exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero :
    ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V),
        ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  intro S _ u hu
  obtain ⟨m, hm, hum⟩ := Ideal.exists_le_maximal (Ideal.span {u})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hum' : u ∈ m := hum (Ideal.mem_span_singleton_self u)
  haveI := hm.isPrime
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := m) bot_le
  haveI hqp : q.IsPrime := hq.1.1
  let L := AlgebraicClosure (FractionRing (S ⧸ q))
  let g : S →+* L := ((algebraMap (FractionRing (S ⧸ q)) L).comp
    (algebraMap (S ⧸ q) (FractionRing (S ⧸ q)))).comp (Ideal.Quotient.mk q)
  have hg : ∀ s, g s = 0 ↔ s ∈ q := by
    intro s
    simp only [g, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (algebraMap (FractionRing (S ⧸ q)) L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) (FractionRing (S ⧸ q))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hne : m.map g.rangeRestrict ≠ ⊤ := by
    intro h
    have h1 : (1 : g.range) ∈ m.map g.rangeRestrict := h ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ :=
      (Ideal.mem_map_iff_of_surjective _ g.rangeRestrict_surjective).1 h1
    have h2 : g (x - 1) = 0 := by
      have := congrArg Subtype.val hx1
      simp only [RingHom.coe_rangeRestrict, OneMemClass.coe_one] at this
      rw [map_sub, this, map_one, sub_self]
    have h3 : x - 1 ∈ m := hqm ((hg _).1 h2)
    have h4 : (1 : S) ∈ m := by simpa using m.sub_mem hx h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h4)
  obtain ⟨V, hV, hV'⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hmem : ∀ s, g s ∈ V := fun s => hV (show g s ∈ g.range from ⟨s, rfl⟩)
  refine ⟨L, inferInstance, inferInstance, V, g.codRestrict V hmem, ?_, ?_⟩
  · have h1 : g u ∈ V.nonunits :=
      hV' ⟨g.rangeRestrict u, Ideal.mem_map_of_mem _ hum', rfl⟩
    have h2 := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨g u, hmem u⟩)).1 h1
    exact h2
  · intro s hs h0
    have h1 : g s = 0 := congrArg Subtype.val h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq)
      ((hg s).1 h1) hs

end GlobalTheory
end

section

namespace GlobalTheory

theorem image_finite_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  intro G Q _ _ ρ J H hH hρ
  classical
  haveI := hH
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  apply (Set.finite_range (fun q : G ⧸ H =>
    if h : ∃ g ∈ J, (g : G ⧸ H) = q then ρ h.choose else 1)).subset
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨(g : G ⧸ H), ?_⟩
  have hex : ∃ g' ∈ J, (g' : G ⧸ H) = g := ⟨g, hg, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  obtain ⟨hJ, hq⟩ := hex.choose_spec
  have hmem : (hex.choose)⁻¹ * g ∈ H := QuotientGroup.eq.mp hq
  have h1 := hρ _ (J.mul_mem (J.inv_mem hJ) hg) hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end GlobalTheory
end
