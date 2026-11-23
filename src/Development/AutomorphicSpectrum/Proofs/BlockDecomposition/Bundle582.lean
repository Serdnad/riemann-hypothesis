module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle002
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem trace_red_mul {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k A * red ϖ k B) = Ideal.Quotient.mk (lev ϖ k) (∑ a, ∑ c, A a c * B c a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, red, Matrix.map_apply, map_sum, map_mul]

theorem psiLev_holds : PositivityTheory.SiegelWeilFormula.Gunr.PsiLev := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.PsiLev
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT k X hX
  rw [trace_red_mul]
  show _ = PositivityTheory.SiegelWeilFormula.Gunr.psiF ψv ϖ _ k _
  unfold PositivityTheory.SiegelWeilFormula.Gunr.psiF PositivityTheory.PfSWUS.Loc.trPair
  congr 1
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.hermOf, PositivityTheory.SiegelWeilFormula.Gunr.GoodLoc.hermLev, PositivityTheory.SiegelWeilFormula.Gunr.matS,
    Matrix.map_apply, Matrix.of_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
    mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul]
  rw [one_div, map_inv₀, map_ofNat]
  ring

end GlobalTheory.CompanionTheory.GunrLev

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrLevChars

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ}
  {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem sigR_algebraMap (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.algebraMap_eq_smul_one, sigR_smul, map_one]

theorem smul_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {β : Fv F v} (hβ : β ∈ v.adicCompletionIntegers F)
    {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hG.carrier]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hG.carrier] at h2
  exact h2

theorem fixed_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (a : S) (ha : σS a = a) :
    ∃ α : Fv F v, (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) α :=
  hG.fixed a (by rw [← hG.sig, ha])

theorem basis_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hG.carrier] at h
  exact h

theorem nontrivial_S (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : Nontrivial S := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hG.quad.notUnit (isUnit_of_subsingleton _)

theorem card_eq_two (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) : d = 2 := by
  obtain ⟨u, hu, hb⟩ := hG.quad.basis
  have : Nontrivial S := nontrivial_S hG
  have : Nontrivial (Fv F v ⊗[F] E) := (Subtype.val_injective (p := fun x => x ∈ S)).nontrivial
  have hinj := (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  have hli : LinearIndependent (Fv F v) ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have ht : t = 0 := by
      by_contra ht
      have e : (u : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (-(t⁻¹ * s)) := by
        have h3 : t • (u : Fv F v ⊗[F] E) = -(s • (1 : Fv F v ⊗[F] E)) := eq_neg_of_add_eq_zero_right h
        have h4 : (u : Fv F v ⊗[F] E) = t⁻¹ • (t • (u : Fv F v ⊗[F] E)) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h4, h3, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, smul_smul]
      have hfix : σS u = u := Subtype.ext (by rw [hG.sig, e, sigR_algebraMap])
      rw [hfix, sub_self, isUnit_zero_iff] at hu
      exact zero_ne_one hu
    subst ht
    refine ⟨?_, rfl⟩
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one] at h
    exact hinj (by rw [h, map_zero])
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range ![(1 : Fv F v ⊗[F] E), (u : Fv F v ⊗[F] E)]) := by
    rw [← (Algebra.TensorProduct.basis (Fv F v) bs).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, y, hx, hy, e⟩ := hb ⟨_, basis_mem hG i⟩
    obtain ⟨α, hα⟩ := fixed_eq hG x hx
    obtain ⟨β, hβ⟩ := fixed_eq hG y hy
    have e2 : Algebra.TensorProduct.basis (Fv F v) bs i =
        α • (1 : Fv F v ⊗[F] E) + β • (u : Fv F v ⊗[F] E) := by
      have e3 := congrArg Subtype.val e
      simp only [Subring.coe_add, Subring.coe_mul] at e3
      rw [e3, hα, hβ, Algebra.smul_def, Algebra.smul_def, mul_one]
    rw [SetLike.mem_coe, e2]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  have h2 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) bs)
  simpa using h2.symm.trans h1

theorem trace_algebraMap_eq (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) (Fv F v ⊗[F] E) x) = 2 * x := by
  rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) bs), Fintype.card_fin,
    card_eq_two hG, two_nsmul, two_mul]

theorem psiF_compat (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (c : Fv F v) (k : ℕ) (a : Fv F v ⊗[F] E) :
    psiF ψv ϖ c (k + 1) (algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * a) = psiF ψv ϖ c k a := by
  unfold psiF
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, ← mul_assoc ((ϖ ^ (k + 1))⁻¹), pow_succ, mul_inv,
    mul_assoc (ϖ ^ k)⁻¹, inv_mul_cancel₀ hG.unif_ne, mul_one]

theorem mem_level_of_character_trivial (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (hc1 : ‖c‖ = 1) (a : S) (ha : σS a = a)
    (hb : ∀ b, σS b = b → hG.psiLev hc 1 (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev hG.pS 1 := by
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h
    have := hG.two
    rw [h, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨α, hα⟩ := fixed_eq hG a ha
  have hαO : α ∈ v.adicCompletionIntegers F := by
    have h2 := hG.trace_mem a.2
    rw [hα, trace_algebraMap_eq hG] at h2
    have h3 := mul_mem hG.half_mem h2
    rwa [← mul_assoc, inv_mul_cancel₀ h20, one_mul] at h3
  have hkey : c * (ϖ⁻¹ * α) ∈ v.adicCompletionIntegers F := by
    refine (hG.psi_cond _).1 fun β hβ => ?_
    have hbS : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
      have h1 := smul_mem hG hβ (one_mem S)
      rwa [← Algebra.algebraMap_eq_smul_one] at h1
    have hfix : σS ⟨_, hbS⟩ = ⟨_, hbS⟩ := Subtype.ext (by rw [hG.sig]; exact sigR_algebraMap β)
    have h1 := hb _ hfix
    rw [hG.psiLev_mk] at h1
    have e : ((a * ⟨_, hbS⟩ : S) : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (α * β) := by
      rw [Subring.coe_mul, hα, map_mul]
    rw [e] at h1
    unfold psiF at h1
    rw [trace_algebraMap_eq hG] at h1
    rw [← h1]
    congr 1
    have := hG.unif_ne
    field_simp
  have hγ : ϖ⁻¹ * α ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at hkey ⊢
    rw [norm_mul, hc1, one_mul] at hkey
    exact hkey
  have hgS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) ∈ S := by
    have h1 := smul_mem hG hγ (one_mem S)
    rwa [← Algebra.algebraMap_eq_smul_one] at h1
  refine Ideal.mem_span_singleton'.2 ⟨⟨_, hgS⟩, Subtype.ext ?_⟩
  rw [pow_one, Subring.coe_mul, hα]
  show algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ⁻¹ * α) * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = _
  rw [← map_mul]
  congr 1
  have := hG.unif_ne
  field_simp

theorem levChars : PositivityTheory.SiegelWeilFormula.Gunr.LevChars := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG c hc hc1
  refine ⟨fun k a => ?_, fun a ha hb => mem_level_of_character_trivial hG hc hc1 a ha hb⟩
  rw [GoodLoc.psiLev_mk, GoodLoc.psiLev_mk]
  exact psiF_compat hG c k a

end GlobalTheory.CompanionTheory.GunrLevChars

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr.TraceDual

open NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

section Abstract

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

theorem repr_mul_mem (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) {x y : A}
    (hx : ∀ k, b.repr x k ∈ O) (hy : ∀ k, b.repr y k ∈ O) (k : Fin d) :
    b.repr (x * y) k ∈ O := by
  have hxy : x * y = ∑ i, ∑ j, (b.repr x i * b.repr y j) • (b i * b j) := by
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have h : b.repr (x * y) k = ∑ i, ∑ j, b.repr x i * b.repr y j * b.repr (b i * b j) k := by
    rw [hxy]

    simp [map_sum, Finsupp.finsetSum_apply]
  rw [h]
  exact O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hx i) (hy j)) (hc i j k)

theorem repr_basis_mem (O : Subring K) (b : Module.Basis (Fin d) K A) (j k : Fin d) :
    b.repr (b j) k ∈ O := by
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

theorem trace_mem (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) {x : A} (hx : ∀ k, b.repr x k ∈ O) :
    Algebra.trace K A x ∈ O := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine O.sum_mem fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_mul_mem O b hc hx (repr_basis_mem O b i) i

theorem adjugate_mem (O : Subring K) (M : Matrix (Fin d) (Fin d) K) (hM : ∀ i j, M i j ∈ O) (i j : Fin d) :
    M.adjugate i j ∈ O := by
  let N : Matrix (Fin d) (Fin d) O := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hN : O.subtype.mapMatrix N = M := by
    ext i j
    rfl
  rw [← hN, ← RingHom.map_adjugate]
  exact (N.adjugate i j).2

theorem dual_iff (O : Subring K) (b : Module.Basis (Fin d) K A)
    (hc : ∀ i j k, b.repr (b i * b j) k ∈ O) (u : K) (huO : u ∈ O)
    (hu : u * (Algebra.traceMatrix K b).det = 1) (a : A) :
    (∀ y : A, (∀ k, b.repr y k ∈ O) → Algebra.trace K A (a * y) ∈ O) ↔ ∀ k, b.repr a k ∈ O := by
  constructor
  · intro h k
    set M := Algebra.traceMatrix K b with hMdef
    have hMij : ∀ i j, M i j = Algebra.trace K A (b i * b j) := fun i j => by
      simp [hMdef, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    have hMO : ∀ i j, M i j ∈ O := fun i j => by
      rw [hMij]
      exact trace_mem O b hc (hc i j)
    let c : Fin d → K := fun i => b.repr a i
    let t : Fin d → K := fun j => Algebra.trace K A (a * b j)
    have ht : Matrix.vecMul c M = t := by
      funext j
      have ha : a * b j = ∑ i, c i • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr a, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
      simp only [t, Matrix.vecMul, dotProduct, hMij]

      rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
    have hc' : M.det • c = Matrix.vecMul t M.adjugate := by
      rw [← ht, Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
    have hk : b.repr a k = u * ∑ j, t j * M.adjugate j k := by
      have h1 := congrFun hc' k
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct] at h1
      rw [← h1, ← mul_assoc, hu, one_mul]
    rw [hk]
    refine O.mul_mem huO (O.sum_mem fun j _ => O.mul_mem ?_ (adjugate_mem O M hMO j k))
    exact h _ (repr_basis_mem O b j)
  · intro ha y hy
    exact trace_mem O b hc (repr_mul_mem O b hc ha hy)

end Abstract

section Base

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K : Type*} [Field K] [Algebra F K] {d : ℕ}

theorem trace_one_tmul [FiniteDimensional F E] (e : E) :
    Algebra.trace K (K ⊗[F] E) ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem traceMatrix_base (bs : Module.Basis (Fin d) F E) :
    Algebra.traceMatrix K (Algebra.TensorProduct.basis K bs) =
      (Algebra.traceMatrix F bs).map (algebraMap F K) := by
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite bs
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul]

theorem det_traceMatrix_base (bs : Module.Basis (Fin d) F E) :
    (Algebra.traceMatrix K (Algebra.TensorProduct.basis K bs)).det =
      algebraMap F K (Algebra.discr F (⇑bs)) := by
  rw [traceMatrix_base, Algebra.discr_def, RingHom.map_det]
  rfl

theorem repr_base (bs : Module.Basis (Fin d) F E) (i j k : Fin d) :
    (Algebra.TensorProduct.basis K bs).repr
        (Algebra.TensorProduct.basis K bs i * Algebra.TensorProduct.basis K bs j) k =
      algebraMap F K (bs.repr (bs i * bs j) k) := by
  simp [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.basis_repr_tmul]

end Base

theorem traceDualAt : TraceDualAt := by
  intro F E _ _ _ _ _ σ _ d bs v hv a
  let O : Subring (Fv F v) := (v.adicCompletionIntegers F).toSubring
  have hc : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) bs).repr
      (Algebra.TensorProduct.basis (Fv F v) bs i * Algebra.TensorProduct.basis (Fv F v) bs j) k ∈ O := by
    intro i j k
    rw [repr_base]
    refine hv _ ?_
    simp only [basisSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl ⟨(i, j, k), rfl⟩))
  have hD : Algebra.discr F (⇑bs) ≠ 0 := by
    exact Algebra.discr_not_zero_of_basis F bs
  have hu : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ O := by
    refine hv _ ?_
    simp [basisSet]
  have h1 : algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ *
      (Algebra.traceMatrix (Fv F v) (Algebra.TensorProduct.basis (Fv F v) bs)).det = 1 := by
    rw [det_traceMatrix_base, ← map_mul, inv_mul_cancel₀ hD, map_one]
  have key := dual_iff O (Algebra.TensorProduct.basis (Fv F v) bs) hc _ hu h1 a
  exact key

end GlobalTheory.CompanionTheory.Gunr.TraceDual

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrClassLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem coe_mul_pS_pow (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (t : S) :
    ((t * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (t : Fv F v ⊗[F] E) := by
  rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
  rfl

theorem smul_sub_mem_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (s s' : S) :
    (ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E) ∈ S ↔ s - s' ∈ lev hG.pS k := by
  have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hG.unif_ne
  constructor
  · intro h
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [coe_mul_pS_pow hG]
    show (ϖ ^ k) • ((ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E)) = (s : Fv F v ⊗[F] E) - s'
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have e : (s : Fv F v ⊗[F] E) - (s' : Fv F v ⊗[F] E) = (ϖ ^ k) • (c : Fv F v ⊗[F] E) := by
      rw [← coe_mul_pS_pow hG, hc, AddSubgroupClass.coe_sub]
    rw [← smul_sub, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact c.2

theorem classLev : ClassLev := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG k X X' hX hX'
  constructor
  · intro h
    refine Matrix.ext fun a b => ?_
    exact Ideal.Quotient.eq.2 ((smul_sub_mem_iff hG k (X a b) (X' a b)).1 (h a b))
  · intro h a b
    exact (smul_sub_mem_iff hG k (X a b) (X' a b)).2 (Ideal.Quotient.eq.1 (congrFun (congrFun h a) b))

end GlobalTheory.CompanionTheory.GunrClassLev

end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrExhaust

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter _root_.Topology
open PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_pow_mul_mem {v : HeightOneSpectrum (𝓞 F)} {ϖ : Fv F v} (h : ‖ϖ‖ < 1) (c : Fv F v) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k * c ∈ v.adicCompletionIntegers F := by
  have h0 : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k * ‖c‖) atTop (𝓝 (0 * ‖c‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h).mul_const _
  rw [zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds one_pos)] with k hk
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_mul, norm_pow]
  exact hk.le

theorem eventually_smul_mem {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
    {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ} (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v ⊗[F] E) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k • x ∈ S := by
  have h : ∀ᶠ k : ℕ in atTop, ∀ i, ϖ ^ k * (Algebra.TensorProduct.basis (Fv F v) bs).repr x i ∈
      v.adicCompletionIntegers F :=
    eventually_all.2 fun i => eventually_pow_mul_mem hG.unif_lt _
  filter_upwards [h] with k hk
  have hmem : ϖ ^ k • x ∈ (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    intro i
    simpa [map_smul] using hk i
  exact hmem

theorem exhaust : Exhaust := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG b
  have h : ∀ᶠ k : ℕ in atTop, ∀ a c, ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ S :=
    eventually_all.2 fun a => eventually_all.2 fun c => eventually_smul_mem hG _
  obtain ⟨k, hk⟩ := h.exists
  have hX : PositivityTheory.PfSWUS.Loc.cT σS (Matrix.of fun a c => (⟨_, hk a c⟩ : S)) = Matrix.of fun a c => (⟨_, hk a c⟩ : S) := by
    ext a c
    have hb := b.2 a c
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hG.sig]
    simp only [sigR_smul]
    exact congrArg _ hb
  refine ⟨k, _, hX, ?_⟩
  apply Subtype.ext
  funext a c
  show (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c = (ϖ ^ k)⁻¹ • ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hG.unif_ne), one_smul]

end GlobalTheory.CompanionTheory.GunrExhaust

end
end
