module

public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.NonGenericAndKTwoTheorems
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Formalism.LocalToGlobal.Divisibility.Bundle002

@[expose] public section

section

open Module
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.L2.Indef

theorem mem_range_adjoint_of_ker_stable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (Θ : E →ₗ[ℂ] F) (T T' : E →ₗ[ℂ] E) (hT' : T' = LinearMap.adjoint T)
    (hker : ∀ u, Θ u = 0 → Θ (T' u) = 0) {y : E} (hy : y ∈ LinearMap.range (LinearMap.adjoint Θ)) :
    T y ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range (LinearMap.adjoint Θ)), Submodule.mem_orthogonal]
  intro v hv
  have hΘv : Θ v = 0 := by
    have h := (Submodule.mem_orthogonal _ _).1 hv (LinearMap.adjoint Θ (Θ v)) ⟨Θ v, rfl⟩
    rw [LinearMap.adjoint_inner_left] at h
    exact inner_self_eq_zero.1 h
  rw [← LinearMap.adjoint_inner_left, ← hT', LinearMap.adjoint_inner_right, hker v hΘv, inner_zero_left]

theorem semilin_comp_eq_constr {ι k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module ℂ W]
    {σ : k →+* ℂ} (b : Basis ι k V) (j : V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : ⊤ ≤ Submodule.span ℂ (Set.range fun i => j (b i))) (f : V →ₗ[k] V) (x : V) :
    j (f x) = (Basis.mk hli hsp).constr ℂ (fun i => j (f (b i))) (j x) := by
  have h := b.ext (f₁ := j.comp f)
    (f₂ := ((Basis.mk hli hsp).constr ℂ (fun i => j (f (b i)))).comp j) (fun i => by
      simp only [LinearMap.comp_apply]
      rw [show j (b i) = Basis.mk hli hsp i from (Basis.mk_apply hli hsp i).symm, Basis.constr_basis])
  exact LinearMap.congr_fun h x

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem jR_opR (hR : X.KFormR) (t : Bs.Tup) (i : A.OpR t) (x : A.FR t) :
    X.jR t (A.opR t i x) = X.opC t i (X.jR t x) := by
  unfold opC
  rw [dite_eq_left (hR t)]
  exact semilin_comp_eq_constr _ (X.jR t) (hR t).1 (hR t).2.ge (A.opR t i) x

theorem jL_opL (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (i : A.OpL j t) (x : A.FL j t) :
    X.jL j t (A.opL j t i x) = X.opLC j t i (X.jL j t x) := by
  unfold opLC
  rw [dite_eq_left (hL j t)]
  exact semilin_comp_eq_constr _ (X.jL j t) (hL j t).1 (hL j t).2.ge (A.opL j t i) x

theorem cutStable : X.CutStable := by
  intro hR hL hkR hkL haR haL
  unfold DefSub.Stable
  refine ⟨fun t i => ?_, fun j t i => ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    show X.jR t (A.opR t i x) ∈ LinearMap.range (LinearMap.adjoint (X.Θ t))
    rw [jR_opR X hR]
    obtain ⟨i', hi'⟩ := haR t i
    exact mem_range_adjoint_of_ker_stable (X.Θ t) (X.opC t i) (X.opC t i') hi'
      (fun u hu => hkR t i' u hu) (y := X.jR t x) hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    show X.jL j t (A.opL j t i x) ∈ LinearMap.range (LinearMap.adjoint (X.θ' j t))
    rw [jL_opL X hL]
    obtain ⟨i', hi'⟩ := haL j t i
    exact mem_range_adjoint_of_ker_stable (X.θ' j t) (X.opLC j t i) (X.opLC j t i') hi'
      (fun u hu => hkL j t i' u hu) (y := X.jL j t x) hx

end CxData

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {K : Type} [Field K] {σ : K →+* ℂ}

def cxSys {I : Type} (σ : K →+* ℂ) (C : (I → K) → Prop) : (I → ℂ) → Prop :=
  fun y => ∃ x, C x ∧ y = fun i => σ (x i)

variable {V E : Type} [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]

theorem map_pow_sub (f : V →ₛₗ[σ] E) (T : Module.End K V) (S : Module.End ℂ E)
    (h : ∀ v, f (T v) = S (f v)) (a : K) (k : ℕ) (v : V) :
    f (((T - a • 1) ^ k) v) = ((S - σ a • 1) ^ k) (f v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smulₛₗ, h]

theorem map_maxGen (f : V →ₛₗ[σ] E) {T : Module.End K V} {S : Module.End ℂ E}
    (h : ∀ v, f (T v) = S (f v)) {a : K} {v : V} (hv : v ∈ T.maxGenEigenspace a) :
    f v ∈ S.maxGenEigenspace (σ a) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  exact ⟨k, by rw [← map_pow_sub f T S h a k v, hk, map_zero]⟩

variable {I : Type}

theorem map_eigAt (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) {x : I → K} {v : V} (hv : v ∈ eigAt op x) :
    f v ∈ eigAt h (fun i => σ (x i)) := by
  unfold eigAt at hv ⊢
  rw [Submodule.mem_iInf] at hv ⊢
  exact fun i => map_maxGen f (hf i) (hv i)

theorem eigSum_le_comap_semi (f : V →ₛₗ[σ] E) {op : I → Module.End K V} {h : I → Module.End ℂ E}
    (hf : ∀ i v, f (op i v) = h i (f v)) (C : (I → K) → Prop) :
    eigSum op C ≤ (eigSum h (cxSys σ C)).comap f := by
  show (⨆ (x : I → K) (_ : C x), eigAt op x) ≤ _
  refine iSup₂_le fun x hx => ?_
  intro v hv
  rw [Submodule.mem_comap]
  exact eigAt_le_eigSum (op := h) ⟨x, hx, rfl⟩ (map_eigAt f hf hv)

theorem mem_eigSum_iff_map [FiniteDimensional K V] [FiniteDimensional ℂ E] (f : V →ₛₗ[σ] E)
    {op : I → Module.End K V} (hc : PairComm op) (hs : SplitOver op)
    {h : I → Module.End ℂ E} (hch : PairComm h) (hf : ∀ i v, f (op i v) = h i (f v))
    {Z : Submodule K V} (hZ : ∀ i, Z ≤ Z.comap (op i)) (hinj : ∀ z ∈ Z, f z = 0 → z = 0)
    (C : (I → K) → Prop) {v : V} (hv : v ∈ Z) :
    v ∈ eigSum op C ↔ f v ∈ eigSum h (cxSys σ C) := by
  constructor
  · intro hv'
    exact eigSum_le_comap_semi f hf C hv'
  · intro hfv
    have hpv : eigProj hc hs C v ∈ eigSum op C := eigProj_apply_mem hc hs C v
    have h2 : v - eigProj hc hs C v ∈ eigSum op (fun x => ¬ C x) := sub_eigProj_mem hc hs C v
    have hZ2 : v - eigProj hc hs C v ∈ Z := Z.sub_mem hv (eigProj_mem_of_stable hc hs C hZ hv)
    have hf1 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ C) := by
      rw [map_sub]
      exact Submodule.sub_mem _ hfv (eigSum_le_comap_semi f hf C hpv)
    have hf2 : f (v - eigProj hc hs C v) ∈ eigSum h (cxSys σ fun x => ¬ C x) :=
      eigSum_le_comap_semi f hf _ h2
    have hdis : Disjoint (eigSum h (cxSys σ C)) (eigSum h (cxSys σ fun x => ¬ C x)) := by
      apply disjoint_eigSum hch
      rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
      apply hx'
      have e : x' = x := funext fun i => (σ.injective (congrFun hxx i)).symm
      rw [e]
      exact hx
    have h0 : f (v - eigProj hc hs C v) = 0 := (Submodule.disjoint_def.1 hdis) _ hf1 hf2
    have e := hinj _ hZ2 h0
    rw [sub_eq_zero] at e
    rw [e]
    exact hpv

theorem inj_of_li {ι : Type*} (b : Basis ι K V) (f : V →ₛₗ[σ] E)
    (h : LinearIndependent ℂ fun k => f (b k)) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun v hv => ?_
  have e := b.linearCombination_repr v
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
  have h3 : ∑ i ∈ (b.repr v).support, σ (b.repr v i) • f (b i) = f v := by

    rw [← congrArg f e, map_sum]
    simp only [map_smulₛₗ]
  have hall := linearIndependent_iff'.1 h _ _ (h3.trans hv)
  have hr : b.repr v = 0 := by
    ext i
    by_contra hi
    exact hi (σ.injective ((hall i (Finsupp.mem_support_iff.2 hi)).trans (map_zero σ).symm))
  simpa using congrArg b.repr.symm hr

end Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem theta_jR_inj (hR : X.KFormR) (t : Bs.Tup) (z : A.FR t) (hz : z ∈ X.Z t)
    (h0 : X.Θ t (X.jR t z) = 0) : z = 0 := by
  simp only [CxData.Z, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jR t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bR (A := A) t) (X.jR t) (hR t).1 (h1.trans (map_zero _).symm)

theorem theta_jL_inj (hL : X.KFormL) (j : Bs.J) (t : Bs.Tup) (z : A.FL j t) (hz : z ∈ X.Zl j t)
    (h0 : X.θ' j t (X.jL j t z) = 0) : z = 0 := by
  simp only [CxData.Zl, Submodule.mem_comap, LinearMap.mem_range] at hz
  obtain ⟨w, hw⟩ := hz
  have h1 : X.jL j t z = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← hw, LinearMap.adjoint_inner_left, hw, h0, inner_zero_right]
  exact inj_of_li (bL (A := A) j t) (X.jL j t) (hL j t).1 (h1.trans (map_zero _).symm)

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt_eq (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, map_smulₛₗ, CxData.iC, lin, Fintype.linearCombination_apply, cpt]

theorem tC_cpt_eq (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

variable {A X}

theorem toF_mem_Z {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]
    exact Submodule.coe_mem _
  simp only [BlockDat.Z0, BlockDat.inV0, BlockDat.coord, Submodule.mem_comap, Submodule.mem_map,
    Matrix.mulVecLin_apply] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have e : B.toF ℓ Z y = w := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    rw [← hwe]
    simp
  rw [e]
  exact hw

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Concrete

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CxData

theorem rinv_spec {d n : ℕ} (P : Matrix (Fin d) (Fin n) K) (h : Function.Surjective P.mulVec) :
    P * rinv P = 1 := by
  have hex : ∃ R : Matrix (Fin n) (Fin d) K, P * R = 1 := by
    choose f hf using h
    refine ⟨Matrix.of fun i k => f (Pi.single k 1) i, ?_⟩
    ext i k
    have h1 := congrFun (hf (Pi.single k 1)) i
    rw [Pi.single_apply] at h1
    rw [Matrix.one_apply, ← h1]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  unfold rinv
  rw [dite_eq_left hex]
  exact hex.choose_spec

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

theorem cutPairing : X.CutPairing cr := by
  intro ζ sEE hW h2 hBt hMI hZ
  refine ⟨?_, fun u => by simp [colDef, colOf, hZ.1 u], fun u t => inv_ne_zero (hZ.2.1 u t),
    fun u w => ?_⟩
  swap
  · show vw w (ζ u (X.μ w))⁻¹ = 0
    rw [ValuationRepresentative.vw_inv, hZ.2.2 u w, neg_zero]
  intro u t φ F
  by_cases ht : t = Bs.μ0
  · subst ht
    show (fc X.zs).Dc.Pt u Bs.μ0 φ F =
      (ζ u Bs.μ0)⁻¹ * X.Bdef u φ ((X.rowMat cr true Bs.μ0).mulVec (((lv (fc X.zs) true).Pq Bs.μ0).mulVec F))
    rw [rowMat_base X cr true h2, Matrix.one_mulVec, hZ.1 u, inv_one, one_mul]
    show (fc X.zs).Dc.Pt u Bs.μ0 φ F = (fc X.zs).Dc.Pt u Bs.μ0 φ
      ((rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F))
    have hR := rinv_spec _ (hW.Pq_surj Bs.μ0)
    have hk : F - (rinv ((fc X.zs).Df1.Pq Bs.μ0)).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec F) ∈
        (fc X.zs).Df1.U Bs.μ0 := by
      rw [DefSide.U, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hR,
        Matrix.one_mulVec, sub_self]
    have h0 := hBt u φ _ hk
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · show (fc X.zs).Dc.Pt u t φ F = (ζ u t)⁻¹ * X.Bdef u φ ((X.rowMat cr true t).mulVec (((fc X.zs).Df1.Pq t).mulVec F))
    rw [← hMI u t ht φ F, ← mul_assoc, inv_mul_cancel₀ (hZ.2.1 u t), one_mul]

theorem cutTuples2 (C CH : ℝ) : X.CutTuples2 cr C CH := by
  intro hH0 hW1
  apply Formalism.IndefR.NonGenericAndKTwoTheorems.hecke_tuple_condition K Bs _ (X.data cr false) _
  · rintro w ⟨j, hj⟩
    show X.μ w ≠ Bs.μ0
    rw [← hH0.2 w]
    apply hW1
    rcases hj with h | h
    · by_contra hc
      apply h
      simp only [CxData.W1, not_exists, not_or, not_not] at hc
      obtain ⟨h1, h2, h3, -, -, -⟩ := hc j
      simp [Formalism.IndefR.HeckeTupleConditions.Atup, h1, h2, h3]
    · exact ⟨j, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact hH0.2

end CxData

end Formalism.IndefR.Cx
end
end
