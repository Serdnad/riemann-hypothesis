module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle416
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.Columns.Bundle028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.Columns.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle003
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSemis

open Module

section Lin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_baseChange_map (L : Type) [Field L] [Algebra K L] (f : Module.End K V) (p : K[X]) :
    aeval (f.baseChange L) (p.map (algebraMap K L)) = (aeval f p).baseChange L := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add (f := _), map_add (f := _), hp, hr, map_add (f := _), LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

theorem isSemisimple_baseChange [CharZero K] [FiniteDimensional K V] (f : Module.End K V)
    (hsq : Squarefree (minpoly K f)) (L : Type) [Field L] [Algebra K L] :
    Module.End.IsSemisimple (f.baseChange L) := by
  have hsep : (minpoly K f).Separable := PerfectField.separable_iff_squarefree.2 hsq
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (hsep.map (f := algebraMap K L)).squarefree
  rw [aeval_baseChange_map, minpoly.aeval, LinearMap.baseChange_zero]

variable {U : Type} [AddCommGroup U] [Module ℂ U] {σ : K →+* ℂ} (φ : V →ₛₗ[σ] U) (T : Module.End K V)
  (S : Module.End ℂ U) (h : ∀ x, φ (T x) = S (φ x))
include h

theorem map_pow_apply (n : ℕ) (x : V) : φ ((T ^ n) x) = (S ^ n) (φ x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]

theorem map_aeval_apply (p : K[X]) (x : V) : φ (aeval T p x) = aeval S (p.map σ) (φ x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), hp, hq, Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply]
  | monomial n c =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smulₛₗ, map_pow_apply φ T S h]

end Lin

end GlobalTheory.HeckeSemis

noncomputable section

namespace GlobalTheory.HeckeSemis

open Module

variable {U : Type} [AddCommGroup U] [Module ℂ U]

theorem isSemisimple_of_sq [FiniteDimensional ℂ U] (S : Module.End ℂ U)
    (h : ∀ (μ : ℂ) (u : U), S (S u - μ • u) = μ • (S u - μ • u) → S u = μ • u) : S.IsSemisimple := by
  apply GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top S]
  refine iSup_mono fun μ => ?_
  intro u hu
  have hA : ∀ v, (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) v) = 0 → (S - μ • 1 : Module.End ℂ U) v = 0 := by
    intro v hv
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [sub_eq_zero] at hv ⊢
    exact h μ v hv
  have step : ∀ k v, ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v = 0 → (S - μ • 1 : Module.End ℂ U) v = 0 := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      apply ih
      have e1 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1 + 1)) v =
          (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v)) := by
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      have e2 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v =
          (S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v) := by
        rw [pow_succ', Module.End.mul_apply]
      rw [e2]
      exact hA _ (e1 ▸ hv)
  rw [Module.End.mem_maxGenEigenspace] at hu
  obtain ⟨k, hk⟩ := hu
  rw [Module.End.mem_eigenspace_iff]
  have hz : (S - μ • 1 : Module.End ℂ U) u = 0 := by
    cases k with
    | zero => simp at hk; simp [hk]
    | succ k => exact step k u hk
  simpa [sub_eq_zero] using hz

theorem apply_eq_zero_of_sq [FiniteDimensional ℂ U] {A : Module.End ℂ U} (hA : A.IsSemisimple) {u : U}
    (hu : A (A u) = 0) : A u = 0 := by
  have h1 : u ∈ A.maxGenEigenspace 0 := by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨2, by simpa [pow_two] using hu⟩
  rw [hA.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff] at h1
  simpa using h1

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}

theorem squarefree_minpoly [FiniteDimensional K V] [FiniteDimensional ℂ U] (φ : V →ₛₗ[σ] U)
    (hφ : Function.Injective φ) (T : Module.End K V) (S : Module.End ℂ U) (h : ∀ x, φ (T x) = S (φ x))
    (hS : S.IsSemisimple) : Squarefree (minpoly K T) := by
  intro p hp
  obtain ⟨r, hr⟩ := hp
  have key : aeval T (p * r) = 0 := by
    ext x
    have hm : aeval T (minpoly K T) = 0 := minpoly.aeval K T
    rw [hr] at hm
    have h0 : aeval T p (aeval T p (aeval T r x)) = 0 := by
      have := LinearMap.congr_fun hm x
      simpa [map_mul, Module.End.mul_apply] using this
    have h1 : aeval S (p.map σ) (aeval S (p.map σ) (φ (aeval T r x))) = 0 := by
      rw [← map_aeval_apply φ T S h, ← map_aeval_apply φ T S h, h0, map_zero]
    have h2 := apply_eq_zero_of_sq (hS.aeval (p.map σ)) h1
    rw [← map_aeval_apply φ T S h] at h2
    have h3 : aeval T p (aeval T r x) = 0 := hφ (by rw [h2, map_zero])
    simpa [map_mul, Module.End.mul_apply] using h3
  have hdvd := minpoly.dvd K T key
  have hm0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  rw [hr] at hdvd hm0
  have hne : p * r ≠ 0 := fun h => hm0 (by rw [mul_assoc, h, mul_zero])
  have h3 : p * (p * r) ∣ 1 * (p * r) := by rw [one_mul, ← mul_assoc]; exact hdvd
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).1 h3)

end GlobalTheory.HeckeSemis

namespace GlobalTheory.HeckeLocN

open Module

theorem finiteDimensional_MtL (D : D7) (μ : D.what₂.Tup) (j : ℕ) : FiniteDimensional D.what₂.LL (D.what₂.MtL μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))).1
  haveI := hli.finite
  exact Module.Finite.of_basis (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  set b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hli := (D.what₂.jMt_basis μ j b).1
  haveI := hli.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have e : D.what₂.jMt μ j x = ∑ i, D.what₂.embLL (b.repr x i) • D.what₂.jMt μ j (b i) := by
    conv_lhs => rw [← b.sum_repr x]

    rw [map_sum]
    simp [LinearMap.map_smulₛₗ]
  rw [e] at hx
  have hc := Fintype.linearIndependent_iff.1 hli _ hx
  apply b.repr.injective
  ext i
  simpa using hc i

theorem semisimpleTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → (∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f) → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → SemisimpleTw (base M C hR X hS) := by
  intro D M C hR X hS hStd hJord hGen hSpl
  intro j w h1 h2 _ v k hg
  obtain ⟨B, hBO, hBv⟩ := hGen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hSpl v hg.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hst := hStd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hjo := hJord D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  set Mr := M (D.what₂.muTw w) j h1 h2 with hMr
  have t0 : NG.tN Mr.J s ϖ k (0 : GAf D.host.E D.R.nV → Mr.wt.W) = 0 := by
    have e := hst.2.1 0 (zero_mem _) 0 (zero_mem _) 1
    simp only [one_smul, add_zero] at e
    exact left_eq_add.mp e
  let S : Module.End ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) :=
    { toFun := fun f => ⟨NG.tN Mr.J s ϖ k f, hst.1 f f.2⟩
      map_add' := fun f g => Subtype.ext (by simpa using hst.2.1 f f.2 g g.2 1)
      map_smul' := fun c f => Subtype.ext (by
        have e := hst.2.1 f f.2 0 (zero_mem _) c
        simpa [t0] using e) }
  haveI : FiniteDimensional ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) := by
    rw [← Mr.real_range]; infer_instance
  haveI := finiteDimensional_MtL D (D.what₂.muTw w) j
  have hmem : ∀ x, Mr.real (D.what₂.jMt (D.what₂.muTw w) j x) ∈ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ := fun x => by
    rw [← Mr.real_range]; exact LinearMap.mem_range_self _ _
  let φ : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[D.what₂.embLL] NG.TypeSp Mr.wt.ρ Mr.J Mr.χ :=
    { toFun := fun x => ⟨Mr.real (D.what₂.jMt _ j x), hmem x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp [LinearMap.map_smulₛₗ]) }
  have hφ : Function.Injective φ := fun x y hxy =>
    jMt_injective D _ j (Mr.real_inj (congrArg Subtype.val hxy))
  have hcomm : ∀ x, φ (hLC (mt0 M) C.Q hR j w v k x) = S (φ x) := fun x =>
    Subtype.ext (hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu x)
  have hSs : S.IsSemisimple := GlobalTheory.HeckeSemis.isSemisimple_of_sq S (fun μ u hμ => Subtype.ext (by
    have e : NG.tN Mr.J s ϖ k (↑(S u - μ • u)) = μ • (↑(S u - μ • u) : GAf D.host.E D.R.nV → Mr.wt.W) :=
      congrArg Subtype.val hμ
    rw [Submodule.coe_sub, Submodule.coe_smul] at e
    exact hjo u u.2 μ e))
  have hsq := GlobalTheory.HeckeSemis.squarefree_minpoly φ hφ (hLC (mt0 M) C.Q hR j w v k) S hcomm hSs
  haveI : CharZero D.what₂.LL := RingHom.charZero D.what₂.embLL
  exact GlobalTheory.HeckeSemis.isSemisimple_baseChange _ hsq (FractionRing (OcC X j w))
end GlobalTheory.HeckeLocN
end
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory

theorem ambSpace_map_eq_sum {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} (A : HLat K)
    {W : Type} [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W) (x : A.V) :
    j x = ∑ i, σ (A.b.repr x i) • j (A.b i) := by
  conv_lhs => rw [← A.b.sum_repr x]

  rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

private lemma exists_linearEquiv_euclidean_norm_eq_mulVec {ι W : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup W]
    [Module ℂ W] (bW : Module.Basis ι ℂ W) (N : Matrix ι ι ℂ) (hN : IsUnit N.det) :
    ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ w, ‖g w‖ = Real.sqrt (∑ i, ‖(N.mulVec (bW.equivFun w)) i‖ ^ 2) := by
  letI := Matrix.invertibleOfIsUnitDet N hN
  let e₂ : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) := Matrix.toLinearEquiv' N this
  let e₃ : (ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ ι := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  let e₄ : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, bW.equivFun.trans (e₂.trans (e₃.trans e₄.toLinearEquiv)), fun w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  rfl

theorem exists_equiv_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  intro K _ _ _ σ A W _ _ j hX hli hsp
  let bW : Module.Basis A.ι ℂ W := Module.Basis.mk hli (by rw [hsp])
  have hc : ∀ x, bW.equivFun (j x) = fun i => σ (A.b.repr x i) := by
    intro x
    have hx : j x = bW.equivFun.symm (fun i => σ (A.b.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply, ambSpace_map_eq_sum]
      simp [bW, Module.Basis.mk_apply]
    rw [hx, LinearEquiv.apply_symm_apply]
  have hU : IsUnit ((A.X (InfinitePlace.mk σ))⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX _)
  have hv : ∀ x, Formalism.HermitianLatticesTheory.vecAt A.b (InfinitePlace.mk σ) x =
      fun i => (InfinitePlace.mk σ).embedding (A.b.repr x i) := fun x => rfl
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (A.X (InfinitePlace.mk σ))⁻¹ hU
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
  · have hU' : IsUnit (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det := by
      have e : (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det =
          starRingEnd ℂ ((A.X (InfinitePlace.mk σ))⁻¹).det := (RingHom.map_det _ _).symm
      rw [e]
      exact hU.map _
    obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)) hU'
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1

    simp [Matrix.mulVec, dotProduct, map_sum, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem pos_iff_side_mem_max {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0)
    (e : ↥D.LL0 →+* FractionRing (D.ntw.O0 (c.twI w)))
    (he : e = if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y = e (x : ↥D.LL0) := by
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have e1 := h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])
  simp only [map_one, mul_one] at e1
  rw [hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]
  exact ⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩

theorem resChar_eq_of_pos {D : D7} (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hq := D.what₂.places.resChar_prime w
  have hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (D.what₂.places.val w).map_le_add ih (by simp)
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hnat m
  have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
  have h2 : 0 < D.what₂.places.val w 1 := by
    rw [← h1]
    refine (D.what₂.places.val w).map_lt_add ?_ ?_
    · rw [AddValuation.map_mul]; exact hq0.trans_le (le_add_of_nonneg_left (hint a))
    · rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b))
  simp at h2

theorem twCoverPair_of_tie (D : D7) (c : NChoice D) (h : NChTie D c) : TwCoverPair D := by
  rintro p hp w hw ⟨w', -, hw'⟩
  refine ⟨c.twI w', ?_, ?_⟩
  · rw [c.twI_l]
    refine resChar_eq_of_pos w' hp ?_
    simpa using (hw' _).1 hw
  · cases hs : c.sd w'
    · exact Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))
    · exact Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))

end GlobalTheory.Mem.Top

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

open Formalism.UG Formalism.MainNotions

namespace GlobalTheory.Mem.ColAd.LevGrp

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem decoRaw_mul_levelIwahori_reduction (g z : GL (Fin n) (AfE F E)) (hz : z ∈ J0 hc n ST) :
    decoRaw ST SG (g * z) = (decoRaw ST SG g).act 1 (redG hc n ST SG ⟨z, hz⟩)⁻¹ := by
  have h := decoRaw_rawSm hc ST SG 1 (⟨z, hz⟩⁻¹ : J0 hc n ST) g
  rw [map_one, map_inv] at h
  have e : Formalism.UG.bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * g *
      (((⟨z, hz⟩⁻¹ : J0 hc n ST) : J0 hc n ST) : GL (Fin n) (AfE F E))⁻¹ = g * z := by
    simp
  rw [e] at h
  exact h

end Gen

section Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) [NeZero n]

end Top

end GlobalTheory.Mem.ColAd.LevGrp

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd.LevGrp

end GlobalTheory.Mem.Col2.TC
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem lamExp_of_princ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : ↥H, lam x ^ m = 1 := by
  set L : Subgroup ↥(GLint E n P) := lam.ker.map H.subtype with hL
  have hfin : Finite (↥(GLint E n P) ⧸ L) := tfFinite_of_princ P N hN L fun g hg =>
    ⟨⟨g, (hH g hg).choose⟩, (hH g hg).choose_spec, rfl⟩
  have hLi : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hrel := Subgroup.relIndex_mul_index hLH
  have hsub : L.subgroupOf H = lam.ker := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hki : lam.ker.index ≠ 0 := by
    intro h0
    apply hLi
    rw [← hrel, Subgroup.relIndex, hsub, h0, zero_mul]
  refine ⟨lam.ker.index, Nat.pos_of_ne_zero hki, fun x => ?_⟩
  have := Subgroup.pow_index_mem lam.ker x
  rw [MonoidHom.mem_ker, map_pow] at this
  exact this

theorem qbLoc_chr_exp {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q) : ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  obtain ⟨N, hN, hH⟩ := hΘ P
  obtain ⟨m, hm, hx⟩ := lamExp_of_princ P.1 N hN (Θ P).H (Θ P).lam hH
  exact ⟨m, hm, fun k => hx _⟩

end GlobalTheory.Mem.Col2.ChEx
end
