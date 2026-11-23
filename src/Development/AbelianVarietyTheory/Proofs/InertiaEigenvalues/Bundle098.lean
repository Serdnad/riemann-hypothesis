module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isIntegral_residue_comap_involution_iff : ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A), IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔ IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | exact GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff | (intros; apply GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices : ∀ (K : UQ) (B : InvAlg K) (x : B.A), ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  first | exact @GlobalTheory.UnitLemma.TorusAction.torus_mem_X | exact GlobalTheory.UnitLemma.TorusAction.torus_mem_X | (intros; apply GlobalTheory.UnitLemma.TorusAction.torus_mem_X <;> assumption)
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

theorem _root_.GlobalTheory.T.exists_power_basis_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  first | exact @GlobalTheory.UnitLemma.exists_basis_pow_of_separable | exact GlobalTheory.UnitLemma.exists_basis_pow_of_separable | (intros; apply GlobalTheory.UnitLemma.exists_basis_pow_of_separable <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.UnitBase.exists_unit_base | exact GlobalTheory.UnitLemma.UnitBase.exists_unit_base | (intros; apply GlobalTheory.UnitLemma.UnitBase.exists_unit_base <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts : ∀ (K : UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u → ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧ (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧ (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧ ∀ x : K.E, val K.O (K.c x) = val K.O x := by
  first | exact @GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | exact GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | (intros; apply GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_aeval_eq_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm0 : minpoly E g ≠ 0 := minpoly.ne_zero hint
  have hf : aeval (LinearMap.mulLeft E g) (minpoly E g) = 0 := by
    have := aeval_algHom_apply (Algebra.lmul E A) g (minpoly E g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hn : 0 < Module.finrank E A := Module.finrank_pos
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  have h2 : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g :=
    (hP.squarefree.dvd_pow_iff_dvd hn.ne').1 h1
  have h3 : Module.finrank E A ≤ (minpoly E g).natDegree := by
    have := natDegree_le_of_dvd h2 hm0
    rwa [LinearMap.charpoly_natDegree] at this
  have hli := linearIndependent_pow (K := E) g
  have h4 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h4
  haveI : Nonempty (Fin (minpoly E g).natDegree) := ⟨⟨0, by omega⟩⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; omega)
  have hle : Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin E {g}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g ∈ Algebra.adjoin E {g} := Algebra.subset_adjoin (Set.mem_singleton g)
    exact Subalgebra.pow_mem (Algebra.adjoin E {g}) hg (i : ℕ)
  have ha : a ∈ Algebra.adjoin E {g} := by
    have : a ∈ Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) := by
      rw [htop]; trivial
    exact hle this
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, hf.symm⟩

theorem InvAlg.exists_aeval_eq_of_separable :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f :=
  fun _ B hP a => exists_aeval_eq_of_charpoly_separable B.g hP a

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | exact GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul | (intros; apply GlobalTheory.UnitLemma.InvAlg.gramDet_eq_norm_mul <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isLocallyConstant_of_isStdChar {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) : IsLocallyConstant (fun t : F => ψ t) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have hs : ‖y - x‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have : y = x + (y - x) := by abel
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hs, mul_one]

def kerLinF {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : Et F E) (x : A.K) (y' : A.L) : A.L →ₗ[F] F where
  toFun y := Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y * y'))
  map_add' a b := by simp [star_add, add_mul, mul_add, map_add (f := _)]
  map_smul' c a := by
    have hc : star (algebraMap F A.L c) = algebraMap F A.L c := by
      rw [IsScalarTower.algebraMap_apply F A.K A.L]; exact A.star_K _
    have h1 : star (c • a) * y' = (algebraMap F A.K c) • (star a * y') := by
      rw [Algebra.smul_def, star_mul, hc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]; ring
    rw [h1, map_smul, smul_eq_mul, ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def, map_smul]
    rfl

theorem isLocallyConstant_psiK_kerL (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  have hl := isLocallyConstant_of_isStdChar ψ hψ
  refine ⟨?_, fun x y' => ?_⟩
  · have hc : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hl.comp_continuous hc
  · have hc : Continuous (kerLinF A x y') := IsModuleTopology.continuous_of_linearMap _
    exact hl.comp_continuous hc

end GlobalTheory.JR.Hyp
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.MulInv

theorem exists_nhds_one_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ →
    ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
  intro F E _ _ _ _ _ A φ hφ
  obtain ⟨h1, h2⟩ := hφ
  let bil : A.K →ₗ[F] A.L →ₗ[F] A.L :=
    (LinearMap.mul F A.L).flip ∘ₗ (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
  have hbil : Continuous fun p : A.K × A.L => bil p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hm : Continuous fun p : A.L × A.K => p.1 * algebraMap A.K A.L p.2 := by
    have := hbil.comp continuous_swap
    simpa [bil, Function.comp_def, mul_comm] using this
  have hl : IsLocallyConstant (fun p : A.L × A.K => (φ (p.1 * algebraMap A.K A.L p.2), φ p.1)) :=
    (h1.comp_continuous hm).prodMk (h1.comp_continuous continuous_fst)
  have ho : IsOpen ((fun p : A.L × A.K => (φ (p.1 * algebraMap A.K A.L p.2), φ p.1)) ⁻¹' {q | q.1 = q.2}) := hl _
  obtain ⟨u, v, -, hv, hu, h0, huv⟩ := generalized_tube_lemma (s := tsupport φ) (t := {(1 : A.K)}) h2
    isCompact_singleton ho (by rintro ⟨x, y⟩ ⟨-, hy⟩; simp at hy; simp [hy])
  refine ⟨v, hv.mem_nhds (h0 rfl), fun s hs s' hs' hss y => ?_⟩
  have key : ∀ x ∈ tsupport φ, ∀ t ∈ v, φ (x * algebraMap A.K A.L t) = φ x := fun x hx t ht =>
    huv (Set.mk_mem_prod (hu hx) ht)
  by_cases hy : y ∈ tsupport φ
  · exact key y hy s hs
  by_cases hy' : y * algebraMap A.K A.L s ∈ tsupport φ
  · have := key _ hy' s' hs'
    rw [mul_assoc, ← map_mul, hss, map_one, mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

end GlobalTheory.JR.MulInv
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

def bas (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [hG.2.1]; simp)

def pt (hG : A.IsGen τ p) (lam : F) (b c : A.K) : Gl r F :=
  (companion p, (bas A hG).equivFun b, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * c), lam)

def tm (hG : A.IsGen τ p) : A.Kˣ →* GL (Fin r) F :=
  Units.map (Algebra.leftMulMatrix (bas A hG)).toRingHom.toMonoidHom

def unitsMeas (μK : Measure A.K) : Measure A.Kˣ :=
  (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹).comap Units.val

def desc (M : Meas r F E)
    (hG : A.IsGen τ p) (lam : F) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (x : A.K × A.K) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem bas_apply (hG : A.IsGen τ p) (i : Fin r) : LinDesc.bas A hG i = τ ^ (i : ℕ) := by
  simp [LinDesc.bas]

theorem repr_sum (hG : A.IsGen τ p) (c : Fin r → F) :
    (LinDesc.bas A hG).repr (∑ i, c i • τ ^ (i : ℕ)) = Finsupp.equivFunOnFinite.symm c := by
  have : (∑ i, c i • τ ^ (i : ℕ)) = (LinDesc.bas A hG).equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]; simp [bas_apply]
  rw [this]
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]; simp

theorem leftMul_tau (hG : A.IsGen τ p) : Algebra.leftMulMatrix (LinDesc.bas A hG) τ = companion p := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, bas_apply, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj]
    have h3 : τ ^ r = ∑ k, (-p k) • τ ^ (k : ℕ) := by
      have := hG.2.2
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left this
    rw [h3, repr_sum]; simp
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    have h3 : τ ^ ((j : ℕ) + 1) = LinDesc.bas A hG ⟨(j : ℕ) + 1, hlt⟩ := by rw [bas_apply]
    rw [h3, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg]
      intro h; exact hi (by rw [← h])

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem tm_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Algebra.leftMulMatrix (bas A hG) (t : A.K) := rfl

theorem tm_inv_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    (((tm A hG t)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Algebra.leftMulMatrix (bas A hG) ((t⁻¹ : A.Kˣ) : A.K) := by
  rw [← map_inv]; rfl

theorem row_mul (hG : A.IsGen τ p) (s c : A.K) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* Algebra.leftMulMatrix (bas A hG) s =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]
  have hx := (bas A hG).sum_repr (s * bas A hG j)
  calc ∑ i : Fin r, Algebra.trace F A.K (τ ^ (i : ℕ) * c) * (bas A hG).repr (s * bas A hG j) i
      = Algebra.trace F A.K (∑ i : Fin r, ((bas A hG).repr (s * bas A hG j) i • bas A hG i) * c) := by

        rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]
    _ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
        rw [← Finset.sum_mul, hx, bas_apply]; ring_nf

theorem act_tm (hG : A.IsGen τ p) (lam : F) (t : A.Kˣ) (b c : A.K) :
    act (tm A hG t) (pt A hG lam b c) = pt A hG lam ((t : A.K) * b) (((t⁻¹ : A.Kˣ) : A.K) * c) := by
  unfold act pt
  rw [tm_inv_coe, tm_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← leftMul_tau A hG, ← map_mul, ← map_mul]; congr 1
    rw [mul_comm (t : A.K) τ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · simp only
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr _ _ _
  · exact row_mul A hG _ c

theorem det_tm (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = Algebra.norm F (t : A.K) := by
  rw [tm_coe, Algebra.norm_eq_matrix_det (bas A hG)]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  unfold act
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem act_one {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) : act 1 Y = Y := by
  unfold act; simp

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
theorem pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ a : A.K, LinDesc.pt A hG lam 1 a = sec (A.invK τ p lam a) := by
  intro F E _ _ _ _ _ A r τ p hG lam a
  unfold LinDesc.pt sec Et.invK
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  have h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩ := by
    simp [LinDesc.bas]
  simp only
  rw [h1, Module.Basis.equivFun_self]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
  · rw [if_neg hi, if_neg]
    intro h; exact hi (by rw [← h])
end GlobalTheory.JR.LinDesc
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)

def mulMat {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' ((j : A.L →ₗ[E] (Fin r → E)) ∘ₗ LinearMap.mulLeft E y ∘ₗ (j.symm : (Fin r → E) →ₗ[E] A.L))

theorem mulMat_mulVec {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) (v : Fin r → E) :
    A.mulMat j y *ᵥ v = j (y * j.symm v) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem mulMat_mulVec_apply {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y z : A.L) :
    A.mulMat j y *ᵥ j z = j (y * z) := by
  simp [mulMat_mulVec]

theorem mulMat_mul {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y y' : A.L) :
    A.mulMat j (y * y') = A.mulMat j y * A.mulMat j y' := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_assoc]

theorem mulMat_one {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) : A.mulMat j 1 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [mulMat_mulVec]

theorem mulMat_mem_unitaryGroup {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j)
    (t : unitary A.L) : A.mulMat j t ∈ Matrix.unitaryGroup (Fin r) E := by
  rw [Matrix.mem_unitaryGroup_iff']
  set N := star (A.mulMat j t) * A.mulMat j t
  have key : ∀ v w : Fin r → E, star v ⬝ᵥ (N *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    obtain ⟨a, rfl⟩ := j.surjective v
    obtain ⟨b, rfl⟩ := j.surjective w
    have h1 : star (j a) ⬝ᵥ (N *ᵥ j b) = star (A.mulMat j t *ᵥ j a) ⬝ᵥ (A.mulMat j t *ᵥ j b) := by
      simp only [N, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    rw [h1, mulMat_mulVec_apply, mulMat_mulVec_apply, hx, hx]
    congr 1
    have ht : star (t : A.L) * t = 1 := Unitary.star_mul_self_of_mem t.2
    calc algebraMap A.K A.L x * star ((t : A.L) * a) * ((t : A.L) * b)
        = algebraMap A.K A.L x * star a * b * (star (t : A.L) * t) := by rw [star_mul]; ring
      _ = _ := by rw [ht, mul_one]
  have hw : ∀ w, N *ᵥ w = w := by
    intro w
    funext i
    have := key (Pi.single i 1) w
    simpa [single_dotProduct] using this
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simp [hw]

def uHom {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) :
    unitary A.L →* Matrix.unitaryGroup (Fin r) E where
  toFun t := ⟨A.mulMat j t, A.mulMat_mem_unitaryGroup hx t⟩
  map_one' := by ext1; simp [mulMat_one]
  map_mul' t t' := by ext1; simp [mulMat_mul]

theorem uHom_apply {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (t : unitary A.L) :
    (A.uHom hx t : Matrix (Fin r) (Fin r) E) = A.mulMat j t := rfl

def descFn {r : ℕ} (M : GlobalTheory.JR.Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E))
    (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ) (f : Hn r F E → ℂ) (y : A.L) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g (Ax, j y, lam)) * (α g : ℂ) ∂M.μU

end GlobalTheory.JR.Et
end
end

section

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def WeilAt (A : Et F E) : Prop :=
  ∀ ψ : AddChar F ℂ, IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∃ γ W, A.IsWeil ψ x A.etaK μ γ W

def IsSplitting (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L) : Prop :=
  (∀ k : A.K, eL (algebraMap A.K A.L k) = (algebraMap A₁.K A₁.L (eK k).1, algebraMap A₂.K A₂.L (eK k).2)) ∧
  (∀ e : E, eL (algebraMap E A.L e) = (algebraMap E A₁.L e, algebraMap E A₂.L e)) ∧
  ∀ y : A.L, eL (star y) = (star (eL y).1, star (eL y).2)

end GlobalTheory.JR
end
end
