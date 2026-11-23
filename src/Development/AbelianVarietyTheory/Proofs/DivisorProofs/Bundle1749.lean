module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle667
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1713
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_pt_of_mem_cone_of_isAlgClosed : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → ∀ (K : Type) [Field K] [Algebra F K] [IsAlgClosed K] (y : Fin S.N → K), y ≠ 0 → (∀ g ∈ S.imageIdeal, aeval y g = 0) → ∃ (x : S.Pt K) (c : K), c ≠ 0 ∧ S.coords x.1 = c • y := by
  intro F _ S hS hb K _ _ _ y hy hI
  classical
  by_contra hno
  push_neg at hno
  have hT : (S.baseChange K).IsVariety := hS.baseChange K
  have hbT : (S.baseChange K).BasePointFree := hb.baseChange K
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hy
  change y i₀ ≠ 0 at hi₀
  let u : Fin S.N → Fin S.N → K := fun j => y i₀ • Pi.single j 1 - y j • Pi.single i₀ 1
  have hu : ∀ (j : Fin S.N) (c : Fin S.N → K), ∑ l, u j l * c l = y i₀ * c j - y j * c i₀ := fun j c => by
    simp [u, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, mul_assoc]

  have hcov : ∀ z : (S.baseChange K).Y, ∃ j, z ∈ nonzeroLocus ((S.baseChange K).comb (u j)) := by
    by_contra hc
    push_neg at hc
    obtain ⟨z, hz⟩ := hc
    have := hT.smooth
    have : Smooth (S.baseChange K).str := SmoothOfRelativeDimension.smooth (S.baseChange K).D _
    have hZ : IsClosed (⋂ j, ((nonzeroLocus ((S.baseChange K).comb (u j)) : Set (S.baseChange K).Y)ᶜ)) :=
      isClosed_iInter fun j => (nonzeroLocus ((S.baseChange K).comb (u j))).isOpen.isClosed_compl
    obtain ⟨a, ha, haZ⟩ := GlobalTheory.ConeOnto.exists_rat_pt (S.baseChange K).str hZ.isLocallyClosed
      (x := z) (Set.mem_iInter.2 hz)
    let xa : (S.baseChange K).Pt K := ⟨a, ha.trans (Spec.map_id _).symm⟩
    have hbase : (S.baseChange K).baseHom a = RingHom.id K := LinSys.baseHom_ptOver xa
    have hv : ∀ j, y i₀ * (S.baseChange K).coords a j - y j * (S.baseChange K).coords a i₀ = 0 := fun j => by
      have h0 := Set.mem_iInter.1 (haZ (IsLocalRing.closedPoint K)) j
      have h1 : (S.baseChange K).val a ((S.baseChange K).comb (u j)) = 0 :=
        not_not.1 fun h => h0 (((S.baseChange K).val_ne_zero_iff a _).1 h)
      have h2 := ((S.baseChange K).val_comb a (u j)).symm.trans h1
      rw [hbase] at h2
      simp only [RingHom.id_apply] at h2
      exact (hu j ((S.baseChange K).coords a)).symm.trans h2
    have hc0 : (S.baseChange K).coords a i₀ ≠ 0 := fun h0 => hbT.coords_ne_zero a (funext fun j => by
      have := hv j
      rw [h0, mul_zero, sub_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hi₀)
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange K a
    refine hno (LinSys.toBase xa) (c⁻¹ * ((S.baseChange K).coords a i₀ / y i₀))
      (mul_ne_zero (inv_ne_zero hc) (div_ne_zero hc0 hi₀)) (funext fun j => ?_)
    have ej := congrFun e j
    have hvj := hv j
    change S.coords (a ≫ S.bcFst K) j = _
    simp only [Pi.smul_apply, smul_eq_mul] at ej ⊢
    have e1 : S.coords (a ≫ S.bcFst K) j = c⁻¹ * (S.baseChange K).coords a j := by
      rw [ej, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have e2 : (S.baseChange K).coords a j = (S.baseChange K).coords a i₀ / y i₀ * y j := by
      field_simp
      linear_combination hvj
    rw [e1, e2]
    ring

  have hX : (X i₀ : MvPolynomial (Fin (S.baseChange K).N) K).IsHomogeneous 1 := isHomogeneous_X K i₀
  obtain ⟨m, A, hA, hrel⟩ := GlobalTheory.SecIntegral.exists_integral_relation K (S.baseChange K) hT S.N 1 u
    ((S.baseChange K).form hX) hcov
  let σ : Fin S.N → MvPolynomial (Fin S.N) K := fun i => ∑ j, C (u i j) * X j
  have hσ : ∀ i, (σ i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C (Fin S.N) (u i j)).mul (isHomogeneous_X K j)
  let G : MvPolynomial (Fin S.N) K := X i₀ ^ m + ∑ k : Fin m, bind₁ σ (A k) * X i₀ ^ (k : ℕ)
  have hG : G.IsHomogeneous m := by
    refine (isHomogeneous_X_pow i₀ m).add (IsHomogeneous.sum _ _ _ fun k _ => ?_)
    have h1 : (bind₁ σ (A k)).IsHomogeneous (1 * (1 * (m - k))) :=
      (hA k).eval₂ C σ (fun r => isHomogeneous_C _ r) hσ
    have h2 := h1.mul (isHomogeneous_X_pow i₀ (k : ℕ))
    have e : 1 * (1 * (m - (k : ℕ))) + k = m := by omega
    rwa [e] at h2

  haveI := HeightExists.isIntegral hT
  obtain ⟨Ω, _, _, xg, hxg, -⟩ := HeightExists.exists_generic hT
  have hmem : G ∈ (S.baseChange K).imageIdeal := by
    rw [imageIdeal_eq_coneIdeal_of_generic K Ω _ xg hxg 1 _ one_ne_zero (one_smul _ _).symm]
    refine (mem_coneIdeal_of_isHomogeneous (K := K) (N := S.N) _ hG).2 ?_
    have h := hrel Ω xg
    rw [LinSys.powVal_form, LinSys.baseHom_ptOver] at h
    erw [eval₂_X] at h
    let cg : Fin S.N → Ω := (S.baseChange K).coords xg.1
    have h' : cg i₀ ^ m + ∑ k : Fin m, aeval (fun i : Fin S.N => ∑ j : Fin S.N, algebraMap K Ω (u i j) * cg j) (A k) *
        cg i₀ ^ (k : ℕ) = 0 := h
    show aeval cg G = 0

    simp only [G, σ, map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_bind₁, aeval_C]
    exact h'

  rw [← HeightExists.map_imageIdeal hS K] at hmem
  have hker : S.imageIdeal.map (MvPolynomial.map (algebraMap F K)) ≤ RingHom.ker (eval y) :=
    Ideal.map_le_iff_le_comap.2 fun g hg => by
      rw [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.eval_map, ← aeval_def]
      exact hI g hg
  have h0 : eval y G = 0 := hker hmem
  have hA0 : ∀ k : Fin m, eval y (bind₁ σ (A k)) = 0 := fun k => by
    show aeval y (bind₁ σ (A k)) = 0
    rw [aeval_bind₁]
    have e : (fun i => aeval y (σ i)) = 0 := funext fun i => by

      simp only [σ, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, Pi.zero_apply]
      rw [hu i y]
      ring
    rw [e, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
    exact (hA k).coeff_eq_zero (d := 0) (by simp; omega)
  have h3 : eval y G = y i₀ ^ m := by

    simp only [G, map_add (f := _), map_pow, map_sum, map_mul, eval_X, hA0, zero_mul, Finset.sum_const_zero, add_zero]
  exact pow_ne_zero m hi₀ (h3.symm.trans h0)

end GlobalTheory.ConeOnto
end
end

section

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3.ReproPf

variable {n : ℕ} (ε : Fin n → Bool)

def pt (k : KG ε) : ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
  Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2))

theorem continuous_toMK : Continuous fun k : KG ε => toMK k :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_pt : Continuous (pt ε) := by
  refine continuous_pi fun v => ?_
  rcases v with x | x
  · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp (continuous_toMK ε))
  · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp (continuous_toMK ε)))

def evL : Poly n →ₗ[ℂ] (KG ε → ℂ) where
  toFun P k := eval (pt ε k) P
  map_add' P Q := by ext k; simp
  map_smul' c P := by ext k; simp [MvPolynomial.smul_eval]

theorem continuous_evL (P : Poly n) : Continuous (evL ε P) :=
  (MvPolynomial.continuous_eval P).comp (continuous_pt ε)

def Fd (d : ℕ) : Submodule ℂ (KG ε → ℂ) := (restrictTotalDegree _ ℂ d).map (evL ε)

instance (d : ℕ) : FiniteDimensional ℂ (Fd ε d) := by
  unfold Fd; infer_instance

theorem continuous_of_mem {d : ℕ} {f : KG ε → ℂ} (hf : f ∈ Fd ε d) : Continuous f := by
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.1 hf
  exact continuous_evL ε P

theorem integrable_of_cont {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem star_evL (P : Poly n) : ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧
    ∀ k, star (evL ε P k) = evL ε Q k := by
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) P), ?_, fun k => ?_⟩
  · exact (totalDegree_rename_le _ _).trans (Finset.sup_mono (support_map_subset _ _))
  · change (starRingEnd ℂ) (eval (pt ε k) P) = eval (pt ε k) (rename Sum.swap (map (starRingEnd ℂ) P))
    rw [eval_rename, eval_map, ← coe_eval₂Hom]
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p v hp =>
      simp only [map_mul, hp, eval_X, coe_eval₂Hom, eval₂_X]
      rcases v with x | x <;> simp [pt]

def gram (d : ℕ) : Fd ε d →ₗ[ℂ] Module.Dual ℂ (Fd ε d) :=
  LinearMap.mk₂ ℂ (fun g f => ∫ k, (g : KG ε → ℂ) k * (f : KG ε → ℂ) k ∂(muK ε))
    (fun g g' f => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f.2)))
        (integrable_of_cont ε ((continuous_of_mem ε g'.2).mul (continuous_of_mem ε f.2))))
    (fun c g f => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun g f f' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f.2)))
        (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f'.2))))
    (fun c g f => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact integral_const_mul c _)

theorem gram_injective (d : ℕ) : Function.Injective (gram ε d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  obtain ⟨P, hP, hgP⟩ := Submodule.mem_map.1 g.2
  obtain ⟨Q, hQ, hQk⟩ := star_evL ε P
  have hQm : evL ε Q ∈ Fd ε d :=
    Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).2
      (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)))
  have h0 := LinearMap.congr_fun hg ⟨evL ε Q, hQm⟩
  simp only [gram, LinearMap.mk₂_apply, LinearMap.zero_apply] at h0
  have hc : Continuous (g : KG ε → ℂ) := continuous_of_mem ε g.2
  have e1 : ∀ k, (g : KG ε → ℂ) k * evL ε Q k = ((‖(g : KG ε → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [← hQk, ← hgP, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  simp_rw [e1, integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  have hnn : 0 ≤ᵐ[muK ε] fun k => ‖(g : KG ε → ℂ) k‖ ^ 2 := Filter.Eventually.of_forall fun k => by positivity
  have hc2 : Continuous fun k => ‖(g : KG ε → ℂ) k‖ ^ 2 := hc.norm.pow 2
  have hint : Integrable (fun k => ‖(g : KG ε → ℂ) k‖ ^ 2) (muK ε) :=
    integrableOn_univ.1 (hc2.continuousOn.integrableOn_compact isCompact_univ)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  have hfun := (hc2.ae_eq_iff_eq (muK ε) continuous_const).1 hae
  ext k
  have h1 : ‖(g : KG ε → ℂ) k‖ ^ 2 = 0 := congrFun hfun k
  have h2 : (g : KG ε → ℂ) k = 0 := by simpa using h1
  simpa using h2

theorem fock_reproducing_formula : Repro := by
  intro n ε d
  have hfin : Module.finrank ℂ (Fd ε d) = Module.finrank ℂ (Module.Dual ℂ (Fd ε d)) :=
    (Subspace.dual_finrank_eq).symm
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 (gram_injective ε d)
  let Λ : Module.Dual ℂ (Fd ε d) := (LinearMap.proj (R := ℂ) (φ := fun _ : KG ε => ℂ) 1).comp (Fd ε d).subtype
  obtain ⟨g, hg⟩ := hs Λ
  obtain ⟨Q, hQ, hgQ⟩ := Submodule.mem_map.1 g.2
  refine ⟨Q, (mem_restrictTotalDegree _ _ _).1 hQ, fun P hP => ?_⟩
  have h := LinearMap.congr_fun hg ⟨evL ε P, Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).2 hP)⟩
  simp only [gram, LinearMap.mk₂_apply, Λ, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.proj_apply] at h
  rw [← hgQ] at h
  exact h.symm

end GlobalTheory.PsCo.Pc3.ReproPf

namespace GlobalTheory.PsCo.Pc3

theorem fock_reproducing_formula : Repro := ReproPf.fock_reproducing_formula

end GlobalTheory.PsCo.Pc3
end
end

section

noncomputable section

open MeasureTheory Filter Topology GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open Formalism.MainNotions.S (IsDS)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc1

def LocalPC4 : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), Gap4 r lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
      (hD : IsDS ε (fun a => (lam a : ℝ)) D) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
      ∃ f, GlobalTheory.PsCo.Pc.IsPC' ε lam μ D hD f

theorem eq_of_const_of_tendsto {a L : ℂ} {u : ℝ → ℂ} (h : ∀ t, 1 ≤ t → u t = a) (hL : Tendsto u atTop (𝓝 L)) : a = L :=
  tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun t ht => (h t ht).symm)) hL

theorem injective_of_regSS {n : ℕ} {z : Fin n → ℂ} (h : IsRegSS (Matrix.diagonal z)) : Function.Injective z := by
  rw [IsRegSS, Matrix.charpoly_diagonal] at h
  exact Polynomial.separable_prod_X_sub_C_iff.1 h

theorem dMode_ne_zero {n : ℕ} (ε : Fin n → Bool) {θ : Fin n → ℝ}
    (h : Function.Injective fun a => Complex.exp (θ a * Complex.I)) : (dMode ε θ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun e => ?_)))
  have h1 := x.2.1
  rw [h e, x.2.2] at h1
  exact Bool.noConfusion h1

theorem torusPt_mem_KG {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) : torusPt ε θ ∈ KG ε := by
  change toM (torusPt ε θ) ∈ Formalism.REAL.Kset ε
  have e : toM (torusPt ε θ) = Matrix.diagonal fun a => Complex.exp (θ a * Complex.I) := rfl
  rw [e]
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem localPC4_of (hAlg : StAlg) (hProf : StProfile) (hFam : StFam) (hHom : StHomot) (hLim : StLim)
    (hSh : StShape) (hOA : StOrbAd) (hOC : StOrbCpt) (hNE : StNonEll) (hTr : StTr) (hTA : StTrAd)
    (hK : StKData) : LocalPC4 := by
  intro r hr ε lam hgap X _ _ D hD μ _
  haveI := hD.1
  haveI := hD.2.1
  obtain ⟨M, P, hP, hcl, htor, hone, hzero⟩ := hK r hr ε lam hgap X D hD
  obtain ⟨p, q, hpq, htop⟩ := hAlg r ε M P hP
  obtain ⟨G, hG⟩ := hProf (nMode ε)
  obtain ⟨d, hd, hfam⟩ := hFam r ε G p hG
  obtain ⟨c, hc, hlim⟩ := hLim r ε μ G hG
  obtain ⟨hl1, hl2⟩ := hlim p
  let φ : ℝ → Mat r → ℂ := fun t => c⁻¹ • famF ε G p t
  have hφ : ∀ t, 1 ≤ t → φ t ∈ ShapeM ε d := fun t ht => Submodule.smul_mem _ _ (hfam t (by linarith)).1
  have hdiff : ∀ t, 1 ≤ t → φ 1 - φ t ∈ AdSpanM ε := fun t ht => by
    rw [← smul_sub]; exact Submodule.smul_mem _ _ (hHom r ε G p q hG hpq t ht)
  have hsum : ∀ t, (fun g : UJ ε => φ 1 (toM g)) = (fun g => φ t (toM g)) + fun g => (φ 1 - φ t) (toM g) :=
    fun t => funext fun g => by simp
  have key : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
      (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∃ (B : U →L[ℂ] U) (a : ℂ),
        (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • π k v ∂(muK ε)) ∧ HasTrace B a ∧
          HasTrace (repOp π μ fun g => φ 1 (toM g)) a := by
    intro U _ _ _ π hu hi
    obtain ⟨w, hw, hw1, hw2⟩ := hTr r ε μ U π hu hi d
    obtain ⟨B, hB, hBt⟩ := hw2 _ (hd _ le_rfl)
    rw [htop] at hB hBt
    refine ⟨B, _, hB, hBt, ?_⟩
    have hint : ∀ t, 1 ≤ t → Integrable (fun g : UJ ε => φ t (toM g) * w g) μ := fun t ht =>
      ((hSh r ε d _ (hφ t ht)).2.2.1.mul hw).integrable_of_hasCompactSupport (hSh r ε d _ (hφ t ht)).2.2.2.mul_right
    have hconst : ∀ t, 1 ≤ t → ∫ g, φ t (toM g) * w g ∂μ = ∫ g, φ 1 (toM g) * w g ∂μ := fun t ht => by
      have h1 := (hw1 _ (Submodule.sub_mem _ (hφ 1 le_rfl) (hφ t ht))).2
      rw [(hTA r ε μ U π hu hi _ (hdiff t ht)).2] at h1
      simp only [Pi.sub_apply, sub_mul] at h1
      rw [integral_sub (hint 1 le_rfl) (hint t ht)] at h1
      exact (sub_eq_zero.1 h1.symm).symm
    have hT := (hl1 w hw).const_mul c⁻¹
    rw [inv_mul_cancel_left₀ hc, htop] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ, mul_assoc])]
    exact hw1 _ (hφ 1 le_rfl)
  refine ⟨fun g => φ 1 (toM g), (hSh r ε d _ (hφ 1 le_rfl)).1, (hSh r ε d _ (hφ 1 le_rfl)).2.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, a, hB, hBa, h⟩ := key X (ujRep hD.2.2.1)
      (isUnitaryRep_repVia _ _ GlobalTheory.HCChar.continuous_ujMat)
      (isTopIrreducible_repVia _ _ (fun x hx => by
        have hJ : IsUnit x := by
          have h : x.conjTranspose * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
          have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
            rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
            congr 1; funext a; split_ifs <;> simp
          have h2 : (Formalism.REAL.Jm ε * x.conjTranspose * Formalism.REAL.Jm ε) * x = 1 := by
            rw [mul_assoc, mul_assoc, ← mul_assoc x.conjTranspose, h, hJ]
          exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse h2)
        exact ⟨⟨hJ.unit, hx⟩, rfl⟩) hD.2.2.2.1)
    rwa [hone B a hB hBa] at h
  · intro U _ _ _ π hu hi hne
    obtain ⟨B, a, hB, hBa, h⟩ := key U π hu hi
    rwa [hzero U π hu hi hne B a hB hBa] at h
  · intro s hs hnc dt _ _
    obtain ⟨R, hR, hx⟩ := hNE r ε s hs hnc
    have ht : (1 : ℝ) ≤ 1 + 2 / R := by have := div_pos two_pos hR; linarith
    have h0 : HasOrbInt μ s dt (fun g => φ (1 + 2 / R) (toM g)) 0 := by
      have e : conjFn s (fun g : UJ ε => φ (1 + 2 / R) (toM g)) = 0 := funext fun x => by
        have h1 : 1 < (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) := by
          have h2 : (1 + 2 / R) * R ≤ (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) :=
            mul_le_mul_of_nonneg_left (hx x) (by linarith)
          have h3 : (1 + 2 / R) * R = R + 2 := by field_simp
          linarith
        simp [conjFn, φ, (hfam _ (by linarith)).2 _ h1]
      rw [HasOrbInt, e]
      exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    rw [hsum (1 + 2 / R)]
    simpa using h0.add (hOA r ε μ s hs dt _ (hdiff _ ht))
  · intro s hs hcp y θ hy dt _ _
    have hreg : IsRegSS (ujMat ε (torusPt ε θ)) := by
      rw [← hy, IsRegSS, map_mul, Matrix.charpoly_mul_comm, ← map_mul, mul_inv_cancel_left]
      exact hs
    have hinj : Function.Injective fun a => Complex.exp (θ a * Complex.I) := injective_of_regSS hreg
    have hO := fun t (ht : 1 ≤ t) => hOC r ε μ s hs hcp dt y _ (hSh r ε d _ (hφ t ht)).2.2.1 (hSh r ε d _ (hφ t ht)).2.2.2
    rw [hy] at hO
    have hconst : ∀ t, 1 ≤ t → (∫ x, φ t (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) =
        (∫ x, φ 1 (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) := fun t ht => by
      have h1 := (hO t ht).add (hOA r ε μ s hs dt _ (hdiff t ht))
      rw [← hsum t, add_zero] at h1
      exact h1.2.symm.trans (hO 1 le_rfl).2
    have hT := ((hl2 θ (torusPt ε θ) rfl hinj fun k => by
      rw [htop]; exact hcl ⟨_, torusPt_mem_KG ε θ⟩ k).const_mul c⁻¹).div_const (dt.real Set.univ : ℂ)
    rw [htop, htor θ hinj, mul_div_assoc c, inv_mul_cancel_left₀ hc, mul_div_cancel_right₀ _ (dMode_ne_zero ε hinj)] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ])]
    exact hO 1 le_rfl

theorem localPC_of_steps : StAlg → StProfile → StFam → StHomot → StLim → StShape → StOrbAd → StOrbCpt → StNonEll → StTr →
    StTrAd → StKData → GlobalTheory.PsCo.Pc.LocalPC :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => localPC4_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end GlobalTheory.PsCo.Pc1
end
end

section

namespace GlobalTheory.PsCo.Pc3

theorem stR : StR := by
  intro n ε
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε
  exact ⟨hcont, hinv, GlobalTheory.T.pseudoUnitary_offDiag_norm_sq_zero_iff_mem_maxCompact n ε, GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε⟩

end GlobalTheory.PsCo.Pc3
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w (n := n) →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w (n := n) → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), g = t * k := by
  first | exact @GlobalTheory.SplitUniq.splitUniq | exact GlobalTheory.SplitUniq.splitUniq | (intros; apply GlobalTheory.SplitUniq.splitUniq <;> assumption)
end
