module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStructure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

private theorem specRoot_semi {R K U : Type} [Field R] [Field K] [Algebra R K] [AddCommGroup U] [Module R U]
    {d : ℕ} (Φ : (Fin d → K) → U) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b)
    (hsm : ∀ (r : R) a, Φ (r • a) = r • Φ a) (T : Module.End R U) (F : Matrix (Fin d) (Fin d) K)
    (h : ∀ c, T (Φ c) = Φ (F.mulVec c)) (q : R[X]) (c : Fin d → K) :
    aeval T q (Φ c) = Φ ((aeval F q).mulVec c) := by
  have hp : ∀ (n : ℕ) (c : Fin d → K), (T ^ n) (Φ c) = Φ ((F ^ n).mulVec c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ', Module.End.mul_apply, ih, h, Matrix.mulVec_mulVec, pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq, Matrix.add_mulVec, hadd]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, LinearMap.smul_apply, hp,
      Matrix.smul_mulVec, hsm]

private theorem specRoot_spec {R K L : Type} [Field R] [Field K] [Field L] [Algebra R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L] {d : ℕ} (F : Matrix (Fin d) (Fin d) K) (q : R[X])
    (hq : q ≠ 0) (c : Fin d → K) (hc : c ≠ 0) (h : (aeval F q).mulVec c = 0) :
    ∃ β ∈ spectrum L (F.map (algebraMap K L)), aeval β q = 0 := by
  have h1 : (aeval F q).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h⟩
  have h2 : (algebraMap K L).mapMatrix (aeval F q) =
      aeval (F.map (algebraMap K L)) (q.map (algebraMap R L)) := by
    refine Polynomial.map_aeval_eq_aeval_map (φ := algebraMap R L)
      (ψ := (algebraMap K L).mapMatrix) ?_ q F
    ext r i j
    simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs
    · simp [← IsScalarTower.algebraMap_apply]
    · simp
  have h3 : ¬ IsUnit (aeval (F.map (algebraMap K L)) (q.map (algebraMap R L))) := by
    rw [← h2, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, h1, map_zero]
    exact not_isUnit_zero
  have hq' : q.map (algebraMap R L) ≠ 0 := Polynomial.map_ne_zero hq
  have hs := (IsAlgClosed.splits (q.map (algebraMap R L))).eq_prod_roots
  obtain ⟨β, hβ, e⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (p := q.map (algebraMap R L))
    (a := F.map (algebraMap K L)) (fun hu => h3 (by
      rw [hs, map_mul, aeval_C]
      exact ((IsUnit.mk0 _ (leadingCoeff_ne_zero.2 hq')).map _).mul hu))
  exact ⟨β, hβ, by rwa [eval_map_algebraMap] at e⟩

theorem UpperTheory.crystalline_period_matrix_relation :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V) (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → ∀ F : Matrix (Fin d) (Fin d) ↥(K0 K), M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ x ∈ Dcris ((PP l).PD K) ρ, x ≠ 0 → ∀ q : ℚ_[l][X], q ≠ 0 → aeval ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f) q x = 0 → ∃ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), aeval β q = 0 := by
  intro l _ K f hσ V _ _ _ ρ d e M M' hMM hρ F hF x hx hx0 q hq h0
  obtain ⟨c, hc⟩ := UpperTheory.crystalline_vector_basis_expansion K ρ e M M' hMM hρ x hx
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  let j := algebraMap ↥(K0 K) (Bcr l)
  let Φ : (Fin d → ↥(K0 K)) → V ⊗[ℚ_[l]] Bcr l := fun c =>
    ∑ i, e i ⊗ₜ[ℚ_[l]] (M.mulVec (fun k => j (c k)) i)
  have hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (j c) = j ((((PP l).PD K).σ)^[k] c) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih =>
      intro c
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]
  have hT : ∀ (k : ℕ) (v : V) (b : Bcr l),
      ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ k) (v ⊗ₜ[ℚ_[l]] b) =
        v ⊗ₜ[ℚ_[l]] (((PP l).φB)^[k] b) := by
    intro k
    induction k with
    | zero => intro v b; rfl
    | succ k ih =>
      intro v b
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', ← (PP l).PD_φ K]
      rfl
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  have key := specRoot_semi Φ (fun a b => by
      simp only [Φ, Pi.add_apply, map_add (f := _), ← Finset.sum_add_distrib, ← TensorProduct.tmul_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib])
    (fun (r : ℚ_[l]) a => by
      simp only [Φ, Finset.smul_sum, ← TensorProduct.tmul_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Pi.smul_apply, Algebra.smul_def, map_mul, j,
        ← IsScalarTower.algebraMap_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f) F
    (fun c => by

      simp only [Φ, map_sum, hT]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [← hψ, RingHom.map_mulVec, hψ, hF, ← Matrix.mulVec_mulVec]
      have e1 : ((PP l).φB)^[f] ∘ (fun k => j (c k)) = j ∘ c := by
        funext m
        exact (hfix f _).trans (congrArg j (hσ _))
      have e2 : (F.map j).mulVec (j ∘ c) = fun k => j (F.mulVec c k) := by
        funext k
        exact (RingHom.map_mulVec j F c k).symm
      rw [e1, e2]) q c
  have hxc : x = Φ c := hc
  rw [← hxc, h0] at key
  refine specRoot_spec F q hq c ?_ ?_
  · rintro rfl
    apply hx0
    rw [hc]
    simp [Matrix.mulVec, dotProduct]
  · set y := (aeval F q).mulVec c
    have h1 := TensorProduct.sum_tmul_basis_left_eq_zero e
      (Finsupp.equivFunOnFinite.symm (M.mulVec (fun k => j (y k)))) (by
        rw [Finsupp.sum_fintype _ _ (fun i => TensorProduct.tmul_zero _ _)]
        exact key.symm)
    have h2 : M.mulVec (fun k => j (y k)) = 0 := by
      funext i
      exact DFunLike.congr_fun h1 i
    have h3 := congrArg M'.mulVec h2
    rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec, Matrix.mulVec_zero] at h3
    haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
      rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
    funext k
    exact j.injective ((congrFun h3 k).trans (map_zero j).symm)
end

section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def slc {K : Type} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    archSmooth K n →ₗ[ℂ] (archCompact K n → ℂ) where
  toFun φ k := φ.1 (g * infEmb K n k.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem slc_op {K : Type} [Field K] [NumberField K] {n : ℕ} (X : (isExpLieAlgebra K n).lieSubalgebra)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X) ∈ archCompact K n) :
    (∃ D : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      D (slc g φ) = slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ)) ∧
    ∀ (V : Submodule ℂ (archCompact K n → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) →
      ∀ g φ, slc g φ ∈ V → slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) ∈ V := by
  let γ : ℝ → archCompact K n := fun t =>
    ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X), hX t⟩
  have F : ∀ (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) (k : archCompact K n),
      HasDerivAt (fun t => slc g φ (k * γ t)) (slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) k) 0 := by
    intro g φ k
    have d := (isExpLieAlgebra K n).hasDerivAt_rightDeriv
      ((show IsArchSmooth φ.1 from φ.2) (g * infEmb K n k.1)) ((isExpLieAlgebra K n).ofLie X) 1
    show HasDerivAt _ ((uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 (g * infEmb K n k.1)) 0
    rw [uAction_ι_apply]
    have e : (fun t => slc g φ (k * γ t)) = fun t => archSlice φ.1 (g * infEmb K n k.1)
        (1 * (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) := by
      funext t
      simp only [slc, LinearMap.coe_mk, AddHom.coe_mk, archSlice_apply, one_mul, Subgroup.coe_mul, map_mul,
        mul_assoc]
      rfl
    rw [e]
    exact d
  let P : Submodule ℂ (archCompact K n → ℂ) :=
    { carrier := {f | ∀ k, DifferentiableAt ℝ (fun t => f (k * γ t)) 0}
      add_mem' := fun ha hb k => (ha k).add (hb k)
      zero_mem' := fun _ => differentiableAt_const _
      smul_mem' := fun c _ hf k => (hf k).const_smul c }
  let D₀ : P →ₗ[ℂ] (archCompact K n → ℂ) :=
    { toFun := fun f k => deriv (fun t => f.1 (k * γ t)) 0
      map_add' := fun f h => by
        funext k
        show deriv (fun t => f.1 (k * γ t) + h.1 (k * γ t)) 0 = _
        exact deriv_add (f.2 k) (h.2 k)
      map_smul' := fun c f => by
        funext k
        show deriv (fun t => c • f.1 (k * γ t)) 0 = _
        exact deriv_const_smul c (f.2 k) }
  obtain ⟨D, hD⟩ := LinearMap.exists_extend D₀
  refine ⟨⟨D, fun g φ => ?_⟩, fun V hV hVs g φ hφ => ?_⟩
  · have hm : slc g φ ∈ P := fun k => (F g φ k).differentiableAt
    have h1 := congrArg (fun L => L ⟨slc g φ, hm⟩) hD
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    funext k
    exact (F g φ k).deriv
  · haveI := hV
    exact mem_of_hasDerivAt V (c := fun t k => slc g φ (k * γ t)) (fun t => hVs _ hφ (γ t)) (fun k => F g φ k)

theorem UpperTheory.algMod_bot_compact_casimir_of_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → ∀ (ι : Type) [Fintype ι] (X : ι → (isExpLieAlgebra K n).lieSubalgebra) (c : ι → ℝ), (∀ i, c i = 0 ∨ ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (X i)) ∈ archCompact K n) → AlgMod S ⊥ (uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i)))) := by
  intro K _ _ n S hS ι _ X c hc
  obtain ⟨V, hV, hVs, hSV⟩ := hS
  have hi : ∀ i, ∃ Di : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      c i • Di (Di (slc g φ)) = slc g (c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ)) := by
    intro i
    rcases hc i with h0 | hX
    · exact ⟨0, fun g φ => by simp [h0]⟩
    · obtain ⟨D, hD⟩ := (slc_op (X i) hX).1
      exact ⟨D, fun g φ => by rw [hD, hD, LinearMap.map_smul_of_tower]⟩
  choose Di hDi using hi
  have e1 : ∀ φ : archSmooth K n, uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) *
      UniversalEnvelopingAlgebra.ι ℝ (X i))) φ = ∑ i, c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ) := by
    intro φ

    simp only [map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  have hinter : ∀ g φ, (∑ i, c i • (Di i * Di i)) (slc g φ) = slc g (uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ) := by
    intro g φ

    rw [e1, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    exact Finset.sum_congr rfl fun i _ => hDi i g φ
  have hstab : ∀ φ ∈ (⨅ g, V.comap (slc g)), uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ ∈ (⨅ g, V.comap (slc g)) := by
    intro φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ ⊢
    intro g

    rw [e1, map_sum]
    refine V.sum_mem fun i _ => ?_
    rw [LinearMap.map_smul_of_tower]
    rcases hc i with h0 | hX
    · rw [h0, zero_smul]
      exact V.zero_mem
    · exact V.smul_of_tower_mem _ ((slc_op (X i) hX).2 V hV hVs g _ ((slc_op (X i) hX).2 V hV hVs g φ (hφ g)))
  have hinV : ∀ g, ∀ φ ∈ (⨅ g, V.comap (slc g)), slc g φ ∈ V := by
    intro g φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ
    exact hφ g
  obtain ⟨q, hq, -, hq0⟩ := UpperTheory.V.Af.CuspFin.polySlices (archSmooth K n) (archCompact K n → ℂ)
    (AdelicGLn.AdelicGL K n) _ _ (fun g => slc g) hinter V hV _ hstab hinV
  refine ⟨q, hq, fun φ hφ => ?_⟩
  rw [Submodule.mem_bot]
  have hN : φ ∈ (⨅ g, V.comap (slc g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => hSV φ hφ g
  apply Subtype.ext
  funext g
  have h1 := congrFun (hq0 g φ hN) 1
  simpa [slc] using h1
end
