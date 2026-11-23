module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import GroundTheory.AutomorphicForms.Bundle017
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
import GroundTheory.AutomorphicForms.ReductionFinite
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle016
public import GroundTheory.AutomorphicForms.Bundle016
import GroundTheory.AutomorphicForms.AdmissibleInduction
import GroundTheory.AutomorphicForms.CuspidalAdmissible
public import GroundTheory.AutomorphicForms.Satake
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import GroundTheory.AutomorphicForms.IwahoriFactorization
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import GroundTheory.LocalFields.LocalFourierHaar
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.Finite.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobenius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open NumberField Filter Topology Matrix
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
  GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.SiegelEscape

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem exists_eq_of_mem_lat {γ : AdelicGLn.AdelicGL K n} (hγ : γ ∈ lat K n) :
    ∃ (γ₀ : GL (Fin n) K) (u : IdeleGroup K),
      γ = AdelicGLn.diagonal K n γ₀ * scalarUnits K n u := by
  set s : IdeleGroup K := posIdele (Real.exp 1) (Real.exp_pos _) with hs
  have hz : (tor K fun _ : Fin n => (1 : ℝ)) = scalarUnits K n s := rfl
  have hN : (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hz, ← map_zpow, ← scalarUnits_mul_comm, mul_inv_cancel_right, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have h := Subgroup.mul_normal (AdelicGLn.diagonal K n).range
    (Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ)))
  have hγ' : γ ∈ (↑((AdelicGLn.diagonal K n).range ⊔
      Subgroup.zpowers (tor K fun _ : Fin n => (1 : ℝ))) : Set (AdelicGLn.AdelicGL K n)) := hγ
  rw [h] at hγ'
  obtain ⟨a, ⟨γ₀, rfl⟩, b, hb, rfl⟩ := Set.mem_mul.1 hγ'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact ⟨γ₀, s ^ k, by rw [hz, map_zpow]⟩

theorem detModule_scalarUnits (u : IdeleGroup K) :
    (detModule K n (scalarUnits K n u) : ℝ) = (ideleModule K u : ℝ) ^ n := by
  rw [detModule, MonoidHom.comp_apply, scalarUnits_apply, det_diagUnits, map_prod,
    coe_finset_prod_pos]
  simp

theorem detModule_unipGL {r : ℕ} (X : UPos n r → 𝔸[K]) : detModule K n (unipGL X) = 1 :=
  mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL X)

theorem detModule_diagonal (γ₀ : GL (Fin n) K) : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)

theorem detModule_aR {r : ℕ} (hr : r ≤ n) (t : ℝ) :
    (detModule K n (aR K n r t) : ℝ) = Real.exp (r * t) ^ Module.finrank ℚ K := by
  have h := ideleModule_det_diagUnits_posIdele (K := K) (n := n)
    (fun i : Fin n => Real.exp (if (i : ℕ) < r then t else 0)) (fun _ => Real.exp_pos _)
  have h2 : ∏ i : Fin n, Real.exp (if (i : ℕ) < r then t else 0) = Real.exp (r * t) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    simp [Fin.card_filter_val_lt, hr]
  rw [h2] at h
  exact h

theorem ratVec_single (l : Fin n) : ratVec (Pi.single l (1 : K)) = Pi.single l (1 : 𝔸[K]) := by
  ext1 i
  by_cases h : i = l
  · subst h; simp [ratVec]
  · simp [ratVec, h]

theorem single_vecMul_unipMatrix {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (X : UPos n r → 𝔸[K]) :
    Pi.single l (1 : 𝔸[K]) ᵥ* unipMatrix X = Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  ext1 j
  rw [Matrix.single_one_vecMul]
  simp [unipMatrix, blockEntry_apply, h, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem single_vecMul_aR {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (t : ℝ) :
    Pi.single l (1 : 𝔸[K]) ᵥ* ((aR K n r t : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) =
      Pi.single l (1 : 𝔸[K]) := by
  have h : ¬ ((l : ℕ) < r) := by omega
  have h1 : ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ = 1 → posIdele (K := K) ρ hρ = 1 := by
    rintro _ _ rfl
    exact map_one (posIdeleHom K)
  rw [aR, tor, coe_diagUnits]
  ext1 j
  rw [Matrix.vecMul_diagonal]
  by_cases hj : j = l
  · subst hj
    rw [h1 _ _ (by simp [h])]
    simp
  · simp [Pi.single_apply, hj]

theorem height_eq {r : ℕ} {l : Fin n} (hl : r ≤ (l : ℕ)) (γ₀ : GL (Fin n) K) (u : IdeleGroup K)
    (X : UPos n r → 𝔸[K]) (t : ℝ) (q : AdelicGLn.AdelicGL K n) :
    Reduction.height (AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q))
        (Pi.single l (1 : K) ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      (ideleModule K u : ℝ) *
        adelicNorm (Pi.single l (1 : 𝔸[K]) ᵥ* (q : Matrix (Fin n) (Fin n) 𝔸[K])) := by
  rw [mul_assoc, height_diagonal_mul, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.vecMul_one, Reduction.height, ratVec_single, Units.val_mul, Units.val_mul,
    Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    coe_unipGL, scalarUnits_apply, coe_diagUnits]
  have h0 : Pi.single l (1 : 𝔸[K]) ᵥ* Matrix.diagonal (fun _ : Fin n => ((u : IdeleGroup K) : 𝔸[K])) =
      ((u : IdeleGroup K) : 𝔸[K]) • Pi.single l (1 : 𝔸[K]) := by
    ext1 j
    rw [Matrix.vecMul_diagonal]
    simp [mul_comm]
  rw [h0, Matrix.smul_vecMul, Matrix.smul_vecMul, Matrix.smul_vecMul, single_vecMul_unipMatrix hl,
    single_vecMul_aR hl]
  have hne : (Pi.single l (1 : K) : Fin n → K) ≠ 0 := by
    intro h
    have := congrFun h l
    simp at this
  have hfc := hasFiniteContent_height q hne
  rw [ratVec_single] at hfc
  exact adelicNorm_smul hfc u

theorem escape : Escape := by
  intro K _ _ n r hr hrn D Q T hD hQ hT
  have hn : 0 < n := by omega
  set l : Fin n := ⟨n - 1, by omega⟩ with hldef
  have hl : r ≤ (l : ℕ) := by simp only [hldef]; omega
  set e : Fin n → K := Pi.single l 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have := congrFun h l
    simp [he] at this
  obtain ⟨ε, hε, hheight⟩ := exists_pos_le_height hT
  obtain ⟨P, hP, hvec⟩ := exists_adelicNorm_vecMul_le_mul hQ
  set A : ℝ := adelicNorm (ratVec e) with hA
  have hA1 : 1 ≤ A := one_le_adelicNorm_ratVec he0
  have hcont : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨_, B, -, -, hB⟩ := exists_pos_bounds hT hcont fun g _ => (detModule K n g).2
  obtain ⟨b, _, hb, -, hb'⟩ := exists_pos_bounds hQ hcont fun g _ => (detModule K n g).2
  set c : ℝ := ε / (P * A) with hc
  have hPA : 0 < P * A := mul_pos hP (by linarith)
  have hcpos : 0 < c := div_pos hε hPA
  set d := Module.finrank ℚ K with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have htend : Tendsto (fun t : ℝ => Real.exp (r * t) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd0).comp
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr0))
  filter_upwards [htend.eventually_gt_atTop (B / (c ^ n * b))] with t ht γ hγ X _ q hq hmem
  obtain ⟨γ₀, u, rfl⟩ := exists_eq_of_mem_lat hγ
  set E : ℝ := (ideleModule K u : ℝ) with hE
  have hEpos : 0 < E := (ideleModule K u).2
  set τ := AdelicGLn.diagonal K n γ₀ * scalarUnits K n u * (unipGL X * aR K n r t * q) with hτ
  have hx0 : (e ᵥ* ((γ₀⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≠ 0 := by
    intro h
    apply he0
    have h2 := congrArg (· ᵥ* ((γ₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
    simpa [Matrix.vecMul_vecMul, ← Units.val_mul] using h2
  have h1 : ε ≤ E * (P * A) := by
    have h2 := hheight τ hmem _ hx0
    rw [hτ, height_eq hl] at h2
    have h3 := hvec q hq (ratVec e) (hasFiniteContent_ratVec he0)
    rw [he, ratVec_single] at h3
    rw [hA, he, ratVec_single]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hEpos.le)
  have hcE : c ≤ E := (div_le_iff₀ hPA).2 h1
  have hdet : (detModule K n τ : ℝ) = E ^ n * (Real.exp (r * t) ^ d * (detModule K n q : ℝ)) := by
    rw [hτ, map_mul, map_mul, map_mul, map_mul, detModule_diagonal, detModule_unipGL, one_mul,
      one_mul, Positive.val_mul, Positive.val_mul, detModule_scalarUnits, detModule_aR hrn.le]
  have hle := (hB τ hmem).2
  rw [hdet] at hle
  have hbq := (hb' q hq).1
  have hexp : 0 < Real.exp (r * t) ^ d := pow_pos (Real.exp_pos _) _
  have hcn : 0 < c ^ n := pow_pos hcpos _
  have h4 : c ^ n * (Real.exp (r * t) ^ d * b) ≤ B := by
    refine le_trans ?_ hle
    exact mul_le_mul (pow_le_pow_left₀ hcpos.le hcE n)
      (mul_le_mul_of_nonneg_left hbq hexp.le) (mul_pos hexp hb).le (pow_pos hEpos _).le
  rw [div_lt_iff₀ (mul_pos hcn hb)] at ht
  nlinarith [ht, h4]

end GlobalTheory.CompanionTheory.SiegelEscape

end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetCoeff

theorem exists_coeff_geometric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  classical
  intro k _ _ _ _ N V _ _ π hπ h β _ m hm a ha hcomm _ hconj y Λ hy hyK hΛ
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m
  have hyfix : y ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π)
      ((GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf
        (GroundTheory.Automorphic.Parabolic.levi k N β)) :=
    fun g hg => hyK g (Subgroup.mem_subgroupOf.1 hg)
  obtain ⟨⟨w, hw⟩, hwy⟩ :=
    GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup β hπ hm ⟨y, hyfix⟩
  have hqw : Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) w = y :=
    congrArg Subtype.val hwy
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π),
      f y = 1 := by
    have h0 : ¬ ∀ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 0 :=
      fun h' => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h')
    push_neg at h0
    obtain ⟨f, hf⟩ := h0
    exact ⟨(f y)⁻¹ • f, by simp [hf]⟩

  have hpowc : ∀ j : ℕ, ∀ g ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a ^ j * g = g * a ^ j := by
    intro j g hg
    exact ((show Commute a g from hcomm g hg).pow_left j)
  have hpowz : ∀ j : ℕ, ∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β,
      (a ^ j)⁻¹ * z * a ^ j ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
        GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β := by
    intro j
    induction j with
    | zero => intro z hz; simpa using hz
    | succ j ih =>
      intro z hz
      have := hconj _ (ih z hz)
      have e : (a ^ (j + 1))⁻¹ * z * a ^ (j + 1) = a⁻¹ * ((a ^ j)⁻¹ * z * a ^ j) * a := by
        rw [pow_succ]; group
      rwa [e]
  have hq : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) =
      Λ ^ j • y := by
    intro j
    induction j with
    | zero => simp [hqw]
    | succ j ih =>
      have e : π (a ^ (j + 1)) w = π a (π (a ^ j) w) := by
        rw [pow_succ', map_mul, Module.End.mul_apply]
      have e2 := GroundTheory.Automorphic.Parabolic.jacquetAction_mk (F := k) (n := N) (β := β) π ⟨a, ha⟩
        (π (a ^ j) w)
      rw [e]
      refine e2.symm.trans ?_
      rw [ih, map_smul, hΛ, smul_smul, pow_succ]
  have hkey : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype)
      (GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo (π (a ^ j) w) : V) =
      Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) := by
    intro j
    refine GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq hπ.1 hKc hKo
      (GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' β hm)
      (fun z hz => ?_) (fun g hg => ?_)
    · have hz' := (Subgroup.mem_inf.1 (hpowz j z hz)).1
      have hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹ := by group
      have : π z (π (a ^ j) w) = π (a ^ j) (π ((a ^ j)⁻¹ * z * a ^ j) w) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [this, hw _ hz']
    · have hc := hpowc j g (Subgroup.mem_inf.1 hg).2
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
        hw g (Subgroup.mem_inf.1 hg).1]
  refine ⟨w, f ∘ₗ Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) ∘ₗ
      (GroundTheory.Automorphic.fixedVectors π
        (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)).subtype ∘ₗ
      GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo, hw, ?_, ?_⟩
  · intro g hg
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [GroundTheory.Automorphic.fixedProj_apply_act hπ.1 hKc hKo hg]
  · intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hkey j, hq j, map_smul, hf, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.JacquetCoeff
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetEigen


open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal in
theorem exists_eigenvector_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → ∀ (W T : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π)) (Λ : ℂ), Λ ≠ 0 → T ≤ W → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w ∈ W) → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w - Λ • w ∈ T) → (∃ w ∈ W, w ∉ T) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π, y ≠ 0 ∧ (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) ∧ GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y := by
  intro k _ _ _ _ N V _ _ π hπ h β _hβ a ha hcomm W T Λ hΛ hTW hWst hWT hex
  obtain ⟨w₀, hw₀W, hw₀T⟩ := hex
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N β π
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N β) := fun m =>
    (congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N β)
  have hA := isAdmissible_jacquetRep (β := β) hπ
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N) (β := β)
    ((hA.1 w₀).mem_nhds (one_mem (stabilizerOf _ w₀)))
  have hfix₁ : w₀ ∈ fixedVectors J (KM m₁) := by
    have : w₀ ∈ fixedVectors (jacquetRep k N β π) (KM m₁) := fun x hx => hm₁ hx
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨m₁, fun m hm => ?_⟩
  have hle : KM m ≤ KM m₁ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone k N hm (Subgroup.mem_subgroupOf.1 hx))
  have hfix : w₀ ∈ fixedVectors J (KM m) := fixedVectors_antitone _ hle hfix₁
  have hfin : FiniteDimensional ℂ (fixedVectors J (KM m)) := by
    have := hA.2 (KM m) (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup k N m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup k N m))
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  let A : Module.End ℂ _ := J ⟨a, ha⟩
  let W' : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) :=
    W ⊓ fixedVectors J (KM m)
  have hW'fin : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_right
  have hst : ∀ w ∈ W', A w ∈ W' := by
    intro w hw
    refine ⟨hWst w hw.1, fun g hg => ?_⟩
    have hw2 := hw.2 g hg
    have hc : g * ⟨a, ha⟩ = ⟨a, ha⟩ * g := Subtype.ext (hcomm g g.2).symm
    show J g (J ⟨a, ha⟩ w) = J ⟨a, ha⟩ w
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ hw2
  let B : W' →ₗ[ℂ] W' := A.restrict hst
  let Tc : Submodule ℂ W' := T.comap W'.subtype
  have hw₀' : w₀ ∈ W' := ⟨hw₀W, hfix⟩
  have hsq : Tc.mkQ ∘ₗ B = (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) ∘ₗ Tc.mkQ := by
    ext w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hWT _ w.2.1
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts W' (W' ⧸ Tc) B
    (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) Tc.mkQ (Submodule.mkQ_surjective _) hsq Λ
    (Tc.mkQ ⟨w₀, hw₀'⟩)
    (fun h0 => hw₀T (by simpa [Tc] using (Submodule.Quotient.mk_eq_zero Tc).1 h0))
    rfl hΛ
  refine ⟨y, fun h0 => hy0 (Subtype.ext h0), fun g hg => y.2.2 g (Subgroup.mem_subgroupOf.2 hg), ?_⟩
  exact congrArg Subtype.val hy

end GlobalTheory.CompanionTheory.JacquetEigen
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.HeckeSub

theorem isSatakeParameter_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  intro k _ _ _ _ n α X V _ _ _ _ ρ hρ ι hι π hπ _ _ μ _ h v hv
  obtain ⟨S, f, hf⟩ := hπ
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨u, rfl⟩ := hf v
  have hfix : ∀ g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n, π g (f u) = f u := fun g hg =>
    GroundTheory.Automorphic.mem_fixedVectors.1 hv g hg
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS
    (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k n) f.toLinearMap u fun g hg => by
      show f (S.toRepresentation g u) = f u
      rw [f.isIntertwining]
      exact hfix g hg
  have hfw' : f w = f u := hfw
  have hw' : w ∈ GroundTheory.Automorphic.fixedVectors S.toRepresentation
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) := by
    simpa [fixed, eig, GroundTheory.Automorphic.fixedVectors] using hw
  let T : S.toRepresentation.IntertwiningMap (principalSeries k n (paramChar k α)) :=
    ⟨ι.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => by
      refine LinearMap.ext fun x => ?_
      exact ι.isIntertwining _ _ g x⟩
  have hT : Function.Injective T := fun a b e => Subtype.ext (hι e)
  have hTw : T w ∈ GroundTheory.Automorphic.fixedVectors (principalSeries k n (paramChar k α))
      (GroundTheory.Automorphic.GLnLocal.integralGL k n) :=
    GroundTheory.Automorphic.mem_fixedVectors.2 fun g hg => by
      rw [← T.isIntertwining, GroundTheory.Automorphic.mem_fixedVectors.1 hw' g hg]
  have hmem := (h : GroundTheory.Automorphic.HeckeAlgebra μ).mem
  set c := GroundTheory.Automorphic.Spherical.evalAt α (satakeTransform μ h) with hc
  have hPS := isSatakeParameter_principalSeries (F := k) (μ := μ) α h (T w) hTw
  have hact : GroundTheory.Automorphic.heckeAct μ S.toRepresentation (h : GroundTheory.Automorphic.HeckeAlgebra μ) w = c • w := by
    apply hT
    rw [GroundTheory.Automorphic.map_heckeAct T hmem (hS w), hPS, map_smul]
  rw [← hfw', ← GroundTheory.Automorphic.map_heckeAct f hmem (hS w), hact, map_smul]

end GlobalTheory.CompanionTheory.HeckeSub
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.finite_field_embeddings_differ_frobenius : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_frobenius_pow_of_ringHoms <;> assumption)
end
end
