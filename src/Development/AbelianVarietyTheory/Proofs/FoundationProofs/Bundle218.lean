module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualETwo
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle009
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB | exact GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB | (intros; apply GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.SumLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

def valEquiv (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) : (Fin N → K) ≃ₗ[K] (C → VV K lam) :=
  LinearEquiv.ofBijective (LinearMap.pi fun c => valAt lam e c) (Model.valAt_bijective lam e)

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.idx_nonempty (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) : Nonempty (_root_.Formalism.L2.DIV.VVIdx lam) := by
  have hne : (_root_.Formalism.L2.Col.extV ℚ lam : _root_.Formalism.L2.DIV.VV ℚ lam) ≠ 0 := by
    intro h
    apply _root_.Formalism.L2.Col.evV_extV_ne_zero (E := ℚ) (fun _ => RingHom.id ℚ) (1 : Matrix (Fin n) (Fin n) ℚ) lam
      (Rat.castHom ℂ)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det})
    rw [h]
    exact map_zero _
  haveI : Nontrivial (_root_.Formalism.L2.DIV.VV ℚ lam) := nontrivial_of_ne _ _ hne
  exact (_root_.Formalism.L2.DIV.bVV ℚ lam).index_nonempty

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat [Finite C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)) (hT : ∀ c, Submodule.IsLattice K (T c)) :
    Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) := by
  classical
  haveI := Fintype.ofFinite C
  set f := _root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e with hf
  let g : C → _root_.Formalism.L2.DIV.VV K lam →ₗ[K] (Fin N → K) := fun c =>
    f.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : C => _root_.Formalism.L2.DIV.VV K lam) c
  have hval : ∀ c c' t, _root_.GlobalTheory.TestLat.valAt lam e c' (g c t) = (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
    intro c c' t
    have h := congrFun (f.apply_symm_apply (Pi.single c t : C → _root_.Formalism.L2.DIV.VV K lam)) c'
    exact h
  have hsum : ∀ u, ∑ c, g c (_root_.GlobalTheory.TestLat.valAt lam e c u) = u := by
    intro u
    apply f.injective

    rw [map_sum]
    have h : ∀ c, f (g c (_root_.GlobalTheory.TestLat.valAt lam e c u)) =
        Pi.single c (_root_.GlobalTheory.TestLat.valAt lam e c u) := fun c => f.apply_symm_apply _
    simp only [h]
    exact Finset.univ_sum_single (fun c => _root_.GlobalTheory.TestLat.valAt lam e c u)
  set L : Submodule (𝓞 K) (Fin N → K) := ⨆ c, (T c).map ((g c).restrictScalars (𝓞 K)) with hL
  have hP : _root_.GlobalTheory.TestLat.sumLat lam e T = L := by
    apply le_antisymm
    · intro u hu
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hu
      rw [← hsum u]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (Submodule.mem_map_of_mem (hu c))
    · rw [hL, iSup_le_iff]
      intro c
      rw [Submodule.map_le_iff_le_comap]
      intro t ht
      rw [Submodule.mem_comap, _root_.GlobalTheory.TestLat.Model.mem_sumLat]
      intro c'
      rw [LinearMap.restrictScalars_apply, hval]
      by_cases hc : c' = c
      · subst hc
        rw [Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hc]
        exact zero_mem _
  rw [hP]
  refine ⟨Submodule.fg_iSup _ fun c => ((hT c).fg).map _, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.SumLat.sumLat_lattice_dual : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (C : Type) [Nonempty C]
    (N : ℕ) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam)),
    (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (_root_.GlobalTheory.TestLat.sumLat lam e T) ∧
      0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) →
        _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) (_root_.GlobalTheory.TestLat.sumLat lam e T) =
          _root_.GlobalTheory.TestLat.sumLat lam e fun c => _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) := by
  intro K _ _ _ ι _ n lam C _ N e T hT
  classical
  obtain ⟨i₀⟩ := _root_.GlobalTheory.TestLat.SumLat.idx_nonempty lam
  haveI : Finite (C × _root_.Formalism.L2.DIV.VVIdx lam) := Finite.of_equiv _ e
  haveI : Finite C :=
    Finite.of_surjective (fun p : C × _root_.Formalism.L2.DIV.VVIdx lam => p.1) (fun c => ⟨(c, i₀), rfl⟩)
  haveI : Fintype C := Fintype.ofFinite C
  refine ⟨_root_.GlobalTheory.TestLat.SumLat.isLattice_sumLat lam e T hT, ?_, ?_⟩
  · obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
    refine Nat.pos_of_ne_zero fun h => ?_
    subst h
    exact (e.symm (c₀, i₀)).elim0
  · intro G _
    ext x
    rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
    have hmemD : ∀ L : Submodule (𝓞 K) (Fin N → K), x ∈ _root_.Formalism.L2.DIV.hdualFr (_root_.GlobalTheory.TestLat.sumGram lam e G) L ↔
        ∀ y ∈ L, star y ⬝ᵥ _root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ x ∈ (1 : Submodule (𝓞 K) K) :=
      fun _ => Iff.rfl
    have hmemV : ∀ (c : C) (v : _root_.Formalism.L2.DIV.VV K lam), v ∈ _root_.Formalism.HermitianLatticesTheory.dual (_root_.Formalism.L2.DIV.pairK lam G) (T c) ↔
        ∀ z ∈ T c, _root_.Formalism.L2.DIV.pairK lam G z v ∈ (1 : Submodule (𝓞 K) K) := by
      intro c v
      unfold _root_.Formalism.HermitianLatticesTheory.dual _root_.Formalism.E.hdual
      simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    rw [hmemD]
    simp_rw [_root_.GlobalTheory.TestLat.Model.sumGram_form, hmemV]
    constructor
    · intro h c z hz
      set y := (_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).symm (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) with hydef
      have hy : ∀ c', _root_.GlobalTheory.TestLat.valAt lam e c' y = (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam) c' := by
        intro c'
        have h' := congrFun
          ((_root_.GlobalTheory.TestLat.SumLat.valEquiv (K := K) lam e).apply_symm_apply (Pi.single c z : C → _root_.Formalism.L2.DIV.VV K lam)) c'
        exact h'
      have hyL : y ∈ _root_.GlobalTheory.TestLat.sumLat lam e T := by
        rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat]
        intro c'
        rw [hy]
        by_cases hc : c' = c
        · subst hc
          rw [Pi.single_eq_same]
          exact hz
        · rw [Pi.single_eq_of_ne hc]
          exact zero_mem _
      have hsum := h y hyL
      rwa [Finset.sum_eq_single c
        (fun c' _ hc => by rw [hy, Pi.single_eq_of_ne hc, map_zero, LinearMap.zero_apply])
        (by simp), hy, Pi.single_eq_same] at hsum
    · intro h y hy
      rw [_root_.GlobalTheory.TestLat.Model.mem_sumLat] at hy
      exact Submodule.sum_mem _ fun c _ => h c _ (hy c)

end GlobalTheory.TestLat.SumLat
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GaussCauchy

theorem factor_le (A B : ℝ) (hA : 0 < A) (n : ℕ) (hn : (n : ℝ) ≤ 2 * B) :
    ((n.factorial : ℝ)) ^ 2 * Real.exp n / (A * n / Real.pi) ^ n
      ≤ (2 * Real.exp 1 * Real.pi * B / A) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity), ← mul_pow]
  have h1 : 2 * Real.exp 1 * Real.pi * B / A * (A * n / Real.pi) = (2 * B) * n * Real.exp 1 := by
    field_simp
  have h2 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h3 : (n : ℝ) ^ n ≤ (2 * B) ^ n := pow_le_pow_left₀ hn0.le hn n
  rw [h1, mul_pow, mul_pow (2 * B), ← Real.exp_nat_mul, mul_one, sq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul (h2.trans h3) h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n).trans h3)

theorem pderivIter_sq_le {ι : Type*} [DecidableEq ι] [Fintype ι] (F : (ι → ℂ) → ℂ) (S A B : ℝ)
    (hA : 0 < A) (hS : 0 ≤ S) (hF : Differentiable ℂ F)
    (hb : ∀ z, ‖F z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ k, ‖z k‖ ^ 2) / A))
    (α : ι →₀ ℕ) (hα : ∀ k, (α k : ℝ) ≤ 2 * B) :
    ‖pderivIter α F 0‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (∑ k, α k) := by
  have hpi := Real.pi_pos
  have hsq : ∀ k, Real.sqrt (A * α k / Real.pi) ^ 2 = A * α k / Real.pi := fun k =>
    Real.sq_sqrt (by positivity)
  have h := norm_pderivIter_le_of_differentiable (F := F) (a := 0)
    (r := fun k => Real.sqrt (A * α k / Real.pi))
    (M := Real.sqrt (S * Real.exp (∑ k, (α k : ℝ)))) α (fun k => Real.sqrt_nonneg _)
    (fun k hk => by
      have : (0 : ℝ) < α k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact Real.sqrt_pos.mpr (by positivity)) hF
    (fun z hz => by
      apply Real.le_sqrt_of_sq_le
      refine (hb z).trans (le_of_eq ?_)
      congr 2
      simp only [Pi.zero_apply, sub_zero] at hz
      simp only [hz, hsq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow, ← Finset.prod_pow,
    Real.exp_sum, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_div_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_) hS
  rw [← pow_mul, mul_comm (α k) 2, pow_mul, hsq]
  exact factor_le A B hA _ (hα k)

noncomputable def curry (D : D7) (N N' : ℕ) :
    (D.what₂.Tau × Fin N' × Fin N → ℂ) →ₗ[ℂ] VC D N N' where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curry_single (D : D7) (N N' : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    curry D N N' (Pi.single k 1) = coordV D k := by
  funext τ i j
  obtain ⟨a, b, c⟩ := k
  simp [curry, coordV, Pi.single_apply, Prod.ext_iff]

theorem factorial_mul_taylor (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α
      = pderivIter α (fun w => G (curry D N N' w)) 0 := by
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [Formalism.MainNotions.TaylorLogMetric.taylor, mul_div_cancel₀ _ hne, pderivIter, pderivList, lineDerivList_comp_linearMap,
    ← lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curry_single]

theorem monomial_deriv_bound : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  intro D N N' G S A B hA _ hS hG hb α hα
  rw [factorial_mul_taylor D N N' G hG, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine pderivIter_sq_le _ S A B hA hS
    (hG.comp (LinearMap.toContinuousLinearMap (curry D N N')).differentiable) (fun z => ?_) α hα
  simp only [Fintype.sum_prod_type]
  exact hb (curry D N N' z)

end GlobalTheory.GaussCauchy
end

section

open Module.End

namespace GlobalTheory.OrthonormalEigenbasis

theorem exists_eigenbasis_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (a : E →ₗ[ℂ] E) (ha : ∀ x y, inner ℂ (a x) (a y) = inner ℂ x y) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (l : Fin (Module.finrank ℂ E) → ℂ),
      ∀ i, a (b i) = l i • b i := by
  set a' := LinearMap.adjoint a with ha'

  have h1 : a' * a = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    rw [Module.End.mul_apply, ha', LinearMap.adjoint_inner_left, ha, Module.End.one_apply]
  have h2 : a * a' = 1 := mul_eq_one_comm.mp h1

  set A : E →ₗ[ℂ] E := a + a' with hAdef
  set B : E →ₗ[ℂ] E := Complex.I • (a' - a) with hBdef
  have hA : A.IsSymmetric := by
    intro x y
    simp only [hAdef, LinearMap.add_apply, inner_add_left, inner_add_right, ha',
      LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
    ring
  have hB : B.IsSymmetric := by
    intro x y
    simp only [hBdef, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
      inner_sub_left, inner_sub_right, ha', LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
      Complex.conj_I]
    ring
  have hAB : Commute A B := by
    have hc : Commute (a + a') (a' - a) := by
      show (a + a') * (a' - a) = (a' - a) * (a + a')
      simp only [add_mul, mul_add, sub_mul, mul_sub, h1, h2]
      abel
    exact hc.smul_right Complex.I
  have hV := LinearMap.IsSymmetric.directSum_isInternal_of_commute hA hB hAB
  have hV' := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB

  have hT : Set.Finite {i : ℂ × ℂ | eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := by
    refine ((Module.End.finite_hasEigenvalue (f := B)).prod
      (Module.End.finite_hasEigenvalue (f := A))).subset fun i hi => ⟨?_, ?_⟩
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_right)
    · exact Module.End.hasEigenvalue_iff.mpr (ne_bot_of_le_ne_bot hi inf_le_left)
  have : Finite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥} := hT.to_subtype
  have := Fintype.ofFinite {i : ℂ × ℂ // eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥}
  classical
  have hW := DirectSum.isInternal_ne_bot_iff.mpr hV
  have hW' := hV'.comp (Subtype.val_injective (p := fun i : ℂ × ℂ => eigenspace A i.2 ⊓ eigenspace B i.1 ≠ ⊥))

  refine ⟨hW.subordinateOrthonormalBasis rfl hW', fun i =>
    ((hW.subordinateOrthonormalBasisIndex rfl i hW').1.2 +
      Complex.I * (hW.subordinateOrthonormalBasisIndex rfl i hW').1.1) / 2, fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate rfl i hW'
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff] at hmem
  have hsum : ∀ v, A v + Complex.I • B v = (2 : ℂ) • a v := by
    intro v
    simp only [hAdef, hBdef, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_sub, two_smul]
    abel
  calc a (hW.subordinateOrthonormalBasis rfl hW' i)
      = (2 : ℂ)⁻¹ • (A (hW.subordinateOrthonormalBasis rfl hW' i) +
          Complex.I • B (hW.subordinateOrthonormalBasis rfl hW' i)) := by
        rw [hsum, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = _ := by
        rw [hmem.1, hmem.2, smul_smul, ← add_smul, smul_smul]
        congr 1
        ring


open GlobalTheory.UnitaryTheta in
theorem exists_orthonormal_eigenbasis {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then (1 : ℂ) else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by

  let cd : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => H y x
      conj_inner_symm := fun x y => (hH.1 y x).symm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hH.2 x hx).le
      add_left := fun x y z => by
        show H z (x + y) = H z x + H z y
        exact map_add _ _ _
      smul_left := fun x y r => by
        show H y (r • x) = (starRingEnd ℂ) r * H y x
        rw [LinearMap.map_smulₛₗ, smul_eq_mul]
      definite := fun x hx => by
        by_contra h
        have := hH.2 x h
        simp [hx] at this }
  let _ : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  have hinner : ∀ x y : V, inner ℂ x y = H y x := fun _ _ => rfl
  obtain ⟨b, l, hb⟩ := exists_eigenbasis_of_isometry a (fun x y => by rw [hinner, hinner]; exact ha y x)
  refine ⟨Module.finrank ℂ V, b.toBasis, l, fun i j => ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [OrthonormalBasis.coe_toBasis, ← hinner, orthonormal_iff_ite.mp b.orthonormal j i]
    exact if_congr eq_comm rfl rfl
  ·
    have h1 : ‖a (b i)‖ = ‖b i‖ := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner, hinner, ha]
    rw [hb i, norm_smul, b.orthonormal.1 i, mul_one] at h1
    exact h1
  · rw [OrthonormalBasis.coe_toBasis]
    exact hb i

end GlobalTheory.OrthonormalEigenbasis
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GKSubmodule

noncomputable def resAct {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) : Mat p q →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

theorem resAct_coe {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) (Z : Mat p q) (x : N) :
    ((resAct M N h Z x : N) : M.V) = M.act Z x := rfl

theorem exists_submodule : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  intro p q M N h
  have hlie : IsLieAct (resAct M N h) := by
    intro X Y
    ext x
    have := congrArg (fun f : Module.End ℂ M.V => f x) (M.lie X Y)
    simpa [resAct_coe] using this
  have hk : ∀ v : N, ∃ W : Submodule ℂ N, FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (resAct M N h) W := by
    intro v
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    refine ⟨W.comap N.subtype, ?_, hv, ?_⟩
    · exact Module.Finite.of_injective
        (N.subtype.restrict (p := W.comap N.subtype) (q := W) (fun x hx => hx))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
    · intro X hX w hw
      exact hs X hX w hw
  have hw : ∀ v : N, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ := by
    intro v
    have h1 := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => h _) v v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, N ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ).map N.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [resAct_coe] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy
  exact ⟨{ V := N, act := resAct M N h, lie := hlie, kfin := hk, wts := hw }, N.subtype,
    N.injective_subtype, N.range_subtype, fun _ _ => rfl⟩

end GlobalTheory.GKSubmodule
end
