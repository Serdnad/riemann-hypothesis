module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellSumEquivariantNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AutomorphicArithmetic.DivisorFrames.SetIntegralMemAddSubgroupOfOpenSubgroupInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat _root_.GlobalTheory.CompanionTheory.QL.instMeasGL

section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isCompact_scaledInt (ϖ : kˣ) (n : ℕ) (m : ℤ) :
    IsCompact (GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) := by
  have h := (isCompact_intMatrix (k := k) (m := Fin n) (n := Fin n)).image
    (f := fun A : Matrix (Fin n) (Fin n) k => ((ϖ ^ m : kˣ) : k) • A) (by fun_prop)
  convert h using 1
  have h0 : valuation k ((ϖ ^ m : kˣ) : k) ≠ 0 := (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
  ext Z
  constructor
  · intro hZ
    refine ⟨(((ϖ ^ m)⁻¹ : kˣ) : k) • Z, fun i j => ?_, ?_⟩
    · rw [Valuation.mem_integer_iff, Matrix.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_mul_le_one_of_le₀ (hZ i j) zero_le
    · simp only [smul_smul, Units.mul_inv, one_smul]
  · rintro ⟨A, hA, rfl⟩ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))

private theorem mem_SB_of_periodic (ϖ : kˣ) {n : ℕ} (m : ℤ) (φ : Matrix (Fin n) (Fin n) k → ℂ)
    (hS : Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n m) (hP : GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ) :
    φ ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun X => ?_,
    HasCompactSupport.intro (isCompact_scaledInt ϖ n m) fun x hx => ?_⟩
  · have hn : (fun Y => Y - X) ⁻¹' {A : Matrix (Fin n) (Fin n) k | ∀ i j, A i j ∈ 𝒪[k]} ∈ nhds X :=
      (isOpen_intMatrix.preimage (continuous_id.sub continuous_const)).mem_nhds (by
        intro i j; simp)
    filter_upwards [hn] with Y hY
    have := hP X (Y - X) (fun i j => by
      simpa using (Valuation.mem_integer_iff _ _).1 (hY i j))
    simpa using this
  · by_contra h
    exact hx (hS h)

private theorem isCompact_shellSet' (ϖ : kˣ) {n : ℕ} (m : Fin n → ℤ) :
    IsCompact (shellSet ϖ m : Set (GL (Fin n) k)) := by
  have h := ((isCompact_KO (k := k) (n := Fin n)).prod (isCompact_KO (k := k) (n := Fin n))).image
    (f := fun p : GL (Fin n) k × GL (Fin n) k => p.1 * (diagGL fun i => ϖ ^ m i) * p.2) (by fun_prop)
  convert h using 1
  ext g
  rw [mem_shellSet]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

end SlopeTestRemainingChoices

theorem UpperTheory.integral_mem_addSubgroup_of_ramified_twisted_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ} (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (J : Subgroup (GL (Fin n) k)), IsOpen (J : Set (GL (Fin n) k)) → J ≤ KO k (Fin n) → μ (J : Set (GL (Fin n) k)) = 1 → ∀ (ϖ : kˣ) (ν : kˣ →* ℂˣ) (e : ℕ), IsUnif ϖ → ¬ IsUnram ν → CondLE ϖ e ν → ∀ (z : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) (a : ℕ), Function.support φ ⊆ GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.scaledInt ϖ n (-(a : ℤ)) → GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic.IsPeriodic ϖ 0 φ → (∀ j ∈ J, ∀ g : GL (Fin n) k, φ (j.val * g.val) * (ν (gdet j) : ℂ) = φ g.val) → ∀ M : AddSubgroup ℂ, (∀ m : Fin n → ℤ, (∀ i, -(a : ℤ) ≤ m i ∧ m i < 0) → ∀ g ∈ shellSet ϖ m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∈ M) → ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ ∈ M := by
  intro k hkField hkRel hkTop hkLocal hkMeas hkBorel n μ hμ J hJo hJK hJμ ϖ ν e hϖ hram hcond z φ a hS hP hinv M hM
  by_cases hint : Integrable (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) μ
  swap
  · rw [integral_undef hint]; exact M.zero_mem
  have hφ := mem_SB_of_periodic ϖ _ φ hS hP
  obtain ⟨-, h2, h3, h4⟩ := @GlobalTheory.T.zetaIntegralShells_vanish_beyondPeriod_ramified
    k hkField hkRel hkTop hkLocal hkMeas hkBorel ϖ hϖ ν e hram hcond n μ hμ φ hφ
  haveI : BorelSpace (GL (Fin n) k) := borel_GL
  haveI : μ.IsMulRightInvariant :=
    @_root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar k hkField hkRel hkTop hkLocal
      (Fin n) _ _ hkMeas hkBorel μ hμ
  have hsh : ∀ m : Fin n → ℤ, shell μ ϖ ν z φ m ∈ M := by
    intro m
    by_cases hm : ∀ i, -(a : ℤ) ≤ m i ∧ m i < 0
    · refine UpperTheory.setIntegral_mem_addSubgroup_of_openSubgroup_invariant μ J hJo hJμ (shellSet ϖ m) (isCompact_shellSet' ϖ m) ?_
        (fun g : GL (Fin n) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) ?_ M (hM m hm)
      · intro j hj g hg
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
        exact mem_shellSet.2 ⟨j * x, mul_mem (hJK hj) hx, y, hy, by simp only [mul_assoc]⟩
      · intro j hj g
        simp only [gdet_mul, apow_mul, map_mul, Units.val_mul,
          apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (hJK hj)), one_mul]
        rw [← hinv j hj g]
        ring
    · by_cases hm' : ∀ i, -(a : ℤ) ≤ m i
      · have : ∃ i, (0 : ℤ) ≤ m i := by
          by_contra h
          push_neg at h
          exact hm fun i => ⟨hm' i, h i⟩
        rw [h2 0 hP m this z]; exact M.zero_mem
      · rw [h3 a hS m hm' z]; exact M.zero_mem
  set S : {m : Fin n → ℤ // Antitone m} → Set (GL (Fin n) k) := fun m => shellSet ϖ m.1 with hSdef
  have hU : ⋃ m, S m = Set.univ :=
    Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).exists
  have hd : Pairwise (Function.onFun Disjoint S) := fun m m' hne =>
    Set.disjoint_left.2 fun g h1 h2 => hne ((GlobalTheory.ShellSumEqv.exists_unique_shell hϖ g).unique h1 h2)
  have hm : ∀ m, MeasurableSet (S m) := fun m => (GlobalTheory.ShellSumEqv.isOpen_shellSet ϖ m.1).measurableSet
  have hfin : (Function.support fun m : {m : Fin n → ℤ // Antitone m} => shell μ ϖ ν z φ m.1).Finite :=
    h4.subset fun m hm => ⟨z, hm⟩
  have key : ∫ g, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ =
      ∑ m ∈ hfin.toFinset, shell μ ϖ ν z φ m.1 :=
    calc _ = ∫ g in ⋃ m, S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ := by
          rw [hU, Measure.restrict_univ]
      _ = ∑' m, ∫ g in S m, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ :=
          integral_iUnion hm hd hint.integrableOn
      _ = ∑ᶠ m : {m : Fin n → ℤ // Antitone m}, shell μ ϖ ν z φ m.1 := tsum_eq_finsum hfin
      _ = _ := finsum_eq_sum _ hfin
  rw [key]
  exact sum_mem fun m _ => hsh m.1
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ n
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKo : IsOpen (U0.comap p : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  exact ⟨U0.comap p, hKo, IsCompact.of_isClosed_subset
    (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩
end
