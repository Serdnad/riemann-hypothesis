module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle010
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle011
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ModularityStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LatticeCongruenceSubgroupsOpenCompact
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.FixedVectorStatement : StFixVec := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFixVec | exact GlobalTheory.CompanionTheory.RgFl.stFixVec | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFixVec <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.MovingStatement : StMove := by
  first | exact @GlobalTheory.CompanionTheory.CartanMove.stMove | exact GlobalTheory.CompanionTheory.CartanMove.stMove | (intros; apply GlobalTheory.CompanionTheory.CartanMove.stMove <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.PairingStatement : StPair := by
  first | exact @GlobalTheory.CompanionTheory.HeckePair.stPair | exact GlobalTheory.CompanionTheory.HeckePair.stPair | (intros; apply GlobalTheory.CompanionTheory.HeckePair.stPair <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.ProjectionStatement : StProj := by
  first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.simple_of_commutative_statement : StComm → StSimple := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | exact GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.StatementCommutative : StComm := by
  first | exact @GlobalTheory.CompanionTheory.Bernstein.stComm | exact GlobalTheory.CompanionTheory.Bernstein.stComm | (intros; apply GlobalTheory.CompanionTheory.Bernstein.stComm <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.StatementStar : StStar := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | exact GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | (intros; apply GlobalTheory.CompanionTheory.RgFl.StarPf.stStar <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.hecke_operators_span_and_faithful : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | exact GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | (intros; apply GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis <;> assumption)
end

section

open CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.ModularityStatement : StMod := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCoinv.stMod | exact GlobalTheory.CompanionTheory.HeckeCoinv.stMod | (intros; apply GlobalTheory.CompanionTheory.HeckeCoinv.stMod <;> assumption)
end

section

open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl

theorem _root_.GlobalTheory.T.lattice_congruence_subgroups_open_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L), (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)), IsLat L Λ → (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J), (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧ (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧ IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧ ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧ ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.BLevel.main | exact GlobalTheory.CompanionTheory.BLevel.main | (intros; apply GlobalTheory.CompanionTheory.BLevel.main <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.NullSets

theorem null_of_lines {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] (φ : ℝ → G) (hφ : Measurable φ) {S : Set G}
    (hS : MeasurableSet S) (h : ∀ x, (volume : Measure ℝ) {t | φ t + x ∈ S} = 0) : μ S = 0 := by
  have hT : MeasurableSet {p : G × ℝ | φ p.2 + p.1 ∈ S} :=
    ((hφ.comp measurable_snd).add measurable_fst) hS
  have h1 : (μ.prod (volume : Measure ℝ)) {p : G × ℝ | φ p.2 + p.1 ∈ S} = 0 := by
    rw [Measure.prod_apply hT]
    have : ∀ x, (volume : Measure ℝ) (Prod.mk x ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = 0 := h
    exact (lintegral_congr (g := fun _ => 0) this).trans (by simp)
  rw [Measure.prod_apply_symm hT] at h1
  have h2 : ∀ t : ℝ, μ ((fun x => (x, t)) ⁻¹' {p : G × ℝ | φ p.2 + p.1 ∈ S}) = μ S :=
    fun t => measure_preimage_add μ (φ t) S
  simp only [h2, lintegral_const, measure_univ, Real.volume_univ] at h1
  by_contra hne
  simp [hne] at h1

section Line

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem q_line (hσ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y0 : Fin M → E) (a : F)
    (hy0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0 = algebraMap F E a) (R : Type) [CommRing R] [Nontrivial R] [Algebra F R]
    (x : Fin M → R ⊗[F] E) :
    ∃ c : R, ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (x + t • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i)) =
      algebraMap F R a * t ^ 2 + c * t + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J x := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set y : Fin M → R ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (y0 i) with hy
  have hs : ∀ e : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R e) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (σ e) := fun e => rfl
  have hyy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y0 y0) := by

      simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform, map_sum, map_mul, y, hs, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply,
      RingHom.coe_coe]
    rw [this, hy0, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have hrk : Module.finrank R (R ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, hσ.2.2.1]
  have hq : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J y = algebraMap F R a := by
    rw [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR, hyy, Algebra.trace_algebraMap, hrk, ← map_nsmul, ← map_mul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hst : ∀ t : R, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
    intro t
    show t ⊗ₜ[F] σ 1 = _
    rw [map_one]
    rfl
  refine ⟨algebraMap F R (1 / 2) *
    Algebra.trace R (R ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J x y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR R σ J y x), fun t => ?_⟩
  have e : t • y = algebraMap R (R ⊗[F] E) t • y := by
    rw [algebraMap_smul]
  rw [← hq]
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR
  generalize algebraMap F R (1 / 2) = u
  rw [e, GlobalTheory.HermLineZeros.hform_expand, hst, mul_assoc (algebraMap R (R ⊗[F] E) t)]
  simp only [← Algebra.smul_def, map_add (f := _), map_smul, smul_eq_mul]
  ring

end Line

section Coord

open GlobalTheory.CompanionTheory.SW.RealCoord

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def diag (t : ℝ) : Ainf F := (coordHomeo F).symm fun _ => t

theorem continuous_diag : Continuous (diag F) :=
  (coordHomeo F).symm.continuous.comp (continuous_pi fun _ => continuous_id)

theorem coord_diag (t : ℝ) (w : InfinitePlace F) : coord F (diag F t) w = t := by
  have h : coordHomeo F (diag F t) = fun _ => t := (coordHomeo F).apply_symm_apply _
  rw [coordHomeo_coe] at h
  exact congrFun h w

theorem continuous_coord (w : InfinitePlace F) : Continuous fun c : Ainf F => coord F c w := by
  have h : Continuous (coord F) := (isHomeomorph_coord F).continuous
  exact (continuous_apply w).comp h

theorem null_nonunit {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ] (f : G → Ainf F)
    (hf : ∀ w, Measurable fun X => coord F (f X) w) (φ : ℝ → G) (hφ : Measurable φ)
    (h : ∀ x w, {t : ℝ | coord F (f (φ t + x)) w = 0}.Finite) : μ {X | ¬ IsUnit (f X)} = 0 := by
  have sub : {X | ¬ IsUnit (f X)} ⊆ ⋃ w, {X | coord F (f X) w = 0} := by
    intro X hX
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hc
    apply hX
    have h1 : IsUnit (coord F (f X)) := Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (hc w)
    exact (isUnit_map_iff (coord F) _).1 h1
  refine measure_mono_null sub (measure_iUnion_null fun w => ?_)
  exact null_of_lines μ φ hφ (hf w (measurableSet_singleton 0)) fun x => (h x w).measure_zero _

end Coord

theorem null_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (Ainf F)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 ∧ μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0)) X)} = 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ ν hμ hν
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨hR1, hLC, hSC, hT2, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI := hR1
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨p1, p2, p3, p4, -, p6, -, p8, -, p10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := p1
  haveI := p2
  haveI := p3
  haveI := p4
  haveI hB2 := p8 1 M
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Ainf F)
  haveI : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul (Ainf F) _
  have hc := fun w => GlobalTheory.CompanionTheory.SW.NullSets.continuous_coord F w
  refine ⟨?_, ?_⟩
  · refine null_nonunit F ν id (fun w => (hc w).measurable) (diag F) (continuous_diag F).measurable ?_
    intro x w
    refine (Set.finite_singleton (-RealCoord.coord F x w)).subset fun t ht => ?_
    simp only [Set.mem_setOf_eq, id, map_add (f := _), Pi.add_apply, coord_diag] at ht
    simp only [Set.mem_singleton_iff]
    linarith
  · obtain ⟨y0, a, ha, hy0⟩ := GlobalTheory.HermLineZeros.exists_anisotropic hσ hM hJ
    set y : Fin M → Ainf F ⊗[F] E := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf F) (y0 i) with hy
    have hcont : Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0) :=
      continuous_const.mul (p6.comp ((p10 1 M J).matrix_elem 0 0))
    refine null_nonunit F μ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (X 0))
      (fun w => ((hc w).comp hcont).measurable) (fun t _ => diag F t • y) ?_ ?_
    · refine Continuous.measurable (continuous_pi fun _ => continuous_pi fun i => ?_)
      exact (continuous_diag F).smul continuous_const
    · intro x w
      obtain ⟨c, hc'⟩ := q_line hσ J y0 a hy0 (Ainf F) (x 0)
      set C := RealCoord.coord F c w
      set Q := RealCoord.coord F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Ainf F) σ J (x 0)) w
      have hne : (Polynomial.C (RealCoord.rho F w a) * Polynomial.X ^ 2 + Polynomial.C C * Polynomial.X
          + Polynomial.C Q : Polynomial ℝ) ≠ 0 := by
        intro h0
        have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 2) h0
        simp [Polynomial.coeff_X, Polynomial.coeff_C] at this
        exact ha this
      refine (Polynomial.finite_setOf_isRoot hne).subset fun t ht => ?_
      simp only [Set.mem_setOf_eq] at ht
      have e : (diag F t • y + x 0) = x 0 + diag F t • y := add_comm _ _
      have e2 : (fun _ : Fin 1 => diag F t • y) + x = fun i => (fun _ : Fin 1 => diag F t • y) i + x i := rfl
      rw [e2] at ht
      simp only [e] at ht
      rw [hc' (diag F t)] at ht
      simp only [map_add (f := _), map_mul, map_pow, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
        coord_diag, RealCoord.coord_algebraMap] at ht
      simpa [Polynomial.IsRoot] using ht

end GlobalTheory.CompanionTheory.SW.NullSets
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LenFib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, OneHerm.sigma_sigma hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem hR_self_fixed {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    have h := hJ.1 j i
    simp only [JR, Matrix.map_apply, inclR, sigR]
    simp [h]
  unfold hR hform

  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, sigR_sigR R hσ, hJR]
  ring

def gramH {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    HermR R σ 1 :=
  ⟨gramR R σ J X, by
    intro a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    exact hR_self_fixed R hσ hJ (X 0)⟩

theorem qR_eq_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = OneHerm.hermHalf R σ (gramH R hσ hJ X) :=
  rfl

theorem hermScal_qR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    ((hermScal R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)) : HermR R σ 1) :
      Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = gramR R σ J X := by
  rw [qR_eq_hermHalf R hσ hJ X, OneHerm.hermScal_hermHalf R hσ]
  rfl

theorem qR_of_gram [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E} {c : R}
    (h : gramR R σ J X = ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = c := by
  have h' : gramH R hσ hJ X = hermScal R σ c := Subtype.ext h
  rw [qR_eq_hermHalf R hσ hJ X, h', OneHerm.hermHalf_hermScal R hσ]

theorem isUnit_det_hermScal (σ : E →ₐ[F] E) {c : R} (hc : IsUnit c) :
    IsUnit ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det := by
  rw [Matrix.det_fin_one]
  exact hc.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)

theorem isUnit_det_gramR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E}
    (h : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : IsUnit (gramR R σ J X).det := by
  rw [← hermScal_qR R hσ hJ X]
  exact isUnit_det_hermScal R σ h

theorem continuous_qR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) := by
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgr⟩ := TopK.topTens_props F E σ hσ R
  have h := (hgr 1 M J).matrix_elem 0 0
  exact continuous_const.mul (htr.comp h)

theorem exists_bump [TopologicalSpace R] [LocallyCompactSpace R] [T2Space R]
    (hU : IsOpen {c : R | IsUnit c}) {c₀ : R} (hc₀ : IsUnit c₀) :
    ∃ χ : R → ℝ, Continuous χ ∧ tsupport χ ⊆ {c : R | IsUnit c} ∧ ∀ᶠ c in 𝓝 c₀, χ c = 1 := by
  obtain ⟨K, hK, hcK, hKU⟩ := exists_compact_subset hU hc₀
  obtain ⟨f, hf1, -, hfs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨f, f.continuous, hfs, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hcK] with c hc using hf1 hc

end GlobalTheory.CompanionTheory.SW.LenFib


open GlobalTheory.CompanionTheory.SW.LenFib in
theorem GlobalTheory.CompanionTheory.SW.isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} (fun c => m (hermScal R σ c)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc μ ν _ _ _ hμ0 m hm
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hOE, -⟩ := hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hfib, hint, hcont⟩ := hm
  set q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) with hq
  have hqc : Continuous q := LenFib.continuous_qR R hσ J
  have hUo : IsOpen {c : R | IsUnit c} := by
    have h := hOE.isOpen_range
    have he : Set.range (Units.val : Rˣ → R) = {c : R | IsUnit c} := by
      ext c
      exact Iff.rfl
    rwa [he] at h
  have hemb : MeasurableEmbedding (hermScal R σ) := (OneHerm.hermHomeo R hσ).measurableEmbedding
  have hsub : ∀ X, IsUnit (q X) → IsUnit (gramR R σ J X).det := fun X h =>
    LenFib.isUnit_det_gramR R hσ hJ h
  have hres : μ.restrict {X | IsUnit (gramR R σ J X).det} = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null ?_ hμ0
    intro X hX hXq
    exact hX (hsub X hXq)
  have hae : ∀ c, ∀ᵐ X ∂(m (hermScal R σ c)), q X = c := by
    intro c
    refine measure_mono_null ?_ (hfib (hermScal R σ c))
    intro X hX hXm
    exact hX (LenFib.qR_of_gram R hσ hJ hXm.1)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine measure_mono_null ?_ (hae c)
    intro X hX hXq
    exact hX ⟨hXq, Set.mem_univ X⟩
  · intro φ hφ
    have h := hint φ hφ
    rw [hres, hemb.lintegral_map] at h
    rw [Measure.restrict_univ, h]
  · intro φ hφc hφs _
    have key : ∀ c₀, IsUnit c₀ → Integrable φ (m (hermScal R σ c₀)) ∧
        ContinuousWithinAt (fun c => ∫ v, φ v ∂(m (hermScal R σ c))) {c | IsUnit c} c₀ := by
      intro c₀ hc₀
      obtain ⟨χ, hχc, hχs, hχ1⟩ := LenFib.exists_bump R hUo hc₀
      have hφ'c : Continuous fun X => φ X * χ (q X) := hφc.mul (hχc.comp hqc)
      have hφ's : HasCompactSupport fun X => φ X * χ (q X) := HasCompactSupport.mul_right hφs
      have hφ't : tsupport (fun X => φ X * χ (q X)) ⊆ {X | IsUnit (gramR R σ J X).det} := by
        intro X hX
        have h1 : X ∈ tsupport (χ ∘ q) := tsupport_mul_subset_right hX
        exact hsub X (hχs (tsupport_comp_subset_preimage χ hqc h1))
      obtain ⟨hI, hC⟩ := hcont _ hφ'c hφ's hφ't
      have heq : ∀ c, χ c = 1 → (fun X => φ X * χ (q X)) =ᵐ[m (hermScal R σ c)] φ := by
        intro c hc
        filter_upwards [hae c] with X hX
        rw [hX, hc, mul_one]
      have hmaps : Set.MapsTo (hermScal R σ) {c : R | IsUnit c}
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} :=
        fun c hc => LenFib.isUnit_det_hermScal R σ hc
      have hC' : ContinuousOn (fun c => ∫ v, φ v * χ (q v) ∂(m (hermScal R σ c))) {c | IsUnit c} :=
        hC.comp (OneHerm.continuous_hermScal R σ).continuousOn hmaps
      refine ⟨(hI _ (hmaps hc₀)).congr (heq c₀ hχ1.self_of_nhds), ?_⟩
      refine (hC' c₀ hc₀).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hχ1] with c hc
        exact (integral_congr_ae (heq c hc)).symm
      · exact (integral_congr_ae (heq c₀ hχ1.self_of_nhds)).symm
    exact ⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩
end
end
