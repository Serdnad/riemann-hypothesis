module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.FinCut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.G2OfLocalOrbitCharacter
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle568
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle558
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle602
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle528

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple

theorem decay_of_functionals {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [Fintype ι] {N : ℕ}
    (e : V ≃+ (Fin N → ℝ)) (hes : Continuous e.symm) (c : ι → V →+ ℂ) (hc : ∀ i, Continuous (c i))
    (f : SchwartzMap (Fin N → ℝ) ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X : V, (∃ i, R < ‖c i X‖) → ‖f (e X)‖ ≤ C / R ^ k := by
  let L : ι → (Fin N → ℝ) →L[ℝ] ℂ := fun i =>
    ((c i).comp e.symm.toAddMonoidHom).toRealLinearMap ((hc i).comp hes)
  have hL : ∀ i X, c i X = L i (e X) := by
    intro i X
    show c i X = c i (e.symm (e X))
    rw [e.symm_apply_apply]
  set T : ℝ := ∑ i, ‖L i‖ + 1 with hT
  have hTpos : 0 < T := by
    have : 0 ≤ ∑ i, ‖L i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  obtain ⟨C0, hC0⟩ := f.decay k 0
  refine ⟨C0 * T ^ k, fun R hR X ⟨i, hi⟩ => ?_⟩
  have hRpos : 0 < R := by linarith
  set x := e X with hx
  have hb : ‖c i X‖ ≤ T * ‖x‖ := by
    rw [hL]
    refine ((L i).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have : ‖L i‖ ≤ ∑ j, ‖L j‖ :=
      Finset.single_le_sum (f := fun j => ‖L j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  have hRx : R ≤ T * ‖x‖ := hi.le.trans hb
  have hd : ‖x‖ ^ k * ‖f x‖ ≤ C0 := by
    simpa [norm_iteratedFDeriv_zero] using hC0.2 x
  rw [le_div_iff₀ (pow_pos hRpos k)]
  calc ‖f x‖ * R ^ k ≤ ‖f x‖ * (T * ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hRpos.le hRx k) (norm_nonneg _)
    _ = (‖x‖ ^ k * ‖f x‖) * T ^ k := by rw [mul_pow]; ring
    _ ≤ C0 * T ^ k := mul_le_mul_of_nonneg_right hd (pow_nonneg hTpos.le k)

theorem schwartzArch_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)), IsHomeomorph κ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Continuous φ ∧ Integrable φ (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M) ∧ (∃ B : ℝ, ∀ X, ‖φ X‖ ≤ B) ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k := by
  intro F E _ _ _ _ _ σ hCM κ hκ n M d b lam hlam φ hφ
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, hsc, -, hrepr, hB, -, hgc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hB n M
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b lam hlam
  haveI := hW n M
  obtain ⟨N, e, he, hes, f, hf⟩ := hφ
  have hφe : φ = fun x => f (e x) := funext hf
  have hφc : Continuous φ := by rw [hφe]; exact f.continuous.comp he
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M with hμ
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hint : Integrable φ μ := by
    have h1 : Integrable (fun x => f x) (μ.map e) := f.integrable
    rw [hφe]
    exact (integrable_map_measure h1.aestronglyMeasurable he.measurable.aemeasurable).1 h1
  refine ⟨hφc, hint, ?_, fun k => ?_⟩
  · obtain ⟨C0, hC0⟩ := f.decay 0 0
    refine ⟨C0, fun X => ?_⟩
    rw [hf]
    simpa [norm_iteratedFDeriv_zero] using hC0.2 (e X)
  · let c : (Fin n × Fin M × NumberField.InfinitePlace F) → (Fin n → Fin M → Ainf F ⊗[F] E) →+ ℂ := fun p =>
      { toFun := fun X => κ (X p.1 p.2.1) p.2.2
        map_zero' := by simp
        map_add' := fun X Y => by simp }
    have hc : ∀ p, Continuous (c p) := fun p =>
      (continuous_apply p.2.2).comp (hκ.continuous.comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1)))
    obtain ⟨C, hC⟩ := decay_of_functionals e hes c hc f k
    refine ⟨C, fun R hR X hX => ?_⟩
    rw [hf]
    refine hC R hR X ?_
    simp only [boxK, Set.mem_setOf_eq, not_forall, not_le] at hX
    obtain ⟨a, i, w, h⟩ := hX
    exact ⟨(a, i, w), h⟩

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.SchwartzTuple
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F.F5

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FinFamAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Cov (S : Set (Pre E n)) : Prop :=
  ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ S, ∃ j, PreEquiv (D j) D'

theorem cov_of_rel {S : Set (Pre E n)} {ι : Type*} [Finite ι] (P : ι → Pre E n → Prop)
    (h1 : ∀ D ∈ S, ∃ a, P a D)
    (h2 : ∀ a, ∀ D₁ ∈ S, ∀ D₂ ∈ S, P a D₁ → P a D₂ → PreEquiv D₁ D₂) : Cov S := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨D₀, -⟩ := hS
    let e := Finite.equivFin ι
    refine ⟨Nat.card ι, fun j => if h : ∃ D ∈ S, P (e.symm j) D then h.choose else D₀, ?_⟩
    intro D' hD'
    obtain ⟨a, ha⟩ := h1 D' hD'
    have hex : ∃ D ∈ S, P (e.symm (e a)) D := ⟨D', hD', by rw [Equiv.symm_apply_apply]; exact ha⟩
    refine ⟨e a, ?_⟩
    show PreEquiv (if h : ∃ D ∈ S, P (e.symm (e a)) D then h.choose else D₀) D'
    rw [dite_eq_left hex]
    obtain ⟨hmem, hP⟩ := hex.choose_spec
    exact h2 _ _ hmem _ hD' hP (by rw [Equiv.symm_apply_apply]; exact ha)
  · exact ⟨0, Fin.elim0, fun D' hD' => (hS ⟨D', hD'⟩).elim⟩

theorem cov_of_cover {S : Set (Pre E n)} {ι : Type*} [Finite ι] (A : ι → Set (Pre E n))
    (hA : ∀ a, Cov (A a)) (hS : ∀ D ∈ S, ∃ a, D ∈ A a) : Cov S := by
  classical
  choose k D hD using fun a => (hA a : ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' ∈ A a, ∃ j, PreEquiv (D j) D')
  let e := Finite.equivFin (Σ a, Fin (k a))
  refine ⟨Nat.card (Σ a, Fin (k a)), fun j => D (e.symm j).1 (e.symm j).2, ?_⟩
  intro D' hD'
  obtain ⟨a, ha⟩ := hS D' hD'
  obtain ⟨j, hj⟩ := hD a D' ha
  refine ⟨e ⟨a, j⟩, ?_⟩
  show PreEquiv (D (e.symm (e ⟨a, j⟩)).1 (e.symm (e ⟨a, j⟩)).2) D'
  rw [Equiv.symm_apply_apply]
  exact hj

abbrev Shape (E : Type) [Field E] : Type :=
  Σ c : ℕ, (Fin c → ℕ) × (Fin c → (E →+* ℂ) → Multiset ℂ)

def shape (D : Pre E n) : Shape E := ⟨D.c, D.N, D.m⟩

def bounded (E : Type) [Field E] (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : Set (Shape E) :=
  {t | t.1 ≤ n ∧ (∀ i, t.2.1 i ≤ n) ∧ ∀ i τ, t.2.2 i τ ≤ m τ}

theorem finite_le (s : Multiset ℂ) : {x : Multiset ℂ | x ≤ s}.Finite := by
  exact (Multiset.finite_toSet s.powerset).subset fun x hx => Multiset.mem_powerset.mpr hx

theorem bounded_finite (n : ℕ) (m : (E →+* ℂ) → Multiset ℂ) : (bounded E n m).Finite := by
  refine ((Set.finite_Iic n).biUnion fun c _ =>
    (((Set.Finite.pi fun _ : Fin c => Set.finite_Iic n).prod
      (Set.Finite.pi fun _ : Fin c => Set.Finite.pi fun τ => finite_le (m τ))).image
        (fun p => (⟨c, p⟩ : Shape E)))).subset ?_
  rintro ⟨c, N, mm⟩ ⟨hc, hN, hm⟩
  exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨(N, mm), ⟨fun i _ => hN i, fun i _ τ _ => hm i τ⟩, rfl⟩⟩

theorem shape_mem_bounded (m : (E →+* ℂ) → Multiset ℂ) (D : Pre E n)
    (hm : ∀ τ, ∑ i, D.m i τ = m τ) : shape D ∈ bounded E n m := by
  refine ⟨?_, fun i => ?_, fun i τ => ?_⟩
  · show D.c ≤ n
    calc D.c = ∑ _i : Fin D.c, 1 := by simp
      _ ≤ ∑ i, D.N i := Finset.sum_le_sum fun i _ => D.pos i
      _ = n := D.h
  · show D.N i ≤ n
    exact (Finset.single_le_sum (f := D.N) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans D.h.le
  · show D.m i τ ≤ m τ
    rw [← hm τ]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun j _ => Multiset.zero_le _) (Finset.mem_univ i)

theorem cov_fibre (hL : LevelFactor) (hF : FinDiscN)
    (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
    (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (hK : IsLevel K) (hW : ∀ N, FiniteDimensional ℂ (W N))
    (t : Shape E) :
    Cov {D' : Pre E n | shape D' = t ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
  classical
  obtain ⟨c, N, mm⟩ := t
  by_cases hsum : ∑ i, N i = n
  swap
  · refine ⟨0, Fin.elim0, ?_⟩
    rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, -, -⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, -⟩ := Prod.mk.inj (eq_of_heq hh)
    exact absurd h' hsum
  choose Ki hKiopen hKiKGL hKisph using fun w => hL E w c n N hsum (K w) (hK.1 w)
  have hlev : ∀ i : Fin c, IsLevel (fun w => Ki w i) := fun i =>
    ⟨fun w => hKiopen w i, hK.2.mono fun w hw => hKiKGL w hw i⟩
  choose k σs hσs using fun i : Fin c =>
    hF E (N i) (fun w => Ki w i) (W (N i)) (mm i) (hlev i) (hW (N i))
  refine cov_of_rel (ι := (i : Fin c) → Fin (k i))
    (fun a D => ∃ hc : D.c = c, ∀ (i : Fin D.c) w, ∃ hs hi,
      D.cls i w = GlobalTheory.LocGL.IrrGL.of (σs (Fin.cast hc i) (a (Fin.cast hc i)) w).ρ hs hi) ?_ ?_
  · rintro ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ ⟨hsh, hsph, hKt⟩
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hsh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh)
    choose a ha using fun i => hσs i (V' i) (fun w => σ' i w) (disc' i) (fun w => loc' i w)
      (fun τ => inf' i τ) (fun w => hKisph w (fun j => σ' j w) (hsph w) i) (hKt i)
    exact ⟨a, rfl, fun i w => ⟨_, _, (ha i w).symm⟩⟩
  · rintro a ⟨c₁, N₁, h₁, V₁, σ₁, m₁, pos₁, disc₁, loc₁, inf₁⟩ ⟨hsh₁, -, -⟩
      ⟨c₂, N₂, h₂, V₂, σ₂, m₂, pos₂, disc₂, loc₂, inf₂⟩ ⟨hsh₂, -, -⟩ ⟨hc₁, hP₁⟩ ⟨hc₂, hP₂⟩
    obtain ⟨rfl, hh₁⟩ := Sigma.mk.inj_iff.mp hsh₁
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₁)
    obtain ⟨rfl, hh₂⟩ := Sigma.mk.inj_iff.mp hsh₂
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq hh₂)
    refine ⟨finCongr rfl, fun i w => ?_, fun i τ => rfl⟩
    obtain ⟨hs₁, hi₁, e₁⟩ := hP₁ i w
    obtain ⟨hs₂, hi₂, e₂⟩ := hP₂ i w
    exact e₁.trans e₂.symm

theorem finFamOf : FinFamOf := by
  intro hL hF E _ _ _ n K W m hK hW
  have hS : Cov {D' : Pre E n | (∀ τ, ∑ i, D'.m i τ = m τ) ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)} := by
    have hfin := bounded_finite (E := E) n m
    haveI := hfin.to_subtype
    refine cov_of_cover (ι := bounded E n m) (fun t => {D' : Pre E n | shape D' = t.1 ∧
      (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) ∧
      ∀ i, HasKType (W (D'.N i)) (D'.V i)}) (fun t => cov_fibre hL hF K W hK hW t.1) ?_
    rintro D' ⟨hm, hsph, hKt⟩
    exact ⟨⟨shape D', shape_mem_bounded m D' hm⟩, rfl, hsph, hKt⟩
  obtain ⟨k, D, hD⟩ := hS
  exact ⟨k, D, fun D' hm hsph hKt => hD D' ⟨hm, hsph, hKt⟩⟩

end GlobalTheory.CompanionTheory.FinFamAssembly

end
end

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.constant_term_hecke_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ν : (w.adicCompletion E)ˣ →* ℂˣ) (ϖ : w.adicCompletion E), IsSplitAt w → IsUnifV E w ϖ → ∀ (k : ℕ) (m : GLw a w × GLw b w), ctT h w ν ϖ k m = (ν ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) * (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * hint (intMat a b w) fun X => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.ctT_split_eq | exact GlobalTheory.CompanionTheory.CtS.ctT_split_eq | (intros; apply GlobalTheory.CompanionTheory.CtS.ctT_split_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

theorem _root_.GlobalTheory.T.globalComplexCoefficients_of_local_orbit_character : EllLocal → KapOrbAE → ChWMap → GlobalComplexCoefficients := by
  first | exact @GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c | exact GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c | (intros; apply GlobalTheory.CompanionTheory.resultantFactorHypotheses.g2c <;> assumption)
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvF

def twistEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H)
    (hc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) : H × H ≃ₜ* H × H where
  toFun y := (y.1, σ y.2)
  invFun y := (y.1, σ y.2)
  left_inv y := by simp [hσ]
  right_inv y := by simp [hσ]
  map_mul' a b := by simp
  continuous_toFun := continuous_fst.prodMk (hc.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (hc.comp continuous_snd)

theorem twOrb_conj_of_biinv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K K' : Subgroup G) (δ g : G) (F : G → ℂ) (hθ : Continuous θ) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) :
    twOrb θ K (g⁻¹ * δ * θ g) F = twOrb θ K δ F :=
  GlobalTheory.TwOrbConj.twOrb_twConj G θ K δ g F
    (GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact θ K K' δ F hθ hK hK' hF)

theorem splitConv_of_finite : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ σ K hc hσ hσK hKo hKc d d' f₁ f₂ K' hK'o hK'K hσK' h₁ h₂ hG hfin
  set θ := (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom with hθ
  have hθc : Continuous θ := (hc.comp continuous_snd).prodMk (hc.comp continuous_fst)
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hK'K'o : IsOpen ((K'.prod K' : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hK'o.prod hK'o
  have hinv : ∀ k ∈ K'.prod K', ∀ x : H × H,
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (k * x) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x ∧
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (x * k) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x := by
    rintro ⟨k₁, k₂⟩ hk ⟨x₁, x₂⟩
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hk₂' : σ k₂ ∈ K' := hσK' _ hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).1, map_mul, (h₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).2, map_mul, (h₂.2 _ hk₂' _).2]
  have hconj : ((1, d') : H × H)⁻¹ * (d, d') * θ (1, d') = (d * σ d', 1) := by
    have e : θ (1, d') = (σ d', 1) := by simp [hθ]
    rw [e]
    ext <;> simp
  have step₁ := twOrb_conj_of_biinv θ (K.prod K) (K'.prod K') (d, d') (1, d')
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) hθc hKKc hK'K'o hinv
  rw [hconj] at step₁
  rw [← step₁]
  have step₂ := GlobalTheory.EulerTw.Transport.twOrb_transport (H × H) (H × H) (twistEquiv σ hc hσ) θ
    (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom (K.prod K) (K.prod K) (d * σ d', 1)
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (fun y : H × H => f₁ y.1 * f₂ y.2)
    (by
      rintro ⟨x₁, x₂⟩
      show (σ x₂, σ (σ x₁)) = (σ x₂, x₁)
      rw [hσ])
    (by
      rintro ⟨x₁, x₂⟩
      show x₁ ∈ K ∧ x₂ ∈ K ↔ x₁ ∈ K ∧ σ x₂ ∈ K
      refine and_congr_right fun _ => ⟨hσK _, fun h => ?_⟩
      simpa [hσ] using hσK _ h)
    (fun _ => rfl)
  have he : (twistEquiv σ hc hσ) (d * σ d', 1) = (d * σ d', 1) := by
    show (d * σ d', σ 1) = (d * σ d', 1)
    rw [map_one]
  rw [he] at step₂
  rw [step₂]
  exact GlobalTheory.T.twisted_orbital_swap_convolution H K K' (d * σ d') f₁ f₂ hKo hKc hK'o hK'K h₁ h₂ hG
    (GlobalTheory.T.exists_compact_conjugacy_transversal H K (d * σ d') hKc hfin)

end GlobalTheory.CompanionTheory.SplitConvF
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
namespace GlobalTheory.CompanionTheory.MuC

theorem isClosed_hermS_val (D : D7) (p : ℕ) (e : AE D) :
    IsClosed ((hermS D p e : AddSubgroup (hermA D p)) : Set (hermA D p)) := by
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hc : Continuous fun x : hermA D p => e • (x : Formalism.IndefR.Datum.Mx D p p) :=
    (continuous_const_smul e).comp continuous_subtype_val
  exact isClosed_eq hc continuous_subtype_val



theorem hermS_facts : ∀ (D : D7) (p : ℕ) (e : AE D), LocallyCompactSpace (hermS D p e) ∧ T2Space (hermS D p e) ∧
    SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e) ∧ IsTopologicalAddGroup (hermS D p e) := by
  intro D p e
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hS := isClosed_hermS_val D p e
  have hA : IsClosed ((hermA D p : AddSubgroup (Formalism.IndefR.Datum.Mx D p p)) : Set (Formalism.IndefR.Datum.Mx D p p)) :=
    GlobalTheory.CompanionTheory.HermVol.isClosed_hermA
  haveI : LocallyCompactSpace (Formalism.IndefR.Datum.Mx D p p) :=
    show LocallyCompactSpace (Fin p → Fin p → AE D) from inferInstance
  haveI : SecondCountableTopology (Formalism.IndefR.Datum.Mx D p p) :=
    show SecondCountableTopology (Fin p → Fin p → AE D) from inferInstance
  haveI : BorelSpace (Formalism.IndefR.Datum.Mx D p p) := by
    first
    | exact show BorelSpace (Fin p → Fin p → AE D) from inferInstance
    | exact ⟨rfl⟩
    | exact Matrix.borelSpace
  haveI : SecondCountableTopology (hermA D p) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermA D p : Set (Formalism.IndefR.Datum.Mx D p p))) from inferInstance
  haveI : SecondCountableTopology (hermS D p e) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermS D p e : Set (hermA D p))) from inferInstance
  haveI : LocallyCompactSpace (hermA D p) := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end GlobalTheory.CompanionTheory.MuC
end
