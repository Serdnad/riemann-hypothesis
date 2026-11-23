module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle610
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem continuous_chiT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ ψ hψ T
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AF F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing (AF F)
  have htr : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) := GlobalTheory.CompanionTheory.SW.TopK.continuous_trace (AF F)
  unfold chiT
  refine hψ.1.comp (Continuous.neg (continuous_const.mul (htr.comp ?_)))
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_trace

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sum_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    x = ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] b k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]

theorem coord_sig {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E)
    (x : R ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ x) l =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k *
        (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] σ (b k)) l := by
  have h : sigR R σ x =
      ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] σ (b k)) := by
    conv_lhs => rw [sum_coord (R := R) b x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [sigR]

  rw [h, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

variable [FiniteDimensional F E]

theorem trace_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) x =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k * algebraMap F R (Algebra.trace F E (b k)) := by
  conv_lhs => rw [sum_coord (R := R) b x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, GlobalTheory.LatVac.trace_tmul, one_mul, smul_eq_mul]

theorem trace_tmul_one {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (x : R ⊗[F] E) :
    (Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x + sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), TensorProduct.add_tmul, hx, hy, map_add (f := _)]
    abel
  | tmul a e =>
    have h1 : (a * algebraMap F R (Algebra.trace F E e)) ⊗ₜ[F] (1 : E) =
        a ⊗ₜ[F] algebraMap F E (Algebra.trace F E e) := by
      rw [mul_comm, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have h2 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [GlobalTheory.LatVac.trace_tmul, h1, hσ, TensorProduct.tmul_add, h2]

theorem half_trace_tmul {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (h2 : (2 : F) ≠ 0) (x : R ⊗[F] E)
    (hx : sigR R σ x = x) :
    (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', trace_tmul_one σ hσ, hx, ← two_smul F x, smul_smul,
    one_div, inv_mul_cancel₀ h2, one_smul]

end Loc

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem latH_iff_at {d : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e)
    (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ)
    (h2 : (2 : F) ≠ 0)
    (hh : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F)
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k ∈
      v.adicCompletionIntegers F)
    (hs : ∀ i k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] σ (b i)) k ∈
      v.adicCompletionIntegers F)
    (ht : ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F)
    (Y : HermR (Fv F v) σ n) :
    Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈
        (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  constructor
  · rintro ⟨hd, ho⟩ a i k
    rcases lt_trichotomy a i with h | h | h
    · exact ho a i h k
    · subst h
      have e := half_trace_tmul (R := Fv F v) σ hσ h2 ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) (Y.2 a a)
      have e2 : (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k =
          (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) *
          (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k := by
        conv_lhs => rw [← e]
        have e3 : (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) ⊗ₜ[F] (1 : E) =
            (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) • ((1 : Fv F v) ⊗ₜ[F] (1 : E)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e3, map_smul, Finsupp.smul_apply, smul_eq_mul]
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k ∈ v.adicCompletionIntegers F
      rw [e2]
      exact mul_mem (hd a) (h1 k)
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) k ∈ v.adicCompletionIntegers F
      have e : sigR (Fv F v) σ ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i a) =
          (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i := Y.2 a i
      rw [← e, coord_sig]
      exact sum_mem fun l _ => mul_mem (ho i a h l) (hs l k)
  · intro h
    refine ⟨fun i => ?_, fun i j _ k => h i j k⟩
    rw [trace_coord b]
    exact mul_mem hh (sum_mem fun l _ => mul_mem (h i i l) (ht l))

end Place

theorem latH_iff_latV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔ (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM n d b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  obtain ⟨I1, I2⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hT : ∀ k, ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F := by
    intro k
    by_cases h0 : Algebra.trace F E (b k) = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · filter_upwards [I2 _ h0] with v hv
      exact hv.le
  filter_upwards [I2 (1 / 2) (by norm_num), I1 1, Filter.eventually_all.2 fun i => I1 (σ (b i)),
    Filter.eventually_all.2 hT] with v hh h1 hs ht Y
  exact latH_iff_at σ (GlobalTheory.CMTrace.trace_eq hCM) b v n two_ne_zero hh.le h1 hs ht Y

end GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Abstract

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

theorem fubini_unimod {dy : Measure Y} {dx : Measure X} [SFinite dy] [SFinite dx] {f : Y → ℂ} {g : X → ℂ}
    (hf : Integrable f dy) (hg : Integrable g dx) {u : Y → X → ℂ}
    (hu : AEStronglyMeasurable (Function.uncurry u) (dy.prod dx)) (hn : ∀ y x, ‖u y x‖ = 1) :
    ∫ y, f y * ∫ x, g x * u y x ∂dx ∂dy = ∫ x, g x * ∫ y, f y * u y x ∂dy ∂dx := by
  have h0 : Integrable (fun z : Y × X => f z.1 * g z.2) (dy.prod dx) := hf.mul_prod hg
  have hint : Integrable (Function.uncurry fun y x => f y * (g x * u y x)) (dy.prod dx) := by
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine (h0.aestronglyMeasurable.mul hu).congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hn, mul_one, le_refl]
  have hL : ∀ y, f y * ∫ x, g x * u y x ∂dx = ∫ x, f y * (g x * u y x) ∂dx := fun y =>
    (integral_const_mul _ _).symm
  have hR : ∀ x, g x * ∫ y, f y * u y x ∂dy = ∫ y, f y * (g x * u y x) ∂dy := fun x => by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hint

end Abstract

section Pair

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem pairHerm_sub (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S A B : HermR R σ n) :
    pairHerm R σ n S (A - B) = pairHerm R σ n S A - pairHerm R σ n S B := by
  simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]

theorem half_trace_mul_eq_pairHerm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem half_trace_mul_eq_pairHerm' (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ} (S G : HermR R σ n) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (Matrix.trace ((G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) =
    pairHerm R σ n S G := by
  rw [Matrix.trace_mul_comm]
  exact half_trace_mul_eq_pairHerm R σ S G

theorem continuous_pairHerm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [Module.Finite F E] (σ : E →ₐ[F] E) (n : ℕ) :
    Continuous fun z : HermR R σ n × HermR R σ n => pairHerm R σ n z.1 z.2 := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing R
  unfold pairHerm
  refine continuous_const.mul ((GlobalTheory.CompanionTheory.SW.TopK.continuous_trace R).comp ?_)
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
    ((continuous_subtype_val.comp continuous_snd).matrix_elem b a)

end Pair

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_pairHerm_gramH_sub (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hg : Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) (c : HermR R σ n) :
    Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2 - c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hp := continuous_pairHerm (F := F) (E := E) R σ n
  have hgH : Continuous fun x : Fin n → Fin M → R ⊗[F] E => gramH hCM hJ R x :=
    Continuous.subtype_mk hg _
  have m1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, gramH hCM hJ R z.2) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst (hgH.comp continuous_snd)
  have m2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      ((z.1, c) : HermR R σ n × HermR R σ n) :=
    Continuous.prodMk continuous_fst continuous_const
  have h1 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) =>
      pairHerm R σ n z.1 (gramH hCM hJ R z.2) := by
    have h := hp.comp m1
    exact h
  have h2 : Continuous fun z : HermR R σ n × (Fin n → Fin M → R ⊗[F] E) => pairHerm R σ n z.1 c := by
    have h := hp.comp m2
    exact h
  have := h1.sub h2
  refine this.congr fun z => ?_
  exact (pairHerm_sub R σ z.1 _ c).symm

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chiT_eq (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c) (y : HermR (AF F) σ n) :
    chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := by
  rw [← half_trace_mul_eq_pairHerm' (AF F) σ y (hermOf (AF F) σ T hT)]
  rfl

theorem psi_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x))) * chiT σ ψ T y =
    ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) := by
  have h2 : algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) :=
    half_trace_mul_eq_pairHerm (AF F) σ y (gramH hCM hJ (AF F) x)
  rw [h2, chiT_eq σ ψ T hT, ← AddChar.map_add_eq_mul, pairHerm_sub, sub_eq_add_neg]

theorem starN_mul_chiT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (y : HermR (AF F) σ n) :
    GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y =
      ∫ x, Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := by
  rw [GlobalTheory.CompanionTheory.SiegelND.starN, ← integral_mul_const]
  congr 1
  funext x
  rw [mul_assoc, psi_mul_chiT hCM hJ ψ T hT]

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN_fouH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) (hCM : IsCMExt F E σ), ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)), SFinite dx → SFinite db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ) db → (∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) ∧ ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ M J hJ n hCM ψ hψ dx db _ _ Φ hΦ τ hTh hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨hψc, hψn, -⟩ := hψ
  have hpc := continuous_pairHerm_gramH_sub (AF F) hCM hJ (hg n M J) (hermOf (AF F) σ T hT)
  refine ⟨?_, ?_⟩
  · have hp := continuous_pairHerm (F := F) (E := E) (AF F) σ n
    have m : Continuous fun y : HermR (AF F) σ n =>
        ((y, hermOf (AF F) σ T hT) : HermR (AF F) σ n × HermR (AF F) σ n) :=
      Continuous.prodMk continuous_id continuous_const
    have h1 := (hp.comp m).neg
    have h2 := hψc.comp h1
    have : GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T =
        fun y => ψ (-pairHerm (AF F) σ n y (hermOf (AF F) σ T hT)) := funext (chiT_eq σ ψ T hT)
    rw [this]
    exact h2
  · have hmeas : AEStronglyMeasurable (Function.uncurry fun (y : HermR (AF F) σ n)
        (x : Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT))) (db.prod dx) :=
      (hψc.comp hpc).aestronglyMeasurable
    have key := fubini_unimod hTh hΦ hmeas (fun y x => hψn _)
    have hL : ∀ y, fouH σ ψ db τ y * (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) =
        fouH σ ψ db τ y * ∫ x, Φ x *
          ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂dx := fun y => by
      rw [starN_mul_chiT hCM hJ ψ dx Φ T hT y]
    have hR : ∀ x, ∫ y, fouH σ ψ db τ y *
        ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - hermOf (AF F) σ T hT)) ∂db =
        τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) := fun x => by
      rw [hinv, neg_sub]
    simp_rw [hL]
    rw [key]
    simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem repr_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E)
    (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem trace_map_tensor {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      f (Algebra.trace R (R ⊗[F] E) x) := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R' b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b)]

  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : Algebra.TensorProduct.map f (AlgHom.id F E) (x * Algebra.TensorProduct.basis R b k) =
      Algebra.TensorProduct.map f (AlgHom.id F E) x * Algebra.TensorProduct.basis R' b k := by
    rw [_root_.map_mul]
    simp [Algebra.TensorProduct.basis_apply]
  rw [← repr_map_tensor f b, h]

theorem hCo_hermMap : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d), hCo R' σ b (hermMap f σ S) i = f (hCo R σ b S i) := by
  intro F E _ _ _ σ R R' _ _ _ _ f d b n S i
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, hermMap, Matrix.map_apply, map_mul, AlgHom.commutes, trace_map_tensor f b]
  · simp only [hCo, Sum.elim_inr, hermMap, Matrix.map_apply, repr_map_tensor f b]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswTop

theorem topC : PositivityTheory.Rg.Rsw.Cell.TopC := by
  intro D p e
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D p e
  exact ⟨inferInstance, inferInstance, inferInstance, h2, h1, h3, h4⟩

end GlobalTheory.CompanionTheory.RswTop
end
end
