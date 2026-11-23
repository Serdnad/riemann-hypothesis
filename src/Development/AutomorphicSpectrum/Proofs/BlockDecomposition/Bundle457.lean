module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle093
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle384
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap

theorem bijective_algHom (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) : Function.Bijective σ := by
  have hinj : Function.Injective σ := (σ : E →+* E).injective
  refine ⟨hinj, ?_⟩
  let τ : E →ₐ[ℚ] E := (σ : E →+* E).toRatAlgHom
  have h2 : Function.Injective τ.toLinearMap := hinj
  exact LinearMap.injective_iff_surjective.mp h2

theorem delta_map (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (c : Matrix (Fin n) (Fin n) E) : delta (c.map σ) = delta c := by
  classical
  let e : E ≃+* E := (AlgEquiv.ofBijective σ (bijective_algHom F E σ)).toRingEquiv
  let ψ : 𝓞 E ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hψ : ∀ o : 𝓞 E, algebraMap (𝓞 E) E (ψ o) = σ (algebraMap (𝓞 E) E o) := fun o => rfl
  let φ : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) :=
    { toFun := fun y i => ψ (y i)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro y z
        funext i
        simp }
  have hφ : ∀ y j, φ y j = ψ (y j) := fun y j => rfl
  have hvec : ∀ y : Fin n → 𝓞 E, (c.map σ) *ᵥ (fun j => algebraMap (𝓞 E) E (φ y j)) =
      fun i => σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) := by
    intro y
    funext i

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, hφ, hψ]
  have key : Kc c = (Kc (c.map σ)).comap φ := by
    ext y
    rw [AddSubgroup.mem_comap]
    show (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i) ↔
      (∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = ((c.map σ) *ᵥ fun j => algebraMap (𝓞 E) E (φ y j)) i)
    rw [hvec]
    refine forall_congr' fun i => ⟨fun h => h.elim fun o ho => ⟨ψ o, by rw [hψ, ho]⟩,
      fun h => h.elim fun o ho => ⟨ψ.symm o, ?_⟩⟩
    apply e.injective
    show σ (algebraMap (𝓞 E) E (ψ.symm o)) = σ _
    rw [← hψ, RingEquiv.apply_symm_apply, ho]
  have hsurj : Function.Surjective φ := fun y =>
    ⟨fun i => ψ.symm (y i), funext fun i => ψ.apply_symm_apply (y i)⟩
  show (Kc (c.map σ)).index = (Kc c).index
  rw [key]
  first
    | exact (AddSubgroup.index_comap_of_surjective hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective _ hsurj).symm
    | exact (AddSubgroup.index_comap_of_surjective (H := Kc (c.map σ)) hsurj).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.DeltaMap
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

theorem summable_comp_of_injective_prod {X Y Q : Type*} [Finite Q] {d : Y → ℝ}
    (hd : ∀ y, 0 ≤ d y) (hs : Summable d) (y : X → Y) (q : X → Q)
    (hinj : Function.Injective fun x => (y x, q x)) : Summable fun x => d (y x) := by
  have h1 : Summable (fun p : Y × Q => d p.1 * (fun _ : Q => (1 : ℝ)) p.2) :=
    Summable.mul_of_nonneg hs (Summable.of_finite) hd (fun _ => zero_le_one)
  have h2 := h1.comp_injective hinj
  simpa [Function.comp_def] using h2

theorem finite_quot_nsmul {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] {τ : ℕ} (hτ : 0 < τ) :
    Finite (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
  haveI : Module.Finite ℤ (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H m =>
    refine ⟨⟨(τ : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hτ.ne')⟩, ?_⟩
    have : ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range))
        = ((τ • m : M) : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
      rw [natCast_zsmul]; rfl
    show ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range)) = 0
    rw [this, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hermO_iff (σ : E →ₐ[F] E) (n : ℕ) (c : hermE σ n) :
    c ∈ hermO σ n ↔ ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b := Iff.rfl

def toInt (σ : E →ₐ[F] E) (n : ℕ) : hermO σ n →+ Matrix (Fin n) (Fin n) (𝓞 E) where
  toFun c := Matrix.of fun a b => Classical.choose ((mem_hermO_iff σ n c.1).1 c.2 a b)
  map_zero' := by
    ext a b
    have h := Classical.choose_spec ((mem_hermO_iff σ n (0 : hermO σ n).1).1 (0 : hermO σ n).2 a b)
    refine Eq.trans h ?_
    change _ = algebraMap (𝓞 E) E 0
    rw [map_zero]
    rfl
  map_add' := by
    intro c d
    ext a b
    have h1 := Classical.choose_spec ((mem_hermO_iff σ n (c + d).1).1 (c + d).2 a b)
    have h2 := Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)
    have h3 := Classical.choose_spec ((mem_hermO_iff σ n d.1).1 d.2 a b)
    refine Eq.trans h1 ?_
    change _ = algebraMap (𝓞 E) E (_ + _)
    rw [map_add (f := _)]
    exact Eq.trans rfl (Eq.symm (Eq.trans (congrArg₂ (· + ·) h2 h3) rfl))

theorem algebraMap_toInt (σ : E →ₐ[F] E) (n : ℕ) (c : hermO σ n) (a b : Fin n) :
    algebraMap (𝓞 E) E (toInt σ n c a b) = c.1.1 a b :=
  Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)

theorem toInt_injective (σ : E →ₐ[F] E) (n : ℕ) : Function.Injective (toInt σ n) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  rw [← algebraMap_toInt σ n c a b, ← algebraMap_toInt σ n d a b, h]

theorem finite_hermO (σ : E →ₐ[F] E) (n : ℕ) : Module.Finite ℤ (hermO σ n) :=
  Module.Finite.of_injective (toInt σ n).toIntLinearMap (toInt_injective σ n)

theorem Kc_le_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : Kc c ≤ Kc (c + l) := by
  intro y hy i
  obtain ⟨o, ho⟩ := hy i
  choose m hm using hl
  refine ⟨o + ∑ j, m i j * y j, ?_⟩
  rw [Matrix.add_mulVec, Pi.add_apply, map_add (f := _), ho]
  congr 1
  simp [Matrix.mulVec, dotProduct, hm]

theorem delta_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : delta (c + l) = delta c := by
  have h1 := Kc_le_add c l hl
  have h2 := Kc_le_add (c + l) (-l) (fun a b => by
    obtain ⟨o, ho⟩ := hl a b
    exact ⟨-o, by simp [ho]⟩)
  rw [add_neg_cancel_right] at h2
  unfold delta
  rw [le_antisymm h2 h1]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua


open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare in
theorem summable_quot_of_le_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  intro F E _ _ _ _ _ σ n Λ t ht τ hτ hΛ g hg hper C s hb hsum
  haveI : Module.Finite ℤ (hermO σ n) := finite_hermO σ n
  haveI := finite_quot_nsmul (M := hermO σ n) hτ
  let y : hermE σ n ⧸ Λ → hermE σ n ⧸ hermO σ n :=
    fun x => QuotientAddGroup.mk (t • Quotient.out x)
  have hmem : ∀ x, t • Quotient.out x - Quotient.out (y x) ∈ hermO σ n := by
    intro x
    have h : (QuotientAddGroup.mk (Quotient.out (y x)) : hermE σ n ⧸ hermO σ n)
        = QuotientAddGroup.mk (t • Quotient.out x) := QuotientAddGroup.out_eq' (y x)
    have := QuotientAddGroup.eq.1 h
    rwa [neg_add_eq_sub] at this
  let w : hermE σ n ⧸ Λ → hermO σ n := fun x => ⟨_, hmem x⟩
  let q : hermE σ n ⧸ Λ → hermO σ n ⧸ (nsmulAddMonoidHom τ : hermO σ n →+ hermO σ n).range :=
    fun x => QuotientAddGroup.mk (w x)
  have hinj : Function.Injective fun x => (y x, q x) := by
    intro x x' h
    have hy : y x = y x' := congrArg Prod.fst h
    have hq : q x = q x' := congrArg Prod.snd h
    obtain ⟨c, hc⟩ := QuotientAddGroup.eq.1 hq
    have hc' : τ • (c.1 : hermE σ n) = t • (Quotient.out x' - Quotient.out x) := by
      have := congrArg Subtype.val hc
      simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        AddSubgroup.coe_nsmul] at this
      rw [this]
      simp only [w, hy, smul_sub]
      abel
    have hd : Quotient.out x' - Quotient.out x = ((τ : F) / t) • (c.1 : hermE σ n) := by
      rw [div_eq_inv_mul, mul_smul, Nat.cast_smul_eq_nsmul F τ, hc', smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    have hmemΛ : Quotient.out x' - Quotient.out x ∈ Λ := hd ▸ hΛ _ c.2
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x']
    apply QuotientAddGroup.eq.2
    rwa [neg_add_eq_sub]
  have hdnn : ∀ z : hermE σ n ⧸ hermO σ n,
      0 ≤ (delta (Quotient.out z).1 : ℝ) ^ (-s) := fun z => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_comp_of_injective_prod hdnn hsum y q hinj
  refine Summable.of_nonneg_of_le (fun x => hg _) (fun x => ?_) (hs.mul_left |C|)
  have hdelta : delta (t • Quotient.out x).1 = delta (Quotient.out (y x)).1 := by
    have hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (w x).1.1 a b := (w x).2
    rw [← delta_add (Quotient.out (y x)).1 (w x).1.1 hl]
    congr 1
    simp [w]
  refine (hb _).trans ?_
  rw [hdelta]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (hdnn _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

theorem sig_sig_of_isCM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (t : R ⊗[F] E) :
    sigR R σ (sigR R σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sigR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (h : F) (t : R ⊗[F] E) :
    sigR R σ (h • t) = h • sigR R σ t :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id F R) σ) h t

theorem inclR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (h : F) (e : E) : inclR (F := F) R (h • e) = h • inclR (F := F) R e :=
  map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) h e

theorem sigR_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem denseRange_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] (hd : DenseRange (algebraMap F R)) :
    DenseRange (inclR R : E →+* R ⊗[F] E) := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have hφ := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.1 _ b
  let φ := hφ.homeomorph
  have hpi : DenseRange (Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    DenseRange.piMap fun _ => hd
  have hc : DenseRange (φ.symm ∘ Pi.map fun _ : Fin (Module.finrank F E) => (algebraMap F R)) :=
    φ.symm.surjective.denseRange.comp hpi φ.symm.continuous
  refine hc.mono ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨b.equivFun.symm a, ?_⟩
  apply φ.injective
  rw [Function.comp_apply, Homeomorph.apply_symm_apply]
  funext k
  show (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (b.equivFun.symm a)) k = _
  simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, apply_ite]

theorem hermE_dense_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  intro F E _ _ _ _ _ σ hCM n U hU g
  obtain ⟨hlc, hsc, ht2, -, -, hden, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hTR, -, -, -, hsig, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)
  have hincl := denseRange_inclR F E σ hCM (Af F) hden
  have hσ := sig_sig_of_isCM σ hCM

  have hmat : DenseRange (fun c : Matrix (Fin n) (Fin n) E => c.map (inclR (Af F))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hincl))

  let h : F := 1 / 2
  let Pm : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun m a b => h • (m a b + sigR (Af F) σ (m b a))
  have hPm : ∀ m, Pm m ∈ HermR (Af F) σ n := by
    intro m a b
    show sigR (Af F) σ (h • (m b a + sigR (Af F) σ (m a b))) = h • (m a b + sigR (Af F) σ (m b a))
    rw [sigR_smul, map_add (f := _), sigR_sigR _ _ hσ, add_comm]
  have hsmul : Continuous fun x : Af F ⊗[F] E => h • x := by
    simp_rw [Algebra.smul_def]
    exact continuous_const.mul continuous_id
  have hPc : Continuous Pm := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact hsmul.comp ((continuous_id.matrix_elem a b).add
      (hsig.comp (continuous_id.matrix_elem b a)))
  let P : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → HermR (Af F) σ n := fun m => ⟨Pm m, hPm m⟩
  have hP : Continuous P := hPc.subtype_mk hPm
  have hW : IsOpen {m | g - P m ∈ U} :=
    hU.preimage (continuous_const.sub hP)
  have hg : P g.1 = g := by
    apply Subtype.ext
    ext a b
    show h • (g.1 a b + sigR (Af F) σ (g.1 b a)) = g.1 a b
    rw [g.2 a b, ← two_smul F, smul_smul]
    norm_num [h]
  have hne : ({m | g - P m ∈ U} : Set _).Nonempty := ⟨g.1, by simp [hg, U.zero_mem]⟩
  obtain ⟨c₀, hc₀⟩ := hmat.exists_mem_open hW hne
  let c : Matrix (Fin n) (Fin n) E := fun a b => h • (c₀ a b + σ (c₀ b a))
  have hc : c ∈ hermE σ n := by
    intro a b
    show σ (h • (c₀ b a + σ (c₀ a b))) = h • (c₀ a b + σ (c₀ b a))
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def, map_add (f := _), hσ, add_comm]
  refine ⟨⟨c, hc⟩, ?_⟩
  have hcP : hermIn (Af F) σ n ⟨c, hc⟩ = P (c₀.map (inclR (Af F))) := by
    apply Subtype.ext
    ext a b
    show inclR (Af F) (h • (c₀ a b + σ (c₀ b a))) =
      h • (inclR (Af F) (c₀ a b) + sigR (Af F) σ (inclR (Af F) (c₀ b a)))
    rw [inclR_smul, map_add (f := _), sigR_inclR]
  rw [hcP]
  exact hc₀

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin

theorem delta_pos_index : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (c : Matrix (Fin n) (Fin n) E),
    delta c ≠ 0 :=
  fun _ _ _ _ c => GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_ne_zero c

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Fin
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField


theorem _root_.GlobalTheory.T.summable_denominator_power_of_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory


theorem _root_.GlobalTheory.T.specializes_iff_point_ideal_le : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x y : MP ℤ m n), x ⤳ y ↔ ptIdeal x ≤ ptIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le | exact GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le | (intros; apply GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le <;> assumption)
end
end
