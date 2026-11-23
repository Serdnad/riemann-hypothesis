module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle591
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle295
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle579
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle595
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle592
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle534
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec.ModulusPf

variable {E : Type} [Field E] [NumberField E]

theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m + m') = GlobalTheory.CellDec.adl ϖ m * GlobalTheory.CellDec.adl ϖ m' := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m + m') v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m' v : (v.adicCompletion E)ˣ) : v.adicCompletion E)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

theorem adl_sub (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m - m') = GlobalTheory.CellDec.adl ϖ m * (GlobalTheory.CellDec.adl ϖ m')⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← adl_add, sub_add_cancel]

theorem zpow_sum_real {ι : Type} (q : ℝ) (hq : q ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

theorem sum_pairs_eq_wtS {n : ℕ} (a : Fin n → ℤ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (a p.1.1 - a p.1.2) = GlobalTheory.CellDec.wtS n a := by
  classical
  rw [GlobalTheory.CellDec.wtS, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (by simp) (fun p : Fin n × Fin n => a p.1 - a p.2), Finset.sum_filter, Fintype.sum_prod_type]

end GlobalTheory.CellDec.ModulusPf

namespace GlobalTheory.CellDec.ModulusPf

theorem modulus_conj : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  intro E _ _ n _ _ ν _ ϖ hϖ l A hA
  classical
  set t := GlobalTheory.CellDec.tl n ϖ l with ht
  let d : Fin n → (AdeleRing (𝓞 E) E)ˣ := fun i => finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))
  have htd : t = GlobalTheory.SmGL.diagT (Ad E) (Fin n) d := GlobalTheory.CellDec.tl_eq_diagT ϖ l
  let φ : GlobalTheory.CellDec.NA E n → GlobalTheory.CellDec.NA E n := fun u => ⟨t * u * t⁻¹, GlobalTheory.CellDec.tl_conj_mem ϖ l u.2⟩
  have hφc : Continuous φ :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hset : {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = t * (u : GA E n) * t⁻¹} = φ ⁻¹' A := by
    ext u
    constructor
    · rintro ⟨a, ha, h⟩
      have : φ u = a := Subtype.ext h.symm
      simpa [Set.mem_preimage, this] using ha
    · intro hu
      exact ⟨φ u, hu, rfl⟩
  rw [hset, ← Measure.map_apply hφc.measurable hA]

  let co : GlobalTheory.CellDec.NA E n → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) :=
    fun u p => ((u : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) p.1.1 p.1.2
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph (Ad E) n
  have hco : ⇑e = co := funext he
  let μR : Measure (Ad E) := Measure.addHaar
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi (Ad E) n μR ν
  let mm : {p : Fin n × Fin n // p.1 < p.2} → (HeightOneSpectrum (𝓞 E) →₀ ℤ) := fun p =>
    Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.1) rfl l - Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.2) rfl l
  let a : {p : Fin n × Fin n // p.1 < p.2} → Ad E := fun p => ((finId E (GlobalTheory.CellDec.adl ϖ (mm p)) : (Ad E)ˣ) : Ad E)
  let S : ({p : Fin n × Fin n // p.1 < p.2} → Ad E) → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) := fun x p => a p * x p
  have hentry : ∀ (u : GA E n) (i j : Fin n), ((t * u * t⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      ((d i : Ad E) * (((d j)⁻¹ : (Ad E)ˣ) : Ad E)) * (u : Matrix (Fin n) (Fin n) (Ad E)) i j := by
    intro u i j
    rw [htd, ← map_inv, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [Pi.inv_apply]
    ring
  have ha : ∀ p, a p = (d p.1.1 : Ad E) * (((d p.1.2)⁻¹ : (Ad E)ˣ) : Ad E) := by
    intro p
    simp only [a, mm, d, adl_sub, map_mul, map_inv, Units.val_mul]
  have hSco : co ∘ φ = S ∘ co := by
    funext u p
    simp only [Function.comp_apply, co, S, φ]
    rw [hentry, ha]
  let k : {p : Fin n × Fin n // p.1 < p.2} → ℝ≥0∞ := fun p => ENNReal.ofReal (∏ v ∈ l.support, (qV E v : ℝ) ^ (mm p v))
  have hk : ∀ p, Measure.map (fun x : Ad E => a p * x) μR = k p • μR := fun p =>
    GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers E ϖ hϖ (mm p) l.support (fun v hv => by simp [mm, Finsupp.notMem_support_iff.1 hv]) μR
  haveI : ∀ p, SigmaFinite (k p • μR) := fun p => (inferInstance : SigmaFinite ((Real.toNNReal _) • μR))
  have hSm : Measurable S := by
    refine Measurable.of_eval fun p => ?_
    exact (measurable_const_mul (a p)).comp (measurable_pi_apply p)
  have hS : Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) =
      (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
    have h1 : Measure.pi (fun p => k p • μR) = Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.map_apply hSm (MeasurableSet.univ_pi hs)]
      rw [show S ⁻¹' Set.univ.pi s = Set.univ.pi fun p => (fun x : Ad E => a p * x) ⁻¹' s p from
        Set.preimage_pi Set.univ s fun p (x : Ad E) => a p * x]
      rw [Measure.pi_pi]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← hk p, Measure.map_apply (measurable_const_mul _) (hs p)]
    have h2 : Measure.pi (fun p => k p • μR) = (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
      rfl
    rw [← h1, h2]
  have hK : (∏ p, k p) = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) := by
    simp only [k]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => Finset.prod_nonneg fun v _ => zpow_nonneg (Nat.cast_nonneg _) _)]
    congr 1
    rw [Finset.prod_comm, GlobalTheory.CellDec.dinv]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hq : (qV E v : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by rw [qV, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    rw [zpow_sum_real _ hq, ← sum_pairs_eq_wtS]
    congr 1
  have key : Measure.map φ ν = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν := by
    have hem : Measurable e := e.continuous.measurable
    have h3 : Measure.map e (Measure.map φ ν) = Measure.map e (ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν) := by
      have hc' : Measure.map e ν = c • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
        rw [hco]; exact hc
      rw [Measure.map_map hem hφc.measurable, hco, hSco, ← Measure.map_map hSm (hco ▸ hem), ← hco, hc',
        Measure.map_smul, Measure.map_smul, hS, hc', ← hK, smul_comm]
      all_goals first | exact hem.aemeasurable | exact hSm.aemeasurable
    have h4 := congrArg (Measure.map e.toMeasurableEquiv.symm) h3
    rwa [show (⇑e : GlobalTheory.CellDec.NA E n → _) = ⇑e.toMeasurableEquiv from rfl, MeasurableEquiv.map_symm_map,
      MeasurableEquiv.map_symm_map] at h4
  rw [key]
  rfl
end GlobalTheory.CellDec.ModulusPf

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

theorem lift_map_eq_of_smul {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A) (hp : φ p = 1)
    (M M' : Matrix (Fin m) (Fin n) A) (h : p • M = p • M') : M.map φ = M'.map φ := by
  ext i j
  have := congrArg φ (congrFun (congrFun h i) j)
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, hp, one_mul, Matrix.map_apply] using this

theorem lift_smul_eq_of_map {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A)
    (hker : ∀ z, φ z = 0 ↔ p * z = 0) (M M' : Matrix (Fin m) (Fin n) A) (h : M.map φ = M'.map φ) : p • M = p • M' := by
  ext i j
  have h2 := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at h2
  have h3 : φ (M i j - M' i j) = 0 := by rw [map_sub, h2, sub_self]
  rw [hker, mul_sub, sub_eq_zero] at h3
  simpa only [Matrix.smul_apply, smul_eq_mul] using h3

theorem lift_smul_conj {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • (β.1 * M * (β⁻¹).1) = β.1 * (p • M) * (β⁻¹).1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_smul_conj_inv {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • ((β⁻¹).1 * M * β.1) = (β⁻¹).1 * (p • M) * β.1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_conj_mul_smul {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M M' : Matrix (Fin n) (Fin n) A)
    (h : p • (M * M') = p • (1 : Matrix (Fin n) (Fin n) A)) :
    p • ((β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1)) = p • (1 : Matrix (Fin n) (Fin n) A) := by
  have e3 : (β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1) = β.1 * (M * M') * (β⁻¹).1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mul]
  rw [e3, lift_smul_conj, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]

theorem lift_conj_part {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (g M : Matrix (Fin n) (Fin n) A)
    (h : p • g = p • (β.1 * M * (β⁻¹).1)) : p • ((β⁻¹).1 * g * β.1) = p • M := by
  rw [lift_smul_conj_inv, h, lift_smul_conj]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem lift_chart_idem {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) (he : toEAf D e * toEAf D e = toEAf D e) : φ (toEAf D e) = 1 := by
  have h0 : φ (1 - toEAf D e) = 0 := by
    rw [hker, mul_sub, mul_one, he, sub_self]
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0.symm

theorem lift_chart_int {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hsurj : Function.Surjective φ) (h1 : φ (toEAf D e) = 1)
    (hint : ∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F)
    (o : GlobalTheory.SplitHecke.Ov D v) : ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ (s : Formalism.IndefR.Lev.EAf D) = (o : Fv D.host.F v) := by
  obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
  refine ⟨⟨toEAf D e * z, (hint z).2 (hz ▸ o.2)⟩, ?_⟩
  show φ (toEAf D e * z) = _
  rw [map_mul, h1, one_mul, hz]

theorem lift_frG_one {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) :
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG T βT 1 = 1 := by
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
  rw [map_one, mul_one, inv_mul_cancel]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_St_of_part_inv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ) (hΛ : HatSelfDual σ J Λ)
    (p : Formalism.L2.Herm.intAf F E) (hq : Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p ∈ Formalism.L2.Herm.intAf F E)
    (Y Y' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))
    (hmm : (p : E ⊗[F] Formalism.L2.Herm.Af F) • ((β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) *
      (β.1 * Y'.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) = (p : E ⊗[F] Formalism.L2.Herm.Af F) • 1)
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Formalism.L2.Herm.Af F))
    (f : E ⊗[F] Formalism.L2.Herm.Af F) (hf : f = p + Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p) (hs : f • (g.1 - 1) = g.1 - 1)
    (hY : (p : E ⊗[F] Formalism.L2.Herm.Af F) • g.1 =
      (p : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) : g ∈ St β := by
  subst hf
  exact (mem_St_iff β Λ hβ g).2 (stab_of_part _ _ _ hΛ p.2 hq g hg hs _ _ (frame_mulVec β Λ hβ Y)
    (frame_mulVec β Λ hβ Y') hmm hY)

end Gen



theorem exists_supp_lift_adj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N : ℕ), IsBaseFrame S βS Λ N → ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), ∃ κ : GA D S, SuppAt e S κ ∧ κ ∈ GfC S ∧ finE S κ ∈ St βS ∧ (redFn βS PP (finE S κ)).val.map ι = h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) ∧ (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T κ 1 x) = h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * rdAdj S T βS βT φ x := by
  intro D S T βS βT e PP v φ ι he hL Λ N hB h
  obtain ⟨hsurj, hker, hint, hres⟩ := hL
  have := PP.isPrime
  obtain ⟨p, hp, hpp, hres1⟩ := exists_idem_int he
  have hpe : toEAf D e = (p : Formalism.IndefR.Lev.EAf D) := hp.symm
  have hpp' : toEAf D e * toEAf D e = toEAf D e := by rw [hpe]; exact congrArg Subtype.val hpp
  have hp1 : φ (p : Formalism.IndefR.Lev.EAf D) = 1 := hpe ▸ lift_chart_idem hker hpp'
  have hker' : ∀ z, φ z = 0 ↔ (p : Formalism.IndefR.Lev.EAf D) * z = 0 := fun z => hpe ▸ hker z
  choose lf hlf using lift_chart_int hsurj (hpe ▸ hp1) hint
  set Y : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := h.val.map lf with hYdef
  set Y' : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := (h⁻¹).val.map lf with hY'def
  have hY : (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hY' : (Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      (h⁻¹).val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hYY : (p : Formalism.IndefR.Lev.EAf D) • (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
      Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = (p : Formalism.IndefR.Lev.EAf D) • 1 := by
    refine lift_smul_eq_of_map φ _ hker' _ _ ?_
    rw [Matrix.map_mul, hY, hY', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hmm := lift_conj_mul_smul βS _ _ _ hYY
  have hmm' := hmm
  rw [hp] at hmm'
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin S he.1 _ _ hmm'
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S
  have hsf := supp_fin S (f := e + cA D e) hs
  have hκ' : (p : Formalism.IndefR.Lev.EAf D) • (finE S κ).1 =
      (p : Formalism.IndefR.Lev.EAf D) • (βS.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (βS⁻¹).1) := by
    rw [hp]; exact hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE S κ ∈ St βS :=
    mem_St_of_part_inv D.sp.cm.sig S.gram Λ βS hB.1 (hatL_selfDual hB) p (sigR_int p.2) Y Y' hmm (finE S κ)
      (finE_mem_UA S κ) _ hf hsf hκ'
  refine ⟨κ, hs, (T3 PP e _ hP).2.2.1 κ hs, hSt, ?_, fun P' h1 h2 => ?_, fun x => ?_⟩
  · rw [redFn_of_smul_eq βS PP _ hSt p hres1 Y hκ']
    ext i j
    simp only [Matrix.map_apply]
    exact hres (lf (h.val i j)) (h.val i j) (hlf _).symm
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one βS P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · have hG : (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG S βS κ).val.map φ =
        h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
      rw [← hY]
      refine lift_map_eq_of_smul φ _ hp1 _ _ ?_
      unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
      rw [Units.val_mul, Units.val_mul]
      exact lift_conj_part βS _ _ _ hκ'
    unfold rdAdj
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_actO, lift_frG_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.map_mul, hG]

end GlobalTheory.DownLift.SplitCoef
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CovSat

theorem satA : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ u : ℕ, ∀ N M : ℕ, N + u ≤ M → ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ GlobalTheory.TraceConjugationCover.latL t M → ∃ H' : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = (l : Om l) ^ N • (H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) := by
  intro l _ Γ _ a m ρs t h1 hst
  classical
  let E : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
    Submodule.span ℤ_[l] (Set.range (GlobalTheory.TraceConjugationCover.tup ρs))
  let Λ := GlobalTheory.TraceConjugationCover.latL t 0
  have hsumE : ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ E := by
    intro H
    rw [Finsupp.mem_span_range_iff_exists_finsupp]
    exact ⟨H, by simp only [GlobalTheory.TraceConjugationCover.zOm_smul]⟩
  have hEsum : ∀ x ∈ E, ∃ H' : Γ →₀ ℤ_[l], x = H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro x hx
    obtain ⟨H', hH'⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    exact ⟨H', by rw [← hH']; simp only [GlobalTheory.TraceConjugationCover.zOm_smul]⟩
  have hc : ∀ (n : ℕ) (w : Fin m → Matrix (Fin a) (Fin a) (Om l)), (l : Om l) ^ n • w = (l : ℤ_[l]) ^ n • w := by
    intro n w
    rw [← GlobalTheory.TraceConjugationCover.zOm_smul, map_pow, map_natCast]
  have hsingle : ∀ k, ∀ z ∈ t k, Pi.single k z ∈ Λ := by
    intro k z hz
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨k, z, hz, by simp⟩)
  have hlat : ∀ M, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, ∃ y ∈ Λ, x = ((l : ℤ_[l]) ^ M) • y := by
    intro M x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      obtain ⟨z, hz, rfl⟩ := hk
      refine ⟨Pi.single k z, hsingle k z hz, ?_⟩
      rw [← hc]
      ext i : 1
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', Λ.add_mem hx' hy', by rw [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨c • x', Λ.smul_mem c hx', by rw [smul_comm]⟩
  have hspan : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]),
      (∑ y ∈ t k, zOm l (c y) • y) ∈ Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hρ : ∀ k g, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) ∈
      Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) := by
    intro k g
    obtain ⟨c', hc'⟩ := h1 k
    rw [← mul_one ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)), ← hc', Finset.mul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [Matrix.mul_smul]
    obtain ⟨c'', hc''⟩ := hst k g y hy
    rw [hc'', GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.smul_mem _ _ (hspan k c'')
  have hspanΛ : ∀ k, Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) ≤
      Λ.comap (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) := by
    intro k
    rw [Submodule.span_le]
    intro z hz
    exact hsingle k z hz
  have hEΛ : E ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [← Finset.univ_sum_single (GlobalTheory.TraceConjugationCover.tup ρs g)]
    exact Submodule.sum_mem _ fun k _ => hspanΛ k (hρ k g)
  have hfg : Λ.FG := Submodule.fg_span (Set.finite_iUnion fun k => (t k).finite_toSet.image _)
  haveI : IsNoetherian ℤ_[l] Λ := isNoetherian_of_fg_of_noetherian Λ hfg
  let f : ℕ →o Submodule ℤ_[l] Λ :=
    ⟨fun v => (E.comap Λ.subtype).comap (((l : ℤ_[l]) ^ v) • LinearMap.id), by
      intro v w hvw y hy
      simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
        Submodule.subtype_apply] at hy ⊢
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvw
      rw [pow_add, mul_comm, mul_smul]
      exact E.smul_mem _ hy⟩
  have hf : ∀ v (y : Λ), y ∈ f v ↔ ((l : ℤ_[l]) ^ v) • (y : Fin m → Matrix (Fin a) (Fin a) (Om l)) ∈ E := by
    intro v y
    show y ∈ (E.comap Λ.subtype).comap (((l : ℤ_[l]) ^ v) • LinearMap.id) ↔ _
    simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      Submodule.subtype_apply]
  obtain ⟨u, hu⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance f
  refine ⟨u, fun N M hNM H hx => ?_⟩
  obtain ⟨y, hyΛ, hxy⟩ := hlat M _ hx
  have hyM : (⟨y, hyΛ⟩ : Λ) ∈ f M := by
    rw [hf]
    show ((l : ℤ_[l]) ^ M) • y ∈ E
    rw [← hxy]
    exact hsumE H
  rw [← hu M (by omega), hf] at hyM
  have hz : ((l : ℤ_[l]) ^ (M - N - u)) • (((l : ℤ_[l]) ^ u) • y) ∈ E := E.smul_mem _ hyM
  obtain ⟨H', hH'⟩ := hEsum _ hz
  refine ⟨H', ?_⟩
  rw [hxy, ← hH', hc, smul_smul, smul_smul, ← pow_add, ← pow_add]
  congr 2
  omega

end GlobalTheory.CovSat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ainf_principal_ideal_saturated_closed : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) → ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) → ∃ a : Ainf l, x = inclW l (ι * a) := by
  first | exact @GlobalTheory.AinfSat.mem_ideal_of_saturated | exact GlobalTheory.AinfSat.mem_ideal_of_saturated | (intros; apply GlobalTheory.AinfSat.mem_ideal_of_saturated <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.periodRings_regular_phi_surjective_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  first | exact @GlobalTheory.MemLoc.tied_regular_and_onto | exact GlobalTheory.MemLoc.tied_regular_and_onto | (intros; apply GlobalTheory.MemLoc.tied_regular_and_onto <;> assumption)
end
