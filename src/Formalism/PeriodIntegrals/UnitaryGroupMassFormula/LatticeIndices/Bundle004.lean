module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocBEOfNatCast
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle001
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
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LeviEmbeddingBlock32
public import ReciprocityTheory.GaloisValuations.Bundle002

@[expose] public section

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

def HaarIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (K A : Subgroup G), A ≤ K → IsOpen (A : Set G) →
    A.relIndex K ≠ 0 → μ (K : Set G) = (A.relIndex K : ℝ≥0∞) * μ (A : Set G)

def RedIdx : Prop :=
  ∀ (K Q : Type) [Group K] [Group Q] [Finite Q] (ρ : K →* Q), Function.Surjective ρ →
    ∀ A : Subgroup K, ρ.ker ≤ A → A.index * Nat.card (A.map ρ) = Nat.card Q

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

abbrev HAp (p : TypX X) : Type := HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J

def KvX (p : TypX X) : Set (HAp X p) :=
  Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1

def KgX (p : TypX X) : Set (HAp X p) :=
  Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1

def KppX (p : TypX X) : Set (HAp X p) :=
  compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1

def KnatX (u : D.what₂.Word) (p : TypX X) : Set (HAp X p) :=
  Knatv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) (gOf p) p.1

abbrev muP (p : TypX X) : Measure (HAp X p) := X.measG.μGv p.1

def StTop (p : TypX X) : Prop := ContinuousMul (HAp X p) ∧ BorelSpace (HAp X p)

def StK (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧ IsOpen (K : Set (HAp X p)) ∧
    IsCompact (K : Set (HAp X p)) ∧ IsOpen (KgX X p)

def StRed (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ρ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ ∧
      ∀ x : K, ρ x = 1 ↔ (x : HAp X p) ∈ KgX X p

def StImA (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∀ ρ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ →
      (∀ x : K, ρ x = 1 ↔ (x : HAp X p) ∈ KgX X p) →
      ∃ A : Subgroup K, Subtype.val '' (A : Set K) = KppX X hb p ∧ ρ.ker ≤ A ∧
        Nat.card (A.map ρ) = nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p)

def StImB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∀ ρ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ →
      (∀ x : K, ρ x = 1 ↔ (x : HAp X p) ∈ KgX X p) →
      ∃ B : Subgroup K, Subtype.val '' (B : Set K) = KnatX X u p ∧ ρ.ker ≤ B ∧
        Nat.card (B.map ρ) = glkC D.R.k (gOf p) * nnC D.R.rS D.R.k (gOf p)

def StMeasA (p : TypX X) : Prop :=
  ∃ i : ℕ, (i : ℝ) * ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) = (ggC D.R.rS D.R.k (gOf p) : ℝ) ∧
    ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) ≠ 0 ∧
    muP X p (KvX X p) = (i : ℝ≥0∞) * muP X p (KppX X hb p)

def StMeasB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ j : ℕ, (j : ℝ) * ((glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ)) = (ggC D.R.rS D.R.k (gOf p) : ℝ) ∧
    ((glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ)) ≠ 0 ∧
    muP X p (KvX X p) = (j : ℝ≥0∞) * muP X p (KnatX X u p) ∧
    muP X p (KnatX X u p) ≠ 0 ∧ muP X p (KnatX X u p) ≠ ⊤

end Loc

def MeasAAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X, StMeasA X hb p

def MeasBAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X, StMeasB X u p

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def scP (p : TypX X) (c : Fv X.B.I.F p.1) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  eOf X.B.I (singleV X.B.I.F p.1 c)

theorem imA_psiV_eOf (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a : Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.psiV X.B.I v (eOf X.B.I a) = algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (a v) := by
  simp [PI.FinKW.psiV, eOf]
  rfl

theorem component_scalarAt_same (p : TypX X) (c : Fv X.B.I.F p.1) :
    PI.FinKW.psiV X.B.I p.1 (scP X p c) = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) c := by
  rw [scP, imA_psiV_eOf, Comp_single_same]

theorem component_scalarAt_of_ne (p : TypX X) (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : v ≠ p.1)
    (c : Fv X.B.I.F p.1) : PI.FinKW.psiV X.B.I v (scP X p c) = 0 := by
  rw [scP, imA_psiV_eOf, Comp_single_ne X.B.I p.1 v h, map_zero]

theorem scalarAt_mem_integralAdeles (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) :
    scP X p (c : Fv X.B.I.F p.1) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  apply LocB_eOf_mem
  intro v
  by_cases h : v = p.1
  · subst h; show singleV X.B.I.F _ _ _ ∈ _; rw [Comp_single_same]; exact c.2
  · show singleV X.B.I.F p.1 _ v ∈ _; rw [Comp_single_ne X.B.I p.1 v h]; exact zero_mem _

theorem imA_smul_alg (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F)
    (u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    c • u = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) (c : Fv X.B.I.F p.1) • u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  rfl

theorem imA_vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_smul' (v : HeightOneSpectrum (𝓞 X.B.I.F)) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (t • w) = PI.FinKW.psiV X.B.I v t • PI.FinKW.vecV X.B.I v w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vec_ext (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ∀ v, PI.FinKW.vecV X.B.I v w = 0) : w = 0 := by
  funext i
  exact PI.FinKW.local_vector_injective X.B.I (w i) fun v => congrFun (h v) i

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

section K

variable {K : Type} [Field K] [NumberField K]

theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hfin := Formalism.L2.SG.TypedSets.finite_over K l hl.out.ne_zero
  set T := hfin.toFinset with hTdef
  have hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := fun v => by
    rw [hTdef, Set.Finite.mem_toFinset]; rfl
  have hsum := ReciprocityTheory.Gal.sum_locDegree l T hT
  have hcard : T.card = Module.finrank ℚ K := by rw [← h, Set.ncard_eq_toFinset_card _ hfin]
  have hpos : ∀ v ∈ T, (fun _ => 1) v ≤ ReciprocityTheory.Gal.locDegree v := fun v _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) v.asIdeal) (Ideal.inertiaDeg_pos v.asIdeal ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by
    simp only [Finset.sum_const, smul_eq_mul, mul_one]; rw [hsum, hcard])
  have hm : w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ = 1 := (hall w ((hT w).2 hw)).symm
  exact ⟨Nat.eq_one_of_mul_eq_one_right hm, Nat.eq_one_of_mul_eq_one_left hm⟩

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) p.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQm.isPrime, hQ0⟩
  have hw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have := (Ideal.mem_of_liesOver Q p.asIdeal ((l : ℕ) : 𝓞 F)).1 hp
    simpa using this
  obtain ⟨he, hf⟩ := locDeg_one l h w hw
  have hQp : Q.IsPrime := hQm.isPrime
  have h1 : p.asIdeal.ramificationIdx ℤ ≤ Q.ramificationIdx ℤ :=
    Ideal.ramificationIdx_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h2 : p.asIdeal.inertiaDeg ℤ ≤ Q.inertiaDeg ℤ :=
    Ideal.inertiaDeg_below_le (R := ℤ) (q := p.asIdeal) (r := Q)
  have h3 := Ideal.ramificationIdx_pos (R := ℤ) p.asIdeal
  have h4 := Ideal.inertiaDeg_pos p.asIdeal ℤ
  change Q.ramificationIdx ℤ = 1 at he
  change Q.inertiaDeg ℤ = 1 at hf
  omega

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hlo : p.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := (ReciprocityTheory.Gal.liesOver_span_iff l p.asIdeal).2 hp
  constructor
  · have := Ideal.pow_inertiaDeg l p.asIdeal
    rw [hf, pow_one] at this
    rw [this, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro h2
    have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {((l : ℕ) : 𝓞 F)} := by
      rw [Ideal.map_span, Set.image_singleton]; simp
    have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 F)) ≠ ⊥ := by
      rw [hmap, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have hm := IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(l : ℤ)}) p.asIdeal hne
    rw [he, hmap] at hm
    have hdvd : p.asIdeal ^ 2 ∣ Ideal.span {((l : ℕ) : 𝓞 F)} := Ideal.dvd_span_singleton.2 h2
    have hfin : FiniteMultiplicity p.asIdeal (Ideal.span {((l : ℕ) : 𝓞 F)}) := by
      apply FiniteMultiplicity.of_not_isUnit
      · rw [Ideal.isUnit_iff]; exact p.isPrime.ne_top
      · rw [Ne, Ideal.zero_eq_bot, ← hmap]; exact hne
    have := hfin.le_multiplicity_of_pow_dvd hdvd
    omega

end Arith

end MassDataIdxRes
end
end
