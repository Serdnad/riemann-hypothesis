module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle177
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle168
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle012
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle321
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem conjP_ne {R : Ranks} (H : Formalism.BasicNotions.Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : conjPrime₂ P ≠ P := by
  intro e
  obtain ⟨x, hx, hy⟩ := h
  have hc : IsConjPl H P P := (isConjPl_iff H P P).2 e.symm
  have e1 : ((cO H.E x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := bridge_star_holds R H x
  exact hy _ e1 ((hc x _ e1).1 hx)

variable {B : Base} {X : PreX B.toPre} {I : ColIn B X}

theorem under_sel (h : I.Ok) (v : HeightOneSpectrum (𝓞 B.host.F)) : (I.sel v).under (𝓞 B.host.F) = v :=
  HeightOneSpectrum.ext (h.sel_ok v)

theorem good_of_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ I.SQ) :
    I.sel (P.under (𝓞 B.host.F)) = P ∧ GoodPl B.host.E I.S (P.under (𝓞 B.host.F)) := by
  obtain ⟨a, ha⟩ := I.mem_SQ.1 hP
  obtain ⟨v, -, rfl, hg⟩ := I.exists_of_mem_Q ha
  rw [under_sel h]
  exact ⟨rfl, hg⟩

theorem plc_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ (B.primes X).vGs) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 B.host.F)) ∈ I.S := by
  classical
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ P.asIdeal := by
    unfold Primes.vGs Primes.vG at hP
    simpa only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two] using hP
  obtain ⟨i, hi⟩ := hm
  have h1 : ((B.primes X).g i : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
  rw [(ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.g_prime i)).2 h1]
  exact h.g_mem i

theorem levOk_twists : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → LevOk B.host (B.primes X).vGs I.SQ ∧ Disjoint (B.primes X).vGs I.SQ ∧ ∀ a, KDq B.host (I.Q a) ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker ∧ (I.xi a).IsUnitary := by
  classical
  intro B X I h
  have hb := levOk_base B X
  have hu : ∀ P : HeightOneSpectrum (𝓞 B.host.E), (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun P =>
    (under_eq_iff B.host P _).2 (Or.inr rfl)
  refine ⟨⟨hb.cover, fun P hP hP' => ?_⟩, Finset.disjoint_left.2 fun P h1 h2 => (good_of_mem h h2).2.2.2 (plc_mem h h1),
    fun a => ?_⟩
  · simp only [Finset.mem_union] at hP hP'
    rcases hP with hP | hP <;> rcases hP' with hP' | hP'
    · exact hb.split P (by simpa using hP) (by simpa using hP')
    · refine (good_of_mem h hP').2.2.2 ?_
      rw [hu]
      exact plc_mem h hP
    · refine (good_of_mem h hP).2.2.2 ?_
      rw [← hu]
      exact plc_mem h hP'
    · have e := (good_of_mem h hP').1
      rw [hu, (good_of_mem h hP).1] at e
      exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 (good_of_mem h hP).2).1 e.symm
  · obtain ⟨⟨⟨n, hn, ho⟩, hT, hta, -⟩, hq, -⟩ :=
      ReadTwist.isTwist_of_reads B.R B.host B.LL B.embLL I.S (I.tup a) (I.xi a) (h.xi_reads a)
    refine ⟨KDq_le_ker_of_tame _ hT hta fun w hw => by_contra fun hr => hw (Or.inr ?_), fun x => ?_⟩
    · have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
        ((UnrAe.finite_ramified (I.xi a)).image (·.under (𝓞 B.host.F))).subset fun v hv => by
          obtain ⟨P, e, hP⟩ := (hq v).1 hv
          exact ⟨P, hP, e⟩
      have hmem : I.sel (w.under (𝓞 B.host.F)) ∈ I.Q a := by
        unfold ColIn.Q QE
        rw [dite_eq_left hfin]
        convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 ((hq _).2 ⟨w, rfl, hr⟩))
      rcases (under_eq_iff B.host _ w).1 (under_sel h _).symm with e | e
      · exact Or.inl (e ▸ hmem)
      · exact Or.inr ⟨_, hmem, (isConjPl_iff B.host _ _).2 e⟩
    · have h1 : (I.xi a).1 x ^ n = 1 := congrArg (fun χ : _root_.Formalism.L2.Host.HChar B.host.E => χ.1 x) ho
      have h2 : ‖(((I.xi a).1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

end GlobalTheory.Mem.LevTwist
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.CyclotomicNorms Polynomial Module

namespace GlobalTheory.WeilDeligne.LabDual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem charpoly_dualMap (f : End ℂ V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f.dualMap (finBasis ℂ V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

theorem exists_proj (a : WDRep h V) : ∃ e : End ℂ V, (∀ v, e v ∈ a.tameSpace) ∧
    (∀ v ∈ a.tameSpace, e v = v) ∧
    (∀ σ : Weil h, (σ : G E Ω) ∈ Wild E A → e * a.ρ σ = e) ∧
    ∀ f ∈ a.dual.tameSpace, ∀ v, f (e v) = f v := by
  classical
  let K : Subgroup (Weil h) := (Wild E A).subgroupOf (Weil h)
  let P : Subgroup (End ℂ V)ˣ := K.map a.ρ.toHomUnits
  have hfin : Finite P := by
    refine Set.Finite.of_finite_image (f := Units.val) (a.smooth.finite_range.subset ?_)
      Units.val_injective.injOn
    rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨⟨σ, Wild_le_Ine hσ⟩, rfl⟩
  have := Fintype.ofFinite P
  have hc : (Fintype.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card P : ℂ)⁻¹ • ∑ p : P, (p.1 : End ℂ V), fun v => ?_, fun v hv => ?_,
    fun σ hσ => ?_, fun f hf v => ?_⟩
  · refine a.mem_tameSpace.mpr fun σ hσ => ?_
    rw [← End.mul_apply, mul_smul_comm, Finset.mul_sum]
    congr 2
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, (p.1 : End ℂ V) v = v := by
      rintro ⟨_, σ, hσ, rfl⟩
      exact a.mem_tameSpace.mp hv σ hσ
    simp [this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc]
  · rw [smul_mul_assoc, Finset.sum_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (⟨_, σ, hσ, rfl⟩ : P)) _ _ fun p => rfl
  · have : ∀ p : P, f ((p.1 : End ℂ V) v) = f v := by
      rintro ⟨_, σ, hσ, rfl⟩
      have := LinearMap.congr_fun (a.dual.mem_tameSpace.mp hf σ⁻¹ (K.inv_mem hσ)) v
      simpa using this
    simp [this, hc]

theorem charpoly_dual_tamePart (a : WDRep h V) (σ : Weil h) :
    (a.dual.tamePart.ρ σ).charpoly = (a.tamePart.ρ σ⁻¹).charpoly := by
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_proj a
  let r : a.dual.tameSpace →ₗ[ℂ] Dual ℂ a.tameSpace :=
    a.tameSpace.dualRestrict ∘ₗ a.dual.tameSpace.subtype
  have hr : Function.Bijective r := by
    refine ⟨(injective_iff_map_eq_zero r).mpr fun f hf => ?_, fun φ => ?_⟩
    · ext v
      rw [← h4 f.1 f.2 v]
      exact LinearMap.congr_fun hf ⟨e v, h1 v⟩
    · refine ⟨⟨φ ∘ₗ e.codRestrict _ h1, a.dual.mem_tameSpace.mpr fun u hu => ?_⟩, ?_⟩
      · ext v
        exact congrArg φ (Subtype.ext
          (LinearMap.congr_fun (h3 u⁻¹ ((Wild E A).inv_mem hu)) v))
      · ext v
        exact congrArg φ (Subtype.ext (h2 v v.2))
  rw [← charpoly_dualMap (a.tamePart.ρ σ⁻¹),
    ← LinearEquiv.charpoly_conj (LinearEquiv.ofBijective r hr)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := (LinearEquiv.ofBijective r hr).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem tameEig_lpDual (x : WD h) {γ : G E Ω} (hγ : γ ∈ Ine (F := E) A) :
    WD.tameEig (WD.lpDual x) γ = (WD.tameEig x γ).map (·⁻¹) := by
  obtain ⟨k, hk, -, hk1⟩ := WD.exists_pow_tameEig x hγ
  induction x using WD.ind with
  | hP m a =>
    have hγ' := Ine_le_Weil h hγ
    obtain ⟨n, h0, -, hn⟩ := a.tame_tamePart.exists_pow_eq_one (γ := ⟨γ, hγ'⟩) hγ
    have hp : n * k - 1 + 1 = n * k := Nat.sub_add_cancel (Nat.mul_pos h0 hk)
    have h1 : a.tamePart.ρ (⟨γ, hγ'⟩ : Weil h)⁻¹ = a.tamePart.ρ ⟨γ, hγ'⟩ ^ (n * k - 1) := by
      rw [← one_mul (a.tamePart.ρ _), ← one_pow k, ← hn, ← pow_mul, ← hp, pow_succ, mul_assoc,
        ← map_mul, mul_inv_cancel, map_one, mul_one, hp]
    have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ _ (n * k - 1)
      (LinearMap.toMatrix (finBasis ℂ _) (finBasis ℂ _) (a.tamePart.ρ ⟨γ, hγ'⟩))
    rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
    rw [WD.tameEig_mk _ hγ'] at hk1
    rw [WD.lpDual_mk, WD.tameEig_mk _ hγ', WD.tameEig_mk _ hγ', charpoly_dual_tamePart, h1, h2]
    refine Multiset.map_congr rfl fun z hz => eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, hp, pow_mul', hk1 z hz, one_pow]

theorem rootsBar_lab_lpDual : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (τ : Fbar g →* ℂ) (γ : G E Ω), ∀ x : WD h,
    rootsBar (WD.lab τ γ (WD.lpDual x)) = (rootsBar (WD.lab τ γ x)).map (·⁻¹) := by
  intro E Ω _ _ _ _ _ A w h g _ τ γ x
  by_cases H : TeichmullerInertiaLabelCondition A w τ γ
  · refine Multiset.map_injective H.2.2.injective ?_
    rw [WD.map_rootsBar_lab H, tameEig_lpDual x H.2.1, ← WD.map_rootsBar_lab H, Multiset.map_map,
      Multiset.map_map]
    refine Multiset.map_congr rfl fun y _ => ?_
    show (τ y)⁻¹ = τ y⁻¹
    rcases eq_or_ne y 0 with rfl | hy
    · rw [inv_zero, H.2.2.map_zero, inv_zero]
    · exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hy, map_one])
  · simp [WD.lab_of_not H, rootsBar]

end GlobalTheory.WeilDeligne.LabDual
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RamQ

theorem not_unr_iff_under_mem (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
  obtain ⟨htw, hq, -⟩ := GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a)
    (hI.xi_reads a)
  rw [hq]
  refine ⟨fun h => ⟨PP, rfl, h⟩, ?_⟩
  rintro ⟨P, hP, hn⟩ hu
  apply hn
  intro x hx
  have h1 := GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1
    (fun y hy => by rw [pow_one]; exact hu y hy) x hx
  simpa using h1

theorem tupleTwist_ramified_iff_chosenPrime_or_conj_host (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP := by
  classical
  rw [not_unr_iff_under_mem X px I hI a PP]
  have hf := Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)
    (I.tup a).2.1.1.1.1.2
  have hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v := fun v => HeightOneSpectrum.ext (hI.sel_ok v)
  have memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a := fun v hv => by
    unfold ColIn.Q
    rw [Formalism.L2.Col.QE, dite_eq_left hf]
    exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)
  have under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) :=
    fun P hP => by
      obtain ⟨v, hv, hs, -⟩ := ColIn.exists_of_mem_Q I hP
      rw [← hs, hsel]
      exact hv
  constructor
  · intro hv
    have key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) →
        Q = P ∨ Q = Formalism.DivisionValues.conjPl P := fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F) := (hsel _).symm
    rcases key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h
    · left
      rw [h]
      exact memQ _ hv
    · right
      exact ⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  · rintro (h | ⟨PP', h, hc⟩)
    · exact under_of_mem _ h
    · have e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F) := GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      rw [← e]
      exact under_of_mem _ h

theorem ram_iff : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (a : I.ι) (PP : Pl X.toD7.host.E),
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP :=
  fun X px I hI a PP => tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP

end GlobalTheory.Mem.Col2.RamQ

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.TwistPlaces

theorem natPrime_not_mem {A : Type} [CommRing A] (P : Ideal A) [hP : P.IsPrime] {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hne : l ≠ p) (hpP : (p : A) ∈ P) : (l : A) ∉ P :=
  _root_.GlobalTheory.NatCastNotMemPrime.natCast_notMem_of_prime_ne P hp hl hne hpP

theorem twistPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ a : I.ι,
    (∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP) → Formalism.IndefR.Lev.IsTwistPlaces (D := X.toD7) X.toD7.host.g (I.Q a) ∧
    ∀ PP ∈ I.Q a, ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal ∧
      ∀ u : X.toD7.what₂.Word, (((X.toD7.mem u).A.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal := by
  intro X px I hI a hU
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host _ X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := fun PP (hPP : PP ∈ I.Q a) => htw.2.2.2 PP (hU PP hPP)
  have hstar : ∀ x : X.B.host.E, star x = X.B.host.conj x := bridge_star_holds X.B.R X.B.host

  have off : ∀ PP ∈ I.Q a, ∀ l : ℕ, l.Prime → l ∈ I.S → ((l : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := by
    intro PP hPP l hl hS
    obtain ⟨-, hp, -, hpS⟩ := key PP hPP
    exact natPrime_not_mem PP.asIdeal hp hl (fun e => hpS (e ▸ hS)) (Ideal.absNorm_mem PP.asIdeal)
  refine ⟨fun PP hPP => ⟨?_, fun PP' hPP' hc => ?_⟩, fun PP hPP => ⟨?_, fun u => ?_⟩⟩
  · obtain ⟨-, hp, hsq, hpS⟩ := key PP hPP
    refine ⟨Ideal.absNorm PP.asIdeal, hp, ?_, hsq, fun i e => hpS (e ▸ hI.g_mem i)⟩
    show Nat.card (𝓞 X.B.host.E ⧸ PP.asIdeal) = Ideal.absNorm PP.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · obtain ⟨v, -, rfl, -⟩ := I.exists_of_mem_Q hPP
    obtain ⟨v', -, rfl, -⟩ := I.exists_of_mem_Q hPP'
    have hle : v.asIdeal ≤ v'.asIdeal := by
      intro c hc'
      have h1 : algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c ∈ (I.sel v).asIdeal := by
        have := hI.sel_ok v
        rw [← this] at hc'
        exact hc'
      obtain ⟨c', h2, h3⟩ := hc _ h1
      have h4 : c' = algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c := by
        apply RingOfIntegers.ext
        rw [h3]
        show star (algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)) = algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)
        rw [hstar, ← X.B.conjF_eq, AlgHom.commutes]
      rw [h4] at h2
      rw [← hI.sel_ok v']
      exact h2
    have hv : v = v' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)
    subst hv
    obtain ⟨⟨x, hx, hy⟩, -⟩ := key _ hPP
    obtain ⟨c', h2, h3⟩ := hc x hx
    exact hy c' (h3.trans (hstar _)) h2
  · have hp2 : ((X.B.host.QS : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := fun h => by
      rw [← Nat.prod_primeFactorsList X.B.host.QS_pos.ne', Nat.cast_list_prod] at h
      have := PP.isPrime
      obtain ⟨a, ha, h'⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem PP.isPrime
        ((X.B.host.QS.primeFactorsList.map Nat.cast : List (𝓞 X.B.host.E)) : Multiset _)).1 (by simpa using h)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ha)
      exact off PP hPP l (Nat.prime_of_mem_primeFactorsList hl)
        (hI.mem_of_dvd_QS (Nat.prime_of_mem_primeFactorsList hl) (Nat.dvd_of_mem_primeFactorsList hl)) h'
    have hq : ((X.B.host.q : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.1 hI.two_q_d_mem.2.1
    have hd : ((X.B.host.d : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.2.1 hI.two_q_d_mem.2.2
    have hT : ((X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal :=
      off PP hPP _ (X.B.T_prime X.B.u₀) (hI.T_mem X.B.u₀)
    have hsp : X.toD7.sp.T = X.B.T X.B.u₀ := X.B.sp_T
    rw [hsp]
    show ((X.B.host.QS * X.B.host.q * X.B.host.d * X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal
    have hPr := PP.isPrime
    push_cast
    intro h
    rcases hPr.mem_or_mem h with h | h
    · rcases hPr.mem_or_mem h with h | h
      · rcases hPr.mem_or_mem h with h | h
        · exact hp2 (by exact_mod_cast h)
        · exact hq h
      · exact hd h
    · exact hT h
  · have hA : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [hA]
    exact off PP hPP _ (X.B.T_prime u) (hI.T_mem u)

end GlobalTheory.Mem.TwistPlaces
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.UnitN

theorem exists_unit_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ]
    {K : Set G} (hK : IsCompact K) (hcov : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) :
    ∃ (ν : Measure G) (𝓝 : Set G), ν.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓝 ν ∧ ν 𝓝 = 1 := by
  let μ : Measure G := Measure.haar
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain Γ μ
  have hle : μ 𝓕 ≤ μ K := by
    rw [h.measure_eq_tsum K]
    refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hK.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h.measure_ne_zero (NeZero.ne μ)
  refine ⟨(μ 𝓕)⁻¹ • μ, 𝓕, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 hpos),
    h.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

theorem exists_isUnitN : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ ν 𝓝, GlobalTheory.Per.IsUnitN B e ν 𝓝 := by
  intro D B ρ e he
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcl : IsClosed (NFlag B e : Set (GA D B)) := by
    have : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
      DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have : LocallyCompactSpace (NFlag B e) := hcl.locallyCompactSpace
  have : SecondCountableTopology (NFlag B e) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))
  have : Countable (NFlagQ B e) := hinj.countable
  have : DiscreteTopology (NFlagQ B e) :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  exact exists_unit_of_cocompact (NFlagQ B e) hK h

end GlobalTheory.Per.UnitN
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schurLemma_equivariant_pair_boundedFunctions_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  first | exact @GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions | exact GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions | (intros; apply GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions <;> assumption)
end
