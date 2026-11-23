module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcris
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle092
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
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_weil_apply_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ τ ∈ Weil h, τ y = d y := by
  intro E Ω _ _ _ _ _ A w h d hd y
  obtain ⟨K, hK, hy, j, hj⟩ := GlobalTheory.T.decompositionGroup_acts_residues_frobeniusPower E Ω A w h d hd y
  obtain ⟨ρ, hρK, hρ⟩ := GlobalTheory.T.exists_fixing_actsAsFrobeniusPowerResidue E Ω A w h K d hd j hj
  refine ⟨d * ρ, (mem_Weil h).2 ⟨j, 0, hρ⟩, ?_⟩
  rw [AlgEquiv.mul_apply, hρK y hy]

end GlobalTheory.WeilDeligne
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomicTower_trace_almost_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), Kinf K ≤ L → (∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) → (∀ s ∈ S, s ∈ Hinf K) → (∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) → ∀ a : Om l, a ∈ Kinf K → ‖a‖ < 1 → ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a := by
  first | exact @GlobalTheory.Cyc.trace_almost_onto | exact GlobalTheory.Cyc.trace_almost_onto | (intros; apply GlobalTheory.Cyc.trace_almost_onto <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LayerGroup

variable {l : ℕ} [Fact l.Prime]

theorem mem_layer_iff (K : FinExt l) (s : ℕ) (σ : GQ l) :
    σ ∈ Gj K s ↔ (∀ x ∈ K0 K, σ x = x) ∧ ∀ x : Om l, x ^ (l ^ s) = 1 → σ x = x := by

  have key : ∀ x : Om l,
      x ∈ IntermediateField.fixedField (Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l)) ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h f hf => ?_⟩
    have hst : Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l) ≤
        MulAction.stabilizer (Om l ≃ₐ[ℚ_[l]] Om l) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  unfold Gj Ks
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
    IntermediateField.mem_fixingSubgroup_iff, ← Subgroup.zpowers_le,
    ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
  exact and_congr Iff.rfl ⟨fun h x hx => (key x).mp (h hx), fun h x hx => (key x).mpr (h x hx)⟩

private theorem absoluteGalois_apply_eq_self_of_mem_maxUnramified (K : FinExt l) {τ : GQ l} (hτ : τ ∈ GK K) {x : Om l} (hx : x ∈ K0 K) :
    τ x = x := by
  unfold K0 at hx
  exact (IntermediateField.mem_fixingSubgroup_iff K.1 τ).mp hτ x (SetLike.le_def.mp inf_le_left hx)

theorem normal_layer (K : FinExt l) (s : ℕ) : ((Gj K s).subgroupOf (GK K)).Normal := by

  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : GQ l) ∈ GK K := g.2
  have hgi : ((g : GQ l))⁻¹ ∈ GK K := inv_mem hg
  rw [mem_layer_iff] at hn ⊢
  obtain ⟨h0, h1⟩ := hn
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    rw [absoluteGalois_apply_eq_self_of_mem_maxUnramified K hgi hx, h0 x hx, absoluteGalois_apply_eq_self_of_mem_maxUnramified K hg hx]
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    have hy : (((g : GQ l))⁻¹ x) ^ (l ^ s) = 1 := by rw [← map_pow, hx, map_one]
    rw [h1 _ hy]
    exact AlgEquiv.apply_symm_apply (g : GQ l) x

theorem layer_group : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ((Gj K s).subgroupOf (GK K)).Normal ∧ ((Gj K s).subgroupOf (GK K)).FiniteIndex ∧ IsOpen (((Gj K s).subgroupOf (GK K) : Subgroup ↥(GK K)) : Set ↥(GK K)) ∧ padicValNat l ((Gj K s).subgroupOf (GK K)).index = padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) - padicValNat l (Module.finrank ℚ_[l] ↥K.1) := by
  intro l _ K s h
  have : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois ℚ_[l] (AlgebraicClosure ℚ_[l])
  have : FiniteDimensional ℚ_[l] (Ks K s) := GlobalTheory.Cyc.TwistLift.finite_Ks K s
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have hle : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_le h

  have hKs : Module.finrank ℚ_[l] (Ks K s) = (Gj K s).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ (Ks K s)
  have hK : Module.finrank ℚ_[l] K.1 = (GK K).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ K.1
  have hmul : ((Gj K s).subgroupOf (GK K)).index * (GK K).index = (Gj K s).index :=
    Subgroup.relIndex_mul_index hle
  have hKpos : 0 < Module.finrank ℚ_[l] K.1 := Module.finrank_pos
  have hKspos : 0 < Module.finrank ℚ_[l] (Ks K s) := Module.finrank_pos
  have hidx : ((Gj K s).subgroupOf (GK K)).index ≠ 0 := by
    intro h0
    rw [h0, zero_mul, ← hKs] at hmul
    omega
  refine ⟨normal_layer K s, ⟨hidx⟩, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Ks K s)).preimage continuous_subtype_val
  · rw [hKs, ← hmul, ← hK, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hidx hKpos.ne']
    omega

end GlobalTheory.Cyc.LayerGroup
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ), Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  first | exact @GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | exact GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion | (intros; apply GlobalTheory.NLink.admittedStatements_of_localBoundsConclusion <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  first | exact @GlobalTheory.JR.unitMatch_of_weilField | exact GlobalTheory.JR.unitMatch_of_weilField | (intros; apply GlobalTheory.JR.unitMatch_of_weilField <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiSpanKer

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φD_smulA' (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have h := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at h
  exact h

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

variable {m : ℕ} (u : Fin m → LetA O n)

theorem mem_sum_form (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T))
    (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {w : W.DD T} (hw : w ∈ φspan W T S) :
    ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j) := by
  have hadd : ∀ w w' : W.DD T,
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w = ∑ j, u j • W.φD T (z j)) →
      (∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w' = ∑ j, u j • W.φD T (z j)) →
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ w + w' = ∑ j, u j • W.φD T (z j) := by
    rintro w w' ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    refine ⟨z + z', fun j => S.add_mem (hz j) (hz' j), ?_⟩
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  have key : ∀ w ∈ φspan W T S, ∀ a : LetA O n,
      ∃ z : Fin m → W.DD T, (∀ j, z j ∈ S) ∧ a • w = ∑ j, u j • W.φD T (z j) := by
    intro w hw
    unfold φspan at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hdec a
      refine ⟨fun j => c j • y, fun j => S.smul_mem _ hy, ?_⟩
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [φD_smulA', mul_smul]
    | zero => intro a; exact ⟨0, fun j => S.zero_mem, by simp⟩
    | add x y _ _ hx hy => intro a; rw [smul_add]; exact hadd _ _ (hx a) (hy a)
    | smul b x _ hx => intro a; rw [smul_smul]; exact hx (a * b)
  simpa using key w hw 1

theorem phispan_of (hdec : ∀ a : LetA O n, ∃ c : Fin m → LetA O n, a = ∑ j, u j * W.φA (c j))
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hinj : Function.Injective (W.map ι)) (hex : Function.Exact (W.map ι) (W.map π))
    (hπN : ∀ x ∈ W.N T₁, W.map π x ∈ W.N T₂)
    (hind : ∀ z : Fin m → W.DD T₂, (∀ j, z j ∈ W.N T₂) →
      ∑ j, u j • W.φD T₂ (z j) = 0 → ∀ j, z j = 0) :
    ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)),
      ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (LetA O n))) := by
  intro y hy
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply] at hy
  obtain ⟨k, hk⟩ := W.N_φinv T₁ _ hy
  refine ⟨k, ?_⟩
  have hk' : W.Q ^ k • W.map ι y ∈ φspan W T₁ (W.N T₁) := hk
  obtain ⟨w, hw, he⟩ := mem_sum_form W u T₁ (W.N T₁) hdec hk'
  have hπ0 : ∀ j, W.map π (w j) = 0 := by
    refine hind _ (fun j => hπN _ (hw j)) ?_
    have h1 := congrArg (W.map π) he

    rw [map_smulA, (hex _).2 ⟨y, rfl⟩, smul_zero, map_sum] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ]
  choose w' hw' using fun j => (hex (w j)).1 (hπ0 j)
  have hmem : ∀ j, w' j ∈ (W.N T₁).comap ((W.map ι).restrictScalars (LetA O n)) := by
    intro j
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hw']
    exact hw j
  have heq : W.Q ^ k • y = ∑ j, u j • W.φD T₀ (w' j) := by
    apply hinj

    rw [map_smulA, he, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smulA, W.map_φ, hw']
  rw [heq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w' j, hmem j, rfl⟩)

end Generic

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hex : Function.Injective (W.map ι) ∧ Function.Exact (W.map ι) (W.map π) ∧
      Function.Surjective (W.map π) := by
    let E := ((F l).E K s LL h).tie
    haveI := GlobalTheory.EtaleExact.finite_OL LL
    haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
    have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
    refine GlobalTheory.EtaleExact.exact_of_tie E (GlobalTheory.EtaleExact.map_ne_top_of_tie E ?_ ?_) T₀ T₁ T₂ ι π hses
    · rw [hp]
      exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow (D.loc l) LL
    · rw [hp]
      exact GlobalTheory.EtaleExact.sep_RW LL
  exact phispan_of W (fun j : Fin l => (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL))
    (GlobalTheory.T.wachLetterRing_frobenius_decomposition D HW l K s LL h) ι π hex.1 hex.2.1 (fun x hx => W.map_N π c1 c2 x hx)
    (GlobalTheory.T.wachFrobenius_flat_crystalline D HW F l K s LL h T₂ c2)

end GlobalTheory.NL.PhiSpanKer
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_banachModel_tensor_Acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (c : ↥LL.1 →+* N) (b : RA LL →+* N) (κ : N →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : N →+* N) (γ : GQ l → (N →+* N)) (t : N), ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∃ C : ℝ, ∀ x : ↥LL.1, ‖c x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖b y‖ ≤ 1) ∧ (∀ o : ↥(OL LL), b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l)) = c (o : ↥LL.1)) ∧ (∀ x, κ (c x) = x ⊗ₜ[ℚ_[l]] (1 : P.R.B)) ∧ (Continuous φ ∧ ∀ x, φ (c x) = c x) ∧ (∀ g, Continuous (γ g) ∧ ∀ x, γ g (c x) = c x) ∧ (∀ s : ℕ, ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ k‖ ≤ C * r ^ k) ∧ Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c (PowerSeries.coeff k (logS LL)) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ k) Filter.atTop (nhds t) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), IsClosed {x : N | Algebra.TensorProduct.productMap ι P.ιB (κ x) ∈ GlobalTheory.ExpImage.FilB P (m : ℤ)} := by
  first | exact @GlobalTheory.HWL.BanachModel.exists_banach_model | exact GlobalTheory.HWL.BanachModel.exists_banach_model | (intros; apply GlobalTheory.HWL.BanachModel.exists_banach_model <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PolyRoot

theorem key_exp (l : ℕ) [Fact l.Prime] (h : ℕ) (P : ℝ) (hP : 0 < P) (k : ℤ) :
    P ^ ((l:ℝ) ^ k) * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P ^ ((l:ℝ) ^ (k + h)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_add hP, zpow_add₀ hl, zpow_natCast]
  congr 1; ring

theorem rho_pow (l : ℕ) [Fact l.Prime] (h D n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ n) = P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ ((n:ℤ) - D)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
  congr 1; push_cast; ring

theorem poly_root_mod_l : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  intro l _ h μ σ h1 hμ hσ
  obtain ⟨pwadd, pwmul, pwzero, pwcomp, pwnat, pwpow, pwnorm⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨m, hm, ⟨k0, hk0⟩, hsum⟩ := GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination l h μ h1 hμ
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = ‖(l : ℂ_[l])‖ := ⟨_, rfl⟩
  rw [← hPd]
  have hP0 : 0 < P := hPd ▸ norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hP1 : P < 1 := hPd ▸ GlobalTheory.RingBasics.norm_p_lt
  have hσn : ‖sh σ‖ = P := by rw [hσ, hPd]
  obtain ⟨α, hα⟩ : ∃ α : ℤ → ℂ_[l], ∀ k, α k = m k * sh (pw k σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ → ℝ, ∀ k, β k = ‖α k‖ := ⟨_, fun _ => rfl⟩
  have hshσ : ∀ k : ℤ, ‖sh (pw k σ)‖ = P ^ ((l:ℝ) ^ k) := fun k => by rw [pwnorm, hσn]
  have hβ : ∀ k, β k = ‖m k‖ * P ^ ((l:ℝ) ^ k) := fun k => by
    rw [hβd, hα, norm_mul, hshσ]
  have hkey : ∀ k : ℤ, β k * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P * β (k + h) := fun k => by
    rw [hβ, hβ, hm k, norm_mul, ← hPd, ← key_exp l h P hP0 k]; ring
  have hσlt : ‖sh σ‖ < 1 := hσn ▸ hP1
  have hαsum : Summable α := by
    have := (hsum σ hσlt).summable
    rwa [show (fun k : ℤ => m k * sh (pw k σ)) = α from funext fun k => (hα k).symm] at this
  have hβt : Filter.Tendsto β Filter.cofinite (nhds 0) := by
    have := (hαsum.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    rwa [show (fun k => ‖α k‖) = β from funext fun k => (hβd k).symm] at this
  have hβne : ∃ k, β k ≠ 0 := ⟨k0, by
    rw [hβ]; exact mul_ne_zero (norm_ne_zero_iff.2 hk0) (Real.rpow_pos_of_pos hP0 _).ne'⟩
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by rw [hβd]; exact norm_nonneg _
  obtain ⟨D, E, M, hD, hME, hpos, hmax, hstrict, htail⟩ :=
    GlobalTheory.T.window_around_last_max_null_sequence β P h hP0 hβ0 hβne hβt
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ((M + h : ℕ) : ℤ) - D := ⟨_, rfl⟩
  rw [← hN] at hpos hmax hstrict htail
  have htn : ‖α N‖ = β N := (hβd N).symm
  have ht0 : α N ≠ 0 := by intro h0; rw [← norm_eq_zero, htn] at h0; linarith
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlD : (0:ℝ) < (l:ℝ) ^ D := by positivity
  have hnorm_a : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ = β ((k:ℤ) - D) / β N := fun k => by
    rw [norm_div, htn, ← hβd]
  have hprod : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ * (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ k)
      = P * β ((k:ℤ) - D + h) / β N := fun k => by
    rw [hnorm_a, rho_pow l h D k P hP0.le, div_mul_eq_mul_div, hkey]
  refine ⟨α N, D, E, M, fun k : ℕ => α ((k:ℤ) - D) / α N, P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D),
    ht0, hME, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    show ‖α ((k:ℤ) - D) / α N‖ ≤ 1
    rw [hnorm_a, div_le_one hpos]; exact hmax _
  · show ‖α (((M + h : ℕ) : ℤ) - D) / α N‖ = 1
    rw [← hN, div_self ht0, norm_one]
  · have he : ((l:ℝ) ^ h - 1) / (l:ℝ) ^ D ≤ 1 := by
      rw [div_le_one hlD]
      have : (l:ℝ) ^ h ≤ (l:ℝ) ^ D := pow_le_pow_right₀ (by linarith) hD
      linarith
    calc P = P ^ (1:ℝ) := (Real.rpow_one P).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hP0 hP1.le he
  · have hq : (l:ℝ) ≤ (l:ℝ) ^ h := le_self_pow₀ (by linarith) (by omega)
    exact Real.rpow_lt_one hP0.le hP1 (div_pos (by linarith) hlD)
  · rw [rho_pow l h D D P hP0.le, sub_self, zpow_zero, mul_one, ← Real.rpow_natCast P (l ^ h)]
    rw [show P * P ^ ((l:ℝ) ^ h - 1) = P ^ ((1:ℝ) + ((l:ℝ) ^ h - 1)) by
      rw [Real.rpow_add hP0, Real.rpow_one]]
    congr 1; push_cast; ring
  · show ‖α ((M:ℤ) - D) / α N‖ * _ = P
    rw [hprod, show (M:ℤ) - D + h = N by rw [hN]; push_cast; ring, mul_div_assoc,
      div_self hpos.ne', mul_one]
  · intro k hk _
    show ‖α ((k:ℤ) - D) / α N‖ * _ < P
    rw [hprod, div_lt_iff₀ hpos]
    exact mul_lt_mul_of_pos_left (hstrict _ (by omega)) hP0
  · intro u
    have hx : ‖sh (σ * u ^ l ^ D)‖ < 1 := by
      rw [shmul, shpow, norm_mul, norm_pow, hσn]
      calc P * ‖sh u‖ ^ l ^ D ≤ P * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (shle u)) hP0.le
        _ < 1 := by rw [mul_one]; exact hP1
    have hS := hsum _ hx
    have hf : ∀ k : ℤ, m k * sh (pw k (σ * u ^ l ^ D)) = α k * sh (pw (k + D) u) := fun k => by
      rw [hα, pwmul, ← pwnat D u, ← pwcomp, shmul]; ring
    rw [show (fun k : ℤ => m k * sh (pw k (σ * u ^ l ^ D))) = fun k => α k * sh (pw (k + D) u)
      from funext hf] at hS
    have htr := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ (fun k => α k * sh (pw (k + D) u)) _
      ((Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D)) (P * ‖α N‖)
      (mul_nonneg hP0.le (norm_nonneg _)) hS (by
        intro j hj
        have hj' : j < -(D:ℤ) ∨ (E:ℤ) - D < j := by
          by_contra hc
          push_neg at hc
          apply hj
          rw [Finset.mem_image]
          exact ⟨(j + D).toNat, Finset.mem_range.2 (by omega), by omega⟩
        show ‖α j * sh (pw (j + D) u)‖ ≤ P * ‖α N‖
        rw [norm_mul, ← hβd, htn]
        exact (mul_le_of_le_one_right (hβ0 j) (shle _)).trans (htail j hj'))
    have heq : ∑ j ∈ (Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D), α j * sh (pw (j + D) u)
        = α N * ∑ k ∈ Finset.range (E + 1), α ((k:ℤ) - D) / α N * sh u ^ l ^ k := by
      rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_add_cancel, pwnat, shpow]
      field_simp
    rw [heq] at htr
    exact htr

end GlobalTheory.PolyRoot
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tiltUntilt_add_estimate_of_norm_le (l : ℕ) [Fact l.Prime] (x y : Fl l) (hxy : ‖sh x‖ ≤ ‖sh y‖) :
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * ‖sh y‖ ∧ ‖sh (x + y)‖ ≤ ‖sh y‖ := by
  obtain ⟨h1, -, hmul, -, hle1, -, hadd, -⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨u, rfl⟩ := (GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le l).2 x y hxy
  have hsum : y * u + y = y * (u + 1) := by ring
  rw [hsum, hmul, hmul]
  constructor
  · have key : sh y * sh (u + 1) - sh y * sh u - sh y
        = sh y * (sh (u + 1) - sh u - sh (1 : Fl l)) := by rw [h1]; ring
    rw [key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]
    exact mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)
  · rw [norm_mul]
    calc ‖sh y‖ * ‖sh (u + 1)‖ ≤ ‖sh y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hle1 _) (norm_nonneg _)
      _ = ‖sh y‖ := mul_one _

theorem sh_add_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r →
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  intro l _ r x y hx hy
  have hl : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  rcases le_total ‖sh x‖ ‖sh y‖ with h | h
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l x y h
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l y x h
    rw [add_comm x y]
    refine ⟨?_, h2.trans hx⟩
    have e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x := by ring
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hx hl)

end GlobalTheory.PSer
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_series_terms_mem_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ c : ℤ → Acris l, (∀ n : ℤ, (l : Acris l) ^ n.natAbs ∣ c n) ∧ ∀ n : ℤ, (l : Acris l) ^ n.toNat * c n = (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
  first | exact @GlobalTheory.PSer.terms_mem | exact GlobalTheory.PSer.terms_mem | (intros; apply GlobalTheory.PSer.terms_mem <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tiltUntilt_multiplicative_extension_surjective : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F) (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ t : ℂ_[l], ∃ z : F, tsh z = t := by
  first | exact @GlobalTheory.PSer.TshOnto.tsh_surjective | exact GlobalTheory.PSer.TshOnto.tsh_surjective | (intros; apply GlobalTheory.PSer.TshOnto.tsh_surjective <;> assumption)
end
