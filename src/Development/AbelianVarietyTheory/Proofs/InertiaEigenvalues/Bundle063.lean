module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.Topology.Sets.Compacts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.RingTheory.Artinian.Ring

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.HaarExist

variable (r : ℕ)

theorem entryBall_compact_open (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ∧
      IsOpen {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have e : {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} =
      Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : K) 1 := by
    ext A
    exact ⟨fun h i _ j _ => mem_closedBall_zero_iff.2 (h i j),
      fun h i j => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))⟩
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero⟩

theorem norm_one_entry_le (K : Type) [NormedField K] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) K) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem glO_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact (glO r K) ∧ IsOpen (glO r K) ∧ (glO r K).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r K
  have e : glO r K = Units.embedProduct _ ⁻¹' ({A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1})) := by
    ext g
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  refine ⟨?_, ?_, 1, fun i j => ⟨norm_one_entry_le r K i j, by rw [inv_one]; exact norm_one_entry_le r K i j⟩⟩
  · rw [e]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hc.prod (MulOpposite.opHomeomorph.symm.isClosedEmbedding.isCompact_preimage hc))
  · rw [e]
    exact (ho.prod (ho.preimage MulOpposite.continuous_unop)).preimage Units.continuous_embedProduct

theorem continuousStar_of_norm_star (E : Type) [NormedField E] [StarRing E] (h : ∀ y : E, ‖star y‖ = ‖y‖) :
    ContinuousStar E :=
  ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) h).continuous⟩

theorem uO_isCompact_isOpen (E : Type) [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [ContinuousStar E] :
    IsCompact (uO r E) ∧ IsOpen (uO r E) ∧ (uO r E).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r E
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  exact ⟨hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, ho.preimage continuous_subtype_val,
    1, fun i j => norm_one_entry_le r E i j⟩

def positiveCompactsOf {X : Type} [TopologicalSpace X] (s : Set X) (h : IsCompact s ∧ IsOpen s ∧ s.Nonempty) :
    TopologicalSpace.PositiveCompacts X :=
  ⟨⟨s, h.1⟩, by simpa [h.2.1.interior_eq] using h.2.2⟩

theorem unitBall_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] :
    IsCompact (Metric.closedBall (0 : K) 1) ∧ IsOpen (Metric.closedBall (0 : K) 1) ∧
      (Metric.closedBall (0 : K) 1).Nonempty := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact ⟨isCompact_closedBall _ _, IsUltrametricDist.isOpen_closedBall _ one_ne_zero, 0, by simp⟩

theorem meas_nonempty : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  intro F E _ _ _ _ h r
  haveI := h.ultraF; haveI := h.ultraE; haveI := h.lcF; haveI := h.lcE
  haveI := continuousStar_of_norm_star E h.norm_star
  letI : MeasurableSpace (GL (Fin r) F) := borel _
  haveI : BorelSpace (GL (Fin r) F) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin r) E) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin r) E) := ⟨rfl⟩
  letI : MeasurableSpace F := borel _
  haveI : BorelSpace F := ⟨rfl⟩
  letI : MeasurableSpace E := borel _
  haveI : BorelSpace E := ⟨rfl⟩
  exact ⟨{ μG := Measure.haarMeasure (positiveCompactsOf _ (glO_isCompact_isOpen r F))
           μU := Measure.haarMeasure (positiveCompactsOf _ (uO_isCompact_isOpen r E))
           μF := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen F))
           μE := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen E))
           haarG := inferInstance, haarU := inferInstance, haarF := inferInstance, haarE := inferInstance
           volG := Measure.haarMeasure_self, volU := Measure.haarMeasure_self
           volF := Measure.addHaarMeasure_self, volE := Measure.addHaarMeasure_self }⟩

end GlobalTheory.JR.HaarExist
end
end

section

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.HilbertNinety

theorem exists_unit_sigma (K : UQ) (B : InvAlg K) (u : B.A) (hu : u * B.σ u = 1) :
    ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  classical
  letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)
  let b : B.A →+ B.A :=
    { toFun := fun a => a + B.σ a * B.σ u
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add (f := _)]; ring }
  have hb : ∀ a, b a = a + B.σ a * B.σ u := fun a => rfl
  have hbσ : ∀ a, B.σ (b a) = b a * u := by
    intro a
    rw [hb, map_add (f := _), map_mul, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ a)) * hu
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  set e : K.E := algebraMap K.O K.E x with he
  have hce : K.c e - e ≠ 0 := by
    intro h
    rw [sub_eq_zero, he, hxy] at h
    have := IsFractionRing.injective K.O K.E h
    exact hne (by rw [this, sub_self]; exact Ideal.zero_mem _)
  have key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z =
      algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z) := by
    intro z
    rw [hb, hb, map_mul, B.σ_alg, map_sub]
    ring
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
  let S : MaximalSpectrum B.A → Submodule ℚ B.A := fun m =>
    { carrier := {a | b a ∈ m.asIdeal}
      add_mem' := fun {a c} ha hc => by
        change b (a + c) ∈ m.asIdeal
        rw [map_add (f := _)]; exact m.asIdeal.add_mem ha hc
      zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem
      smul_mem' := fun q a ha => by
        change b (q • a) ∈ m.asIdeal
        rw [map_rat_smul]
        change (algebraMap ℚ K.E q) • b a ∈ m.asIdeal
        rw [Algebra.smul_def]
        exact m.asIdeal.mul_mem_left _ ha }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    have hall : ∀ a, b a ∈ m.asIdeal := fun a => by
      have : a ∈ S m := hm ▸ Submodule.mem_top
      exact this
    have h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal := by
      have := key 1
      rw [mul_one] at this
      rw [this]
      exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hce, map_one]
    rw [← h2]
    exact m.asIdeal.mul_mem_left _ h1
  have h3 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 h3
  have hunit : IsUnit (b a) := by
    by_contra hn
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
    apply ha
    exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm
  exact ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩

end GlobalTheory.UnitLemma.HilbertNinety
end
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory

theorem UnitLemma.exists_unit_residue (K : UQ) (B : InvAlg K) (hB : IsReduced B.A) (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal) (hz : z ≠ 0) :
    ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  classical
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  let e := IsArtinianRing.equivPi B.A
  let v : (I : MaximalSpectrum B.A) → B.A ⧸ I.asIdeal := fun I =>
    if h : I = m then h ▸ z else 1
  have hv : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro I
    letI := Ideal.Quotient.field I.asIdeal
    rw [isUnit_iff_ne_zero]
    by_cases h : I = m
    · subst h; simpa [v] using hz
    · simp [v, h]
  have hy : IsUnit (e.symm v) := hv.map e.symm
  refine ⟨hy.unit, ?_, ?_⟩
  · have := IsArtinianRing.equivPi_apply B.A (e.symm v) m
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v]
  · intro m' hm'
    have := IsArtinianRing.equivPi_apply B.A (e.symm v) m'
    rw [AlgEquiv.apply_symm_apply] at this
    simp only [IsUnit.unit_spec]
    rw [← this]; simp [v, hm']

theorem UnitLemma.unit_prescribed_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 :=
  fun K B hB m z hz => UnitLemma.exists_unit_residue K B hB m z hz

end GlobalTheory
end

section

noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.NormUnits

theorem group_fg_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, CommGroup (G i)]
    (hG : ∀ i, Group.FG (G i)) : Group.FG (∀ i, G i) := by
  classical
  have := Fintype.ofFinite ι
  choose S hS using fun i => Group.fg_iff.mp (hG i)
  refine Group.fg_iff.mpr ⟨⋃ i, Pi.mulSingle i '' S i, ?_,
    Set.finite_iUnion fun i => (hS i).2.image _⟩
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_prod_mulSingle x]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hx : x i ∈ Subgroup.closure (S i) := by rw [(hS i).1]; trivial
  have h1 : Pi.mulSingle i (x i) ∈ (Subgroup.closure (S i)).map (MonoidHom.mulSingle G i) :=
    ⟨x i, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  exact Subgroup.closure_mono (fun y hy => Set.mem_iUnion.2 ⟨i, hy⟩) h1

theorem isIntegral_of_forall_quot {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [IsArtinianRing A] [IsReduced A] (x : A)
    (hx : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal x)) :
    IsIntegral O x := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum A)
  choose p hpm hp using hx
  refine ⟨∏ I, p I, monic_prod_of_monic _ _ fun I _ => hpm I, ?_⟩
  rw [← aeval_def]
  apply (IsArtinianRing.equivPi A).injective
  funext J
  rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply, map_prod, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ J) ?_
  have h2 := aeval_algHom_apply (Ideal.Quotient.mkₐ O J.asIdeal) x (p J)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h2
  rw [← h2, aeval_def]
  exact hp J

theorem units_quot_intUnits_fg : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L]
    [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) →
    ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A]
    [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  intro K hL A _ _ _ _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K.E A
  have := Fintype.ofFinite (MaximalSpectrum A)

  have hfg : ∀ I : MaximalSpectrum A,
      Group.FG ((A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K.E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K.E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact hL (A ⧸ I.asIdeal)
  have hP := group_fg_pi (fun I : MaximalSpectrum A =>
    (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal)) hfg
  let ψ : Aˣ →* ∀ I : MaximalSpectrum A, (A ⧸ I.asIdeal)ˣ ⧸ intUnits K.O (A ⧸ I.asIdeal) :=
    MonoidHom.pi fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hsurj : Function.Surjective ψ := by
    intro c
    choose u hu using fun I => QuotientGroup.mk'_surjective _ (c I)
    let e := IsArtinianRing.equivPi A
    refine ⟨Units.map (e.symm : (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) →* A)
      (MulEquiv.piUnits.symm u), ?_⟩
    funext I
    rw [← hu I]
    change QuotientGroup.mk' _ _ = _
    congr 1
    ext
    have h3 : ∀ z : ∀ I : MaximalSpectrum A, A ⧸ I.asIdeal,
        Ideal.Quotient.mk I.asIdeal (e.symm z) = z I := fun z => by
      rw [← IsArtinianRing.equivPi_apply A (e.symm z) I]
      exact congrFun (e.apply_symm_apply z) I
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [h3]
    rfl
  have hker : ψ.ker ≤ intUnits K.O A := by
    intro t ht
    have hI : ∀ I : MaximalSpectrum A,
        Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom t ∈ intUnits K.O (A ⧸ I.asIdeal) :=
      fun I => (QuotientGroup.eq_one_iff _).mp (congrFun (MonoidHom.mem_ker.mp ht) I)
    refine ⟨NormUnits.isIntegral_of_forall_quot _ fun I => (hI I).1,
      NormUnits.isIntegral_of_forall_quot _ fun I => ?_⟩
    have := (hI I).2
    rwa [Units.coe_map_inv] at this
  haveI : Group.FG (Aˣ ⧸ ψ.ker) :=
    Group.fg_of_surjective (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map ψ.ker (intUnits K.O A) (MonoidHom.id _) fun t ht => hker ht) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  exact ⟨QuotientGroup.mk y, rfl⟩

end GlobalTheory.UnitLemma.NormUnits
end
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isIntegral_iff_forall_maximalSpectrum (K : UQ) (B : InvAlg K) (hred : IsReduced B.A) (x : B.A) :
    IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  constructor
  · intro h m
    have := h.map (Ideal.Quotient.mkₐ K.O m.asIdeal)
    simpa [Ideal.Quotient.mkₐ_eq_mk] using this
  · intro h
    letI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
    choose p hpm hp using fun m : MaximalSpectrum B.A => h m
    refine ⟨∏ m, p m, monic_prod_of_monic _ _ (fun m _ => hpm m), ?_⟩
    have hmem : ∀ m : MaximalSpectrum B.A, eval₂ (algebraMap K.O B.A) x (∏ m, p m) ∈ m.asIdeal := by
      intro m
      rw [Polynomial.eval₂_finsetProd]
      classical
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
      apply Ideal.mul_mem_right
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have h1 := hp m
      have h2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K.O m.asIdeal) x (p m)
      rw [Ideal.Quotient.mkₐ_eq_mk, aeval_def, h1] at h2
      rw [← aeval_def]
      exact h2.symm
    set z := eval₂ (algebraMap K.O B.A) x (∏ m, p m)
    have hj : z ∈ Ideal.jacobson (⊥ : Ideal B.A) := by
      rw [Ideal.jacobson, Submodule.mem_sInf]
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B.A)
    have hz : z ^ k = 0 := by
      have := Ideal.pow_mem_pow hj k
      rw [hk] at this
      simpa using this
    exact IsReduced.eq_zero z ⟨k, hz⟩

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullLat

theorem fg_of_le {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {L X : Submodule R M} (hL : L.FG) (hX : X ≤ L) : X.FG := by
  haveI : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : (X.comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hX] at h2

theorem exists_hull : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x,
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧
      (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧
      (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
        (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by
  intro K B x c hc L hL hcL
  obtain ⟨⟨hfg, hspan⟩, -, hdual⟩ := hL
  set Λ := Subalgebra.toSubmodule (integralClosure K.O B.A) with hΛ
  set J : Submodule K.O B.A := Λ * L with hJ
  set γ := algebraMap K.O B.A c with hγ

  have hγu : IsUnit γ := by
    have h0 : algebraMap K.O K.E c ≠ 0 := by
      intro h; exact hc (IsFractionRing.injective K.O K.E (by simpa using h))
    rw [hγ, IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (isUnit_iff_ne_zero.mpr h0).map (algebraMap K.E B.A)
  have hLJ : L ≤ J := fun y hy => by
    simpa using Submodule.mul_mem_mul (M := Λ) (N := L)
      (show (1 : B.A) ∈ Λ from (integralClosure K.O B.A).one_mem) hy
  have hcJ : ∀ y ∈ J, γ * y ∈ L := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu l hl
      rw [← mul_assoc]
      exact hcL u ((mem_integralClosure_iff _ _).mp hu) l hl
    · intro a b ha hb
      rw [mul_add]; exact add_mem ha hb
  have hmulJ : mulLat K.O γ J ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcJ y hy

  have hJfg : J.FG := by
    obtain ⟨u, hu⟩ := hγu
    have hM : (L.map (LinearMap.mulLeft K.O ((u⁻¹ : B.Aˣ) : B.A))).FG := hfg.map _
    refine fg_of_le hM ?_
    intro y hy
    refine ⟨γ * y, hcJ y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨J, ⟨hJfg, ?_⟩, ?_, ?_, ?_, hmulJ, hLJ⟩
  · rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono hLJ
  · intro a ha y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu l hl
      rw [← mul_assoc]
      have hu' : u ∈ integralClosure K.O B.A := hu
      exact Submodule.mul_mem_mul (show a * u ∈ Λ from (integralClosure K.O B.A).mul_mem ha hu') hl
    · intro p q hp hq
      rw [mul_add]; exact add_mem hp hq
  · intro y hy
    exact hLJ ((hdual y).mpr fun z hz => hy z (hLJ hz))
  · intro y hy z hz
    exact (hdual (γ * y)).mp (hcJ y hy) (γ * z) (hcJ z hz)

end GlobalTheory.HullLat
end
