module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDiscriminantModuleIntegralOverlatticeSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle076
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContentThickenedTupleOrbitNormalSubgroup
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeStabilizerNormalisingSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeTraceInitialSpanVolumeEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentatives
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.SplitResidue

theorem card_eq_ncard_primesOver (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // (g : 𝓞 E) ∈ w.asIdeal} =
      (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)
  · haveI := w.1.isPrime
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using w.2
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro ⟨P, hP, hPl⟩
    refine ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1
      (Ideal.mem_span_singleton_self _)

theorem residue_and_unramified : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely E g →
    ∀ w : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ w.asIdeal →
      Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod g) ∧ (g : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro E _ _ g hg h w hw
  haveI := w.isPrime
  haveI := Fact.mk hg
  have h' := (card_eq_ncard_primesOver E hg).symm.trans h
  obtain ⟨h1, h2⟩ := GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw
  refine ⟨?_, h1⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  refine ⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal))
    ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := h2 x
  refine ⟨(m : ZMod g), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]
  exact hm

end GlobalTheory.SplitResidue
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.card_discriminantModule_integralOverlattice_span : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → Fin n → E) (c : F), c ≠ 0 → (Matrix.of fun a b => hf L Hm (v b) (v a)).det = algebraMap F E c → ∀ Mh Md : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range v) ≤ Mh → (∀ x ∈ Mh, x ∈ Submodule.span E (Set.range v)) → (∀ x ∈ Mh, ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → (∀ x, x ∈ Md ↔ x ∈ Submodule.span E (Set.range v) ∧ ∀ y ∈ Mh, hf L Hm x y ∈ L.O) → 0 ≤ vE L ϖ (algebraMap F E c) ∧ Mh.toAddSubgroup.relIndex Md.toAddSubgroup * ((Submodule.span L.O (Set.range v)).toAddSubgroup.relIndex Mh.toAddSubgroup) ^ 2 = resQ ϖ ^ (2 * (vE L ϖ (algebraMap F E c)).toNat) ∧ (∀ x ∈ Md, algebraMap F E c • x ∈ Submodule.span L.O (Set.range v)) ∧ ∃ b : ι → Fin n → E, Md = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.DiscOver.disc_overlattice | exact GlobalTheory.DiscOver.disc_overlattice | (intros; apply GlobalTheory.DiscOver.disc_overlattice <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.VolPerp

open GlobalTheory.HL.DualInter

theorem relIndex_split {G : Type} [AddCommGroup G] {M A : AddSubgroup G} (Z : AddSubgroup G)
    (h : M ≤ A) : M.relIndex A = (M ⊓ Z).relIndex (A ⊓ Z) * (M ⊔ Z).relIndex (A ⊔ Z) := by
  have h1 : (M ⊔ Z) ⊓ A = M ⊔ (Z ⊓ A) := sup_inf_assoc_of_le Z h
  have h2 : M ≤ (M ⊔ Z) ⊓ A := le_inf le_sup_left h
  rw [← AddSubgroup.relIndex_mul_relIndex M _ A h2 inf_le_right]
  congr 1
  · rw [h1, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right M, inf_comm Z A,
      ← inf_assoc, inf_eq_left.2 h]
  · rw [AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right A (M ⊔ Z),
      ← sup_assoc, sup_eq_left.2 h]

theorem relIndex_split' {G : Type} [AddCommGroup G] (A B Z : AddSubgroup G) :
    B.relIndex A = (B ⊓ Z).relIndex (A ⊓ Z) *
      (((A ⊓ B) ⊔ Z).relIndex ((A ⊔ Z) ⊓ (B ⊔ Z)) * (B ⊔ Z).relIndex (A ⊔ Z)) := by
  rw [← AddSubgroup.inf_relIndex_left, relIndex_split Z inf_le_left]
  congr 1
  · rw [inf_inf_distrib_right, AddSubgroup.inf_relIndex_left]
  · rw [← AddSubgroup.inf_relIndex_left (A ⊔ Z) (B ⊔ Z), AddSubgroup.relIndex_mul_relIndex _ _ _
      (le_inf (sup_le_sup_right inf_le_left _) (sup_le_sup_right inf_le_right _)) inf_le_left]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem expand {m : ℕ} {b c : Fin m → Fin n → E}
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) {v : Fin n → E}
    (hv : v ∈ Submodule.span E (Set.range b)) : v = ∑ j, hf L Hm v (c j) • b j := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  simp [sum_l, smul_l, hbc]

theorem inter_eq {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) :
    Λ ⊓ (Submodule.span E (Set.range b)).restrictScalars L.O
      = Submodule.span L.O (Set.range b) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro v ⟨hv, hvY⟩
    rw [expand hbc hvY]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
      ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    exact ⟨hb j, Submodule.subset_span ⟨j, rfl⟩⟩

theorem map_eq (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0)
    (φ : (Fin n → E) →ₗ[E] (Fin m → E)) (w : Fin m → Fin m → E)
    (hφ : ∀ v, φ v = ∑ j, hf L Hm v (b j) • w j) :
    Λ.toAddSubgroup.map φ.toAddMonoidHom = (Submodule.span L.O (Set.range w)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change φ v ∈ Submodule.span L.O (Set.range w)
    rw [hφ]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range w))
      ⟨_, (hΛ.2 _).2 (hb j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    have : Submodule.span L.O (Set.range w) ≤ Λ.map (φ.restrictScalars L.O) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨c j, hc j, ?_⟩
      have : ∀ i, hf L Hm (c j) (b i) = if i = j then 1 else 0 := fun i => by
        rw [← cj_hf h, hbc]; split_ifs <;> simp
      simp [hφ, this]
    exact this hx

theorem key (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') {m : ℕ} (y : Fin m → Fin n → E) (hy : LinearIndependent E y)
    {Y Z : Submodule L.O (Fin n → E)}
    (hY : Y = (Submodule.span E (Set.range y)).restrictScalars L.O)
    (hZ : Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O) :
    (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧
    (Λ.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup =
    (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have := L.free
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  obtain ⟨b, c, hb, hc, hs, hbc⟩ := exists_dual_family h hΛ m y hy
  obtain ⟨b', c', hb', hc', hs', hbc'⟩ := exists_dual_family h hΛ' m y hy
  have hQ : Λ ⊓ Y = Submodule.span L.O (Set.range b) := by
    rw [hY, ← hs]; exact inter_eq hΛ hb hc hbc
  have hQ' : Λ' ⊓ Y = Submodule.span L.O (Set.range b') := by
    rw [hY, ← hs']; exact inter_eq hΛ' hb' hc' hbc'
  let A : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b' j) (c i)
  let B : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b j) (c' i)
  have hA : ∀ j, b' j = ∑ i, A i j • b i := fun j =>
    expand hbc (by rw [hs, ← hs']; exact Submodule.subset_span ⟨j, rfl⟩)
  have hBA : B * A = 1 := by
    ext k j
    have := hbc' j k
    rw [hA j, sum_l] at this
    simp only [smul_l] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← if_congr eq_comm rfl rfl, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hu : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hBA
  obtain ⟨d, hd⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (hu.mul (hu.map L.cj)).ne_zero (by rw [← hd, map_zero])
  have hli : LinearIndependent E b := by
    refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
    have := congrArg (fun v => hf L Hm v (c k)) hg
    simp only [sum_l, smul_l, hbc] at this
    simpa [hf] using this
  obtain ⟨-, p2, p3⟩ := GlobalTheory.T.relIndex_span_lattice_matrix_det_norm L ϖ hϖ b hli A d hd0 hd.symm (Λ ⊓ Y) (Λ' ⊓ Y) hQ
    (by rw [hQ']; congr 2; exact funext hA)
  have hdet : (cT L A).det = L.cj A.det := by
    have : cT L A = ((L.cj : E →+* E).mapMatrix A).transpose := rfl
    rw [this, Matrix.det_transpose, ← RingHom.map_det]; rfl
  obtain ⟨-, -, r3⟩ := GlobalTheory.T.relIndex_span_lattice_matrix_det_norm L ϖ hϖ (Pi.basisFun E (Fin m))
    (Pi.basisFun E (Fin m)).linearIndependent (cT L A) d hd0
    (by rw [hdet, L.cj_cj, mul_comm, hd]) _ _ rfl rfl
  let φ : (Fin n → E) →ₗ[E] (Fin m → E) := LinearMap.pi fun j => hfL L Hm (b' j)
  have hφ : ∀ v k, φ v k = hf L Hm v (b' k) := fun v k => rfl
  have m1 := map_eq h hΛ' hb' hc' hbc' φ (Pi.basisFun E (Fin m))
    (fun v => by ext k; simp [hφ, Pi.single_apply])
  have m2 := map_eq h hΛ hb hc hbc φ (fun j => ∑ i, cT L A i j • Pi.basisFun E (Fin m) i)
    (fun v => by
      ext k
      rw [hφ, hA k]
      simp [sum_r, smul_r, cT, Pi.single_apply, mul_comm])
  rw [← m1, ← m2, AddSubgroup.relIndex_map_map, AddSubgroup.relIndex_map_map] at r3
  have hker : φ.toAddMonoidHom.ker = Z.toAddSubgroup := by
    ext x
    rw [hZ, ← hs']
    constructor
    · intro hx v hv
      rw [← cj_hf h, hf_eq_zero_of_span (S := Set.range b') ?_ v hv, map_zero]
      rintro _ ⟨j, rfl⟩
      have : hf L Hm x (b' j) = 0 := congrFun hx j
      rw [← cj_hf h, this, map_zero]
    · intro hx
      funext j
      exact hx _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hker] at r3
  refine ⟨p2, ?_⟩
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [p3, r3]
  ring

theorem relIndex_symm (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') : Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ≠ 0 ∧
    Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  have hY : (⊤ : Submodule L.O (Fin n → E))
      = (Submodule.span E (Set.range (Pi.basisFun E (Fin n)))).restrictScalars L.O := by
    rw [Module.Basis.span_eq]; rfl
  have hZ : (⊥ : Submodule L.O (Fin n → E))
      = (perp L Hm (Submodule.span E (Set.range (Pi.basisFun E (Fin n))))).restrictScalars L.O := by
    rw [Module.Basis.span_eq, eq_comm, eq_bot_iff]
    intro x hx
    refine eq_zero_of_hf h fun v => ?_
    rw [← cj_hf h, hx v trivial, map_zero]
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' _ (Pi.basisFun E (Fin n)).linearIndependent hY hZ
  simp only [inf_top_eq, Submodule.bot_toAddSubgroup, sup_bot_eq] at k1 k2
  exact ⟨k1, Nat.mul_self_inj.1 k2⟩

theorem vol_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ Λ' hΛ hΛ' m y hy Y Z hY hZ
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' y hy hY hZ
  obtain ⟨a1, a2⟩ := relIndex_symm h hΛ hΛ'
  have s1 := relIndex_split' Λ.toAddSubgroup Λ'.toAddSubgroup Z.toAddSubgroup
  have s2 := relIndex_split' Λ'.toAddSubgroup Λ.toAddSubgroup Z.toAddSubgroup
  rw [inf_comm Λ'.toAddSubgroup Λ.toAddSubgroup, inf_comm (Λ'.toAddSubgroup ⊔ _)] at s2
  have e1 : (Λ ⊓ Z).toAddSubgroup = Λ.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  have e2 : (Λ' ⊓ Z).toAddSubgroup = Λ'.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  rw [e1, e2]
  have b1 := a2 ▸ a1
  rw [s1] at b1
  rw [s1, s2] at a2
  rw [s2] at a1
  simp only [ne_eq, mul_eq_zero, not_or] at a1 b1
  refine ⟨a1.1, k1, ?_⟩
  rw [mul_left_comm, mul_left_comm _ (AddSubgroup.relIndex (_ ⊓ _ ⊔ _) _)] at a2
  have a3 := mul_left_cancel₀ a1.2.1 a2
  refine mul_right_cancel₀ b1.2.2 ?_
  rw [mul_assoc, mul_comm (AddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup _), ← k2, ← mul_assoc, a3]
  ring

end GlobalTheory.HL.VolPerp
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by
  first | exact @GlobalTheory.HL.cont_thick_torb_normal | exact GlobalTheory.HL.cont_thick_torb_normal | (intros; apply GlobalTheory.HL.cont_thick_torb_normal <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  first | exact @GlobalTheory.Mass.DiscOrder.main | exact GlobalTheory.Mass.DiscOrder.main | (intros; apply GlobalTheory.Mass.DiscOrder.main <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem sublattice_count : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ M hM i hi
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.IsTorsionFree (𝓞 K) M := inferInstance
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
    have h1 : Module.rank (𝓞 K) M ≤ Module.rank K V := by
      rw [IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
      exact Submodule.rank_le M
    exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K V)
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (Module.finrank K V) i hi hr
  have hinj : Set.InjOn (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i} := by
    intro N hN N' hN' e
    have := congrArg (Submodule.map M.subtype) e
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hN.1, inf_eq_right.mpr hN'.1] using this
  have hmaps : Set.MapsTo (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}
      {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i} := by
    intro N hN
    exact hN.2
  have h2 := Set.encard_le_encard_of_injOn hmaps hinj
  rw [← hfin.cast_ncard_eq] at h2
  calc _ ≤ (((({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast h2
    _ = ENNReal.ofReal ({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℝ) := by
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

end GlobalTheory.Mass
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.St.G.stepLevel_tLat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : _root_.Formalism.L2.Forms.StepLevel F E σ J T f bad),
    _root_.GlobalTheory.St.G.TLat σ J T f S.Lb := by
  intro F E _ _ _ _ _ n σ J T f bad S
  refine ⟨⟨S.Lb_fin, S.Lb_span⟩, S.Lb_int, S.Lb_dual, S.Lb_index, fun v hv => ?_⟩
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (S.fT_ne v hv)
  exact ⟨x, x.2, fun hmem => hx (S.fT_L v hv x hmem)⟩

end GlobalTheory.St.G
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by
  first | exact @GlobalTheory.HL.FrameStabLat.main | exact GlobalTheory.HL.FrameStabLat.main | (intros; apply GlobalTheory.HL.FrameStabLat.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianTerm_splits_unimodular_complement : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ b : Fin (k - 1) → S.V, (∀ i, b i ∈ S.W0) ∧ Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) ∧ (∀ i j, hf L S.Hm (b i) (b j) ∈ L.O) ∧ ∃ P : Matrix (Fin (k - 1)) (Fin (k - 1)) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (b i) (b j)) * P = 1 := by
  first | exact @GlobalTheory.HL.UnimodSplit.main | exact GlobalTheory.HL.UnimodSplit.main | (intros; apply GlobalTheory.HL.UnimodSplit.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.frameLattice_trace_initialSpan_volume_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ d' Λ', S.IsTerm d' Λ' → ∀ (J : ℕ) (Yy : Submodule L.O S.V), J ≤ r + 1 → Yy = (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O → (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup = (S.M d' Λ' ⊓ Yy).toAddSubgroup.relIndex (S.M d Λ ⊓ Yy).toAddSubgroup ∧ (S.M d Λ ⊓ Yy).toAddSubgroup.relIndex (S.M d' Λ' ⊓ Yy).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.HL.TraceVol.trace_volume | exact GlobalTheory.HL.TraceVol.trace_volume | (intros; apply GlobalTheory.HL.TraceVol.trace_volume <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) ∧ S.om d (h • Λ) = S.om d Λ ∧ S.M d (h • Λ) = h • S.M d Λ ∧ S.sat (h • Λ) = h • S.sat Λ ∧ S.Fr d (h • Λ) = h • S.Fr d Λ ∧ S.be d (h • Λ) = S.be d Λ ∧ S.cardI d (h • Λ) = S.cardI d Λ ∧ (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) ∧ (S.TypeBe d (h • Λ) ↔ S.TypeBe d Λ) ∧ (∀ β J βJ, S.InFF β J βJ d (h • Λ) ↔ S.InFF β J βJ d Λ) ∧ ∀ J x x' u s, S.IsMove J d Λ x x' u s ↔ S.IsMove J d (h • Λ) (h x) (h x') (h u) s := by
  first | exact @GlobalTheory.FrameAct.stabiliser_acts_on_terms | exact GlobalTheory.FrameAct.stabiliser_acts_on_terms | (intros; apply GlobalTheory.FrameAct.stabiliser_acts_on_terms <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.pairing_second_type_test_on_representatives : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  first | exact @GlobalTheory.HL.TypeRep.main | exact GlobalTheory.HL.TypeRep.main | (intros; apply GlobalTheory.HL.TypeRep.main <;> assumption)
end
