module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle001
public import Development.EtaleCohomology.CohomologicalPurity.Bundle004
public import Development.EtaleCohomology.CohomologicalPurity.Bundle002
public import Development.EtaleCohomology.CohomologicalPurity.Bundle006
public import Development.EtaleCohomology.CohomologicalPurity.Bundle003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

namespace LateralTheory.Fin.LeafHens
theorem henselization_compatible_maps_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafComp := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafComp_of
theorem henselization_inverse_limit_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafInv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafInv_of
theorem standard_etale_simple_root_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootStd := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootStd_of
theorem henselian_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRootHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRootHens_of
theorem henselization_simple_root_lift_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafRoot := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafRoot_of <;> first | exact standard_etale_simple_root_of_henselization | exact henselian_simple_root_lift_of_henselization
theorem henselization_supremum_neighborhood_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafSup := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafSup_of
theorem henselization_coequalizer_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafCoeq := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafCoeq_of <;> first | exact henselization_inverse_limit_of_henselization | exact henselization_compatible_maps_of_henselization
theorem henselization_diagonal_section_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafDiag := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafDiag_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization
theorem henselization_etale_neighborhood_stage_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafStage := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafStage_of
theorem henselization_colimit_henselian_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColHens := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColHens_of <;> first | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization
theorem henselization_colimit_universal_of_henselization : LateralTheory.CohomologicalPurity.Hz.LeafColUniv := by
  apply LateralTheory.CohomologicalPurity.Hz.LeafColUniv_of
theorem etale_purity_henselian_local_of_henselization : LateralTheory.CohomologicalPurity.LeafHens := by
  apply LateralTheory.CohomologicalPurity.Hz.goal_of <;> first | exact henselization_compatible_maps_of_henselization | exact henselization_inverse_limit_of_henselization | exact henselization_simple_root_lift_of_henselization | exact henselization_supremum_neighborhood_of_henselization | exact henselization_coequalizer_of_henselization | exact henselization_diagonal_section_of_henselization | exact henselization_etale_neighborhood_stage_of_henselization | exact henselization_colimit_henselian_of_henselization | exact henselization_colimit_universal_of_henselization
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafHens := etale_purity_henselian_local_of_henselization
end LateralTheory.Fin.LeafHens
end

section

namespace LateralTheory.Fin.LeafSemi
theorem etale_purity_semilocal_of_reduction : LateralTheory.CohomologicalPurity.LeafSemi := by
  apply LateralTheory.CohomologicalPurity.LeafSemi_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafSemi := etale_purity_semilocal_of_reduction
end LateralTheory.Fin.LeafSemi
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem LeafLoc_of : LeafLoc := by
  intro d P x W hxW
  have := P.cl; have := P.smX; have := P.smZ
  obtain ⟨T, hT, hxT, -⟩ := exists_isAffineOpen_mem_and_subset (x := P.p.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ P.p ⁻¹ᵁ T) ⟨hxW, hxT⟩
  have e : V ≤ P.p ⁻¹ᵁ T := fun y hy => (hVW hy).2
  refine ⟨⟨V, hV⟩, hxV, fun y hy => (hVW hy).1, Γ(P.S, T), inferInstance, (P.p.appLE T V e).hom, ?_, ?_⟩
  · exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension (P.e + d)) P.p P.smX ⟨T, hT⟩ ⟨V, hV⟩ e
  · have hV' : IsAffineOpen (P.ι ⁻¹ᵁ V) := hV.preimage P.ι
    have e2 : P.ι ⁻¹ᵁ V ≤ (P.ι ≫ P.p) ⁻¹ᵁ T := fun y hy => e hy
    have h2 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension P.e) (P.ι ≫ P.p) P.smZ
      ⟨T, hT⟩ ⟨P.ι ⁻¹ᵁ V, hV'⟩ e2
    have hc : (P.ι ≫ P.p).appLE T (P.ι ⁻¹ᵁ V) e2 = P.p.appLE T V e ≫ P.ι.app V := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [hc] at h2
    have hs : Function.Surjective (P.ι.app V).hom := P.ι.app_surjective V hV
    have hk : P.ι.ker.ideal ⟨V, hV⟩ = RingHom.ker (P.ι.app V).hom := P.ι.ker_apply ⟨V, hV⟩
    rw [hk]
    let eqv := RingHom.quotientKerEquivOfSurjective hs
    have heq : (Ideal.Quotient.mk (RingHom.ker (P.ι.app V).hom)).comp (P.p.appLE T V e).hom =
        eqv.symm.toRingHom.comp ((P.p.appLE T V e ≫ P.ι.app V).hom) := by
      ext a
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      apply eqv.injective
      simp [eqv]
    rw [heq]
    exact (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ _ h2

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurPf

def actH (q : ℕ) {P : Arrow Spc} (n : ℤ) {m i j : ℤ} (b : Hs q P m j) :
    Ht q P.right n i →+ Hs q P (n + m) (i + j) where
  toFun a := Hs.act q a b
  map_zero' := by
    apply Subtype.ext
    simp [Hs.act, Hs.proj]
  map_add' x y := by
    apply Subtype.ext
    simp only [Hs.act, Hs.proj, map_add (f := _), AddMonoidHom.add_apply, AddSubgroup.coe_add]
    abel

theorem bij_comp {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C] {f : B →+ C} {g : A →+ B}
    (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (f.comp g) := by
  rw [AddMonoidHom.coe_comp]; exact hf.comp hg

def purT {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) (P : SP d) (n i : ℤ) :
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d) := by
  classical
  exact if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
    haveI : NeZero q := ⟨h.1⟩
    ((AddEquiv.ofBijective _ (((T P).ok q h.2).2.2.1 (n + 2 * d) (i + d))).symm.toAddMonoidHom.comp
      (actH q (P := abv P.U (T P).π) n (i := i) (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)))).comp
      ((AddEquiv.ofBijective _ (((T P).ok q h.2).1 i n)).symm.toAddMonoidHom.comp
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n))
  else 0

theorem purT_bij {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) : Function.Bijective (purT T q P n i) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dite_eq_left h]
  refine bij_comp (bij_comp (AddEquiv.bijective _) ?_) (bij_comp (AddEquiv.bijective _) (((T P).ok q hq).2.1 i n))
  exact ((T P).ok q hq).2.2.2 n i

def TubeRef {d : ℕ} (T : ∀ P : SP d, Tube P) : Prop := ∀ (P' P : SP d) (φ : P'.Hom P),
  ∃ (T' : Tube P') (a : T'.E ⟶ (T P').E) (b : T'.E ⟶ (T P).E), a ≫ (T P').π = T'.π ∧ b ≫ (T P).π = T'.π ≫ sch.map φ.f

end PurPf

open PurPf

def EtalePurityNaturality : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P), TubeRef T →
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purT T q P n i a) = purT T q P' n i (pull _ (sch.map φ.g) _ _ a)

def EtalePurityProjection : Prop := Hyp → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (purT T q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)

def EtalePurityReduction : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (purT T r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (purT T q P n i a).1

theorem EtalePurity_of_parts (hCl : LeafCl) (hTube : LeafTube) (hN : EtalePurityNaturality) (hP : EtalePurityProjection) (hR : EtalePurityReduction) :
    LeafPur := by
  intro hH d
  obtain ⟨T, hT⟩ := hTube hH d
  exact ⟨purT T, fun q _ P hq =>
    ⟨purT_bij T q P hq, hN hH hCl d T hT q P hq, hP hH d T q P hq, hR hH hCl d T q P hq⟩⟩

end LateralTheory.CohomologicalPurity
end
end

section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafRankPf

theorem finrank_tensor_surj {A B K X : Type*} [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [Algebra B K] [IsScalarTower A B K] [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (h : Function.Surjective (algebraMap A B)) :
    Module.finrank K (K ⊗[A] X) = Module.finrank K (K ⊗[B] X) := by
  have : CompatibleSMul A B K X := CompatibleSMul.of_algebraMap_surjective K X h
  exact (LinearEquiv.finrank_eq (equivOfCompatibleSMul A B K K X)).symm

theorem finrank_tensor_cotangent {A K : Type*} [CommRing A] [Field K] [Algebra A K] (J : Ideal A)
    (hJ : ∀ a ∈ J, algebraMap A K a = 0) :
    Module.finrank K (K ⊗[A] J) = Module.finrank K (K ⊗[A] J.Cotangent) := by
  have hex := lTensor_exact K (LinearMap.exact_subtype_mkQ (J • (⊤ : Submodule A J)))
    (Submodule.mkQ_surjective _)
  have hz : ∀ (x : K) (z : J), z ∈ J • (⊤ : Submodule A J) → (x ⊗ₜ[A] z : K ⊗[A] J) = 0 := by
    intro x z hz
    refine Submodule.smul_induction_on (p := fun z => (x ⊗ₜ[A] z : K ⊗[A] J) = 0) hz ?_ ?_
    · intro a ha m _
      rw [← smul_tmul, Algebra.smul_def, hJ a ha, zero_mul, zero_tmul]
    · intro u v hu hv
      rw [tmul_add, hu, hv, add_zero]
  have h0 : LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype = 0 := by
    ext x z; exact hz x z z.2
  have hinj : Function.Injective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have : y ∈ LinearMap.range (LinearMap.lTensor K (J • (⊤ : Submodule A J)).subtype) :=
      (hex y).mp (by rw [LinearMap.baseChange_eq_ltensor] at hy; exact hy)
    rw [h0, LinearMap.range_zero] at this
    simpa using this
  have hsurj : Function.Surjective (LinearMap.baseChange K (Ideal.toCotangent J)) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective K (Submodule.mkQ_surjective _)
  exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

theorem _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  intro e d R A _ _ _ I p _ hIp hA hB
  have hk : ∀ a ∈ I, algebraMap A p.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hIp ha)
  letI : Algebra (A ⧸ I) p.ResidueField := (Ideal.Quotient.lift I (algebraMap A p.ResidueField) hk).toAlgebra
  haveI : IsScalarTower A (A ⧸ I) p.ResidueField := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have hsurj : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (Ideal.IsPrime.ne_top ‹_›) hIp)
  haveI : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  haveI : Algebra.IsStandardSmooth R A := hA.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := hB.isStandardSmooth
  have rA : Module.finrank A Ω[A⁄R] = e + d := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (e + d))
  have rB : Module.finrank (A ⧸ I) Ω[(A ⧸ I)⁄R] = e := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential e)
  have eqv := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) p.ResidueField p.ResidueField Ω[A⁄R]
  have h1 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) = e + d := by
    rw [finrank_tensor_surj hsurj, LinearEquiv.finrank_eq eqv, Module.finrank_baseChange, rA]
  have h2 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[(A ⧸ I)⁄R]) = e := by
    rw [finrank_tensor_surj hsurj, Module.finrank_baseChange, rB]
  have hK : RingHom.ker (algebraMap A (A ⧸ I)) = I := Ideal.mk_ker
  have h3 : Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] (RingHom.ker (algebraMap A (A ⧸ I))).Cotangent) := by
    rw [← finrank_tensor_cotangent _ (by rw [hK]; exact hk), hK]
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) (P := A) (A := A ⧸ I) hsurj).mp inferInstance
  have e0 : Function.Exact (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I))
      ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I) hsurj
  have s0 : Function.Surjective ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A) :=
    KaehlerDifferential.mapBaseChange_surjective R A (A ⧸ I) hsurj
  set f := (KaehlerDifferential.kerCotangentToTensor R A (A ⧸ I)).baseChange p.ResidueField
  set g := ((KaehlerDifferential.mapBaseChange R A (A ⧸ I)).restrictScalars A).baseChange p.ResidueField
  have hex : Function.Exact f g := by
    simpa only [f, g, LinearMap.baseChange_eq_ltensor] using lTensor_exact p.ResidueField e0 s0
  have hg : Function.Surjective g := by
    simpa only [g, LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective p.ResidueField s0
  have hf : Function.Injective f := by
    have hc : (l.baseChange p.ResidueField).comp f = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := l.baseChange p.ResidueField) (fun x => by
      simpa using LinearMap.congr_fun hc x)
  have : CompatibleSMul A (A ⧸ I) p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R]) :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  haveI : Module.Finite p.ResidueField (p.ResidueField ⊗[A] ((A ⧸ I) ⊗[A] Ω[A⁄R])) :=
    Module.Finite.equiv ((LinearEquiv.restrictScalars p.ResidueField
      (equivOfCompatibleSMul A (A ⧸ I) p.ResidueField p.ResidueField ((A ⧸ I) ⊗[A] Ω[A⁄R])).symm).trans
      eqv).symm
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hf,
    h1, h2] at hrk
  rw [h3]; omega

end LateralTheory.CohomologicalPurity.LeafRankPf
end
end

section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem pick_span_top (A M K : Type) [CommRing A] [AddCommGroup M] [Module A M] [Field K] [Algebra A K] :
    Submodule.span K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[A] m = k • ((1 : K) ⊗ₜ[A] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add a c ha hc => exact add_mem (ha trivial) (hc trivial)

theorem LeafPick_of : LeafPick := by
  intro d A M _ _ _ _ p _ hd
  set K := p.ResidueField
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m)
  rw [pick_span_top] at hbspan
  let B : Module.Basis b K (K ⊗[A] M) := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = d := by rw [← hd, Module.finrank_eq_card_basis B]
  let B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  have hmem : ∀ i, ∃ m : M, (1 : K) ⊗ₜ[A] m = B' i := by
    intro i
    have : B' i ∈ b := by simp [B', B]
    obtain ⟨m, hm⟩ := hbs this
    exact ⟨m, hm⟩
  choose x hx using hmem
  set N := Submodule.span A (Set.range x)
  let g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N) := (N.mkQ).baseChange K
  have hgsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N)
  have hg0 : ∀ v, g v = 0 := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range B') := by rw [B'.span_eq]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i, rfl⟩
      rw [← hx i]
      simp [g, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩)]
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro r a _ ha; simp [ha]
  have hsub : Subsingleton (K ⊗[A] (M ⧸ N)) := by
    constructor; intro u w
    obtain ⟨u', rfl⟩ := hgsurj u
    obtain ⟨w', rfl⟩ := hgsurj w
    rw [hg0, hg0]
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro h
    exact (not_nontrivial_iff_subsingleton.2 hsub) h
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.1 hnot
  refine ⟨x, f, hfp, fun m => ?_⟩
  rw [SetLike.mem_coe, Module.mem_annihilator] at hf
  have := hf (Submodule.Quotient.mk m)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

lemma kd_span {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] (f : A) [IsLocalization.Away f A'] (N : Submodule A' Ω[A'⁄R])
    (hN : ∀ a : A, KaehlerDifferential.D R A' (algebraMap A A' a) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a', rfl⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) a'
  simp only at hs
  have hu : IsUnit (algebraMap A A' (s : A)) := IsLocalization.map_units A' s
  have h1 : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' ∈ N := by
    have h := congrArg (KaehlerDifferential.D R A') hs
    rw [Derivation.leibniz] at h
    have e : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' =
        KaehlerDifferential.D R A' (algebraMap A A' a) - a' • KaehlerDifferential.D R A' (algebraMap A A' s) := by
      rw [← h]; abel
    rw [e]; exact N.sub_mem (hN a) (N.smul_mem _ (hN s))
  obtain ⟨u, hu'⟩ := hu
  have h2 := N.smul_mem (↑u⁻¹ : A') h1
  rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

theorem LeafCoord_of (hR : LeafRank) (hP : LeafPick) (hS : LeafSpan) (hE : LeafEt) : LeafCoord := by
  intro e d R A _ _ φ I p hp hIp hstd
  letI : Algebra R A := φ.toAlgebra
  haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A := hstd.1
  haveI h2 : Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) := hstd.2
  haveI : Algebra.IsStandardSmooth R A := h1.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := h2.isStandardSmooth
  have hfg : I.FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
    simpa [Ideal.Quotient.mkₐ_ker] using this
  haveI : Module.Finite A I := Module.Finite.iff_fg.mpr hfg
  haveI := hp
  have hrank := hR e d R A I p hIp h1 h2
  obtain ⟨x, f, hf, hx⟩ := hP d A I p hrank
  set x' : Fin d → A := fun j => (x j : A) with hx'
  have hxI : ∀ j, x' j ∈ I := fun j => (x j).2
  have hfx : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x') := by
    intro a ha
    have h := Submodule.mem_map_of_mem (f := I.subtype) (hx ⟨a, ha⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  obtain ⟨y, g, hg, hy⟩ := hS e d R A I p hp hIp h2 x' f hxI hf hfx
  refine ⟨f * g, fun h => (hp.mem_or_mem h).elim hf hg, ?_⟩
  intro A' _ _ _
  letI : Algebra R A' := ((algebraMap A A').comp φ).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfgu : IsUnit (algebraMap A A' (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgu
  have hfu : IsUnit (algebraMap A A' f) := isUnit_of_mul_isUnit_left hfgu
  have hgu : IsUnit (algebraMap A A' g) := isUnit_of_mul_isUnit_right hfgu
  refine ⟨fun j => algebraMap A A' (x' j), fun k => algebraMap A A' (y k), ?_, ?_⟩
  · haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away (f * g)
    have h3 : Algebra.IsStandardSmoothOfRelativeDimension (0 + (e + d)) R A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := A') (n := e + d) (m := 0)
    rw [zero_add] at h3
    refine hE (e + d) R A' (Fin d ⊕ Fin e) _ (by simp [add_comm]) h3 ?_
    apply kd_span (R := R) (A := A) (f * g)
    intro a
    have hm := Submodule.mem_map_of_mem (f := KaehlerDifferential.map R R A A')
      (hy (KaehlerDifferential.D R A a))
    rw [Submodule.map_span, LinearMap.map_smul, KaehlerDifferential.map_D] at hm
    have hle : Submodule.span A (KaehlerDifferential.map R R A A' ''
        Set.range fun k => KaehlerDifferential.D R A (Sum.elim x' y k)) ≤
        (Submodule.span A' (Set.range fun k => KaehlerDifferential.D R A'
          (Sum.elim (fun j => algebraMap A A' (x' j)) (fun k => algebraMap A A' (y k)) k))).restrictScalars A := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      apply Submodule.subset_span
      exact ⟨k, by cases k <;> rfl⟩
    have h5 := hle hm
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul A'] at h5
    obtain ⟨u, hu⟩ := hgu
    have h6 := Submodule.smul_mem _ (↑u⁻¹ : A') h5
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h6
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h := Ideal.mem_map_of_mem (algebraMap A A') (hfx a ha)
      rw [Ideal.map_span, map_mul, ← Set.range_comp] at h
      obtain ⟨u, hu⟩ := hfu
      have h6 := Ideal.mul_mem_left _ (↑u⁻¹ : A') h
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h6
      exact h6
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hxI j)

end LateralTheory.CohomologicalPurity.ChartCut
end
end
