module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle042
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Formalism.LocalToGlobal.SiegelLatticeTheory.EFSymmCont
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle382
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem exists_eq_of_isAlgebraic (ι : Qb →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) : ∃ x, ι x = z := by
  let := ι.toAlgebra
  have hi : IsIntegral Qb z := (hz.tower_top Qb).isIntegral
  exact minpoly.mem_range_of_degree_eq_one Qb z
    (IsAlgClosed.degree_eq_one_of_irreducible Qb (minpoly.irreducible hi))

def qbEquiv (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ M] : qb ι M ≃+* M :=
  RingEquiv.ofBijective ((ι.comp (qb ι M).val.toRingHom).codRestrict M fun x => x.2) ⟨RingHom.injective _, fun z => by
    obtain ⟨x, hx⟩ := exists_eq_of_isAlgebraic ι
      (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z))
    exact ⟨⟨x, mem_qb.2 (hx ▸ z.2)⟩, Subtype.ext hx⟩⟩

theorem numberField_qb (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] : NumberField (qb ι M) :=
  NumberField.of_ringEquiv M _ (qbEquiv ι M).symm

variable {E : Type} [Field E] [NumberField E] (j : E →ₐ[ℚ] Qb)

@[instance_reducible] def algThrough (L : Fld) (h : j.fieldRange ≤ L) : Algebra E L :=
  (j.toRingHom.codRestrict L fun x => h ⟨x, rfl⟩).toAlgebra

theorem finrank_div (L : Type) [Field L] [NumberField L] [Algebra E L] :
    Module.finrank ℚ L / Module.finrank ℚ E = Module.finrank E L := by
  rw [← Module.finrank_mul_finrank ℚ E L, Nat.mul_div_cancel_left _ Module.finrank_pos]

theorem isRayField_qb (ι : Qb →+* ℂ) {𝔮 : Ideal (𝓞 E)} {M : IntermediateField ℚ ℂ}
    (hM : IsRayFieldIn (ι.comp j.toRingHom) 𝔮 M) :
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M), letI := algThrough j _ h; IsRayField E (qb ι M) 𝔮 := by
  obtain ⟨h, hN, hR⟩ := hM
  have hle : j.fieldRange ≤ qb ι M := by
    rintro _ ⟨x, rfl⟩
    exact h x
  refine ⟨numberField_qb ι M, hle, ?_⟩
  let := algOf _ M h
  let := algThrough j _ hle
  have := numberField_qb ι M
  exact hR.of_algEquiv (AlgEquiv.ofRingEquiv (f := qbEquiv ι M) fun x => rfl).symm

theorem le_of_algHom {L N : Fld} (hL : j.fieldRange ≤ L) (hN : j.fieldRange ≤ N)
    (hn : letI := algThrough j L hL; Normal E L)
    (ψ : letI := algThrough j L hL; letI := algThrough j N hN; L →ₐ[E] N) : L ≤ N := by
  let := algThrough j L hL
  let := algThrough j N hN
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower E N Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : L →ₐ[E] Qb := (IsScalarTower.toAlgHom E N Qb).comp ψ
  intro x hx
  obtain ⟨y, hy⟩ := (φ.restrictNormal' L).surjective ⟨x, hx⟩
  have h1 : algebraMap L Qb (φ.restrictNormal' L y) = φ y := φ.restrictNormal_commutes L y
  rw [hy] at h1
  have h2 : x = (ψ y : Qb) := h1
  exact h2 ▸ (ψ y).2

theorem isAbelianGalois_iff (L : Fld) (h : j.fieldRange ≤ L) :
    (letI := algThrough j L h; IsAbelianGalois E L) ↔
      ∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x) := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ E Qb := IsScalarTower.of_algebraMap_eq fun q => (j.commutes q).symm
  have : IsAlgClosure ℚ Qb := AlgebraicClosure.instIsAlgClosure ℚ
  have : IsGalois ℚ Qb := IsAlgClosure.isGalois ℚ Qb
  have : IsGalois E Qb := IsGalois.tower_top_of_isGalois ℚ E Qb
  have hmem : ∀ s : Qb ≃ₐ[E] Qb, s.restrictScalars ℚ ∈ GalOf j.fieldRange := fun s => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, rfl⟩
    exact s.commutes x
  constructor
  · intro hab s hs t ht x hx
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ht
    let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
    let t' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := t.toRingEquiv) fun y => ht _ ⟨y, rfl⟩
    have hc : AlgEquiv.restrictNormalHom L (s' * t') = AlgEquiv.restrictNormalHom L (t' * s') := by
      rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]
    have h1 := AlgEquiv.restrictNormal_commutes (s' * t') L ⟨x, hx⟩
    have h2 := AlgEquiv.restrictNormal_commutes (t' * s') L ⟨x, hx⟩
    have h3 : (s' * t').restrictNormal L = (t' * s').restrictNormal L := hc
    rw [h3, h2] at h1
    exact h1.symm
  · intro H
    have hst : ∀ s : Qb ≃ₐ[E] Qb, ∀ x ∈ L, s x ∈ L := fun s x hx => by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro t ht
      have h1 := H t (IntermediateField.fixingSubgroup_antitone h ht) _ (hmem s) x hx
      rw [(IntermediateField.mem_fixingSubgroup_iff _ _).1 ht x hx] at h1
      exact h1
    let L' : IntermediateField E Qb := (IsScalarTower.toAlgHom E L Qb).fieldRange
    have hn' : Normal E L' := IntermediateField.normal_iff_forall_map_le'.2 fun s => by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨⟨_, hst s x x.2⟩, rfl⟩
    let e : L ≃ₐ[E] L' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E L Qb)
    have hn : Normal E L := Normal.of_algEquiv e.symm
    have : IsGalois E L := {}
    refine { is_comm := ⟨fun a b => ?_⟩ }
    obtain ⟨s, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb a
    obtain ⟨t, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) Qb b
    rw [← map_mul, ← map_mul]
    refine AlgEquiv.ext fun x => (algebraMap L Qb).injective ?_
    exact (AlgEquiv.restrictNormal_commutes (s * t) L x).trans
      ((H _ (hmem s) _ (hmem t) x x.2).trans (AlgEquiv.restrictNormal_commutes (t * s) L x).symm)

theorem map_mem_of_normal (L : Fld) (h : j.fieldRange ≤ L) (hn : letI := algThrough j L h; Normal E L) :
    ∀ s ∈ GalOf j.fieldRange, ∀ x ∈ L, s x ∈ L := by
  let := algThrough j L h
  let : Algebra E Qb := j.toRingHom.toAlgebra
  have : IsScalarTower E L Qb := IsScalarTower.of_algebraMap_eq fun _ => rfl
  intro s hs x hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  let s' : Qb ≃ₐ[E] Qb := AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun y => hs _ ⟨y, rfl⟩
  have h1 : ((s'.restrictNormal L ⟨x, hx⟩ : L) : Qb) = s x := AlgEquiv.restrictNormal_commutes s' L ⟨x, hx⟩
  exact h1 ▸ (s'.restrictNormal L ⟨x, hx⟩).2


omit j in
theorem hilbert_qb : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ (_ : NumberField (qb ι M)) (h : j.fieldRange ≤ qb ι M),
      (letI := algThrough j _ h; IsAbelianGalois E (qb ι M)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L] (hL : j.fieldRange ≤ L), (letI := algThrough j L hL; IsAbelianGalois E L) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hR⟩ := isRayField_qb j ι hM
  let := algThrough j _ h
  have := hR.1
  refine ⟨hN, h, hR.1, ?_, fun L _ hL hab hd => ?_⟩
  · rw [finrank_div]
    exact (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E _).1 fun 𝔭 =>
      hR.2.1 𝔭 fun hd => 𝔭.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hd))
  · let := algThrough j L hL
    rw [finrank_div] at hd
    obtain ⟨ψ⟩ := GlobalTheory.UnramInRay.nonempty_algHom_rayField H E L (qb ι M) ⊤ top_ne_bot hR
      ((GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr E L).2 hd)
    exact le_of_algHom j hL h inferInstance ψ


omit j in
theorem hilbert_qb_aut : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ), IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M), j.fieldRange ≤ qb ι M ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s x ∈ qb ι M) ∧
      (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ qb ι M, s (t x) = t (s x)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L], j.fieldRange ≤ L →
        (∀ s ∈ GalOf j.fieldRange, ∀ t ∈ GalOf j.fieldRange, ∀ x ∈ L, s (t x) = t (s x)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hab, hd, hmax⟩ := hilbert_qb H E j ι M hM
  refine ⟨hN, h, map_mem_of_normal j _ h ?_, (isAbelianGalois_iff j _ h).1 hab, hd,
    fun L _ hL hc => hmax L hL ((isAbelianGalois_iff j L hL).2 hc)⟩
  let := algThrough j _ h
  infer_instance

end GlobalTheory.HilbertInClosure

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem continuous_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {a : ℕ} (f : A →+* B) (hf : Continuous f) (ρ : Γ →* GL (Fin a) A)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A)) :
    Continuous fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) := by
  have : (fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B)) =
      fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
    funext g; rfl
  rw [this]
  exact hρ.matrix_map hf

end GlobalTheory.HeightCounting.PhtExt

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

noncomputable def ext (Wd₀ : WDSide D T) : WDSide D T :=
  { Wd₀ with
    IsdRW := fun l _ ι a r w =>
      (Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ Wd₀.IsdRW l ι r w
    wdOf_unrL := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_unrL l ι r w hw hc hd.2
    wdOf_mono0L := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_mono0L l ι r w hw hc hd.2
    loc := by
      intro l _ ι w hw O _ _ _ Bw hB φ hφ
      obtain ⟨h1, h2⟩ := Wd₀.loc l ι w hw O Bw hB φ hφ
      have hφc : Continuous φ := by
        have e : (φ : O → Qbar l) = fun x => ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) := funext hφ
        rw [e]
        unfold LocBridge.toLL
        exact continuous_subtype_val.comp (continuous_subtype_val.comp Bw.eO_cont)
      refine ⟨fun m ρ hρ => ?_, fun LL' hLL' m ρ hρ => ?_⟩
      · obtain ⟨c1, c2, c3, c4⟩ := h1 m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep φ hφc ρ hρ)).trans c2, c3, c4⟩
      · have hf : Continuous (algebraMap ↥LL'.1 (Qbar l)) := continuous_subtype_val
        obtain ⟨c1, c2, c3, c4⟩ := h2 LL' hLL' m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep _ hf ρ hρ)).trans c2, c3, c4⟩ }

theorem exists_phtOn_all : PhtCmp → ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), WDSide D T →
    ∃ Wd : WDSide D T, PhtOn Wd fr fun _ _ _ _ => True := by
  intro hP D fr T Wd₀
  exact ⟨ext Wd₀, ⟨fun l _ ι a r τ w _ hw hd => (hP D fr T Wd₀).card l ι a r τ w hd.1 hw hd.2⟩⟩

end GlobalTheory.HeightCounting.PhtExt
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorHolo

section Hol

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Z : Scheme.{0}}

theorem isHolTo_of_openImmersion (i : X ⟶ Z) [IsOpenImmersion i] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have hU : i ⁻¹ᵁ (i ''ᵁ U) = U := i.preimage_image_eq U
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [← ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp] at this
    exact this
  exact key U hU f

theorem isHolTo_const {B : Set W} (hB : IsOpen B) (x : Sp ℂ ⟶ X) : IsHolTo B fun _ => x := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simpa only [h, and_true, Set.ofPred_mem_eq] using hB
  · simpa only [h, and_false, Set.ofPred_false] using isOpen_empty

theorem isHolTo_of_fst {S : Scheme.{0}} (p : X ⟶ Z) (q : S ⟶ Z) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    {y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback p q)} (s : Sp ℂ ⟶ S) (hs : ∀ b, y b ≫ pullback.snd _ _ = s)
    (h : IsHolTo B fun b => y b ≫ pullback.fst _ _) : IsHolTo B y := by
  have he : ∀ b, (y b ≫ pullback.fst p q) ≫ p = s ≫ q := fun b => by
    rw [← hs b, Category.assoc, Category.assoc, pullback.condition]
  refine LocLift.isHolTo_congr (holPair _ _ _ p q n B _ (fun _ => s) he hB h (isHolTo_const hB s)) fun b _ => ?_
  exact pullback.hom_ext (pullback.lift_fst _ _ _).symm ((hs b).trans (pullback.lift_snd _ _ _).symm)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousOn_of_isHolTo {B : Set W} {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1) :
    ContinuousOn y B := by
  rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
    ext b
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩

theorem differentiableAt_chart {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1)
    (ch : AlgChart p σ D) {b : W} (hb : b ∈ B) (hy : y b ∈ ch.e.source) :
    DifferentiableAt ℂ (fun v => ch.e (y v)) b := by
  refine (differentiableAt_piLp 2).2 fun a => ?_
  have h1 := ((h ch.U (ch.x a)).2).differentiableAt ((h ch.U (ch.x a)).1.mem_nhds ⟨hb, ch.source_subset hy⟩)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [((continuousOn_of_isHolTo h).continuousAt (hB.mem_nhds hb)).preimage_mem_nhds
    (ch.e.open_source.mem_nhds hy)] with v hv
  exact ch.apply_eq _ hv a

theorem isHolTo_symm (ch : AlgChart p σ D) : IsHolTo ch.e.target fun v => (ch.e.symm v).1 := fun U f =>
  ⟨ChartGlue.isOpen_over ch.e (isOpen_ptsIn U), ch.holo U f⟩

end Hol

section Frames

open GlobalTheory.TorsionHolomorphic ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (X : Data E r) {B : Set W}

theorem differentiableOn_perFr {x : W → Frame X.Ψ r} (hx : ∀ b ∈ B, x b ∈ X.dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b) τ a c) B) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    DifferentiableOn ℂ (fun b => perFr X (x b) v τ i) B := by
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun a _ =>
      (differentiableOn_matrix_inv _ B (hd _) (fun b hb => (hx b hb _).1) _ _).mul_const _
  · exact differentiableOn_const _
  · simp only [hermC]
    exact DifferentiableOn.fun_sum fun a _ => DifferentiableOn.fun_sum fun c _ =>
      ((hd _ _ _).mul_const _).mul_const _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem differentiable_stdMat [Fintype Tau] (hj : j ≤ r) (κ : Tau ≃ X.Ψ) (τ : X.Ψ) (a c : Fin r) :
    Differentiable ℂ fun v => mat (stdMat X hj κ (unflat v)) τ a c := by
  refine differentiableOn_univ.1 (differentiableOn_matrix_mul (fun _ => mat (x0F X) τ)
    (fun v => reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) _
    (fun _ _ => differentiableOn_const _) (fun a c => ?_) a c)
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases idx hj a with a | a <;> rcases idx hj c with c | c
  · exact differentiableOn_const _
  · exact differentiableOn_apply (κ.symm τ, a, c) _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

end Frames

end GlobalTheory.TrueCx.TorHolo
end
end

section

noncomputable section

namespace GlobalTheory.Mem.SProv

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

theorem conjF_invol (B : Pre) (x : B.host.E) : B.conjF (B.conjF x) = x := by
  rw [B.conjF_eq, B.conjF_eq]
  simpa [Examples₂.conjF_apply] using Examples₂.conjF_conjF B.host x

theorem exists_sStage_true : ∀ (K : Ctx) (B : Base) (C : Cols B) (W : RowsRest B C) (cd : CDHaar), K.Over B.toPre →
    SpectralModel.ColsPos C → W.Drows ≤ W.Dall → ∃ S : SStage B C W, S.s.Del = (Delv K.s K.cD : ℚ) ∧
      S.s.cdScale = Vol.trueScale cd ∧ (∀ τ, S.dsig τ = Vol.trueDsig B.R (B.hc τ)) ∧
      ∀ (V : DivStage B C W) (N : NStage B C W) (G : GJStage B C) p,
        Nonempty (Formalism.L2.S.LocIso ((assemble B C W V S N G).s.atP p) (Formalism.L2.S.locC (assemble B C W V S N G) p)) := by
  intro K B C W cd h h2 h3
  obtain ⟨S, a, b, c, d⟩ := exists_sStage_loc K B C W cd h h2 h3
    (fun p => Examples₂.locAtC B.toPre.conjF (conjF_invol B.toPre) (Examples₂.finrank_FE B.host) p)
  exact ⟨S, a, b, c, fun V N G => Formalism.L2.S.loc_of_adj (assemble B C W V S N G) d⟩

end GlobalTheory.Mem.SProv

end
end

section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Mem.Top.NodeGap

theorem gapHyp_of_nodes (D : D7) (hm : 1801 ≤ D.R.m) (h : ℕ) (hh : 16 * (D.R.r : ℝ) ^ 19 ≤ (h : ℝ))
    (hb : ∀ τ, ∃ b1 : ℤ, ∀ j : Fin D.R.m, (D.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ)) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.m_add_three_le_k
    show 1801 ≤ D.R.k + D.R.m - 1
    omega
  · intro τ j hj
    obtain ⟨b1, hb1⟩ := hb τ
    rw [hb1 ⟨j.1 + 1, hj⟩, hb1 j]
    have h2 : 16 * D.R.r ^ 19 ≤ h := by exact_mod_cast hh
    have h3 : (16 * (D.R.r : ℚ) ^ 19) ≤ (h : ℚ) := by exact_mod_cast h2
    push_cast
    linarith

private theorem ev_mono_of_forall_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  unfold Ev at hp ⊢
  obtain ⟨w, hw, H⟩ := hp
  refine ⟨w, hw, fun eps C8 a b c d => ?_⟩
  obtain ⟨K0, H1⟩ := H eps C8 a b c d
  refine ⟨K0, fun C e f g => ?_⟩
  obtain ⟨c1, H2⟩ := H1 C e f g
  refine ⟨c1, fun cD hc => ?_⟩
  obtain ⟨c2, H3⟩ := H2 cD hc
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H4⟩ := H3 ch hch
  exact ⟨x0, fun K k1 k2 k3 k4 k5 => h K (H4 K k1 k2 k3 k4 k5)⟩

theorem ev_gapHyp : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → Formalism.L2.SG.ConcreteSettingExists.GapHyp X.toD7 := by
  refine ev_mono_of_forall_imp ?_ (ev_nodes 16 19 1801)
  intro K hK X hX
  obtain ⟨hm, h, hh, hb⟩ := hK X hX
  exact gapHyp_of_nodes X.toD7 hm h hh fun τ => (hb τ).imp fun b1 hb1 j => (hb1 j).1

end GlobalTheory.Mem.Top.NodeGap
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroForms

theorem law0_choose_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V),
    (l0 u I.mu0).choose x = x := by
  intro B X I h l Z l0 u x
  apply (I.fm l u I.mu0).emb_inj 0
  rw [(l0 u I.mu0).choose_spec.2 x]
  show LinearEquiv.funCongrLeft ℂ _ (I.eCls0 l u I.mu0).symm ((I.fm l u I.mu0).emb 0 x) = _
  funext c
  rw [LinearEquiv.funCongrLeft_apply]
  show (I.fm l u I.mu0).emb 0 x ((I.eCls0 l u I.mu0).symm c) = _
  have hc : (I.eCls0 l u I.mu0).symm c = c :=
    (I.eCls0 l u I.mu0).symm_apply_eq.2 (GlobalTheory.T.eCls0_mu0_eq_self I h l u c).symm
  rw [hc]

end GlobalTheory.Mem.Col2.TC.MuZeroForms
end
