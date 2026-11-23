module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
public import Formalism.SharpRestriction.Divisibility.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Host

variable (D : D7) (H : Geo.Tor.Host D.host.E)

theorem isAbelianGalois_host : IsAbelianGalois ℚ D.host.E := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have : IsMulCommutative Gal(D.host.E/ℚ) := ⟨⟨fun σ τ => hbij.1 (by rw [hmul, hmul, _root_.mul_comm])⟩⟩
  exact {}

theorem not_cube_dvd (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ¬ w.asIdeal ^ 3 ∣ Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have hp := D.host.hyp.2.1
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := w.isPrime
  have hmax : (Ideal.span {(D.host.d : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have : w.asIdeal.LiesOver (Ideal.span {(D.host.d : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simpa using hw)⟩
  have hb : (Ideal.span {(D.host.d : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have hIn : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) =
        Nat.card ({1, D.R.toFrame.iod} : Set (D.R.GG)) :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbij) fun σ => by
        rw [AddSubgroup.mem_inertia]
        exact D.host.der.inertia_d w.asIdeal σ)
    rw [e, Nat.card_coe_set_eq, Set.ncard_pair]
    intro h
    have := congrArg (fun g : D.R.GG => g.1.2) h
    exact absurd (show (1 : ℤˣ) = -1 from this) (by decide)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(D.host.d : ℤ)}) w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(D.host.d : ℤ)}) w.asIdeal hb] at hIn
  intro h
  have hm : Ideal.map (algebraMap ℤ (𝓞 D.host.E)) (Ideal.span {(D.host.d : ℤ)}) =
      Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton]; simp
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity (by rw [hm]; simpa using hp.ne_zero) w.isPrime, hm] at hIn
  have hf : FiniteMultiplicity w.asIdeal (Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)}) := by
    by_contra hn
    rw [multiplicity_eq_one_of_not_finiteMultiplicity hn] at hIn
    omega
  have := hf.le_multiplicity_of_pow_dvd h
  omega

theorem isHostField (hd : H.d = D.host.d) : EigenvectorLieDegree.IsHostField H := by
  have hA := isAbelianGalois_host D
  obtain ⟨-, -, hdisc, hmov⟩ := PlaceInt.host_galois_discr_moves D H
  refine (HostRamif.isHostField_iff _ H).2 ⟨hA, fun l w hl hdv hw hlw => ?_⟩
  have h1 : l ∣ D.host.condN := hdisc l hl hdv
  have h2 : l ∈ D.host.small ∨ l = D.host.q ∨ l = D.host.d := (D.host.toHostRaw.dvd_condN_iff_small hl).1 h1
  refine ⟨fun h => ?_, fun h => (HostRamif.isSquare_iff H hl hw hlw h).1 ?_, fun h h3 => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (hmov l (Nat.mem_primeFactors.2 ⟨hl, h1, D.host.toHostRaw.condN_ne_zero⟩)).2 w hw.isPrime hlw
    exact hx' (h ▸ Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hx)
  · rcases h2 with h2 | rfl | h2
    · by_cases e2 : l = 2
      · subst e2
        exact FiniteField.isSquare_of_char_two (ZMod.ringChar_zmod_n 2) _
      · have := Fact.mk hl
        have := ZMod.isSquare_of_jacobiSym_eq_one
          (D.host.QS_split l hl e2 ((D.host.toHostRaw.mem_small_iff).1 h2).2)
        rw [hd]
        simpa using this
    · have := Fact.mk hl
      have := ZMod.isSquare_of_jacobiSym_eq_one D.host.hyp.2.2.2.2
      rw [hd]
      simpa using this
    · exact absurd (h2.trans hd.symm) h
  · obtain rfl : l = D.host.d := h.trans hd
    have hb : w ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hlw
      exact hl.ne_zero (by exact_mod_cast hlw)
    exact not_cube_dvd D ⟨w, hw.isPrime, hb⟩ hlw (Ideal.dvd_span_singleton.2 h3)

end Host

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_eigenBasis {S : Scheme.{0}} {T : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {t : SAB H (Sp R)}
    (n : SABMap t T x) {χ : 𝓞 E →+* R} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)} (hv : EigenvectorLieDegree.IsEigBasis t.act χ v) :
    ∃ u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G), FramedFlatCoordinates.IsEigenBasis T.act x χ u ∧ ∀ i, (v i).left ≫ n.φ = (u i).left := by
  have h := n.cart
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  have one : (1 : Over.mk x ⟶ T.G).left = η[t.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ t.G), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have hP : ∀ v : epsR R ⟶ t.G, EigenvectorLieDegree.IsEigVec t.act χ v ↔ FramedFlatCoordinates.IsEigenTangent T.act x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[t.G]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ t.act.act c) = e v ≫ T.act.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, n.act, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin m → (epsR R ⟶ t.G), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine ⟨fun i => e (v i), ⟨fun i => (hP _).1 (hv.1 i), fun w hw => ?_⟩, fun i => (he _).symm⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (hv.2 w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

variable {Y : Model Xo c β} {Xc : (Xo.XF c).Opens} {τ : E →+* ℂ}

end Point

section Record

variable {D : D7} (large₂ : SizeData₂ D) {X : DivX D} (Lc : placeRankTwoOne.Loc D X)

end Record

end GlobalTheory.FlatRow
end
end

section

noncomputable section

namespace GlobalTheory.Equiv.StdSpace

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coe_pi_one_eq_intVecs (n : ℕ) :
    ((Submodule.pi Set.univ (fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) :
      Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D n := by
  ext x
  rw [SetLike.mem_coe, Submodule.mem_pi]
  exact ⟨fun k a => Submodule.mem_one.1 (k a trivial), fun k a _ => Submodule.mem_one.2 (k a)⟩

theorem identityClassLattice_eq_selfDualFrameLattice (V : HSp D) : (Bridge.hLat V 1 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank _ hfg hsp).1
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.coe_set_eq]
  unfold Bridge.hLat
  rw [← Submodule.span_eq (GlobalTheory.Member.latC V)]
  congr 1
  ext x
  rw [SetLike.mem_coe, ← key x, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq,
    show ((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) = 1 from Subtype.ext inv_one]
  show (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ _ ∈
    Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ _
  rw [Matrix.one_mulVec]
  exact Iff.rfl

theorem lattice_clause_iff (V : HSp D) :
    (Bridge.hLat V 1 = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔
      L0c D V = GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.intVecs D V.rank := by
  rw [← identityClassLattice_eq_selfDualFrameLattice, ← coe_pi_one_eq_intVecs, SetLike.coe_set_eq]

end GlobalTheory.Equiv.StdSpace

end
end

section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2KernelIntegral

theorem integrable_descend_orbitSum {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {h : G → ℂ} (hh : Integrable h μ) :
    Integrable (descend Γ (orbitSum Γ h)) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, (leftInv_orbitSum h).lift_descend]
    have hm : ∀ γ : Γ, AEMeasurable (fun x => h (γ * x)) μ := fun γ =>
      hh.1.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving
    exact (AEMeasurable.tsum hm).aestronglyMeasurable
  · have h1 := lintegral_eq_lintegral_tsum (Γ := Γ) hh.1.enorm
    refine lt_of_le_of_lt ?_ (h1.symm.trans_lt hh.2)
    exact lintegral_mono fun q => enorm_tsum_le_tsum_enorm

theorem convR_eq_integral_kernelQ : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ (F : L2 Γ μ) (x : G),
      Integrable (fun q => kernelQ Γ f (mk Γ x) q * F q) (_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∧
        convR μ f (lift Γ F) x = ∫ q, kernelQ Γ f (mk Γ x) q * F q ∂_root_.GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F x
  have hf' : Continuous fun y => f (x⁻¹ * y) := hf.comp (continuous_const_mul _)
  have hc' : HasCompactSupport fun y => f (x⁻¹ * y) := hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have hloc : LocallyIntegrable (lift Γ F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact G Γ μ F C hC).2
  have hi : Integrable (fun y => f (x⁻¹ * y) * lift Γ F y) μ :=
    hloc.integrable_smul_left_of_hasCompactSupport hf' hc'
  have key : descend Γ (orbitSum Γ fun y => f (x⁻¹ * y) * lift Γ F y) =
      fun q => kernelQ Γ f (mk Γ x) q * F q := by
    funext q
    induction q using Quotient.inductionOn with
    | h y =>
      refine ((leftInv_orbitSum _).descend_mk y).trans ?_
      change _ = kernelQ Γ f (mk Γ x) (mk Γ y) * F (mk Γ y)
      rw [kernelQ_mk, kernel_eq_orbitSum, orbitSum, orbitSum, ← tsum_mul_right]
      exact tsum_congr fun γ => congrArg (fun z => _ * F z) (mk_mul γ y)
  refine ⟨key ▸ integrable_descend_orbitSum hi, ?_⟩
  rw [convR_eq, integral_eq_integral_orbitSum (Γ := Γ) hi, key]

end GlobalTheory.AutomorphicL2KernelIntegral
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ

theorem B_free_finite : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → Module.Free ℤ_[l] (X.B N l w) ∧ Module.Finite ℤ_[l] (X.B N l w) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hcop hw
  have L1 : ∀ x : X.Khat l, (l : ℤ_[l]) • x = 0 → x = 0 := fun x hx => GlobalTheory.T.kummerCompletion_no_prime_torsion X l x hx
  have Ladd : ∀ b b' c c', BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := fun b b' c c' h h' => GlobalTheory.T.bettiKummerRelationPadic_add X N l b b' c c' h h'
  have Lsmul : ∀ (r : ℤ_[l]) b c, BtZ X N l b c → BtZ X N l (r • b) (r • c) := fun r b c h => GlobalTheory.T.bettiKummerRelationPadic_smul X N l r b c h
  have Lzero : BtZ X N l 0 0 := btZ_zero X N l
  have L3 : ∀ b, BtZ X N l b 0 → b = 0 := fun b h => GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero ε X hε hj N l (by omega) b h
  have L4 : Module.Finite ℤ_[l] (Z1 N l w) := GlobalTheory.T.gammaOneGammaZeroHomogeneousCocycles_finite N l w (by omega)
  have L5 : ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := GlobalTheory.T.exists_betti_cocycle_kummer_relation ε X hε hj N l w hl2 hN hcop hw

  let S : Submodule ℤ_[l] (X.Fn l × Z1 N l w) :=
    { carrier := {p | BtZ X N l p.1 (p.2 : Gam N l → MvPolynomial (Fin 2) ℤ_[l])}
      add_mem' := fun {p q} hp hq => by simpa using Ladd _ _ _ _ hp hq
      zero_mem' := by simpa using Lzero
      smul_mem' := fun r p hp => by simpa using Lsmul r _ _ hp }
  have hinj : Function.Injective ((LinearMap.snd ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
    intro p q hpq
    have hd : (p : X.Fn l × Z1 N l w) - q ∈ S := S.sub_mem p.2 q.2
    have h2 : ((p : X.Fn l × Z1 N l w) - q).2 = 0 := by simpa [sub_eq_zero] using hpq
    have h1 : ((p : X.Fn l × Z1 N l w) - q).1 = 0 := by
      apply L3
      have := hd
      simp only [S, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rwa [h2] at this
    apply Subtype.ext
    exact sub_eq_zero.mp (Prod.ext h1 h2)
  haveI : IsNoetherian ℤ_[l] (Z1 N l w) := inferInstance
  haveI hSf : Module.Finite ℤ_[l] S := Module.Finite.of_injective _ hinj
  have hle : X.B N l w ≤ S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) := by
    refine Submodule.span_le.mpr ?_
    intro b hb
    obtain ⟨c, hc, hbc⟩ := L5 b hb
    exact ⟨(b, ⟨c, hc⟩), hbc, rfl⟩
  have hfg : (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))).FG := by
    have e : S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)) =
        LinearMap.range ((LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w)).comp S.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [e]
    exact Module.Finite.iff_fg.mp inferInstance
  have hB : (X.B N l w).FG := by
    haveI : IsNoetherian ℤ_[l] (S.map (LinearMap.fst ℤ_[l] (X.Fn l) (Z1 N l w))) := isNoetherian_of_fg_of_noetherian _ hfg
    have := (isNoetherian_submodule.mp this) (X.B N l w) ?_
    · exact this
    · exact hle
  haveI hBf : Module.Finite ℤ_[l] (X.B N l w) := Module.Finite.iff_fg.mpr hB

  have Lpow : ∀ (k : ℕ) (x : X.Khat l), ((l : ℤ_[l]) ^ k) • x = 0 → x = 0 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      apply L1
      rw [← mul_smul, ← pow_succ']; exact hx
  haveI : NoZeroSMulDivisors ℤ_[l] (X.B N l w) := by
    refine ⟨fun {r b} h => ?_⟩
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrw := PadicInt.unitCoeff_spec hr
    apply Subtype.ext
    funext u
    have h' : (r • (b : X.Fn l)) u = 0 := by
      have := congrArg (fun y : X.B N l w => (y : X.Fn l) u) h
      simpa using this
    have h'' : ((l : ℤ_[l]) ^ r.valuation) • (((PadicInt.unitCoeff hr : ℤ_[l]ˣ) : ℤ_[l]) • (b : X.Fn l) u) = 0 := by
      rw [smul_smul, mul_comm, ← hrw]; simpa using h'
    have := Lpow _ _ h''
    simpa using this
  exact ⟨Module.free_of_finite_type_torsion_free', hBf⟩

end GlobalTheory.KZ
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.KZ.exists_pot_rel_of_mem_bSet : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  intro Ω _ _ _ ε X _ hj N l w hl h2 hN hc hw b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨φ, hφ, hφ'⟩ := hj
  exact GlobalTheory.T.exists_kummerPotentialRelation_padic Ω ε X l ⟨φ, hφ', hφ⟩ N w (by omega) h2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hc.symm) hw b (Submodule.subset_span hb)
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.H3.LamInj

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] [CharZero E] :
    Function.Injective (algebraMap ℤ_[l] E) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have e := PadicInt.unitCoeff_spec h0
  rw [e, map_mul, map_pow, map_natCast] at hx
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rcases mul_eq_zero.1 hx with h | h
  · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[l] E)).ne_zero h
  · exact pow_ne_zero _ hl h

theorem gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem gamma_le_gam (N l : ℕ) : CongruenceSubgroup.Gamma (N * l) ≤ Gam N l := by
  intro δ hδ
  have h1 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro l rfl : N ∣ N * l) hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (gamma_le_of_dvd (Dvd.intro_left N rfl : l ∣ N * l) hδ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N δ).2 ⟨h1.1, h1.2.2.2, h1.2.2.1⟩, CongruenceSubgroup.Gamma0_mem.2 h2.2.2.1⟩

theorem fst_eq_zero_of_triv : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E], CharZero E →
    ∀ (y : E ⊗[ℤ_[l]] X.Fn l) (G : ℂ → MvPolynomial (Fin 2) E), (y, G) ∈ H3.abelian₂ X l E → G ∈ Triv E w (Gam N l) →
    y = 0 := by
  intro Ω _ _ _ ε X _ _ N l w _ hN E _ _ hE y G hp hG
  exact GlobalTheory.T.trivial_eigenvalue_congruence_vanishes Ω ε X l E (algebraMap_injective l E) w (Gam N l) (N * l)
    (Nat.mul_pos hN (Fact.out : l.Prime).pos) (gamma_le_gam N l) (y, G) hp hG

end GlobalTheory.KZ.H3.LamInj
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ ∧ IsLat 1 φ := by
  first | exact @GlobalTheory.ThEx.thex | exact GlobalTheory.ThEx.thex | (intros; apply GlobalTheory.ThEx.thex <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.definiteThetaPair_testVector_expansion : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  first | exact @GlobalTheory.NormSum.Expand.om_expand | exact GlobalTheory.NormSum.Expand.om_expand | (intros; apply GlobalTheory.NormSum.Expand.om_expand <;> assumption)
end
