module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle032
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle350
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058
public import ReciprocityTheory.SemistableReduction.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle087
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle120
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle121
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle358
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle023
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.SemistableReduction.Bundle007

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.valuativeExistence) | (exact GlobalTheory.HilbAff.valuativeExistence) | (intros; apply GlobalTheory.HilbAff.valuativeExistence  <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue Opposite

theorem GlobalTheory.HilbGlue.isSheaf_hilbFunctor {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbFunctor z r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (GlobalTheory.T.hilbert_point_glue_open_cover z r Y 𝒰 x fun i j R b c h => hx i j R b c h)
    fun y y' h h' => GlobalTheory.T.hilbert_point_eq_of_open_cover z r Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem GlobalTheory.HilbGlue.isHilbRep_of_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z →
    LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) →
    IsHilbRep z r := by
  intro S Z z _ _ _ r hS
  have hloc : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, HPt.map c y = x := fun s => by
    obtain ⟨W, hs, hW⟩ := hS s
    exact ⟨W, hs, GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict z r W hW⟩
  have hloc' := hloc
  choose W hsW T y π _ hπ huniq using hloc
  have hrep : (hilbFunctor z r).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover (hilbFunctor z r) (GlobalTheory.HilbGlue.isSheaf_hilbFunctor z r) (hilbProj z r) W
      (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsW s⟩) T y π hπ huniq
  obtain ⟨H, u, hu⟩ : ∃ (H : Scheme.{0}) (u : HPt z r H), ∀ (T : Scheme.{0}) (x : HPt z r T),
      ∃! c : T ⟶ H, HPt.map c u = x := by
    obtain ⟨H, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {T : Scheme.{0}} (c : T ⟶ H), HPt.map c (e.homEquiv (𝟙 H)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨H, e.homEquiv (𝟙 H), fun T x => ⟨e.homEquiv.symm x, (h _).trans (e.homEquiv.apply_symm_apply x),
      fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  have hprop : IsProper u.1 := GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local z r H u hu hloc'
  obtain ⟨h, I⟩ := u
  refine ⟨H, h, I.1.subscheme, I.1.subschemeι, hprop, inferInstance, I.2.1, I.2.2.1, I.2.2.2, ?_⟩
  intro T g V v _ h1 h2 h3
  have hv' : IsFinFlatRk (v ≫ pullback.snd z g) r := ⟨h1, h2, h3⟩
  obtain ⟨c, hc, hcu⟩ := hu T (mkPt g v hv')
  have key : ∀ (f : T ⟶ H) (hf : f ≫ h = g), HPt.map f ⟨h, I⟩ = mkPt g v hv' ↔
      ∃ w : V ⟶ I.1.subscheme, IsPullback v w (bc z f h g hf) I.1.subschemeι := by
    intro f hf
    rw [mkPt, HPt.map_eq_mk_iff f ⟨h, I⟩ hf]
    exact GlobalTheory.HilbGlue.comap_eq_ker_iff (bc z f h g hf) I.1 v
  have hcg : c ≫ h = g := congrArg Sigma.fst hc
  exact ⟨c, ⟨hcg, (key c hcg).1 hc⟩, fun f ⟨hf, hw⟩ => hcu f ((key f hf).2 hw)⟩
end

section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanDrop

theorem measurePreserving_polar_gaussProb (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)))
      ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  set f : UnitSphereC n × Ioi (0:ℝ) → EuclideanSpace ℂ (Fin n) :=
    fun p => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)) with hf_def
  set S := (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hS
  set R0 := Measure.volumeIoiPow (2 * n - 1) with hR0
  set h : Ioi (0:ℝ) → ENNReal := fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)) with hh_def
  set g : EuclideanSpace ℂ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hg_def
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
  have hhm : Measurable h := Measurable.ennreal_ofReal (by fun_prop)
  have hgm : Measurable g := Measurable.ennreal_ofReal (by fun_prop)

  have hA : MeasurePreserving f (S.prod R0) volume := by
    have h1 := Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))
    rw [finrank_euclidean_complex] at h1
    have h2 : MeasurePreserving (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin n))).toMeasurableEquiv
      _ _ := h1
    have h3 := h2.symm
    have h4 : MeasurePreserving (Subtype.val : ({(0 : EuclideanSpace ℂ (Fin n))}ᶜ : Set _) → _)
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).comap Subtype.val) volume := by
      refine ⟨measurable_subtype_coe, ?_⟩
      rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
    have h5 := h4.comp h3
    convert h5 using 1
    funext p
    simp [hf_def]

  have hB : MeasurePreserving f (S.prod (R0.withDensity h))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) := by
    refine ⟨hfm, ?_⟩
    rw [prod_withDensity_right hhm]
    ext s hs
    rw [Measure.map_apply hfm hs, withDensity_apply _ (hfm hs), withDensity_apply _ hs]
    have hpt : ∀ z : UnitSphereC n × Ioi (0:ℝ), h z.2 = g (f z) := by
      intro z
      simp only [hh_def, hg_def, hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < z.2 from z.2.2)]
      have : ‖(z.1 : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
      rw [this, mul_one]
    simp_rw [hpt]
    exact hA.setLIntegral_comp_preimage hs hgm

  have ha0 : S univ ≠ 0 := by
    rw [hS, Measure.toSphere_apply_univ, finrank_euclidean_complex]
    exact mul_ne_zero (by simp; omega) (Metric.measure_ball_pos _ _ one_pos).ne'
  have haT : S univ ≠ ⊤ := measure_ne_top _ _
  have hsph : sphereProb n = (S univ)⁻¹ • S := sphereProb_eq n
  have hrad : radProb n = ((R0.withDensity h) univ)⁻¹ • R0.withDensity h := by
    simp only [radProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hgau : gaussProb n = (((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g := by
    simp only [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hmass : ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ
      = S univ * (R0.withDensity h) univ := by
    rw [← hB.map_eq, Measure.map_apply hfm MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod]
  refine ⟨hfm, ?_⟩
  rw [hsph, hrad, hgau, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ hfm.aemeasurable, hB.map_eq, hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]

end GlobalTheory.SphereMeanDrop
end
end

section

open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (p : α) :
    ∃ t : T, t • p = Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α) := by
  have h : (Quotient.mk'' (Quotient.out (Quotient.mk'' p : MulAction.orbitRel.Quotient T α)) :
      MulAction.orbitRel.Quotient T α) = Quotient.mk'' p := Quotient.out_eq' _
  exact MulAction.orbitRel_apply.1 (Quotient.eq''.1 h)

theorem finite_support_pairs : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite := by
  intro H _ X _ f hinv hfo hsupp
  refine (Set.finite_iUnion fun a : MulAction.orbitRel.Quotient H X =>
    (hsupp (Quotient.out a)).image fun γ => (Quotient.mk'' (ConjPair.mk γ (Quotient.out a)) :
      MulAction.orbitRel.Quotient H (ConjPair H X))).subset ?_
  intro O hO
  have hO' : f (Quotient.out O).elt (Quotient.out O).pt ≠ 0 := hO
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := H) (Quotient.out O).pt
  refine Set.mem_iUnion.2 ⟨Quotient.mk'' (Quotient.out O).pt, δ * (Quotient.out O).elt * δ⁻¹, ?_, ?_⟩
  · show f _ _ ≠ 0
    rw [← hδ, hinv]; exact hO'
  · have e : ConjPair.mk (δ * (Quotient.out O).elt * δ⁻¹)
        (Quotient.out (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) =
        δ • Quotient.out O := by
      rw [← hδ]; rfl
    show (Quotient.mk'' (ConjPair.mk _ _) : MulAction.orbitRel.Quotient H (ConjPair H X)) = O
    rw [e]
    exact (Quotient.sound' (MulAction.mem_orbit _ δ)).trans (Quotient.out_eq' O)

theorem finite_support_weighted {H X : Type} [Group H] [MulAction H X] (f : H → X → ℂ)
    (hfin : {O : MulAction.orbitRel.Quotient H (ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite) :
    (Function.support fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
        f (Quotient.out O).elt (Quotient.out O).pt).Finite := by
  refine hfin.subset fun O hO => ?_
  exact right_ne_zero_of_mul hO

theorem mass_pt_side : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    Finite (MulAction.orbitRel.Quotient H X) → (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) |
      f (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ a : MulAction.orbitRel.Quotient H X,
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out a)) : ℂ)) * ∑ᶠ γ : H, f γ (Quotient.out a) =
      ∑ᶠ O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X),
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O)) : ℂ)) *
          f (Quotient.out O).elt (Quotient.out O).pt := by
  intro H _ X _ f hinv hfo hstab hsupp hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient H (ConjPair H X) =>
      (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X)) _
    (finite_support_weighted f hfin)]
  refine finsum_congr fun a => ?_
  have h := GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum H X f hinv hstab hsupp (Quotient.out a)
  rw [Quotient.out_eq'] at h
  exact h.symm

theorem mass_class_side : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) |
      Φ (Quotient.out O).elt (Quotient.out O).pt ≠ 0}.Finite →
    ∑ᶠ O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X),
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O)) : ℂ)) *
          Φ (Quotient.out O).elt (Quotient.out O).pt =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hstab hfin
  rw [GlobalTheory.finsum_fiberwise_of_finite_support
    (fun O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) => ConjClasses.mk (Quotient.out O).elt) _
    (finite_support_weighted Φ hfin)]
  refine finsum_congr fun c => ?_
  have h := GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass G X Γ Φ hinv (Quotient.out c)
  have e : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c
  rw [e] at h
  exact h

theorem mass_formula_conj : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    Finite (MulAction.orbitRel.Quotient Γ X) → (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    (∀ x : X, (Function.support fun γ : Γ => Φ γ x).Finite) →
    {c : ConjClasses Γ | ∃ x : X, Φ (Quotient.out c) x ≠ 0}.Finite ∧
    ∑ᶠ a : MulAction.orbitRel.Quotient Γ X,
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out a)) : ℂ)) * ∑ᶠ γ : Γ, Φ γ (Quotient.out a) =
      ∑ᶠ c : ConjClasses Γ, ∑ᶠ b : MulAction.orbitRel.Quotient
          (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {((Quotient.out c : Γ) : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ (Quotient.out c) (Quotient.out b) := by
  intro G _ X _ Γ Φ hinv hfo hstab hsupp
  have hinv' : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) (δ • x) = Φ γ x := fun δ γ x => hinv δ γ x
  have hfin := finite_support_pairs Γ X Φ hinv' hfo hsupp
  refine ⟨?_, mass_pt_side Γ X Φ hinv' hfo hstab hsupp hfin |>.trans (mass_class_side G X Γ Φ hinv hstab hfin)⟩
  refine (hfin.image (fun O => ConjClasses.mk (Quotient.out O).elt)).subset ?_
  rintro c ⟨x, hx⟩
  obtain ⟨δ, hδ⟩ := exists_smul_eq_out' (T := Γ) (ConjPair.mk (Quotient.out c) x)
  refine ⟨Quotient.mk'' (ConjPair.mk (Quotient.out c) x), ?_, ?_⟩
  · show Φ _ _ ≠ 0
    rw [← hδ, smul_elt, smul_pt, hinv']
    exact hx
  · show ConjClasses.mk _ = c
    rw [← hδ, smul_elt]
    calc ConjClasses.mk (δ * Quotient.out c * δ⁻¹) = ConjClasses.mk (Quotient.out c) :=
          ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨δ, rfl⟩).symm
      _ = c := Quotient.out_eq c

end GlobalTheory.MassConj
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.coprime_unit_etale_extension : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (exact GlobalTheory.EtC.unit_isPow_on_excisionNbhd) | (intros; apply GlobalTheory.EtC.unit_isPow_on_excisionNbhd  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.unit_eq_mul_pow_on_etaleExcisionNbhd_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  first | (exact @GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus) | (exact GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus) | (intros; apply GlobalTheory.EtC.unit_eq_mul_qth_power_near_zeroLocus <;> assumption)
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_poly_vanishing_of_fiber : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  first | exact @GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre | exact GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre | (intros; apply GlobalTheory.DenseSec.exists_poly_vanishing_of_fibre <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finiteEtale_of_galois_descent_hartogs : ∀ (A R C O : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [IsNoetherianRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Module.FaithfullyFlat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → GlobalTheory.GoodEtale.Hart A R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    Nonempty (C →ₐ[R] O) →
    Module.Finite R C ∧ Algebra.Etale R C := by
  first | (exact @GlobalTheory.GoodEtale.descent_finiteEtale) | (exact GlobalTheory.GoodEtale.descent_finiteEtale) | (intros; apply GlobalTheory.GoodEtale.descent_finiteEtale  <;> assumption)
end

section

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange_point :
    ∀ (A A₁ R R₁ : Type) [CommRing A] [CommRing A₁] [IsDomain A₁] [CommRing R] [Algebra A R]
    [CommRing R₁] [Algebra A₁ R₁] (j : A →+* A₁) (γ : R →+* R₁) (ρ : R →+* A) (ρ₁ : R₁ →+* A₁)
    (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) = (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp γ →
    ρ₁.comp (algebraMap A₁ R₁) = RingHom.id A₁ →
    ρ₁.comp γ = j.comp ρ →
    ∀ (q : ℕ), 0 < q → ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q actA →
    ∃ (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ R₁] DA₁)) (h : DA →+* DA₁),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁ q actA₁ ∧
      h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁).comp β ∧
      ∀ σ : DA →+* FractionRing A₁,
        (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA)).comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
          (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
        ∃ σ₁ : DA₁ →+* FractionRing A₁,
          (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA₁)).comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) =
            (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro A A₁ R R₁ _ _ _ _ _ _ _ j γ ρ ρ₁ β hβ hret hργ q hq DA _ _ actA hT
  letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) := β.toAlgebra
  obtain ⟨act', -, hT'⟩ := GlobalTheory.LocAcyc.isZModTorsor_baseChange (GlobalTheory.LocAcyc.GenFib A R)
    (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA q hq actA hT

  let M₁ := Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁)
  let f : R₁ →+* FractionRing A₁ := (algebraMap A₁ (FractionRing A₁)).comp ρ₁
  have hf : ∀ m : M₁, IsUnit (f m) := by
    rintro ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := hm
    have : ρ₁ (algebraMap A₁ R₁ a) = a := by
      simpa using congrArg (fun φ : A₁ →+* A₁ => φ a) hret
    simp only [f, RingHom.comp_apply, this]
    exact IsLocalization.map_units (FractionRing A₁) (⟨a, ha⟩ : nonZeroDivisors A₁)
  let ρK : GlobalTheory.LocAcyc.GenFib A₁ R₁ →+* FractionRing A₁ :=
    IsLocalization.lift (M := M₁) (S := GlobalTheory.LocAcyc.GenFib A₁ R₁) hf
  have hρK : ρK.comp (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)) = f :=
    IsLocalization.lift_comp hf
  refine ⟨TensorProduct (GlobalTheory.LocAcyc.GenFib A R) (GlobalTheory.LocAcyc.GenFib A₁ R₁) DA, inferInstance,
    inferInstance, act', Algebra.TensorProduct.includeRight.toRingHom, hT', ?_, ?_⟩
  · ext b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  · intro σ hσ
    have hagree : ρK.comp β = σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A R) DA) := by
      apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
      rw [hσ, RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hρK, ← hργ]
      rfl
    letI : Algebra (GlobalTheory.LocAcyc.GenFib A R) (FractionRing A₁) := (ρK.comp β).toAlgebra
    let fA : GlobalTheory.LocAcyc.GenFib A₁ R₁ →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { ρK with commutes' := fun _ => rfl }
    let gA : DA →ₐ[GlobalTheory.LocAcyc.GenFib A R] FractionRing A₁ :=
      { σ with commutes' := fun b => (congrArg (fun φ => φ b) hagree).symm }
    refine ⟨(Algebra.TensorProduct.productMap fA gA).toRingHom, ?_⟩
    ext r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.productMap_apply_tmul, map_one,
      mul_one]
    show ρK (algebraMap R₁ _ r) = _
    rw [← RingHom.comp_apply ρK, hρK]
    rfl

end GlobalTheory.KeyOriginCut
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_normal_local_between_alt : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  first | (exact @GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (exact GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (intros; apply GlobalTheory.LocAcycEmbed.exists_normal_local_between  <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckeEisensteinFourierTerm_move_unit : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  first | exact @GlobalTheory.HeckeTwoUnit.fTerm_unit_move | exact GlobalTheory.HeckeTwoUnit.fTerm_unit_move | (intros; apply GlobalTheory.HeckeTwoUnit.fTerm_unit_move <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isColimit_finiteSubextensionRingCocone : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω], Nonempty (CategoryTheory.Limits.IsColimit (GlobalTheory.SepCech.ringCocone K Ω)) := by
  first | (exact @GlobalTheory.SepCech.ringCocone_isColimit) | (exact GlobalTheory.SepCech.ringCocone_isColimit) | (intros; apply GlobalTheory.SepCech.ringCocone_isColimit  <;> assumption)
end
