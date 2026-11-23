module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.AlgebraicIndependentFreeVar
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AemeasurableFinsumSection
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteVerticalGaussValuations
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableSumEmbeddingsOverGenericPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FdegEqFinrankResidueField
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.AdeleCocompact

variable (F : Type) [Field F] [NumberField F]

theorem exists_bound_sub_integer :
    ∃ C : InfinitePlace F → ℝ, ∀ x : F, ∃ y : 𝓞 F, ∀ v : InfinitePlace F, v (x - y) ≤ C v := by
  classical
  refine ⟨fun v => ∑ i, v (integralBasis F i), fun x => ?_⟩
  refine ⟨∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i, fun v => ?_⟩
  have h : x - ((∑ i, ⌊(integralBasis F).repr x i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F)
      = ∑ i, ((Int.fract ((integralBasis F).repr x i) : ℚ) : F) * integralBasis F i := by
    conv_lhs => enter [1]; rw [← (integralBasis F).sum_repr x]
    change _ - algebraMap (𝓞 F) F _ = _

    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, Int.fract, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring

  rw [h, ← InfinitePlace.norm_embedding_eq, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_mul, norm_mul, InfinitePlace.norm_embedding_eq v (integralBasis F i), map_ratCast,
    Complex.norm_ratCast]
  refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
  rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
  exact_mod_cast (Int.fract_lt_one _).le

omit [NumberField F] in
theorem properSpace_completion (v : InfinitePlace F) : ProperSpace v.Completion := by
  refine ⟨fun x r => ?_⟩
  have h := InfinitePlace.Completion.isometry_extensionEmbedding v
  rw [← h.preimage_closedBall]
  exact h.isClosedEmbedding.isCompact_preimage (isCompact_closedBall _ _)

theorem exists_compact_infinite :
    ∃ K : Set (InfiniteAdeleRing F), IsCompact K ∧
      ∀ a : InfiniteAdeleRing F, ∃ y : 𝓞 F, a - algebraMap F (InfiniteAdeleRing F) y ∈ K := by
  obtain ⟨C, hC⟩ := exists_bound_sub_integer F
  haveI := properSpace_completion F
  refine ⟨Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) (1 + C v),
    isCompact_univ_pi fun v => isCompact_closedBall _ _, fun a => ?_⟩
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (a v) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  obtain ⟨x, hx⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hU
    ⟨a, fun v _ => Metric.mem_ball_self one_pos⟩
  obtain ⟨y, hy⟩ := hC x
  refine ⟨y, fun v _ => ?_⟩
  have h1 : ‖a v - algebraMap F (InfiniteAdeleRing F) x v‖ < 1 := by
    rw [← dist_eq_norm, dist_comm]; exact hx v trivial
  have h2 : ‖algebraMap F (InfiniteAdeleRing F) (x - y) v‖ ≤ C v := by
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
    exact hy v
  have h3 : (a - algebraMap F (InfiniteAdeleRing F) y) =
      (a - algebraMap F (InfiniteAdeleRing F) x) + algebraMap F (InfiniteAdeleRing F) (x - y) := by
    rw [map_sub]; ring
  rw [mem_closedBall_zero_iff, h3]
  exact (norm_add_le (a v - algebraMap F (InfiniteAdeleRing F) x v) _).trans (add_le_add h1.le h2)

theorem isCompact_integral :
    IsCompact {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem exists_compact_adele : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  intro F _ _
  obtain ⟨K, hK, hK'⟩ := exists_compact_infinite F
  refine ⟨K ×ˢ {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    hK.prod (isCompact_integral F), fun a => ?_⟩
  obtain ⟨x, b, hb, hab⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos a.2
  obtain ⟨y, hy⟩ := hK' (a.1 - algebraMap F (InfiniteAdeleRing F) x)
  refine ⟨x + y, ?_, ?_⟩
  · change a.1 - algebraMap F (InfiniteAdeleRing F) (x + y) ∈ K
    rw [map_add (f := _), ← sub_sub]; exact hy
  · change ∀ v, (a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y)) v ∈ v.adicCompletionIntegers F
    have h : a.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (x + y) =
        b - algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
      rw [hab, map_add (f := _), one_smul]; ring
    rw [h]
    intro v
    exact sub_mem (hb v) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v y)

end GlobalTheory.AdeleCocompact
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_support_and_density_and_aemeasurable :
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite) ∧ (∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε) ∧ (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure) :=
  ⟨finite_support_admissible finite_vertical_gauss_valuations finite_zeros_poles_of_trdeg_one,
    generic_points_dense exists_algIndep_tuple_near,
    aemeasurable_finsum_section ae_eval₂_ne_zero_pi_toSphere
      (measurable_sum_embeddings_over_generic_point exists_measurable_roots_enumeration)
      existsUnique_ringHom_OmS⟩

end GlobalTheory
end

section

open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

open IsLocalRing GlobalTheory.ResDegPlace in

theorem _root_.GlobalTheory.T.fdeg_eq_finrank_residueField_alt : ∀ (R R' F : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F], Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif (A := A) ϖ → ∀ (ζ : Pts R' A) [IsDVRAt ζ] (w : AddValuation L (WithTop ℤ)), w ∈ ValPl.PlacesOver R L → ∀ (S : Type) [CommRing S] (u : AddValuation S (WithTop ℤ)) (Ψ : A →+* S) (ι : L →+* S), Function.Surjective Ψ → (∀ r : R, Ψ (algebraMap R' A (algebraMap R R' r)) = ι (algebraMap R L r)) → (∀ g, u (ι g) = w g) → (∀ a, ord ϖ ζ a = u (Ψ a)) → (∀ x, 0 ≤ u x → ∃ g, 0 ≤ w g ∧ 0 < u (x - ι g)) → fdeg ζ = (letI := resAlg (F := F) w; Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap F L))) (IsLocalRing.ResidueField (vRing w))) := by
  intro R R' F _ _ _ _ _ _ _ _ _ _ _ hRR L _ _ _ _ A _ _ ϖ h ζ _ w hw S _ u Ψ ι hΨ hcomp hι hord
    hres
  let := resAlg (F := F) w
  have ord_pos_iff (a : As R' A) : 0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
    rw [ord_of_mem ζ h a.2, ← not_not (a := a ∈ ζ.asIdeal), ← vL_eq_zero_iff ζ a]
    change 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
    generalize vL ζ a = v
    cases v with
    | top => simp
    | coe n =>
      rw [ENat.map_natCast, WithTop.coe_pos]
      simp [Nat.pos_iff_ne_zero]
  have exists_approx (x : A) (hx : 0 ≤ ord ϖ ζ x) :
      ∃ a : As R' A, 0 < ord ϖ ζ ((a : A) - x) := by
    obtain ⟨n, hn⟩ := h.denom x
    have h1 := hx
    rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
      IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective ζ.asIdeal.primeCompl c
    have h2 : algebraMap (As R' A) (Loc ζ) (⟨ϖ ^ n • x, hn⟩ * (s : As R' A)) =
        algebraMap (As R' A) (Loc ζ) (algebraMap R' (As R' A) ϖ ^ n * b) := by
      rw [map_mul, hc, mul_assoc, IsLocalization.mk'_spec, ← map_mul]
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h2
    have h3 : (algebraMap R' A ϖ) ^ n * ((((t : As R' A) : A) * ((s : As R' A) : A)) * x) =
        (algebraMap R' A ϖ) ^ n * (((t : As R' A) : A) * (b : A)) := by
      have := congrArg Subtype.val ht
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow] at this
      have e : ((algebraMap R' (As R' A) ϖ : As R' A) : A) = algebraMap R' A ϖ := rfl
      rw [e] at this
      linear_combination this
    have h4 := (h.isUnit.pow n).mul_right_inj.1 h3
    obtain ⟨d, i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv ζ.isMaximal (t * s).2
    refine ⟨d * (t * b), ?_⟩
    have h5 : ((d * (t * b) : As R' A) : A) - x = ((-i : As R' A) : A) * x := by
      have := congrArg Subtype.val hdi
      simp only [AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one,
        NegMemClass.coe_neg] at this ⊢
      linear_combination x * this - (d : A) * h4
    rw [h5, ord_mul ζ h]
    exact add_pos_of_pos_of_nonneg ((ord_pos_iff _).2 (ζ.asIdeal.neg_mem hi)) hx
  let T : Subring (As R' A × vRing w) :=
    { carrier := {z | 0 < u (Ψ (z.1 : A) - ι (z.2 : L))}
      mul_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2))
        have e : Ψ ((z.1 : A) * z'.1) - ι ((z.2 : L) * z'.2) =
            (Ψ (z'.1 : A) - ι (z'.2 : L)) * Ψ z.1 + (Ψ (z.1 : A) - ι (z.2 : L)) * ι z'.2 := by
          rw [map_mul, map_mul]; ring
        rw [e]
        refine u.map_lt_add ?_ ?_
        · rw [u.map_mul, ← hord]
          exact add_pos_of_pos_of_nonneg hz' (ord_nonneg ζ h z.1.2)
        · rw [u.map_mul, hι]
          exact add_pos_of_pos_of_nonneg hz z'.2.2
      one_mem' := by
        change 0 < u (Ψ 1 - ι 1)
        simp
      add_mem' := by
        intro z z' hz hz'
        change 0 < u (Ψ ((z.1 : A) + z'.1) - ι ((z.2 : L) + z'.2))
        rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
        exact u.map_lt_add hz hz'
      zero_mem' := by
        change 0 < u (Ψ 0 - ι 0)
        simp
      neg_mem' := by
        intro z hz
        change 0 < u (Ψ (-(z.1 : A)) - ι (-(z.2 : L)))
        rw [map_neg, map_neg, ← neg_sub', u.map_neg]
        exact hz }
  have hT : ∀ z : T, 0 < u (Ψ (z.1.1 : A) - ι (z.1.2 : L)) := fun z => z.2
  let jw : R →+* vRing w := (algebraMap R L).codRestrict (vRing w) (fun r => (hw.2 r).1)
  let j : R →+* T := (((algebraMap R' (As R' A)).comp (algebraMap R R')).prod jw).codRestrict T
    (fun r => by
      change 0 < u (Ψ (algebraMap R' A (algebraMap R R' r)) - ι (algebraMap R L r))
      rw [hcomp, sub_self]; simp)
  have hOw : ∀ a : R, algebraMap R F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (hw.2 a).1
  let φ : R →+* (vRing w).comap (algebraMap F L) := (algebraMap R F).codRestrict _ hOw
  let p : T →+* ResidueField (Loc ζ) := ((residue (Loc ζ)).comp (algebraMap (As R' A) (Loc ζ))).comp
    ((RingHom.fst _ _).comp T.subtype)
  let q : T →+* ResidueField (vRing w) := (residue (vRing w)).comp
    ((RingHom.snd _ _).comp T.subtype)
  refine finrank_eq_of_surjective j ((residue R').comp (algebraMap R R')) ((residue _).comp φ) p q
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y
    obtain ⟨y, rfl⟩ := hRR y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨r, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨a, ha⟩ := exists_eq_of_nonneg hw (x : F) x.2
    exact ⟨a, congrArg (residue _) (Subtype.ext ha)⟩
  · intro y
    have := ζ.isMaximal
    obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective ζ.asIdeal y
    obtain ⟨g, hg, hag⟩ := hres (Ψ a) (by rw [← hord]; exact ord_nonneg ζ h a.2)
    exact ⟨⟨(a, ⟨g, hg⟩), hag⟩, rfl⟩
  · intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    obtain ⟨x, hx⟩ := hΨ (ι g)
    obtain ⟨a, ha⟩ := exists_approx x (by rw [hord, hx, hι]; exact g.2)
    rw [hord, map_sub, hx] at ha
    exact ⟨⟨(a, g), ha⟩, rfl⟩
  · intro z
    change residue (Loc ζ) (algebraMap (As R' A) (Loc ζ) z.1.1) = 0 ↔ residue (vRing w) z.1.2 = 0
    rw [residue_eq_zero_iff, residue_eq_zero_iff, mem_maximalIdeal_vRing,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Loc ζ) ζ.asIdeal, ← ord_pos_iff, hord, ← hι]
    refine ⟨pos_of_sub_pos u ?_, pos_of_sub_pos u (hT z)⟩
    rw [← neg_sub, u.map_neg]
    exact hT z
  · intro r
    rfl
  · intro r
    change residue (vRing w) (comapIncl (vRing w) (algebraMap F L) (φ r)) = residue (vRing w) (jw r)
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply R F L r).symm
end

end

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory

theorem _root_.GlobalTheory.T.exists_compact_adeleRing_mod_numberField : ∀ (F : Type) [Field F] [NumberField F], ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ a : AdeleRing (𝓞 F) F, ∃ x : F, a - algebraMap F (AdeleRing (𝓞 F) F) x ∈ K := by
  first | exact @GlobalTheory.AdeleCocompact.exists_compact_adele | exact GlobalTheory.AdeleCocompact.exists_compact_adele | (intros; apply GlobalTheory.AdeleCocompact.exists_compact_adele <;> assumption)

end
end
