module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
public import Mathlib.RingTheory.RingHom.Unramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle005
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle033
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianIntegralVectorsPairing
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧ ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b → ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  first | (exact @GlobalTheory.W1.Base.forms_baseChange) | (exact GlobalTheory.W1.Base.forms_baseChange) | (intros; apply GlobalTheory.W1.Base.forms_baseChange  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.formally_unramified_differentials_span : ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) (B' : Subalgebra k L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.FormallyUnramified → ∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → L) (w : Fin m → K), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D k L v) = ∑ j, b j • mapDR k K L (ι1 (D k K (w j))) := by
  first | (exact @GlobalTheory.W1.dv_mem_span_of_formallyUnramified) | (exact GlobalTheory.W1.dv_mem_span_of_formallyUnramified) | (intros; apply GlobalTheory.W1.dv_mem_span_of_formallyUnramified  <;> assumption)
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (θ : 𝓞 E) (D : 𝓞 F), (∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ) → ∀ (m : Ideal (𝓞 F)), m ≠ ⊥ → m ≤ Ideal.span {D} → ∀ (y : 𝓞 E) (N : ℕ), ∃ k : 𝓞 E, k - algebraMap (𝓞 F) (𝓞 E) D * y ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (m ^ N) ∧ ∀ P : HeightOneSpectrum (𝓞 E), ¬ m ≤ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) → k ∈ P.asIdeal → DegOne F P := by
  first | exact @GlobalTheory.exists_shift_mod_pow_degOne | exact GlobalTheory.exists_shift_mod_pow_degOne | (intros; apply GlobalTheory.exists_shift_mod_pow_degOne <;> assumption)
end

section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

theorem _root_.GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w → ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  first | exact @GlobalTheory.HeckeSplit.eventually_degOne_moved | exact GlobalTheory.HeckeSplit.eventually_degOne_moved | (intros; apply GlobalTheory.HeckeSplit.eventually_degOne_moved <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

namespace GlobalTheory.WH.PullCoc

section Gen

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

end Gen

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section J2

variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

theorem mapDR_smul_ιMulti {L : Type} [Field L] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] (b : K) (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      algebraMap K L b • ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  rw [map_smul, algebraMap_smul]
  congr 1
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, mapDR, map1, Function.comp_def,
    KaehlerDifferential.map_D]

theorem deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD (j2 : K →ₐ[ℂ] K') (b : K) (q : ℕ) (v : Fin q → K) :
    pr2L j2 (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      j2 b • ExteriorAlgebra.ιMulti K' q fun j => D ℂ K' (j2 (v j)) := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul_ιMulti (L := K') b q v

end J2

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

theorem free_hom_glue_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S)
    (hT : T ∈ Scheme.etaleTopology S)
    (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F))
    (hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) :
    ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v),
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by

  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) T.arrows := fun V v hv =>
    Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))

  have hres : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.res g (Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [map_res, freeGen_res]
    congr 2
  have hcomp : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.map (σ (g ≫ v) (T.downward_closed hv g)) (freeGen R (yoneda.obj W) W (𝟙 W)) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [← hσ v hv g]
    change Sec.map (σ v hv) (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map g)) (freeGen R (yoneda.obj W) W (𝟙 W))) = _
    rw [freeGen_map]
    congr 2
  have hx : x.SieveCompatible := by
    intro V W v g hv
    exact (hcomp v hv g).trans (hres v hv g).symm
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property)
  obtain ⟨s, hs, -⟩ := hF T hT x ((Presieve.compatible_iff_sieveCompatible x).2 hx)
  obtain ⟨t, ht⟩ := free_exists (R := R) (yoneda.obj S) F (fun U g => Sec.res g (show Sec F S from s))
    (fun V U g h => by
      change Sec.res g (Sec.res h _) = Sec.res (g ≫ h) _
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply])
  refine ⟨t, fun V v hv => ?_⟩
  apply free_ext
  intro U w
  change Sec.map t (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map v)) (freeGen R (yoneda.obj V) U w)) = _
  rw [freeGen_map, ht, ← hres v hv w]
  have hsv : Sec.res v (show Sec F S from s) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V)) := hs v hv
  rw [← hsv]
  change Sec.res (w ≫ v) _ = Sec.res w (Sec.res v _)
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end GlobalTheory.EtC.Tr
end
end

section

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.freeSch_hom_ext_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S), T ∈ Scheme.etaleTopology S → (∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) → φ = ψ := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_ext_of_covering  <;> assumption)
end

section

open GlobalTheory.PD

namespace GlobalTheory

theorem finite_quotient_of_integral {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra.FiniteType k S] (f : R →ₐ[k] S) (hi : (f : R →+* S).IsIntegral) (I : Ideal S)
    (hc : ∀ r, ∃ c : k, f r - algebraMap k S c ∈ I) : Module.Finite k (S ⧸ I) := by
  classical
  letI : Algebra R S := (f : R →+* S).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Algebra.IsIntegral R S := ⟨hi⟩
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨⟨G.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hs : s ∈ Submodule.span R (G : Set S) := hG ▸ Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    obtain ⟨c, hc⟩ := hc r
    have e : Ideal.Quotient.mk I (r • a) = c • Ideal.Quotient.mk I a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
      congr 1
      exact Ideal.Quotient.eq.2 hc
    rw [e]
    exact Submodule.smul_mem _ _ ha

end GlobalTheory

namespace GlobalTheory.PD

theorem isArtinianRing_fib_quot : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  intro k K _ _ _ F _ _ _ _ d x h
  haveI := h.smooth 0
  set I := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) with hI
  let f : rA k x {0} →ₐ[k] rB k K x {0} :=
    ((IsScalarTower.toAlgHom k F K).comp (rA k x {0}).val).codRestrict (rB k K x {0})
      (fun a => (integralClosure (rA k x {0}) K).algebraMap_mem a)
  have hi : (f : rA k x {0} →+* rB k K x {0}).IsIntegral := by
    intro s
    obtain ⟨p, hm, hp⟩ := s.2
    refine ⟨p, hm, Subtype.val_injective ?_⟩
    have e := Polynomial.hom_eval₂ p (f : rA k x {0} →+* rB k K x {0}) (rB k K x {0}).val.toRingHom s
    refine e.trans ?_
    exact hp
  have hc : ∀ r, ∃ c : k, f r - algebraMap k _ c ∈ I := by
    rintro ⟨r, hr⟩
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi0, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi0
      subst hi0
      cases j using Fin.cases with
      | zero =>
        refine ⟨1, ?_⟩
        convert I.zero_mem using 1
        rw [map_one, sub_eq_zero]
        refine Subtype.ext ?_
        show algebraMap F K (x 0 / x 0) = 1
        rw [div_self (h.pd.ne 0), map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, sub_zero]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap r =>
      refine ⟨r, ?_⟩
      have : f ⟨algebraMap k F r, _⟩ = algebraMap k _ r := f.commutes r
      rw [this, sub_self]
      exact I.zero_mem
    | add a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ + c₂, ?_⟩
      have : f ⟨a + b, add_mem ha hb⟩ = f ⟨a, ha⟩ + f ⟨b, hb⟩ := map_add f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_add (f := _)]
      convert add_mem h₁ h₂ using 1
      ring
    | mul a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ * c₂, ?_⟩
      have : f ⟨a * b, mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := map_mul f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_mul]
      convert add_mem (I.mul_mem_right (f ⟨b, hb⟩) h₁) (I.mul_mem_left (algebraMap k _ c₁) h₂) using 1
      ring
  haveI := GlobalTheory.finite_quotient_of_integral f hi I hc
  exact IsArtinianRing.of_finite k _

end GlobalTheory.PD
end

section

open GlobalTheory.PRep GlobalTheory.SmGL

theorem _root_.GlobalTheory.T.smoothContragredient_irreducible_and_reflexive : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → (π.IsIrreducible → (contra π).IsIrreducible) ∧ Nonempty (π.Equiv (contra (contra π))) ∧ (Nonempty ((contra π).Equiv (contra π')) → Nonempty (π.Equiv π')) := by
  first | exact @GlobalTheory.ContraRefl.contra_irreducible_reflexive | exact GlobalTheory.ContraRefl.contra_irreducible_reflexive | (intros; apply GlobalTheory.ContraRefl.contra_irreducible_reflexive <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.latticeKernel_le_of_matrixLatticeIndex_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (x y : Matrix (Fin n') (Fin n) L),
    (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x →
    ∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq | exact GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq | (intros; apply GlobalTheory.Hk3.HoweDuality.ker_le_of_latIdx_eq <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.unitaryGroup_newton_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  first | exact @GlobalTheory.Hk3.UnitaryNewton.newton_step | exact GlobalTheory.Hk3.UnitaryNewton.newton_step | (intros; apply GlobalTheory.Hk3.UnitaryNewton.newton_step <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.hermitian_integral_vectors_pairing : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) -
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ g : Matrix (Fin n') (Fin n') L, (∀ i j, g i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1
        ((Formalism.UG.cT σ g * (JT : Matrix (Fin n') (Fin n') L) * g - (JT : Matrix (Fin n') (Fin n') L)) i j)) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((g *ᵥ z i) r - z' i r) := by
  first | exact @GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod | exact GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod | (intros; apply GlobalTheory.Hk3.ResWitt.exists_int_unitary_mod_of_gram_mod <;> assumption)
end
