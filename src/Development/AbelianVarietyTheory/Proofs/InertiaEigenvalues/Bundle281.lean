module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle260
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle254
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointObjectsTransportAlongConjugationOverFractio
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituent
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import ReciprocityTheory.BasicDefinitions.AdRep
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isDeRham_of_restrict_galois_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.DeRhamDescent.isDR_of_restrict | exact GlobalTheory.DeRhamDescent.isDR_of_restrict | (intros; apply GlobalTheory.DeRhamDescent.isDR_of_restrict <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LocalIntegers

theorem goodO_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (good_integers l LL).1

end GlobalTheory.LocalIntegers
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem goodO_ringOfIntegers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

end GlobalTheory.Pass
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.UnramifiedClasses

theorem eq_zero_of_locallyConstant {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A : Type} [AddCommGroup A] (I : Subgroup G) (φ : G)
    (hgen : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤) (c : G → A)
    (hlc : IsLocallyConstant c) (hc : ∀ g h, c (g * h) = c g + c h) (hφ : c φ = 0)
    (hI : ∀ g ∈ I, c g = 0) (g : G) : c g = 0 := by
  have h1 : c 1 = 0 := by
    have := hc 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  let H : Subgroup G :=
    { carrier := {g | c g = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hc, ha, hb, add_zero]
      one_mem' := h1
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have := hc a a⁻¹
        rw [mul_inv_cancel, h1, ha, zero_add] at this
        exact this.symm }
  have hle : Subgroup.zpowers φ ⊔ I ≤ H :=
    sup_le ((Subgroup.zpowers_le (G := G)).mpr hφ) (fun g hg => hI g hg)
  have hcl : (Subgroup.zpowers φ ⊔ I).topologicalClosure ≤ H :=
    Subgroup.topologicalClosure_minimal _ hle (hlc.isClosed_fiber 0)
  rw [hgen] at hcl
  exact hcl (Subgroup.mem_top g)

theorem isLocallyConstant_mkQ {X : Type} [TopologicalSpace X] {O V : Type} [CommRing O]
    [AddCommGroup V] [Module O V] [TopologicalSpace V] [ContinuousAdd V] (T : Submodule O V)
    (hT : IsOpen (T : Set V)) (f : X → V) (hf : Continuous f) :
    IsLocallyConstant (fun x => T.mkQ (f x)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => f y + (-f x)) ⁻¹' (T : Set V),
    hT.preimage (hf.add continuous_const), by simp, fun y hy => ?_⟩
  simp only [Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, sub_eq_add_neg]
  exact hy

theorem exists_not_mem_range {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field LL] [Algebra O LL] [IsFractionRing O LL] :
    ∃ y : LL, y ∉ Set.range (algebraMap O LL) := by
  by_contra h
  push Not at h
  apply IsDiscreteValuationRing.not_isField O
  exact (RingEquiv.ofBijective (algebraMap O LL)
    ⟨IsFractionRing.injective O LL, h⟩).toMulEquiv.isField (Field.toIsField LL)

theorem HfD_eq_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [IsTopologicalGroup G] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL] [IsTopologicalRing LL], GoodO (Qp := Qp) LL O → ∀ (T : LocLat G Qp LL O), Module.finrank LL T.V = 1 → (∀ g x, T.ρ g x = x) → Module.finrank LL (FiniteCohomology PD T.ρ) = 1 → ∀ (I : Subgroup G) (φ : G), (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤ → ∀ δ : G → LL, δ ∈ finiteCocycles PD (1 : Representation LL G LL) → (∀ g ∈ I, δ g = 0) → δ ≠ 0 → HfD PD T.L ≠ ⊥ ∧ ∀ c : G → T.V ⧸ T.L.T, c ∈ HfD PD T.L ↔ (c ∈ divisibleCocycles T.L ∧ ∃ x, ∀ g ∈ I, c g = actD T.L g x - x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ _ LL _ _ _ O _ _ _ hO T hV hρ
    hH I φ hgen δ hδ hδI hδ0
  have hopen := GlobalTheory.Cyc.locLat_isOpen hO T
  obtain ⟨⟨hdom, hdvr, hfr⟩, -⟩ := hO
  obtain ⟨⟨e, he⟩, -⟩ := GlobalTheory.LineLattice.lattice_rank_one T.L hV
  obtain ⟨y₀, hy₀⟩ := exists_not_mem_range (O := O) (LL := LL)
  obtain ⟨⟨hδc, hδh⟩, x₀, hx₀⟩ := hδ
  have hδadd : ∀ g h, δ (g * h) = δ g + δ h := fun g h => by simpa using hδh g h
  have hact : ∀ g (x : T.V ⧸ T.L.T), actD T.L g x = x := by
    intro g x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg (Submodule.Quotient.mk (p := T.L.T)) (hρ g x)
  have hBD : BD T.L = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [hact]
  have hB1 : B1 T.ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob, hρ]
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hc₀c : Continuous fun g => e (δ g) := by
    have : (fun g => e (δ g)) = fun g => δ g • e 1 := by
      funext g
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact hδc.smul continuous_const
  have hc₀ : (fun g => e (δ g)) ∈ finiteCocycles PD T.ρ := by
    let m := AlgebraTensorModule.map (e : LL →ₗ[LL] T.V) (LinearMap.id : B →ₗ[Qp] B)
    have hm : ∀ g y, m (actVB PD (1 : Representation LL G LL) g y) = actVB PD T.ρ g (m y) := by
      intro g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m, actVB, hρ]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    refine ⟨⟨hc₀c, fun g h => by simp only [hδadd, map_add (f := _), hρ]⟩, m x₀, fun g => ?_⟩
    have := congrArg m (hx₀ g)
    simp only [m, AlgebraTensorModule.map_tmul, LinearMap.id_apply, map_sub] at this
    rw [← hm]
    exact this
  obtain ⟨g₀, hg₀⟩ : ∃ g, δ g ≠ 0 := Function.ne_iff.mp hδ0
  have hdim : Module.finrank LL ↥(finiteCocycles PD T.ρ) = 1 := by
    rw [← hH]
    refine (Submodule.quotEquivOfEqBot _ ?_).finrank_eq.symm
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  have hspan : ∀ z ∈ finiteCocycles PD T.ρ, ∃ a : LL, ∀ g, z g = e (a * δ g) := by
    intro z hz
    have hne : (⟨_, hc₀⟩ : ↥(finiteCocycles PD T.ρ)) ≠ 0 := by
      intro h
      have := congrFun (congrArg Subtype.val h) g₀
      exact hg₀ (by simpa using this)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hz⟩
    refine ⟨a, fun g => ?_⟩
    have := congrFun (congrArg Subtype.val ha) g
    rw [← smul_eq_mul, map_smul]
    exact this.symm

  let r : LL → G → T.V ⧸ T.L.T := fun a g => T.L.T.mkQ (e (a * δ g))
  have hHf : ∀ c, c ∈ HfD PD T.L ↔ ∃ a, c = r a := by
    intro c
    unfold HfD
    rw [hBD, sup_bot_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨a, ha⟩ := hspan z hz
      exact ⟨a, funext fun g => by simp [r, ha]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨a • fun g => e (δ g), (finiteCocycles PD T.ρ).smul_mem a hc₀, ?_⟩
      funext g
      simp [r, ← map_smul]
  have hrlc : ∀ a, IsLocallyConstant (r a) := fun a => by
    refine isLocallyConstant_mkQ T.L.T hopen (fun g => e (a * δ g)) ?_
    have : (fun g => e (a * δ g)) = fun g => a • e (δ g) := by
      funext g
      rw [← map_smul, smul_eq_mul]
    rw [this]
    exact hc₀c.const_smul a
  have hradd : ∀ a g h, r a (g * h) = r a g + r a h := fun a g h => by
    simp only [r, hδadd, mul_add, map_add (f := _)]
  have hrI : ∀ a, ∀ g ∈ I, r a g = 0 := fun a g hg => by
    simp only [r, hδI g hg, mul_zero, map_zero]
  have hr₀ : r (y₀ / δ g₀) g₀ ≠ 0 := by
    intro h
    simp only [r, div_mul_cancel₀ _ hg₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    exact hy₀ ((he _).mp h)
  have hφ : δ φ ≠ 0 := by
    intro h
    exact hr₀ (eq_zero_of_locallyConstant I φ hgen _ (hrlc _) (hradd _)
      (by simp only [r, h, mul_zero, map_zero]) (hrI _) g₀)
  refine ⟨fun h => ?_, fun c => ?_⟩
  · have : r (y₀ / δ g₀) ∈ HfD PD T.L := (hHf _).mpr ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact hr₀ (congrFun this g₀)
  · rw [hHf]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨hrlc a, fun g h => by rw [hact, hradd]⟩, 0, fun g hg => by
        rw [hrI a g hg, hact, sub_zero]⟩
    · rintro ⟨⟨hlc, hcoc⟩, x, hx⟩
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (c φ)
      refine ⟨e.symm v / δ φ, funext fun g => sub_eq_zero.mp ?_⟩
      refine eq_zero_of_locallyConstant I φ hgen (fun g => c g - r (e.symm v / δ φ) g)
        (hlc.sub (hrlc _)) (fun g h => ?_) ?_ (fun g hg => ?_) g
      · simp only [hcoc, hact, hradd]
        abel
      · simp only [r, div_mul_cancel₀ _ hφ, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, hv,
          sub_self]
      · simp only [hx g hg, hact, hrI _ g hg, sub_self]

end GlobalTheory.UnramifiedClasses
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.StableLat

theorem exists_lattice : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  intro G _ _ _ Qp LL O _ _ _ _ _ _ _ hO A
  classical
  obtain ⟨⟨hDom, hDVR, hFrac⟩, -, -, hTop, hOpen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := hTop
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL

  let e := Module.finBasis LL A.V
  let n := Module.finrank LL A.V
  let T₀ : Submodule O A.V := Submodule.span O (Set.range e)
  have hT₀fg : T₀.FG := Submodule.fg_span (Set.finite_range e)
  have hT₀span : Submodule.span LL (T₀ : Set A.V) = ⊤ := by
    simp only [T₀, Submodule.span_span_of_tower, e.span_eq]
  have hT₀open : IsOpen (T₀ : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hOpen T₀ hT₀fg hT₀span

  have hcov : ∀ x : A.V, ∃ b : nonZeroDivisors O, (b : O) • x ∈ T₀ := by
    intro x
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
      (fun i => e.repr x i)
    refine ⟨b, ?_⟩
    have hx : (b : O) • x = ∑ i, (b : O) • (e.repr x i • e i) := by
      rw [← Finset.smul_sum, e.sum_repr]
    rw [hx]
    refine T₀.sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := hb i (Finset.mem_univ i)
    rw [← smul_assoc, ← ha, algebraMap_smul]
    exact T₀.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)

  let C : Set A.V := ⋃ i, Set.range fun g : G => A.ρ g (e i)
  have hC : IsCompact C := isCompact_iUnion fun i => isCompact_range (A.cont (e i))
  let U : nonZeroDivisors O → Set A.V := fun b => (fun x => (b : O) • x) ⁻¹' (T₀ : Set A.V)
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    have : (fun x : A.V => (b : O) • x) = fun x => algebraMap O LL b • x := by
      funext x; rw [algebraMap_smul]
    exact hT₀open.preimage (this ▸ continuous_const_smul _)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU (fun x _ => by
    obtain ⟨b, hb⟩ := hcov x; exact Set.mem_iUnion.2 ⟨b, hb⟩)
  let b : O := ∏ c ∈ t, (c : O)
  have hb0 : b ∈ nonZeroDivisors O := by
    simpa [b] using (∏ c ∈ t, c).2
  have hbC : ∀ y ∈ C, b • y ∈ T₀ := by
    intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have : b = (∏ d ∈ t.erase c, (d : O)) * c := by
      simp only [b]; rw [← Finset.prod_erase_mul _ _ hct]
    rw [this, mul_smul]
    exact T₀.smul_mem _ hc

  let T : Submodule O A.V := Submodule.span O C
  have hCT : C ⊆ T := Submodule.subset_span
  have hstable : ∀ g, ∀ x ∈ T, A.ρ g x ∈ T := by
    intro g x hx
    have hle : T ≤ T.comap ((A.ρ g).restrictScalars O) := by
      refine Submodule.span_le.2 ?_
      intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, rfl⟩ := hi
      show A.ρ g (A.ρ h (e i)) ∈ T
      rw [← Module.End.mul_apply, ← map_mul]
      exact hCT (Set.mem_iUnion.2 ⟨i, g * h, rfl⟩)
    exact hle hx

  let f : A.V →ₗ[O] A.V := b • LinearMap.id
  have hbne : algebraMap O LL b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb0 (hinj (by rw [h, map_zero]))
  have hf : Function.Injective f := by
    intro x y hxy
    have : algebraMap O LL b • x = algebraMap O LL b • y := by
      simpa [f, algebraMap_smul] using hxy
    exact smul_right_injective A.V hbne this
  have hfT : T.map f ≤ T₀ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 fun y hy => ?_
    simpa [f] using hbC y hy
  have hTfg : T.FG := Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hT₀fg hfT)
  haveI : NoZeroSMulDivisors O A.V := ⟨fun {c x} h => by
    rw [← algebraMap_smul LL c x] at h
    rcases smul_eq_zero.1 h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h⟩
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hTfg
  have hfree : Module.Free O T := Module.free_of_finite_type_torsion_free'
  have hspan : Submodule.span LL (T : Set A.V) = ⊤ := by
    rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span (hCT (Set.mem_iUnion.2 ⟨i, 1, ?_⟩))
    simp
  exact ⟨⟨T, hstable, hTfg, hfree, hspan⟩⟩

end GlobalTheory.StableLat
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Pointwise

namespace GlobalTheory.InertiaEigenvalues

theorem actQ_pow_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  intro l _ G _ _ LL _ _ _ O _ _ hG A LA r hI x
  obtain ⟨_, _, _, hTR, hO⟩ := hG
  haveI := hTR
  haveI : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  set c : LL := ((l : ℕ) : LL) ^ r with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hT : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO LA.T LA.fg LA.span
  have hcT : IsOpen (c • (LA.T : Set A.V)) := hT.smul₀ hc0
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [IsLocallyConstant.iff_exists_open]
  intro g0
  refine ⟨(fun g => A.ρ g t - A.ρ g0 t) ⁻¹' (c • (LA.T : Set A.V)),
    hcT.preimage ((A.cont _).sub continuous_const), ?_, ?_⟩
  · show A.ρ g0 t - A.ρ g0 t ∈ c • (LA.T : Set A.V)
    rw [sub_self]
    exact ⟨0, LA.T.zero_mem, smul_zero c⟩
  · intro g hg
    obtain ⟨w, hw, hwe⟩ := hg
    simp only [actQ, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨⟨w, hw⟩, Submodule.mem_top, ?_⟩
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_sub, actT, LinearMap.restrict_coe_apply,
      LinearMap.coe_restrictScalars]
    rw [← algebraMap_smul LL ((l : O) ^ r) w, map_pow, map_natCast]
    exact hwe

end GlobalTheory.InertiaEigenvalues
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.pointObjects_transport_along_conjugation_over_fraction_field : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), (∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)))) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) → ∀ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S → ∃ S' : IdempotentChoiceData N i, S'.g0 = S.g0 ∧ GoodCongruenceObjects N r' ρ' π S' := by
  first | exact @GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main | exact GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main | (intros; apply GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.span_representation_density_of_isInternal_constituents : ∀ {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V) (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K V) (hs : ∀ j, Stable ρ (Vs j)), DirectSum.IsInternal Vs → (∀ j, Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) → (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[K] Vs j', ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v)) → ∀ f : V →ₗ[K] V, (∀ j, ∀ v ∈ Vs j, f v ∈ Vs j) → f ∈ Submodule.span K (Set.range ρ) := by
  first | exact @GlobalTheory.BlockDensity.density | exact GlobalTheory.BlockDensity.density | (intros; apply GlobalTheory.BlockDensity.density <;> assumption)
end

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem finite_module_killed_by_pow_of_not_isUnit :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  intro O _ _ lam hlam X _ _ _
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes (R := O) X lam
  set Y : Submodule O X := LinearMap.range (lam ^ n • (LinearMap.id : X →ₗ[O] X)) with hY
  have hFG : Y.FG := Module.Finite.iff_fg.mp inferInstance
  have hle : Y ≤ Ideal.span {lam} • Y := by
    intro y hy
    have hy' : y ∈ LinearMap.range (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) := by
      rw [← hn (n + 1) (Nat.le_succ n)]; exact hy
    obtain ⟨x, rfl⟩ := hy'
    have hmem : lam ^ n • x ∈ Y := ⟨x, by simp⟩
    have : (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) x = lam • (lam ^ n • x) := by
      simp [pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self lam) hmem
  have hjac : Ideal.span {lam} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal lam).mpr hlam
  have hbot : Y = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ Y hFG hle hjac
  refine ⟨n, fun x => ?_⟩
  have : lam ^ n • x ∈ Y := ⟨x, by simp⟩
  rw [hbot] at this
  simpa using this

end GlobalTheory
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.laurent_coeff_neg_eq_zero_of_bounded' : ∀ (F : ℂ⸨X⸩) (T C : ℝ), (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) → ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  first | exact @GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | exact GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | (intros; apply GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded <;> assumption)
end
