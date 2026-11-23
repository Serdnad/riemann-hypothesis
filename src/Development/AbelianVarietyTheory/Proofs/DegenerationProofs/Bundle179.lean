module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle131
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle117
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle176
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle112
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.AbelianLocus

theorem isProper_of_eq {S G G₁ G₂ : Scheme.{0}} (f : G ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    {K₁ K₂ : Type} [Field K₁] [Field K₂] {t₁ : Sp K₁ ⟶ S} {t₂ : Sp K₂ ⟶ S}
    {φ₁ : G₁ ⟶ G} {f₁ : G₁ ⟶ Sp K₁} {φ₂ : G₂ ⟶ G} {f₂ : G₂ ⟶ Sp K₂}
    (h₁ : IsPullback φ₁ f₁ f t₁) (h₂ : IsPullback φ₂ f₂ f t₂) (p₁ : Sp K₁) (p₂ : Sp K₂) (hp : t₁ p₁ = t₂ p₂)
    [IsProper f₁] : IsProper f₂ := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t₁) (g := t₂) p₁ p₂ hp
  let j := (pullback t₁ t₂).fromSpecResidueField z
  let u := j ≫ pullback.fst t₁ t₂
  let u' := j ≫ pullback.snd t₁ t₂
  have e : u ≫ t₁ = u' ≫ t₂ := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback f₁ u).paste_horiz h₁
  have P₂ := (IsPullback.of_hasPullback f₂ u').paste_horiz h₂
  rw [← e] at P₂
  have h₃ : UniversallyClosed (pullback.snd f₂ u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd f₂ u'), P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K₂) := inferInstanceAs (Subsingleton (PrimeSpectrum K₂))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed f₂ :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₃
  have : IsSeparated f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  have : LocallyOfFiniteType f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  exact ⟨⟩

theorem mem_abLocus_iff {S G₁ : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] {t : Sp K ⟶ S} {φ : G₁ ⟶ G.left} {f : G₁ ⟶ Sp K} (h : IsPullback φ f G.hom t)
    (p : Sp K) : t p ∈ abLocus G ↔ IsProper f := by
  constructor
  · intro hp
    let K' := AlgebraicClosure K
    let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have q : Sp K' := (default : PrimeSpectrum K')
    have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
    have := hp K' (u ≫ t) ⟨q, e⟩
    exact isProper_of_eq G.hom (IsPullback.of_hasPullback G.hom (u ≫ t)) h q p e
  · rintro hf K' _ _ t' ⟨q, hq⟩
    exact isProper_of_eq G.hom h (IsPullback.of_hasPullback G.hom t') p q hq.symm

theorem isProper_iff_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (hs : C.Split c) :
    IsProper H.hom ↔ d = 0 := by
  obtain ⟨hc, i, hi⟩ := hs
  obtain ⟨B, _, q, hB, hq, hf, hsu, ha, hp, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hi
  have := hi.hom
  constructor
  · intro hH
    have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique _ _⟩
    have : Mono i := MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hp.flip this
    have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mono K (Fin d → ℤ) H i hi.hom
    rcases d with _ | d
    · rfl
    · exact absurd (congrFun (Subsingleton.elim (0 : Fin (d + 1) → ℤ) 1) 0) zero_ne_one
  · rintro rfl
    have : Mono q := ⟨fun {Y} x y hxy => by
      have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
        rfl
      have h2 : hp.lift _ _ h1 = 1 := by
        apply (splitTorusPointsEquiv (Sp K) (Fin 0 → ℤ) Y).injective
        refine MonoidHom.ext fun a => ?_
        rw [Subsingleton.elim a 1, map_one, map_one]
      have h3 := hp.lift_fst _ _ h1
      rw [h2, MonObj.one_comp] at h3
      exact mul_inv_eq_one.1 h3.symm⟩
    have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
    have := hB.proper
    have := hB.smooth
    have : LocallyOfFinitePresentation (q.left ≫ B.hom) := by rw [Over.w q]; infer_instance
    have : LocallyOfFiniteType (q.left ≫ B.hom) := inferInstance
    have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp _ B.hom
    have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
    have : LocallyOfFinitePresentation q.left := inferInstance
    have : IsOpenImmersion q.left := IsOpenImmersion.of_flat_of_mono _
    have : IsIso q.left := isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext q.left.surjective.range_eq)
    rw [← Over.w q]
    infer_instance

theorem isProper_snd {P Z : Scheme.{0}} (f : P ⟶ Z) [IsProper f] (G : P.Opens) (U : Z.Opens) (h : f ⁻¹ᵁ U ≤ G) :
    IsProper (pullback.snd (G.ι ≫ f) U.ι) := by
  have h₁ := IsPullback.of_hasPullback f U.ι
  have h₂ := IsPullback.of_hasPullback G.ι (pullback.fst f U.ι)
  have h₃ := h₂.paste_vert h₁
  have : IsIso (pullback.snd G.ι (pullback.fst f U.ι)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    refine Set.eq_univ_of_forall fun x => h ?_
    have : pullback.fst f U.ι x ∈ Set.range (pullback.fst f U.ι) := ⟨x, rfl⟩
    rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at this
  rw [← h₃.isoPullback_inv_snd]
  infer_instance

theorem abLocus_eq : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → ∀ Zab : C.Z.Opens, (∀ w : C.P.left, IsClosed ({w} : Set C.P.left) → C.P.hom w ∈ Zab → w ∈ C.G) → (∀ z : C.Z, IsClosed ({z} : Set C.Z) → z ∉ Zab → z ∉ abLocus C.GG) → abLocus C.GG = Zab ∧ IsProper (pullback.snd C.GG.hom Zab.ι) := by
  intro C L hT hC Zab h₁ h₂
  let := L.grp
  have := L.comm
  obtain ⟨hsep, hlft, hqc, -⟩ := GlobalTheory.ZJ.core_basic C
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have := C.proper
  have := C.lft
  have hle : C.P.hom ⁻¹ᵁ Zab ≤ C.G := by
    have := (GlobalTheory.jacobson_closedPoints_tools_int C.P.left (C.P.hom ≫ C.π)).2.2.1 (C.P.hom ⁻¹ᵁ Zab)
      (C.P.hom ⁻¹ᵁ Zab ⊓ C.G) fun w hw => ⟨fun h => ⟨h, h₁ w hw h⟩, fun h => h.1⟩
    exact inf_eq_left.1 this.symm
  have hpr : IsProper (pullback.snd C.GG.hom Zab.ι) := isProper_snd C.P.hom C.G Zab hle
  refine ⟨Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_), hpr⟩
  · by_contra hzn
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hs, hcl⟩ := GlobalTheory.T.exists_dense_closedPoints_chartSplitting C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd _ _))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have key : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R)
        [IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom s)],
        Charts.Split (H := (Over.pullback s).obj ((Over.pullback t).obj C.GG))
          (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c → ∀ p, (t (s p) ∈ abLocus C.GG ↔ d = 0) := by
      intro K _ s _ hsp p
      have : Smooth ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IsSeparated ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (IsSeparated (pullback.snd _ _))
      have : QuasiCompact ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (QuasiCompact (pullback.snd _ _))
      rw [← isProper_iff_of_split K ((Over.pullback s).obj ((Over.pullback t).obj C.GG))
        (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c hsp]
      exact mem_abLocus_iff C.GG ((IsPullback.of_hasPullback (pullback.snd C.GG.hom t) s).paste_horiz
        (IsPullback.of_hasPullback C.GG.hom t)) p
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    have hgen := GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hs
    have p₀ : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
    have hp₀ : Out.jK R p₀ = (⊥ : PrimeSpectrum R) := by
      have : p₀ = (⊥ : PrimeSpectrum (FractionRing R)) := Subsingleton.elim (α := PrimeSpectrum _) _ _
      subst this
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
    have hd0 : d = 0 := (key _ _ hgen p₀).1 (by rw [hp₀, ht]; exact hz)
    have : Nonempty (Sp R) := ⟨(⊥ : PrimeSpectrum R)⟩
    obtain ⟨x, hx⟩ := hd.nonempty
    obtain ⟨K, _, s, _, hr, hsp⟩ := hs x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range s := hr ▸ rfl
    refine h₂ _ (hcl _ hx) (fun hm => hzn ?_) ((key K s hsp p).2 hd0)
    have hsz : (⊥ : PrimeSpectrum R) ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have := (hsz.map t.continuous).mem_open Zab.2 hm
    rwa [← ht]
  · rintro K _ _ t ⟨p, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have hr : Set.range t ⊆ Set.range Zab.ι := by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim q p]
      exact hz
    have P := (IsPullback.of_hasPullback (pullback.snd C.GG.hom Zab.ι) (IsOpenImmersion.lift Zab.ι t hr)).paste_horiz
      (IsPullback.of_hasPullback C.GG.hom Zab.ι)
    rw [IsOpenImmersion.lift_fac] at P
    rw [← P.isoPullback_inv_snd]
    infer_instance

end GlobalTheory.ZJ.AbelianLocus
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.UT

theorem eigensection_support : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (q : QkPt D.toPre F N) τ, q.y = 0 → IsTor τ q.g → ∀ x, QkToAkU U.toUnifPre F N q x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) (s : Fam D.toPre F N) (c : F), U.ExpandsF F N w₀ t s → IsActOf A.A A.L N θ t t' → (∀ j, t'.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j) → ∀ β, (τ (Multiplicative.ofAdd β)).val ≠ c → ∀ j, (s.s β).f j = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ N hN q τ hy hτ x hx θ hθ w₀ hw₀ t t' s c hs hact ht β hβ j
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hI D F N hN q).1
  have h₁ := (expBijF_and_expandsF_lin hL R I hI D A G hG U).2 F N w₀ t t t' s s (c - 1) hs hs (fun i => by
    rw [ht i]
    simp only [liftFun, map_sub, map_one, sub_mul, _root_.one_mul, sub_add_cancel])
  have h₂ := symLift_acts_as_phi hL R I hI D A G hG U F N hN q x hx θ hθ w₀ hw₀ w hw t t' s _ hs h₁ hact
  have h₃ := ((TorusWeight.torus_weight hL R I hI D A G hG U F N hN q τ hy hτ w hw).2 _ _).1 h₂ β j
  rw [sub_smul, one_smul, sub_add_cancel, DVR.smul_f, constBF_eq] at h₃
  have key : ∀ {S : Type} [CommRing S] (g : F →+* S) (a b : F) (y : S), a ≠ b → g b * y = g a * y → y = 0 := by
    intro S _ g a b y hab e
    have hu : IsUnit (g (a - b)) := (IsUnit.mk0 _ (sub_ne_zero.2 hab)).map g
    exact hu.mul_right_eq_zero.1 (by rw [map_sub, sub_mul, e, sub_self])
  exact key ((((DegPre.BF D.toPre F).left.presheaf.map (homOfLE le_top).op).hom).comp (gF D.toPre F)) _ c _ hβ h₃

end GlobalTheory.UT
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem exists_parAt : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (a : u.PtC), ∃ g, u.ParAt S.N a g := by
  intro hL hT o Ω _ _ _ _ S ρ p _ y₀ u l a
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h1 : 2 ≤ ρ.n ^ ρ.k := le_trans ρ.n_prime.two_le
      (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    nlinarith
  haveI : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  obtain ⟨k, hk, hint⟩ := GlobalTheory.T.theta_test_power_integral hL o Ω S ρ p y₀ u a
  obtain ⟨a₁, ⟨c, hc, hca⟩, hpow⟩ := GlobalTheory.T.exists_integral_nthRoot_testModel_point hL o Ω S ρ p y₀ u (a ^ k) k hk hint
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_torusExtensionPoint_of_integralModelPoint hL o Ω S ρ p y₀ u c hc
  have hpar := (GlobalTheory.T.torusCoord_unit_and_section_eq_expansion hL o Ω S ρ p y₀ u c g₁ a₁ hc hca hg₁).2
  have hNk : 1 ≤ S.N * k := Nat.mul_pos (by omega) hk
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.N * k) hNk
  haveI : IsMonHom u.U.gen.hom := u.U.gen_hom
  have hk' : (a₁ ≫ u.U.gen.hom) ^ k = (a ≫ u.U.gen.hom) ^ k := by
    rw [← MonObj.pow_comp, ← MonObj.pow_comp, hpow]
  have hx : ((a ≫ u.U.gen.hom) * (a₁ ≫ u.U.gen.hom)⁻¹) ^ (S.N * k) = 1 := by
    rw [mul_comm S.N k, pow_mul, mul_pow, inv_pow, hk', mul_inv_cancel, one_pow]
  obtain ⟨pk, hpk⟩ := hsurj _ hx
  obtain ⟨g, hg⟩ := (gt_add_iota_sub_exist hL o Ω S ρ p y₀ u).1 pk.g g₁
  refine ⟨g, GlobalTheory.T.thetaParameter_of_thetaParameter_mul_degree hL o Ω S ρ p y₀ u l S.N k a g hN hk ?_⟩
  exact ParTranslate.parAt_translate hL o Ω S ρ p y₀ u (S.N * k) pk _ a₁ a g₁ g hNk
    ((hf pk _).2 hpk.symm) (by rw [inv_mul_cancel_right]) hg (hpar _ hNk)

end GlobalTheory.ZH
end
