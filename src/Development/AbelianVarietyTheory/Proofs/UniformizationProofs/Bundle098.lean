module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.NondegGen

theorem card_hom_lattice (X U : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] :
    Nat.card (Multiplicative X →* U) = Nat.card U ^ Module.finrank ℤ X := by
  have e1 : (Multiplicative X →* U) ≃ (X →ₗ[ℤ] Additive U) :=
    (MonoidHom.toAdditiveRight).trans (addMonoidHomLequivInt ℤ).toEquiv
  have e2 := ((Module.finBasis ℤ X).constr ℤ (M' := Additive U)).toEquiv
  rw [Nat.card_congr (e1.trans e2.symm), Nat.card_fun, Nat.card_congr (Additive.toMul : Additive U ≃ U)]
  simp

theorem card_roots (W F : Type) [CommRing W] [Field F] [IsAlgClosed F] (φ : W →+* F) (hφ : Function.Injective φ)
    (N : ℕ) (hN : (N : F) ≠ 0) (h : ∀ z : F, z ^ N = 1 → z ∈ φ.range) : Nat.card (rootsOfUnity N W) = N := by
  haveI : NeZero (N : F) := ⟨hN⟩
  haveI : NeZero N := ⟨fun e => hN (by simp [e])⟩
  refine Eq.trans (Nat.card_congr ?_) (HasEnoughRootsOfUnity.natCard_rootsOfUnity F N)
  refine (Equiv.ofBijective (restrictRootsOfUnity φ N) ⟨fun a b e => ?_, fun z => ?_⟩)
  · have := congrArg (fun u : rootsOfUnity N F => ((u : Fˣ) : F)) e
    simp only [restrictRootsOfUnity_coe_apply] at this
    exact Subtype.ext (Units.ext (hφ this))
  · have hz : ((z : Fˣ) : F) ^ N = 1 := (mem_rootsOfUnity' N _).1 z.2
    obtain ⟨w, hw⟩ := h _ hz
    have hw1 : w ^ N = 1 := hφ (by rw [map_pow, hw, hz, map_one])
    refine ⟨rootsOfUnity.mkOfPowEq w hw1, Subtype.ext (Units.ext ?_)⟩
    rw [restrictRootsOfUnity_coe_apply]
    exact hw

theorem card_hom_torsion (X W : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing W] (N : ℕ) :
    Nat.card (powMonoidHom N : (Multiplicative X →* Wˣ) →* _).ker =
      Nat.card (rootsOfUnity N W) ^ Module.finrank ℤ X := by
  rw [← card_hom_lattice]
  refine Nat.card_congr ⟨fun c => c.1.codRestrict _ fun x => ?_, fun c => ⟨(rootsOfUnity N W).subtype.comp c, ?_⟩,
    fun c => rfl, fun c => rfl⟩
  · exact DFunLike.congr_fun (MonoidHom.mem_ker.1 c.2) x
  · exact MonoidHom.mem_ker.2 (MonoidHom.ext fun x => (c x).2)

theorem card_torsion_ext {GW BF C : Type} [CommGroup GW] [Group BF] [CommGroup C] (N : ℕ) (τ : GW →* BF)
    (j : C →* GW) (hj : Function.Injective j) (hker : ∀ y, τ y = 1 ↔ ∃ c, y = j c)
    (hs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x) :
    Nat.card (powMonoidHom N : GW →* GW).ker =
      Nat.card (powMonoidHom N : C →* C).ker * Nat.card {x : BF // x ^ N = 1} := by
  let f := τ.comp (powMonoidHom N : GW →* GW).ker.subtype
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card (powMonoidHom N : GW →* GW).ker := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [← h1]
  congr 1
  · symm
    refine Nat.card_congr (Equiv.ofBijective (fun c => ⟨⟨j c.1, ?_⟩, (hker _).2 ⟨c.1, rfl⟩⟩) ⟨fun a b e => ?_, fun y => ?_⟩)
    · show j c.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg j c.2).trans (map_one j)
    · exact Subtype.ext (hj (congrArg (fun u => u.1.1) e))
    · obtain ⟨c, hc⟩ := (hker y.1.1).1 y.2
      refine ⟨⟨c, hj ?_⟩, Subtype.ext (Subtype.ext hc.symm)⟩
      show j (c ^ N) = _
      rw [map_pow, ← hc, map_one]
      exact y.1.2
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨?_, fun hx => ?_⟩)
    · rintro ⟨y, rfl⟩
      show τ y.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg τ y.2).trans (map_one τ)
    · obtain ⟨y, hy, e⟩ := hs x hx
      exact ⟨⟨y, hy⟩, e⟩

theorem eq_one_of_cubWeil_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    {c : CubicalStr G L} {N : ℕ} {T : Over S} {y : T ⟶ G} {ζ} (h : CubWeil c N 1 y ζ) : ζ = 1 := by
  have h2 := (GlobalTheory.UU.cubWeil_basic S G L c N T).2.1 1 1 y ζ ζ h h
  rw [_root_.mul_one] at h2
  exact mul_eq_left.1 (h2.unique h)

end GlobalTheory.UU.NondegGen


open GlobalTheory.UU.NondegGen in
theorem GlobalTheory.UU.cubWeil_nondegenerate_generic :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ a.B, y ^ N = 1 → CubWeil a.M.c N x y 1) → x = 1 := by
  intro hcard hL V _ _ _ A G _ _ s t a F _ _ _ _ N hN x hx horth
  obtain ⟨W, _, _, _, φ, hφ, hcomp, hW, hloc, hroots, hlift⟩ := GlobalTheory.T.torsion_lift_abelianPart_finite_extension hcard V A G s t a F N hN
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero F := charZero_of_injective_ringHom
    (f := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI := s.semi.separated
  haveI := a.isAb.proper
  let SW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let σ : TF (R := V) F ⟶ SW := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp])
  choose ρf hρ hρu using fun y : SW ⟶ G => GlobalTheory.T.existsUnique_abelianPart_image_adicComplete_point V A G s t a W hW hloc y
  let ρ : (SW ⟶ G) →* (SW ⟶ a.B) := MonoidHom.mk' ρf fun y y' =>
    (hρu _ _ ((GlobalTheory.T.abelianPart_image_one_mul_inv V A G s t a W y y' (ρf y) (ρf y')).2 (hρ y) (hρ y')).1).symm
  obtain ⟨ι', hι, hιs⟩ := GlobalTheory.T.exists_formalTorus_points_semiAbelian_model V A G s t W hW hloc
  let pG : (SW ⟶ G) →* (TF (R := V) F ⟶ G) := preHom σ
  let pB : (SW ⟶ a.B) →* (TF (R := V) F ⟶ a.B) := preHom σ
  have hpG : Function.Injective pG := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ G W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  have hpB : Function.Injective pB := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ a.B W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  let τ := pB.comp ρ
  have hker : ∀ y, τ y = 1 ↔ ∃ c, y = ι' c := fun y => by
    have e1 : τ y = 1 ↔ ρ y = 1 := map_eq_one_iff pB hpB
    have e2 := GlobalTheory.T.abelianPart_image_eq_one_iff_torus_point V A G s t a W hW hloc y
    rw [e1]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := e2.1 (by have := hρ y; rw [show ρf y = 1 from h] at this; exact this)
      exact ⟨c, (hιs y c).2 hc⟩
    · rintro ⟨c, hc⟩
      exact (hρu y 1 (e2.2 ⟨c, (hιs y c).1 hc⟩)).symm
  have hs : ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x := fun x hx => by
    obtain ⟨y, b, hy, hb, e⟩ := hlift x hx
    refine ⟨y, hy, ?_⟩
    have : ρ y = b := (hρu y b hb).symm
    show pB (ρ y) = x
    rw [this]
    exact Over.OverMorphism.ext e
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim V a.B a.isAb
  have hdim := (GlobalTheory.T.dim_eq_abelianPart_dim_add_torus_rank V A G s t g').2 a hg'
  have hB : Nat.card {x : TF (R := V) F ⟶ a.B // x ^ N = 1} = N ^ (2 * g') :=
    GlobalTheory.card_torsion_geometricPoint_of_field hcard _ a.B a.isAb g' hg' F _ N hNF
  have hC := card_hom_torsion s.X W N
  rw [card_roots W F φ hφ N hNF hroots] at hC
  have hH := card_torsion_ext N τ ι' hι hker hs
  rw [hC, hB] at hH
  have hρN : ∀ y : SW ⟶ G, y ^ N = 1 → ρ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]

  have hpair : ∀ y y' : SW ⟶ G, y ^ N = 1 → y' ^ N = 1 → CubWeil a.M.c N (τ y) (τ y') 1 →
      CubWeil s.P.c N (pG y) (pG y') 1 := fun y y' hy hy' h => by
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have h1 := (GlobalTheory.T.cubicalWeilPairing_eq_abelianPart_image V A G s t a W hW hloc N y y' (ρ y) (ρ y') ζ (hρ y) (hρ y') (hρN y hy) (hρN y' hy') hζ).comp σ
    have h2 := hζ.comp σ
    rw [h1.unique h] at h2
    exact h2
  have hτN : ∀ y : SW ⟶ G, y ^ N = 1 → τ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨y, hy, rfl⟩ := hs x hx
  have hmem := GlobalTheory.UU.mem_of_cubWeil_orthogonal hL V A G s F N hN
    ((powMonoidHom N : (Multiplicative s.X →* Wˣ) →* _).ker.map (pG.comp ι'))
    ((powMonoidHom N : (SW ⟶ G) →* _).ker.map pG) ?_ ?_ ?_ ?_ (pG y) (by rw [← map_pow, hy, map_one]) ?_
  · obtain ⟨c, -, hc⟩ := hmem
    exact (hker y).2 ⟨c, (hpG hc).symm⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rw [Subgroup.card_map_of_injective (f := pG.comp ι') (hpG.comp hι), Subgroup.card_map_of_injective hpG, hH, hC, hdim]
    ring
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨y', hy', rfl⟩
    have hcN : ι' c ^ N = 1 := by
      rw [← map_pow]
      exact (congrArg _ hc).trans (map_one _)
    refine hpair (ι' c) y' hcN hy' ?_
    rw [(hker _).2 ⟨c, rfl⟩]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil a.M.c (one_pow N) (hτN y' hy')
    rwa [eq_one_of_cubWeil_one hζ] at hζ
  · rintro _ ⟨y', hy', rfl⟩
    exact hpair y y' hy hy' (horth _ (hτN y' hy'))
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.OneDim

theorem gs_zero {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

def zeroSec {Y : Scheme.{0}} (M : LB Y) : LB.Sec M :=
  ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem expF_zero (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) :
    U.ExpF F k (zeroSec _) (fun _ => zeroSec _) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_, ?_⟩
  · intro Z rA y rG _ _ z JA JG _ _
    rw [Fin.sum_univ_zero]
    exact (congrArg (_ * ·) (gs_zero _ _ _)).trans (mul_zero _)
  · intro α Z rF rB _ z J _
    rw [Fin.sum_univ_zero]
    exact gs_zero _ _ _

theorem appTop_injective (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Injective (toUnit (TF (R := R) F)).left.appTop.hom := by
  have e₂ : (toUnit (TF (R := R) F)).left =
      Spec.map (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    have a := Over.w (toUnit (TF (R := R) F))
    exact ((Category.comp_id _).symm.trans a).trans (Spec.map_comp _ _).symm
  rw [e₂]
  have n := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))
  have i : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
      CommRingCat.ofHom ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))).hom :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))).comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  rw [← n] at i
  exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom) i

theorem eq_zero_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h : U.PullG F (toUnit _) k σ t) (ht : ∀ j, t.f j = 0) (j) : σ.f j = 0 := by
  have hs : Smooth G.hom := U.semi.smooth
  have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (TF (R := R) F).left := inferInstanceAs (IsAffine (Spec _))
  refine GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero _ G (𝟙_ _) (TF (R := R) F) (toUnit _) (appTop_injective F)
    _ U.P.L.L U.P.L.isLB _ _ _ σ (fun z J hJ => ?_) j
  have w : (snd (TF (R := R) F) G).left ≫ G.hom =
      ((fst (TF (R := R) F) G).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (snd (TF (R := R) F) G)).trans ((Over.w (fst (TF (R := R) F) G)).symm.trans (Category.assoc _ _ _).symm)
  let y : (TF (R := R) F ⊗ G).left ⟶ ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w
  have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have w' : (fst (TF (R := R) F) G).left ≫ jFK (R := R) F = (y ≫ U.gen.hom.left) ≫ A.A.hom := by
    rw [Category.assoc, e₄]
    exact (pullback.lift_snd _ _ _).symm
  let rA : (TF (R := R) F ⊗ G).left ⟶ (TFK (R := R) F ⊗ A.A).left := pullback.lift _ _ w'
  obtain ⟨JA, hJA⟩ := exists_good_pt A.isLB z
  refine (h _ rA y (toUnit (TF (R := R) F) ▷ G).left (pullback.lift_snd _ _ _) ?_ ?_ z JA J hJA hJ).symm.trans ?_
  · exact (congrArg CommaMorphism.left (whiskerRight_snd (toUnit (TF (R := R) F)) G)).trans
      (pullback.lift_fst _ _ w).symm
  · refine (congrArg CommaMorphism.left (whiskerRight_fst (toUnit (TF (R := R) F)) G)).trans ?_
    rw [← Category.assoc]
    exact congrArg (· ≫ (toUnit (TF (R := R) F)).left) (pullback.lift_fst _ _ w').symm
  · exact (congrArg (_ * ·) ((congrArg (gs rA z _) (ht _)).trans (gs_zero _ _ _))).trans (mul_zero _)

end

theorem exists_smul_of_finrank_one {F B M : Type} [Field F] [CommRing B] [AddCommGroup M] [Module B M]
    (e : F ≃+* B) (h : Module.finrank B M = 1) {v : M} (hv : v ≠ 0) (w : M) : ∃ c : F, e c • v = w := by
  letI : Field B := (e.symm.toMulEquiv.isField (Field.toIsField F)).toField
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := B) v hv).1 h w
  exact ⟨e.symm c, by rw [e.apply_symm_apply]; exact hc⟩

theorem expF_one_dim : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → (∃ j, th.f j ≠ 0) ∧ U.ExpF (Kbar V) 1 th s₀ ∧ ∀ t s, U.ExpF (Kbar V) 1 t s → ∃ c : (Kbar V), ∀ α j, (s α).f j = DegPre.constBF D (Kbar V) c _ * (s₀ α).f j) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hG hB
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hn
    obtain ⟨j, hj⟩ := hθ.2
    exact hj (eq_zero_of_pullG U (Kbar V) 1 θ th hG (fun j => by_contra fun h => hn ⟨j, h⟩) j)
  have hE := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 1 θ f th s₀ hθ.1 hG hB
  refine ⟨hne, hE, fun t s hts => ?_⟩
  obtain ⟨-, -, hr, -⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) 1
    (by rw [Nat.cast_one]; exact one_ne_zero)
  rw [one_pow] at hr
  have hv : SecM.ofSec A.A th ≠ 0 := fun h => by
    obtain ⟨j, hj⟩ := hne
    exact hj (congrFun (congrArg Subtype.val h) j)
  obtain ⟨c, hc⟩ := exists_smul_of_finrank_one
    (Scheme.ΓSpecIso (CommRingCat.of (Kbar V))).symm.commRingCatIsoToRingEquiv hr hv (SecM.ofSec A.A t)
  let s' : Raw D (Kbar V) 1 := fun α =>
    ⟨fun j => DegPre.constBF D (Kbar V) c _ * (s₀ α).f j, fun i j => by
      rw [map_mul, map_mul, (s₀ α).compat i j, mul_left_comm]
      congr 2
      exact fn_ext fun x hx => (gs_res _ x _ hx _).trans ((gs_res _ x _ hx.1 _).trans
        ((gs_res _ x _ hx _).trans (gs_res _ x _ hx.2 _)).symm)⟩
  have hs' : U.ExpF (Kbar V) 1 t s' :=
    GlobalTheory.UU.ExpLin.expF_linear V hV D A G U (Kbar V) 1 th (zeroSec _) t s₀ (fun _ => zeroSec _) s' c hE
      (expF_zero U _ 1) (fun j => ((congrFun (congrArg Subtype.val hc) j).symm).trans (add_zero _).symm)
      (fun α j => (add_zero _).symm)
  have e : s = s' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U (Kbar V) 1 t t s s' hts hs').1 rfl
  exact ⟨c, fun α j => by rw [e]⟩

end GlobalTheory.UU.OneDim
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.card_torsion_points_abelianVariety : GlobalFnsSt → RigiditySt → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) := by
  first | exact @GlobalTheory.UU.TorsionCount.card_torsion_points | exact GlobalTheory.UU.TorsionCount.card_torsion_points | (intros; apply GlobalTheory.UU.TorsionCount.card_torsion_points <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = 0 := by
  refine (gs_eq r z _ (hJ.mem φ r) _).trans ?_
  exact (congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → ∀ (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k), (∀ jj, s.f jj = 0) → U.Expands k s F → F = 0 := by
  intro R _ _ I D A G _ _ U k hR s F hs hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  obtain ⟨r, hr, σ, f, h₁, hf, hE⟩ := hE
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hσ : ∀ j, σ.f j = 0 := fun j => by
    refine ExpInt.generic_app_injective G _ (Eq.trans (fn_ext fun y hy => ?_) (map_zero _).symm)
    obtain ⟨J, hJ, e⟩ := exists_good U.LG.L U.LG.isLB y
      (fun _ : Unit => (𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hy 0)
    have ej : ∀ a : Fin 1, J ((𝟙 _ ≫ pullback.fst G.hom (jK R)) ≫ 𝟙 G.left) = j a := fun a => by
      rw [Subsingleton.elim a 0]; exact e ()
    have e₂ := ExpInt.secScal_sval h₁ (𝟙 _) y hJ
    rw [sval_eq_zero hs _ y hJ, mul_zero, sval_of σ _ y J j ej] at e₂
    refine ((gs_pull (𝟙 _) _ y _ hy _).trans e₂).trans ((gs_eq _ y _ hy _).trans ?_).symm
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  have hf0 : ∀ α j, (f α).f j = 0 := fun α => by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ f (fun j => ?_) (hE e) α j)
    exact (congrArg _ (hσ j)).trans (map_zero _)
  refine fam_ext fun α j => ?_
  refine sec_ext_val D.toPre.P.isLB (s' := SecOps.secZero) (fun y J hJ => ?_) j
  have e₁ := ExpInt.secScal_sval (hf α) (𝟙 _) y hJ
  rw [sval_eq_zero (hf0 α) _ y hJ, ExpInt.gs_scal] at e₁
  have e₃ : 𝟙 _ ≫ (DegPre.BF D.toPre (FractionRing R)).hom =
      ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm
  rw [e₃] at e₁
  refine Eq.trans ?_ (sval_eq_zero (fun _ => rfl) _ y hJ).symm
  exact (IsUnit.mul_right_eq_zero (ExpInt.isUnit_cst _ y hr)).1 e₁.symm

end GlobalTheory.ExpZero
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisation_degenerationData_unique : GlobalFnsSt → SecBaseChangeSt → AmpleSt → UnifUniqSt := by
  first | exact @GlobalTheory.unifUniq | exact GlobalTheory.unifUniq | (intros; apply GlobalTheory.unifUniq <;> assumption)
end
