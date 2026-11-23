module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TwoPlaces

theorem exists_deep_one_sub :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A A' : ValuationSubring Ω)
      (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → IsPlaceOver (F := E) A' P → A ≠ A' →
      ∀ c : Ω, IsIntegral ℤ c → c ≠ 0 →
        ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ A'.valuation (1 - e) < 1 := by
  intro E Ω _ _ _ _ _ A A' P hA hA' hne c hc hc0
  have hQ : (primeBelow (F := E) A).under (𝓞 E) = P.asIdeal := under_primeBelow hA
  have hQ' : (primeBelow (F := E) A').under (𝓞 E) = P.asIdeal := under_primeBelow hA'
  haveI : (primeBelow (F := E) A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A)).IsMaximal; rw [hQ]; exact P.isMaximal)
  haveI : (primeBelow (F := E) A').IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 E) _
      (by change (Ideal.under (𝓞 E) (primeBelow (F := E) A')).IsMaximal; rw [hQ']; exact P.isMaximal)
  have hQne : primeBelow (F := E) A ≠ primeBelow (F := E) A' := by
    intro h
    apply hne
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    have hb' : IsIntegral (𝓞 E) b := hb.tower_top
    have := congrArg (fun I : Ideal (IntCl E Ω) => (⟨b, hb'⟩ : IntCl E Ω) ∈ I) h
    simpa [mem_primeBelow] using this
  have hnle : ¬ primeBelow (F := E) A ≤ primeBelow (F := E) A' := fun h =>
    hQne (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) h)
  obtain ⟨x, hxQ, hxQ'⟩ := SetLike.not_le_iff_exists.mp hnle
  rw [mem_primeBelow] at hxQ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place E Ω A P hA (x : Ω) c (isIntegral_int_of_isIntegral x.2) hc hc0 hxQ
  have hxk : x ^ k ∉ primeBelow (F := E) A' := fun h => hxQ' (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv inferInstance hxk
  refine ⟨((y * x ^ k : IntCl E Ω) : Ω), isIntegral_int_of_isIntegral (y * x ^ k).2, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, Valuation.map_mul, SubmonoidClass.coe_pow, Valuation.map_pow]
    calc A.valuation (y : Ω) * A.valuation (x : Ω) ^ k ≤ 1 * A.valuation (x : Ω) ^ k :=
          mul_le_mul_left (valuation_le_one_intCl A y) _
      _ < A.valuation c := by rw [one_mul]; exact hk
  · have e1 : (1 : Ω) - ((y * x ^ k : IntCl E Ω) : Ω) = (i : Ω) := by
      have := congrArg (fun z : IntCl E Ω => (z : Ω)) hyi
      simp only [AddMemClass.coe_add, OneMemClass.coe_one] at this
      rw [← this]; ring
    rw [e1]
    exact hi

end GlobalTheory.TwoPlaces
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeightCounting.ToClC

theorem norm_le_one_of_mem_OL (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥(Loc.OL K)) :
    ‖((x : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := by
  have h : IsIntegral ℤ_[l] ((x : ↥K.1) : PadicAlgCl l) :=
    (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).2 x.2
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] _).coeff n).2

theorem mem_clC_of_OL (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (y : ↥(Loc.OL K₀)) :
    algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ clC l (Kt l K₀ L) := by
  refine ⟨Subring.le_topologicalClosure _ ⟨((y : ↥K₀.1) : PadicAlgCl l), ?_, rfl⟩, ?_⟩
  · show ((y : ↥K₀.1) : PadicAlgCl l) ∈ Kt l K₀ L
    exact (le_sup_left.trans (le_sup_left : K₀.1 ⊔ L.1 ≤ _)) (y : ↥K₀.1).2
  · change algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ PadicComplexInt l
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, ← PadicComplex.coe_eq, PadicComplex.valuation_extends, ← NNReal.coe_le_one, PadicAlgCl.valuation_coe]
    exact norm_le_one_of_mem_OL l K₀ y

def toClC (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)) :=
  ((algebraMap (PadicAlgCl l) ℂ_[l]).comp (K₀.1.val.toRingHom.comp (Loc.OL K₀).val.toRingHom)).codRestrict _
    fun y => mem_clC_of_OL l K₀ L y

theorem exists_toClC : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l), ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)),
    ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) :=
  fun l _ K₀ L => ⟨toClC l K₀ L, fun _ => rfl⟩

end GlobalTheory.HeightCounting.ToClC
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_square_generator_through_squareIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  first | exact @GlobalTheory.SqLB.exists_sq_gen | exact GlobalTheory.SqLB.exists_sq_gen | (intros; apply GlobalTheory.SqLB.exists_sq_gen <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqSym

open GlobalTheory.SqLevel

variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]

theorem sq_chart_le (L : LB X) (φ : K → (Y ⟶ X)) (j : K → Fin 1 → L.ι) :
    LB.wchart (sqLB L) φ j ≤ LB.wchart L φ (fun k => j k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => mem_sq.1 (Set.mem_iInter.1 hy k)

def sqGen (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb (sqLB L) φ ε) :=
  ⟨fun j => res (sq_chart_le L φ j) (t.s (fun k => j k 0)) ^ 2⟩

theorem gm_sqGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (j : K → Fin 1 → L.ι) (h : r z ∈ LB.wchart (sqLB L) φ j) :
    gm r z _ ((sqGen L φ ε t).s j) = gm r z _ (t.s (fun k => j k 0)) ^ 2 := by
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ h _))

theorem sqGen_isGen {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) : (sqGen L φ ε t).IsGen := by
  intro (i : K → Fin 1 → L.ι) (j : K → Fin 1 → L.ι)
  apply unit_ext
  intro y hy
  have hi := sq_chart_le L φ i hy.1
  have hj := sq_chart_le L φ j hy.2
  rw [gm_res (𝟙 _) y _ hy, map_mul, gm_res (𝟙 _) y _ hy, gm_sqGen t (𝟙 Y) y i hy.1, gm_sqGen t (𝟙 Y) y j hy.2]
  refine (congrArg (· ^ 2) (gen_trans ht (𝟙 _) y hi hj)).trans ?_
  refine (mul_pow _ _ 2).trans (congrArg (· * _) ?_)
  refine Eq.trans ?_ (gm_linComb (sqLB L) φ ε (𝟙 _) y i j hy.1 hy.2).symm
  rw [trF, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g L (𝟙 _ ≫ φ k) y (i k) (j k) (by simpa using Set.mem_iInter.1 hi k)
    (by simpa using Set.mem_iInter.1 hj k), ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem val_sqGen {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {z : Z}
    {J : (Z ⟶ X) → Fin 1 → L.ι} (hJ : Good (sqLB L) z J) (r : Z ⟶ Y) :
    val (sqGen L φ ε t) r z J = val t r z (fun ψ => J ψ 0) ^ 2 :=
  gm_sqGen t r z _ (hJ.mem φ r)

theorem good_of_sq {L : LB X} {z : Z} {J : (Z ⟶ X) → Fin 1 → L.ι} (hJ : Good (sqLB L) z J) :
    Good L z (fun ψ => J ψ 0) := fun ψ => mem_sq.1 (hJ ψ)

end GlobalTheory.SqSym

namespace GlobalTheory


open RigidIsoCube SqSym SqLevel in
theorem sq_iso_respects_symmetry_pointwise : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2 := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL hw Z r z N N' hN hN'
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have hL : (sqLB U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have hL' : (sqLB U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  have pg := isoPullId_pgen hw (rfl : 𝟙 G.left = 𝟙 G.left)
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have key := pmaps_of_section pg hL hL' (φ' := ![(ι[G]).left, 𝟙 G.left]) (φ := ![(ι[G]).left, 𝟙 G.left])
    (ε := ![1, -1]) (sqGen _ _ _ U'.symG) (sqGen_isGen U'.LG.isLB U'.symG_gen) (sqGen _ _ _ U.symG)
    (sqGen_isGen U.LG.isLB U.symG_gen) (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁
    fun y J J' hJ hJ' => by
      have a := val_corr (good_of_sq hJ) U.symG_rig (𝟙 _)
      rw [val_pull (good_of_sq hJ), val_one, Category.id_comp] at a
      have b := val_corr (good_of_sq hJ') U'.symG_rig (𝟙 _)
      rw [val_pull (good_of_sq hJ'), val_one, Category.id_comp] at b
      rw [val_sqGen _ hJ, val_sqGen _ hJ', a, b, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, oi, Category.comp_id]
      simp
  set φ : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left] with hφ
  have m1 : ∀ k, (r ≫ φ k) z ∈ (sqLB U.LG.L).U (fun _ => N (r ≫ φ k)) := fun k => mem_sq.2 (hN _)
  have m2 : ∀ k, (r ≫ φ k) z ∈ (sqLB U'.LG.L).U (fun _ => N' (r ≫ φ k)) := fun k => mem_sq.2 (hN' _)
  have e := key Z r z (fun k _ => N (r ≫ φ k)) (fun k _ => N' (r ≫ φ k)) (fun k => by simpa using m1 k)
    (fun k => by simpa using m2 k)
  have h1 : (r ≫ 𝟙 G.left) z ∈ LB.wchart (sqLB U.LG.L) φ (fun k _ => N (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => by simpa using m1 k
  have h2 : r z ∈ LB.wchart (sqLB U'.LG.L) φ (fun k _ => N' (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => by simpa using m2 k
  have e1 := gm_sqGen U.symG (r ≫ 𝟙 G.left) z _ h1
  have e2 := gm_sqGen U'.symG r z _ h2
  simp only [Category.comp_id] at e1 e
  exact e1.symm.trans (e.trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun k _ => by rw [gw_isoPullId wL rfl _ z _ _ (m1 k) (m2 k)]) e2))
end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

variable {X Y : Scheme.{0}} {K : Type} [Fintype K]

theorem sqGen_le (L₀ : LB X) (φ : K → (Y ⟶ X)) (j : K → Fin 1 → L₀.ι) :
    LB.wchart (sqLB L₀) φ j ≤ LB.wchart L₀ φ (fun k => j k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => mem_sq.1 (Set.mem_iInter.1 hy k)

def sqGen {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε)) :
    LB.Gen (LB.LinComb (sqLB L₀) φ ε) :=
  ⟨fun j => res (sqGen_le L₀ φ j) (t.s (fun k => j k 0)) ^ 2⟩

theorem gm_sqGen {Z : Scheme.{0}} {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε))
    (r : Z ⟶ Y) (z : Z) (j : K → Fin 1 → L₀.ι) (hj : r z ∈ LB.wchart (sqLB L₀) φ j) :
    gm r z _ ((sqGen t).s j) = gm r z _ (t.s (fun k => j k 0)) ^ 2 :=
  (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hj _))

theorem sqGen_isGen {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L₀ φ ε)} (ht : t.IsGen) :
    (sqGen t).IsGen := by
  intro j j'
  apply unit_ext
  intro x hx
  have hj := sqGen_le L₀ φ j hx.1
  have hj' := sqGen_le L₀ φ j' hx.2
  have hm : (𝟙 Y) x ∈ (LB.LinComb L₀ φ ε).U (fun k => j k 0) ⊓ (LB.LinComb L₀ φ ε).U (fun k => j' k 0) := ⟨hj, hj'⟩
  have e := congrArg (gm (𝟙 Y) x _) (ht (fun k => j k 0) (fun k => j' k 0))
  rw [gm_res (𝟙 Y) x _ hm, map_mul, gm_res (𝟙 Y) x _ hm] at e
  erw [gm_linComb L₀ φ ε (𝟙 Y) x _ _ hj hj'] at e
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx, gm_sqGen t (𝟙 Y) x j hx.1, gm_sqGen t (𝟙 Y) x j' hx.2]
  erw [gm_linComb (sqLB L₀) φ ε (𝟙 Y) x j j' hx.1 hx.2]
  rw [e, mul_pow]
  congr 1
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  have a₁ : (𝟙 Y ≫ φ k) x ∈ L₀.U (j k 0) := Set.mem_iInter.1 hj k
  have a₂ : (𝟙 Y ≫ φ k) x ∈ L₀.U (j' k 0) := Set.mem_iInter.1 hj' k
  rw [gm_sq_g L₀ (𝟙 Y ≫ φ k) x (j k) (j' k) a₁ a₂, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem val_sqGen {Z : Scheme.{0}} {L₀ : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L₀ φ ε))
    {z : Z} {J : (Z ⟶ X) → Fin 1 → L₀.ι} (hJ : Good (sqLB L₀) z J) (r : Z ⟶ Y) :
    val (sqGen t) r z J = val t r z (fun ψ => J ψ 0) ^ 2 :=
  gm_sqGen t r z _ (hJ.mem φ r)

theorem good_sq {Z : Scheme.{0}} {L₀ : LB X} {z : Z} {J : (Z ⟶ X) → Fin 1 → L₀.ι} (hJ : Good (sqLB L₀) z J) :
    Good L₀ z (fun ψ => J ψ 0) :=
  fun ψ => mem_sq.1 (hJ ψ)

end GlobalTheory.SqLevel

namespace GlobalTheory


open RigidIsoCube SqLevel in
theorem sq_iso_carries_sq_cube : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2 := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL hw Z r z N N' hN hN'
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have hL := DVR.linComb_isLB U.LG.L U.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2)
  have hL' := DVR.linComb_isLB U'.LG.L U'.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2)
  have pg : PGen (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)) := isoPullId_pgen hw rfl
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have PM := pmaps_of_section pg hL hL' (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
    (sqGen U'.cubG.t) (sqGen_isGen U'.cubG.isGen) (sqGen U.cubG.t) (sqGen_isGen U.cubG.isGen)
    (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => by
      refine (val_sqGen _ hJ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_sqGen _ hJ' _)).symm)
      have c₁ : val U.cubG.t e.left y (fun ψ => J ψ 0) = 1 := (isCub_cubV U.cubG (good_sq hJ)).face 1 1
      have c₂ : val U'.cubG.t e.left y (fun ψ => J' ψ 0) = 1 := (isCub_cubV U'.cubG (good_sq hJ')).face 1 1
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
        (fun q => gw (isoPullId wL (rfl : 𝟙 G.left = 𝟙 G.left)) q y (J (q ≫ 𝟙 _)) (J' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg (· ^ 2) c₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) p (congrArg (· ^ 2) c₂)).symm)
      simp
  have hp : ∀ k, (r ≫ thφ G (x3 G) k) z ∈ (sqLB U.LG.L).U (fun _ => N (r ≫ thφ G (x3 G) k)) :=
    fun k => mem_sq.2 (hN _)
  have hq : ∀ k, (r ≫ thφ G (x3 G) k) z ∈ (sqLB U'.LG.L).U (fun _ => N' (r ≫ thφ G (x3 G) k)) :=
    fun k => mem_sq.2 (hN' _)
  have v := PM Z r z (fun k _ => N (r ≫ thφ G (x3 G) k)) (fun k _ => N' (r ≫ thφ G (x3 G) k)) hp hq
  rw [Category.comp_id] at v
  refine (gm_sqGen U.cubG.t r z (fun k _ => N (r ≫ thφ G (x3 G) k)) (Set.mem_iInter.2 hp)).symm.trans
    (v.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_)
      (gm_sqGen U'.cubG.t r z (fun k _ => N' (r ≫ thφ G (x3 G) k)) (Set.mem_iInter.2 hq))))
  exact congrArg (· ^ thε k) (gw_isoPullId wL rfl _ z _ _ (hp k) (hq k))

end GlobalTheory
end
end
