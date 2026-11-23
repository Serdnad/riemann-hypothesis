module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingRotBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGenPoint

theorem valR_constFn {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (p : X ⟶ Sp B) (x : Sp A ⟶ X)
    (χ : B →+* A) (hx : x ≫ p = spMap χ) (a : B) : valR x ⊤ (constFn p ⊤ a) = χ a := by
  have h : ⊤ ≤ x ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold constFn
  refine (GlobalTheory.ZH.CrdMove.valR_appLE x p ⊤ ⊤ _ h _).trans ?_
  rw [hx]
  have h' : ⊤ ≤ (spMap χ) ⁻¹ᵁ (⊤ : (Sp B).Opens) := fun _ _ => trivial
  rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h']
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a)) n
  refine Eq.trans ?_ (this.trans (congrArg χ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv_hom_id_apply a)))
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.UnifGenPoint


open GlobalTheory.UnifGenPoint in
theorem GlobalTheory.UnifGenPoint.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) ∧ ξ ≫ P.A.A.hom = spMap ψ ∧ ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' ∧ ∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0 := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx _ _ _ hinj g _ δL _

  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun r hr => ?_
    have h1 : valR x' ⊤ (constFn t.G.hom ⊤ r) = 0 := (valR_constFn t.G.hom x' φ hx r).trans hr
    have h2 := hinj ⊤ (constFn t.G.hom ⊤ r) (fun _ _ => trivial) h1
    have h3 := valR_constFn t.G.hom (eSec t.G) (RingHom.id R) (by
      rw [eSec, Over.w]; simp [spMap]) r
    rw [h2, GlobalTheory.ZH.CrdCalc.valR_eq (eSec t.G) ⊤ (fun _ _ => trivial), map_zero] at h3
    exact h3.symm

  set L := FractionRing Ω
  have hinjL : Function.Injective ((algebraMap Ω L).comp φ) :=
    (IsFractionRing.injective Ω L).comp hφ
  let ψ : FractionRing R →+* L := IsFractionRing.lift (K := FractionRing R) hinjL
  have hψ : ∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω L (φ r) := fun r => by
    simp [ψ, IsFractionRing.lift_algebraMap]
  let u : Sp L ⟶ t.G.left := spMap (algebraMap Ω L) ≫ x'
  have hu : u ≫ t.G.hom = spMap ψ ≫ jK R := by
    simp only [u, Category.assoc, hx, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => (hψ r).symm
  let ξ₀ : Sp L ⟶ pullback t.G.hom (jK R) := pullback.lift u (spMap ψ) hu
  let ξ : Sp L ⟶ P.A.A.left := ξ₀ ≫ P.U.gen.hom.left
  have n₁ : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id, Over.id_left]
  have hξ1 : ξ ≫ P.A.A.hom = spMap ψ := by
    simp only [ξ, Category.assoc, Over.w]
    exact pullback.lift_snd _ _ _
  have hξ2 : ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = u := by
    simp only [ξ, Category.assoc]
    rw [← Category.assoc P.U.gen.hom.left, n₁, Category.id_comp]
    exact pullback.lift_fst _ _ _
  refine ⟨ψ, ξ, hψ, hξ1, hξ2, ?_⟩

  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyConnected t.G.hom := t.semi.geomConnected
  haveI : IrreducibleSpace t.G.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R t.G inferInstance inferInstance
      ⟨x' (IsLocalRing.closedPoint Ω)⟩
  set q := u (IsLocalRing.closedPoint L) with hq
  have hqg : q = genericPoint t.G.left := by
    have h1 : q ⤳ genericPoint t.G.left := by
      refine specializes_iff_forall_open.2 fun s hs hgs => ?_
      obtain ⟨V, hVa, hpV, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⊤) (x := x' (IsLocalRing.closedPoint Ω)) trivial
      have hV : ⊤ ≤ x' ⁻¹ᵁ V := (GlobalTheory.ZH.CrdCalc.top_le_iff x' V).2 hpV
      have hgV : genericPoint t.G.left ∈ V :=
        ((genericPoint_spec t.G.left).mem_open_set_iff V.isOpen).2 ⟨_, trivial, hpV⟩
      let W : t.G.left.Opens := V ⊓ ⟨s, hs⟩
      obtain ⟨b, hbW, hgb⟩ := hVa.exists_basicOpen_le (V := W) ⟨genericPoint t.G.left, hgV, hgs⟩ hgV
      have hb : b ≠ 0 := by
        rintro rfl
        rw [Scheme.basicOpen_zero] at hgb
        exact hgb
      have hv : valR x' V b ≠ 0 := fun h => hb (hinj V b hV h)
      obtain ⟨hV', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap Ω L) x' V hV
      have hu : IsUnit (valR u V b) := by
        rw [hval]
        exact (Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective Ω L)).2 hv))
      have := ((GlobalTheory.ZH.CrdCalc.isUnit_valR_iff u V hV' b).1 hu) (Set.mem_univ (IsLocalRing.closedPoint L))
      exact (hbW this).2
    exact (h1.antisymm (genericPoint_specializes q)).eq

  haveI : Smooth P.A.A.hom := P.A.isAb.smooth
  haveI : GeometricallyConnected P.A.A.hom := P.A.isAb.geomConnected
  haveI : IrreducibleSpace P.A.A.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain (FractionRing R) P.A.A inferInstance
      inferInstance ⟨ξ (IsLocalRing.closedPoint L)⟩
  haveI : IsIntegral P.A.A.left := GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace P.A.A.hom
  set y := ξ (IsLocalRing.closedPoint L) with hy
  let mm : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)
  haveI : IsIso P.U.gen.inv.left := ⟨⟨P.U.gen.hom.left, by
    rw [← Over.comp_left, P.U.gen.inv_hom_id, Over.id_left], n₁⟩⟩
  haveI : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  haveI : IsPreimmersion (pullback.fst t.G.hom (jK R)) := MorphismProperty.of_isPullback (IsPullback.of_hasPullback t.G.hom (jK R)).flip inferInstance
  haveI : IsPreimmersion mm := inferInstance
  have hmy : mm y = q := by
    rw [hq, ← hξ2]
    rfl
  have hyg : y = genericPoint P.A.A.left := by
    apply (Scheme.Hom.isEmbedding mm).injective
    have h1 : mm (genericPoint P.A.A.left) ⤳ mm y :=
      (genericPoint_specializes y).map (Scheme.Hom.continuous mm)
    rw [hmy, hqg] at h1 ⊢
    exact ((genericPoint_specializes _).antisymm h1).eq
  intro O f hO hf
  by_contra hne
  have hne' : P.A.A.left.basicOpen f ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff f).1 h)
  have hgen : genericPoint P.A.A.left ∈ P.A.A.left.basicOpen f := by
    refine ((genericPoint_spec P.A.A.left).mem_open_set_iff (P.A.A.left.basicOpen f).isOpen).2 ?_
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne'
    exact ⟨z, trivial, hz⟩
  have hu : IsUnit (valR ξ O f) :=
    (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ O hO f).2
      ((GlobalTheory.ZH.CrdCalc.top_le_iff ξ _).2 (by rw [← hy, hyg]; exact hgen))
  exact hu.ne_zero hf
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.invariantVectorField_constFn_eq_zero : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (r : R), dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.IsInv.apply_constFn | exact GlobalTheory.Heat.IsInv.apply_constFn | (intros; apply GlobalTheory.Heat.IsInv.apply_constFn <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem Heat.acts_const_at_points : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}} (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (v : Fin n → TanM (𝟙 (Sp R)) G) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat G m L dd ⇑D) (k : ℕ) (a b : R) (ρ τ ρ' τ' : SecM m L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ r z J) → h.Acts k ρ ρ' → h.Acts k τ τ' → ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J → gs r z ⊤ (scal G.hom a) * sval ρ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D a)) * sval ρ r z J = gs r z ⊤ (scal G.hom b) * sval τ' r z J + gs r z ⊤ (scal G.hom (2 * (k : R) * D b)) * sval τ r z J := by
  intro R _ G _ _ n X m L hL v dd hinv D h k a b ρ τ ρ' τ' hpt hρ hτ

  have cTop : ∀ c : R, constFn G.hom ⊤ c = scal G.hom c := fun c => by
    simp only [constFn, Out.scal, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have gsR : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) {O O₀ : G.left.Opens} (hle : O ≤ O₀) (hz : r z ∈ O)
      (s : Γ(G.left, O₀)), gs r z O (rsT s O) = gs r z O₀ s := fun r z _ _ hle hz s => by
    rw [GlobalTheory.KS.rsT_of_le hle]; exact gs_res r z hle hz s
  have gsC : ∀ {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z) (O : G.left.Opens) (hz : r z ∈ O) (c : R),
      gs r z O (constFn G.hom O c) = gs r z ⊤ (scal G.hom c) := fun r z O hz c => by
    rw [← GlobalTheory.KS.rsT_constFn G.hom (le_top : O ≤ ⊤) c, gsR r z le_top hz, cTop]
  have cMul : ∀ (O : G.left.Opens) (c : R),
      constFn G.hom O (2 * (k : R) * c) = 2 * (k : Γ(G.left, O)) * constFn G.hom O c := fun O c => by
    simp [constFn, map_mul, map_natCast, map_ofNat]
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => Glue.le_wchart _ (h.le i)

  have leib : ∀ i (c : R) (F : Γ(G.left, h.W i)),
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) F +
          constFn G.hom (h.W i) (2 * (k : R) * D c) * F := by
    intro i c F
    have hd := (h.lift i).1.2.1 (h.W i) le_rfl (constFn G.hom (h.W i) c) F
    have hdc := (h.lift i).2 (h.W i) le_rfl c
    have hdd : ∀ a' (f : Γ(G.left, h.W i)), dd a' (h.W i) (constFn G.hom (h.W i) c * f) =
        constFn G.hom (h.W i) c * dd a' (h.W i) f := fun a' f => by
      rw [(hinv a').1.2.1 (h.W i) le_top, IsInv.apply_constFn G (v a') (dd a') (hinv a'), mul_zero, add_zero]
    have hs : ∀ (f : Γ(G.left, h.W i)),
        ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) (constFn G.hom (h.W i) c * f)) =
          constFn G.hom (h.W i) c * ∑ a', ∑ b', constFn G.hom (h.W i) (h.Θ a' b') * dd a' (h.W i) (dd b' (h.W i) f) := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hdd, hdd]; ring
    have hs' : ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) (constFn G.hom (h.W i) c * F) =
        constFn G.hom (h.W i) c * ∑ a', constFn G.hom (h.W i) (h.u a') * dd a' (h.W i) F := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hdd]; ring
    simp only [op]
    rw [hs, hs', hd, hdc, cMul]
    ring

  have onW : ∀ i, constFn G.hom (h.W i) a * rsT (ρ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D a) * rsT (ρ.f fun _ => h.j i) (h.W i) =
      constFn G.hom (h.W i) b * rsT (τ'.f fun _ => h.j i) (h.W i) +
      constFn G.hom (h.W i) (2 * (k : R) * D b) * rsT (τ.f fun _ => h.j i) (h.W i) := by
    intro i
    have hA : constFn G.hom (h.W i) a * rsT (ρ.f fun _ => h.j i) (h.W i) =
        constFn G.hom (h.W i) b * rsT (τ.f fun _ => h.j i) (h.W i) := by
      refine fn_ext fun x hx => ?_
      obtain ⟨J, hJ, e⟩ := exists_good L hL x (fun _ : Fin 1 => m) (fun _ => h.j i) (fun _ _ _ => rfl)
        (fun _ => h.le i hx)
      have hp := hpt G.left (𝟙 _) x J hJ
      have s1 : ∀ σ : SecM m L k, sval σ (𝟙 G.left) x J = gs (𝟙 G.left) x (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) :=
        fun σ => by
          rw [sval_of σ (𝟙 G.left) x J (fun _ => h.j i) (fun q => by rw [Category.id_comp]; exact e q)]
          exact (gsR (𝟙 G.left) x (hWc i) hx _).symm
      rw [s1, s1] at hp
      rw [gs_mul _ x _ hx, gs_mul _ x _ hx, gsC _ x _ hx, gsC _ x _ hx]
      exact hp
    rw [hρ i, hτ i, ← leib, ← leib, hA]

  intro Z r z J hJ
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := by
    have : r z ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have hz1 := hJ.mem (fun _ : Fin 1 => m) r
  have hz2 : r z ∈ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := hWc i hi
  have sv : ∀ σ : SecM m L k, sval σ r z J =
      (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (σ.f fun _ => h.j i) (h.W i)) := fun σ => by
    exact (sec_trans σ r z hz1 hz2).trans (congrArg _ (gsR r z (hWc i) hi _).symm)
  have E := congrArg (gs r z (h.W i)) (onW i)
  simp only [gs_add r z _ hi, gs_mul r z _ hi, gsC r z _ hi] at E
  rw [sv ρ, sv τ, sv ρ', sv τ']
  linear_combination (trF (fun _ : Fin 1 => m) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ m)) (fun _ => h.j i)).val * E

end GlobalTheory.Heat
end
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def IsEigTan {K : Type} [CommRing K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (τ : E →+* ℂ)
    (w : Sp (DualNumber K) ⟶ Z.t.G.left) : Prop :=
  IsTanAtG Z.t x w ∧ ∀ a : 𝓞 E, w ≫ (Z.t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w


omit [NumberField E] [IsCMField E] in
def trCo {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U U' : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f)
    (f' : Fin r → Γ(M, U')) (b a : Fin r) : Γ(X, U ⊓ U') :=
  (hf.basis inf_le_left).repr (Twist.resM M inf_le_right (f' a)) b

abbrev FrAssign {X W : Scheme.{0}} (M : X.Modules) (r : ℕ) (jB : W ⟶ X) : Type 1 :=
  ∀ (U : X.Opens) (f : Fin r → Γ(M, U)), VB.IsFrame f → ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W),
    ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)


end Free

end GlobalTheory.ArLieBase

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.ImageHeightNonneg

theorem IsImageHeight.neg_log_le {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d n : ℕ} {w : Fin n → V} {abelian₂ h : ℝ} (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : Submodule.span (𝓞 K) (Set.range w) = L) (hle : ∀ i σ, Nm σ (w i) ≤ abelian₂) (hh : IsImageHeight Nm L ev d h) :
    0 ≤ h + Real.log abelian₂ := by
  obtain ⟨N, n', b, w', A, δ, f, hF, hf, e⟩ := hh
  have hF' : IsFrame Nm L b (Matrix.of fun j k => b.repr (w k) j) A := by
    refine ⟨?_, ?_, hF.herm, hF.conj, hF.norm⟩
    · simp only [Matrix.of_apply, Module.Basis.sum_repr]; exact hw
    · have h1 : Submodule.span K (Set.range w) = ⊤ := by rw [← hs, ← hw, Submodule.span_span_of_tower]
      have h2 := congrArg (Submodule.map b.equivFun.toLinearMap) h1
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
      exact h2
  have h1 := GlobalTheory.ImageHeightUnique.formHeight_linSubst hF hF' δ f
  rw [Module.Basis.toMatrix_self, GlobalTheory.HeightUnique.linSubst_one] at h1
  obtain ⟨y, hy, -⟩ := hf.exists_point
  obtain ⟨j, -⟩ := Function.ne_iff.1 hy
  have h2 := GlobalTheory.FormHtLower.formHeight_ge (Λ := abelian₂) (Fin.pos j) hF'.full hF'.herm
    (fun k σ => (hF.norm σ (w k)).trans_le (hle k σ)) hf.ne_zero hf.homog
  rw [h1, ← e] at h2
  have hpos : (0 : ℝ) < ((d : ℝ) + 1) * δ := mul_pos (by positivity) (Nat.cast_pos.2 hf.pos)
  refine nonneg_of_mul_nonneg_right (a := ((d : ℝ) + 1) * δ) ?_ hpos
  push_cast at h2
  linarith

theorem imageHeight_add_log_nonneg (K V Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (d n : ℕ) (w : Fin n → V) (abelian₂ : ℝ) (hG : HasGram Nm)
    (hc : ∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) (hs : Submodule.span K (L : Set V) = ⊤)
    (hw : IsShortGen Nm L w abelian₂) (hd : 0 < imageDeg ev d) : 0 ≤ imageHeight Nm L ev d + Real.log abelian₂ := by
  have hL : Submodule.span (𝓞 K) (Set.range w) = L :=
    le_antisymm (Submodule.span_le.2 fun x hx => (hw.gen x).2 (Submodule.subset_span hx))
      fun x hx => Submodule.span_le_restrictScalars ℤ (𝓞 K) _ ((hw.gen x).1 hx)
  have hK : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ := fun σ h =>
    IsTotallyComplex.complexEmbedding_not_isReal σ h
  exact IsImageHeight.neg_log_le hs hL hw.le (isImageHeight_imageHeight (exists_isImageHeight_iff.2
    ⟨exists_isFrame hK hc hG (hL ▸ Submodule.fg_span (Set.finite_range _)) hs, hd⟩))

end GlobalTheory.ImageHeightNonneg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom ∧ GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.ModelRelDim.relDim_and_isVB_omega | exact GlobalTheory.ModelRelDim.relDim_and_isVB_omega | (intros; apply GlobalTheory.ModelRelDim.relDim_and_isVB_omega <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  first | exact @GlobalTheory.primCris_isBC_of_nilThick | exact GlobalTheory.primCris_isBC_of_nilThick | (intros; apply GlobalTheory.primCris_isBC_of_nilThick <;> assumption)
end
