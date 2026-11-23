module

public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.casK_isSymmetric_and_inner_re_eq : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → LinearMap.IsSymmetric (CasK ε E) ∧ ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.casK_isSymmetric_and_form | exact GlobalTheory.casK_isSymmetric_and_form | (intros; apply GlobalTheory.casK_isSymmetric_and_form <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtRestrictCompare

section General

variable {X Y Y' Z Z' : Scheme.{0}} {L : LB X}

theorem gen_eq_of_pull {φ : PUnit → (Y ⟶ X)} {ε : PUnit → ℤ} (t t' : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hinj : ∀ U : Y.Opens, Function.Injective (h.app U))
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  have e := H j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hle : h ⁻¹ᵁ (LB.wchart L φ j) ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
  have key : ∀ {U : Y.Opens} {A B : Z.Opens} (h₁ : h ⁻¹ᵁ U ≤ A) (h₂ : A ≤ B)
      (h₃ : B ≤ h ⁻¹ᵁ U) (s : Γ(Y, U)ˣ),
      ((res h₁ (res h₂ (res h₃ (pullU h U s))) : Γ(Z, h ⁻¹ᵁ U)ˣ) : Γ(Z, h ⁻¹ᵁ U)) = (h.app U).hom s := by
    intro U A B h₁ h₂ h₃ s
    change (h.app U ≫ Z.presheaf.map (homOfLE h₃).op ≫ Z.presheaf.map (homOfLE h₂).op ≫
      Z.presheaf.map (homOfLE h₁).op).hom s.1 = (h.app U).hom s.1
    rw [← Functor.map_comp, ← Functor.map_comp]
    erw [Z.presheaf.map_id]
    rw [Category.comp_id]
  refine Units.ext (hinj _ ?_)
  exact (key hle _ _ _).symm.trans ((congrArg (fun u => (res hle u).1) e).trans (key hle _ _ _))

end General

variable {R : Type} [CommRing R] [IsDomain R]

section Points

variable (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))

variable {D T}

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

section OnOpen

variable {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}


theorem psiOn_unique (ψ ψ' : PsiOn D W) : ψ = ψ' := by
  have hd : IsDominant (jK R) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant (jK R) := .of_isDominant _
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  have e : ψ.psi = ψ'.psi := funext fun χ => gen_eq_of_pull _ _ (jK R ∣_ W) (Scheme.Hom.app_injective _)
    (corr_trans D.P.isLB (ψ.psi_eq χ) (corr_symm (ψ'.psi_eq χ)))
  obtain ⟨a, _, _⟩ := ψ
  obtain ⟨b, _, _⟩ := ψ'
  obtain rfl : a = b := e
  rfl

variable {ψ : PsiOn D W} {k : ℕ} {T : Over W.toScheme}

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end OnOpen

end GlobalTheory.GtRestrictCompare
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace JetGenerators

theorem exists_tangent {k A : Type} [Field k] [CommRing A] [Algebra k A] (aug : A →ₐ[k] k)
    {I : Ideal A} {n : ℕ} (hJ : (RingHom.ker aug) ^ (n + 1) = ⊥) (hI : I ≤ RingHom.ker aug)
    (hne : ¬ RingHom.ker aug ≤ I) :
    ∃ φ : A →ₐ[k] DualNumber k, (TrivSqZeroExt.fstHom k k k).comp φ = aug ∧ (∀ a ∈ I, φ a = 0) ∧
      ∃ a ∈ RingHom.ker aug, φ a ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.NotLeSqSup.main
  | exact _root_.GlobalTheory.NotLeSqSup.main
  | (apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NotLeSqSup.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NotLeSqSup.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NotLeSqSup.main ..)

theorem spMap_jetAug {k : Type} [CommRing k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G] {d : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (n : ℕ) {A : Type} [CommRing A] [Algebra k A] :
    Chart.spMap ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n)) ≫ x n = 1 := by
  have : (Algebra.ofId k A).comp (Chart.jetAug k (Fin d) n) =
      ((Algebra.ofId k A).comp (Chart.jetAug k (Fin d) 0)).comp (Chart.jetZeroR k (Fin d) n) := by
    apply Chart.jet_ext
    intro j
    rfl
  rw [this, ← Chart.spMap_comp, Category.assoc, hx.2.1 n, MonObj.comp_one]

theorem eq_one_of_basis {S : Scheme.{0}} {X : Type} [AddCommGroup X] {κ : Type}
    (b : Module.Basis κ ℤ X) {Z : Over S} (y : Z ⟶ splitTorus S X)
    (h : ∀ j, y.left.appTop.hom (charUnit S X (b j)).val = 1) : y = 1 := by
  obtain ⟨e, he⟩ := exists_splitTorus_points_mulEquiv S X Z
  apply e.injective
  rw [map_one]
  have h1 : (MonoidHom.toAdditiveRight (e y)).toIntLinearMap = 0 := by
    apply b.ext
    intro j
    change Additive.ofMul (e y (Multiplicative.ofAdd (b j))) = Additive.ofMul 1
    congr 1
    exact Units.ext ((he y (b j)).trans (h j))
  refine MonoidHom.ext fun χ => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun h1 χ.toAdd)

end JetGenerators

theorem ker_jetAug_eq_span_torus_union_quotient :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] (r : ℕ) (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G), IsMonHom q → IsMonHom i → IsPullback i (toUnit _) q η[B] → ∀ (d g n : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin d) m) ⟶ G) (xB : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin g) m) ⟶ B), Chart.IsUnivChart G d x → Chart.IsUnivChart B g xB → ∀ (ψ : (Chart.JetR k (Fin g) n) →ₐ[k] (Chart.JetR k (Fin d) n)), x n ≫ q = Chart.spMap ψ ≫ xB n → ∀ T : Fin r → (Chart.JetR k (Fin d) n), (∀ j, Chart.jetAug k (Fin d) n (T j) = 0) → (∀ (φ : (Chart.JetR k (Fin d) n) →ₐ[k] DualNumber k) (y : Chart.sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j, (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) = y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) → RingHom.ker (Chart.jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) := by
  intro k _ X _ r b G B _ _ q i hq hi hpb d g n x xB hx hxB ψ hψ T hT hchar
  have hI : Ideal.span (Set.range T ∪ Set.range fun l => ψ (Chart.zR n l)) ≤
      RingHom.ker (Chart.jetAug k (Fin d) n) := by
    rw [Ideal.span_le]
    rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hT j
    · have hz : IsNilpotent (Chart.zR (R := k) n l) := ⟨n + 1, by
        have := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := k) n l) (n + 1)
        rwa [Chart.ker_jetAug_pow, Ideal.mem_bot] at this⟩
      exact ((hz.map ψ).map (Chart.jetAug k (Fin d) n)).eq_zero
  refine le_antisymm ?_ hI
  by_contra hne
  obtain ⟨φ, hφ1, hφ2, a, haJ, ha⟩ :=
    JetGenerators.exists_tangent _ (Chart.ker_jetAug_pow (R := k) (Fin d) n) hI hne
  have hn : n ≠ 0 := by
    rintro rfl
    have : RingHom.ker (Chart.jetAug k (Fin d) 0) = ⊥ :=
      (pow_one _).symm.trans (Chart.ker_jetAug_pow (R := k) (Fin d) 0)
    exact hne (this ▸ bot_le)
  have hφψ : φ.comp ψ = (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin g) n) := by
    apply Chart.jet_ext
    intro l
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero]
    exact hφ2 _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩))
  have hq1 : (Chart.spMap φ ≫ x n) ≫ q = toUnit _ ≫ η[B] := by
    rw [Category.assoc, hψ, ← Category.assoc, Chart.spMap_comp, hφψ, JetGenerators.spMap_jetAug hxB]
    rfl
  have hy := (hpb.lift_fst _ _ hq1).symm
  have hy1 : hpb.lift _ _ hq1 = 1 := by
    apply JetGenerators.eq_one_of_basis b
    intro j
    rw [← hchar φ _ hy j, hφ2 _ (Ideal.subset_span (Or.inl ⟨j, rfl⟩)), add_zero, map_one]
  rw [hy1, MonObj.one_comp] at hy
  have hker : (RingHom.ker (TrivSqZeroExt.fstHom k k k)) ^ (n + 1) = ⊥ := by
    rw [← le_bot_iff]
    refine (Ideal.pow_le_pow_right (show 2 ≤ n + 1 by omega)).trans ?_
    rw [pow_two, Ideal.mul_le]
    intro u hu v hv
    have hu' : u.fst = 0 := hu
    have hv' : v.fst = 0 := hv
    rw [Ideal.mem_bot]
    ext <;> simp [hu', hv']
  have huniq := (hx.2.2 (DualNumber k) (TrivSqZeroExt.fstHom k k k) n hker 1
    (MonObj.comp_one _)).unique (y₁ := φ)
    (y₂ := (Algebra.ofId k (DualNumber k)).comp (Chart.jetAug k (Fin d) n)) ⟨hφ1, hy.symm⟩
    ⟨by ext1 z; simp, (JetGenerators.spMap_jetAug hx n).symm⟩
  apply ha
  have h0 : Chart.jetAug k (Fin d) n a = 0 := haJ
  rw [huniq, AlgHom.comp_apply, h0, map_zero]

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace GmPoints

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem unitOf_val (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf w : R) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (w.left.appTop.hom (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1)).val) := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Spec (CommRingCat.of R)).presheaf.map (𝟙 (Opposite.op ⊤))).hom
      (w.left.appTop.hom (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1)).val)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem evalOne_bijective {M : Type} [Group M] :
    Function.Bijective (fun f : Multiplicative (ULift.{0} ℤ) →* M =>
      f (Multiplicative.ofAdd (ULift.up 1))) := by
  have h : ∀ n : ℤ, (Multiplicative.ofAdd (ULift.up n) : Multiplicative (ULift.{0} ℤ)) =
      (Multiplicative.ofAdd (ULift.up 1)) ^ n := by
    intro n
    rw [← ofAdd_zsmul]
    congr 1
    ext
    simp
  constructor
  · intro f g hfg
    ext ⟨n⟩
    have := h n
    change f (Multiplicative.ofAdd (ULift.up n)) = g (Multiplicative.ofAdd (ULift.up n))
    rw [this, map_zpow, map_zpow]
    exact congrArg (· ^ n) hfg
  · intro m
    exact ⟨{ toFun := fun x => m ^ x.toAdd.down
             map_one' := zpow_zero m
             map_mul' := fun x y => zpow_add m _ _ }, zpow_one m⟩

theorem unitOf_eq (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf w = Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R) w
        (Multiplicative.ofAdd (ULift.up 1))) := by
  ext
  rw [unitOf_val, ← splitTorusPointsEquiv_val]
  rfl

theorem unitOf_bijective :
    Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) := by
  rw [funext (unitOf_eq (O := O) (R := R))]
  exact (Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv).bijective.comp
    (evalOne_bijective.comp
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)).bijective)

theorem unitOf_mul (w w' : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf (w * w') = unitOf w * unitOf w' := by
  rw [unitOf_eq, unitOf_eq, unitOf_eq]
  refine Eq.trans ?_ (map_mul _ _ _)
  congr 1
  exact DFunLike.congr_fun (map_mul
    (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)) w w') _

theorem unitOf_ptMap {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R')
    (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) := by
  rw [unitOf_val, unitOf_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of R' => g.hom _)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))

end GmPoints

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem exists_primitive_idempotent_map_eq_one {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by
  let S : Set (Ideal A) := {I | ∃ e : A, e * e = e ∧ φ e = 1 ∧ I = Ideal.span {1 - e}}
  have hS : S.Nonempty := ⟨_, 1, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, hφe, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian A A)) S hS
  have key : ∀ f : A, f * f = f → f * e = f → φ f = 1 → f = e := by
    intro f hf hfe hφf
    have hle : Ideal.span {1 - e} ≤ Ideal.span {1 - f} := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨1 - e, by linear_combination hfe⟩
    have heq : Ideal.span {1 - e} = Ideal.span {1 - f} := by
      by_contra hne
      exact hmax _ ⟨f, hf, hφf, rfl⟩ (lt_of_le_of_ne hle hne)
    have hmem : 1 - f ∈ Ideal.span {1 - e} := heq ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    linear_combination e * hc - hfe + c * he
  refine ⟨e, he, ?_, ?_, hφe⟩
  · rintro rfl
    simp at hφe
  · intro f hf hfe
    have hid : IsIdempotentElem (φ f) := by
      change φ f * φ f = φ f
      rw [← map_mul, hf]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h
    · left
      have := key (e - f) (by linear_combination he + hf - 2 * hfe)
        (by linear_combination he - hfe) (by rw [map_sub, h, hφe, sub_zero])
      linear_combination -this
    · exact Or.inr (key f hf hfe h)

theorem exists_placeU_mem_emb (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] OE) :=
    IsNoetherianRing.of_finite ℤ_[p] _
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_primitive_idempotent_map_eq_one
    (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (p := p) σ).toRingHom
  exact ⟨⟨e, h1, h2, h3⟩, h4⟩

end GlobalTheory
end
