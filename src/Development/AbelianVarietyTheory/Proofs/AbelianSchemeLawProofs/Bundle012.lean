module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThickeningDetermines

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace

variable {X Y : Scheme.{0}} {N : LB X}

theorem exists_mem_chart (hN : N.IsLB) (x : X) : ∃ i, x ∈ N.U i :=
  Opens.mem_iSup.1 (hN.cover.ge (Set.mem_univ x))

theorem associated_germ_sec (s : N.Sec) (i j : N.ι) (x : X) (hi : x ∈ N.U i) (hj : x ∈ N.U j) :
    Associated ((X.presheaf.germ _ x hi).hom (s.f i)) ((X.presheaf.germ _ x hj).hom (s.f j)) := by
  have hm : x ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  have h0 : Associated (resG X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i))
      (resG X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j)) :=
    (congrArg (Associated · _) (s.compat i j)).mpr
      (associated_unit_mul_left _ _ (N.g i j).isUnit)
  have := h0.map (X.presheaf.germ _ x hm).hom
  rwa [germ_resG, germ_resG] at this

noncomputable def secIdeal (hN : N.IsLB) (s : N.Sec) : X.IdealSheafData :=
  locIdeal N.U s.f (exists_mem_chart hN) (associated_germ_sec s)

theorem secIdeal_le_ker (hN : N.IsLB) (s : N.Sec) (φ : Y ⟶ X) [QuasiCompact φ]
    (h : ∀ j, (φ.app _).hom (s.f j) = 0) : secIdeal hN s ≤ φ.ker := by
  have loc : ∀ x : X, ∃ (W : X.affineOpens) (i : N.ι), x ∈ W.1 ∧ W.1 ≤ N.U i := fun x ↦ by
    obtain ⟨i, hi⟩ := exists_mem_chart hN x
    obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
    exact ⟨W, i, hxW, hW⟩
  choose W i hx hW using loc
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩) fun x ↦ ?_
  refine (ideal_locIdeal _ _ _ _ (W x) (i x) (hW x)).trans_le ?_
  rw [Ideal.span_singleton_le_iff_mem, Scheme.Hom.ker_apply, RingHom.mem_ker, app_resG, h,
    map_zero]

theorem eq_zero_of_secIdeal_eq_bot (hN : N.IsLB) (s : N.Sec) (h : secIdeal hN s = ⊥) (j : N.ι) :
    s.f j = 0 := by
  refine X.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  refine ⟨W.1, hW, hxW, ?_⟩
  have h1 := ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW
  have h2 : (secIdeal hN s).ideal W = ⊥ := by rw [h]; rfl
  have h3 := Ideal.span_singleton_eq_bot.1 (h1.symm.trans h2)
  exact h3.trans (map_zero _).symm

end ThickeningDetermines


open ThickeningDetermines in
theorem sec_eq_zero_and_hom_eq_of_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom], (∀ (N : LB H.left), N.IsLB → ∀ s : LB.Sec N, (∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) → ∀ j, s.f j = 0) ∧ (∀ (Y : Over (Spec (CommRingCat.of R))) [IsSeparated Y.hom] (f g : H ⟶ Y), (∀ n : ℕ, (fstG I n H).left ≫ f.left = (fstG I n H).left ≫ g.left) → f = g) := by
  intro R _ _ I hI H _ _ _
  have := grpObj_geometricallyIntegral_of_smooth _ H
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H η[H] (fun p ↦ inferInstance)
  refine ⟨fun N hN s hs ↦ eq_zero_of_secIdeal_eq_bot hN s ?_, fun Y _ f g h ↦ ?_⟩
  · have := key _ (secIdeal hN s).subschemeι fun n ↦ by
      have : IsClosedImmersion (thick R I n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I n H).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
      exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
    rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
    exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this
  · have := key _ (equalizer.ι f g).left fun n ↦
      ⟨(equalizer.lift (fstG I n H) (Over.OverMorphism.ext (h n))).left,
        by rw [← Over.comp_left, equalizer.lift_ι]⟩
    refine Over.OverMorphism.ext ?_
    rw [← cancel_epi (equalizer.ι f g).left]
    exact congrArg CommaMorphism.left (equalizer.condition f g)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtendRig

theorem isRegularRing_of_isLocalization {B : Type} [CommRing B] [IsRegularRing B]
    (M : Submonoid B) (R : Type) [CommRing R] [Algebra B R] [IsLocalization M R] :
    IsRegularRing R := by
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing M R inferInstance
  rw [isRegularRing_iff]
  intro q hq
  have h : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap B R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap B R)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap B R))) (Localization.AtPrime q)).toRingEquiv

theorem isRegularRing_of_isDiscreteValuationRing (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] : IsRegularRing V :=
  have : IsDedekindDomain V := IsPrincipalIdealRing.isDedekindDomain V
  inferInstance

theorem isLocalization_away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

theorem isOpenImmersion_etaK (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] :
    IsOpenImmersion (etaK V K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away_of_irreducible V K hπ
  exact IsOpenImmersion.of_isLocalization π

theorem isRegularRing_stalk
    (hreg : ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B]
      [Algebra.Smooth V B], IsRegularRing B)
    (V : Type) [CommRing V] [IsRegularRing V] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V))
    [Smooth f] (x : X) : IsRegularRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have : IsRegularRing Γ(Spec (CommRingCat.of V), ⊤) :=
    IsRegularRing.of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U le_top).hom]
  have : IsRegularRing Γ(X, U) := hreg Γ(Spec (CommRingCat.of V), ⊤) Γ(X, U)
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact isRegularRing_of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _

theorem extend_exists :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B], IsRegularRing B) → (∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R], UniqueFactorizationMonoid R) → (∀ (X Y : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X), IsOpenImmersion j → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ ∃ φ : LB.Iso (L'.pull j) L, φ.IsGen) → Semi.extend_existsSt.{0} := by
  intro hint hreg hufd hext V _ _ _ K _ _ _ G _ _ _ _ _ _ eA _ L hL _ _
  have hV : IsRegularRing V := isRegularRing_of_isDiscreteValuationRing V
  have : GeometricallyIntegral G.hom := hint _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := isOpenImmersion_etaK V K
  have hj : IsOpenImmersion (jA V K G) := inferInstance
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := isRegularRing_stalk hreg V G.hom x
    hufd _
  obtain ⟨L', hL', φ, hφ⟩ := hext G.left _ (jA V K G) hj hst L hL
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := V) L' hL' (K := PUnit)
    (fun _ => eSec G) (fun _ => 1)
  exact ⟨⟨L', e, hL', he⟩, φ, hφ⟩

end GlobalTheory.ExtendRig
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isGen_pull {X Y : Scheme.{0}} (M : LB X) (v : LB.Gen M) (hv : v.IsGen) (f : Y ⟶ X) :
    ∃ c : LB.Gen (M.pull f), c.IsGen := by
  have le : ∀ J : PUnit → M.ι, (M.pull f).U J ≤ f ⁻¹ᵁ M.U (J PUnit.unit) := fun J y hy => mem_pull.1 hy
  refine ⟨⟨fun J => res (le J) (pullU f _ (v.s (J PUnit.unit)))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J : PUnit → M.ι, y ∈ (M.pull f).U J →
      gm (𝟙 Y) y _ (res (le J) (pullU f _ (v.s (J PUnit.unit)))) =
        gm (𝟙 Y ≫ f) y _ (v.s (J PUnit.unit)) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gm (𝟙 Y ≫ f) y _) (hv (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))

theorem exists_isGen_of_invariant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y'))
    (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = m ≫ φ k)
    (u : LB.Gen (LB.LinComb L φ' ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (t i) y J = val u (𝟙 Y') y J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen := by
  obtain rfl : φ' = fun k => m ≫ φ k := funext hφ
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have le : ∀ j : K → L.ι, m ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => m ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j)ˣ, pullU m _ b = res (le j) (u.s j) := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ LB.wchart L φ j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    refine (gm_res (t i) y (le j) (e hy) _).trans (Eq.trans ?_ (gm_res (𝟙 Y') y (le j) hy _).symm)
    refine (gen_trans hu (t i) y (le j (e hy)) (hJ'.mem _ _)).trans
      (Eq.trans ?_ (gen_trans hu (𝟙 Y') y (le j hy) (hJ'.mem _ _)).symm)
    refine congrArg₂ (· * ·) ?_ (hinv i y J hJ')
    have e3 : ∀ k, t i ≫ m ≫ φ k = 𝟙 Y' ≫ m ≫ φ k := fun k => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X => gm ψ y (L.U (j k) ⊓ L.U (J ψ)) (L.g (j k) (J ψ)) ^ ε k) (e3 k)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j : K → L.ι, y ∈ m ⁻¹ᵁ LB.wchart L φ j →
      gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (u.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans ((congrArg _ (hb j)).trans (gm_res (𝟙 Y') y (le j) hj _))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans
    ((gen_trans hu (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_linComb L φ ε (𝟙 Y' ≫ m) y i j hy.1 hy.2).trans ?_) ((gm_res _ y _ hy _).trans (val j hy.2)))
  simp only [trF, Category.assoc]

theorem weilNondeg_of_descent :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε)))) → WeilNondegSt := by
  intro hG hC K _ _ P k hk x hx hy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, ε, hu, -, hcorr⟩ := hC K P k x hx
  let B := baseOver (Spec (CommRingCat.of K))
  let β : P.A ⟶ B := Over.homMk P.A.hom (Category.comp_id _)
  have hβ : ∀ {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ B), a = b := fun a b =>
    Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w a)).trans
      ((Category.comp_id _).symm.trans (Over.w b)).symm)
  let σ : P.A ⟶ B ⊗ P.A := lift β (𝟙 _)
  have hσ : snd B P.A ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ]
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ P.A), y ≫ mulA P.A k = y ^ k :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have h0 : σ ≫ mulT P.A B k = mulA P.A k ≫ σ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ, mulT, mulA, MonObj.comp_pow]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(σ ≫ translPt P.A x).left, 𝟙 _] ![1, -1] (mulA P.A k).left
    (I := {y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A // y ^ k = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul, mulA])
    (fun U f hf => hG K P k hk U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change (σ ≫ mulT P.A B k ≫ translPt P.A x).left = (mulA P.A k ≫ σ ≫ translPt P.A x).left
        rw [reassoc_of% h0]
      · change (σ ≫ snd B P.A ^ k).left = (mulA P.A k ≫ 𝟙 _).left
        simp [σ, mulA, MonObj.comp_pow])
    (LB.pullGen P.L _ _ u σ.left) (DVR.pullGen_isGen _ _ _ u hu _)
    (fun y z J hJ => by
      have hy' : (toUnit B ≫ y.1) ^ k = 1 := by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      have h1 := val_corr hJ (hcorr _ 1 hy' (hy _ hy')) σ.left
      have h2 : ((toUnit P.A ≫ y.1) * 𝟙 P.A) ≫ σ = σ ≫ translT P.A (toUnit B ≫ y.1) := by
        apply CartesianMonoidalCategory.hom_ext
        · exact hβ _ _
        · clear hG hC hcorr h1
          simp only [σ, translT, translPt, Hom.mul_def, Category.assoc, lift_snd, Category.comp_id,
            comp_lift_assoc, lift_fst_assoc, comp_toUnit_assoc]
      rw [val_pull hJ, val_mul hJ, one_zpow] at h1
      rw [val_pull hJ, val_pull hJ, Category.id_comp, ← Over.comp_left, h2]
      refine h1.trans ?_
      refine mul_eq_left.2 ?_
      exact (congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
  have h3 : (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) =
      ![(translPt P.A x).left, (snd B P.A).left] := by
    funext i
    fin_cases i
    · change (snd B P.A ≫ σ ≫ translPt P.A x).left = (translPt P.A x).left
      rw [reassoc_of% hσ]
    · exact Category.comp_id _
  have h4 : ∃ w : LB.Gen (LB.LinComb P.L
      (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
  rw [h3] at h4
  obtain ⟨w, hw⟩ := h4
  exact exists_isGen_pull (translDiff P.A P.L x) w hw _

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem globalFns_holds : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

theorem rigidity_holds : RigiditySt :=
  rigidity_of_local_rigidity globalFns_holds local_rigidity

theorem lemmaB_holds : Semi.lemmaBSt.{0} :=
  sec_eq_zero_of_dvd_pow_uniformiser
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B], IsAbelianScheme B → ∀ (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∃ (O : X → RigLB B) (h₁ : _) (h₂ : _) (h₃ : _), ∀ hB : IsAbelianScheme B, ∃ d : (SplitExt.mk B hB X O h₁ h₂ h₃).GtDatum G, d.q = q ∧ d.i = i := by
  first | exact @GlobalTheory.exists_gtDatum_of_splitTorus_extension | exact GlobalTheory.exists_gtDatum_of_splitTorus_extension | (intros; apply GlobalTheory.exists_gtDatum_of_splitTorus_extension <;> assumption)
end
