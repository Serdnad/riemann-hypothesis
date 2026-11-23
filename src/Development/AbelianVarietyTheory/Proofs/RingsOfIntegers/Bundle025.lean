module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoOfIsClosedImmersionOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GermDiv

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ThickeningDetermines

theorem dvd_of_app_eq_zero {R : Type} [CommRing R] (r : R) {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hf : ((pullback.fst p (spMap (Ideal.Quotient.mk (Ideal.span {r})))).app U).hom f = 0) :
    constFn p U r ∣ f := by
  have h := ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (Ideal.span {r})))) hU f hf
  have hk : RingHom.ker (spMap (Ideal.Quotient.mk (Ideal.span {r}))).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r} := by
    intro x hx
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    have e := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r}))))
    have h0 : Ideal.Quotient.mk (Ideal.span {r}) a = 0 :=
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {r}))).inv).1
        ((e.trans hx).trans (map_zero _).symm)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    exact Ideal.mem_span_singleton.2 (map_dvd (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h0)
  have h' := Ideal.map_mono hk h
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h'
  exact h'

theorem cst_zero {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, gs_eq q z ⊤ trivial, map_zero, map_zero, map_zero]

theorem app_eq_zero_of_dvd {R : Type} [CommRing R] (r : R) {X Y Z : Scheme.{0}} (p : X ⟶ Sp R)
    (a : Y ⟶ X) (m : Z ⟶ Y) (t : Z ⟶ Sp (R ⧸ Ideal.span {r}))
    (ht : m ≫ a ≫ p = t ≫ spMap (Ideal.Quotient.mk (Ideal.span {r})))
    (U : X.Opens) (f : Γ(X, U)) (h : ∀ y : Y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) :
    ((m ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz => ?_
  have hz' : a (m z) ∈ U := hz
  have e1 : gs (𝟙 Z) z ((m ≫ a) ⁻¹ᵁ U) (((m ≫ a).app U).hom f) = gs (m ≫ a) z U f :=
    (gs_pull (𝟙 Z) (m ≫ a) z U hz f).trans (by rw [Category.id_comp])
  have e2 : gs (m ≫ a) z U f = (m.stalkMap z).hom (gs a (m z) U f) := by
    rw [← gs_pull m a z U hz', gs_stalkMap m z _ hz', gs_pull (𝟙 Y) a (m z) U hz', Category.id_comp]
  have e3 : (m.stalkMap z).hom (cst (a ≫ p) (m z) r) = 0 := by
    rw [H1.cst_stalkMap, ht, cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r), cst_zero]
  obtain ⟨c, hc⟩ := h _ hz'
  rw [e1, e2, hc, map_mul, e3, zero_mul, gs_eq (𝟙 Z) z _ hz, map_zero, map_zero]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (N : LB H.left), N.IsLB → ∀ (s : LB.Sec N) (r : R), r ≠ 0 → (∀ (n : ℕ) (x : (thickObj R I n H).left) (j : N.ι), (fstG I n H).left x ∈ N.U j → Geo.Tor.cst ((fstG I n H).left ≫ H.hom) x r ∣ Geo.Tor.gs (fstG I n H).left x (N.U j) (s.f j)) → ∃ s' : LB.Sec N, SecIsMul H.hom r s s' := by
  intro R _ _ _ I hI H _ _ _ N hN s r hr h
  let q := Ideal.Quotient.mk (Ideal.span {r})
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback (spMap q)).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom (spMap q)
  let I₀ := I.map q
  have hI₀ : I₀ ≤ Ideal.jacobson ⊥ := by
    refine Ideal.map_le_iff_le_comap.2 (hI.trans ?_)
    rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective]
    exact Ideal.jacobson_mono bot_le
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom (spMap q)))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom (spMap q)))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom (spMap q)))
  let κ := (secIdeal hN s).subschemeι
  have hiso := isIso_of_isClosedImmersion_of_thickenings _ I₀ hI₀ H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.fst π κ) fun n ↦ by
      have : IsClosedImmersion (thick _ I₀ n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I₀ n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ I₀ n)))
      let m : (thickObj _ I₀ n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG I₀ n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ I₀ n) ≫ spMap (Ideal.quotientMap (I₀ ^ (n + 1)) q
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))
          (by
            have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
            have e2 : (fstG I₀ n H₀).left ≫ H₀.hom =
              pullback.snd H₀.hom (thick _ I₀ n) ≫ thick _ I₀ n := pullback.condition
            rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc,
              ← Spec.map_comp, ← Spec.map_comp]
            rfl)
      have hm : m ≫ (fstG I n H).left = (fstG I₀ n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG I₀ n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j => by
        rw [← hm]
        refine app_eq_zero_of_dvd r H.hom _ m ((fstG I₀ n H₀).left ≫ H₀.hom) ?_ _ _
          fun y hy => h n y j hy
        have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
        rw [← Category.assoc, hm, Category.assoc, Category.assoc, e1]
      have hle : κ.ker ≤ ((fstG I₀ n H₀).left ≫ π).ker := by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0
      exact ⟨pullback.lift (fstG I₀ n H₀).left (IsClosedImmersion.lift κ _ hle)
        (IsClosedImmersion.lift_fac _ _ _).symm, pullback.lift_fst _ _ _⟩
  have hker : secIdeal hN s ≤ π.ker := by
    have e : π = (inv (pullback.fst π κ) ≫ pullback.snd π κ) ≫ κ := by
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [e]
    exact (Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)).ge.trans
      (Scheme.Hom.le_ker_comp _ _)
  refine exists_div_sec H.hom hr s fun j x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    H.left.isBasis_affineOpens.exists_subset_of_mem_open hx (N.U j).isOpen
  have hle : U ≤ N.U j := hUW
  have h1 := EffCartierData.ideal_locIdeal _ _ (exists_mem_chart hN)
    (associated_germ_sec s) ⟨U, hU⟩ j hle
  have h2 := Scheme.Hom.ideal_ker_le π ⟨U, hU⟩
    (hker ⟨U, hU⟩ (h1.ge (Ideal.mem_span_singleton_self _)))
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero r H.hom hU
    ((H.left.presheaf.map (homOfLE hle).op).hom (s.f j)) h2
  have hxU' : (𝟙 H.left : H.left ⟶ H.left) x ∈ U := hxU
  refine ⟨gs (𝟙 H.left) x U g, ?_⟩
  rw [← gs_res (𝟙 H.left) x hle hxU' (s.f j), hg, gs_mul _ x U hxU',
    gs_constFn H.hom U _ x hxU', Category.id_comp]

end GlobalTheory.GermDiv
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiWZeroProd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem four_comm {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (p : A' ⟶ A) [IsMonHom p] (f : A ⟶ A) (f' : A' ⟶ A') (h : f' ≫ p = p ≫ f) (k : Fin 4) :
    (![(padd A' (𝟙 _) f').left, 𝟙 A'.left, f'.left, (toUnit A' ≫ η[A']).left] : Fin 4 → _) k ≫ p.left =
      p.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) k := by
  fin_cases k
  · show (padd A' (𝟙 _) f').left ≫ p.left = p.left ≫ (padd A (𝟙 _) f).left
    rw [← Over.comp_left, ← Over.comp_left]
    unfold padd
    congr 1
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, Category.id_comp, h, ← Category.assoc, comp_lift,
      Category.comp_id]
  · show 𝟙 A'.left ≫ p.left = p.left ≫ 𝟙 A.left
    simp
  · show f'.left ≫ p.left = p.left ≫ f.left
    rw [← Over.comp_left, ← Over.comp_left, h]
  · show (toUnit A' ≫ η[A']).left ≫ p.left = p.left ≫ (toUnit A ≫ η[A]).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Category.assoc, IsMonHom.one_hom, ← Category.assoc, toUnit_unique (p ≫ toUnit A) (toUnit A')]


theorem psi_weight_zero_product (pD : IsPowDeg D' D j) {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (hx : ∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) (oa : D.OAct O) (oa' : D'.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (w0 : O) (h : TraceFormTwistIso D oa w0) :
    TraceFormTwistIso D' oa' w0 := by
  obtain ⟨u, hu, h0, hy⟩ := h
  have := oa'.onB.hom w0
  have : ∀ i, IsMonHom (pD.pw.pr i) := pD.pw.hom
  obtain ⟨u', hu', hval⟩ := exists_boxPull_gen pD.w pD.w_gen D.P.isLB D'.P.isLB
    (φ' := ![(padd D'.P.A (𝟙 _) (oa'.onB.act w0)).left, 𝟙 D'.P.A.left, (oa'.onB.act w0).left, (toUnit D'.P.A ≫ η[D'.P.A]).left])
    (φ := fun _ => ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left])
    (ε := ![1, -2, -1, 2])
    (fun i => (pD.pw.pr i).left) (fun i k => four_comm (pD.pw.pr i) _ _ (hact w0 i) k) (fun _ => u) (fun _ => hu)
  have hη : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  refine ⟨u', hu', ?_, ?_⟩
  · apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    rw [val_pull hJ', val_one]
    have e1 := hval _ (𝟙 _ ≫ eSec D'.P.A) z J J' hJ hJ'
    have e2 : ∀ i, val u ((𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left) z J = 1 := by
      intro i
      have hc : (𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ eSec D.P.A := by
        simp only [Category.id_comp, eSec, ← Over.comp_left, IsMonHom.one_hom]
      rw [hc, ← val_pull hJ, val_corr hJ h0, val_one]
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (η[D'.P.A]) (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    simp only [← hη] at e3
    rw [Finset.prod_eq_one (fun i _ => e2 i)] at e1
    simp only [Category.assoc] at e1
    have e4 : ∀ m : D'.P.A.left ⟶ D'.P.A.left, eSec D'.P.A ≫ m = (η[D'.P.A]).left ≫ m := fun m => rfl
    have h1f : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ oa'.onB.act w0 = 1 := by
      rw [hη, IsMonHom.one_hom]
    simp only [e4, ← hη, e3, h1f] at e1
    have alg : ∀ {G : Type} [CommGroup G] (a v : G), a * (a ^ 2)⁻¹ * a⁻¹ * a ^ 2 * v = v := by
      intros
      group
    have h11 : ((1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) * 1) = 1 := mul_one _
    erw [h11] at e1
    rwa [alg] at e1
  · intro y
    apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    have hD : ∀ x : D.X, val (D.psi (x + w0 • x)) (𝟙 _) z J * (val (D.psi x) (𝟙 _) z J)⁻¹ *
        (val (D.psi (w0 • x)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (𝟙 _ ≫ D.xK x) z J =
        val (D.psi x) (𝟙 _) z J * val D.rigK (𝟙 _) z J := by
      intro x
      have hc := val_corr hJ (hy x) (𝟙 _)
      simp only [DegPre.tau, val_mul hJ, val_inv, val_pull hJ] at hc
      exact hc
    rw [val_mul hJ', val_mul hJ', val_pull hJ']
    simp only [DegPre.tau, val_mul hJ', val_inv]
    have P := fun x => psi_val pD hJ hJ' x (𝟙 _)
    have Rg := rig_val pD hJ hJ' (𝟙 _)
    have U := hval _ (𝟙 _ ≫ D'.xK y) z J J' hJ hJ'
    have hpr : ∀ i, (𝟙 _ ≫ D'.xK y) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ D.xK (pD.xe y i) := by
      intro i
      simp only [Category.id_comp, DegPre.xK, ptK, ← Over.comp_left, Category.assoc, pD.c_pr]
    simp only [hpr] at U
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (toUnit (TK R) ≫ D'.c y)
      (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    have e6 : (toUnit (TK R) ≫ D'.c y) ≫ oa'.onB.act w0 = toUnit (TK R) ≫ D'.c (w0 • y) := by
      rw [Category.assoc, ← oa'.c_lin]
    have e7 : (toUnit (TK R) ≫ D'.c y) * (toUnit (TK R) ≫ D'.c (w0 • y)) = toUnit (TK R) ≫ D'.c (y + w0 • y) := by
      rw [D'.c_add]
      unfold padd
      rw [← Category.assoc, comp_lift, Hom.mul_def]
    have e8 : ∀ x, (toUnit (TK R) ≫ D'.c x).left = D'.xK x := fun _ => rfl
    have e9 : (toUnit (TK R) ≫ η[D'.P.A]).left = (toUnit (TK R)).left ≫ eSec D'.P.A := rfl
    rw [e6, e7, Hom.one_def] at e3
    simp only [e8, e9] at e3
    simp only [Category.id_comp] at P Rg U e3 hD ⊢
    rw [e3] at U
    have hxe1 : ∀ i, pD.xe (y + w0 • y) i = pD.xe y i + w0 • pD.xe y i := by
      intro i
      rw [map_add (f := _), hx]
      rfl
    have hxe2 : ∀ i, pD.xe (w0 • y) i = w0 • pD.xe y i := by
      intro i
      rw [hx]
      rfl
    have Py := inv_mul_eq_iff_eq_mul.mp (P y)
    have Ps := inv_mul_eq_iff_eq_mul.mp (P (y + w0 • y))
    have Pw := inv_mul_eq_iff_eq_mul.mp (P (w0 • y))
    have key := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => (by rw [hxe1 i, hxe2 i]; exact hD (pD.xe y i) :
      val (D.psi (pD.xe (y + w0 • y) i)) (𝟙 _) z J * (val (D.psi (pD.xe y i)) (𝟙 _) z J)⁻¹ *
        (val (D.psi (pD.xe (w0 • y) i)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (D.xK (pD.xe y i)) z J =
        val (D.psi (pD.xe y i)) (𝟙 _) z J * val D.rigK (𝟙 _) z J))
    simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
    rw [Py, Ps, Pw, eq_inv_mul_of_mul_eq Rg, eq_inv_mul_of_mul_eq U, eq_inv_mul_of_mul_eq key]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ (oa : D.OAct O) (oa' : D'.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ w0 : O, Geo.Tor.TraceFormTwistIso D oa w0 → Geo.Tor.TraceFormTwistIso D' oa' w0 := by
  intro R _ _ j D D' pD O _ _ _ _ hx oa oa' hact w0 h
  exact psi_weight_zero_product pD hx oa oa' hact w0 h

end GlobalTheory.PsiWZeroProd
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullExpInt

theorem secScal_scale {R : Type} [CommRing R] {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (p : Y ⟶ Spec (CommRingCat.of R)) {p' : Y' ⟶ Spec (CommRingCat.of R)} (hp : h ≫ p = p') (a b c : R)
    (hc : c = a * b) (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h (scal p' b)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ (SecOps.secScale (scal p a) s₂) h (scal p' c) := by
  unfold GeneratorPullback.SecScal at H ⊢
  intro j₁ j₂ hj
  have e1 : (SecOps.secScale (scal p a) s₂).f j₂ = resTop _ (scal p a) * s₂.f j₂ := rfl
  have e2 : h.appTop.hom (scal p a) = scal p' a := by
    subst hp
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [e1]
  erw [map_mul, map_mul, H j₁ j₂ hj, GlobalTheory.ExpansionLinear.app_resTop, SecOps.resTop_res]
  rw [e2, hc, GlobalTheory.ExpansionLinear.scal_mul, GlobalTheory.ExpansionLinear.resTop_mul]
  exact (_root_.mul_assoc _ _ _).symm

private theorem secIsMul_secScale_scal {R : Type} [CommRing R] {Y : Scheme.{0}} {L : LB Y}
    (p : Y ⟶ Spec (CommRingCat.of R)) (a : R) (s : LB.Sec L) :
    SecIsMul p a (SecOps.secScale (scal p a) s) s := by
  unfold SecIsMul
  intro j
  rfl

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∃ (c : V) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), c ≠ 0 ∧ GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => ((k : ℕ) : ℤ)) τ (pullback.fst t.G.hom (jK V)) (scal (pullback.snd t.G.hom (jK V) ≫ jK V) c) ∧ GeneratorPullback.SecScal P.U.LG.L (fun _ : Fin 1 => pullback.fst t.G.hom (jK V)) (fun _ => ((k * N : ℕ) : ℤ)) u (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => ((k * N : ℕ) : ℤ)) σ'' (pullback.fst t.G.hom (jK V)) (scal (pullback.snd t.G.hom (jK V) ≫ jK V) c) ∧ ∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL')) := by
  intro hG V _ _ _ E _ _ _ H t P a N ha hN X hX hXc k s F u F' hs hu hpull
  letI := H.starRing
  have hR : RosatiAdj P.D.toPre.P.A P.D.toPre.P.L (P.oD.onB.act (star a)) (P.oD.onB.act a) := by
    have h0 := P.oD.onB.2 (star a)
    rwa [star_star] at h0
  haveI := P.oD.onB.toRingAct.2 (star a)
  haveI := P.oD.onB.toRingAct.2 a
  obtain ⟨uR, huR, huR0⟩ := Geo.Tor.exists_ros hG P.D.toPre.P.isAb P.D.toPre.P.isLB
    (P.oD.onB.act (star a)) (P.oD.onB.act a) hR
  obtain ⟨r₁, hr₁, τ₁, f₁, hτ₁, hf₁, he₁⟩ := hs
  obtain ⟨r₂, hr₂, σ₂, f₂, hσ₂, hf₂, he₂⟩ := hu
  have hpB : (DegPre.prB P.D.toPre (FractionRing V)).left ≫ P.D.toPre.P.A.hom =
      (DegPre.BF P.D.toPre (FractionRing V)).hom := Over.w _
  let f : ∀ α : P.D.toPre.X, P.D.toPre.SecB k α := fun α => SecOps.secScale (scal P.D.toPre.P.A.hom r₂) (f₁ α)
  let f'' : ∀ α : P.D.toPre.X, P.D.toPre.SecB (k * N) α :=
    fun α => SecOps.secScale (scal P.D.toPre.P.A.hom r₁) (f₂ α)
  let τ : H0 P.U.LG.L k := SecOps.secScale (scal t.G.hom r₂) τ₁
  let σ'' : H0 P.U.LG.L (k * N) := SecOps.secScale (scal t.G.hom r₁) σ₂
  have hτ := secScal_scale t.G.hom pullback.condition r₂ r₁ (r₁ * r₂) (mul_comm _ _) hτ₁
  have hσ := secScal_scale t.G.hom pullback.condition r₁ r₂ (r₁ * r₂) rfl hσ₂
  have hf : ∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε k) (F.s α)
      (P.D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r₁ * r₂)) := fun α =>
    secScal_scale P.D.toPre.P.A.hom hpB r₂ r₁ (r₁ * r₂) (mul_comm _ _) (hf₁ α)
  have hf'' : ∀ α, GeneratorPullback.SecScal P.D.toPre.P.L (DegPre.famφ P.D.toPre (FractionRing V) α) (DegPre.famε (k * N))
      (F'.s α) (P.D.toPre.famφB α) (DegPre.famε (k * N)) (f'' α) (DegPre.prB P.D.toPre (FractionRing V)).left
      (scal (DegPre.BF P.D.toPre (FractionRing V)).hom (r₁ * r₂)) := fun α =>
    secScal_scale P.D.toPre.P.A.hom hpB r₁ r₂ (r₁ * r₂) rfl (hf₂ α)
  have hrel := GlobalTheory.PullIntegral.main hG V E H t P a N ha hN X hX hXc uR huR huR0 k F F' hpull (r₁ * r₂) f'' f hf hf''
  refine ⟨r₁ * r₂, σ'', τ, mul_ne_zero hr₁ hr₂, hτ, hσ, fun e => ?_⟩
  have hE : P.U.ExpandsAt e k τ f :=
    GlobalTheory.expandsAt_secIsMul V (maximalIdeal V) P.D P.A t.G P.U.toUnifPre e k r₂ τ₁ τ f₁ f
      (secIsMul_secScale_scal _ _ _) (fun α => secIsMul_secScale_scal _ _ _) (he₁ e)
  have hE'' : P.U.ExpandsAt e (k * N) σ'' f'' :=
    GlobalTheory.expandsAt_secIsMul V (maximalIdeal V) P.D P.A t.G P.U.toUnifPre e (k * N) r₁ σ₂ σ'' f₂ f''
      (secIsMul_secScale_scal _ _ _) (fun α => secIsMul_secScale_scal _ _ _) (he₂ e)
  exact GlobalTheory.PullExpLoc.main hG V E H t P a N ha hN X uR huR huR0 e k σ'' τ f'' f hE'' hE hrel

end GlobalTheory.PullExpInt
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.productUniformization_torus_isPower : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (e : ℕ), ∃ pT : IsPowGrp (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X) (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X) j, (∀ i, (U'.gt e).i ≫ (Over.pullback (thick R I e)).map (pG.pr i) = pT.pr i ≫ (U.gt e).i) ∧ ∀ (i : Fin j) (χ : D.toPre.X), res (fun x _ => show (pT.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (pT.pr i).left ⊤ (charUnit _ D.toPre.X χ)) = charUnit _ D'.toPre.X (pD.xe.symm (Pi.single i χ)) := by
  first | exact @GlobalTheory.PowTorus.torus_isPow | exact GlobalTheory.PowTorus.torus_isPow | (intros; apply GlobalTheory.PowTorus.torus_isPow <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem powDeg_diagonal_action : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a :=
  GlobalTheory.TauBalBox.exists_pow_oAct

end GlobalTheory
end
