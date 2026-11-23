module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle043
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle002
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.DiscreteGroups.GlobalIrreducibility.Bundle011

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace CanonLB

open TopForm LB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {f : X ⟶ Sp R} (e : Y ⟶ X) [IsOpenImmersion e]
  {d : ℕ} [SmoothOfRelativeDimension d f]

theorem comp_spMap_id (f : X ⟶ Sp R) : e ≫ f = (e ≫ f) ≫ spMap (RingHom.id R) := by
  simp [spMap]

theorem isFrame_pullForm_openImm {U : X.Opens} {ω : FormsOn f d U} (hω : IsFrame ω)
    {W : Y.Opens} (hW : IsAffineOpen W) (h : W ≤ e ⁻¹ᵁ U) :
    IsFrame (pullForm (comp_spMap_id e f) h ω) := by
  have hle : e ''ᵁ W ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h hy
  have h' : W ≤ e ⁻¹ᵁ (e ''ᵁ W) := (e.preimage_image_eq W).ge
  have hω' : IsFrame (resForm hle ω) := hω.res (hW.image_of_isOpenImmersion e) hle
  have key : pullForm (comp_spMap_id e f) h ω = pullForm (comp_spMap_id e f) h' (resForm hle ω) := by
    rw [pullForm_resForm]
  rw [key]
  have hiso : IsIso (e.appLE (e ''ᵁ W) W h') := by
    have : e.appLE (e ''ᵁ W) W h' = (e.appIso W).hom := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
      rfl
    rw [this]
    infer_instance
  have sq := appLE_comp_algX (comp_spMap_id e f) h'
  haveI : IsIso (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) := by
    simpa using hiso
  haveI : IsIso (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id]
    infer_instance
  have H : IsPushout (CommRingCat.ofHom (algX f (e ''ᵁ W))) (CommRingCat.ofHom (RingHom.id R))
      (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) (CommRingCat.ofHom (algX (e ≫ f) W)) := by
    refine IsPushout.of_vert_isIso ⟨?_⟩
    ext x
    exact RingHom.congr_fun sq x
  exact ⟨hW, hω'.gen.formMapSq (RingHom.id R) (e.appLE (e ''ᵁ W) W h').hom sq H⟩

abbrev OIdx (e : Y ⟶ X) (K : CanonLB f d) : Type :=
  Σ i : K.bundle.ι, {W : Y.Opens // IsAffineOpen W ∧ W ≤ e ⁻¹ᵁ K.bundle.U i}

def oBundle (e : Y ⟶ X) (K : CanonLB f d) : LB Y :=
  ZH.UFib.refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1) (fun a => a.2.2.2)

theorem resG_oBundle_g (K : CanonLB f d) (a b : OIdx e K)
    {W : Y.Opens} (h : W ≤ (oBundle e K).U a ⊓ (oBundle e K).U b) :
    resG Y h ((oBundle e K).g a b : Γ(Y, (oBundle e K).U a ⊓ (oBundle e K).U b)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W
        (h.trans (fun _ hy => ⟨a.2.2.2 hy.1, b.2.2.2 hy.2⟩))).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) := by
  simp only [oBundle, ZH.UFib.refinePull, res, pullU, Units.coe_map, MonoidHom.coe_coe]
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  simp only [Scheme.Hom.appLE, Category.assoc, resG]
  rw [← Functor.map_comp]
  rfl

theorem iSup_oIdx (K : CanonLB f d) : ⨆ a : OIdx e K, a.2.1 = ⊤ :=
  eq_top_iff.2 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart K.isLB (e y)
    obtain ⟨W, hW, hy, hsub⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := e ⁻¹ᵁ K.bundle.U i) hi
    exact Opens.mem_iSup.2 ⟨⟨i, W, hW, fun z hz => hsub hz⟩, hy⟩

def oChartPull (K : CanonLB f d) : ChartPull (oBundle e K) K.bundle e where
  idx a := a.1
  le a := a.2.2.2
  g y a b h h' := ZH.UFib.gm_refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1)
    (fun a => a.2.2.2) y a b h h'

variable [SmoothOfRelativeDimension d (e ≫ f)]

theorem resForm_pullForm_om (K : CanonLB f d) (a b : OIdx e K) {W : Y.Opens} (hW : IsAffineOpen W)
    (ha : W ≤ a.2.1) (hb : W ≤ b.2.1) (h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1)) :
    resForm hb (pullForm (comp_spMap_id e f) b.2.2.2 (K.om b.1)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W h).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) •
        resForm ha (pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)) := by
  have hfa := isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2
  have h₁ := (K.isFrame a.1).coeff_pullForm (comp_spMap_id e f) a.2.2.2 hfa inf_le_left ha h
    (resForm inf_le_right (K.om b.1))
  rw [pullForm_resForm] at h₁
  rw [g_eq_ratio, resForm_pullForm]
  exact (hfa.coeff_smul_resForm hW ha _).symm.trans (congrArg (· • _) h₁)

def openImm (K : CanonLB f d) : CanonLB (e ≫ f) d where
  bundle := oBundle e K
  isLB := ZH.UFib.refinePull_isLB K.bundle K.isLB e _ _ _ (iSup_oIdx e K)
  affine a := a.2.2.1
  om a := pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)
  gen a := (isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2).gen
  trans a b W hW ha hb := by
    have h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1) :=
      le_inf (ha.trans a.2.2.2) (hb.trans b.2.2.2)
    exact (resForm_pullForm_om e K a b hW ha hb h).trans
      (congrArg (· • _) (resG_oBundle_g e K a b (le_inf ha hb)).symm)

end CanonLB

theorem cls_canonLB_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R)
    (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension d (e ≫ f)] (K : CanonLB f d) (K' : CanonLB (e ≫ f) d),
    cls K'.bundle K'.isLB = CechPic.pull e (cls K.bundle K.isLB) := by
  intro R _ X Y f e _ d _ _ K K'
  have hp : (K.bundle.pull e).IsLB := Semi.LB.isLB_linComb K.isLB _ _
  calc cls K'.bundle K'.isLB = cls (K.openImm e).bundle (K.openImm e).isLB :=
        (cls_eq_iff _ _).2 (K'.lbIso (K.openImm e))
    _ = cls (K.bundle.pull e) hp :=
        (cls_eq_iff _ _).2 (LBIso.chartPull (K.oChartPull e)
          (Geo.Tor.chartPullPull K.bundle e e rfl) (K.lbIso K))
    _ = CechPic.pull e (cls K.bundle K.isLB) := cls_pull K.isLB e hp

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolExists

theorem exists_sum_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (a b : Fin n → M), ∑ k, exteriorPower.ιMulti R 2 ![a k, b k] = w := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, c, d, rfl⟩ := hy
    refine ⟨n + m, Fin.append a c, Fin.append b d, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨n, a, b, rfl⟩ := hx
    refine ⟨n, fun k ↦ r • a k, b, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • a k, b k] : Fin 2 → M) = Function.update ![a k, b k] 0 (r • ![a k, b k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

theorem mem_of_annihilates {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ψ : LinearMap.BilinForm K V) [hψ : ψ.IsPerfPair] (F : Submodule K V)
    (hiso : ∀ f ∈ F, ∀ g ∈ F, ψ f g = 0) (hdim : 2 * Module.finrank K F = Module.finrank K V) (f : V)
    (hf : ∀ g ∈ F, ψ f g = 0) : f ∈ F := by
  let Φ : V →ₗ[K] Module.Dual K F := F.subtype.dualMap ∘ₗ ψ
  have hΦ : Function.Surjective Φ :=
    (LinearMap.dualMap_surjective_of_injective F.injective_subtype).comp hψ.bijective_left.2
  have hker : F ≤ LinearMap.ker Φ := fun f hf' ↦ LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hiso f hf' g g.2)
  have hr := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hΦ, finrank_top, Subspace.dual_finrank_eq] at hr
  have heq : F = LinearMap.ker Φ := Submodule.eq_of_le_of_finrank_eq hker (by omega)
  rw [heq]
  exact LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hf g g.2)

theorem isGen_self {X : Scheme.{0}} {L : Semi.LB X} (hL : L.IsLB) :
    Semi.LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : Semi.LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

end GlobalTheory.PolExists

namespace GlobalTheory.PolExists

open GlobalTheory.Published GlobalTheory.CatCoh

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X}
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo K _ x A _ π hπ
  have hA : Semi.IsAbelianScheme A := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hc : IsCommMonObj A := by
      open MonoidalCategory CartesianMonoidalCategory MonObj in
      open scoped CategoryTheory.Obj in
        exact (by
          rw [isCommMonObj_iff_isMulCommutative]
          intro T
          refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
          rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
            ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm])
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 K A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso K ⊥ (dp0 K) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 K) (𝟙 _) A
    rw [show prim (dp0 K) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 K) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by

      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 K) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 K A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, -, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, -, hFfin, -, hFrk⟩ := P.2.1 K A _ hA gA
  let p : PrimeSpectrum K := IsLocalRing.closedPoint K
  have d1 : Module.finrank K (primDR A) = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d2 : Module.finrank K (PrimitiveSubmodule A) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have := hFrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d3 := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
  have d4 : Module.finrank K (HdR A) = Module.finrank K (primDR A) := Subspace.dual_finrank_eq
  exact mem_of_annihilates _ (Fil A) hiso (by
    change 2 * Module.finrank K (PrimitiveSubmodule A).dualAnnihilator = _
    omega) f hf

end GlobalTheory.PolExists
end
end

section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem mul_apply_succ {n : ℕ} {X Y : GL (Fin n) R} (hX : X ∈ unipB R (Fin n)) (hY : Y ∈ unipB R (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a a' =
      (X : Matrix (Fin n) (Fin n) R) a a' + (Y : Matrix (Fin n) (Fin n) R) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

end GlobalTheory.GamMul.UnipPlaced

namespace GlobalTheory.GamMul.UnipPlaced

variable {R : Type} [CommRing R]

theorem superDiag_mul_unip {n : ℕ} {u v : GL (Fin n) R} (hu : u ∈ unipB R (Fin n)) (hv : v ∈ unipB R (Fin n)) :
    superDiag (u * v) = superDiag u + superDiag v := by
  simp only [superDiag, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
    mul_apply_succ hu hv (Finset.mem_filter.1 hj).2

end GlobalTheory.GamMul.UnipPlaced
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped TensorProduct

namespace GlobalTheory.NormSum.IntOver

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] 𝔸
local notation "𝒮" => tensInt (F := F) 𝔸 (intOE E) (intAd F)

theorem eps_mul_mem (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : (m : 𝓞 F) ∉ v.asIdeal) (x : 𝒜)
    (hx : (m : 𝒜) * x ∈ 𝒮) : afsplitEps E v * x ∈ 𝒮 := by
  have hval : Valued.v (m : v.adicCompletion F) = 1 := by
    rw [RepAt.val_nat]
    exact le_antisymm (v.valuation_le_one _) (not_lt.1 fun h' => hm ((v.valuation_lt_one_iff_mem _).1 h'))
  have hm0 : (m : v.adicCompletion F) ≠ 0 := fun h => by rw [h, map_zero] at hval; exact zero_ne_one hval
  have ha : (m : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  set u : 𝒮 := RepAt.incInt ⟨afsplitI v (m : v.adicCompletion F)⁻¹, afsplitI_mem_intAd v _ ha⟩ with hu
  have e1 : afsplitI v (m : v.adicCompletion F)⁻¹ * (m : 𝔸) = afsplitI v 1 := by
    rw [← map_natCast (algebraMap F 𝔸) m]
    ext w
    rw [afsplit_mul_apply]
    congr 1
    change afsplitI v (m : v.adicCompletion F)⁻¹ w * algebraMap F (w.adicCompletion F) (m : F) = afsplitI v 1 w
    by_cases h : w = v
    · subst h
      rw [afsplitI_self, afsplitI_self, map_natCast]
      exact inv_mul_cancel₀ hm0
    · rw [afsplitI_ne v w h, afsplitI_ne v w h, zero_mul]
  have e2 : (u : 𝒜) * (m : 𝒜) = afsplitEps E v := by
    rw [hu]
    change (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) (afsplitI v (m : v.adicCompletion F)⁻¹) * (m : 𝒜) = _
    rw [← map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) m, ← map_mul, e1, afsplitEps,
      Algebra.TensorProduct.one_def, afsplitIE_tmul]
    rfl
  rw [← e2, mul_assoc]
  exact mul_mem u.2 hx

end Ad

end GlobalTheory.NormSum.IntOver


open GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem in
theorem GlobalTheory.NormSum.exists_prime_integralOver :
    ∀ (D : Formalism.BasicNotions.D7) (N : ℕ) (h : ↥(Formalism.MainNotions.StandardLatticesGL3.GA D N)), ∃ p : ℕ, p.Prime ∧ GlobalTheory.NormSum.IntegralOver D p h := by
  intro D N h
  set g : Matrix (Fin N) (Fin N) (AE D) := ((h : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j) l
  rw [← htriv i j] at this
  exact this
end
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  first | exact @GlobalTheory.exists_lift_to_complete_dvr_of_finite | exact GlobalTheory.exists_lift_to_complete_dvr_of_finite | (intros; apply GlobalTheory.exists_lift_to_complete_dvr_of_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_lineBundle_nhd_of_stalk_baseChange : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h] [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB → ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧ ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W), a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  first | exact @GlobalTheory.StalkLB.exists_lb_nhd | exact GlobalTheory.StalkLB.exists_lb_nhd | (intros; apply GlobalTheory.StalkLB.exists_lb_nhd <;> assumption)
end
