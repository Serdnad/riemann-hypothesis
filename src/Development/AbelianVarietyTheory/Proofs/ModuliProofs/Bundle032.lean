module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitsOfIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle023
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle024
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ValGenExtend

def genSec {X : Scheme.{0}} {L : LB X} (t : LB.Gen L) (ht : t.IsGen) : LB.Sec L :=
  ⟨fun i => (t.s i).val, fun i j => by
    have h := congrArg Units.val (ht i j)
    exact h⟩

theorem isGen_inv_of_eq {X : Scheme.{0}} {N : LB X} (t : LB.Gen N) (ht : t.IsGen)
    (g : ∀ a b, Γ(X, N.U a ⊓ N.U b)ˣ) (hg : ∀ a b, g a b = (N.g a b)⁻¹) :
    LB.Gen.IsGen (L := ⟨N.ι, N.U, g⟩) ⟨fun i => (t.s i)⁻¹⟩ := by
  intro a b
  have h : res (inf_le_left : N.U a ⊓ N.U b ≤ _) (t.s a)⁻¹ =
      g a b * res (inf_le_right : N.U a ⊓ N.U b ≤ _) (t.s b)⁻¹ := by
    rw [map_inv, map_inv, ht a b, _root_.mul_inv, hg]
  exact h

theorem exists_isGen_inv {X Y : Scheme.{0}} {I : Type} {U : I → X.Opens}
    (g g' : ∀ a b, Γ(X, U a ⊓ U b)ˣ) (hg : ∀ a b, g' a b = (g a b)⁻¹) (j : Y ⟶ X)
    (t : LB.Gen ((⟨I, U, g⟩ : LB X).pull j)) (ht : t.IsGen) :
    ∃ t' : LB.Gen ((⟨I, U, g'⟩ : LB X).pull j), t'.IsGen ∧ ∀ i : I,
      rs Y (le_pull ⟨I, U, g⟩ j (W := U i) (i := i) le_rfl) (t.s fun _ => i).val *
        rs Y (le_pull ⟨I, U, g'⟩ j (W := U i) (i := i) le_rfl) (t'.s fun _ => i).val = 1 := by
  refine ⟨⟨fun i => (t.s i)⁻¹⟩,
    isGen_inv_of_eq t ht ((⟨I, U, g'⟩ : LB X).pull j).g fun a b => ?_, fun i => ?_⟩
  · dsimp only [LB.pull, LB.LinComb]
    simp only [hg, map_inv, zpow_one, Finset.prod_inv_distrib]
    try rfl
  · exact (map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _))

theorem mem_basicOpen_of_mem {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) {i : L.ι} (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have h := congrArg X.basicOpen (s.compat i k)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (L.g i k).isUnit] at h
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at h
  have hm : x ∈ L.U i ⊓ L.U k := ⟨hi, X.basicOpen_le _ hk⟩
  exact (h.ge (⟨hm, hm, hk⟩ : x ∈ _ ⊓ (_ ⊓ X.basicOpen (s.f k)))).2

theorem app_cst {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {X Y : Scheme.{0}}
    {f : X ⟶ Sp O} {j : Y ⟶ X} {g : Y ⟶ Sp K} (h : j ≫ f = g ≫ spMap φ) (U : X.Opens) (a : O) :
    (j.app U).hom (GlobalTheory.AbLaw.cst f U a) = GlobalTheory.AbLaw.cst g (j ⁻¹ᵁ U) (φ a) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  have h2 := congrArg (fun u => u.hom a) h1
  have h3 := congrArg (fun u => u.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)))
    (j.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  exact h3.trans (congrArg (rs Y le_top) h2)

theorem isUnit_of_mem_basicOpen {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}}
    (f : X ⟶ Sp O) {U : X.Opens} {a : O} {x : X} (hx : x ∈ X.basicOpen (GlobalTheory.AbLaw.cst f U a))
    (hf : f x = IsLocalRing.closedPoint O) : IsUnit a := by
  have h : X.basicOpen (GlobalTheory.AbLaw.cst f U a) =
      U ⊓ X.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) :=
    Scheme.basicOpen_res _ _ _
  have h1 : x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) := (h.le hx).2
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  have h2 : a ∉ (f x).asIdeal := h1
  rw [hf] at h2
  exact not_not.1 h2

theorem triv_of_triv_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  intro O K _ _ _ _ _ _ _ _ X XK f j fK hp hsm hqc hgi M hM ⟨t, ht⟩
  have : IsDominant (spMap (algebraMap O K)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap O K))
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  have : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ hp
  obtain ⟨z⟩ : Nonempty XK := inferInstance
  obtain ⟨i₀, hi₀⟩ := exists_chart hM (j z)
  have : Nonempty ((M.pull j).U fun _ => i₀) := ⟨⟨z, le_pull M j le_rfl hi₀⟩⟩
  obtain ⟨t', ht', htt⟩ := exists_isGen_inv M.g (GlobalTheory.AbLaw.pw M (-1)).g
    (fun a b => zpow_neg_one _) j t ht
  have hne : (t'.s fun _ => i₀).val ≠ 0 := fun h => by
    have h1 := htt i₀
    have : Nonempty (j ⁻¹ᵁ M.U i₀) := ⟨⟨z, hi₀⟩⟩
    rw [h, map_zero, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c, s, hc, hs, x, hx, hfx⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K X XK f j fK hp hsm hqc hgi M hM
    (genSec t ht) ⟨fun _ => i₀, (t.s fun _ => i₀).ne_zero⟩
  obtain ⟨c', s', hc', hs', x', hx', hfx'⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K X XK f j fK hp hsm hqc hgi _
    (isLB_pw hM (-1)) (genSec t' ht') ⟨fun _ => i₀, hne⟩
  have hprod : ∀ i : M.ι, (j.app (M.U i)).hom (s.f i * (show Γ(X, M.U i) from s'.f i)) =
      GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) (c * c') := fun i => by
    have h' : (j.app (M.U i)).hom (s'.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c' *
      rs XK (le_pull (GlobalTheory.AbLaw.pw M (-1)) j (W := M.U i) (i := i) le_rfl)
        (t'.s fun _ => i).val := hs' i
    have h : (j.app (M.U i)).hom (s.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c *
      rs XK (le_pull M j le_rfl) (t.s fun _ => i).val := hs i
    rw [map_mul, h, h', _root_.mul_mul_mul_comm, ← map_mul]
    exact (congrArg _ (htt i)).trans (_root_.mul_one _)
  have key : ∀ i, IsUnit (s.f i) := by
    rcases ValuationRing.isInteger_or_isInteger O (c * c') with ⟨a, ha⟩ | ⟨a, ha⟩
    · have e : ∀ i : M.ι, s.f i * (show Γ(X, M.U i) from s'.f i) = GlobalTheory.AbLaw.cst f (M.U i) a :=
        fun i => j.app_injective _ ((hprod i).trans (ha ▸ (app_cst _ hp.w _ a).symm))
      obtain ⟨y, hy, hy₁, hy₂⟩ := (f.isIrreducible_preimage f.isOpenMap
        (isIrreducible_singleton (x := IsLocalRing.closedPoint O))).isPreirreducible _ _
        (Out.nonzeroLocus s).isOpen (Out.nonzeroLocus s').isOpen ⟨x, hfx, hx⟩ ⟨x', hfx', hx'⟩
      obtain ⟨k, hk⟩ := exists_chart hM y
      have hu : IsUnit a := by
        refine isUnit_of_mem_basicOpen f (U := M.U k) (x := y) ?_ hy
        rw [← e k, Scheme.basicOpen_mul]
        exact ⟨mem_basicOpen_of_mem s hy₁ hk, mem_basicOpen_of_mem s' hy₂ (i := k) hk⟩
      exact fun i => isUnit_of_mul_isUnit_left ((e i).symm ▸ hu.map _)
    · intro i
      have e : s.f i * ((show Γ(X, M.U i) from s'.f i) * GlobalTheory.AbLaw.cst f (M.U i) a) = 1 := by
        refine j.app_injective _ ?_
        change (j.app (M.U i)).hom _ = (j.app (M.U i)).hom _
        rw [← _root_.mul_assoc, map_mul, hprod, app_cst _ hp.w, ← map_mul, ha,
          mul_inv_cancel₀ (mul_ne_zero hc hc'), map_one, map_one]
      exact IsUnit.of_mul_eq_one _ e
  exact ⟨⟨fun i => (key i).unit⟩, fun a b => Units.ext (s.compat a b)⟩

end GlobalTheory.ValGenExtend
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Primitive

open GlobalTheory.KuennethOne

variable {T Z A : Scheme.{0}} {I : Type} {U : I → A.Opens} {c : C1 U}

theorem rsT_eq_rs {O₀ O : A.Opens} (s : Γ(A, O₀)) (h : O ≤ O₀) : rsT s O = rs h s := by
  rw [rsT, dif_pos h]
  rfl

theorem pbT_eq (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀) :
    pbT f s O = (f.appLE O₀ O h).hom s := by
  unfold pbT
  exact dif_pos h

theorem rs_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens} (h : O ≤ f ⁻¹ᵁ O₀)
    (h' : O' ≤ O) : rs h' (pbT f s O) = pbT f s O' := by
  rw [pbT_eq f s h, pbT_eq f s (h'.trans h)]
  show (T.presheaf.map (homOfLE h').op).hom ((f.appLE O₀ O h).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem app_pbT (r : T ⟶ Z) (f : Z ⟶ A) (g : T ⟶ A) (e : r ≫ f = g) {O₀ : A.Opens} (s : Γ(A, O₀))
    {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : (r.app O).hom (pbT f s O) = pbT g s (r ⁻¹ᵁ O) := by
  subst e
  rw [pbT_eq f s h, pbT_eq (r ≫ f) s (r.preimage_mono h)]
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

theorem le_pre_inf (f : T ⟶ A) {N : T.Opens} {V W : A.Opens} (h : N ≤ f ⁻¹ᵁ V) (h' : N ≤ f ⁻¹ᵁ W) :
    N ≤ f ⁻¹ᵁ (V ⊓ W) :=
  fun _ hx => ⟨h hx, h' hx⟩

private lemma pbT_add' (f : T ⟶ A) {O₀ : A.Opens} (s s' : Γ(A, O₀)) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O₀) : pbT f (s + s') N = pbT f s N + pbT f s' N := by
  simp only [pbT_eq f _ hN, map_add (f := _)]

private lemma pbT_rsT' (f : T ⟶ A) {O₀ O : A.Opens} (s : Γ(A, O₀)) (hO : O ≤ O₀) {N : T.Opens}
    (hN : N ≤ f ⁻¹ᵁ O) : pbT f (rsT s O) N = pbT f s N := by
  rw [rsT_eq_rs s hO, pbT_eq f _ hN, pbT_eq f s (hN.trans (f.preimage_mono hO))]
  show (f.appLE O N hN).hom ((A.presheaf.map (homOfLE hO).op).hom s) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem pbT_coc (hc : IsCoc U c) (f : T ⟶ A) (i j k : I) {N : T.Opens} (hi : N ≤ f ⁻¹ᵁ U i)
    (hj : N ≤ f ⁻¹ᵁ U j) (hk : N ≤ f ⁻¹ᵁ U k) :
    pbT f (c i j) N + pbT f (c j k) N = pbT f (c i k) N := by
  have hN : N ≤ f ⁻¹ᵁ (U i ⊓ U j ⊓ U k) := le_pre_inf f (le_pre_inf f hi hj) hk
  have l1 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  have l2 : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have l3 : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [← pbT_rsT' f (c i j) l1 hN, ← pbT_rsT' f (c j k) l2 hN, ← pbT_rsT' f (c i k) l3 hN,
    ← pbT_add' f _ _ hN, hc i j k]

theorem exists_split (hc : IsCoc U c) (f g : T ⟶ A) {i₀ : I} (hg : ⊤ ≤ g ⁻¹ᵁ U i₀) {J : Type}
    (i₁ i₂ i₃ : J → I) (N : J → T.Opens) (h₁ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₁ a))
    (h₂ : ∀ a, N a ≤ f ⁻¹ᵁ U (i₂ a)) (h₃ : ∀ a, N a ≤ g ⁻¹ᵁ U (i₃ a)) :
    ∃ ψ : ∀ a, Γ(T, N a), ∀ a b (M : T.Opens) (ha : M ≤ N a) (hb : M ≤ N b),
      pbT f (c (i₁ a) (i₁ b)) M - pbT f (c (i₂ a) (i₂ b)) M - pbT g (c (i₃ a) (i₃ b)) M =
        rs ha (ψ a) - rs hb (ψ b) := by
  refine ⟨fun a => pbT f (c (i₁ a) (i₂ a)) (N a) - pbT g (c (i₃ a) i₀) (N a), ?_⟩
  intro a b M ha hb
  have hg' : M ≤ g ⁻¹ᵁ U i₀ := le_top.trans hg
  have e1 := pbT_coc hc f (i₁ a) (i₂ a) (i₁ b) (ha.trans (h₁ a)) (ha.trans (h₂ a)) (hb.trans (h₁ b))
  have e2 := pbT_coc hc f (i₂ a) (i₁ b) (i₂ b) (ha.trans (h₂ a)) (hb.trans (h₁ b)) (hb.trans (h₂ b))
  have e3 := pbT_coc hc g (i₃ a) i₀ (i₃ b) (ha.trans (h₃ a)) hg' (hb.trans (h₃ b))
  have e4 := pbT_coc hc g (i₃ b) i₀ (i₃ b) (hb.trans (h₃ b)) hg' (hb.trans (h₃ b))
  have e5 := pbT_coc hc g (i₃ b) (i₃ b) (i₃ b) (hb.trans (h₃ b)) (hb.trans (h₃ b)) (hb.trans (h₃ b))
  have r1 := rs_pbT f (c (i₁ a) (i₂ a)) (le_pre_inf f (h₁ a) (h₂ a)) ha
  have r2 := rs_pbT f (c (i₁ b) (i₂ b)) (le_pre_inf f (h₁ b) (h₂ b)) hb
  have r3 := rs_pbT g (c (i₃ a) i₀) (le_pre_inf g (h₃ a) (le_top.trans hg)) ha
  have r4 := rs_pbT g (c (i₃ b) i₀) (le_pre_inf g (h₃ b) (le_top.trans hg)) hb
  simp only [map_sub, r1, r2, r3, r4]
  linear_combination e2 - e1 + e3 - e4 - e5

theorem iSup_triple (hU : ⨆ i, U i = ⊤) (m p q : Z ⟶ A) :
    ⨆ α : I × I × I, m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2 = ⊤ := by
  have cov : ∀ y : A, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨i, hi⟩ := cov (m x)
  obtain ⟨j, hj⟩ := cov (p x)
  obtain ⟨k, hk⟩ := cov (q x)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j, k), ⟨⟨hi, hj⟩, hk⟩⟩

private lemma preimage_le_preimage_of_comp_eq {X₁ X₂ X₃ : Scheme.{0}} (s : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (g : X₁ ⟶ X₃)
    (e : s ≫ m = g) {W : X₂.Opens} {O : X₃.Opens} (h : W ≤ m ⁻¹ᵁ O) : s ⁻¹ᵁ W ≤ g ⁻¹ᵁ O := by
  subst e
  intro x hx
  show (s ≫ m) x ∈ O
  rw [Scheme.Hom.comp_apply]
  exact h hx

private lemma presheaf_map_pbT (f : T ⟶ A) {O₀ : A.Opens} (s : Γ(A, O₀)) {O O' : T.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (h' : O' ≤ O) :
    (T.presheaf.map (homOfLE h').op).hom (pbT f s O) = pbT f s O' :=
  rs_pbT f s h h'


private theorem cech_coboundary_mul_sub_fst_sub_snd : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) := by
  intro hL _ _ K _ P₀ I U c hU hc
  have : IsProper P₀.A.hom := P₀.isAb.proper
  have hsub : Subsingleton (𝟙_ (Over (Sp K))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))
  let _ : Inhabited (𝟙_ (Over (Sp K))).left := inferInstanceAs (Inhabited (Spec (CommRingCat.of K)))
  have hbij : Function.Bijective P₀.A.hom.appTop.hom := hL.globalFns _ P₀.A P₀.isAb
  let e : 𝟙_ (Over (Sp K)) ⟶ P₀.A := MonObj.one
  let g₀ : P₀.A.left ⟶ P₀.A.left := (toUnit P₀.A ≫ e).left
  let m := (fst P₀.A P₀.A * snd P₀.A P₀.A).left
  let p := (fst P₀.A P₀.A).left
  let q := (snd P₀.A P₀.A).left

  have hpt : ∀ x : P₀.A.left, g₀ x = e.left default := by
    intro x
    show ((toUnit P₀.A).left ≫ e.left) x = _
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have cov : ∀ y : P₀.A.left, ∃ i, y ∈ U i := fun y => by
    have hy : y ∈ (⨆ i, U i) := hU ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨i₀, hi₀⟩ := cov (e.left default)
  have hg : ⊤ ≤ g₀ ⁻¹ᵁ U i₀ := fun x _ => by
    show g₀ x ∈ U i₀
    rw [hpt x]
    exact hi₀

  have es_m : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (mul_one (𝟙 P₀.A))
  have es_p : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ p = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]
    rfl
  have es_q : (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left ≫ q = g₀ := by
    rw [← Over.comp_left, lift_snd]
  have et_m : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ m = 𝟙 _ := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst, lift_snd]
    exact congrArg Over.Hom.left (one_mul (𝟙 P₀.A))
  have et_p : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ p = g₀ := by
    rw [← Over.comp_left, lift_fst]
  have et_q : (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left ≫ q = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]
    rfl
  let V : I × I × I → (P₀.A ⊗ P₀.A).left.Opens := fun α =>
    m ⁻¹ᵁ U α.1 ⊓ p ⁻¹ᵁ U α.2.1 ⊓ q ⁻¹ᵁ U α.2.2
  have hVm : ∀ α, V α ≤ m ⁻¹ᵁ U α.1 := fun α => inf_le_left.trans inf_le_left
  have hVp : ∀ α, V α ≤ p ⁻¹ᵁ U α.2.1 := fun α => inf_le_left.trans inf_le_right
  have hVq : ∀ α, V α ≤ q ⁻¹ᵁ U α.2.2 := fun α => inf_le_right
  obtain ⟨ψ, hK⟩ := kuenneth_injective K P₀.A P₀.A e e inferInstance inferInstance inferInstance
    inferInstance hbij hbij (I × I × I) V (iSup_triple hU m p q)
    (fun a b => pbT m (c a.1 b.1) (V a ⊓ V b) - pbT p (c a.2.1 b.2.1) (V a ⊓ V b) -
      pbT q (c a.2.2 b.2.2) (V a ⊓ V b))
    (by
      intro a b d
      have w1 : V a ⊓ V b ⊓ V d ≤ V a := inf_le_left.trans inf_le_left
      have w2 : V a ⊓ V b ⊓ V d ≤ V b := inf_le_left.trans inf_le_right
      have w3 : V a ⊓ V b ⊓ V d ≤ V d := inf_le_right
      simp only [map_sub]
      rw [presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm b)) (inf_le_right.trans (hVm d))),
        presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp b)) (inf_le_right.trans (hVp d))), presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq b)) (inf_le_right.trans (hVq d))),
        presheaf_map_pbT m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm d))), presheaf_map_pbT p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp d))),
        presheaf_map_pbT q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq d)))]
      have cm := pbT_coc hc m a.1 b.1 d.1 (w1.trans (hVm a)) (w2.trans (hVm b)) (w3.trans (hVm d))
      have cp := pbT_coc hc p a.2.1 b.2.1 d.2.1 (w1.trans (hVp a)) (w2.trans (hVp b)) (w3.trans (hVp d))
      have cq := pbT_coc hc q a.2.2 b.2.2 d.2.2 (w1.trans (hVq a)) (w2.trans (hVq b)) (w3.trans (hVq d))
      linear_combination cm - cp - cq)
    (by
      let s := (lift (𝟙 P₀.A) (toUnit P₀.A ≫ e)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.1)
        (fun α => α.2.2) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ es_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s p _ es_p (hVp α)) (fun α => preimage_le_preimage_of_comp_eq s q _ es_q (hVq α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) es_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p (𝟙 _) es_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q g₀ es_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b)))]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
    (by
      let s := (lift (toUnit P₀.A ≫ e) (𝟙 P₀.A)).left
      obtain ⟨χ, hχ⟩ := exists_split hc (𝟙 _) g₀ hg (fun α : I × I × I => α.1) (fun α => α.2.2)
        (fun α => α.2.1) (fun α => s ⁻¹ᵁ V α) (fun α => preimage_le_preimage_of_comp_eq s m _ et_m (hVm α))
        (fun α => preimage_le_preimage_of_comp_eq s q _ et_q (hVq α)) (fun α => preimage_le_preimage_of_comp_eq s p _ et_p (hVp α))
      refine ⟨χ, fun a b => ?_⟩
      rw [map_sub, map_sub, app_pbT s m (𝟙 _) et_m _ (le_pre_inf m (inf_le_left.trans (hVm a)) (inf_le_right.trans (hVm b))),
        app_pbT s p g₀ et_p _ (le_pre_inf p (inf_le_left.trans (hVp a)) (inf_le_right.trans (hVp b))),
        app_pbT s q (𝟙 _) et_q _ (le_pre_inf q (inf_le_left.trans (hVq a)) (inf_le_right.trans (hVq b))), sub_right_comm]
      exact hχ a b _ (s.preimage_mono inf_le_left) (s.preimage_mono inf_le_right))
  unfold IsCob
  refine ⟨fun a => -ψ a, fun a b => (hK a b).trans ?_⟩
  rw [rsT_eq_rs _ inf_le_right, rsT_eq_rs _ inf_le_left, map_neg, map_neg]
  exact (neg_sub_neg _ _).symm

theorem cech_primitive : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (I : Type) (U : I → P₀.A.left.Opens) (c : C1 U), ⨆ i, U i = ⊤ → IsCoc U c → IsCob (fun α : I × I × I => (fst P₀.A P₀.A * snd P₀.A P₀.A).left ⁻¹ᵁ U α.1 ⊓ (fst P₀.A P₀.A).left ⁻¹ᵁ U α.2.1 ⊓ (snd P₀.A P₀.A).left ⁻¹ᵁ U α.2.2) (fun α β => pbT (fst P₀.A P₀.A * snd P₀.A P₀.A).left (c α.1 β.1) _ - pbT (fst P₀.A P₀.A).left (c α.2.1 β.2.1) _ - pbT (snd P₀.A P₀.A).left (c α.2.2 β.2.2) _) :=
  cech_coboundary_mul_sub_fst_sub_snd

end GlobalTheory.KS.Primitive
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.level_on_factor_of_eighth_power_abelianScheme : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  first | exact @GlobalTheory.ZM.level_on_factor_of_eighth_power | exact GlobalTheory.ZM.level_on_factor_of_eighth_power | (intros; apply GlobalTheory.ZM.level_on_factor_of_eighth_power <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem exists_fac_field {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) (K : Type) [Field K]
    (x : Sp K ⟶ S) : ∃ (i : I) (x' : Sp K ⟶ (U i).toScheme), x' ≫ (U i).ι = x := by
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum K) := inferInstance
  obtain ⟨i, hi⟩ := exists_mem hU (x p)
  have hr : Set.range x.base ⊆ Set.range (U i).ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : q = p := Subsingleton.elim (α := PrimeSpectrum K) q p
    subst hq
    exact hi
  exact ⟨i, IsOpenImmersion.lift (U i).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (x : Fin n → (T' ⟶ G')) (c : Fin n → ℕ) :
    ρ (Out.linComb x c) = Out.linComb (fun l => ρ (x l)) c := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow]

private theorem exists_bijective_monoidHom_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {ψ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f ψ) (T : Over S') :
    ∃ ρ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ z, (ρ z).left = z.left ≫ ψ) ∧ Function.Injective ρ ∧ Function.Surjective ρ := by
  have hw : ∀ z : T ⟶ G', (z.left ≫ ψ) ≫ G.hom = T.hom ≫ f := fun z => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w z]
  refine ⟨MonoidHom.mk' (fun z => Over.homMk (z.left ≫ ψ) (hw z)) (fun a b => ?_), fun _ => rfl, ?_, ?_⟩
  · exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  · intro a b hab
    exact lift_ext h.1 (congrArg CommaMorphism.left hab)
  · intro y
    obtain ⟨z, hz⟩ := exists_lift h.1 y
    exact ⟨z, Over.OverMorphism.ext hz.symm⟩

theorem torsionBasis_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  intro S I U A _ G _ ψ hU hψ _ _ g k P Q hPQ hQ K _ _ x y hy
  obtain ⟨i, x', rfl⟩ := exists_fac_field hU K x
  obtain ⟨ρ, hρ, hinj, hsurj⟩ := exists_bijective_monoidHom_points_of_isGrpPullback (hψ i) (Over.mk x')
  obtain ⟨y', rfl⟩ := hsurj y
  have hpt : ∀ l, ρ ((Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) =
      (Over.homMk (x' ≫ (U i).ι) (by simp) : Over.mk (x' ≫ (U i).ι) ⟶ Out.baseOver S) ≫ P l := by
    intro l
    apply Over.OverMorphism.ext
    rw [hρ]
    simp [hPQ]
  have hy' : y' ^ k = 1 := hinj (by rw [map_pow, map_one]; exact hy)
  obtain ⟨c, hc, huniq⟩ := hQ i K x' y' hy'
  refine ⟨c, ?_, fun c' hc' => huniq c' (hinj ?_)⟩
  · rw [← hc, map_linComb]
    simp only [hpt]
  · rw [map_linComb]
    simp only [hpt]
    exact hc'

end GlobalTheory.CoverGlue
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (La' : Type) [AddCommGroup La'] (EF' : LinearMap.BilinForm ℤ La') (lam' : Fin (2 * g) → La') (ac' : J → La' → La') (Q' : La' →+ (Fin g → ℂ)) (Hm' : Matrix (Fin g) (Fin g) ℂ) (e : La ≃+ La') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (Function.Injective Q' ∧ DiscreteTopology (Q').range ∧ Submodule.span ℝ (Set.range Q') = ⊤ ∧ (Hm').IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧ ∀ x y, (hermForm Hm' (Q' x) (Q' y)).im = EF' x y) → (∀ x, Q' (e x) = h (Q x)) → (∀ x y, EF' (e x) (e y) = EF x y) → (∀ j x, e (ac j x) = ac' j (e x)) → (∀ i, ∃ y, e (lam i) = lam' i + k • y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm' χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q').range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q' x → χ' l = (-1) ^ EF' x (ac' w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q' (lam' i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q' x) = Q' (ac' j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.UnifTransport.transport_uniformisation | exact GlobalTheory.UnifTransport.transport_uniformisation | (intros; apply GlobalTheory.UnifTransport.transport_uniformisation <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

theorem _root_.GlobalTheory.T.isPullback_flat_of_tame_alt : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).asIso.hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).asIso.hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).asIso.hom = x → pullback.fst p x ≫ (τ g).asIso.hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  first | exact @GlobalTheory.TameDescent.isPullback_flat_of_tame | exact GlobalTheory.TameDescent.isPullback_flat_of_tame | (intros; apply GlobalTheory.TameDescent.isPullback_flat_of_tame <;> assumption)
end
