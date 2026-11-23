module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

section Generic
variable {O : Type} [CommRing O] [StarRing O]


omit [StarRing O] in
theorem exists_lift_ct [IsDedekindDomain O] [Module.Finite ℤ O] {V G X : Type} [AddCommGroup V] [Module ℂ V] [CommGroup G]
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (F : O →+* Module.End ℂ V) (ex : V → G)
    (hadd : ∀ z w, ex (z + w) = ex z * ex w) (hs : Function.Surjective ex) (c : X → G)
    (hc : ∀ x y, c (x + y) = c x * c y) (hl : ∀ (a : O) x z, ex z = c x → ex (F a z) = c (a • x)) :
    ∃ ct : X →+ V, (∀ (a : O) x, ct (a • x) = F a (ct x)) ∧ ∀ x, c x = ex (ct x) := by
  let _ : Module O V := Module.compHom V F
  have e0 : ex 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have c0 : c 0 = 1 := by
    have := hc 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let P : Submodule O (X × V) :=
    { carrier := {p | ex p.2 = c p.1}
      zero_mem' := e0.trans c0.symm
      add_mem' := fun {p q} hp hq => by
        change ex (p.2 + q.2) = c (p.1 + q.1)
        rw [hadd, hc, (show ex p.2 = _ from hp), (show ex q.2 = _ from hq)]
      smul_mem' := fun a p hp => hl a p.1 p.2 hp }
  obtain ⟨g, hg⟩ := GlobalTheory.Forms.exists_linearMap_lift_of_int (LinearMap.fst O X V ∘ₗ P.subtype)
    (fun x => by
      obtain ⟨z, hz⟩ := hs (c x)
      exact ⟨⟨(x, z), hz⟩, rfl⟩) LinearMap.id
  refine ⟨(LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).toAddMonoidHom,
    fun a x => (LinearMap.snd O X V ∘ₗ P.subtype ∘ₗ g).map_smul a x, fun x => ?_⟩
  have h1 : (g x).1.1 = x := hg x
  have h2 : ex (g x).1.2 = c (g x).1.1 := (g x).2
  rw [h1] at h2
  exact h2.symm

theorem exists_log_frame [IsDedekindDomain O] [Module.Finite ℤ O] [Module.Free ℤ O] {N : NumD ℂ} {B : AnArc O}
    {ex : (Fin B.gB → ℂ) → N.A} {fr : (Fin B.gB → ℂ) → ℂˣ} {th : (Fin B.gB → ℂ) → ℂ} (hab : IsAbFrame N.toNumB B ex fr th)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module O X] (e : X ≃+ N.X)
    (ct : X →+ (Fin B.gB → ℂ)) (hc : ∀ x, N.c (e x) = ex (ct x)) {w : O} (hw : w + star w = 1)
    (hbal : ∀ (a : O) y x, (N.τ (e (a • y)) (e x) : ℂ) * fr (ct (a • y) + ct x) * fr (ct y) * fr (ct (star a • x)) =
      N.τ (e y) (e (star a • x)) * fr (ct y + ct (star a • x)) * fr (ct (a • y)) * fr (ct x)) :
    ∃ T : X →+ X →+ ℂ, (∀ x y, T x y = T y x) ∧ (∀ (a : O) y x, T (a • y) x = T y (star a • x)) ∧
      ∀ x y, eTwoPi (T x y) * fr (ct x) * fr (ct y) = N.τ (e x) (e y) * fr (ct x + ct y) := by
  have := GlobalTheory.Forms.projective_of_int O X
  have : Module.Finite O X := Module.Finite.of_restrictScalars_finite ℤ O X
  obtain ⟨T, h1, h2, h3⟩ := GlobalTheory.Forms.exists_log_of_bimul hw
    (fun x y : X => N.τ (e x) (e y) * fr (ct x + ct y) / fr (ct x) / fr (ct y))
    (fun y x x' => by
      have a := congrArg Additive.ofMul (N.τ_add_right (e y) (e x) (e x'))
      have b := congrArg Additive.ofMul (hab.2.2.2.2.2.1 (ct x) (ct x') (ct y))
      apply Additive.ofMul.injective
      simp only [hc, map_add (f := _), add_comm (ct y), ofMul_mul, ofMul_div] at a b ⊢
      linear_combination (norm := abel) a - b)
    (fun y x => by rw [N.τ_symm, add_comm, div_right_comm])
    (fun a y x => by
      have b := hbal a y x
      simp only [← Units.val_mul, Units.val_inj] at b
      replace b := congrArg Additive.ofMul b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div] at b ⊢
      linear_combination (norm := abel) b)
  refine ⟨AddMonoidHom.mk' (fun x => (T x).toAddMonoidHom) fun x y => by ext; simp, h1, h2, fun x y => ?_⟩
  change Complex.exp (2 * Real.pi * Complex.I * T x y) * _ * _ = _
  rw [← h3]
  simp only [← Units.val_mul, Units.val_inj]
  rw [mul_right_comm, div_mul_cancel, div_mul_cancel]

end Generic

theorem dict_of_val : BrActSt → ValSt → DictSt := by
  intro hBr hVal E _ _ _ H D R _ _ _ A k β hβ
  let _ := H.starRing
  obtain ⟨B, ex, fr, th, hab, hth, hchi, hsig, hF, hros, hprim⟩ := hVal E H D R A
  have := A.closed
  obtain ⟨b1, b2, b3⟩ := hBr R A.D₀ A.even A.bimult ℂ A.N A.ν (𝓞 E) A.oa
  have := A.D₀.freeX
  have := A.D₀.finX
  set e : A.D₀.X ≃+ A.N.X := A.ν.eX.symm with he
  have hee : ∀ x, A.ν.eX (e x) = x := A.ν.eX.apply_symm_apply
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  obtain ⟨ct, hct, hc⟩ := exists_lift_ct B.F ex hab.1 hab.2.1 (fun x : A.D₀.X => A.N.c (e x))
    (fun x y => by rw [map_add (f := _), A.N.c_add]) (fun a x z hz => A.ν.eA.injective (by
      rw [hF, hz, A.ν.c_eq, A.ν.c_eq, hee, hee, DegPre.cF, DegPre.cF, A.oa.c_lin, Category.assoc]))
  obtain ⟨T, hT1, hT2, hT⟩ := exists_log_frame hab e ct hc hw (fun a y x => by
    obtain ⟨r, hr, h⟩ := b1 a
    have h1 := h (e y) (e x)
    have h2 := hros a (star a) r hr (ct y) (ct x)
    rw [hee, hee, hc, hc] at h1
    rw [← h1, hct, hct]
    linear_combination -(A.N.τ (e (a • y)) (e x) : ℂ) * h2)
  have hact : ∀ (a : 𝓞 E) x, e (a • x) = A.act a (e x) := fun a x => by rw [ArcF.act, hee]
  let B' : An H :=
    { B with
      X := A.D₀.X
      acg := inferInstance
      free := inferInstance
      fin := inferInstance
      mod := inferInstance
      ct := ct
      ct_smul := hct
      T := T
      T_symm := hT1
      T_adj := hT2
      psi := fun x => A.N.ψ (e x) * fr (ct x)
      psi_neg := fun x => by
        rw [map_neg, map_neg, ← hab.2.2.2.2.2.2.1, ← hc, ← _root_.mul_assoc, A.N.even]
      psi_add := fun x y => by
        have h := hT x y
        rw [map_add (f := _), map_add (f := _), A.N.ψ_add]
        push_cast
        linear_combination -(A.N.ψ (e x) : ℂ) * A.N.ψ (e y) * h
      be := β.be.comp e.toIntLinearEquiv.toLinearMap e.toIntLinearEquiv.toLinearMap
      be_symm := fun x y => β.symm _ _
      be_pos := fun x hx => β.pos _ fun h => hx (e.map_eq_zero_iff.1 h)
      be_adj := fun a y x => by
        change β.be (e (a • y)) (e x) = β.be (e y) (e (star a • x))
        rw [hact, hact]
        exact hβ a _ _
      be_even := fun x => (dvd_mul_right 2 (k : ℤ)).trans (β.dvd _ _) }
  have hab' : IsAbFrame A.N.toNumB B' ex fr th := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hab
    refine ⟨a1, a2, a3, a4, a5, a6, a7, ⟨a8.1, fun l z => ?_⟩, a9⟩
    have := a8.2 l z
    rw [map_zero] at this ⊢
    exact this
  refine ⟨B', ⟨e, ex, fr, th, hab', hc, fun _ => rfl⟩, ⟨hact, ?_⟩, fun _ _ => rfl, ⟨hw, hchi, fun y => ?_⟩, hth, hsig⟩
  · rintro a g g' c c' v hg hg' hgg ⟨hv1, hv2⟩
    obtain ⟨r, hr, h⟩ := b2 a
    obtain ⟨h1, h2⟩ := h g g' c c' hg hg' hgg
    change c.b = ex v.2 at hv1
    refine ⟨A.ν.eA.injective (by rw [h1, hv1]; exact (hF a v.2).symm), fun x : A.D₀.X => ?_⟩
    have h3 := h2 (e x)
    have h4 : (c.s (e (star a • x)) : ℂ) * fr (ct (star a • x) + v.2) =
      eTwoPi (v.1 (star a • x)) * fr (ct (star a • x)) * fr v.2 := hv2 (star a • x)
    have h5 := hros (star a) a r hr (ct x) v.2
    rw [hee, hc, hv1] at h3
    rw [hct] at h4
    change (c'.s (e x) : ℂ) * fr (ct x + B.F a v.2) = eTwoPi (v.1 (star a • x)) * fr (ct x) * fr (B.F a v.2)
    refine mul_right_cancel₀ (mul_ne_zero (fr (B.F (star a) (ct x))).ne_zero (fr v.2).ne_zero) ?_
    rw [h3]
    linear_combination (c.s (e (star a • x)) : ℂ) * h5 + (fr (ct x) : ℂ) * fr (B.F a v.2) * h4
  · obtain ⟨t, ht, h⟩ := b3 H.w0 A.w0
    have h1 := h (e y)
    have h2 := hprim t ht (ct y)
    have h3 := hT y (H.w0 • y)
    rw [hee, hc] at h1
    rw [hct] at h3
    change ((A.N.ψ (e y) * fr (ct y) : ℂˣ) : ℂ) = eTwoPi (T y (H.w0 • y))
    refine mul_right_cancel₀ (mul_ne_zero (fr (ct y)).ne_zero (fr (B.F H.w0 (ct y))).ne_zero) ?_
    rw [Units.val_mul, ← h1]
    linear_combination (A.N.τ (e y) (e (H.w0 • y)) : ℂ) * h2 - h3

end GlobalTheory.Ex.Arch
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibPrim
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.FrameValue

theorem differentiable_quot {A : Over (Sp ℂ)} [GrpObj A] {X : Scheme.{0}} {L : LB X} {L' : LB A.left} (hL' : L'.IsLB)
    {φ : A.left ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) {g : ℕ} (u : HolUnif A L' g)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      fr z = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {ψ : K → (X ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen)
    {z : (Fin g → ℂ) → K → Fin g → ℂ} (hd : ∀ k, Differentiable ℂ fun v => z v k)
    (hz : ∀ v k, ((u.ex v).left ≫ φ) ≫ ψ k = (u.ex (z v k)).left ≫ φ) :
    Differentiable ℂ fun v => vF t ((u.ex v).left ≫ φ) J / ∏ k, fr (z v k) ^ ε k := by
  intro v₀
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex v₀).left ≫ φ) ⁻¹ᵁ L.wchart ψ j :=
    ⟨_, (le_preimage_wchart _ L ψ _).2 fun _ => hJ _⟩
  obtain ⟨i, hi⟩ : ∃ i : K → L'.ι, ∀ k, ⊤ ≤ (u.ex (z v₀ k)).left ⁻¹ᵁ L'.U (i k) := ⟨_, fun _ => le_chartAt hL' _⟩
  have key : ∀ v, ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j → ∀ k,
      ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L.wchart (fun _ : PUnit => φ) (fun _ => j k) := fun v hv k =>
    (le_preimage_wchart _ L _ _).2 fun _ => hz v k ▸ (le_preimage_wchart _ L ψ _).1 hv k
  obtain ⟨ho, hh⟩ := u.hol (φ ⁻¹ᵁ L.wchart ψ j) ((φ.app _).hom (t.s j).val)
  have hn : {v | ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j} ∈ nhds v₀ := ho.mem_nhds hj
  have d₁ : DifferentiableAt ℂ (fun v => valAt' ((u.ex v).left ≫ φ) (L.wchart ψ j) (t.s j).val) v₀ := by
    refine (hh.differentiableAt (ho.mem_nhds hj)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
    exact ((valueRules _ (u.ex v).left).2.2.2.1 _ φ _ _).symm
  let G : K → (Fin g → ℂ) → ℂ := fun k x =>
    valAt' (u.ex x).left (L.wchart (fun _ : PUnit => φ) (fun _ => j k) ⊓ L'.U (i k)) (w.s (fun _ => j k, i k)).val *
      u.fr (i k) x
  have h₀ := fun k => (le_preimage_inf _ _ _).2 ⟨key v₀ hj k, hi k⟩
  have n₀ : ∀ k, G k (z v₀ k) ≠ 0 := fun k =>
    mul_ne_zero (val_unit_ne_zero _ valueRules (h₀ k) _) (u.fr_ne _ _ (hi k))
  have d₂ : DifferentiableAt ℂ (fun v => ∏ k, G k (z v k) ^ ε k) v₀ := by
    have a : ∀ k, DifferentiableAt ℂ (fun v => G k (z v k) ^ ε k) v₀ := fun k => by
      refine DifferentiableAt.zpow ?_ (Or.inl (n₀ k))
      refine DifferentiableAt.comp v₀ (g := G k) ?_ (hd k v₀)
      exact ((u.hol _ _).2.differentiableAt ((u.hol _ 0).1.mem_nhds (h₀ k))).fun_mul
        ((u.fr_hol (i k)).differentiableAt ((u.hol _ 0).1.mem_nhds (hi k)))
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (a k).hasFDerivAt).differentiableAt
  refine (d₁.fun_mul (d₂.fun_inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n₀ k)))).congr_of_eventuallyEq ?_
  have hn' : ∀ᶠ v in nhds v₀, ∀ k, ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L'.U (i k) :=
    Filter.eventually_all.2 fun k => (hd k v₀).continuousAt.preimage_mem_nhds ((u.hol _ 0).1.mem_nhds (hi k))
  filter_upwards [hn, hn'] with v hv hv'
  have hJv : ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ fun k => J (((u.ex v).left ≫ φ) ≫ ψ k) :=
    (le_preimage_wchart _ L ψ _).2 fun _ => hJ _
  have e₁ := (val_gen _ valueRules t ht _ _ hJv hv).trans
    (congrArg (· * _) (val_linComb _ valueRules L ψ ε _ _ hJv hv))
  have e₂ : ∀ k, fr (z v k) = valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val * G k (z v k) := fun k => by
    rw [hfr _ _ (hv' k), hz v k, ← _root_.mul_assoc]
    refine congrArg (· * _) ((GlobalTheory.PowUnif.val_iso _ L L' (fun _ : PUnit => φ) w hw _ _ _ _
      ((le_preimage_wchart _ L _ _).2 fun _ => hJ _) (key v hv k) (hv' k) (hv' k)).trans ?_)
    rw [GlobalTheory.PowUnif.val_g_self hL' _ _ (hv' k), inv_one, _root_.mul_one, Fintype.prod_unique]
  have n : (∏ k, valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (val_unit_ne_zero _ valueRules
      ((le_preimage_inf _ _ _).2 ⟨hJ _, (le_preimage_wchart _ L ψ _).1 hv k⟩) _)
  simp only [e₂, mul_zpow, Finset.prod_mul_distrib]
  exact (congrArg (· / _) e₁).trans ((mul_div_mul_left _ _ n).trans (div_eq_mul_inv _ _))

theorem vF_eq_one {X Y Z : Scheme.{0}} {L : LB X} {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} {e : Z ⟶ Y}
    (h : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t e) (LB.oneGen L)) (y : Sp ℂ ⟶ Z) : vF t (y ≫ e) J = 1 := by
  have h₁ : ⊤ ≤ y ⁻¹ᵁ L.wchart (fun k => e ≫ ψ k) fun k => J (y ≫ e ≫ ψ k) :=
    (le_preimage_wchart _ L _ _).2 fun _ => hJ _
  have h₂ : ⊤ ≤ y ⁻¹ᵁ L.wchart (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim :=
    (le_preimage_wchart _ L _ _).2 fun k => k.elim
  have h₃ := (le_preimage_inf y _ _).2 ⟨h₁, h₂⟩
  have := congrArg (fun q : Γ(Z, _)ˣ => valAt' y _ q.val) (h (fun k => J (y ≫ e ≫ ψ k)) PEmpty.elim
    (fun a b q => congrArg (fun q => J (y ≫ q)) q) (fun a => a.elim) (fun _ b => b.elim))
  have e₁ := (val_res y valueRules inf_le_left h₃ _).symm.trans (this.trans (val_res y valueRules inf_le_right h₃ _))
  obtain ⟨r, hr⟩ := (valueRules Z y).2.1 _ h₂
  exact ((val_res y valueRules _ h₁ _).trans (val_pullU y valueRules e _ _)).symm.trans
    (e₁.trans ((hr _).trans (map_one r)))

theorem fibPrim : FibPrimSt := by
  rintro R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, rfl, hφ, hw, hAH, -, -, -, hex, hfr⟩ f hf F hF hFf hH Ef hEf t ⟨ht, h₀⟩
  change u.IsAH Hm χ at hAH
  have hL := P'.isLB
  have add : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => Over.OverMorphism.ext (by
    rw [hex, u.ex_add, ← hφ.2 _ _ _ (pushPt hφ.1.w (u.ex z)) (pushPt hφ.1.w (u.ex z')) rfl rfl]
    exact mul_left_congr (Category.id_comp _) _ _ _ _ (hex z).symm (hex z').symm)
  have zero : ex 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have per : ∀ (l : u.Λ) z, (ex (z + l)).left = (ex z).left := fun l z => by
    rw [hex, hex, ex_add_period u z l l.2]
  have fac : ∀ (l : u.Λ) z, (fr z : ℂ) = ahFactor Hm χ l z * fr (z + l) := fun l z => by
    have hi := le_chartAt hL (u.ex z).left
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P'.L.U (chartAt hL (u.ex z).left) := by
      rw [ex_add_period u z l l.2]; exact hi
    rw [hfr _ _ hi, hfr _ _ hi', hAH.2.2.2 l _ z hi, per, ex_add_period u z l l.2, mul_left_comm]
    rfl
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → ℂ, ∀ v, V v = vF t (ex v).left J /
      (fr (v + F v) * ((fr v : ℂ) ^ 2)⁻¹ * (fr (F v) : ℂ)⁻¹ * fr 0 ^ 2) := ⟨_, fun _ => rfl⟩
  have dF : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have hd : Differentiable ℂ V := by
    have := differentiable_quot hL hw u hJ (fr := fun z => fr z) (fun z i hi => by rw [← hex]; exact hfr z i hi) ht
      (z := fun v => ![v + F v, v, F v, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop) (fun v k => by
        rw [← hex, ← hex]
        fin_cases k
        · exact congrArg (fun m => m.left) (show ex v ≫ (𝟙 _ * f) = ex (v + F v) by
            rw [MonObj.comp_mul, Category.comp_id, ← hFf, add])
        · exact Category.comp_id _
        · exact congrArg (fun m => m.left) (hFf v).symm
        · exact congrArg (fun m => m.left) ((MonObj.comp_one (ex v)).trans zero.symm))
    convert this using 2 with v
    rw [hV, hex]
    simp [Fin.prod_univ_four]
  have hper : ∀ (l : u.Λ) v, V (v + l) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ / χ l * V v := fun l v => by
    have a₁ := fac (l + ⟨F l, hF l l.2⟩) (v + F v)
    have a₂ := fac l v
    have a₃ := fac ⟨F l, hF l l.2⟩ (F v)
    have c := chi_add hL hAH l ⟨F l, hF l l.2⟩
    have s : Complex.exp (Real.pi * Complex.I * (hermForm Hm l (F l)).im) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ := by
      rw [← hEf l ⟨F l, hF l l.2⟩, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    have x : Complex.exp (Real.pi * hermForm Hm (v + F v) (l + F l) + Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) =
        Complex.exp (Real.pi * hermForm Hm v l + Real.pi / 2 * hermForm Hm l l) ^ 2 *
        Complex.exp (Real.pi * hermForm Hm (F v) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      simp only [EigenNorm.hermForm_add_left, EigenNorm.hermForm_add_right]
      push_cast
      linear_combination (-Real.pi : ℂ) * hH v l - (Real.pi / 2 : ℂ) * hH l l
    rw [s] at c
    rw [hV, hV, per, a₁, a₂, a₃, map_add (f := _), add_add_add_comm v]
    simp only [ahFactor, c, Submodule.coe_add, x]
    have n := chi_ne_zero hAH l
    have n' := chi_ne_zero hAH ⟨F l, hF l l.2⟩
    have n'' : (-1 : ℂ) ^ Ef l ⟨F l, hF l l.2⟩ ≠ 0 := zpow_ne_zero _ (by simp)
    field_simp
  have hc := const_of_norm_periodic u hd (fun l v => by
    rw [hper, norm_mul, norm_div, hAH.2.2.1, norm_zpow, norm_neg, norm_one, one_zpow, div_one, _root_.one_mul])
  have h1 : V 0 = 1 := by
    have e : (ex 0).left = (TF (R := R) ℂ).hom ≫ eSec D.P.A := by rw [zero, Hom.one_def]; simp [eSec]
    rw [hV, e, vF_eq_one hJ h₀, map_zero, add_zero]
    have := (fr 0).ne_zero
    field_simp
  refine ⟨fun l => ?_, fun z => ?_⟩
  · have := hper l 0
    rw [hc _ 0, h1, _root_.mul_one] at this
    exact ((div_eq_one_iff_eq (chi_ne_zero hAH l)).1 this.symm).symm
  · have := (hV z).symm.trans ((hc z 0).trans h1)
    have a := (fr z).ne_zero
    have b := (fr (F z)).ne_zero
    have c := (fr (z + F z)).ne_zero
    have d := (fr 0).ne_zero
    field_simp at this
    exact this

theorem fibPrim_of_laws : Laws → FibPrimSt := fun _ => fibPrim

end GlobalTheory.Ex.Arch.FibPrim
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.ActValues
open GlobalTheory.TorusExt GlobalTheory.ValuesExist

section Val
variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : (Sp F ⟶ X) → L.ι}

theorem vF_corr {z : Sp F} (hJ : Good L z J) {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y' ⟶ X)} {ε'' : K'' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {u : LB.Gen (LB.LinComb L φ' ε')}
    {t' : LB.Gen (LB.LinComb L φ'' ε'')} {h : Y' ⟶ Y}
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ u h)) t') (r : Sp F ⟶ Y') :
    vF t r J * vF u (r ≫ h) J = vF t' r J := by
  have e := val_corr hJ H r
  rw [val_mul hJ, val_pull hJ] at e
  rw [← coe_val t r hJ, ← coe_val u _ hJ, ← coe_val t' r hJ, ← e, map_mul, Units.val_mul]
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N)

theorem good (z : Sp F) : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem psi_eq (y : N.X) :
    (N.ψ y : F) = vF (LB.mulGen D.P.L _ _ _ _ (D.psi (ν.eX y)) D.rigK) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  rw [ν.ψ_eq, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← Units.val_mul, ← map_mul]
  exact congrArg (fun q => (((stalkUnits z).symm q : Fˣ) : F))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm

theorem tau_eq (a b : N.X) : (N.τ a b : F) = vF (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  let e := (stalkUnits z).symm
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z ν.J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z ν.J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have hψ : ∀ y, N.ψ y = e (p (ν.eX y) * ρ) := fun y => Units.ext ((psi_eq ν y).trans
    ((coe_val _ _ hJ).symm.trans (congrArg (fun q => ((e q : Fˣ) : F)) (val_mul hJ _ _ _))))
  refine Eq.trans ?_ (coe_val _ _ hJ)
  rw [hτ, NumD.τ, hψ, hψ, hψ, ← map_div, ← map_div, map_add (f := _)]
  refine congrArg (fun q => ((e q : Fˣ) : F)) (Additive.ofMul.injective ?_)
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem brAct : Laws → BrActSt := by
  intro hL R _ _ D _ _ F _ _ _ N ν O _ _ _ oa
  have hJ := good ν (IsLocalRing.closedPoint F)
  refine ⟨fun a => ?_, fun a => ?_, fun w₀ hw => ?_⟩
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨r, ⟨hr, r₀⟩, fun y y' => ?_⟩
    have h := vF_corr hJ (oa.tau_bal a r hr r₀ (ν.eX y) (ν.eX y')) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.pt2 (ν.eX y) (ν.eX y') = (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left := by
      rw [ν.c_eq, ν.c_eq]
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
      refine congrArg CommaMorphism.left (show κ ≫ lift _ _ = _ from ?_)
      simp only [comp_lift, comp_toUnit_assoc]
    rw [tau_eq ν, tau_eq ν, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← h2]
    exact h
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ hr
    refine ⟨r, ⟨hr, r₀⟩, fun g g' c c' hc hc' hg => ⟨by rw [hc.1, hc'.1, hg.1], fun χ => ?_⟩⟩
    have h := vF_corr hJ (hg.2 r hr r₀ (ν.eX χ)) (𝟙 (Sp F))
    rw [hc'.2, hc.2, AddEquiv.apply_symm_apply, ν.c_eq, hc.1]
    exact h.symm.trans (congrArg (fun q => _ * vF r q ν.J) (Category.id_comp _))
  · obtain ⟨t, ht, t₀, hy⟩ := hw
    refine ⟨t, ⟨ht, t₀⟩, fun y => ?_⟩
    have h := vF_corr hJ (hy (ν.eX y)) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.xK (ν.eX y) = (ν.eA (N.c y)).left := by
      rw [ν.c_eq]
      exact (Category.assoc _ _ _).symm
    rw [tau_eq ν, psi_eq ν, AddEquiv.apply_symm_apply, ← h2]
    exact h

end GlobalTheory.ActValues
end
