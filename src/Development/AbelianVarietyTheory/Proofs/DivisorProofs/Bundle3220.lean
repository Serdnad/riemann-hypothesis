module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

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

namespace GlobalTheory.HeatShiftW

theorem heat_div_monomial' (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) :
    letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (e : ℕ), 1 ≤ e → ∀ (mu α : P.D.toPre.X) (N : Fin m → ℕ) (σ σ' : P.D.toPre.SecB e α) (σ₁ σ₁u σ₁' σ₁u' : P.D.toPre.SecB e (α + e • mu)), TActs Y h e α σ σ' → ShiftEq P.D.toPre e mu α σ σ₁ 0 σ₁ → ShiftEq P.D.toPre e mu α σ' σ₁' 0 σ₁' → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁ x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u x z J) → (∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁' x z J = gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval σ₁u' x z J) → ∃ σ₁u'' : P.D.toPre.SecB e (α + e • mu), TActs Y h e (α + e • mu) σ₁u σ₁u'' ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ P.D.toPre.P.A.left) (z : Z) J, Good P.D.toPre.P.L z J → sval σ₁u'' x z J = sval σ₁u' x z J - gs (x ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i)) * sval σ₁u x z J := by
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hb hdef e he mu α N σ σ' σ₁ σ₁u σ₁' σ₁u' hT hS hS' hv hv'
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq h hb hdef ⊢
  letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
  let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
    { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
  have hA1 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁
  have hA2 := heat_acts_on_terms (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd D' h hb e (α + e • mu) σ₁u
  obtain ⟨σ₁'', hA1⟩ := hA1
  obtain ⟨σ₁u'', hA2⟩ := hA2
  refine ⟨σ₁u'', hA2, ?_⟩
  have hd : ShiftEq P.D.toPre e mu α σ' σ₁'' 0 σ₁ := hdef e mu α σ σ' σ₁ σ₁'' he hS hT hA1
  obtain ⟨⟨u, hu, hc⟩, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_fe (D := P.D.toPre) (F := FractionRing (ChartRing k m d))
    GlobalTheory.SemiRigid.globalFns e mu α
  have hU : ∀ z J, Good P.D.toPre.P.L z J → sval σ₁'' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J =
      sval σ₁' (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J := by
    intro z J hJ
    have E1 := GlobalTheory.HeatDefect.shiftEq_at hd u hu hc (𝟙 _) z J hJ
    have E2 := GlobalTheory.HeatDefect.shiftEq_at hS' u hu hc (𝟙 _) z J hJ
    simp only [Category.id_comp, GlobalTheory.HeatDefect.scal_zero, zero_mul, add_zero] at E1 E2
    rw [E1, E2]
  obtain ⟨τ₁, τ₁'', t1, t1'', a1⟩ := hA1
  obtain ⟨τu, τu'', tu, tu'', a2⟩ := hA2
  have hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → sval τ₁ r z J = gs (r ≫ Y.H.hom) z ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ N i)) * sval τu r z J := by
    intro Z r z J hJ
    let x : Over.mk (r ≫ Y.H.hom) ⟶ Y.H := Over.homMk r rfl
    have e1 := t1 _ x z J hJ
    have e2 := tu _ x z J hJ
    have e3 := hv Z (r ≫ Y.q.left) z J hJ
    have hw : (r ≫ Y.q.left) ≫ P.D.toPre.P.A.hom = r ≫ Y.H.hom := by rw [Category.assoc, Over.w]
    rw [hw] at e3
    change sval τ₁ r z J = _ at e1
    change sval τu r z J = _ at e2
    rw [Over.comp_left] at e1 e2
    change _ = sval σ₁ (r ≫ Y.q.left) z J * _ at e1
    change _ = sval σ₁u (r ≫ Y.q.left) z J * _ at e2
    rw [e1, e2, e3, _root_.mul_assoc]
  have hτ'' := GlobalTheory.T.heatOperator_const_mul_derivation_term (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y n' (fun a => v' a) dd hdd D' h e
    (∏ i, bdParam k m d i ^ N i) τ₁ τ₁'' τu τu'' a1 a2 hτ
  have hP := GlobalTheory.T.fourierTerm_identity_descends_genericFibre (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y e (α + e • mu) σ₁'' σ₁u'' σ₁u τ₁'' τu'' τu
    (∏ i, bdParam k m d i ^ N i) (2 * (e : ChartRing k m d) * D' (∏ i, bdParam k m d i ^ N i)) t1'' tu'' tu hτ''
  have hpow : ∀ (x c : ChartRing k m d), D' x = c * x → ∀ n : ℕ, D' (x ^ n) = (n : ChartRing k m d) * c * x ^ n := by
    intro x c hx n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, ih, hx, smul_eq_mul, smul_eq_mul]
      push_cast; ring
  have hDt : ∀ s : Finset (Fin m), D' (∏ i ∈ s, bdParam k m d i ^ N i) =
      (∑ i ∈ s, (N i : ChartRing k m d) * q i) * ∏ i ∈ s, bdParam k m d i ^ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih,
        hpow _ (q a) (hq a) (N a), smul_eq_mul, smul_eq_mul]
      ring
  have hne0 : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  have hne : (∏ i, bdParam k m d i ^ N i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne0 i)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ P.D.toPre.P.A.left) (z : Z) (c : ChartRing k m d),
      gs (r ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom c) =
        GlobalTheory.HeatMod.germConstHom (r ≫ P.D.toPre.P.A.hom) z c := fun r z c =>
    (GlobalTheory.HeatTermLin.gs_constFn _ r z c).symm.trans (GlobalTheory.HeatMod.gs_constFn_eq_germConstHom _ r z c)
  have key := GlobalTheory.T.secB_eq_everywhere_of_generic_agree_const (ChartRing k m d) P.D.toPre e (α + e • mu) σ₁u''
    (σ₁u' - constFn P.D.toPre.P.A.hom ⊤ (2 * (e : ChartRing k m d) * ∑ i, (N i : ChartRing k m d) * q i) • σ₁u)
    (∏ i, bdParam k m d i ^ N i) hne (by
      intro z J hJ
      have a1 := hP z J hJ
      have a2 := hU z J hJ
      have a3 := hv' _ (DegPre.prB P.D.toPre (FractionRing (ChartRing k m d))).left z J hJ
      rw [GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ]
      rw [hDt] at a1
      simp only [hg] at a1 a3 ⊢
      simp only [map_mul, map_natCast, map_ofNat] at a1 ⊢
      linear_combination a2 + a3 - a1)
  intro Z x z J hJ
  rw [key Z x z J hJ, GlobalTheory.HeatMod.sval_sub_constFn_smul _ _ _ _ _ _ hJ, hg]

end GlobalTheory.HeatShiftW

theorem GlobalTheory.HeatShiftW.exists_int_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∃ (Nv : Fin m → ℕ) (w : ∀ (z : P.D.toPre.P.A.left) (J : (P.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), (P.D.toPre.P.A.left.presheaf.stalk z)ˣ) (Sh : P.D.toPre.SecB N 0 → P.D.toPre.SecB N (0 + N • y)), ∀ x : P.D.toPre.SecB N 0, (∀ (z : P.D.toPre.P.A.left) (J : (P.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → sval (Sh x) (𝟙 _) z J = sval x (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left z J * (w z J).val) ∧ ∃ x₁ : P.D.toPre.SecB N (0 + N • y), ShiftEq P.D.toPre N y 0 x x₁ 0 x₁ ∧ ∀ (Z : Scheme.{0}) (X : Z ⟶ P.D.toPre.P.A.left) (z : Z) (J : (Z ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι), Good P.D.toPre.P.L z J → sval x₁ X z J = gs (X ≫ P.D.toPre.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i ^ Nv i)) * sval (Sh x) X z J := by
  intro E _ _ _ H k _ _ m d t P gam hmon y N hN
  obtain ⟨Nv, uR, huR, hu⟩ := GlobalTheory.T.exists_integralGenerator_translationBundle_monomial E H k m d t P gam hmon y N hN
  obtain ⟨w, Sh, hSh⟩ := GlobalTheory.T.exists_integralShift_of_generator_up_to_const (ChartRing k m d) P.D.toPre y N (∏ i, bdParam k m d i ^ Nv i) uR huR hu
  exact ⟨Nv, w, Sh, hSh⟩



theorem GlobalTheory.HeatShiftW.shift_ratio_rem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (y : P.D.toPre.X) (N : ℕ), 1 ≤ N → ∀ (σ σ' σp σp' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f g : Γ(P.D.toPre.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f → TActs Y h N 0 σ σp → TActs Y h N 0 σ' σp' → GlobalTheory.HeatRatio.IsRem P.D.toPre σ' σp σp' U f g → ∃ (β : P.D.toPre.X) (s s' sp sp' : P.D.toPre.SecB N β), GlobalTheory.HeatRatio.IsRatio P.D.toPre s s' ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) ∧ TActs Y h N β s sp ∧ TActs Y h N β s' sp' ∧ GlobalTheory.HeatRatio.IsRem P.D.toPre s' sp sp' ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom g) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hb hdef y N hN σ σ' σp σp' U f g hr a1 a2 hrem
  obtain ⟨Nv, w, Sh, hSh⟩ := GlobalTheory.HeatShiftW.exists_int_shift E H k m d t P gam hmon y N hN
  obtain ⟨e1, x1, s1, v1⟩ := hSh σ
  obtain ⟨e2, x2, s2, v2⟩ := hSh σ'
  obtain ⟨e3, x3, s3, v3⟩ := hSh σp
  obtain ⟨e4, x4, s4, v4⟩ := hSh σp'
  obtain ⟨sp, hsp, esp⟩ := GlobalTheory.HeatShiftW.heat_div_monomial' E H k m d t P Y n' v' dd hdd D q hq h hb hdef N hN y 0 Nv
    σ σp x1 (Sh σ) x3 (Sh σp) a1 s1 s3 v1 v3
  obtain ⟨sp', hsp', esp'⟩ := GlobalTheory.HeatShiftW.heat_div_monomial' E H k m d t P Y n' v' dd hdd D q hq h hb hdef N hN y 0 Nv
    σ' σp' x2 (Sh σ') x4 (Sh σp') a2 s2 s4 v2 v4
  set T := (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left with hT
  have hsv : ∀ (x : P.D.toPre.SecB N 0) (z : P.D.toPre.P.A.left) (J : (P.D.toPre.P.A.left ⟶ P.D.toPre.P.A.left) → P.D.toPre.P.L.ι),
      Good P.D.toPre.P.L z J → sval x T z J = (T.stalkMap z).hom (sval x (𝟙 _) (T z) (fun ψ => J (T ≫ ψ))) := by
    intro x z J hJ
    have := GlobalTheory.HeatDefect.sval_comp_stalk x (𝟙 _) T z hJ
    rwa [Category.comp_id] at this
  have hgs : ∀ (z : P.D.toPre.P.A.left), T z ∈ U → ∀ a : Γ(P.D.toPre.P.A.left, U),
      gs (𝟙 _) z (T ⁻¹ᵁ U) ((T.app U).hom a) = (T.stalkMap z).hom (gs (𝟙 _) (T z) U a) := by
    intro z hz a
    have e := gs_pull (𝟙 _) T z U hz a
    rw [Category.id_comp] at e
    rw [e]
    have e' := GlobalTheory.HeatDefect.gs_comp_stalk T (𝟙 _) z U hz a
    rwa [Category.comp_id] at e'
  refine ⟨0 + N • y, Sh σ, Sh σ', sp, sp', ?_, hsp, hsp', ?_⟩
  · intro z hz J hJ
    have hJ' := GlobalTheory.HeatDefect.good_comp T z hJ
    obtain ⟨hu, he⟩ := hr (T z) hz _ hJ'
    rw [e1 z J hJ, e2 z J hJ, hsv σ z J hJ, hsv σ' z J hJ, hgs z hz f, he, map_mul]
    exact ⟨(hu.map (T.stalkMap z).hom).mul (w z J).isUnit, by ring⟩
  · intro z hz J hJ
    have hJ' := GlobalTheory.HeatDefect.good_comp T z hJ
    obtain ⟨-, he⟩ := hr (T z) hz _ hJ'
    have hm := hrem (T z) hz _ hJ'
    rw [esp _ (𝟙 _) z J hJ, esp' _ (𝟙 _) z J hJ, e1 z J hJ, e2 z J hJ, e3 z J hJ, e4 z J hJ, hsv σ z J hJ,
      hsv σ' z J hJ, hsv σp z J hJ, hsv σp' z J hJ, hgs z hz f, hgs z hz g, he, hm]
    simp only [map_add (f := _), map_mul]
    ring
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

theorem _root_.GlobalTheory.T.thetaMember_lies_over_rescale_frames : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  first | exact @GlobalTheory.GSep.over_rescale | exact GlobalTheory.GSep.over_rescale | (intros; apply GlobalTheory.GSep.over_rescale <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_centred_ext_tower : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), (∀ m : ℕ, m ≠ 0 → IsUnit (m : V)) → IsCN V → IsLocalHom ev → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ J : Ideal V, (J.map io).comap io = J) ∧ 𝔗.Ext ev io ev₂ := by
  intro I X₁ z₁ act _ 𝔗 z₂ hz V _ _ _ ev hunit hV hev _
  subst hz
  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ := (X₁.M.stalkHom (𝔗.p z₂)).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := stalk_isNoetherian_normal_fractionRing X₁ (𝔗.p z₂)
  letI : Algebra (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := (𝔗.X₂.M.stalkHom z₂).toAlgebra
  obtain ⟨hdom₂, hfr₂, hic₂, -⟩ := stalk_isNoetherian_normal_fractionRing 𝔗.X₂ z₂
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.Poinc.integralClosure_galois_finite_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁
  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom (𝔗.p z₂))).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdom; haveI := hfr; haveI := hic; haveI := hdom₂; haveI := hfr₂; haveI := hic₂
  haveI : Algebra.IsInvariant (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) :=
    ⟨fun b hb => hfix b hb⟩
  haveI : Module.Finite (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfin
  haveI : Finite (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfinA

  haveI : CharZero V := hV.2.2.2
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨K', _, _, β, hK'fd, -, hβ⟩ := GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) hinj (FractionRing V)
    ((algebraMap V (FractionRing V)).comp ev)
  haveI := hK'fd

  have hK'u : IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) := hunit _ Module.finrank_pos.ne'
  obtain ⟨V', _, _, _, io, j, hV', hioi, hiof, hiol, hcon, hjinj, hj, hjr⟩ := GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank V hV K' hK'u
  have hβmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, β b ∈ j.range := by
    intro b
    obtain ⟨P, hPm, hP⟩ := integralClosure.isIntegral b
    obtain ⟨y, hy⟩ := hjr (β b) ⟨P.map ev, hPm.map ev, by
      rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hβ, ← Polynomial.hom_eval₂, hP, map_zero]⟩
    exact ⟨y, hy⟩
  let jr : V' ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hjinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let β' : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* V' := jr.symm.toRingHom.comp (β.codRestrict j.range hβmem)
  have hβ' : ∀ b, j (β' b) = β b := fun b => congrArg Subtype.val (jr.apply_symm_apply ⟨β b, hβmem b⟩)

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) := (𝔗.p.stalkMap z₂).hom.toAlgebra
  have hg1 : ∀ x : (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), 𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) :=
    fun x => (GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p 𝔗.p_pt z₂ x)
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq fun x => (hg1 x).symm
  have hinj₂ := 𝔗.X₂.M.stalkHom_injective z₂
  have hBmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, (b : 𝔗.X₂.Ω₁) ∈ (𝔗.X₂.M.stalkHom z₂).range := fun b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (𝔗.X₂.M.Z.presheaf.stalk z₂)) (K := 𝔗.X₂.Ω₁)).1
      (IsIntegral.tower_top (A := (𝔗.X₂.M.Z.presheaf.stalk z₂)) b.2)
    exact ⟨y, hy⟩
  let e₂ : (𝔗.X₂.M.Z.presheaf.stalk z₂) ≃+* (𝔗.X₂.M.stalkHom z₂).range := RingEquiv.ofBijective (𝔗.X₂.M.stalkHom z₂).rangeRestrict
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), (𝔗.X₂.M.stalkHom z₂).rangeRestrict_surjective⟩
  let f : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* (𝔗.X₂.M.Z.presheaf.stalk z₂) :=
    e₂.symm.toRingHom.comp (((integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁).val : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] 𝔗.X₂.Ω₁).toRingHom.codRestrict _ hBmem)
  have hf : ∀ b, 𝔗.X₂.M.stalkHom z₂ (f b) = b := fun b => congrArg Subtype.val (e₂.apply_symm_apply ⟨_, hBmem b⟩)
  have hfB : ∀ (t : (𝔗.X₂.M.Z.presheaf.stalk z₂)) (h : 𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁), f ⟨_, h⟩ = t :=
    fun t h => hinj₂ (hf _)
  have hloc : IsLocalHom (f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁))) := by
    have h : f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = (𝔗.p.stalkMap z₂).hom :=
      RingHom.ext fun a => hinj₂ (by rw [RingHom.comp_apply, hf, hg1]; rfl)
    rw [h]; infer_instance
  have hint : ∀ t : (𝔗.X₂.M.Z.presheaf.stalk z₂), (∃ P : Polynomial (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), P.Monic ∧ P.eval₂ (𝔗.p.stalkMap z₂).hom t = 0) →
      𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := by
    rintro t ⟨P, hPm, hP⟩
    refine ⟨P, hPm, ?_⟩
    have h : algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ = (𝔗.X₂.M.stalkHom z₂).comp (𝔗.p.stalkMap z₂).hom := RingHom.ext fun x => (hg1 x).symm
    rw [h, ← Polynomial.hom_eval₂, hP, map_zero]
  have hsurj : ∀ y : (𝔗.X₂.M.Z.presheaf.stalk z₂), ∃ b s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ y * f s = f b := by
    intro y
    obtain ⟨b, s, hs, hys, hb, hs'⟩ := GlobalTheory.Poinc.finite_stalk_quot_integral _ _ 𝔗.p 𝔗.p_fin z₂ y
    refine ⟨⟨_, hint b hb⟩, ⟨_, hint s hs'⟩, ?_, ?_⟩
    · rw [hfB]; exact hs
    · rw [hfB, hfB]; exact hys
  have hker : ∀ b, f b = 0 → ∃ s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ s * b = 0 := fun b hb =>
    ⟨1, by rw [map_one]; exact isUnit_one, by
      rw [_root_.one_mul]; exact Subtype.ext (by rw [← hf b, hb, map_zero]; rfl)⟩
  haveI := hiol; haveI := hev
  have hβ'A : β'.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = io.comp ev := RingHom.ext fun a =>
    hjinj ((hβ' _).trans ((RingHom.congr_fun hβ a).trans (RingHom.congr_fun hj (ev a)).symm))
  obtain ⟨ev₂, hev₂, hcomp⟩ := GlobalTheory.twisted_lift_to_localisation (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (𝔗.X₂.M.Z.presheaf.stalk z₂)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) f hloc hsurj hker V' (io.comp ev) β' inferInstance hβ'A
  refine ⟨V', inferInstance, inferInstance, inferInstance, io, ev₂, hV', hioi, hiof, hiol, hcon, hev₂, fun x x₂ hx => ?_⟩
  have h : x₂ = f (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) x) := hinj₂ (by rw [hf]; exact hx)
  rw [h]
  exact RingHom.congr_fun hcomp x

end GlobalTheory.GSep
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep
open GlobalTheory.Points GlobalTheory.ZH GlobalTheory.Poinc.Sep.GalVal

theorem val_galois_conj : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂ → GlobalTheory.GSep.RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by

  intro I X₁ act 𝔗 z₂ V' _ _ ev₂ ev₂' σ h1 h2 hr hr' a
  have ha := hr' a a.2
  obtain ⟨x, d, hxd, hd, hu⟩ := exists_mul_eq_stalkHom (specializes_jK ev₂' _) ha
  obtain ⟨x', hx'⟩ := h2 x
  obtain ⟨d', hd'⟩ := h2 d
  have ex := h1 x x' hx'
  have ed := h1 d d' hd'
  have hsp' := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have hsp := RatModel.specializes_of_range_eq
    (RatModel.range_eq_singleton (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (IsLocalRing.closedPoint _))
  have e1 := RatModel.val_mul hsp' ha hd
  rw [hxd, val_stalkHom, val_stalkHom] at e1
  have hne := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ _) ⟨_, hd⟩).2 hu
  rw [val_stalkHom] at hne
  have hb := hr _ (𝔗.sR σ a).2
  have hd'' := RatModel.O_le_of_specializes (specializes_jK ev₂ (IsLocalRing.closedPoint _))
    (𝔗.X₂.M.stalkEquiv z₂ d').2
  have e2 := RatModel.val_mul hsp hb hd''
  have key : σ (a : 𝔗.X₂.Ω₁) * 𝔗.X₂.M.stalkHom z₂ d' = 𝔗.X₂.M.stalkHom z₂ x' := by
    rw [hd', hx', ← map_mul, hxd]
  rw [RatModel.coe_stalkEquiv, 𝔗.sR_eq, key, val_stalkHom, val_stalkHom, ← ed, ← ex] at e2
  rw [𝔗.sR_eq]
  exact mul_right_cancel₀ hne (e1.symm.trans e2)

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep
open GlobalTheory.Points


open GlobalTheory.ZH.RatModel in
theorem Tower.valF_app_p {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {U : X₁.M.Z.Opens} (hU : (U : Set X₁.M.Z).Nonempty) (a : Γ(X₁.M.Z, U)) :
    valF 𝔗.X₂.M.pt (𝔗.p ⁻¹ᵁ U) (𝔗.p.app U a) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (valF X₁.M.pt U a) := by
  refine (valR_comp 𝔗.X₂.M.pt 𝔗.p U a).symm.trans ?_
  rw [𝔗.p_pt]
  exact valR_spMap_comp _ X₁.M.pt U (X₁.M.top_le_preimage_pt hU) a

theorem Tower.stalkHom_stalkMap_p {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    (z₂ : 𝔗.X₂.M.Z) (x : X₁.M.Z.presheaf.stalk (𝔗.p z₂)) :
    𝔗.X₂.M.stalkHom z₂ (𝔗.p.stalkMap z₂ x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) := by
  obtain ⟨U, hz, f, rfl⟩ := X₁.M.Z.presheaf.germ_exist x
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ hz f]
  exact (RatModel.stalkHom_germ (M := 𝔗.X₂.M) (U := 𝔗.p ⁻¹ᵁ U) hz _).trans (𝔗.valF_app_p ⟨_, hz⟩ f)

theorem Tower.val_comp_p {I : Type} {X₁ : GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    {K : Type} [Field K] (y : Sp K ⟶ 𝔗.X₂.M.Z) (w : Sp K) {x : X₁.Ω₁} (hx : x ∈ X₁.M.O (𝔗.p (y w))) :
    X₁.M.val (y ≫ 𝔗.p) x = 𝔗.X₂.M.val y (algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ x) := by
  obtain ⟨U, a, hz, rfl⟩ := hx
  have h1 : Set.range y ⊆ (𝔗.p ⁻¹ᵁ U : 𝔗.X₂.M.Z.Opens) := by
    rw [RatModel.range_eq_singleton y w, Set.singleton_subset_iff]
    exact hz
  rw [← 𝔗.valF_app_p ⟨_, hz⟩ a, RatModel.val_valF h1,
    RatModel.val_valF (U := U) (by rintro _ ⟨w', rfl⟩; exact h1 ⟨w', rfl⟩)]
  exact valR_comp y 𝔗.p U a

theorem Tower.val_om_ext : ∀ {I : Type} {X₁ : GlobalTheory.GSep.GSet} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : GlobalTheory.GSep.Tower X₁ act) {z₁ : X₁.M.Z} {z₂ : 𝔗.X₂.M.Z}, 𝔗.p z₂ = z₁ → ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.RegAt X₁ z₁ ev → ∀ a : X₁.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.om a) = f (X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) := by
  intro I X₁ act 𝔗 z₁ z₂ hz V V' _ _ _ _ ev io ev₂ f hf hio hext hreg a
  subst hz
  have e1 : ev₂.comp (𝔗.p.stalkMap z₂).hom = io.comp ev :=
    RingHom.ext fun x => hext.2 x _ (𝔗.stalkHom_stalkMap_p z₂ x)
  have e2 : jK V' ≫ spMap io = spMap f ≫ jK V := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hf v).symm
  have h1 : (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) ≫ 𝔗.p =
      spMap f ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) := by
    have e3 : spMap ev₂ ≫ Spec.map (𝔗.p.stalkMap z₂) = spMap io ≫ spMap ev := by
      show Spec.map (CommRingCat.ofHom ev₂) ≫ Spec.map (CommRingCat.ofHom (𝔗.p.stalkMap z₂).hom) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc (spMap ev₂), e3,
      Category.assoc, ← Category.assoc (jK V'), e2]
    simp only [Category.assoc]
  have hmem := hreg a a.2
  have hp : 𝔗.p ((jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (closedPoint (FractionRing V'))) =
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) (closedPoint (FractionRing V)) := by
    have e := congrArg (fun q : Sp (FractionRing V') ⟶ X₁.M.Z => q (closedPoint (FractionRing V'))) h1
    refine e.trans ?_
    show (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (𝔗.p z₂)) ((spMap f) (closedPoint (FractionRing V'))) = _
    rw [Subsingleton.elim ((spMap f) (closedPoint (FractionRing V'))) (closedPoint (FractionRing V))]
  rw [𝔗.om_eq, ← 𝔗.val_comp_p (K := FractionRing V') _ (closedPoint (FractionRing V')) (hp ▸ hmem), h1,
    RatModel.val_spMap_comp_field (K := FractionRing V) f _ (closedPoint (FractionRing V)) hmem]

end GlobalTheory.GSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic


theorem _root_.GlobalTheory.T.thetaMember_torsion_frame_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b → (∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J) →
  ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J := by
  first | exact @GlobalTheory.GSep.FrameUniq.frame_val_eq | exact GlobalTheory.GSep.FrameUniq.frame_val_eq | (intros; apply GlobalTheory.GSep.FrameUniq.frame_val_eq <;> assumption)
end
