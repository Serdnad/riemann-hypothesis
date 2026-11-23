module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforwardStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle192
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle066
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

theorem exists_secsOver : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u x hx
  obtain ⟨w, hw⟩ := u.lb
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  have := ρ.P.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun q => spMap q) u.fac.symm
  have hx' : ∀ a, (x a).left ≫ u.φ = τ ≫ (ρ.pt a).left := hx
  obtain ⟨rig, hrig, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec u.A.A) (φ := fun _ => eSec ρ.P.A)
    (ε := fun _ => 1) (h := spMap u.yK) hw hL₀ hL₁ (fun _ => PolBaseChange.eSec_comm hp) ρ.rig ρ.rig_gen
  choose e he He using fun a => exists_gen_through (φ' := fun _ : Fin 1 => (x a).left) (h := τ) hw hL₀ hL₁
    (fun _ => hx' a) (ρ.fr a) (ρ.fr_tors a).2.1
  have hfr : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) := fun a =>
    FrameMove.isTorsFrame_move hp hw
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx' a) (ρ.fr_tors a) (he a) (fun z J J' hJ hJ' => by
        have := He a _ (𝟙 _) z J J' hJ hJ'
        rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this)
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, ρ.pt (n • a) = ρ.pt a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := ρ.pt_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => FrameMove.pow_eq_one_of hp (hx' _) (by
    rw [hpow, ← pow_mul]
    exact (ρ.fr_tors a).1)
  refine ⟨rig, e, th, s, hrig, hfr, fun a z J hJ => ?_, fun i a z J hJ => ?_,
    ⟨α, hα, ThetaGeom.norm_move hp τ hτ hL₀ hL₁ Hr vα ρ.α_norm,
      isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero⟩, fun a => ?_⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (He a) hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [ThetaGeom.val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (ThetaGeom.genThrough_pow τ (He a) S.N) (hs i)
      (ρ.ev_val i a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    exact q
  · obtain ⟨θ, hθ, H⟩ := ClassWeight.symLift_act_move hp τ hτ hw hL₀ hL₁ (hx' _).symm (hN a) (ρ.U_sym a)
      (fun l i => fn (algebraMap o S.R (S.ρ a l i))) (fun l i => cF u.V (y₀ (algebraMap o S.R (S.ρ a l i))))
      (fun l i => spMap_appTop_fn y₀ _) hs (ρ.U_act a)
    exact ⟨θ, hθ, fun i σ h => (ThetaGeom.comb_iff _ _ _).2 (H i σ h)⟩

end GlobalTheory.TestFibre
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.SecComb

theorem equiv_sum {K M J : Type} [CommRing K] [AddCommGroup M] [Module K M] [Fintype J] (ρ : M ≃ₗ[K] M)
    (c : J → K) (v w : J → M) (h : ∀ i, ρ (v i) = w i) : ρ (∑ i, c i • v i) = ∑ i, c i • w i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, h]

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

omit [IsDomain R] in
theorem ofSec_inj {t t' : SecA A F k}
    (h : (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) = SecM.ofSec A.A t') : t = t' := by
  have h' : t.f = t'.f := congrArg Subtype.val h
  cases t; cases t'; cases h'; rfl

theorem isComb_iff {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) :
    IsComb A s b t ↔ (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) =
      ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
  have e : ∀ j, ((∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)).1 j) =
      ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun H => Subtype.ext (funext fun j => (H j).trans (e j).symm),
    fun H j => (congrFun (congrArg Subtype.val H) j).trans (e j)⟩

omit [IsDomain R] in
theorem exists_rho (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    ∃ ρ : SecM A.A A.L (k : ℤ) (TFK (R := R) F) ≃ₗ[Γ((TFK (R := R) F).left, ⊤)]
      SecM A.A A.L (k : ℤ) (TFK (R := R) F), ∀ s s' : SecA A F k,
      IsActOf A.A A.L k θ s s' ↔ ρ (SecM.ofSec A.A s) = SecM.ofSec A.A s' := by
  have hL := A.isLB
  obtain ⟨ρ, hρ⟩ := ThetaAct.exists_equiv hL θ
  refine ⟨ρ, fun s s' => ?_⟩
  rw [ThetaAct.isActOf_iff hL]
  exact ⟨fun H => ThetaAct.sv_ext hL fun y J hJ => (hρ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ hJ⟩

end GlobalTheory.SecComb

namespace GlobalTheory


open SecComb in
theorem secComb_thetaAct : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  intro R _ _ A F _ _ k J _ s b
  refine ⟨⟨SecM.toSec A.A (∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)),
    (isComb_iff A _ _ _).2 rfl⟩, fun t t' h h' => ?_, fun θ s' t t' hs h => ?_, fun θ t => ?_,
    fun I _ M r a t hr h => ?_⟩
  · exact ofSec_inj A (((isComb_iff A _ _ _).1 h).trans ((isComb_iff A _ _ _).1 h').symm)
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    have e := (congrArg ρ ((isComb_iff A _ _ _).1 h)).trans
      (equiv_sum ρ (fun l => cF R (b l)) _ _ fun i => (hρ _ _).1 (hs i))
    exact ⟨fun H => (isComb_iff A _ _ _).2 (((hρ _ _).1 H).symm.trans e),
      fun H => (hρ _ _).2 (e.trans ((isComb_iff A _ _ _).1 H).symm)⟩
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    refine ⟨SecM.toSec A.A (ρ (SecM.ofSec A.A t)), (hρ _ _).2 rfl, fun t' h => ofSec_inj A ?_⟩
    exact ((hρ _ _).1 h).symm
  · rw [isComb_iff] at h ⊢
    rw [h]
    simp only [fun i => (isComb_iff A _ _ _).1 (hr i), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have e : cF R (∑ i, M i j * a i) = ∑ i, cF R (M i j * a i) := map_sum _ _ _
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_comm _ _).trans (map_mul _ _ _).symm

end GlobalTheory
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre.CombValue

open GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {x : TFK (R := R) F ⟶ A.A} {e : FrameAt A x}

theorem valIs_comb {J : Type} [Fintype J] {s : J → SecA A F k} {b c : J → F} {t : SecA A F k} (h : IsComb A s b t)
    (hs : ∀ i, ValIs A (s i) x e (c i)) : ValIs A t x e (∑ i, b i * c i) := fun z I hI => by
  have e₀ : SecM.ofSec A.A t = ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  let φ : SecM A.A A.L k (TFK (R := R) F) →+ (TFK (R := R) F).left.presheaf.stalk z :=
    AddMonoidHom.mk' (fun v => ThetaAct.sv v (ptSecT A.A x).left z I) fun a b => ThetaAct.sv_add a b _ z hI
  let ψ : F →+* (TFK (R := R) F).left.presheaf.stalk z := cstH (R := R) z
  have e₁ : ∀ a : F, @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z a) = ψ a := fun a => cst_eq z a
  refine (congrArg φ e₀).trans ((map_sum φ _ _).trans ?_)

  rw [e₁, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => (ThetaAct.sv_smul _ _ _ z hI).trans ?_
  rw [ThetaPtMove.ptSecT_fst, map_mul, _root_.mul_assoc, ← e₁, ← e₁]
  exact congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z (b i)) * ·) (hs i z I hI)

theorem valIs_smul {t t' : SecA A F k} {a c : F} (h : ∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j)
    (ht : ValIs A t x e c) : ValIs A t' x e (a * c) := by
  have := valIs_comb (J := Unit) (s := fun _ => t) (b := fun _ => a) (c := fun _ => c) (t := t')
    (fun j => (h j).trans (by rw [Fintype.sum_unique])) fun _ => ht
  rwa [Fintype.sum_unique] at this

theorem valIs_unique {t : SecA A F k} {c c' : F} (h : ValIs A t x e c) (h' : ValIs A t x e c') : c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem exists_valIs (hL : Laws) (he : e.IsGen) (t : SecA A F k) : ∃ c, ValIs A t x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem valIs_linear : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x), (∀ (J : Type) [Fintype J] (s : J → SecA A F k) (b c : J → F) (t : SecA A F k), IsComb A s b t → (∀ i, ValIs A (s i) x e (c i)) → ValIs A t x e (∑ i, b i * c i)) ∧ (∀ (t t' : SecA A F k) (a c : F), (∀ j, t'.f j = liftFun A.A _ (cF R a) * t.f j) → ValIs A t x e c → ValIs A t' x e (a * c)) ∧ (∀ (t : SecA A F k) c c', ValIs A t x e c → ValIs A t x e c' → c = c') ∧ (e.IsGen → ∀ t : SecA A F k, ∃ c, ValIs A t x e c) :=
  fun hL _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun _ _ _ _ _ _ h hs => valIs_comb h hs, fun _ _ _ _ h ht => valIs_smul h ht,
      fun _ _ _ h h' => valIs_unique h h', fun he t => exists_valIs hL he t⟩

end GlobalTheory.TestFibre.CombValue
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestValuation

open GlobalTheory.ZH.PsiForm

theorem norm_eq_one_of_isUnit {o F : Type} [CommRing o] [NormedField F] (f : o →+* F) (h : ∀ a, ‖f a‖ ≤ 1)
    {a : o} (ha : IsUnit a) : ‖f a‖ = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have h3 : ‖f a‖ * ‖f b‖ = 1 := by rw [← norm_mul, ← map_mul, hb, map_one, norm_one]
  refine le_antisymm (h a) ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left (h b) (norm_nonneg _)
    _ = _ := mul_one _

theorem isUnit_of_norm_eq_one {V : Type} [CommRing V] [IsDomain V] {F : Type} [NormedField F]
    [Algebra (FractionRing V) F]
    (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))
    {a : V} (ha : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)‖ = 1) : IsUnit a := by
  have h0 : algebraMap V (FractionRing V) a ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at ha
    exact zero_ne_one ha
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) a)⁻¹).1 (by rw [map_inv₀, norm_inv, ha, inv_one])
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

theorem isPrimitiveRoot_map {o F : Type} [CommRing o] [IsDomain o] [Field F] [CharZero F] (f : o →+* F) {ζ : o}
    {n : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (f ζ) n := by
  have h1 := h.isRoot_cyclotomic hn
  have h2 := h1.map (f := f)
  rw [Polynomial.map_cyclotomic] at h2
  exact (Polynomial.isRoot_cyclotomic_iff_charZero hn).1 h2

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → CharZero u.V ∧ IsUnit ((ρ.n : ℕ) : u.V) ∧ AdmBase u.V (IsLocalRing.maximalIdeal u.V) ∧ ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 ∧ IsPrimitiveRoot (y₀ (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) ∧ ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ ∧ ValOver ϖ (PadicAlgCl p) v ∧ NormIs u l ϖ Q v lam := by
  intro o Ω _ _ _ hA S ρ p _ y₀ u l hy
  haveI : IsDomain o := hA.ded.toIsDomain
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  have hN : ‖((S.r * S.N : ℕ) : PadicAlgCl p)‖ = 1 := by
    have := norm_eq_one_of_isUnit (y₀.comp (algebraMap o S.R)) hy S.unit
    rwa [map_natCast] at this
  have hpos : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  refine ⟨?_, ?_, ⟨inferInstance, inferInstance, inferInstance, u.complete⟩, hN,
    isPrimitiveRoot_map (y₀.comp (algebraMap o S.R)) (pow_pos hpos 2) S.prim, ?_⟩
  · exact ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  · have h1 : IsUnit ((S.r * S.N : ℕ) : u.V) :=
      isUnit_of_norm_eq_one u.norm_le (by rw [map_natCast, map_natCast, hN])
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast ?_) h1
    rw [ρ.N_eq, ← pow_mul]
    exact Dvd.dvd.mul_left (dvd_pow_self _ (by have := ρ.two_le; omega)) _
  · choose Q hQ using QForm.exists_QVal hϖ u.D
    have h0 := norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
    have h1 := norm_lt_one_of_irreducible u.norm_le hϖ
    obtain ⟨v, hv1, hv2⟩ := GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff p _ h0 h1
    refine ⟨ϖ, Q, v, _, hϖ, ?_, neg_pos.2 (Real.log_neg h0 h1), hQ, fun χ => ?_, hv1, hv2⟩
    · intro c n hc
      rw [hv2, norm_of_hasVal u.norm_le hϖ hc, Rat.cast_intCast]
    · have hc := u.D.toPre.P.isLB.cover
      let x : Sp u.V := IsLocalRing.closedPoint u.V
      have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
        ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
      have e1 := l.q_eq χ (fun _ => i) htop
      have e2 := norm_of_hasVal u.norm_le hϖ
        (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => i) htop)
      exact neg_injective (Real.exp_injective (e1.symm.trans e2))

end GlobalTheory.TestValuation
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
noncomputable section
namespace GlobalTheory.TestFibre

theorem ptsOver_group_pairing : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∃ x, PtsOver u x) ∧ ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → (∀ a b, x (a + b) = x a * x b) ∧ (∀ a, x a ^ (S.r * S.N) = 1) ∧ (∀ z, z ^ (S.r * S.N) = 1 → ∃! a, x a = z) ∧ ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ a b).val) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨x₀, h₀, hadd, hinj, hsurj⟩ := utest_torsion_points o Ω S ρ p y₀ u
  refine ⟨⟨x₀, h₀⟩, fun x hx => ?_⟩
  obtain rfl : x = x₀ := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₀ a).symm) ((Over.w _).trans (Over.w _).symm))
  refine ⟨hadd, fun a => GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) u.cart (hx a) (ρ.fr_tors a).1,
    fun z hz => ?_, fun a b c hc => weilIs_uTest hL o Ω S ρ p y₀ u x hx a b c ?_⟩
  · obtain ⟨a, ha⟩ := hsurj z hz
    exact ⟨a, ha.symm, fun b hb => hinj (hb.trans ha)⟩
  · rw [hc, map_pow, map_pow]

end GlobalTheory.TestFibre
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem isComb_iff_expandsF_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ k hk w₀ hw J _ s Φ b t hs
  obtain ⟨hb, hl⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨h₁, h₂⟩ := hb F k hk w₀ hw
  have h0 : U.ExpandsF F k w₀ (SecOps.secZero : SecA A F k) (0 : Fam D.toPre F k) := by
    obtain ⟨σ, hσ⟩ := (h₁ (SecOps.secZero : SecA A F k)).exists
    have h := hl F k w₀ SecOps.secZero SecOps.secZero SecOps.secZero σ σ (-1) hσ hσ (fun j => ((add_zero _).trans (mul_zero _)).symm)
    rwa [neg_one_smul, neg_add_cancel] at h
  have key : ∀ S : Finset J, ∃ u : SecA A F k,
      (∀ j, u.f j = ∑ l ∈ S, liftFun A.A _ (cF R (b l)) * (s l).f j) ∧
        U.ExpandsF F k w₀ u (∑ i ∈ S, b i • Φ i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨SecOps.secZero, fun j => by rw [Finset.sum_empty]; rfl, by rw [Finset.sum_empty]; exact h0⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, eu⟩ := ih
      refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (cF R (b a))) (s a)) u,
        fun j => ?_, ?_⟩
      · rw [Finset.sum_insert ha, ← hu j]; rfl
      · rw [Finset.sum_insert ha]
        exact hl F k w₀ (s a) u _ (Φ a) _ (b a) (hs a) eu (fun j => rfl)
  obtain ⟨u, hu, eu⟩ := key Finset.univ
  constructor
  · intro h
    obtain rfl : t = u := SecOps.sec_ext fun j => (h j).trans (hu j).symm
    exact eu
  · intro h
    obtain rfl : t = u := (h₂ _).unique h eu
    exact hu

end GlobalTheory.TestFibre
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem perp_torus_point : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  intro h h₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x hx t
  obtain ⟨x', h₁, hadd, -, hs⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain rfl : x = x' := funext fun a => Over.OverMorphism.ext
    (u.cart.1.hom_ext ((hx a).trans (h₁ a).symm) (by rw [Over.w, Over.w]))
  obtain ⟨q, τ, a, b, c, d⟩ := PerpCharacter.exists_torus_point_eStd (laws_all h h₂).1 hT o Ω S ρ p y₀ u l x h₁ hadd hs
    t t.2
  exact ⟨τ, q, a, b, c, fun a β e => (d a β e).trans (by rw [map_pow, map_pow])⟩

end GlobalTheory.TestFibre
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN

theorem partI_of_inputs : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ModelsSt → N0 → PartI := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA hM h0
  refine ⟨h0, fun E _ _ _ H D hD Xo => ?_⟩
  obtain ⟨Y, hY, hgl⟩ := hM E H D hD Xo
  refine ⟨Y, fun p W hp hW => ⟨(hY p W hp hW).1, fun i => ⟨((hY p W hp hW).2 i).1, ?_, ?_⟩⟩, hgl⟩
  · exact GlobalTheory.T.model_uniformisation_of_abelianLocus_directImage h1 h2 h3 h4 h5 hE hU hP E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
  · exact GlobalTheory.T.arcFamily_fourthCondition_invertible_pushforward hT h1 h2 h3 h4 h5 h6 hE hU hP hH hA E H D _ _ _ _ _ p ((hY p W hp hW).1.1 i)
      ((hY p W hp hW).2 i).2

end GlobalTheory.LN
end

end

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x t) ∧ ∀ a β, l.yy a = QuotientAddGroup.mk β → (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζ) ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) := by
  first | exact @GlobalTheory.TestFibre.perp_torus_point | exact GlobalTheory.TestFibre.perp_torus_point | (intros; apply GlobalTheory.TestFibre.perp_torus_point <;> assumption)

end
end
