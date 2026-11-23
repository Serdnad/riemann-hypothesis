module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

section Lift

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem gtHol_toUnit_left :
    (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) = 𝟙 (Sp ℂ) := by
  have h : (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) =
      Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ := by
    have := Over.w (toUnit (Out.TF (R := ℂ) ℂ))
    exact (Category.comp_id _).symm.trans this
  refine h.trans ((Spec.map_comp _ _).symm.trans ?_)
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem gtHol_isLift (D₀ : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D₀.P.A D₀.P.L g) (p : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A)
    (χ : D₀.X) (c z : Fin g → ℂ) (hc : u.ex c = D₀.c χ) (hp : (show Sp ℂ ⟶ _ from p.left) = (u.ex z).left) :
    FrameValue.IsLift u (Out.DegPre.gtφ D₀ ℂ p χ) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] := by
  have e : ∀ w, (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ u.ex w).left) = (u.ex w).left := fun w =>
    (congrArg (fun q : Sp ℂ ⟶ Sp ℂ => q ≫ (u.ex w).left) gtHol_toUnit_left).trans (Category.id_comp _)
  have hp' : p = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hp.trans (e z).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  intro k
  refine (Category.id_comp _).trans ?_
  fin_cases k
  · refine Eq.trans ?_ (e (c + z))
    refine congrArg (fun m : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A => m.left) ?_
    rw [u.ex_add, MonObj.comp_mul, hc, ← hp']
    rfl
  · refine Eq.trans ?_ (e c)
    rw [hc]
    rfl
  · exact hp
  · refine Eq.trans ?_ (e 0)
    rw [h0]
    rfl

end Lift

theorem analyticDictionaryExp_holomorphic_over_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 z).b.left)) ∧ ∀ x j, DifferentiableOn ℂ (fun z => chiVal (Λ.ex0 z) x j) {z | ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j} ∧ ∀ z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j → chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hl : ∀ (z : Λ.A.V) (x : a.D₀.X), FrameValue.IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] := fun z x =>
    gtHol_isLift a.D₀ Λ.u _ x _ _ (by rw [Λ.ct, LinearEquiv.apply_symm_apply]) (Λ.ex0_b z)
  have hv : ∀ x j z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j →
      chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε
        ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
    intro x j z hj
    have h₁ := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 z).isGen x) (hl z x) (j := j) hj
    obtain ⟨y, rfl⟩ := Λ.ε.surjective x
    rw [LinearEquiv.symm_apply_apply] at h₁ ⊢
    rw [Λ.arcDict_expZero_section] at h₁
    exact h₁
  refine ⟨fun U f => ?_, fun x j => ⟨?_, hv x j⟩⟩
  · obtain ⟨ho, hd⟩ := Λ.u.hol U f
    simp only [Λ.ex0_b, Set.mem_univ, true_and]
    exact ⟨ho.preimage continuous_snd, hd.comp differentiable_snd.differentiableOn (fun _ h => h)⟩
  · refine DifferentiableOn.congr ?_ (hv x j)
    refine DifferentiableOn.fun_mul ?_ ?_
    · have : Differentiable ℂ (fun z : Λ.A.V => z.1 (Λ.ε.symm x)) :=
        (Λ.A.evalCLM (Λ.ε.symm x)).differentiable.comp differentiable_fst
      exact ((this.const_mul _).cexp).differentiableOn
    · intro z₀ hz₀
      refine DifferentiableAt.differentiableWithinAt ?_
      have hd : ∀ k, Differentiable ℂ fun z : Λ.A.V =>
          (![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k := fun k => by
        fin_cases k
        · exact differentiable_snd.const_add _
        · exact differentiable_const _
        · exact differentiable_snd
        · exact differentiable_const _
      have h : ∀ k, DifferentiableAt ℂ (fun z : Λ.A.V => Λ.u.fr (j k)
          ((![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k) ^
            Out.DegPre.gtε k) z₀ := fun k => by
        have hk := ((hl z₀ x).le_iff j).1 hz₀ k
        refine DifferentiableAt.zpow ?_ (Or.inl (Λ.u.fr_ne _ _ hk))
        exact ((Λ.u.fr_hol (j k)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds hk)).comp z₀ (hd k z₀)
      exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (h k).hasFDerivAt).differentiableAt

end GlobalTheory.ArcPts
end
end

section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory

theorem eq_zero_of_forall_smul_mem_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Set V}
    (hS : S.Countable) {z : V} (hz : ∀ s : ℂ, s • z ∈ S) : z = 0 := by
  by_contra h
  have hinj : Function.Injective fun s : ℂ => s • z := smul_left_injective ℂ h
  have h1 : (Set.univ : Set ℂ).Countable :=
    (hS.preimage_of_injOn hinj.injOn).mono fun s _ => hz s
  exact not_countable_complex h1

namespace KerPerp

variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}

def kerPerp (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')) (y : L →ₗ[O] Y) : Submodule O L where
  carrier := {t | ∀ v, y v = 0 → EF t v = 0}
  zero_mem' v _ := by simp
  add_mem' {t t'} ht ht' v hv := by simp [ht v hv, ht' v hv]
  smul_mem' a t ht v hv := by rw [hadj]; exact ht _ (by simp [hv])

variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}

theorem mem_kerPerp {t : L} : t ∈ kerPerp hadj y ↔ ∀ v, y v = 0 → EF t v = 0 := Iff.rfl

theorem isotropic (hle : kerPerp hadj y ≤ LinearMap.ker y) {t t' : L} (ht : t ∈ kerPerp hadj y)
    (ht' : t' ∈ kerPerp hadj y) : EF t t' = 0 := ht t' (hle ht')

theorem apply_eq_of_eq {t : L} (ht : t ∈ kerPerp hadj y) {v v' : L} (h : y v = y v') : EF t v = EF t v' := by
  rw [← sub_eq_zero, ← map_sub]
  exact ht _ (by rw [map_sub, h, sub_self])

theorem exists_of_dual (hs : Function.Surjective EF) (φ : Module.Dual ℤ Y) :
    ∃ t ∈ kerPerp hadj y, ∀ v, -EF t v = φ (y v) := by
  obtain ⟨t, ht⟩ := hs (-(φ ∘ₗ y.toAddMonoidHom.toIntLinearMap))
  exact ⟨t, fun v hv => by simp [ht, hv], fun v => by simp [ht]⟩

theorem ker_iff [Module.Projective ℤ Y] (hs : Function.Surjective EF) (v : L) :
    y v = 0 ↔ ∀ t ∈ kerPerp hadj y, EF t v = 0 := by
  refine ⟨fun hv t ht => ht v hv, fun h => (Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_⟩
  obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hs φ
  rw [← hφ, h t ht, neg_zero]

variable (hadj)

def toDual (hy : Function.Surjective y) : kerPerp hadj y →ₗ[ℤ] Module.Dual ℤ Y :=
  LinearMap.mk₂ ℤ (fun t x => -EF t (Function.surjInv hy x))
    (fun _ _ _ => by simp [add_comm]) (fun _ _ _ => by simp)
    (fun t x x' => by
      rw [← neg_add, ← map_add (f := _)]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))
    (fun k t x => by
      rw [smul_neg, ← map_zsmul]
      exact congrArg _ (apply_eq_of_eq t.2 (by simp [Function.surjInv_eq])))

@[simp] theorem toDual_apply (hy : Function.Surjective y) (t : kerPerp hadj y) (v : L) :
    toDual hadj hy t (y v) = -EF t v :=
  congrArg Neg.neg (apply_eq_of_eq t.2 (Function.surjInv_eq hy _))

theorem toDual_bijective (hb : Function.Bijective EF) (hy : Function.Surjective y) :
    Function.Bijective (toDual hadj hy) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    refine Subtype.ext (hb.1 (LinearMap.ext fun v => ?_))
    have := toDual_apply hadj hy t v
    rw [ht] at this
    simpa using this
  · intro φ
    obtain ⟨t, ht, hφ⟩ := exists_of_dual (hadj := hadj) (y := y) hb.2 φ
    refine ⟨⟨t, ht⟩, LinearMap.ext fun x => ?_⟩
    obtain ⟨v, rfl⟩ := hy x
    rw [toDual_apply, hφ]

def equivDual (hb : Function.Bijective EF) (hy : Function.Surjective y) : kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y :=
  LinearEquiv.ofBijective _ (toDual_bijective hadj hb hy)

@[simp] theorem equivDual_apply (hb : Function.Bijective EF) (hy : Function.Surjective y) (t : kerPerp hadj y)
    (v : L) : equivDual hadj hb hy t (y v) = -EF t v := toDual_apply hadj hy t v

theorem neg_apply_equivDual_symm (hb : Function.Bijective EF) (hy : Function.Surjective y) (φ : Module.Dual ℤ Y)
    (v : L) : -EF ((equivDual hadj hb hy).symm φ) v = φ (y v) := by
  rw [← equivDual_apply hadj hb hy, LinearEquiv.apply_symm_apply]

theorem equivDual_smul (hb : Function.Bijective EF) (hy : Function.Surjective y) (a : O) (t : kerPerp hadj y)
    (x : Y) : equivDual hadj hb hy (a • t) x = equivDual hadj hb hy t (bar a • x) := by
  obtain ⟨v, rfl⟩ := hy x
  rw [← map_smul y, equivDual_apply, equivDual_apply, Submodule.coe_smul, hadj]

theorem finrank_kerPerp [Module.Free ℤ Y] [Module.Finite ℤ Y] (hb : Function.Bijective EF)
    (hy : Function.Surjective y) : Module.finrank ℤ (kerPerp hadj y) = Module.finrank ℤ Y := by
  rw [(equivDual hadj hb hy).finrank_eq, Module.finrank_linearMap_self]

variable {be : LinearMap.BilinForm ℤ Y}

def nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) : L →ₗ[O] kerPerp hadj y where
  toFun a := (equivDual hadj hb hy).symm (be (y a))
  map_add' a b := by simp
  map_smul' c a := (equivDual hadj hb hy).injective (LinearMap.ext fun x => by
    rw [RingHom.id_apply, equivDual_smul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul, hbe])

theorem neg_apply_nilTo (hb : Function.Bijective EF) (hy : Function.Surjective y)
    (hbe : ∀ (a : O) x x', be (a • x) x' = be x (bar a • x')) (a b : L) :
    -EF (nilTo hadj hb hy hbe a) b = be (y a) (y b) := neg_apply_equivDual_symm hadj hb hy _ b

variable {hadj}

section Nil

variable {nn : L → L}

theorem nil_eq_zero (hi : Function.Injective EF) (h : ∀ a b, -EF (nn a) b = be (y a) (y b)) {a : L}
    (ha : y a = 0) : nn a = 0 :=
  hi (LinearMap.ext fun b => by simpa [ha] using h a b)

end Nil

end KerPerp

namespace AnArc

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem orth_ker_iff (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ v.l = 0 := by
  constructor
  · intro h
    refine ⟨(Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_, A.Ef_bij.1 (LinearMap.ext fun l => ?_)⟩
    · simpa [EF_apply] using h (La.mk 0 φ.toAddMonoidHom 0) rfl
    · simpa [EF_apply] using h (La.mk 0 0 l) rfl
  · rintro ⟨hy, hl⟩ v' hv'
    simp [EF_apply, hy, hl, hv']

theorem y_l_eq_zero_iff (v : A.La) : v.y = 0 ∧ v.l = 0 ↔ ∃ n, v = La.mk 0 n 0 :=
  ⟨fun h => ⟨v.n, La.ext h.1 rfl h.2⟩, by rintro ⟨n, rfl⟩; exact ⟨rfl, rfl⟩⟩

theorem orth_ker_iff_exists (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ ∃ n, v = La.mk 0 n 0 :=
  (A.orth_ker_iff v).trans (A.y_l_eq_zero_iff v)

theorem smul_periodMap_mk_zero_fst_eq_neg_form (s : ℂ) (n : A.X →+ ℤ) (v' : A.La) :
    (s • A.P0 (La.mk 0 n 0)).1 v'.y = -(s * A.EF (La.mk 0 n 0) v') := by
  simp [EF_n_left]

theorem l_eq_zero_of_forall_smul_mem {v : A.La} (hv : v.y = 0) (h : ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂) : v.l = 0 := by
  have hc : Countable A.abelian₂ := Finsupp.Countable.of_moduleFinite (R := ℤ)
  refine Subtype.ext (eq_zero_of_forall_smul_mem_countable (S := (A.abelian₂ : Set _)) (Set.countable_coe_iff.1 hc) fun s => ?_)
  simpa [hv] using h s

theorem orth_ker_iff_forall_smul_mem (v : A.La) :
    (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂ := by
  rw [orth_ker_iff]
  refine and_congr_right fun hv => ⟨fun hl s => ?_, A.l_eq_zero_of_forall_smul_mem hv⟩
  simp [hv, hl]

theorem smul_periodMap_of_orthogonal_ker {v : A.La} (h : ∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) (s : ℂ) :
    (s • A.P0 v).2 = 0 ∧ ∀ v' : A.La, (s • A.P0 v).1 v'.y = -(s * A.EF v v') := by
  obtain ⟨n, rfl⟩ := (A.orth_ker_iff_exists v).1 h
  exact ⟨by simp, A.smul_periodMap_mk_zero_fst_eq_neg_form s n⟩

theorem nilTo_ne_zero {a : A.La} (ha : a.y ≠ 0) :
    KerPerp.nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a ≠ 0 := fun h => by
  have h1 := KerPerp.neg_apply_nilTo A.EF_smul A.EF_bijective A.yLin_surjective A.be_adj a a
  rw [h] at h1
  have h2 : (0 : ℤ) = A.be a.y a.y := by simpa using h1
  exact (A.be_pos _ ha).ne h2

end AnArc

end GlobalTheory
end
end
