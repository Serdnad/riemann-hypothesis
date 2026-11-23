module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
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
public import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.UnifJac

theorem valT_comp {T : Type} [CommRing T] {X Y : Scheme.{0}} (w : Sp T ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valT (w ≫ φ) U f = valT w (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valT
  by_cases h : ⊤ ≤ w ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]
    rfl
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U from h)]

variable {A : Over (Sp ℂ)} [GrpObj A]

theorem translate_left {T : Over (Sp ℂ)} (z : 𝟙_ (Over (Sp ℂ)) ⟶ A) (v : T ⟶ A) :
    ((toUnit T ≫ z) * v).left = v.left ≫ ((toUnit A ≫ z) * 𝟙 A).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem le_of_isTangent {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ η[A].left ⁻¹ᵁ U) : ⊤ ≤ v.left ⁻¹ᵁ U := by
  intro p _
  have hp : p = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (IsLocalRing.closedPoint ℂ) := by
    have : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := by
      refine ⟨fun a b => ?_⟩
      have hn : ∀ c : PrimeSpectrum (DualNumber ℂ), c.asIdeal = IsLocalRing.maximalIdeal _ := fun c => by
        refine le_antisymm (IsLocalRing.le_maximalIdeal c.isPrime.ne_top) ?_
        rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem]
        exact c.isPrime.mem_of_pow_mem 2 (by rw [sq, DualNumber.eps_mul_eps]; exact zero_mem _)
      exact PrimeSpectrum.ext ((hn a).trans (hn b).symm)
    exact Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
  have h1 : η[A].left (IsLocalRing.closedPoint ℂ) ∈ U := h (show _ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  rw [← hv] at h1
  rw [hp]
  exact h1

variable {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_translate (z w : Fin g → ℂ) :
    (u.ex w).left ≫ ((toUnit A ≫ u.ex z) * 𝟙 A).left = (u.ex (z + w)).left := by
  rw [← translate_left, u.ex_add, toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]

theorem snd_valT_translate {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w : Fin g → ℂ} (hd : u.IsDiff w v)
    (z : Fin g → ℂ) (U : A.left.Opens) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    TrivSqZeroExt.snd (valT (T := DualNumber ℂ) ((toUnit (epsR ℂ) ≫ u.ex z) * v).left U f) =
      fderiv ℂ (fun y => valAt' (u.ex y).left U f) z w := by
  have h0 : ⊤ ≤ η[A].left ⁻¹ᵁ (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U) := by
    have e := ex_translate u z 0
    rw [add_zero, ex_zero] at e
    rw [← e] at hz
    have e1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over (Sp ℂ)))) (𝟙 _), Category.id_comp]
    rw [e1] at hz
    exact hz
  have h1 := le_of_isTangent hv _ h0
  rw [translate_left]
  refine (congrArg _ (valT_comp _ _ _ _)).trans ?_
  refine (congrArg TrivSqZeroExt.snd (dif_pos h1)).trans ((hd _ h1 _).trans ?_)
  have e : (fun y => valAt' (u.ex y).left (((toUnit A ≫ u.ex z) * 𝟙 A).left ⁻¹ᵁ U)
      ((((toUnit A ≫ u.ex z) * 𝟙 A).left.app U).hom f)) = fun y => valAt' (u.ex (z + y)).left U f := by
    funext y
    rw [← ex_translate]
    exact (valT_comp (T := ℂ) _ _ _ _).symm
  rw [e, fderiv_comp_add_left (f := fun y => valAt' (u.ex y).left U f), add_zero]

theorem fderiv_val (c : L.ι) (f : Γ(A.left, L.U c)) (F : (Fin g → ℂ) → ℂ) (hF : Differentiable ℂ F) (n : ℕ)
    (hf : ∀ y, ⊤ ≤ (u.ex y).left ⁻¹ᵁ L.U c → valAt' (u.ex y).left (L.U c) f = F y * u.fr c y ^ n)
    (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U c) (h0 : F z = 0) (w : Fin g → ℂ) :
    fderiv ℂ (fun y => valAt' (u.ex y).left (L.U c) f) z w = u.fr c z ^ n * fderiv ℂ F z w := by
  have hn := (u.hol (L.U c) f).1.mem_nhds hz
  have e : (fun y => valAt' (u.ex y).left (L.U c) f) =ᶠ[nhds z] fun y => F y * u.fr c y ^ n :=
    Filter.eventually_of_mem hn hf
  have hd : DifferentiableAt ℂ (fun y => u.fr c y ^ n) z := ((u.fr_hol c).differentiableAt hn).pow n
  rw [e.fderiv_eq, fderiv_fun_mul (hF z) hd, h0]
  simp

end GlobalTheory.UnifJac

namespace GlobalTheory


open UnifJac in
theorem unif_value_jac_zeros : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (n : ℕ) (s : Fin x.P.g → RR x n) (F : Fin x.P.g → (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) (c : x.P.L.ι), Wit x h u τ a b → (∀ i, Differentiable ℂ (F i) ∧ FnPw x u (s i) (F i)) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := ℂ) (u.ex z).left (x.P.L.U c) ((s i).f c) = F i z * u.fr c z ^ n) ∧ ((∀ i, F i z = 0) → jac x s (u.ex z) c = u.fr c z ^ (g * n) * (Matrix.of fun i k : Fin x.P.g => (2 * Real.pi * Complex.I)⁻¹ * fderiv ℂ (F i) z (Pi.single (k.cast h) 1)).det) ∧ ∀ (d : ℕ) (zs : Fin d → Fin g → ℂ), (∀ y, (∀ i, F i y = 0) → ∃ a, ∃ e ∈ u.Λ, y = zs a + e) → ∀ y : x.P.A.left, (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y := by
  intro _ g x h u τ a b n s F z c hW hF hz
  refine ⟨fun i => (hF i).2 c z hz, fun h0 => ?_, fun d zs hzs y hy => ?_⟩
  · subst h
    unfold jac
    rw [mul_comm x.P.g n, pow_mul, show (u.fr c z ^ n) ^ x.P.g = (u.fr c z ^ n) ^ Fintype.card (Fin x.P.g) by
      rw [Fintype.card_fin], ← Matrix.det_smul]
    congr 1
    ext i k
    have hd := hW.2.2.2.2.2 k
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    refine (snd_valT_translate u (x.basis.1 k) hd z _ hz _).trans ?_
    refine (fderiv_val u c _ (F i) (hF i).1 n ((hF i).2 c) z hz (h0 i) _).trans ?_
    rw [show (Pi.single k (2 * Real.pi * Complex.I)⁻¹ : Fin x.P.g → ℂ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • Pi.single k 1 by rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one], map_smul]
    rfl
  · haveI := x.P.isAb.smooth
    by_contra hne
    have hcl : IsClosed {y : x.P.A.left | ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y} := by
      have : {y : x.P.A.left | ∃ a, ∃ p : Sp ℂ, (u.ex (zs a)).left p = y} =
          ⋃ a, Set.range (u.ex (zs a)).left := by
        ext y; simp
      rw [this]
      refine isClosed_iUnion_of_finite fun a => ?_
      haveI := x.P.isAb.proper
      have : IsClosedImmersion (u.ex (zs a)).left := by
        have hw : (u.ex (zs a)).left ≫ x.P.A.hom = 𝟙 _ := Over.w _
        have : IsClosedImmersion ((u.ex (zs a)).left ≫ x.P.A.hom) := by rw [hw]; infer_instance
        exact IsClosedImmersion.of_comp _ x.P.A.hom
      exact (u.ex (zs a)).left.isClosedEmbedding.isClosed_range
    have hcz : IsClosed {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
    obtain ⟨q, hq, hqZ⟩ := ComplexPoints.exists_point_mem x.P.A.hom
      (hcz.isLocallyClosed.inter hcl.isOpen_compl.isLocallyClosed) ⟨y, hy, hne⟩
    obtain ⟨w, hw⟩ := u.ex_onto (Over.homMk q hq)
    have hw' : (u.ex w).left = q := congrArg (fun φ => φ.left) hw
    let p : Sp ℂ := IsLocalRing.closedPoint ℂ
    obtain ⟨j, hj⟩ : ∃ j, q p ∈ x.P.L.U j :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [x.P.isLB.cover]; trivial)
    have hj' : ⊤ ≤ q ⁻¹ᵁ x.P.L.U j := (ComplexPoints.top_le_preimage_iff q _ p).2 hj
    obtain ⟨a', e, he, hwe⟩ := hzs w fun i => by
      by_contra hi
      refine (hqZ p).1 i (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩)
      refine (ComplexPoints.top_le_preimage_iff q _ p).1
        ((ComplexPoints.top_le_preimage_basicOpen_iff q _ hj' _).2 ?_)
      have hv := (hF i).2 j w (by rw [hw']; exact hj')
      rw [hw'] at hv
      exact ((dif_pos hj').symm.trans hv).trans_ne (mul_ne_zero hi (pow_ne_zero _ (u.fr_ne j w (by rw [hw']; exact hj'))))
    refine (hqZ p).2 ⟨a', p, ?_⟩
    rw [← hw', hwe, u.ex_add, (u.ker e).2 he, _root_.mul_one]

end GlobalTheory

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish

theorem exactAt_of_trace {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A B : GlobalTheory.Cube.{0} κ R)
    (φ : ∀ s, A.obj s →+ B.obj s) (T : ∀ s, B.obj s →+ B.obj s)
    (hφ : ∀ {s t : Finset κ} (h : s ⊆ t) x, φ t (Cube.res A h x) = Cube.res B h (φ s x))
    (hT : ∀ {s t : Finset κ} (h : s ⊆ t) x, T t (Cube.res B h x) = Cube.res B h (T s x))
    (inj : ∀ s, Function.Injective (φ s)) (n : ℕ) (hn : IsUnit (n : R))
    (himg : ∀ s y, ∃ x, φ s x = T s y) (htr : ∀ s x, T s (φ s x) = n • φ s x) (p : ℕ)
    (H : (cubeComplex B).ExactAt p) : (cubeComplex A).ExactAt p := by
  have dφ : ∀ q (x : Cube.Term A q), Cube.d B q (fun s => φ s.1 (x s)) = fun t => φ t.1 (Cube.d A q x t) :=
    fun q x => funext fun t => by

      simp only [Cube.d_apply, map_sum, map_zsmul, hφ]
  have dT : ∀ q (x : Cube.Term B q), Cube.d B q (fun s => T s.1 (x s)) = fun t => T t.1 (Cube.d B q x t) :=
    fun q x => funext fun t => by

      simp only [Cube.d_apply, map_sum, map_zsmul, hT]
  rcases p with _ | p
  · rw [cubeComplex_exactAt_zero_iff'] at H ⊢
    intro x y hxy
    have : (fun s => φ s.1 (x s) : Cube.Term B 0) = fun s => φ s.1 (y s) := H (by rw [dφ, dφ, hxy])
    exact funext fun s => inj _ (congrFun this s)
  · rw [cubeComplex_exactAt_succ_iff] at H ⊢
    intro x
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ Cube.d_d A p y⟩
    obtain ⟨y, hy⟩ := (H (fun s => φ s.1 (x s))).1 (by
      rw [dφ, hx]; exact funext fun t => map_zero _)
    choose z hz using fun s : {s : Finset κ // s.card = p} => himg s.1 (y s)
    have key : Cube.d A p z = (n : R) • x := funext fun t => inj _ (by
      have e := congrFun (dφ p z) t
      have e' := congrFun (dT p y) t
      simp only [hz] at e
      rw [← e, e', hy, htr, Pi.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul])
    obtain ⟨u, hu⟩ := hn.exists_left_inv
    exact ⟨u • z, by rw [map_smul, key, smul_smul, hu, one_smul]⟩

variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)

theorem le_deck {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) (j : (M.pull f).ι) :
    W' ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U j) := fun y hy =>
  ⟨e hy.1, mem_pull.2 (by
    have := mem_pull.1 hy.2
    rwa [← hτ] at this)⟩

def act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) :
    SecOn (M.pull f) W →+ SecOn (M.pull f) W' where
  toFun s := GlobalTheory.LB.mkSec (fun j => pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j)) fun i j => by
    have e₀ : W' ⊓ (M.pull f).U i ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U i ⊓ (M.pull f).U j) :=
      le_deck f M hτ (le_deck f M hτ e i) j
    have h := congrArg (pb τ e₀) (GlobalTheory.LB.coord_mem s i j)
    have g₁ : ∀ (O : Y.Opens) (e : O ≤ (M.pull f).U i ⊓ (M.pull f).U j),
        rs Y e ((M.pull f).g i j).val = pb f (pre_pull M f (i PUnit.unit) (j PUnit.unit) e)
          (M.g (i PUnit.unit) (j PUnit.unit)).val :=
      fun O e => rs_pull_g M f (i PUnit.unit) (j PUnit.unit) (W := O) e
    exact (rs_pb τ _ _ _).trans ((pb_rs τ e₀ _ _).symm.trans (h.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ((congrArg (pb τ e₀) (g₁ _ _)).trans ((pb_pb τ f _ e₀ _).trans
        ((pb_congr hτ _ _).trans (g₁ _ _).symm))) ((pb_rs τ e₀ _ _).trans (rs_pb τ _ _ _).symm)))))
  map_zero' := GlobalTheory.LB.sec_ext fun j => map_zero (pb τ _)
  map_add' s t := GlobalTheory.LB.sec_ext fun j => map_add (pb τ _) _ _

theorem coord_act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W)
    (s : SecOn (M.pull f) W) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (act f M hτ e s) j = pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j) := rfl

theorem act_restrict {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W' ≤ τ ⁻¹ᵁ W')
    (h : W' ≤ W) (s : SecOn (M.pull f) W) :
    act f M hτ e' (SecOn.restrict _ h s) = SecOn.restrict _ h (act f M hτ e s) :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, SecOn.coord_restrict, SecOn.coord_restrict, coord_act, pb_rs, rs_pb]

theorem act_act {τ σ ρ : Y ⟶ Y} (hτ : τ ≫ f = f) (hσ : σ ≫ f = f) (hρ : ρ ≫ f = f) (H : τ ≫ σ = ρ)
    {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W ≤ σ ⁻¹ᵁ W) (e'' : W ≤ ρ ⁻¹ᵁ W) (s : SecOn (M.pull f) W) :
    act f M hτ e (act f M hσ e' s) = act f M hρ e'' s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_act, coord_act, pb_pb, pb_congr H]

theorem coord_pullLE {V : X.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (SecOn.pullLE M f V W e s) j =
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V j)) (GlobalTheory.LB.coord s (j PUnit.unit)) :=
  SecOn.coord_pullLE f e s j

theorem act_pullLE {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {V : X.Opens} {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W)
    (h : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) :
    act f M hτ e (SecOn.pullLE M f V W h s) = SecOn.pullLE M f V W h s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_pullLE, pb_pb, pb_congr hτ]

variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal


omit hτ in
theorem exists_fun (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) (s : Γ(Y, W))
    (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), pb (τ y) e s = s) : ∃! g : Γ(X, U), pb f e g = s := by
  obtain rfl := le_antisymm e e'
  simpa only [app_eq_pb] using hgal U s hs

theorem pb_injective (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) :
    Function.Injective (pb f e) := fun a _ hab =>
  (exists_fun f τ hgal U W e e' (pb f e a) (fun y _ => by rw [pb_pb, pb_congr (hτ y)])).unique rfl hab.symm

theorem pullLE_injective (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W) :
    Function.Injective (SecOn.pullLE M f V W e) := fun a b hab => GlobalTheory.LB.sec_ext fun i => by
  have h := (coord_pullLE f M e a (fun _ => i)).symm.trans
    ((congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) hab).trans (coord_pullLE f M e b (fun _ => i)))
  exact pb_injective f τ hτ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
    (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) h

theorem exists_pullLE (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W)
    (s : SecOn (M.pull f) W) (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), act f M (hτ y) e s = s) :
    ∃ x, SecOn.pullLE M f V W e x = s := by
  have inv : ∀ y, W ≤ τ y ⁻¹ᵁ W := fun y => by
    obtain rfl := le_antisymm e e'
    rw [← Scheme.Hom.comp_preimage, hτ]
  have H : ∀ i : M.ι, ∃ g : Γ(X, V ⊓ M.U i),
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V (fun _ => i))) g =
        GlobalTheory.LB.coord s (fun _ => i) := fun i =>
    (exists_fun f τ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
      (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) _ fun y _ =>
      congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) (hs y (inv y))).exists
  choose g hg using H
  refine ⟨GlobalTheory.LB.mkSec g fun i j => ?_, GlobalTheory.LB.sec_ext fun j => (coord_pullLE f M e _ j).trans (hg _)⟩
  have e₀ : W ⊓ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
    fun y hy => ⟨⟨e hy.1.1, mem_pull.1 hy.1.2⟩, mem_pull.1 hy.2⟩
  apply pb_injective f τ hτ hgal (V ⊓ M.U i ⊓ M.U j) _ e₀
    (fun y hy => ⟨⟨e' hy.1.1, mem_pull.2 hy.1.2⟩, mem_pull.2 hy.2⟩)
  have h := GlobalTheory.LB.coord_mem s (fun _ => i) (fun _ => j)
  rw [← hg, ← hg] at h
  exact (pb_rs f e₀ _ _).trans ((rs_pb f _ _ _).symm.trans (h.trans ((congrArg₂ (· * ·)
    ((rs_pull_g M f i j _).trans (pb_rs f e₀ _ _).symm)
    ((rs_pb f _ _ _).trans (pb_rs f e₀ _ _).symm)).trans (map_mul _ _ _).symm)))

theorem exactAt_of_pull [Group G] [Fintype G] (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    {R : Type} [CommRing R] (a : X ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ Spec (CommRingCat.of R))
    (hu : IsUnit ((Fintype.card G : ℕ) : R)) {I : Type} [LinearOrder I] (D : I → X.Opens) (p : ℕ)
    (H : (cubeComplex (secCube b (M.pull f) (fun i => f ⁻¹ᵁ D i))).ExactAt p) :
    (cubeComplex (secCube a M D)).ExactAt p := by
  have inv : ∀ y (s : Finset I), (⨅ i ∈ s, f ⁻¹ᵁ D i) ≤ τ y ⁻¹ᵁ (⨅ i ∈ s, f ⁻¹ᵁ D i) := fun y s => by
    rw [← preimage_biInf, ← Scheme.Hom.comp_preimage, hτ]
  let φ : ∀ s : Finset I, SecOn M (⨅ i ∈ s, D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => (SecOn.pullLE M f _ _ (preimage_biInf D f s).ge).toAddMonoidHom
  let T : ∀ s : Finset I, SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => ∑ y, act f M (hτ y) (inv y s)
  have hT : ∀ s x, T s x = ∑ y, act f M (hτ y) (inv y s) x := fun s x => AddMonoidHom.finsetSum_apply _ _ _
  refine exactAt_of_trace _ _ φ T (fun {s t} h x => ?_) (fun {s t} h x => ?_)
    (fun s => pullLE_injective f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le) _ hu (fun s y => ?_)
    (fun s x => ?_) p H
  · exact (SecOn.pullLE_restrict f (iInf_le_iInf_of_subset D h) (preimage_biInf D f t).ge _).trans
      (SecOn.restrict_pullLE f (preimage_biInf D f s).ge (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) _).symm
  · change T t (SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x) =
      SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) (T s x)

    rw [hT t, hT s x, map_sum]
    exact Finset.sum_congr rfl fun y _ => act_restrict f M (hτ y) (inv y s) (inv y t) _ x
  · refine exists_pullLE f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le (T s y)
      fun z e => ?_

    rw [hT s y, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w =>
      act_act f M (hτ z) (hτ w) (hτ (z * w)) (hmul z w) e (inv w s) (inv (z * w) s) y
  · refine (hT s _).trans ((Finset.sum_congr rfl fun y _ =>
      act_pullLE f M (hτ y) (inv y s) (preimage_biInf D f s).ge x).trans ?_)
    rw [Finset.sum_const, Finset.card_univ]
    rfl

end GlobalTheory.TraceDescent

theorem GlobalTheory.exactAt_secCube_of_mul_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  intro L K _ _ P m N I _ _ D p hm _ H
  classical
  haveI := P.isAb.comm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => hm (by rw [h, Nat.cast_zero])
  let G : Subgroup (𝟙_ (Over (Sp K)) ⟶ P.A) := (powMonoidHom m).ker
  have hc : Nat.card G = m ^ (2 * P.g) := (L.mulN _ P m hm1).2.2.2.2 K (𝟙 _) hm
  haveI : Finite G := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega))
  haveI : Fintype G := Fintype.ofFinite G
  have hgal := GlobalTheory.torsion_invariant_descends (fun S _ P n hn =>
    have h := L.mulN S P n hn
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) K P m hm
  refine GlobalTheory.TraceDescent.exactAt_of_pull (Out.mulA P.A m).left N (G := G)
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
    (fun U f hf => hgal U f fun y hy e => hf ⟨y, hy⟩ e) (fun y z => ?_) _ _ ?_ D p H
  · have hy : y.1 ^ m = 1 := y.2
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hc, Nat.cast_pow]
    exact (IsUnit.mk0 _ hm).pow _
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_descent_symmetric_linearised_bundle : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ c, i c ≫ ψ = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])) (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])), ((∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧ ∀ c (T : Over S) (x : T ⟶ A) (z : T.left) (J), Good L z J → val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J = val j x.left z J * val (u c⁻¹) (x⁻¹).left z J) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) ∧ LBIso M (M.pull (GrpObj.inv : B ⟶ B).left) := by
  first | exact @GlobalTheory.LinDescent.exists_descent_symmetric | exact GlobalTheory.LinDescent.exists_descent_symmetric | (intros; apply GlobalTheory.LinDescent.exists_descent_symmetric <;> assumption)
end
