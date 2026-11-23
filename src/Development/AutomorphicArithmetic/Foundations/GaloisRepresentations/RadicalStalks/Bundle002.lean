module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma tmul_p_mul (p : ℕ) (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (l : k) (t : C) :
    l ⊗ₜ[ℤ] ((p : C) * t) = 0 := by
  have h1 : (p : C) * t = p • t := (nsmul_eq_mul p t).symm
  have h2 : (p • l : k) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]

private lemma core (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] :
    ∃ (I : Type) (β : I → k),
      (∀ x : k ⊗[ℤ] C, ∃ c : I →₀ C, x = c.sum fun j d => β j ⊗ₜ[ℤ] d) ∧
      (∀ (s : Finset I) (c : I → C), ∑ j ∈ s, β j ⊗ₜ[ℤ] c j = 0 → ∀ j ∈ s, (p : C) ∣ c j) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let B := Module.Basis.ofVectorSpace (ZMod p) k
  let J : Ideal C := Ideal.span {(p : C)}
  have hpJ : (Int.castAddHom (C ⧸ J)) (p : ℤ) = 0 := by
    show ((p : ℤ) : C ⧸ J) = 0
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let φ : ZMod p →+ C ⧸ J := ZMod.lift p ⟨Int.castAddHom (C ⧸ J), hpJ⟩
  have hφ1 : φ 1 = 1 := by
    have h1 := ZMod.lift_coe p ⟨Int.castAddHom (C ⧸ J), hpJ⟩ (1 : ℤ)
    simpa using h1
  refine ⟨_, B, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l t =>
      refine ⟨(B.repr l).mapRange (fun r => ((r.val : ℕ) : C) * t) (by simp), ?_⟩
      rw [Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
      have hl := B.linearCombination_repr l
      rw [Finsupp.linearCombination_apply] at hl
      conv_lhs => rw [← hl]
      rw [Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : (B.repr l j) • B j = (B.repr l j).val • B j := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (B.repr l j)]
        rw [Nat.cast_smul_eq_nsmul]
      rw [hs, TensorProduct.smul_tmul, nsmul_eq_mul]
    | add x y hx hy =>
      obtain ⟨c1, rfl⟩ := hx
      obtain ⟨c2, rfl⟩ := hy
      exact ⟨c1 + c2, by rw [Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)]⟩
  · intro s c hs j hj
    let L : k →ₗ[ℤ] C →ₗ[ℤ] C ⧸ J := LinearMap.mk₂ ℤ (fun l t => φ (B.repr l j) * Ideal.Quotient.mk J t)
      (by intros; simp [add_mul])
      (by intro n m t; rw [map_zsmul, Finsupp.smul_apply, map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add])
      (by intro n m t; rw [map_zsmul, mul_smul_comm])
    have h0 := congrArg (TensorProduct.lift L) hs

    rw [map_sum, map_zero] at h0
    have step : ∀ i ∈ s, TensorProduct.lift L (B i ⊗ₜ[ℤ] c i) = if i = j then Ideal.Quotient.mk J (c i) else 0 := by
      intro i _
      rw [TensorProduct.lift.tmul]
      by_cases h : i = j
      · subst h; simp [L, hφ1]
      · simp [L, h, Finsupp.single_apply]
    rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' s j, if_pos hj, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact Ideal.mem_span_singleton.mp h0

private lemma exact1 {R : Type} [CommRing R] (g a b : R) (h : ∀ x : R, g * x = 0 → ∃ u v, x = a * u + b * v)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : g • x = 0) :
    ∃ u v : M, x = a • u + b • v := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, g * s x m = 0 := by
    intro m
    have h0 : s (g • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u v huv using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ∑ m ∈ (s x).support, v m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [huv m, add_smul, mul_smul, mul_smul]
  rfl

private lemma exact2 {R : Type} [CommRing R] (e g a : R) (h : ∀ x : R, a * x = 0 → ∃ u, e * x = g * u)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : a • x = 0) :
    ∃ u : M, e • x = g • u := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, a * s x m = 0 := by
    intro m
    have h0 : s (a • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u hu using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_smul, hu m, mul_smul]
  rfl

theorem UpperTheory.Gal.Ord.proj :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ) (π : Par p w f)
      (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] C) M] [Module.Projective (k ⊗[ℤ] C) M],
      (∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.g) • x = 0 → ∃ u v : M, x = ((1 : k) ⊗ₜ[ℤ] π.a) • u + ((1 : k) ⊗ₜ[ℤ] (1 - π.ε)) • v) ∧
      ∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.a) • x = 0 → ∃ u : M, ((1 : k) ⊗ₜ[ℤ] π.ε) • x = ((1 : k) ⊗ₜ[ℤ] π.g) • u := by
  intro p _ k _ _ C _ w f π M _ _ _
  obtain ⟨I, β, hspan, hind⟩ := core p k C
  constructor
  · intro x hx
    refine exact1 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.g * c j := hind c.support (fun j => π.g * c j) hy
    choose! u v hd using fun j (hj : j ∈ c.support) => π.annG (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ∑ j ∈ c.support, β j ⊗ₜ[ℤ] v j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← TensorProduct.tmul_add]
    have hc : c j = π.a * u j + (1 - π.ε) * v j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
  · intro x hx
    refine exact2 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.a * c j := hind c.support (fun j => π.a * c j) hy
    choose! u hd using fun j (hj : j ∈ c.support) => π.annA (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    have hc : π.ε * c j = π.g * u j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.transl :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (σ : k →+* k) (ψ : A.left ⟶ A.left), SMor A σ ψ →
      (∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ)) → ∀ v : epsR k ⟶ A, IsConst (v.left ≫ ψ) := by
  intro k _ A _ σ ψ m hT v
  let z : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  let r : Sp (DualNumber k) ⟶ Sp k := spMap (algebraMap k (DualNumber k))
  have hq : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) = r ≫ z := by
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hzr : z ≫ r = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; simp
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have hqq : (r ≫ z) ≫ r ≫ z = r ≫ z := by
    rw [Category.assoc, reassoc_of% hzr]
  let c : epsR k ⟶ epsR k := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r = r
    rw [Category.assoc, hzr, Category.comp_id])
  let zz : 𝟙_ (Over (Sp k)) ⟶ epsR k := Over.homMk z hzr
  have hzc : zz ≫ c = zz := Over.OverMorphism.ext (by
    show z ≫ r ≫ z = z
    rw [reassoc_of% hzr])
  let v0 : epsR k ⟶ A := c ≫ v
  let t : epsR k ⟶ A := v0⁻¹ * v
  have hvt : v = v0 * t := by simp [t]
  have hzt : zz ≫ t = 1 := by
    have a : zz ≫ v0 = zz ≫ v := by simp only [v0, ← Category.assoc, hzc]
    calc zz ≫ t = (zz ≫ v0⁻¹) * (zz ≫ v) := MonObj.comp_mul _ _ _
      _ = (zz ≫ v0⁻¹) * (zz ≫ v0) := by rw [a]
      _ = zz ≫ (v0⁻¹ * v0) := (MonObj.comp_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, MonObj.comp_one]
  have htan : IsTangent t := by
    have e1 : (1 : 𝟙_ (Over (Sp k)) ⟶ A) = η[A] := by
      show toUnit _ ≫ η[A] = _
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    show z ≫ t.left = η[A].left
    rw [← e1, ← hzt]
    rfl
  let Y : Over (Sp k) := Over.mk ((epsR k).hom ≫ spMap σ)
  let Q : Y ⟶ Y := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r ≫ spMap σ = r ≫ spMap σ
    rw [Category.assoc, reassoc_of% hzr])
  let down (x : epsR k ⟶ A) : Y ⟶ A :=
    Over.homMk (x.left ≫ ψ) (by simp [Y, m.w])
  have down_mul (x y : epsR k ⟶ A) : down (x * y) = down x * down y :=
    Over.OverMorphism.ext (m.mul (epsR k) x y (down x) (down y) rfl rfl).symm
  have h0 : Q ≫ down v0 = down v0 := Over.OverMorphism.ext (by
    show (r ≫ z) ≫ ((r ≫ z) ≫ v.left) ≫ ψ = ((r ≫ z) ≫ v.left) ≫ ψ
    simp only [← Category.assoc]
    rw [show ((r ≫ z) ≫ r) ≫ z = r ≫ z by simpa using hqq])
  have h1 : Q ≫ down t = down t := Over.OverMorphism.ext (by
    have := hT t htan
    unfold IsConst at this
    rw [hq] at this
    exact this)
  have key : Q ≫ down v = down v := by
    rw [hvt, down_mul, MonObj.comp_mul, h0, h1]
  unfold IsConst
  rw [hq]
  exact congrArg (fun u => u.left) key
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem pow_inj {R : Type*} [CommRing R] [_root_.IsReduced R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) {a b : R} (e : a ^ p = b ^ p) : a = b := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (a - b) b
  rw [sub_add_cancel, e, h] at hr
  have h0 : (a - b) ^ p = 0 := by
    simpa using hr.symm
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)

private theorem step {p : ℕ} {A B C : CommRingCat} (u : A ⟶ B) (v : A ⟶ C) (FB : B ⟶ B) (FC : C ⟶ C)
    (r : B ⟶ C) (hB : ∀ x, FB x = x ^ p) (hC : ∀ x, FC x = x ^ p)
    (hU : v ≫ FC = (u ≫ FB) ≫ r) (a : A) : (u ≫ r).hom a ^ p = v.hom a ^ p := by
  have ha := ConcreteCategory.congr_hom hU a
  simp only [ConcreteCategory.comp_apply, hB, hC, map_pow] at ha
  simpa using ha.symm

private theorem frob_epi (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X]
    (h : (p : Γ(X, ⊤)) = 0) : Epi (GlobalTheory.VB.frob X p h) := by
  have hV (V : X.Opens) : (p : Γ(X, V)) = 0 := by
    have := congrArg (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h
    simpa using this
  refine ⟨fun {Y} f g e => ?_⟩
  have hx (x : X) : f x = g x := by
    have := congrArg (fun φ : X ⟶ Y => φ x) e
    simpa [GlobalTheory.VB.frob, GlobalTheory.SS.FrobField.absFrob,
      GlobalTheory.SS.FrobField.absPre] using this
  refine Scheme.Hom.ext (by ext x; exact hx x) fun U => ?_
  have hU := Scheme.Hom.congr_app e.symm U
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hU
  ext a
  apply pow_inj (Fact.out : p.Prime) (hV _)
  exact step (p := p) (f.app U) (g.app U) ((GlobalTheory.VB.frob X p h).app (f ⁻¹ᵁ U))
    ((GlobalTheory.VB.frob X p h).app (g ⁻¹ᵁ U)) _ (GlobalTheory.VB.frob_app p h _) (GlobalTheory.VB.frob_app p h _) hU a

theorem UpperTheory.Gal.Ord.epi :
    ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsReduced X] (h : (p : Γ(X, ⊤)) = 0), Epi (GlobalTheory.VB.frob X p h) ∧ ∀ j, Epi (frobN p X h j) := by
  intro p _ X _ h
  have hF := frob_epi p X h
  refine ⟨hF, fun j => ?_⟩
  induction j with
  | zero => exact (inferInstance : Epi (𝟙 X))
  | succ j ih =>
    have : Epi (frobN p X h j) := ih
    exact epi_comp (GlobalTheory.VB.frob X p h) (frobN p X h j)
end
