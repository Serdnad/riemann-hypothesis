module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {S : Scheme.{0}}

def postHom {T A : Over S} [GrpObj A] (φ : A ⟶ A) [IsMonHom φ] : (T ⟶ A) →* (T ⟶ A) where
  toFun f := f ≫ φ
  map_one' := MonObj.one_comp _
  map_mul' f g := MonObj.mul_comp _ _ _

theorem bilin_ext {M La Q I J : Type} [AddCommGroup M] [AddCommGroup La] [CommGroup Q] [Fintype I] [Fintype J]
    (bM : Module.Basis I ℤ M) (bL : Module.Basis J ℤ La) (F G : M → La → Q)
    (hF1 : ∀ c c' a, F (c + c') a = F c a * F c' a) (hF2 : ∀ c a a', F c (a + a') = F c a * F c a')
    (hG1 : ∀ c c' a, G (c + c') a = G c a * G c' a) (hG2 : ∀ c a a', G c (a + a') = G c a * G c a')
    (h : ∀ i j, F (bM i) (bL j) = G (bM i) (bL j)) : ∀ c a, F c a = G c a := by
  intro c a
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => F c a) (fun c c' => hF1 c c' a) c,
    GlobalTheory.LatticeTorsion.eq_prod_zpow bM (fun c => G c a) (fun c c' => hG1 c c' a) c]
  refine Finset.prod_congr rfl fun i _ => ?_
  beta_reduce
  rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bL (F (bM i)) (hF2 _) a, GlobalTheory.LatticeTorsion.eq_prod_zpow bL (G (bM i)) (hG2 _) a]
  simp only [h]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev.RepLat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Kil {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (f : T ⟶ o.A) : Prop :=
  ∀ c ∈ w0 ^ r, f ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1

theorem Kil.comp {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T T' : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (h : T' ⟶ T) : Kil o w0 r (h ≫ f) := fun c hc => by
  rw [Category.assoc, hf c hc, MonObj.comp_one]

theorem Kil.act {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} {f : T ⟶ o.A} (hf : Kil o w0 r f) (d : D.O) : Kil o w0 r (f ≫ o.act.act d) := fun c hc => by
  haveI := o.act.hom d
  rw [Category.assoc, ← o.act.mul, Algebra.commutes, o.act.mul, ← Category.assoc, hf c hc, MonObj.one_comp]

theorem vanish {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
    {T : Over S} (l : D.La → (T ⟶ o.A)) (hadd : ∀ x y, l (x + y) = l x * l y)
    (hlin : ∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) (hk : ∀ a, Kil o w0 r (l a)) :
    ∀ x ∈ wSub D w0 r, l x = 1 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [hlin]
    exact hk z' c hc
  | zero =>
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.1 h0.symm)
  | add x y _ _ hx hy => rw [hadd, hx, hy, _root_.mul_one]
  | smul d x _ hx =>
    haveI := o.act.hom d
    rw [hlin, hx, MonObj.one_comp]

end GlobalTheory.UPel.HT.EtLev.RepLat

namespace GlobalTheory.UPel.HT.EtLev


open RepLat in
theorem exists_finiteEtale_linTorsHom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ x y, et (x + y) = et x * et y) ∧ (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) ∧ (∀ x ∈ wSub D w0 r, et x = 1) ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), (∀ x y, l (x + y) = l x * l y) → (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, l x = 1) → ∃! h : T ⟶ Z, ∀ y, h ≫ et y = l y := by
  intro p _ D R _ b N w0 r _ S _ s o K κ hKf hKe hκ hK
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI := hKf
  haveI := hKe
  have hκ' : Kil o w0 r κ := hκ
  have hcan : ∀ {T : Over S} (v v' : T ⟶ K), v ≫ κ = v' ≫ κ → v = v' := fun v v' e =>
    (hK _ (v' ≫ κ) (hκ'.comp v')).unique e rfl
  have hfac : ∀ {T : Over S} (f : T ⟶ o.A), Kil o w0 r f → ∃ u : T ⟶ K, u ≫ κ = f := fun f hf =>
    (hK _ f hf).exists
  let bb := Module.finBasis ℤ D.La
  let n := Module.finrank ℤ D.La
  let bO := Module.finBasis ℤ D.O
  let Z₀ := Out.powObj K n
  let x : Fin n → (Z₀ ⟶ o.A) := fun i => Out.powPr K i ≫ κ
  let et₀ : D.La → (Z₀ ⟶ o.A) := fun a => ∏ i, x i ^ (bb.repr a i)
  have hadd : ∀ a c, et₀ (a + c) = et₀ a * et₀ c := fun a c => by
    simp only [et₀, map_add (f := _), Finsupp.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hb : ∀ i, et₀ (bb i) = x i := fun i => by
    simp only [et₀, Module.Basis.repr_self]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj]) (by simp)]
    simp
  have hkil : ∀ a, Kil o w0 r (et₀ a) := fun a c hc => by
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    change postHom (T := Z₀) _ (∏ i, x i ^ (bb.repr a i)) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_zpow]
    change (x i ≫ _) ^ _ = 1
    rw [(hκ'.comp (Out.powPr K i)) c hc, one_zpow]
  haveI hZf : IsFinite Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @IsFinite K hKf n
  haveI hZe : Etale Z₀.hom := GlobalTheory.LatticeTorsion.prop_powObj @Etale K hKe n
  have c1 : ClopenCond Z₀ fun _ h => ∀ (c : D.O) a, h ≫ et₀ (c • a) = h ≫ (et₀ a ≫ o.act.act c) := by
    have hfin : ClopenCond Z₀ fun _ h => ∀ ji : Fin (Module.finrank ℤ D.O) × Fin n,
        h ≫ et₀ (bO ji.1 • bb ji.2) = h ≫ (et₀ (bb ji.2) ≫ o.act.act (bO ji.1)) := by
      refine ClopenCond.forall_finite fun ji => ?_
      obtain ⟨u, hu⟩ := hfac _ (hkil (bO ji.1 • bb ji.2))
      obtain ⟨u', hu'⟩ := hfac _ ((hkil (bb ji.2)).act (bO ji.1))
      refine (clopenCond_eq u u').congr fun T' h => ?_
      rw [← hu, ← hu', ← Category.assoc, ← Category.assoc]
      exact ⟨hcan _ _, fun e => by rw [e]⟩
    refine hfin.congr fun T' h => ⟨fun H ji => H _ _, fun H => ?_⟩
    refine bilin_ext bO bb (fun c a => h ≫ et₀ (c • a)) (fun c a => h ≫ (et₀ a ≫ o.act.act c))
      (fun c c' a => by beta_reduce; rw [add_smul, hadd, MonObj.comp_mul])
      (fun c a a' => by beta_reduce; rw [smul_add, hadd, MonObj.comp_mul])
      (fun c c' a => by beta_reduce; rw [o.act.add, MonObj.comp_mul, MonObj.comp_mul])
      (fun c a a' => by
        beta_reduce
        haveI := o.act.hom c
        rw [hadd, MonObj.mul_comp, MonObj.comp_mul])
      (fun j i => H (j, i))
  obtain ⟨U, hU, HU⟩ := c1
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU V i).2 ((Hi V i).2 ⟨𝟙 V, Category.id_comp i⟩)
  have hVadd : ∀ a c, i ≫ et₀ (a + c) = (i ≫ et₀ a) * (i ≫ et₀ c) := fun a c => by
    rw [hadd, MonObj.comp_mul]
  have hVlin : ∀ (c : D.O) a, i ≫ et₀ (c • a) = (i ≫ et₀ a) ≫ o.act.act c := fun c a => by
    rw [hi, Category.assoc]
  refine ⟨V, fun a => i ≫ et₀ a, hV1, hV2, hVadd, hVlin,
    vanish _ hVadd hVlin fun a => (hkil a).comp i, fun T l hladd hllin hlw => ?_⟩
  have hlk : ∀ a, Kil o w0 r (l a) := fun a c hc => by
    rw [← hllin]
    exact hlw _ (Submodule.subset_span ⟨c, hc, a, rfl⟩)
  choose y hy using fun j : Fin n => hfac _ (hlk (bb j))
  let h : T ⟶ Z₀ := (Out.powIsLimit K n).lift (Fan.mk T y)
  have hh : ∀ j, h ≫ Out.powPr K j = y j := fun j => (Out.powIsLimit K n).fac (Fan.mk T y) ⟨j⟩
  have hhe : ∀ a, h ≫ et₀ a = l a := fun a => by
    rw [GlobalTheory.LatticeTorsion.eq_prod_zpow bb (fun a => h ≫ et₀ a) (fun a c => by rw [hadd, MonObj.comp_mul]) a,
      GlobalTheory.LatticeTorsion.eq_prod_zpow bb l hladd a]
    refine Finset.prod_congr rfl fun j _ => ?_
    beta_reduce
    rw [hb, ← hy j, ← hh j, Category.assoc]
  have hext : ∀ u u' : T ⟶ Z₀, (∀ a, u ≫ et₀ a = u' ≫ et₀ a) → u = u' := fun u u' e =>
    (Out.powIsLimit K n).hom_ext fun ⟨j⟩ => by
      have := e (bb j)
      rw [hb] at this
      exact hcan _ _ (by simp only [x, Category.assoc] at this; exact this)
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 fun c a => by rw [hhe, hllin, ← hhe a, Category.assoc])
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hhe], fun g hg => ?_⟩
  exact (cancel_mono i).1 (hext _ _ fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hhe])

end GlobalTheory.UPel.HT.EtLev
end
end

section

open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PELU

theorem isPeriod_comp_realLinear {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (M : Matrix (Fin g) (Fin g) ℂ) (hP₀ : IsPeriod D ρ P₀) (hR : Function.Injective R)
    (hRρ : ∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re)
    (hE : ∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) :
    IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP₀
  have hsurj : Function.Surjective R := LinearMap.injective_iff_surjective.mp hR
  let e : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo R hR
  have he : ∀ z, e z = R z := fun z => rfl
  let ec := e.toContinuousLinearEquiv
  refine ⟨?_, ?_, ?_, ?_, M, hM, hpos, ?_⟩
  · intro a x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, hRρ]
  · exact hR.comp h2
  · let f : (R.toAddMonoidHom.comp P₀).range → P₀.range := fun z =>
      ⟨ec.symm z.1, by
        obtain ⟨z, x, rfl⟩ := z
        exact ⟨x, (e.symm_apply_apply (P₀ x)).symm⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact ec.symm.continuous.comp continuous_subtype_val
    have hi : Function.Injective f := by
      intro z w h
      apply Subtype.ext
      have := congrArg (fun u : P₀.range => ec u.1) h
      simpa [f] using this
    exact DiscreteTopology.of_continuous_injective hf hi
  · have : Set.range (R.toAddMonoidHom.comp P₀) = R '' Set.range P₀ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  · intro x y
    exact hE x y

end GlobalTheory.PELU
end

section

namespace GlobalTheory.PELU

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem hermForm_pullback_matrix {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Bᵀ * Hm * B.map star) u v = hermForm Hm (B *ᵥ u) (B *ᵥ v) := by
  unfold hermForm
  have e : star (B *ᵥ v) = B.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem IsPeriod.comp_linearEquiv (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ)
    (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hP : GlobalTheory.PELU.IsPeriod D ρ P) (hh : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    GlobalTheory.PELU.IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x) := fun _ => rfl
  set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB
  have hBv : ∀ u, B *ᵥ u = h.symm u := fun u => by
    rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩
  · rw [ev, ev, h1, hh]
  · exact h.injective.comp h2
  · let f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range := fun z =>
      ⟨h.symm z.1, by
        obtain ⟨x, hx⟩ := z.2
        exact ⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩
    have hc : Continuous f :=
      Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
    have hi : Function.Injective f := fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))
    exact DiscreteTopology.of_continuous_injective hc hi
  · have e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact h.surjective
  · have e1 : (B.map star)ᴴ = Bᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Bᵀ)ᴴ = B.map star := by
      ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]
  · rw [hermForm_pullback_matrix, hBv]
    exact h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))
  · rw [hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]

end GlobalTheory.PELU
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_transport : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 0 < N → UnifAt F σ ρ N D' t P y e → IsMarkedIsom N D' D'' t t' w → (∀ x, P' (w x) = h (P x)) → IsPeriod D'' ρ P' → UnifAt F σ ρ N D'' t' P' y (fun z => e (h.symm z)) := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e w h hN hU hW hPP' hP'
  obtain ⟨hy, hP, hexp, hker, hact, hweil, heta⟩ := hU
  obtain ⟨hiso, hmark⟩ := hW
  have hQs : ∀ x, h.symm (P' x) = P (w.symm x) := by
    intro x
    rw [h.symm_apply_eq, ← hPP', w.apply_symm_apply]

  have hcomm : ∀ a z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    have hL : ((h.toLinearMap ∘ₗ Matrix.mulVecLin (ρ a)).restrictScalars ℝ) =
        ((Matrix.mulVecLin (ρ a) ∘ₗ h.toLinearMap).restrictScalars ℝ) := by
      apply LinearMap.ext_on hP.2.2.2.1
      rintro _ ⟨x, rfl⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
        Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
      rw [← hP.1, ← hPP', ← hPP', map_smul, hP'.1]
    exact congrArg (fun f => f z) hL
  have hcomm' : ∀ a z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    rw [h.symm_apply_eq, hcomm, h.apply_symm_apply]
  set hc := h.symm.toContinuousLinearEquiv with hhc
  have hcc : ∀ z, hc z = h.symm z := fun z => rfl
  have hder : ∀ u v, IsDerivAt0 (fun z => (e (h.symm z)).left) u v ↔ IsDerivAt0 (fun z => (e z).left) (h.symm u) v := by
    intro u v
    unfold IsDerivAt0
    simp only [map_zero]
    refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
    have key := hc.comp_right_fderiv (f := fun z => valAt' (e z).left U f) (x := 0)
    have e1 : ((fun z => valAt' (e z).left U f) ∘ hc) = (fun z => valAt' (e (h.symm z)).left U f) := rfl
    rw [e1, map_zero] at key
    rw [key]
    rfl
  refine ⟨hy, hP', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro z z'
    simp only [map_add (f := _)]
    exact hexp.1 _ _
  · exact hexp.2.1.comp h.symm.surjective
  · intro U f
    obtain ⟨ho, hd⟩ := hexp.2.2.1 U f
    have hs : {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e (h.symm b)).left ⁻¹ᵁ U} =
        hc ⁻¹' {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e b).left ⁻¹ᵁ U} := by
      ext b; simp [hcc]
    rw [hs]
    exact ⟨ho.preimage hc.continuous, hd.comp hc.differentiableOn (Set.mapsTo_preimage _ _)⟩
  · intro u
    obtain ⟨v, hv, huniq⟩ := hexp.2.2.2.1 (h.symm u)
    exact ⟨v, (hder u v.left).2 hv, fun v' hv' => huniq v' ((hder u v'.left).1 hv')⟩
  · intro v hv
    dsimp only at hv
    rw [map_zero] at hv
    obtain ⟨u, hu, huniq⟩ := hexp.2.2.2.2 v hv
    refine ⟨h u, (hder (h u) v.left).2 (by rwa [h.symm_apply_apply]), fun u' hu' => ?_⟩
    rw [← huniq (h.symm u') ((hder u' v.left).1 hu'), h.apply_symm_apply]
  · intro z
    rw [hker]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨w x, by rw [hPP', hx, h.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, (hQs x).symm⟩
  · intro a z
    dsimp only
    rw [hcomm', hact]
  · intro k a b c hk hc'
    have h1 := hweil k (w.symm a) (w.symm b) c hk (by
      rw [hc', ← hiso (w.symm a) (w.symm b), w.apply_symm_apply, w.apply_symm_apply])
    simpa only [map_smul, hQs] using h1
  · intro a
    obtain ⟨x, hx⟩ := hmark a
    rw [heta a]
    have h1 : t' a = w (t a - N • w.symm x) := by
      rw [map_sub, map_nsmul, w.apply_symm_apply, hx, add_sub_cancel_right]
    have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h2 : h.symm ((N : ℂ)⁻¹ • P' (t' a)) = (N : ℂ)⁻¹ • P (t a) + P (-(w.symm x)) := by
      rw [h1, hPP', map_smul, h.symm_apply_apply, map_sub, map_nsmul, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hN', one_smul, map_neg, sub_eq_add_neg]
    dsimp only
    rw [h2, hexp.1, (hker _).2 ⟨_, rfl⟩, _root_.mul_one]

end GlobalTheory.PELU
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

theorem isIsogDeg_of_isFinite_of_finrank_origin :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  intro k _ _ A _ hA φ _ hfin d hd
  obtain ⟨hflat, hsurj⟩ := GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A hA φ inferInstance hfin
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation (φ.left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp φ.left A.hom
  refine ⟨hfin, hflat, hsurj, fun y => ?_⟩
  rw [← hd]
  exact (Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace y _

end GlobalTheory.IwLevel
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isNilpotent_invTranspose_blockFrobenius_ainf_of_frameNil : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), IsUnit U → IsUnit V → (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε))) := by
  first | exact @GlobalTheory.WinLift.NilF.isNil_frob | exact GlobalTheory.WinLift.NilF.isNil_frob | (intros; apply GlobalTheory.WinLift.NilF.isNil_frob <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.transpose_lift_solves_mod_frobXi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  first | exact @GlobalTheory.WinLift.lift_solves_div_frob_xi_mu | exact GlobalTheory.WinLift.lift_solves_div_frob_xi_mu | (intros; apply GlobalTheory.WinLift.lift_solves_div_frob_xi_mu <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.mu_dvd_lift_of_frame_matrix_equation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  first | exact @GlobalTheory.WinLift.mu_dvd_of_mod_tau | exact GlobalTheory.WinLift.mu_dvd_of_mod_tau | (intros; apply GlobalTheory.WinLift.mu_dvd_of_mod_tau <;> assumption)
end
