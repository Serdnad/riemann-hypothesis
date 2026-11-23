module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open scoped TensorProduct

private lemma UpperTheory.Gal.crystallineComparison.Mod.tensor_decomp (p : ℕ) [Fact p.Prime] (B : Type) [AddCommGroup B]
    (a : B ⊗[ℤ] ℤ_[p]) :
    ∃ (c : B) (a' : B ⊗[ℤ] ℤ_[p]), a = c ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • a' := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c z =>
    obtain ⟨r, z', hz⟩ : ∃ (r : ℤ) (z' : ℤ_[p]), z = r • (1 : ℤ_[p]) + (p : ℤ) • z' := by
      have h : z - (PadicInt.zmodRepr z : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
        rw [← PadicInt.maximalIdeal_eq_span_p]
        exact PadicInt.sub_zmodRepr_mem z
      obtain ⟨z', hz'⟩ := Ideal.mem_span_singleton'.mp h
      refine ⟨(PadicInt.zmodRepr z : ℤ), z', ?_⟩
      have : z = (PadicInt.zmodRepr z : ℤ_[p]) + z' * p := by rw [hz']; ring
      simp only [zsmul_eq_mul, mul_one]
      push_cast
      rw [mul_comm (p : ℤ_[p])]
      first | (rw [mul_one]; exact this) | simpa using this
    refine ⟨r • c, c ⊗ₜ[ℤ] z', ?_⟩
    rw [hz, TensorProduct.tmul_add, TensorProduct.tmul_smul (p : ℤ), TensorProduct.tmul_smul r,
      TensorProduct.smul_tmul']
  | add a b ha hb =>
    obtain ⟨c, a', rfl⟩ := ha
    obtain ⟨d, b', rfl⟩ := hb
    exact ⟨c + d, a' + b', by rw [TensorProduct.add_tmul, smul_add]; abel⟩

theorem UpperTheory.Gal.crystallineComparison.Mod.oMod_of :
    OMod := by
  intro p _ D hm x
  obtain ⟨e⟩ := D.splitP
  have hsub : Subsingleton (Fin D.m) := by rw [hm]; infer_instance
  let i0 : Fin D.m := ⟨0, D.m_pos⟩
  obtain ⟨c, a', ha⟩ := tensor_decomp p (𝓞 D.F) (e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) i0 i0)
  let M' : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) := Matrix.of fun _ _ => a'
  have hM : e (x ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) _ c + (p : ℤ) • M' := by
    ext i j
    obtain rfl := Subsingleton.elim i i0
    obtain rfl := Subsingleton.elim j i0
    rw [ha]
    simp [M', Matrix.algebraMap_matrix_apply, Algebra.TensorProduct.algebraMap_apply]
  have hx : x ⊗ₜ[ℤ] (1 : ℤ_[p]) =
      (algebraMap (𝓞 D.F) D.O c) ⊗ₜ[ℤ] (1 : ℤ_[p]) + (p : ℤ) • e.symm M' := by
    have := congrArg e.symm hM
    rw [e.symm_apply_apply, map_add (f := _), map_zsmul, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply] at this
    exact this
  let P : Submodule ℤ D.O := LinearMap.range (LinearMap.lsmul ℤ D.O (p : ℤ))
  have hP : ∀ q : D.O ⧸ P, p • q = 0 := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, by simp⟩
  letI : Module (ZMod p) (D.O ⧸ P) := AddCommGroup.zmodModule hP
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₗ[ℤ] D.O ⧸ P := TensorProduct.lift <|
    LinearMap.mk₂ ℤ (fun y z => PadicInt.toZMod z • (Submodule.Quotient.mk y : D.O ⧸ P))
      (fun y y' z => by simp [smul_add])
      (fun n y z => by rw [Submodule.Quotient.mk_smul]; exact smul_comm _ _ _)
      (fun y z z' => by simp [add_smul])
      (fun n y z => by rw [map_zsmul, smul_assoc])
  have h1 : ∀ y : D.O, Φ (y ⊗ₜ[ℤ] (1 : ℤ_[p])) = Submodule.Quotient.mk y := by
    intro y
    change PadicInt.toZMod (1 : ℤ_[p]) • (Submodule.Quotient.mk y : D.O ⧸ P) = _
    rw [map_one, one_smul]
  have h2 := congrArg Φ hx
  rw [map_add (f := _), map_zsmul, h1, h1] at h2
  have h3 : (p : ℤ) • Φ (e.symm M') = 0 := by
    rw [natCast_zsmul]; exact hP _
  rw [h3, add_zero, Submodule.Quotient.eq] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨c, y, ?_⟩
  have hy' : (p : ℤ) • y = x - algebraMap (𝓞 D.F) D.O c := hy
  rw [map_natCast, ← sub_eq_iff_eq_add', ← hy']
  simp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.uElt_of :
    UElt := by
  intro p _ D r w hw huw e
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hbb : ∀ x : 𝓞 D.F, D.bar (D.bar x) = x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    rw [D.bar_eq, D.bar_eq]
    exact IsCMField.complexConj_apply_apply _ _
  have hp : (p : 𝓞 D.F) ∈ uIdeal D r := p_mem_uIdeal D r
  have hs : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r := sub_mem_uIdeal D r
  set ub : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.bar D.ω - (r : 𝓞 D.F)} with hub
  have hmap : Ideal.map D.bar (uIdeal D r) = ub := by
    simp [uIdeal, Ideal.map_span, Set.image_pair, hub]
  have hc : (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - r) = (r : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * r + D.nm := by
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    apply hw
    rw [Ideal.eq_top_iff_one]
    apply huw
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - r) * (D.bar D.ω - r)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * hc
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hs))
  have hprod : uIdeal D r * ub ≤ Ideal.span {(p : 𝓞 D.F)} := by
    obtain ⟨k, hk⟩ := hdvd
    show Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)} * ub ≤ _
    rw [hub, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [SetLike.mem_coe, hc, Ideal.mem_span_singleton]
      exact ⟨(k : 𝓞 D.F), by exact_mod_cast hk⟩
  have hsup : uIdeal D r ⊔ ub = ⊤ := by
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 D.disc_p
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    rw [Ideal.eq_top_iff_one]
    have hdiff : D.ω - D.bar D.ω ∈ uIdeal D r ⊔ ub := by
      have : D.ω - D.bar D.ω = (D.ω - r) - (D.bar D.ω - r) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hs) (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    have hpm : (p : 𝓞 D.F) ∈ uIdeal D r ⊔ ub := Ideal.mem_sup_left hp
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - D.bar D.ω) * (D.ω - D.bar D.ω)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * (D.ω + D.bar D.ω + D.tr) * D.tr_eq + 4 * (b : 𝓞 D.F) * D.nm_eq
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hdiff))
  have hcopE : uIdeal D r ^ e ⊔ ub ^ e = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hsup).pow)
  have hle : uIdeal D r ^ e * ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← mul_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hprod e
  have hinf : uIdeal D r ^ e ⊓ ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← Ideal.mul_eq_inf_of_coprime hcopE]
    exact hle
  have h1 : (1 : 𝓞 D.F) ∈ uIdeal D r ^ e ⊔ ub ^ e := by
    rw [hcopE]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  have hbz : D.bar z ∈ uIdeal D r ^ e := by
    rw [← hmap, ← Ideal.map_pow] at hz
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv D.bar z).mp hz
    rwa [hbb]
  have hup : ∀ x ∈ uIdeal D r ^ e, D.bar x ∈ ub ^ e := by
    intro x hx
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  have hx0u : z + D.bar z - 1 ∈ uIdeal D r ^ e := by
    have : z + D.bar z - 1 = D.bar z - y := by
      rw [← hyz]
      ring
    rw [this]
    exact Ideal.sub_mem _ hbz hy
  have hx0b : z + D.bar z - 1 ∈ ub ^ e := by
    have h := hup _ hx0u
    have : D.bar (z + D.bar z - 1) = z + D.bar z - 1 := by
      rw [map_sub, map_add (f := _), map_one, hbb]
      ring
    rwa [this] at h
  exact ⟨z, fun a ha => hle (Ideal.mul_mem_mul ha hz), hinf (Ideal.mem_inf.mpr ⟨hx0u, hx0b⟩), hbz⟩
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private def killedSub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S) :
    letI := ptModuleWvs o T
    Submodule (𝓞 D.F) (Additive (T ⟶ o.A)) :=
  letI := ptModuleWvs o T
  { carrier := {g | KilledBy o w g.toMul}
    zero_mem' := KilledBy.one o w T
    add_mem' := fun {g h} hg hh a ha => by
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
      show (g.toMul * h.toMul) ≫ _ = 1
      rw [mul_comp, hg a ha, hh a ha, _root_.mul_one]
    smul_mem' := fun c g hg a ha => by
      show (g.toMul ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm, map_mul, o.act.mul, ← Category.assoc, hg a ha,
        one_comp] }

theorem UpperTheory.Gal.crystallineComparison.Mod.wModEx_of :
    WModEx := by
  intro p _ D R _ b N S s o w T
  letI := ptModuleWvs o T
  have htor : Module.IsTorsionBySet (𝓞 D.F) (killedSub o w T) (w : Set (𝓞 D.F)) := by
    intro x a
    apply Subtype.ext
    show (a : 𝓞 D.F) • (x : Additive (T ⟶ o.A)) = Additive.ofMul 1
    exact x.2 a a.2
  letI : Module (𝓞 D.F ⧸ w) (killedSub o w T) := htor.module
  refine ⟨⟨killedSub o w T, fun x => Additive.toMul (x : Additive (T ⟶ o.A)), ?_, ?_, ?_, ?_⟩⟩
  · intro x y h
    exact Subtype.ext (Additive.toMul.injective h)
  · intro g
    constructor
    · rintro ⟨h, rfl⟩
      exact h.2
    · intro hg
      exact ⟨⟨Additive.ofMul g, hg⟩, rfl⟩
  · intro x y
    rfl
  · intro a x
    rw [Module.IsTorsionBySet.mk_smul]
    rfl
end
