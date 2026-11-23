module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle622
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle117
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory GlobalTheory.PointQuot

private theorem constObj_hom_ext {S : Scheme} {I : Type} {Z : Over S} (f₁ f₂ : constObj S I ⟶ Z)
    (h : ∀ c, PointQuot.constPt S c ≫ f₁ = PointQuot.constPt S c ≫ f₂) : f₁ = f₂ := by
  ext : 1
  apply Sigma.hom_ext
  intro c
  have := congrArg Over.Hom.left (h c)
  exact this

theorem UpperTheory.Gal.crystallineComparison.Mod.constSub_of : ConstSub := by
  intro K _ A _ hsep Γ hfin
  have hinj : Function.Injective (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) := Subtype.val_injective
  haveI hmono : Mono (constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A))) := mono_constDesc _ hinj
  obtain ⟨hG, hmon⟩ := exists_grpObj_constObj (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) Γ
    Subtype.range_coe
  have hsplit : FinEt.IsSplitOfRank (constObj (Sp K) Γ).hom (Nat.card Γ) := by
    rw [FinEt.isSplitOfRank_iff_exists_iso]
    refine ⟨Sigma.reindex (Finite.equivFin Γ).symm (fun _ => Sp K), ?_⟩
    apply Sigma.hom_ext
    intro j
    have h := Sigma.ι_reindex_hom (Finite.equivFin Γ).symm (fun _ : Γ => Sp K) j
    simp only [constObj, Over.mk_hom]
    rw [← Category.assoc]
    erw [h]
    simp
  haveI := hsplit.isFinite
  haveI := hsplit.etale
  refine ⟨constObj (Sp K) Γ, hG, constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)), hmon, hmono,
    hsplit.isFinite, hsplit.etale, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsplit.isFinite, (inferInstance : Flat (constObj (Sp K) Γ).hom), ?_, hsplit.finrank_eq⟩
    let c0 : Γ := ⟨1, Γ.one_mem⟩
    have hw : (PointQuot.constPt (Sp K) c0).left ≫ (toUnit (constObj (Sp K) Γ)).left = 𝟙 _ := by
      rw [← Over.comp_left]
      simp
    refine ⟨fun y => ⟨(PointQuot.constPt (Sp K) c0).left y, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, hw]
    rfl
  · intro g
    constructor
    · rintro ⟨y, hy⟩
      let z : (𝟙_ (Over (Sp K))).left := (⊥ : PrimeSpectrum K)
      obtain ⟨V, hzV, c, hc⟩ := locally_const_desc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) y z
      haveI : Nonempty (openObj (𝟙_ (Over (Sp K))) V).left := ⟨⟨z, hzV⟩⟩
      haveI := epi_toUnit (openObj (𝟙_ (Over (Sp K))) V)
      have e : openι (𝟙_ (Over (Sp K))) V = toUnit _ := toUnit_unique _ _
      rw [hy, e] at hc
      have := (cancel_epi _).1 hc
      rw [this]
      exact c.2
    · intro hg
      exact ⟨PointQuot.constPt (Sp K) (⟨g, hg⟩ : Γ), constPt_desc _ _⟩
  · intro α hα
    apply constObj_hom_ext
    intro c
    rw [← Category.assoc, constPt_desc]
    exact (hα _ c.2).trans (comp_one _).symm
  · intro α hα
    refine ⟨constDesc (fun c : Γ => PointQuot.constPt (Sp K) (⟨c.1 ≫ α, hα _ c.2⟩ : Γ)), ?_⟩
    apply constObj_hom_ext
    intro c
    simp only [← Category.assoc, constPt_desc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma ofFn_prod_one {X : Type*} [Monoid X] {n : ℕ} (h : n = 1) (f : Fin n → X) :
    (List.ofFn f).prod = f ⟨0, by omega⟩ := by
  subst h; simp

private lemma alg_core {F κ V : Type} [CommRing F] [Field κ] [AddCommGroup V] [Module κ V] (p : ℕ) [CharP κ p]
    (T : F →+* Module.End κ V) (u : Ideal F) (α α' : F)
    (h1 : ∀ a ∈ u, a * α ∈ Ideal.span {(p : F)})
    (h2 : α + α' - 1 ∈ Ideal.span {(p : F)}) (h3 : α' ∈ u)
    (v : V) (e : ℕ) (hv : ∀ a ∈ u ^ e, T a v = 0) : ∀ a ∈ u, T a v = 0 := by
  have hp : ∀ x ∈ Ideal.span {(p : F)}, T x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_natCast]
    have hz : ((p : ℕ) : Module.End κ V) = 0 := by
      ext y
      rw [natCast_apply_eq_smul, ← Nat.cast_smul_eq_nsmul κ, CharP.cast_eq_zero, zero_smul]
      rfl
    rw [hz, mul_zero]
  have key : ∀ a ∈ u, T a = T (a * α') := by
    intro a ha
    have e1 : T (a * (α + α' - 1)) = 0 := hp _ (Ideal.mul_mem_left _ _ h2)
    have e2 : T (a * α) = 0 := hp _ (h1 a ha)
    have hs : a * α' = a + a * (α + α' - 1) - a * α := by ring
    rw [hs, map_sub, map_add (f := _), e1, e2]
    simp
  intro a ha
  have step : ∀ k : ℕ, T a = T (a * α' ^ k) ∧ a * α' ^ k ∈ u ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      obtain ⟨h, hm⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [h, key _ (Ideal.pow_le_self (Nat.succ_ne_zero k) hm), pow_succ, _root_.mul_assoc]
      · rw [pow_succ α', ← _root_.mul_assoc, pow_succ u]
        exact Ideal.mul_mem_mul hm h3
  obtain ⟨h, hm⟩ := step e
  rw [h]
  exact hv _ (Ideal.pow_le_pow_right (Nat.le_succ e) hm)

private lemma comp_idpow {S : Scheme.{0}} {T G : Over S} [GrpObj G] (g : T ⟶ G) (n : ℕ) :
    g ≫ (𝟙 G) ^ n = g ^ n := by
  rw [MonObj.comp_pow, Category.comp_id]

private lemma tan_pow {κ : Type} [Field κ] (p : ℕ) [CharP κ p] {S : Scheme.{0}} (x : Sp κ ⟶ S) (G : Over S)
    [GrpObj G] [IsCommMonObj G] (g : epsPtR x ⟶ G) (hg : g ∈ GlobalTheory.TanPtMod.tanSub x G) (n : ℕ) (hn : p ∣ n) :
    g ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hv : (p * m) • (Additive.ofMul (⟨g, hg⟩ : GlobalTheory.TanPtMod.tanSub x G) : GlobalTheory.TanPtMod.Tan x G) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul κ, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_smul]
  have h2 := congrArg (fun w => ((Additive.toMul w : GlobalTheory.TanPtMod.tanSub x G) : epsPtR x ⟶ G)) hv
  simpa using h2

private theorem left_one_eq_hom_comp_eta {S : Scheme.{0}} {T A : Over S} [GrpObj A] :
    Over.Hom.left (1 : T ⟶ A) = T.hom ≫ Over.Hom.left (η[A] : 𝟙_ (Over S) ⟶ A) := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

private theorem left_one_algPt_dualNumber_eq_epsPtR {κ : Type} [Field κ] {A : Over (Sp κ)} [GrpObj A] :
    Over.Hom.left (1 : algPt κ (DualNumber κ) ⟶ A) = Over.Hom.left (1 : epsPtR (𝟙 (Sp κ)) ⟶ A) := by
  rw [left_one_eq_hom_comp_eta, left_one_eq_hom_comp_eta]
  simp

theorem UpperTheory.Gal.crystallineComparison.Mod.tanOne_of :
    UElt → TanOne := by
  intro hU p _ D R _ b N hm ha r w hw κ _ _ _ β hβ o e
  have i0 : Fin D.a := ⟨0, by omega⟩
  have j0 : Fin D.m := ⟨0, by omega⟩
  have hi : ∀ i j : Fin D.a, i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hj : ∀ i j : Fin D.m, i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hwt : w ≠ ⊤ := by
    intro h
    have h0 := hβ i0 1 (h ▸ Submodule.mem_top)
    simp at h0
  obtain ⟨α, h1, h2, h3⟩ := hU p D r w hwt hw 1
  simp only [pow_one] at h1 h2 h3
  have hρ : β b.ρ = (r : κ) := by
    have h0 := hβ i0 _ (hw (sub_mem_uIdeal D r))
    rw [map_sub, map_sub, b.t_ω, map_intCast, map_intCast, sub_eq_zero] at h0
    exact h0
  let Tm : 𝓞 D.F →+* Module.End κ (GlobalTheory.TanPtMod.Tan (𝟙 (Sp κ)) o.A) :=
    (GlobalTheory.TanPtMod.actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  let toE : (algPt κ (DualNumber κ) ⟶ o.A) → (epsPtR (𝟙 (Sp κ)) ⟶ o.A) :=
    fun v => Over.homMk v.left (by simp)
  let frE : (epsPtR (𝟙 (Sp κ)) ⟶ o.A) → (algPt κ (DualNumber κ) ⟶ o.A) :=
    fun v => Over.homMk v.left (by simp)
  have eig : ∀ v : algPt κ (DualNumber κ) ⟶ o.A, Inf (TrivSqZeroExt.fstHom κ κ κ) v →
      (∃ e', KilledBy o (uIdeal D r ^ e') v) →
      IsLieEigen (OActN.toF D o.act) (𝟙 (Sp κ)) (β.comp (b.t i0)) (toE v) := by
    intro v hinf ⟨e', hk⟩
    have hmem : toE v ∈ GlobalTheory.TanPtMod.tanSub (𝟙 (Sp κ)) o.A := by
      exact (GlobalTheory.TanPtMod.mem_tanSub_iff _ _ _).2 hinf
    have hkill : ∀ a ∈ uIdeal D r ^ e', Tm a (GlobalTheory.TanPtMod.Tan.mk (toE v) hmem) = 0 := by
      intro a ha'
      apply GlobalTheory.TanPtMod.Tan.ext
      show toE v ≫ o.act.act (algebraMap _ _ a) = 1
      ext1
      have h4 := congrArg Over.Hom.left (hk a ha')
      rw [Over.comp_left] at h4
      rw [Over.comp_left]
      exact h4.trans left_one_algPt_dualNumber_eq_epsPtR
    have hu := alg_core p Tm (uIdeal D r) α (D.bar α) h1 h2 h3 _ e' hkill
    have hsc : IsTanScal o.act (𝟙 (Sp κ)) (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) (toE v) := by
      refine ⟨?_, ?_⟩
      · rw [GlobalTheory.TanPtMod.mem_tanSub_iff] at hmem
        exact hmem
      · have hz := hu _ (sub_mem_uIdeal D r)
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero, map_intCast] at hz
        have hz2 := congrArg GlobalTheory.TanPtMod.Tan.hom hz
        rw [intCast_apply_eq_smul, ← Int.cast_smul_eq_zsmul κ, GlobalTheory.TanPtMod.Tan.hom_smul] at hz2
        rw [hρ]
        exact congrArg Over.Hom.left hz2
    obtain ⟨w', hw', hprod⟩ := o.lie κ β (𝟙 (Sp κ)) (Category.id_comp _) (toE v) hsc
    rw [ofFn_prod_one ha, hi ⟨0, _⟩ i0] at hprod
    refine ⟨hsc.1, fun c => ?_⟩
    have h5 := (hw' i0 c).2
    rw [← hprod] at h5
    exact h5
  obtain ⟨vs, hvs, huniq⟩ := o.lieRank κ (𝟙 (Sp κ)) β (Category.id_comp _) i0
  refine ⟨frE (vs j0), ⟨?_, 1, ?_⟩, ?_, ?_⟩
  · ext1
    rw [Over.comp_left, left_one_algPt_dualNumber_eq_epsPtR]
    have hm0 : vs j0 ∈ GlobalTheory.TanPtMod.tanSub (𝟙 (Sp κ)) o.A := by
      rw [GlobalTheory.TanPtMod.mem_tanSub_iff]
      exact (hvs j0).1
    have h6 := tan_pow p (𝟙 (Sp κ)) o.A (vs j0) hm0 (p ^ (e + 1)) (dvd_pow_self p (Nat.succ_ne_zero e))
    rw [← comp_idpow] at h6
    exact congrArg Over.Hom.left h6
  · intro a ha'
    rw [pow_one] at ha'
    ext1
    rw [Over.comp_left, left_one_algPt_dualNumber_eq_epsPtR]
    have hz : β (b.t i0 a) = 0 := hβ i0 a (hw ha')
    have h7 := (hvs j0).2 a
    rw [RingHom.comp_apply, hz] at h7
    have h0 := congrArg Over.Hom.left (GlobalTheory.GrpTangentPt.epsScalePt_zero_comp (𝟙 (Sp κ)) (hvs j0).1)
    rw [← h0]
    exact h7
  · exact (hvs j0).1
  · intro v ⟨_, hk⟩ hinf
    obtain ⟨c, ⟨u', hu', hprod⟩, -⟩ := huniq (toE v) (eig v hinf hk)
    rw [ofFn_prod_one hm, hj ⟨0, _⟩ j0] at hprod
    refine ⟨c j0, ?_⟩
    have h8 := hu' j0
    rw [← hprod] at h8
    exact h8
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem pt_core {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s} {o₁ o₁' : Obj b N s'}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A)
    (hsq : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (T : Over S') (g : T ⟶ o₁.A) :
    (g ≫ ψ₁ = 1 ↔ m.ptEquiv T g ≫ ψ = 1) ∧ (g = 1 ↔ m.ptEquiv T g = 1) ∧
      ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I (m.ptEquiv T g) := by
  have key : m'.ptEquiv T (g ≫ ψ₁) = m.ptEquiv T g ≫ ψ := by
    apply Over.OverMorphism.ext
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, ← hsq,
      Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key, MulEquiv.map_eq_one_iff]
  · rw [MulEquiv.map_eq_one_iff]
  · intro I
    unfold KilledBy
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]

theorem UpperTheory.Gal.crystallineComparison.Mod.pullKer_of :
    PullKer := by
  intro p _ D R _ b N S S' s s' f o o' o₁ o₁' m m' ψ ψ₁ hsq
  refine ⟨?_, ?_⟩
  · intro T T₀ h g g₀ hg₀
    have hw : T₀.hom = eqToHom h ≫ T.hom ≫ f := by
      have e1 := Over.w g₀
      have e2 := Over.w (m.ptEquiv T g)
      rw [ObjMap.ptEquiv_left] at e2
      simp only [Category.assoc] at e2
      rw [← e1, hg₀]
      simp only [Category.assoc]
      rw [e2]
      rfl
    obtain ⟨L, ⟨⟨⟩⟩, hom⟩ := T₀
    change L = T.left at h
    subst h
    simp only [eqToHom_refl, Category.id_comp] at hw hg₀
    subst hw
    have hg : g₀ = m.ptEquiv T g := by
      apply Over.OverMorphism.ext
      rw [ObjMap.ptEquiv_left, hg₀]
    subst hg
    exact pt_core m m' ψ ψ₁ hsq T g
  · intro r w j htj k _ _ _ x
    obtain ⟨h1, h2⟩ := htj k (x ≫ f)
    have c := fun g => pt_core m m' ψ ψ₁ hsq (Over.mk x) g
    refine ⟨fun g hg he => ?_, ?_⟩
    · rw [(c g).2.2 w]
      obtain ⟨n, hn⟩ := he
      exact h1 _ ((c g).1.mp hg) ⟨n, ((c g).2.2 _).mp hn⟩
    · rw [← h2]
      exact Nat.card_congr ((m.ptEquiv (Over.mk x)).toEquiv.subtypeEquiv fun g => by
        rw [(c g).1, (c g).2.2 w]
        rfl)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private noncomputable def frPt {κ Λ Λ' : Type} [Field κ] [CommRing Λ] [CommRing Λ'] [Algebra κ Λ] [Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ') : algPt κ Λ' ⟶ algPt κ Λ :=
  Over.homMk (spMap σ) (by
    change spMap σ ≫ spMap (algebraMap κ Λ) = spMap (algebraMap κ Λ')
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ])

private theorem frob_mid (hI : InfE) {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {r : ℤ} {κ : Type} [Field κ] {s : Sp κ ⟶ Sp R} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} {d : ℕ}
    (hrep : RepAlg o.A (UKer r o ψ) d)
    (hcard : Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [IsLocalRing Λ'] [Algebra κ Λ] [algΛ' : Algebra κ Λ']
    (σ : Λ →+* Λ') (hσ : σ.comp (algebraMap κ Λ) = algebraMap κ Λ')
    (ε : Λ →ₐ[κ] κ) (ε' : Λ' →+* κ) (h1 : ∀ c, ε' (algebraMap κ Λ' c) = c)
    (h2 : ε'.comp σ = ε.toRingHom) (g : algPt κ Λ ⟶ o.A)
    (hK : ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) (hinf : Inf ε g)
    (hker : spMap σ ≫ (g ≫ ψ).left = spMap σ ≫ (1 : algPt κ Λ ⟶ o'.A).left) :
    spMap σ ≫ g.left = spMap σ ≫ (1 : algPt κ Λ ⟶ o.A).left := by
  let ε'' : Λ' →ₐ[κ] κ := { ε' with commutes' := h1 }
  have hfl : (frPt σ hσ).left = spMap σ := rfl
  have hone : ∀ {X Y A : Over (Sp κ)} [GrpObj A] (f : X ⟶ Y), f ≫ (1 : Y ⟶ A) = 1 := by
    intro X Y A _ f
    simp [Hom.one_def]
  have hcomp : spMap ε''.toRingHom ≫ spMap σ = spMap ε.toRingHom := by
    rw [spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h2]
  have hgψ : (frPt σ hσ ≫ g) ≫ ψ = 1 := by
    rw [← hone (frPt σ hσ)]
    ext1
    simp only [Over.comp_left] at hker ⊢
    rw [hfl, Category.assoc]
    exact hker
  obtain ⟨e, he⟩ := hK
  have hP : UKer r o ψ (algPt κ Λ') (frPt σ hσ ≫ g) := by
    refine ⟨hgψ, e, ?_⟩
    intro a ha
    rw [Category.assoc, he a ha, hone]
  have hinf' : Inf ε'' (frPt σ hσ ≫ g) := by
    unfold Inf at hinf ⊢
    rw [Over.comp_left, hfl, ← Category.assoc, hcomp]
    exact hinf
  have h0 := hI κ o.A (UKer r o ψ) d hrep hcard Λ' ε'' (frPt σ hσ ≫ g) hP hinf'
  have h0' := congrArg Over.Hom.left (h0.trans (hone (frPt σ hσ)).symm)
  simp only [Over.comp_left] at h0'
  exact h0'

theorem UpperTheory.Gal.crystallineComparison.Mod.frobPass_of :
    InfE → FrobPass := by
  intro hI p _ D R _ b N r f κ _ _ _ s o o' ψ hψ d hrep hcard
  haveI := hψ
  have hp : Nat.Prime p := Fact.out
  have hone' : ∀ {X A B : Over (Sp κ)} [GrpObj A] [GrpObj B] (h : A ⟶ B) [IsMonHom h], (1 : X ⟶ A) ≫ h = 1 := by
    intro X A B _ _ h _
    simp [Hom.one_def]
  let φ : κ ≃+* κ := iterateFrobeniusEquiv κ p f
  have hφ : ∀ c : κ, φ c = c ^ p ^ f := fun c => rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    have h0 := GlobalTheory.SS.FrobField.cast_zero_sp κ (CharP.cast_eq_zero κ p)
    have e := GlobalTheory.SS.FrobField.absFrob_spec κ p f hp h0 φ.toRingHom hφ
    have hk : spMap φ.toRingHom ≫ g.left = spMap φ.toRingHom ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
      rw [← e]
      exact hg h0
    have hinv : spMap φ.symm.toRingHom ≫ spMap φ.toRingHom = 𝟙 _ := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      simp
    ext1
    calc g.left = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ g.left := by rw [hinv, Category.id_comp]
      _ = (spMap φ.symm.toRingHom ≫ spMap φ.toRingHom) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ o'.A).left := by
        rw [Category.assoc, hk, ← Category.assoc]
      _ = _ := by rw [hinv, Category.id_comp]
  · intro Λ _ _ _ ε g hK hinf
    have hΛ : (p : Λ) = 0 := by
      rw [← map_natCast (algebraMap κ Λ), CharP.cast_eq_zero, map_zero]
    let τ := GlobalTheory.SS.FrobField.powHom Λ p f hp hΛ
    have hτ : ∀ c : Λ, τ c = c ^ p ^ f := fun c => rfl
    let ε' : Λ →+* κ := φ.symm.toRingHom.comp ε.toRingHom
    have h2 : ε'.comp τ = ε.toRingHom := by
      ext x
      show φ.symm (ε (x ^ p ^ f)) = ε x
      rw [map_pow, ← hφ, RingEquiv.symm_apply_apply]
    constructor
    · intro hk h
      have e := GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h τ hτ
      have hker : spMap τ ≫ (g ≫ ψ).left = spMap τ ≫ (1 : algPt κ Λ ⟶ o'.A).left := by
        rw [← e]
        exact hk h
      have h1 : ∀ c : κ, ε' (@algebraMap κ Λ _ _ (τ.comp (algebraMap κ Λ)).toAlgebra c) = c := by
        intro c
        show (ε'.comp τ) (algebraMap κ Λ c) = c
        rw [h2]
        exact ε.commutes c
      have := frob_mid hI hrep hcard (Λ' := Λ) (algΛ' := (τ.comp (algebraMap κ Λ)).toAlgebra) τ rfl ε ε' h1 h2 g
        ⟨hK.choose, hK.choose_spec⟩ hinf hker
      rw [← e] at this
      exact this
    · intro hk h
      have h' := hk h
      rw [Over.comp_left, ← Category.assoc, h', Category.assoc, ← Over.comp_left, hone']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.sameE_of :
    KillLocal → InfE → SameE := by
  intro hK hI p _ D R _ b N r κ _ _ s o o₁ o₂ ψ₁ ψ₂ hψ₂ hsub d hrep hcard hkill T g hg
  refine ⟨hK κ o.A o₂.A ψ₂ hψ₂ (UKer r o ψ₁) d hrep hsub hkill ?_ T g hg, hg.2⟩
  intro Λ _ _ _ ε g' hP hinf
  rw [hI κ o.A (UKer r o ψ₁) d hrep hcard Λ ε g' hP hinf]
  exact MonObj.one_comp _
end
