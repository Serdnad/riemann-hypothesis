module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle016
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle073
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle076
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
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
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem _root_.GlobalTheory.T.conjugateSection_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  first | exact @GlobalTheory.GalTw.galRul_sec_val_semilinear | exact GlobalTheory.GalTw.galRul_sec_val_semilinear | (intros; apply GlobalTheory.GalTw.galRul_sec_val_semilinear <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem finite_latMod (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LatMod Dw k) := by
  haveI := Dw.fin
  haveI : Module.Finite ℤ (LatMod Dw k) := Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion (M := LatMod Dw k) fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
  change (k : ℤ) • Submodule.mkQ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) x = 0
  rw [natCast_zsmul, ← map_nsmul]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_levGrp (Dw : Datum H) {k : ℕ} (hk : 0 < k) : Finite (LevGrp Dw k) := by
  haveI := finite_latMod Dw hk
  exact Finite.of_injective (fun g : LevGrp Dw k => (g : LatMod Dw k → LatMod Dw k)) DFunLike.coe_injective

theorem map_etaExpr {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {k : ℕ} (hk : 0 < k) {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) :
    φ (etaExpr k cf x w) = etaExpr k cf x (fun q => φ (w q)) := by
  haveI := finite_levGrp Dw hk
  haveI := Fintype.ofFinite (LevGrp Dw k)

  simp only [etaExpr, finprod_eq_prod_of_fintype, map_prod, map_sum, map_mul, map_intCast]

theorem etaExpr_comp {S : Type} [CommRing S] {k : ℕ} {J : Type} [Fintype J]
    {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) (g₀ : LevGrp Dw k) :
    etaExpr k cf x (fun q => w (g₀ q)) = etaExpr k cf x w := by
  unfold etaExpr
  exact finprod_eq_of_bijective (fun g : LevGrp Dw k => g₀ * g) (Group.mulLeft_bijective g₀) fun g => rfl

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_level_baseChange (hL : Laws) {R : ℕ} (hR : Odd R) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)} {w : LatMod Dw (R ^ 4) → S}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) :
    ∃ ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G), IsFullLev Xo (R ^ 4) z.x ev' ∧
      ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (ψ (w q)) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  refine ⟨fun q => h ≫ ev q,
    ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S T ψ.toRingHom y.x z.x h rfl ev hev).1, fun q => ?_⟩
  exact (GlobalTheory.T.thetaNullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).2.1 S T ψ y z hm (ev q) (h ≫ ev q) rfl _ (hw q)

theorem existsUnique_nullVal (hL : Laws) {R : ℕ} (hR : Odd R) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} {ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)}
    (hev : IsFullLev Xo (R ^ 4) y.x ev) (q : LatMod Dw (R ^ 4)) : ∃! w, IsNullVal Xo c (R ^ 2) y (ev q) w := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine (GlobalTheory.T.thetaNullValue_existsUnique_natural_linear hL E H Dw l Xo c (R ^ 2) hR.pow).1 S y (ev q) ?_
  have h1 := ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.1 S S (RingHom.id S) y.x y.x (𝟙 _)
    (by simp [spMap]) ev hev).2 q
  rw [← pow_mul]
  exact h1

theorem etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T}
    {ev ev' : LatMod Dw (R ^ 4) → (ptO Xo z.x ⟶ Xo.univ.t.G)} {w w' : LatMod Dw (R ^ 4) → T}
    (hev : IsFullLev Xo (R ^ 4) z.x ev) (hw : ∀ q, IsNullVal Xo c (R ^ 2) z (ev q) (w q))
    (hev' : IsFullLev Xo (R ^ 4) z.x ev') (hw' : ∀ q, IsNullVal Xo c (R ^ 2) z (ev' q) (w' q)) :
    etaExpr (R ^ 4) cf x w = etaExpr (R ^ 4) cf x w' := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  refine Module.eq_of_localization_maximal (R := T) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap T (Localization.AtPrime P)) _ _ fun P _ => ?_
  let ψ : T →ₐ[c.F] Localization.AtPrime P := IsScalarTower.toAlgHom c.F T _
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c T _ ψ z
  obtain ⟨e, he, hv⟩ := exists_level_baseChange hL hR ψ hu hev hw
  obtain ⟨e', he', hv'⟩ := exists_level_baseChange hL hR ψ hu hev' hw'
  obtain ⟨g, hg⟩ := ((GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).2.2.1 _ u.x e he).2 e' he'
  have hww : (fun q => ψ (w' q)) = fun q => ψ (w (g q)) := funext fun q =>
    (existsUnique_nullVal hL hR he (g q)).unique (hg q ▸ hv' q) (hv (g q))
  change algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w) =
    algebraMap T (Localization.AtPrime P) (etaExpr (R ^ 4) cf x w')
  rw [map_etaExpr _ hk, map_etaExpr _ hk]
  exact (etaExpr_comp cf x (fun q => ψ (w q)) g).symm.trans (congrArg _ hww.symm)

theorem map_etaExpr_eq_of_levels (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S₁ S₂ T : Type} [CommRing S₁] [Algebra c.F S₁] [CommRing S₂] [Algebra c.F S₂]
    [CommRing T] [Algebra c.F T] (ψ₁ : S₁ →ₐ[c.F] T) (ψ₂ : S₂ →ₐ[c.F] T) {y₁ : FrPt Xo c S₁} {y₂ : FrPt Xo c S₂}
    {z : FrPt Xo c T} (h₁ : FrMap ψ₁ y₁ z) (h₂ : FrMap ψ₂ y₂ z)
    {ev₁ : LatMod Dw (R ^ 4) → (ptO Xo y₁.x ⟶ Xo.univ.t.G)} {w₁ : LatMod Dw (R ^ 4) → S₁}
    {ev₂ : LatMod Dw (R ^ 4) → (ptO Xo y₂.x ⟶ Xo.univ.t.G)} {w₂ : LatMod Dw (R ^ 4) → S₂}
    (hev₁ : IsFullLev Xo (R ^ 4) y₁.x ev₁) (hw₁ : ∀ q, IsNullVal Xo c (R ^ 2) y₁ (ev₁ q) (w₁ q))
    (hev₂ : IsFullLev Xo (R ^ 4) y₂.x ev₂) (hw₂ : ∀ q, IsNullVal Xo c (R ^ 2) y₂ (ev₂ q) (w₂ q)) :
    ψ₁ (etaExpr (R ^ 4) cf x w₁) = ψ₂ (etaExpr (R ^ 4) cf x w₂) := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨e₁, he₁, hv₁⟩ := exists_level_baseChange hL hR ψ₁ h₁ hev₁ hw₁
  obtain ⟨e₂, he₂, hv₂⟩ := exists_level_baseChange hL hR ψ₂ h₂ hev₂ hw₂
  exact (map_etaExpr ψ₁.toRingHom hk cf x w₁).trans
    ((etaExpr_eq_of_levels hL hR cf x he₁ hv₁ he₂ hv₂).trans (map_etaExpr ψ₂.toRingHom hk cf x w₂).symm)

theorem map_eq_of_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} {cf : J → ℤ}
    {x : J → Fin n → LatMod Dw (R ^ 4)} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {y₀ : FrPt Xo c S} {y : FrPt Xo c T} (hm : FrMap φ y₀ y) {v₀ : S} {v : T}
    (h₀ : EtaValAt Xo c R cf x y₀ v₀) (h : EtaValAt Xo c R cf x y v) : φ v₀ = v := by
  obtain ⟨S', _, _, α, y₀', ev₀, w₀, hα, hmα, hev₀, hw₀, e₀⟩ := h₀
  obtain ⟨T', _, _, β, y', ev, w, hβ, hmβ, hev, hw, e⟩ := h
  obtain ⟨U, _, _, ψ₁, ψ₂, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F S T' S' (β.comp φ) α hα
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c T' U ψ₁ y'
  have hz₀ : FrMap (ψ₂.comp α) y₀ z :=
    hc ▸ FramedBaseChange.trans _ ψ₁ (FramedBaseChange.trans φ β hm hmβ) hz
  have key := map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel α ψ₂ hmα hz₀) hev hw hev₀ hw₀
  have hβi : Function.Injective β := hβ.injective
  refine hβi (hinj ?_)
  rw [e, key, ← e₀]
  exact DFunLike.congr_fun hc v₀

theorem exists_etaValAt (hL : Laws) {R : ℕ} (hR : Odd R) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw (R ^ 4)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ∃ v, EtaValAt Xo c R cf x y v := by
  have hk : 0 < R ^ 4 := pow_pos hR.pos _
  obtain ⟨B, _, φ₀, ev₀, hφ, hev₀⟩ := (GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo _ hk).1 S y.x
  letI : Algebra c.F B := (φ₀.comp (algebraMap c.F S)).toAlgebra
  let φ : S →ₐ[c.F] B := { φ₀ with commutes' := fun _ => rfl }
  obtain ⟨y', hm⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S B φ y
  obtain ⟨ev, hev⟩ : ∃ ev, IsFullLev Xo (R ^ 4) y'.x ev := by
    rw [hm.1]
    exact ⟨ev₀, hev₀⟩
  choose w hw using fun q => (existsUnique_nullVal hL hR hev q).exists
  obtain ⟨v, hv, -⟩ := GlobalTheory.existsUnique_preimage_of_faithfullyFlat c.F S B φ hφ (etaExpr (R ^ 4) cf x w)
    fun T _ _ ψ₁ ψ₂ hc => by
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c B T ψ₁ y'
      have hz₀ : FrMap (ψ₂.comp φ) y z := hc ▸ FramedBaseChange.trans φ ψ₁ hm hz
      exact map_etaExpr_eq_of_levels hL hR cf x ψ₁ ψ₂ hz (FramedBaseChange.cancel φ ψ₂ hm hz₀) hev hw hev hw
  exact ⟨v, B, inferInstance, inferInstance, φ, y', ev, w, hφ, hm, hev, hw, hv⟩

theorem etaValAt_existsUnique_natural : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4)), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, EtaValAt Xo c R cf x y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, EtaValAt Xo c R cf x y0 v0 → EtaValAt Xo c R cf x y v → φ v0 = v := by
  intro hL E _ _ _ H Dw l Xo c R hR J _ n cf x
  refine ⟨fun S _ _ y => ?_, fun S T _ _ _ _ φ y₀ y hm v₀ v h₀ h => map_eq_of_etaValAt hL hR φ hm h₀ h⟩
  obtain ⟨v, hv⟩ := exists_etaValAt hL hR cf x y
  exact ⟨v, hv, fun v' hv' => map_eq_of_etaValAt hL hR (AlgHom.id c.F S) (FramedBaseChange.refl y) hv' hv⟩

end GlobalTheory.EtaForm
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem _root_.GlobalTheory.T.exists_base_embedding_reading_forms : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)), ∃ (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e := by
  first | exact @GlobalTheory.Shares.exists_isRdgU | exact GlobalTheory.Shares.exists_isRdgU | (intros; apply GlobalTheory.Shares.exists_isRdgU <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

theorem _root_.GlobalTheory.T.ruleBaseChange_section_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  first | exact @GlobalTheory.FieldBC.rulBC_sec_val_linear | exact GlobalTheory.FieldBC.rulBC_sec_val_linear | (intros; apply GlobalTheory.FieldBC.rulBC_sec_val_linear <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in
theorem _root_.GlobalTheory.FieldBC.exists_emb_ext {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (hle : c.F ≤ c'.F) (σ : c.F →+* ℂ) :
    ∃ σ' : c'.F →+* ℂ, σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle) = σ := by
  letI : Algebra c.F c'.F := (_root_.Formalism.L2.Pj.incF c c' hle).toAlgebra
  letI : Algebra c.F ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic ℚ c'.F := Algebra.IsAlgebraic.of_finite ℚ c'.F
  haveI : Algebra.IsAlgebraic c.F c'.F := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let τ : c'.F →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨τ.toRingHom, ?_⟩
  ext x
  exact τ.commutes x


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in
theorem _root_.GlobalTheory.FieldBC.rulBC_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)
    (hle : c.F ≤ c'.F) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ)
    (n : ℕ), ∀ f ∈ _root_.Formalism.L2.Pj.sec Xo c a n,
    (∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f) ∧
    (_root_.GlobalTheory.FieldBC.rulBC hle f ∈ _root_.Formalism.L2.Pj.cusp Xo c' (_root_.Formalism.L2.Pj.unfBC hle U) a n ↔ f ∈ _root_.Formalism.L2.Pj.cusp Xo c U a n) := by
  intro E _ _ _ H Dw l Xo c c' hle r U a n f hf
  obtain ⟨hsec, hval⟩ := (_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf
  have hread : ∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f := by
    intro σ'
    have hbc : _root_.Formalism.L2.Pj.IsBC hle (_root_.GlobalTheory.FieldBC.rulBC hle f) ![1] ![f] := by
      unfold _root_.Formalism.L2.Pj.IsBC
      intro S _ _ _ h y
      simp [hval S h y]
    rw [_root_.Formalism.L2.Pj.rdU_unfBC hle U σ' hbc, Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero, map_one]
    exact one_smul ℂ _
  refine ⟨hread, ?_⟩
  rw [_root_.Formalism.L2.Pj.mem_cusp, _root_.Formalism.L2.Pj.mem_cusp]
  constructor
  · rintro ⟨-, hcusp⟩
    refine ⟨hf, fun σ hσ => ?_⟩
    obtain ⟨σ', rfl⟩ := _root_.GlobalTheory.FieldBC.exists_emb_ext hle σ
    have hmem := hcusp σ' (_root_.Formalism.L2.Pj.goodEmb_ext hle hσ rfl)
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC] at hmem
    exact hmem
  · rintro ⟨-, hcusp⟩
    refine ⟨hsec, fun σ' hσ' => ?_⟩
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC]
    exact hcusp _ (by unfold _root_.Formalism.L2.Pj.GoodEmb at hσ' ⊢; exact hσ')

end GlobalTheory.FieldBC
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.SecRelation

theorem coeff_aeval_C_mul_X {K Ω σ : Type} [Field K] [Field Ω] [Algebra K Ω] [Fintype σ] (v : σ → Ω)
    (P : MvPolynomial σ K) (d : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff d =
      MvPolynomial.aeval v (MvPolynomial.homogeneousComponent d P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    have h : MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) (MvPolynomial.monomial s a) =
        Polynomial.C (MvPolynomial.aeval v (MvPolynomial.monomial s a)) * Polynomial.X ^ s.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow,
        Polynomial.algebraMap_apply, Finsupp.degree_apply, mul_assoc]
    rw [h, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]

theorem exists_isHomogeneous_aeval_eq_zero {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (hD : Algebra.trdeg K Ω = D) (hm : D + 2 ≤ m) (v : Fin m → Ω) :
    ∃ (Q : MvPolynomial (Fin m) K) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval v Q = 0 := by
  have htr : Algebra.trdeg K (Polynomial Ω) = ((D + 1 : ℕ) : Cardinal) := by
    rw [← trdeg_add_eq K Ω (A := Polynomial Ω), Polynomial.trdeg_of_isDomain, hD]
    push_cast
    rfl
  have hdep : ¬ AlgebraicIndependent K (fun i => Polynomial.C (v i) * Polynomial.X) := by
    intro h
    have h1 := h.cardinalMk_le_trdeg
    rw [htr, Cardinal.mk_fin, Nat.cast_le] at h1
    omega
  rw [algebraicIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨P, hP, hP0⟩ := hdep
  have hex : ∃ d, MvPolynomial.homogeneousComponent d P ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hP0
    rw [← MvPolynomial.sum_homogeneousComponent P]
    exact Finset.sum_eq_zero fun d _ => hall d
  obtain ⟨d, hd⟩ := hex
  refine ⟨_, d, hd, MvPolynomial.homogeneousComponent_isHomogeneous d P, ?_⟩
  rw [← coeff_aeval_C_mul_X, hP, Polynomial.coeff_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => ?_, fun p t y y' _ => ?_⟩
  · show (1 : q.R) = φ 1
    rw [map_one]
  · show (1 : p.R) = wchar (ex Dw 0 0) t * 1
    have : ex Dw (0 : (E →+* ℂ) × ℕ → ℕ) 0 = fun _ => 0 := by funext i; cases i <;> rfl
    simp [wchar, this]

theorem multiset_prod_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) (s : Multiset σ) :
    (s.map u).prod ∈ sec Xo c (s.card • a) (s.card • n) := by
  induction s using Multiset.induction_on with
  | empty => simpa using one_mem_sec
  | cons i s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul', succ_nsmul']
    exact sec_mul Xo c _ _ _ _ (hu i) ih

theorem aeval_mem_sec {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {σ : Type} (u : σ → Rul Xo c)
    (hu : ∀ i, u i ∈ sec Xo c a n) {Q : MvPolynomial σ c.F} {d : ℕ} (hQ : Q.IsHomogeneous d) :
    MvPolynomial.aeval u Q ∈ sec Xo c (d • a) (d • n) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hc : s.toMultiset.card = d := by
    rw [Finsupp.card_toMultiset]
    have := hQ (MvPolynomial.mem_support_iff.1 hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h1 := multiset_prod_mem_sec u hu s.toMultiset
  rw [hc, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])] at h1
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h1

theorem exists_algHom_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    ∃ ψ : Rul Xo c →ₐ[c.F] S, ∀ f, evR Xo c f y = ψ f :=
  ⟨AlgHom.ofLinearMap (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
    (evalAt_one _ _ y h) (fun f g => evalAt_mul _ _ f g y), fun _ => rfl⟩

theorem exists_homogeneous_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ), Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) + 2 ≤ m → ∀ u : Fin m → Rul Xo c, (∀ i, u i ∈ sec Xo c a n) → ∃ (Q : MvPolynomial (Fin m) c.F) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧ MvPolynomial.aeval u Q = 0 := by
  intro E _ _ _ H Dw l Xo c a n m hm u hu
  classical
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg E H Dw l Xo c).2
  haveI := CompFin.finite_comp Xo c
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  choose Q d hQ0 hQd hQv using fun Z : Comp Xo c =>
    exists_isHomogeneous_aeval_eq_zero (htr Z) hm (fun i => evC h Z (u i))
  have hhom : (∏ Z, Q Z).IsHomogeneous (∑ Z, d Z) := MvPolynomial.IsHomogeneous.prod _ _ _ fun Z _ => hQd Z
  refine ⟨∏ Z, Q Z, ∑ Z, d Z, Finset.prod_ne_zero_iff.2 fun Z _ => hQ0 Z, hhom, ?_⟩
  refine GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) _ _ _ (aeval_mem_sec u hu hhom) fun Z => ?_
  obtain ⟨ψ, hψ⟩ := exists_algHom_evR (genFr h Z) (hL.test _ _)
  have h1 : ψ (MvPolynomial.aeval u (Q Z)) = 0 := by
    rw [← hQv Z, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact congrArg (fun v => MvPolynomial.aeval v (Q Z)) (funext fun i => (hψ (u i)).symm)
  show evR Xo c _ (genFr h Z) = 0
  rw [hψ, map_prod, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ Z) h1

end GlobalTheory.SecRelation
end

section

set_option autoImplicit false

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem secBC_and_cuspBC (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) :
    SecBC Xo hle ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), CuspBC hle U :=
  ⟨GlobalTheory.SecFieldChange.secBC_holds hle, fun _ U => GlobalTheory.SecFieldChange.cuspBC_holds hle U⟩

end GlobalTheory.FieldBC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.shortThetaValue_existsUnique_natural_of_laws : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), ∃! v, ShortValAt Xo c nab w Λ β N P y v) ∧ ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ v0 v, ShortValAt Xo c nab w Λ β N P y0 v0 → ShortValAt Xo c nab w Λ β N P y v → φ v0 = v := by
  first | exact @GlobalTheory.shortThetaValue_existsUnique_natural | exact GlobalTheory.shortThetaValue_existsUnique_natural | (intros; apply GlobalTheory.shortThetaValue_existsUnique_natural <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaValue_natural_algebraMap : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  first | exact @GlobalTheory.thetaValue_natural | exact GlobalTheory.thetaValue_natural | (intros; apply GlobalTheory.thetaValue_natural <;> assumption)
end
