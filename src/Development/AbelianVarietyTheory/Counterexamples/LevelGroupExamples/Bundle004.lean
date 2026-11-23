module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.BaseClassMove

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem latAdm_unit (l : Level H) (bad n : ℕ) : LatAdm l bad (unitLat E n) := by
  have ht : ∀ m, (unitLat E n).TrivAt m := fun m => ⟨1, by simp, by simp [unitLat], by simp [unitLat]⟩
  refine ⟨fun v => ⟨fun hv w hw => ?_, fun hv => ?_⟩, ht _, ht _⟩
  · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hv j trivial)
      exact ⟨H.bar a, by rw [← ha]; exact H.bar_eq a⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hw j trivial)
      exact ⟨a, ha⟩
  · intro j _
    have h := hv (Pi.single j 1) (fun i _ => by
      by_cases hi : i = j
      · subst hi; simpa using Submodule.one_le.1 le_rfl
      · simp [Pi.single_eq_of_ne hi])
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    obtain ⟨a, ha⟩ := h
    refine Submodule.mem_one.2 ⟨H.bar a, ?_⟩
    have := H.bar_eq a
    change ((H.bar a : 𝓞 E) : E) = v j
    rw [this]
    change IsCMField.complexConj E (algebraMap _ _ a) = _
    rw [ha, IsCMField.complexConj_apply_apply]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem shortValAt_beta (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F)
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by
  have key : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (a b d : c.F) (T : S'),
      φ v = algebraMap c.F S' (β⁻¹ * a * b * d) * T ↔
        φ (algebraMap c.F S β * v) = algebraMap c.F S' (1⁻¹ * a * b * d) * T := by
    intro S' _ _ φ a b d T
    have hu : algebraMap c.F S' β * algebraMap c.F S' β⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hβ, map_one]
    simp only [map_mul, AlgHom.commutes, inv_one, map_one]
    constructor
    · intro h; rw [h]; linear_combination (algebraMap c.F S' a * algebraMap c.F S' b * algebraMap c.F S' d * T) * hu
    · intro h; linear_combination (algebraMap c.F S' β⁻¹) * h - φ v * hu
  constructor
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).1 h7⟩
  · rintro ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, (key S' φ _ _ _ _).2 h7⟩

theorem isBeta_unit (n : ℕ) : IsBeta Dw c (unitLat E n) 1 := by
  have e : (unitLat E n).Ln = (unitLat E n).La := inf_idem _
  refine ⟨one_ne_zero, ?_, fun σ => ?_⟩
  · unfold BetaIs; rw [e, ← Submodule.one_eq_span, one_mul]
  · rw [e]; simp

theorem zetaM_pow : zetaM c ^ l.M = 1 := by
  have hM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have h0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  unfold zetaM
  rw [← pow_mul, Nat.div_mul_cancel hM]
  apply Subtype.ext
  exact (Complex.isPrimitiveRoot_exp l.M' h0).pow_eq_one

end GlobalTheory.Survey.BaseClassMove
end
end

section

namespace GlobalTheory.PeriodFormEdge

open ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj IsLocalRing

section Local
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

end Local

section At
variable {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C]

end At

section Agree
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PsiCoordLocal
variable {R : Type} [CommRing R] [IsDomain R]

theorem psiIn_iff {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (J : Ideal R) : D.PsiIn χ J ↔ r ∈ J := by
  obtain ⟨j0, hc0, h0, e0⟩ := hr
  constructor
  · intro hJ
    obtain ⟨r', hr', e'⟩ := hJ j0 ⊤ (AlgebraicGeometry.isAffineOpen_top _) hc0 h0
    have hrr : r' = DegPre.toOpen ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e0.symm)
    subst hrr
    rwa [← Ideal.mem_comap, Ideal.comap_map_of_bijective _ GlobalTheory.PsiCoordLocal.toOpen_top_bijective] at hr'
  · intro hJ j V hV hle h
    have h' := GlobalTheory.PsiCoordLocal.generic_le D χ j0 (le_top.trans hc0 : V ≤ _)
    obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_trans D χ j j0 hle (le_top.trans hc0) h h'
    refine ⟨(u : _) * DegPre.toOpen V r, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hJ), ?_⟩
    have hres := congrArg Units.val hu
    simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.val_mul, Units.coe_map,
      MonoidHom.coe_coe] at hres
    rw [map_mul]
    refine Eq.trans ?_ hres.symm
    congr 1
    have hVt : (TopologicalSpace.Opens.map (jK R).base).obj V ≤ (TopologicalSpace.Opens.map (jK R).base).obj ⊤ :=
      fun x _ => trivial
    have e1 := congrArg (CommRingCat.Hom.hom ((TK R).left.presheaf.map (CategoryTheory.homOfLE hVt).op)) e0
    refine Eq.trans ?_ (e1.trans ?_)
    · have hnat := AlgebraicGeometry.Scheme.Hom.naturality (jK R) (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op
      have ht : DegPre.toOpen V r = (CommRingCat.Hom.hom ((AlgebraicGeometry.Spec (CommRingCat.of R)).presheaf.map
          (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op)) (DegPre.toOpen ⊤ r) := by
        simp only [DegPre.toOpen, RingHom.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl
      rw [ht, ← CommRingCat.comp_apply, hnat, CommRingCat.comp_apply]
      rfl
    · rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl

variable [IsDiscreteValuationRing R]

end Agree

end GlobalTheory.PeriodFormEdge
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntChartCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem const_zero (C : IntegralChartA3 Xo c T io y) :
    (∀ j, MvPowerSeries.constantCoeff (C.FT j) = 0) ∧ ∀ a j, MvPowerSeries.constantCoeff (C.actT a j) = 0 := by
  letI := io.toAlgebra
  obtain ⟨⟨h1, h2, -⟩, -⟩ := C.gen
  refine ⟨fun j => ?_, fun a j => ?_⟩
  · have := C.ch.B.G.const j
    rw [h1 j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this
  · have := C.ch.B.A.const a j
    rw [h2 a j, MvPowerSeries.constantCoeff_map] at this
    exact (map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)).1 this

theorem dim_eq (C : IntegralChartA3 Xo c T io y) : chD C.ch = Fintype.card (Lt1 Dw) := by
  letI := io.toAlgebra
  let f : (Lt1 Dw → T.Fr) →ₗ[T.Fr] (Fin C.ch.d → T.Fr) :=
    { toFun := fun a j => ∑ ℓ, a ℓ * C.ch.uvec ℓ j
      map_add' := fun a b => by funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r a => by funext j; simp [Finset.mul_sum, _root_.mul_assoc] }
  have hb : Function.Bijective f := (Function.bijective_iff_existsUnique f).2 fun v => by
    obtain ⟨a, ha, hu⟩ := C.ch.chart.basis v
    exact ⟨a, funext ha, fun b hb => hu b (congrFun hb)⟩
  have := (LinearEquiv.ofBijective f hb).finrank_eq
  simpa using this.symm

end GlobalTheory.IntChartCheck
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverDatum

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj GlobalTheory.LevelPairing
open CategoryTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.pd_pos (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) : 0 < d.pd := by
  obtain ⟨-, hM, -⟩ := h
  have h3 := d.l₂.three_le
  rw [hM] at h3
  refine Nat.pos_of_ne_zero fun h0 => ?_
  rw [h0, mul_zero] at h3
  omega


set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.half_mul_conj (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) :
    d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)} := by
  obtain ⟨-, hM, -, hMb, -⟩ := h
  have h2 := d.l₂.prod
  rw [hMb, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, l.prod] at h2
  have hne : Ideal.span {(l.M : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := l.three_le
    omega
  exact mul_left_cancel₀ hne h2


set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
set_option synthInstance.maxHeartbeats 200000 in
theorem _root_.GlobalTheory.LevelCoverDatum.isLev_smul (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.IsLev) (a : d.c₂.F) (ha : a ≠ 0) :
    _root_.Formalism.L2.Pj.DeltaDat.IsLev { d with cδ := a • d.cδ } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, Submodule.smul_mem _ a h8, ?_⟩
  intro k _ _ _ y₂
  have hy := h9 k y₂
  simp only [_root_.Formalism.L2.Pj.evR] at hy ⊢
  rw [_root_.Formalism.L2.Pj.evalAt_smul]
  exact mul_ne_zero ((map_ne_zero _).mpr ha) hy

set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.zetaM_cover (d : _root_.Formalism.L2.Pj.DeltaDat Xo c n) (h : d.l₂.M = l.M * d.pd) :
    _root_.Formalism.L2.Pj.zetaM d.c₂ ^ d.pd = d.eF (_root_.Formalism.L2.Pj.zetaM c) := by
  have h3 := d.l₂.three_le
  rw [h] at h3
  have hM : l.M ≠ 0 := fun h0 => by rw [h0, zero_mul] at h3; omega
  have hp : d.pd ≠ 0 := fun h0 => by rw [h0, mul_zero] at h3; omega
  apply Subtype.ext
  simp only [SubmonoidClass.coe_pow]
  change ((_root_.Formalism.L2.Pj.zetaM d.c₂ : ℂ)) ^ d.pd = (_root_.Formalism.L2.Pj.zetaM c : ℂ)
  rw [_root_.GlobalTheory.LevelPairing.zetaM_coe, _root_.GlobalTheory.LevelPairing.zetaM_coe, h]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp


set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.noDelta_w (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) (x0 : Fin n → Dw.La) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).w x0 = _root_.Formalism.L2.Pj.x0Dat c x0 := by
  funext q
  apply Subtype.ext
  simp only [_root_.Formalism.L2.Pj.DeltaDat.w, _root_.Formalism.L2.Pj.noDelta, mul_one]
  unfold _root_.Formalism.L2.Pj.x0Dat
  rfl


set_option autoImplicit false in
open NumberField in
open CategoryTheory in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable {Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ} in
theorem _root_.GlobalTheory.LevelCoverDatum.noDelta_etaOK (nab : _root_.Formalism.L2.Pj.NabV Xo c)
    (m : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X)) :
    (_root_.Formalism.L2.Pj.noDelta Xo c nab m n).EtaOK ↔ (∀ a, (Xo.univ.eta a).left ≫ m.φ = (Xo.univ.eta a).left) ∧
      ∀ a, (Xo.univ.etaA a).left ≫ m.φ = (Xo.univ.etaA a).left := by
  simp only [_root_.Formalism.L2.Pj.DeltaDat.EtaOK, _root_.Formalism.L2.Pj.noDelta, Nat.div_self l.A_pos, Category.id_comp]
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_) <;>
  · apply Iff.of_eq
    congr 3
    open scoped MonObj in exact pow_one _

end GlobalTheory.LevelCoverDatum
end
end
