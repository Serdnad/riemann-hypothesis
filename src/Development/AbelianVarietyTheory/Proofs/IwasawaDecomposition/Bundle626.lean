module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle108
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle622
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRFree

attribute [local instance] Over.cartesianMonoidalCategory

theorem intO_isLocalRing (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have hu : ∀ b : ↥(intO C), ‖(b : C)‖ = 1 → IsUnit b := fun b hb => by
    have h0 : (b : C) ≠ 0 := fun h => by simp [h] at hb
    have hi : (b : C)⁻¹ ∈ intO C := by
      show ‖(b : C)⁻¹‖ ≤ 1
      rw [norm_inv, hb, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (hu a h)
  · refine Or.inr (hu _ ?_)
    have : ‖(1 : C) + (-(a : C))‖ = max ‖(1 : C)‖ ‖-(a : C)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact h.ne')
    rw [norm_neg, norm_one, max_eq_left h.le, ← sub_eq_add_neg] at this
    exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem latDR_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (xO : Sp ↥(intO C) ⟶ X), (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO) → ∃ (g : ℕ) (v : Fin g → (Sp (DualNumber C) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO C).subtype ≫ xO) (v i)) ∧ (∀ w, IsTanAtG t (spMap (intO C).subtype ≫ xO) w → ∃! cf : Fin g → C, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w) ∧ ∀ (cf : Fin g → C) w, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w → (w ∈ latDR t (spMap (intO C).subtype ≫ xO) ↔ ∀ i, ‖cf i‖ ≤ 1) := by
  intro E _ _ _ H X t C _ _ xO huniq
  have := intO_isLocalRing C
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (↥(intO C)) xO
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 : ∀ w, IsTanAtG t xO w → ∃! a : Fin n → ↥(intO C), IsCombAtG t xO D a w := by
    have h := hDb _ (RingHom.id ↥(intO C))
    simp only [h1, h3, Category.id_comp] at h
    exact h
  have hDk := fun j => isTanAtG_map t (intO C).subtype (hD j)
  refine ⟨n, fun e => spMap (dualMap (intO C).subtype) ≫ D e, hDk, hDb C _, fun cf w hw => ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := huniq xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (hDb C _ _ (isTanAtG_map t (intO C).subtype hv)).unique hw (comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · let a : Fin n → ↥(intO C) := fun i => ⟨cf i, hc i⟩
    have ha : IsCombAtG t xO D a (combT xO (fun j => ovT (hD j)) a).left :=
      (isCombAtG_iff t xO (fun j => ovT (hD j)) a _).2 rfl
    refine ⟨xO, rfl, _, isTanAtG_of _ (combT_tan _ (fun j => ovT (hD j)) (fun j => smT_zero_ovT _) a), ?_⟩
    have hb := comb_map t (intO C).subtype ha
    exact ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hb).symm.trans
      ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hw)

end GlobalTheory.LatDRFree
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.PinPlace

theorem mem_mul_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (y : K) :
    (∃ a : R, y = algebraMap R K (ϖ * a)) ↔ y = 0 ∨ y⁻¹ ∉ (algebraMap R K).range := by
  have hinj := IsFractionRing.injective R K
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, b, hb⟩ := hc
    have h1 : ϖ * a * b = 1 := hinj (by rw [map_mul, hb, mul_inv_cancel₀ h0, map_one])
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a * b) (by rw [← mul_assoc, h1]))
  · rintro (rfl | h)
    · exact ⟨0, by simp⟩
    · rcases ValuationRing.isInteger_or_isInteger R y with ⟨b, rfl⟩ | hb
      · have hb : ¬ IsUnit b := by
          rintro ⟨u, rfl⟩
          refine h ⟨(u⁻¹ : Rˣ), ?_⟩
          exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        have hm : b ∈ IsLocalRing.maximalIdeal R := hb
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨a, rfl⟩ := hm
        exact ⟨a, rfl⟩
      · exact absurd hb h

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem mem_range_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    y ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ↔
      la.1.valuation D.what₂.LL z ≤ 1 := by
  obtain ⟨W, h1, h2⟩ := h
  rw [← h2, hyz, h1]

theorem mem_pW_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    (∃ a : WittVector p (AlgebraicClosure (ZMod p)),
        y = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
      la.1.valuation D.what₂.LL z < 1 := by
  rw [mem_mul_iff (WittVector.irreducible p) y,
    mem_range_iff h (y := y⁻¹) (z := z⁻¹) (by rw [map_inv₀, map_inv₀, hyz])]
  have h0 : y = 0 ↔ z = 0 := by
    rw [← map_eq_zero_iff jc jc.injective, hyz, map_eq_zero_iff _ D.what₂.embLL.injective]
  rw [h0, map_inv₀, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hv : 0 < la.1.valuation D.what₂.LL z := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz)
    rw [one_lt_inv₀ hv]
    simp [hz]

theorem pinned_reads_place : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) →
    ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
      (jC p la).comp τ = D.what₂.embLL.comp e → ∀ x : 𝓞 D.host.E,
        τ x ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ∧
        ((∃ a : WittVector p (AlgebraicClosure (ZMod p)),
            τ x = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
          la.1.valuation D.what₂.LL (e x) < 1) ∧
        (la.1.valuation D.what₂.LL (e x) < 1 ↔ RingOfIntegers.mapRingHom e x ∈ la.1.asIdeal) := by
  intro D jC h p _ la τ e hτ x
  have hx : jC p la (τ x) = D.what₂.embLL (e x) := RingHom.congr_fun hτ (x : D.host.E)
  have he : e x = algebraMap (𝓞 D.what₂.LL) D.what₂.LL (RingOfIntegers.mapRingHom e x) := rfl
  refine ⟨(mem_range_iff (h p la) hx).2 ?_, mem_pW_iff (h p la) hx, ?_⟩
  · rw [he]; exact la.1.valuation_le_one _
  · rw [he]; exact la.1.valuation_lt_one_iff_mem _

theorem coeff_zero_eq_zero_iff {k : Type} [Field k] [CharP k p] [PerfectRing k p] (b : WittVector p k) :
    b.coeff 0 = 0 ↔ ∃ a : WittVector p k, b = p * a := by
  constructor
  · intro h0
    have hb : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      have h1 := congrArg (fun w : WittVector p k => w.coeff 0) u.mul_inv
      simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hm : b ∈ IsLocalRing.maximalIdeal (WittVector p k) := hb
    rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [WittVector.mul_coeff_zero]
    have : ((p : WittVector p k)).coeff 0 = 0 := by simp
    rw [this, zero_mul]

theorem pinned_tiedFor : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) → Formalism.L2.Geo.ComplexEmbeddingsCompatible jC := by
  intro D jC h p _ la τ e hτ x
  obtain ⟨-, h2, -⟩ := pinned_reads_place D jC h p la τ e hτ x
  rw [← h2]
  constructor
  · rintro ⟨b, hb, h0⟩
    obtain ⟨a, rfl⟩ := (coeff_zero_eq_zero_iff b).1 h0
    exact ⟨a, hb.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨p * a, ha.symm, (coeff_zero_eq_zero_iff _).2 ⟨a, rfl⟩⟩

end GlobalTheory.ShFam.PinPlace
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Col2
open Formalism.MainNotions.Inhab Formalism.BasicNotions.TH Formalism.L2.GlobalTheoryTheory IsDedekindDomain NumberField GlobalTheory.EX GlobalTheory.EX.OB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up.SizePar

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar



theorem ev_params_withLoc : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    (∃ L : SizeData₂ X.toD7, Nonempty (ParameterChoice' X.toD7 L)) ∧
      ∀ Lc : LocAll (lay0 X.toD7), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := GlobalTheory.EX.szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  have hGam : ∀ u, Real.log (D.mem u).A.GamP = K.C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * K.s.L := fun u => by
    have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
    rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl
  refine ⟨?_, fun Lc => ?_⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
      (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩
  · obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s (withLoc Lc) (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx)
      hP.rank hP.val (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta hGam
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
    obtain ⟨⟨M⟩, -, -⟩ := hN (withLoc Lc) L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
      ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
    exact ⟨L, ⟨M.params⟩⟩

end GlobalTheory.HeightCounting.Up.SizePar

namespace GlobalTheory.HeightCounting.Up.SizePar

theorem stepW_start_ev {Q : Ctx → Prop} (h : Ev Q) : StepW Start fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)

theorem aj_zero_at_state : StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P),
    ∀ v, (Dof x).what₂.muAt v = (Dof x).what₂.mu0 → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → (Dof x).what₂.Aj j v = 0 := by
  refine StepW.of_all fun K B f T w hO hF hS P x v hv j h1 h2 => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have e1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ e1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.Mem.Top.Bl.RowWt.forcedContent_eq_over_same_choices K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  have H := GlobalTheory.T.indices_pairingLengths_vanish_off_twistedPlaces K B f T w hO hF ⟨hS.1, ⟨P⟩⟩ P x hex
  have key : ∀ v', (w.D x.o.Z).what₂.muAt v' = (w.D x.o.Z).what₂.mu0 → v' ∉ P.Wt := by
    intro v' he hw
    have he' : P.q.W₀.muAt v' = w.C.mu0 := he
    rw [P.q.mu.on v' hw] at he'
    have e2 := P.q.mu.tw v'
    rw [he'] at e2
    exact (TwFin.tw_fin B f T).2.1 v' (e2.symm.trans (show w.I.xi w.C.mu0 = 1 from w.l.xi0))
  change (w.D x.o.Z).what₂.Aj j v = 0
  replace hv : (w.D x.o.Z).what₂.muAt v = (w.D x.o.Z).what₂.mu0 := hv
  have a := H v (key v hv) j h1 h2
  have b := H _ (key _ (((w.D x.o.Z).what₂.muAt_conj v).trans hv)) j h1 h2
  unfold Formalism.BasicNotions.Rows.Data.Aj
  rw [hv, a.1, a.2, b.1]
  rfl

theorem exists_params_allSt : AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧
    ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) :=
  ((stepW_start_ev ev_params_withLoc).and aj_zero_at_state).trans
    (StepW.of_all fun _ _ _ _ w hO _ H P x => H.1 (w.st x.o.Z) hO x.etaF (H.2 P x))

end GlobalTheory.HeightCounting.Up.SizePar

end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.OpenReg

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Transfer

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {x : Sp R ⟶ S'} {x' : Sp R ⟶ S}

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (h : A →+* B) :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem epsMul_over (s : R) : spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) =
    spMap (algebraMap R (DualNumber R)) := by
  rw [spMap_comp]
  congr 1
  ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_lift {T : Scheme.{0}} (q : T ⟶ S') (v : T ⟶ t.G.left) (hv : v ≫ t.G.hom = q ≫ f) :
    ∃ w : T ⟶ t'.G.left, w ≫ t'.G.hom = q ∧ w ≫ m.φ = v :=
  ⟨m.cart.1.lift v q hv, m.cart.1.lift_snd _ _ _, m.cart.1.lift_fst _ _ _⟩

theorem tan_iff (hx : x ≫ f = x') {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsTanAtG t x' (w ≫ m.φ) ↔ IsTanAtG t' x w := by
  subst hx
  have e : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ f) ⟶ t.G).left :=
    congrArg (fun z => z.left) (map_one (pushHom m.cart (Over.mk x)))
  constructor
  · intro h
    refine ⟨hw, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h.2.trans e.symm
    · have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
        RingHom.ext fun r => by simp
      rw [Category.assoc, hw, ← Category.assoc, spMap_comp, hid, Over.w]
      exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw, Category.assoc], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h.2).trans e

theorem eig_iff {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : 𝓞 E) (s : R) :
    (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul s) ≫ w ≫ m.φ ↔
      w ≫ (t'.act.act a).left = spMap (epsMul s) ≫ w := by
  have e : (w ≫ m.φ) ≫ (t.act.act a).left = (w ≫ (t'.act.act a).left) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc (spMap _)]; exact h
    · rw [Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, epsMul_over]
  · intro h
    rw [h, Category.assoc]

theorem prod_iff {q : Sp (DualNumber R) ⟶ S'} {q' : Sp (DualNumber R) ⟶ S} (hq : q ≫ f = q') {n : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (hv : ∀ i, v i ≫ t'.G.hom = q)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = q) :
    (∃ u : Fin n → (Over.mk q' ⟶ t.G), (∀ i, (u i).left = v i ≫ m.φ) ∧ ((List.ofFn u).prod).left = w ≫ m.φ) ↔
      ∃ u : Fin n → (Over.mk q ⟶ t'.G), (∀ i, (u i).left = v i) ∧ ((List.ofFn u).prod).left = w := by
  subst hq
  have push : ∀ u : Fin n → (Over.mk q ⟶ t'.G), ((List.ofFn u).prod).left ≫ m.φ =
      ((List.ofFn fun i => pushHom m.cart (Over.mk q) (u i)).prod).left := fun u => by
    have := map_list_prod (pushHom m.cart (Over.mk q)) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact congrArg (fun z => z.left) this
  constructor
  · rintro ⟨u, hu, hw'⟩
    let u' : Fin n → (Over.mk q ⟶ t'.G) := fun i => Over.homMk (v i) (hv i)
    have e : u = fun i => pushHom m.cart (Over.mk q) (u' i) := funext fun i => Over.OverMorphism.ext (hu i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · rw [e] at hw'
      exact (push u').trans hw'
    · rw [Over.w, hw]; rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (Over.mk q) (u i), fun i => ?_, (push u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu]

theorem comb_iff (hx : x ≫ f = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (cf : Fin n → R)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsCombAtG t x' (fun i => v i ≫ m.φ) cf (w ≫ m.φ) ↔ IsCombAtG t' x v cf w := by
  have := prod_iff m (q := spMap (algebraMap R (DualNumber R)) ≫ x) (q' := spMap (algebraMap R (DualNumber R)) ≫ x')
    (by rw [Category.assoc, hx]) (v := fun i => spMap (epsMul (cf i)) ≫ v i)
    (fun i => by rw [Category.assoc, hv, ← Category.assoc, epsMul_over]) hw
  simp only [Category.assoc] at this
  exact this

end Transfer

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem exists_frPt_of_eigFrame {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) :
    ∃ (y : FrPt Xo c R) (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.oF.t.G.left)),
      y.x = xF ≫ pullback.fst _ _ ∧ ∀ τ i, w τ i ≫ Z.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ xF ∧
        w τ i ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w τ i ≫ Z.m.φ = f.v τ i := by
  have hover : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp]; rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frPt (c := c) _ hover
  choose w hw1 hw2 using fun τ i => exists_lift Z.m (spMap (algebraMap R (DualNumber R)) ≫ xF) (f.v τ i)
    (by rw [(f.tan τ i).1, ← hx, Category.assoc])
  refine ⟨⟨z.x, z.x_over, fun τ i => w τ i ≫ Z.m0.toSABMap.φ, fun τ i => ?_, fun τ i a => ?_, fun τ v hv he => ?_,
    z.s, z.gen⟩, w, hz, fun τ i => ⟨hw1 τ i, rfl, hw2 τ i⟩⟩
  · exact (tan_iff Z.m0.toSABMap hz.symm (hw1 τ i)).2 ((tan_iff Z.m hx (hw1 τ i)).1 (hw2 τ i ▸ f.tan τ i))
  · exact (eig_iff Z.m0.toSABMap (hw1 τ i) a _).2 ((eig_iff Z.m (hw1 τ i) a _).1 (hw2 τ i ▸ f.eig τ i a))
  · obtain ⟨v', h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap R (DualNumber R)) ≫ xF) v
      (by rw [hv.1, hz, Category.assoc])
    have hb := f.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hz.symm h1).1 hv))
      fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
    have e : f.v τ = fun i => w τ i ≫ Z.m.φ := funext fun i => (hw2 τ i).symm
    rw [e] at hb
    exact (existsUnique_congr fun cf => (comb_iff Z.m0.toSABMap hz.symm (hw1 τ) cf h1).trans
      (comb_iff Z.m hx (hw1 τ) cf h1).symm).2 hb

variable {F : Type} [Field F] {e : F ≃+* c.F}

theorem mono_spMap_algebraMap (A K : Type) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Mono (spMap (algebraMap A K)) := by
  have : IsPreimmersion (spMap (algebraMap A K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  infer_instance

end GlobalTheory.ShFam.OpenReg
end
end
