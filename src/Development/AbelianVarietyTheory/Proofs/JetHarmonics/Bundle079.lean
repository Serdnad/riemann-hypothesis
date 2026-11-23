module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle070
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeValueLePlanBlocks
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle071
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LabSelf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

theorem rt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (starRingEnd ℂ) H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  apply GlobalTheory.ThetaClaimsCompare.rt0_conj_neg_ne_zero <;> assumption

theorem inPsi_or_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have h : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]
    simp
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact Or.inl h
  · right
    rw [h, map_neg, (rt_conj H).1, neg_neg]

theorem not_inPsi_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {τ : E →+* ℂ} (h1 : InPsi H τ) :
    ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1, (rt_conj H).1] at h2
  exact (rt_conj H).2 (by linear_combination (-1 / 2 : ℂ) * h2)

theorem embK_conj {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (H.bar x) := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem zmod_two (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s; decide

theorem arithS_tauC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → PhiC N V.l → ∀ n j j' : ℕ, ArithS V io ι (⟨tauC N pl, n, j, j'⟩ : LabS E (RPl N.R)) ∧ Function.Surjective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ V ι _ hl hla hC n j j'
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have h10 : ¬ (1 : ZMod 2) = 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have t0 : ∀ z, tauC N pl z 0 = pl z := fun z => if_pos rfl
  have t1 : ∀ z, tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := fun z => if_neg h10
  have hpos : ∀ z, N.pos (resCharOf la) z 1 = z := by
    intro z
    unfold NumDatum.pos
    rw [← hl, hC.1, hC.2]
    simp
  have hfr : ∀ z x, V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl z)) x - emA3 io ι (pl z) x ^ V.l) := by
    intro z x
    obtain ⟨y, hy, he⟩ := hP.frob la (Or.inl (hl ▸ hC.1)) z x
    have h1 := hla y hy
    rw [he, hpos, ← hl, map_sub, map_sub, map_pow, map_pow] at h1
    exact h1
  have hem : ∀ τ x, emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (H.bar x) := by
    intro τ x
    show ι (io (embK c _ x)) = ι (io (embK c τ (H.bar x)))
    rw [embK_conj]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨z, s⟩ ⟨z', s'⟩ h
    dsimp only at h
    rcases zmod_two s with rfl | rfl <;> rcases zmod_two s' with rfl | rfl
    · rw [t0, t0] at h
      rw [hP.inj h]
    · rw [t0, t1] at h
      exact absurd (h ▸ hpsi z) (not_inPsi_conj H (hpsi z'))
    · rw [t1, t0] at h
      exact absurd (h ▸ hpsi z') (not_inPsi_conj H (hpsi z))
    · rw [t1, t1] at h
      have h' := congrArg ComplexEmbedding.conjugate h
      rw [conj_conj, conj_conj] at h'
      rw [hP.inj h']
  · intro z s
    dsimp only
    rcases zmod_two s with rfl | rfl
    · rw [zero_add, t0, t1]
    · rw [h11, t0, t1, conj_conj]
  · intro z s x
    dsimp only
    rcases zmod_two s with rfl | rfl
    · rw [zero_add, t0, t1]
      exact hfr z x
    · rw [h11, t0, t1]
      have h1 := hfr z (H.bar x)
      rwa [← hem, ← hem, conj_conj] at h1
  · have h := hC.1
    unfold NumDatum.cls primeClass at h
    refine hP.unr _ V.l_prime (fun h2 => ?_) (fun hq => ?_) (fun hd => ?_)
    · rw [if_pos h2] at h
      cases h
    · rw [if_pos hq] at h
      split_ifs at h
    · rw [if_pos hd] at h
      split_ifs at h
  · intro τ
    rcases inPsi_or_conj H τ with h | h
    · obtain ⟨z, hz⟩ := (hP.psi _).1 h
      exact ⟨(z, 0), (t0 z).trans hz⟩
    · obtain ⟨z, hz⟩ := (hP.psi _).1 h
      exact ⟨(z, 1), (t1 z).trans (by rw [hz, conj_conj])⟩

end GlobalTheory.LabSelf
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDepth


open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in
theorem isCanonGauge_mapFB_tower {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) {h : PS k 2 d} {R' : Type} [CommRing R'] [Algebra R' k]
    (φ : R →+* R') (hφ : ∀ x, algebraMap R' k (φ x) = algebraMap R k x) (hh : B.IsCanonGauge k h) :
    (FBMap.mapFB φ B).IsCanonGauge k h := by
  have hK : ∀ {n : ℕ} (f : PS R n d), FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
    intro n f
    ext mo
    simp only [MvPowerSeries.coeff_map, hφ]
  have hF : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => hK _
  have hA : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => hK _
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK _).trans hh.ph1
  · rw [hF]; exact (hK _).trans hh.ph2
  · exact (hK _).trans hh.sy
  · rw [hA]; exact (hK _).trans (hh.ad a)

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_formalBiext_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧
      (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧
      B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X
  letI := io.toAlgebra
  obtain ⟨BT, e1, e2, -, -, -, -, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨-, -, h3, h4⟩ := e7 X.C
  refine ⟨FBMap.mapFB X.ι BT, ?_, fun a => ?_,
    isCanonGauge_mapFB_tower BT X.ι (fun x => (X.comp x).symm) ((h3 _).2 h4)⟩
  · rw [← e1]; rfl
  · rw [← e2]; rfl

end GlobalTheory.CharDepth
end
end

section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertLabelling

open GlobalTheory.LevelsOrbits

lemma ordP_dvd_of_pos_eq (N : NumDatum) (l : ℕ) (z : RPl N.R) (u : ℕ) (h : N.pos l z u = z) : N.ordP l ∣ u := by
  unfold NumDatum.pos at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  dsimp only at h1 h2
  have h3 : u • N.hP l = 0 := by simpa using h2
  unfold NumDatum.ordP
  by_cases hc : N.cls l = PrimeClass.signal
  · rw [if_pos hc]
    have ho : ¬ Odd u := by
      intro ho
      rw [decide_eq_true (⟨hc, ho⟩ : N.cls l = PrimeClass.signal ∧ Odd u)] at h1
      cases hz : z.1 <;> simp [hz] at h1
    obtain ⟨t, rfl⟩ := Nat.not_odd_iff_even.1 ho
    rw [← two_mul]
    refine Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero ?_)
    rw [← mul_smul, mul_two, h3]
  · rw [if_neg hc]
    exact addOrderOf_dvd_of_nsmul_eq_zero h3

lemma pos_inj (N : NumDatum) (l : ℕ) (z : RPl N.R) (s t : ZMod (N.ordP l))
    (h : N.pos l z s.val = N.pos l z t.val) : s = t := by
  wlog hst : s.val ≤ t.val generalizing s t
  · exact (this t s h.symm (not_le.1 hst).le).symm
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hst
  rw [hu, ← pos_add] at h
  have hd := ordP_dvd_of_pos_eq N l _ u h.symm
  have hlt := ZMod.val_lt t
  have : u = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  apply ZMod.val_injective
  omega

def orbSetoid (N : NumDatum) (l : ℕ) : Setoid (RPl N.R) where
  r z z' := ∃ s : ℕ, N.pos l z s = z'
  iseqv := ⟨fun z => ⟨N.ordP l * 0, pos_mul_period N l z 0⟩, fun {z z'} ⟨s, hs⟩ => ⟨(N.ordP l - 1) * s, by
      have hp : 0 < N.ordP l := Nat.pos_of_ne_zero (NeZero.ne _)
      obtain ⟨n, hn⟩ : ∃ n, N.ordP l = n + 1 := ⟨N.ordP l - 1, by omega⟩
      rw [← hs, pos_add, show s + (N.ordP l - 1) * s = N.ordP l * s by rw [hn, Nat.add_sub_cancel]; ring,
        pos_mul_period]⟩,
    fun {a b c} ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s + t, by rw [← pos_add, hs, ht]⟩⟩

lemma exists_reps (N : NumDatum) (l : ℕ) : ∃ Z : Finset (RPl N.R),
    ∀ z' : RPl N.R, ∃! p : RPl N.R × ZMod (N.ordP l), p.1 ∈ Z ∧ N.pos l p.1 p.2.val = z' := by
  refine ⟨Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z, fun z' => ?_⟩
  obtain ⟨s, hs⟩ : (orbSetoid N l).r (Quotient.mk (orbSetoid N l) z').out z' := Quotient.mk_out z'
  have key : ∀ p : RPl N.R × ZMod (N.ordP l),
      p.1 ∈ (Finset.univ.filter fun z => (Quotient.mk (orbSetoid N l) z).out = z) ∧ N.pos l p.1 p.2.val = z' →
      p.1 = (Quotient.mk (orbSetoid N l) z').out := by
    rintro p ⟨h1, h2⟩
    rw [← (Finset.mem_filter.1 h1).2]
    congr 1
    exact Quotient.sound ⟨_, h2⟩
  refine ⟨((Quotient.mk (orbSetoid N l) z').out, (s : ZMod (N.ordP l))), ⟨?_, ?_⟩, fun p hp => ?_⟩
  · simp
  · rw [ZMod.val_natCast, pos_mod, hs]
  · have h1 := key p hp
    refine Prod.ext h1 (pos_inj N l p.1 _ _ ?_)
    rw [hp.2, ZMod.val_natCast, pos_mod, h1, hs]

lemma even_ordP (N : NumDatum) (l : ℕ) (hI : Inert N l) (hC : ¬ ConjIn N l) : Even (N.ordP l) :=
  GlobalTheory.GoodDepth.even_ordP_of_not_conjIn hI hC

lemma bg_succ {d : ℕ} [NeZero d] (hd : Even d) (s : ZMod d) (g : Fin 2) : g = RF.bg (s + 1) ↔ ¬ g = RF.bg s := by
  have h : Even (s + 1).val ↔ ¬ Even s.val := by
    have e : s + 1 = ((s.val + 1 : ℕ) : ZMod d) := by simp
    rw [e, ZMod.val_natCast, ← Nat.even_add_one, Nat.even_iff, Nat.even_iff,
      Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hd)]
  unfold RF.bg
  by_cases hs : Even s.val
  · rw [if_pos hs, if_neg (fun hh => h.1 hh hs)]; fin_cases g <;> simp
  · rw [if_neg hs, if_pos (h.2 hs)]; fin_cases g <;> simp

lemma pos_succ (N : NumDatum) (l : ℕ) (z : RPl N.R) (s : ZMod (N.ordP l)) :
    N.pos l z (s + 1).val = N.pos l (N.pos l z s.val) 1 := by
  have e : s + 1 = ((s.val + 1 : ℕ) : ZMod (N.ordP l)) := by simp
  rw [e, ZMod.val_natCast, pos_mod, pos_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

lemma inPsi_conj_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by linear_combination this)
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [← map_pow, this, map_neg, map_natCast]
  have h2 : ∀ w : ℂ, w ^ 2 = -(H.d : ℂ) → starRingEnd ℂ w = -w := by
    intro w hw
    have hre := congrArg Complex.re hw
    have him := congrArg Complex.im hw
    simp [pow_two] at hre him
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have : w.re = 0 := by
      by_contra hne
      have : w.im = 0 := by
        have : w.re * w.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg w.re]
    apply Complex.ext <;> simp [this]
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq, h2 _ h1]
  have h3 : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm)
  constructor
  · intro a b
    exact h0 (by linear_combination (-1/2 : ℂ) * a - (1/2 : ℂ) * b)
  · intro a
    rw [h3.resolve_left a, neg_neg]

lemma embK_conj_bar {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c τ (H.bar x) = embK c (ComplexEmbedding.conjugate τ) x := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

lemma conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
  ComplexEmbedding.involutive_conjugate E τ

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → Inert N V.l → ¬ ConjIn N V.l → ∀ j : ℕ, ∃ Z : Finset (RPl N.R), RF.IsReps (parOf N j V.l) Z ∧ Z.Nonempty ∧ Even (N.ordP V.l) ∧ Function.Bijective (fun x : Z × Fin 2 × ZMod (N.ordP V.l) => tauIn N pl V.l x.1.1 x.2.1 x.2.2) ∧ ∀ z g, FrobOrd V io ι (tauIn N pl V.l z g) ∧ ∀ s, tauIn N pl V.l z 1 s = ComplexEmbedding.conjugate (tauIn N pl V.l z 0 s) := by
  intro E _ _ _ H lv c N pl hT la T io C _ _ V ι _ hl hla hI hC j
  obtain ⟨Z, hZ⟩ := exists_reps N V.l
  have hev := even_ordP N V.l hI hC
  have hin : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  have hne : ∀ z z', pl z ≠ ComplexEmbedding.conjugate (pl z') := fun z z' h =>
    (inPsi_conj_iff (pl z')).1 (h ▸ hin z) (hin z')
  have hcinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
    (ComplexEmbedding.involutive_conjugate E).injective
  refine ⟨Z, hZ, ?_, hev, ⟨?_, ?_⟩, fun z g => ⟨fun s x => ?_, fun s => ?_⟩⟩
  · obtain ⟨p, hp, -⟩ := hZ (false, 0)
    exact ⟨p.1, hp.1⟩
  · rintro ⟨z, g, s⟩ ⟨z', g', s'⟩ h
    have main : N.pos V.l z.1 s.val = N.pos V.l z'.1 s'.val → (g = RF.bg s ↔ g' = RF.bg s') →
        (z, g, s) = (z', g', s') := by
      intro h1 h2
      have := (hZ _).unique (y₁ := (z.1, s)) (y₂ := (z'.1, s')) ⟨z.2, h1⟩ ⟨z'.2, rfl⟩
      obtain ⟨a, b⟩ := Prod.mk.inj this
      obtain rfl := Subtype.ext a
      subst b
      have : g = g' := (by decide : ∀ g g' b : Fin 2, (g = b ↔ g' = b) → g = g') _ _ _ h2
      rw [this]
    dsimp only [tauIn] at h
    by_cases a : g = RF.bg s <;> by_cases b : g' = RF.bg s'
    · rw [if_pos a, if_pos b] at h
      exact main (hT.inj h) (by tauto)
    · rw [if_pos a, if_neg b] at h
      exact absurd h (hne _ _)
    · rw [if_neg a, if_pos b] at h
      exact absurd h.symm (hne _ _)
    · rw [if_neg a, if_neg b] at h
      exact main (hT.inj (hcinj h)) (by tauto)
  · intro τ
    by_cases h : InPsi H τ
    · obtain ⟨z', rfl⟩ := (hT.psi _).1 h
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg p.2, p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_pos rfl, hp.2]
    · obtain ⟨z', hz'⟩ := (hT.psi _).1 ((inPsi_conj_iff τ).2 h)
      obtain ⟨p, hp, -⟩ := hZ z'
      refine ⟨(⟨p.1, hp.1⟩, RF.bg (p.2 + 1), p.2), ?_⟩
      dsimp only [tauIn]
      rw [if_neg ((bg_succ hev _ _).1 rfl), hp.2, hz', conj_conj]
  · have hf : ∀ (w : RPl N.R) (x : 𝓞 E), V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl (N.pos V.l w 1))) x -
        emA3 io ι (pl w) x ^ V.l) := by
      intro w x
      obtain ⟨y, hy, e⟩ := hT.frob la (hl ▸ hI) w x
      have := hla y hy
      rw [e, ← hl, map_sub, map_sub, map_pow, map_pow] at this
      exact this
    unfold tauIn
    rw [pos_succ]
    by_cases a : g = RF.bg s
    · rw [if_pos a, if_neg (fun hh => (bg_succ hev _ _).1 hh a)]
      exact hf _ _
    · rw [if_neg a, if_pos ((bg_succ hev _ _).2 a)]
      have := hf (N.pos V.l z s.val) (H.bar x)
      simp only [emA3, RingHom.comp_apply, embK_conj_bar, conj_conj] at this ⊢
      exact this
  · unfold tauIn
    by_cases a : (0 : Fin 2) = RF.bg s
    · rw [if_pos a, if_neg (by rw [← a]; decide)]
    · rw [if_neg a, if_pos (by revert a; generalize RF.bg s = b; revert b; decide), conj_conj]

end GlobalTheory.InertLabelling
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.largePrime_packages_depth_nonpos : ZeroBd := by
  first | exact @GlobalTheory.GoodDepth.zeroBd | exact GlobalTheory.GoodDepth.zeroBd | (intros; apply GlobalTheory.GoodDepth.zeroBd <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.forcedContent_bounds_programmeValue_goodPrime : ∀ (N : NumDatum) (j l : ℕ), l.Prime → l ∉ N.H.small → l ≠ N.q → l ≠ N.d → l ≠ N.g 0 → l ≠ N.g 1 → (∀ z, 0 ≤ N.w j z) → (∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z) →
  0 ≤ N.FjP j l ∧ (Inert N l ∨ N.cls l = PrimeClass.splitK) ∧ ParOK (parOf N j l) ∧
  (PhiC N l → ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ∧
  (Inert N l → ¬ PhiC N l → ∀ Z : Finset (RPl N.R), RF.IsReps (parOf N j l) Z →
    (∑ z ∈ Z, Fnum l (N.ordP l) fun s => ((N.R.k : ℝ) - 1) * N.w j (N.pos l z s.val)) ≤ N.FjP j l + if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) := by
  first | exact @GlobalTheory.ContentValue.main | exact GlobalTheory.ContentValue.main | (intros; apply GlobalTheory.ContentValue.main <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.splitPrimeDepthContentBound_proof : SplitBd := by
  first | exact @GlobalTheory.GoodDepth.splitBd | exact GlobalTheory.GoodDepth.splitBd | (intros; apply GlobalTheory.GoodDepth.splitBd <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.inertPrime_value_le_planBlocks : ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), ParOK P → 5 ≤ l → ∀ (Pk : RF.PkgInert P l C1) (p : ∀ z, Plan l P.d (RF.alongOrb P z Pk.W)),
  (∀ z ∈ Pk.Z, ∀ a i, i0 P.k l ≤ i → (p z).y a i = 0) →
  (∀ z ∈ Pk.Z, ∀ a i, (p z).y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i ((p z).y a i)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i ((p z).y a i))) →
  Pk.ν ≤ (∑ z ∈ Pk.Z, (p z).bound (P.k - 1) P.m) + Pk.rest / ((l : ℝ) - 1) := by
  first | exact @GlobalTheory.PlanValue.val_le_plan | exact GlobalTheory.PlanValue.val_le_plan | (intros; apply GlobalTheory.PlanValue.val_le_plan <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.universalJets_power_product : UnivPowSt := by
  first | exact @GlobalTheory.PowGerm.univPow | exact GlobalTheory.PowGerm.univPow | (intros; apply GlobalTheory.PowGerm.univPow <;> assumption)
end
