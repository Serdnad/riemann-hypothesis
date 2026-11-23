module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTupleMeasureExtOfPureTensorIntegrals
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.LocM.BaseMdl

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {S : Type} [CommRing S] {x' : Sp S ⟶ X'}

theorem prod_left_congr {B T : Scheme.{0}} {G : Over B} [GrpObj G] {a b : T ⟶ B} (h : a = b) {n : ℕ}
    (u : Fin n → (Over.mk a ⟶ G)) (u' : Fin n → (Over.mk b ⟶ G)) (hu : ∀ i, (u i).left = (u' i).left) :
    (List.ofFn u).prod.left = (List.ofFn u').prod.left := by
  subst h
  rw [show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]

theorem epsMul_comp (c : S) :
    spMap (epsMul c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsMul c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem fst_comp :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    ext s; simp
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  simp

theorem one_push : (1 : Over.mk x' ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x' ≫ f) ⟶ t.G).left :=
  congrArg (fun q => q.left) (map_one (pushHom m.cart (Over.mk x')))

theorem prod_push {n : ℕ} (u : Fin n → (tEpsG x' ⟶ t'.G)) (u' : Fin n → (tEpsG (x' ≫ f) ⟶ t.G))
    (h : ∀ i, (u' i).left = (u i).left ≫ m.φ) :
    (List.ofFn u).prod.left ≫ m.φ = (List.ofFn u').prod.left := by
  have e : (List.ofFn u).prod.left ≫ m.φ =
      (List.ofFn fun i => pushPt m.cart.1.w (u i)).prod.left :=
    congrArg (fun q => q.left) ((map_list_prod (pushHom m.cart (tEpsG x')) _).trans (by rw [List.map_ofFn]; rfl))
  exact e.trans (prod_left_congr (Category.assoc _ _ _) _ _ fun i => (h i).symm)

theorem tan_push {v : Sp (DualNumber S) ⟶ t'.G.left}
    (hv : v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsTanAtG t' x' v ↔ IsTanAtG t (x' ≫ f) (v ≫ m.φ) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hv, Category.assoc]
    · rw [← Category.assoc, h.2, one_push]
  · intro h
    refine ⟨hv, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]
      exact h.2.trans (one_push m).symm
    · rw [Category.assoc, hv, ← Category.assoc, fst_comp, Category.id_comp]
      exact (Over.w (1 : Over.mk x' ⟶ t'.G)).symm

theorem exists_lift {w : Sp (DualNumber S) ⟶ t.G.left}
    (hw : w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f) :
    ∃ v : Sp (DualNumber S) ⟶ t'.G.left, v ≫ m.φ = w ∧ v ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' :=
  ⟨m.cart.1.lift w _ (hw.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩

theorem comb_push {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') (cf : Fin n → S)
    {w : Sp (DualNumber S) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') :
    IsCombAtG t' x' v cf w ↔ IsCombAtG t (x' ≫ f) (fun i => v i ≫ m.φ) cf (w ≫ m.φ) := by
  have hs : ∀ i, (spMap (epsMul (cf i)) ≫ v i) ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' := fun i => by
    rw [Category.assoc, hv, ← Category.assoc, epsMul_comp]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => Over.homMk ((u i).left ≫ m.φ) ?_, fun i => ?_, (prod_push m u _ fun i => rfl).symm⟩
    · show ((u i).left ≫ m.φ) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ≫ f
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hu, hs, Category.assoc]
    · show (u i).left ≫ m.φ = _
      rw [hu, Category.assoc]
  · rintro ⟨u, hu, hp⟩
    let u' : Fin n → (tEpsG x' ⟶ t'.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (hs i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · exact (prod_push m u' u fun i => (hu i).trans (Category.assoc _ _ _).symm).trans hp
    · exact (Over.w (List.ofFn u').prod).trans hw.symm


end Push

section Generic

theorem away_of_valuation (F : Type) [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (V : ValuationSubring F) (p : ℕ)
    (hp : p.Prime) (hV : (p : F) ∈ V.nonunits) : IsLocalization.Away ((p : ℕ) : V) F := by
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hm : ((p : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := ValuationSubring.coe_mem_nonunits_iff.1 (by simpa using hV)
  have key : ∀ x : F, ∃ (k : ℕ) (a : V), x * (p : F) ^ k = a := by
    intro x
    have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨n, hn, hi⟩ := hx.exists_integral_multiple
    have hi' : IsIntegral ℤ ((n.natAbs : ℤ) • x) := by
      rcases Int.natAbs_eq n with h | h
      · rw [← h]; exact hi
      · rw [show (n.natAbs : ℤ) = -n by omega, neg_smul]; exact hi.neg
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 hi'.tower_top
    obtain ⟨e, n', hn', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hn) p hp.ne_one
    have hu : IsUnit ((n' : ℕ) : V) := by
      by_contra h
      have h' : ((n' : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := h
      have hc : IsCoprime ((p : ℕ) : V) ((n' : ℕ) : V) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').cast
      obtain ⟨a, b, hab⟩ := hc
      exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ h')))
    obtain ⟨w, hw⟩ := hu.exists_left_inv
    have hw' : (w : F) * (n' : F) = 1 := by simpa using congrArg (fun z : V => (z : F)) hw
    refine ⟨e, w * y, ?_⟩
    have hy' : (y : F) = (p : F) ^ e * n' * x := by
      rw [show (y : F) = algebraMap V F y from rfl, hy, he]; simp
    push_cast
    rw [hy']
    linear_combination (-(x * (p : F) ^ e)) * hw'
  refine IsLocalization.Away.mk _ ?_ (fun s => ?_) fun a b h => ⟨0, by rw [Subtype.val_injective h]⟩
  · rw [map_natCast]; exact IsUnit.mk0 _ hp0
  · rw [map_natCast]; exact key s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isOpenImmersion_j {p : ℕ} {W : ValuationSubring ℂ} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (Y : Model Xo c (c.V W).subtype) : IsOpenImmersion Y.j := by
  have := c.fin
  have hV : (p : c.F) ∈ (c.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c.F.val.toRingHom (p : c.F)⁻¹ ∈ W := h
    simpa using h2
  have := away_of_valuation c.F (c.V W) p hp hV
  have : IsOpenImmersion (spMap (c.V W).subtype) := IsOpenImmersion.of_isLocalization (S := c.F) ((p : ℕ) : c.V W)
  have := Y.jQ_open
  unfold Model.j
  infer_instance

theorem dense_j {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β) (Y : Model Xo c β) :
    Dense (Set.range Y.j) := by
  have := Y.flat
  have h1 : DenseRange (pullback.fst Y.s (spMap β)) := by
    intro x
    let q : Sp c.F := (⊥ : PrimeSpectrum c.F)
    have hs : spMap β q ⤳ Y.s x := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      show Ideal.comap β ⊥ ≤ _
      rw [Ideal.comap_bot_of_injective _ hβ]
      exact bot_le
    obtain ⟨x', hx', e⟩ := Flat.generalizingMap Y.s hs
    refine closure_mono ?_ (specializes_iff_mem_closure.1 hx')
    rw [Set.singleton_subset_iff, Scheme.Pullback.range_fst]
    exact ⟨q, e.symm⟩
  have := h1.comp Y.jQ_dense (pullback.fst Y.s (spMap β)).continuous
  refine this.mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨t, Scheme.Hom.comp_apply _ _ _⟩

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

end GlobalTheory.LocM.BaseMdl
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.TupHecke

section General

variable {L : Type} [Field L] [NumberField L]

abbrev FI (L : Type) [Field L] [NumberField L] : Type := (FiniteAdeleRing (𝓞 L) L)ˣ

def sing (P : HeightOneSpectrum (𝓞 L)) : (P.adicCompletion L)ˣ →* FI L := Units.map (finiteSingle L P)

def cmp (P : HeightOneSpectrum (𝓞 L)) : FI L →* (P.adicCompletion L)ˣ :=
  Units.map { toFun := fun a => a P, map_one' := rfl, map_mul' := fun _ _ => rfl }



variable (L) in
def finP : Neutral.B1.Ideles L →* FI L := Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem cmp_val (P : HeightOneSpectrum (𝓞 L)) (u : FI L) :
    (cmp P u : P.adicCompletion L) = (u : FiniteAdeleRing (𝓞 L) L) P := rfl

open Classical in
theorem cmp_sing_self (P : HeightOneSpectrum (𝓞 L)) (x) : cmp P (sing P x) = x := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) P x P = x
  exact Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) P _ _

open Classical in
theorem cmp_sing_ne {P Q : HeightOneSpectrum (𝓞 L)} (h : P ≠ Q) (x) : cmp P (sing Q x) = 1 := by
  apply Units.ext
  show Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) Q x P = 1
  exact Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) h _ _


theorem valued_eq_one_of_le {P : HeightOneSpectrum (𝓞 L)} (x : (P.adicCompletion L)ˣ)
    (h : Valued.v (x : P.adicCompletion L) ≤ 1) (h' : Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) ≤ 1) :
    Valued.v (x : P.adicCompletion L) = 1 := by
  refine le_antisymm h ?_
  have e : Valued.v (x : P.adicCompletion L) * Valued.v ((x⁻¹ : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact e.symm.le.trans (mul_le_of_le_one_right' h')

theorem finite_nonunit (u : FI L) : {P | ¬ IsUnitAt P (cmp P u)}.Finite := by
  have h1 := Filter.eventually_cofinite.1 (u : FiniteAdeleRing (𝓞 L) L).2
  have h2 := Filter.eventually_cofinite.1 ((u⁻¹ : FI L) : FiniteAdeleRing (𝓞 L) L).2
  refine (h1.union h2).subset fun P hP => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hP (valued_eq_one_of_le _ hn.1 hn.2)

theorem finite_nat {N : ℕ} (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | Valued.v (N : P.adicCompletion L) ≠ 1}.Finite := by
  refine (finite_nonunit (Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom
    (Units.mk0 (N : L) (Nat.cast_ne_zero.2 hN.ne')))).subset fun P hP h => hP ?_
  rw [← map_natCast (algebraMap L (P.adicCompletion L))]
  exact h

def Cong (N : ℕ) (u : FI L) : Prop :=
  ∀ P, IsUnitAt P (cmp P u) ∧ Valued.v ((cmp P u : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)

variable {G : Type} [CommGroup G]

theorem cong_sing {N : ℕ} {P : HeightOneSpectrum (𝓞 L)} {x : (P.adicCompletion L)ˣ} (h : IsUnitAt P x)
    (h' : Valued.v ((x : P.adicCompletion L) - 1) ≤ Valued.v (N : P.adicCompletion L)) : Cong N (sing P x) := by
  intro Q
  by_cases e : Q = P
  · subst e
    rw [cmp_sing_self]
    exact ⟨h, h'⟩
  · rw [cmp_sing_ne e]
    simp [IsUnitAt]

theorem continuous_finP {N : ℕ} (hN : 0 < N) (ψ : FI L →* ℂˣ) (hψ : ∀ u, Cong N u → ψ u = 1) :
    Continuous (ψ.comp (finP L)) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 L)), ∀ P, P ∉ T → Valued.v (N : P.adicCompletion L) = 1 :=
    ⟨(finite_nat (L := L) hN).toFinset, fun P hP => by simpa using hP⟩
  choose n hn using fun P : HeightOneSpectrum (𝓞 L) =>
    GlobalTheory.Idele.exists_exp_neg_lt (GlobalTheory.AdLat.valued_natCast_ne_zero P hN)
  have ho := (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open L).2 T (T.sup n)
  have h1 := ho.mem_nhds (x := (1 : Neutral.B1.Ideles L)) ⟨one_mem _, fun v _ => by
    have : ((1 : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 := rfl
    rw [this, sub_self, map_zero]
    exact zero_le⟩
  have h2 : (fun _ => (1 : ℂˣ)) =ᶠ[nhds (1 : Neutral.B1.Ideles L)] (ψ.comp (finP L)) := by
    filter_upwards [h1] with a ha
    have hu : ∀ P, IsUnitAt P (cmp P (finP L a)) := ha.1
    refine (hψ (finP L a) fun P => ⟨hu P, ?_⟩).symm
    by_cases hP : P ∈ T
    · refine le_trans (ha.2 P hP) (le_trans ?_ (hn P).le)
      rw [WithZero.exp_le_exp]
      have := Finset.le_sup (f := n) hP
      omega
    · rw [hT P hP]
      exact Valuation.map_sub_le _ (hu P).le (by simp)
  exact continuous_of_continuousAt_one _ (continuousAt_const.congr h2)

end General

end GlobalTheory.Mem.TupHecke
end
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  first | exact @GlobalTheory.ConjTwist.conj_twist_isKTypeOf | exact GlobalTheory.ConjTwist.conj_twist_isKTypeOf | (intros; apply GlobalTheory.ConjTwist.conj_twist_isKTypeOf <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.KudlaSiegelWeil

namespace GlobalTheory.SmallThetaModules

section Restricted

variable {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def AdmFun (s : ∀ i, N i) : Type := {l : ∀ i, N i →ₗ[ℂ] ℂ // {i | l i (s i) ≠ 1}.Finite}

def evFam (s : ∀ i, N i) (ξ : ∀ i, N i) : AdmFun s → ℂ := fun l => ∏ᶠ i, l.1 i (ξ i)

def RTens (s : ∀ i, N i) : Submodule ℂ (AdmFun s → ℂ) :=
  Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = evFam s ξ}


open Classical in
def pureT (s : ∀ i, N i) (ξ : ∀ i, N i) : RTens s :=
  if h : Restr s ξ then ⟨evFam s ξ, Submodule.subset_span ⟨ξ, h, rfl⟩⟩ else 0

theorem coe_pureT {s ξ : ∀ i, N i} (h : Restr s ξ) : (pureT s ξ : AdmFun s → ℂ) = evFam s ξ := by
  unfold pureT; rw [dite_eq_left h]

omit [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] in
theorem restr_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (x : N v) :
    Restr s (Function.update ξ v x) := by
  refine (h.insert v).subset fun i hi => ?_
  by_cases hv : i = v
  · exact Or.inl hv
  · right
    simpa [Function.update_of_ne hv] using hi

theorem mulSupport_fin {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) :
    (Function.mulSupport fun i => l.1 i (ξ i)).Finite := by
  refine (Set.Finite.union h l.2).subset fun i hi => ?_
  by_cases e : ξ i = s i
  · right
    simpa [e] using hi
  · exact Or.inl e

theorem evFam_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) (v : ι) (x : N v) :
    evFam s (Function.update ξ v x) l = l.1 v x * ∏ᶠ (i) (_ : i ≠ v), l.1 i (ξ i) := by
  unfold evFam
  rw [← mul_finprod_cond_ne v (mulSupport_fin (restr_update h v x) l), Function.update_self]
  congr 1
  refine finprod_congr fun i => finprod_congr fun hi => ?_
  rw [Function.update_of_ne hi]

theorem pureT_mlin [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (c : ℂ) (x y : N v) :
    pureT s (Function.update ξ v (c • x + y)) =
      c • pureT s (Function.update ξ v x) + pureT s (Function.update ξ v y) := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, coe_pureT (restr_update h v _), coe_pureT (restr_update h v _),
    coe_pureT (restr_update h v _)]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, evFam_update h, map_add (f := _), map_smul, smul_eq_mul]
  ring

theorem pureT_span (s : ∀ i, N i) :
    Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = pureT s ξ} = ⊤ := by
  apply Submodule.map_injective_of_injective (RTens s).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  change _ = Submodule.span ℂ _
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨ξ, h, rfl⟩, rfl⟩
    exact ⟨ξ, h, coe_pureT h⟩
  · rintro ⟨ξ, h, rfl⟩
    exact ⟨_, ⟨ξ, h, rfl⟩, coe_pureT h⟩

theorem pureT_sep (s : ∀ i, N i) (l : ∀ i, N i →ₗ[ℂ] ℂ) (hl : {i | l i (s i) ≠ 1}.Finite) :
    ∃ Λ : RTens s →ₗ[ℂ] ℂ, ∀ ξ, Restr s ξ → Λ (pureT s ξ) = ∏ᶠ i, l i (ξ i) :=
  ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : AdmFun s => ℂ) (show AdmFun s from ⟨l, hl⟩)).comp (RTens s).subtype,
    fun _ h => congrFun (coe_pureT h) (show AdmFun s from ⟨l, hl⟩)⟩

theorem exists_lift {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (m : ∀ i, M i)
    {S : Type} [AddCommGroup S] [Module ℂ S] (pu : (∀ i, M i) → S)
    (hsep : ∀ l : ∀ i, M i →ₗ[ℂ] ℂ, {i | l i (m i) ≠ 1}.Finite →
      ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l i (φ i))
    (s : ∀ i, N i) (p : ∀ i, M i →ₗ[ℂ] N i) :
    ∃ P : S →ₗ[ℂ] RTens s, ∀ φ, Restr m φ → P (pu φ) = pureT s fun i => p i (φ i) := by
  by_cases hp : {i | p i (m i) ≠ s i}.Finite
  · have h1 : ∀ l : AdmFun s, ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l.1 i (p i (φ i)) := by
      intro l
      refine hsep (fun i => (l.1 i).comp (p i)) ((hp.union l.2).subset fun i hi => ?_)
      by_cases e : p i (m i) = s i
      · right
        simpa [e] using hi
      · exact Or.inl e
    choose Λ hΛ using h1
    obtain ⟨r, hr⟩ := (RTens s).subtype.exists_leftInverse_of_injective (RTens s).ker_subtype
    refine ⟨r.comp (LinearMap.pi Λ), fun φ hφ => ?_⟩
    have h2 : Restr s fun i => p i (φ i) := by
      refine (Set.Finite.union hφ hp).subset fun i hi => ?_
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    have h3 : LinearMap.pi Λ (pu φ) = (RTens s).subtype (pureT s fun i => p i (φ i)) := by
      rw [Submodule.subtype_apply, coe_pureT h2]
      funext l
      exact hΛ l φ hφ
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  · refine ⟨0, fun φ hφ => ?_⟩
    have h2 : ¬ Restr s fun i => p i (φ i) := by
      intro h
      refine hp ((Set.Finite.union hφ h).subset fun i hi => ?_)
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    unfold pureT
    rw [dite_eq_right h2, LinearMap.zero_apply]

end Restricted

variable {D : D7} {X : ThetaX D}

section Collapse

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Collapse

end GlobalTheory.SmallThetaModules

end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (n M : ℕ) (ν ν' : Measure (Fin n → Fin M → AF F ⊗[F] E)), (∀ (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ), Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf → Integrable Φ ν ∧ Integrable Φ ν' ∧ ∫ X, Φ X ∂ν = ∫ X, Φ X ∂ν') → ν = ν' := by
  first | exact @GlobalTheory.GaugeEx.PureUniq.measure_ext_of_pure | exact GlobalTheory.GaugeEx.PureUniq.measure_ext_of_pure | (intros; apply GlobalTheory.GaugeEx.PureUniq.measure_ext_of_pure <;> assumption)
end
