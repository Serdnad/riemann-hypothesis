module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle022
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdIccFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbFund
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RcFlag
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle037
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle010
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A36
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle033
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle035
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimSeq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle044
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle036
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle034
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle021
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

open Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap in
theorem map_first_power {R R₂ : Type} [CommRing R] [CommRing R₂] {f : R →+* R₂} {d : ℕ} {O : Type} [CommRing O]
    [StarRing O] {B : FB R d O} {B₂ : FB R₂ d O} (h : IsMapOf f B B₂) (m : ℕ) :
    pow1 B₂ m = MvPowerSeries.map f (pow1 B m) := by
  have hact : ∀ a : O, mp f (B.A.act a) = B₂.A.act a := fun a => funext fun i => (h.act a i).symm
  unfold pow1
  rw [map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  have hc : ∀ (j : Fin 3) (i : Fin d),
      constantCoeff ((![comp1 (B.A.act (n : O)) (pt R d 0), pt R d 0, pt R d 1] : Fin 3 → Pt R 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cz_comp1 _ (B.A.const _) _ (cz_pt 0) i
    · exact cz_pt 0 i
    · exact cz_pt 1 i
  rw [map_ev' f _ hc B.ph1, ← h.ph1]
  congr 1
  funext j
  fin_cases j
  · simp [mp_comp1 f _ _ (cz_pt 0), mp_pt, hact]
  · simp [mp_pt]
  · simp [mp_pt]

private theorem lin_map' {R R₂ : Type} [CommRing R] [CommRing R₂] (f : R →+* R₂) {d : ℕ}
    (φ : Pt R 1 d) (m : ℕ) : lin (fun i => MvPowerSeries.map f (φ i)) m = (lin φ m).map f := by
  ext i j
  simp [lin, Matrix.map_apply, MvPowerSeries.coeff_map]

private theorem bil_map' {R R₂ : Type} [CommRing R] [CommRing R₂] (f : R →+* R₂) {d : ℕ}
    (g : PS R 2 d) (m n : ℕ) : bil (MvPowerSeries.map f g) m n = (bil g m n).map f := by
  ext i j
  simp [bil, Matrix.map_apply, MvPowerSeries.coeff_map]

theorem map_mats : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f := by
  intro R R₂ _ _ f d O _ _ B B₂ h
  have hact : ∀ a : O, B₂.A.act a = fun i => MvPowerSeries.map f (B.A.act a i) :=
    fun a => funext fun i => h.act a i
  refine ⟨fun a => ⟨?_, ?_⟩, ?_, fun p => ⟨?_, ?_⟩⟩
  · show lin (B₂.A.act a) 1 = _
    rw [hact, lin_map']
    rfl
  · rw [h.ad, bil_map']
  · rw [h.sy, bil_map']
  · show lin (B₂.A.act (p : O)) p = _
    rw [hact, lin_map']
    rfl
  · show bil (pow1 B₂ p) p 1 = _
    rw [map_first_power h, bil_map']
    rfl

end PositivityTheory.HtPt.Cc
end
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rfin

theorem a_nonunit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  Rom.a_nonunit_of @Pmono.r_mono

end PositivityTheory.HtPt.Rfin
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem flag_om : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r :=
  flag_om_of @PositivityTheory.HtPt.Rb.fund_ex @PositivityTheory.HtPt.Rc.subquo @PositivityTheory.HtPt.Rc.om_split
    @PositivityTheory.HtPt.Rc.om_step

theorem gr_partial : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) :=
  gr_partial_of @PositivityTheory.HtPt.Rb.fund_ex @PositivityTheory.HtPt.Rc.subquo @PositivityTheory.HtPt.Rc.step
    @PositivityTheory.HtPt.Rc.om_split @PositivityTheory.HtPt.Rc.om_step

end PositivityTheory.HtPt.Rd
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace PositivityTheory.HtPt.Mk

theorem epi_fieldMap {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (Spec.map (CommRingCat.ofHom a)) := by
  have : Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := a.toAlgebra
    exact (inferInstance : Module.Flat Ω K)
  have : Surjective (Spec.map (CommRingCat.ofHom a)) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint K, Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem spec_map_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem card_char_le (T K : Type) [Group T] [Finite T] [Field K] :
    Finite (T →* Kˣ) ∧ Nat.card (T →* Kˣ) ≤ Nat.card T := by
  classical
  have := Fintype.ofFinite T
  have hinj : Function.Injective (fun χ : T →* Kˣ => (Units.coeHom K).comp χ) := fun a b h =>
    MonoidHom.ext fun t => Units.ext (DFunLike.congr_fun h t)
  have hli := (linearIndependent_monoidHom T K).comp _ hinj
  have hf : Finite (T →* Kˣ) := hli.finite
  refine ⟨hf, ?_⟩
  have := Fintype.ofFinite (T →* Kˣ)
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

theorem char_descend {T K K' : Type} [Group T] [Finite T] [Field K] [Field K'] (i : K →+* K')
    (hsep : ∀ t : T, (∀ χ : T →* Kˣ, χ t = 1) → t = 1) (χ' : T →* K'ˣ) :
    ∃ χ : T →* Kˣ, ∀ t, (χ' t : K') = i (χ t) := by
  obtain ⟨h1, -⟩ := card_char_le T K
  obtain ⟨h2, c2⟩ := card_char_le T K'
  obtain ⟨h3, c3⟩ := card_char_le (T →* Kˣ) K
  let ev : T →* ((T →* Kˣ) →* Kˣ) := MonoidHom.mk' (fun t => MonoidHom.mk' (fun χ => χ t) fun _ _ => rfl)
    fun a b => MonoidHom.ext fun χ => map_mul χ a b
  have hev : Function.Injective ev := (injective_iff_map_eq_one ev).2 fun t h =>
    hsep t fun χ => DFunLike.congr_fun h χ
  have c4 := Nat.card_le_card_of_injective _ hev
  let m : (T →* Kˣ) → (T →* K'ˣ) := fun χ => (Units.map i.toMonoidHom).comp χ
  have hm : Function.Injective m := fun a b h =>
    MonoidHom.ext fun t => Units.ext (i.injective (congrArg Units.val (DFunLike.congr_fun h t)))
  have hb := hm.bijective_of_nat_card_le (c2.trans (c4.trans c3))
  obtain ⟨χ, rfl⟩ := hb.2 χ'
  exact ⟨χ, fun t => rfl⟩

theorem ht_weil_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ n : ℕ, FullTorsion G ξ n → FullTorsion G' ξ' n ∧ ∀ e, GenWeil G L ξ n e → ∃ e', GenWeil G' L' ξ' n e' ∧ ∀ (x g : Over.mk ξ ⟶ G) (x' g' : Over.mk ξ' ⟶ G'), x ^ n = 1 → g ^ n = 1 → x'.left ≫ φ = spMap i ≫ x.left → g'.left ≫ φ = spMap i ≫ g.left → (e' x' g' : Ω') = i (e x g) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hd G _ _ G' _ φ hp L L' hL hL' hw n hF
  have hd' : spMap i ≫ ξ = ξ' ≫ f := hd.symm
  have hsp : ∀ {k : Type} [Field k] (a : Ω' →+* k), spMap (a.comp i) = spMap a ≫ spMap i := fun a =>
    spec_map_comp i a
  have hdk : ∀ {k : Type} [Field k] (a : Ω' →+* k), spMap (a.comp i) ≫ ξ = (spMap a ≫ ξ') ≫ f := fun a => by
    rw [hsp, Category.assoc, hd', Category.assoc]
  obtain ⟨E, hE⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (Over.mk ξ') (spMap i ≫ ξ) hd'
  let ψ : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl
  let inc : (Over.mk ξ ⟶ G) →* (Over.mk ξ' ⟶ G') :=
    E.symm.toMonoidHom.comp (MonoidHom.mk' (fun x => ψ ≫ x) fun x y => MonObj.comp_mul ψ x y)
  have hinc : ∀ x, (inc x).left ≫ φ = spMap i ≫ x.left := fun x => by
    rw [← hE]
    exact congrArg (·.left) (E.apply_symm_apply (ψ ≫ x))
  have hext : ∀ {T : Over X'} (a b : T ⟶ G'), a.left ≫ φ = b.left ≫ φ → a = b := fun a b h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have hepi := epi_fieldMap i
  have hinj : Function.Injective inc := fun a b h => Over.OverMorphism.ext
    ((cancel_epi (spMap i)).1 (by rw [← hinc, ← hinc, h]))
  have hsurj : ∀ x', x' ^ n = 1 → ∃ x, x ^ n = 1 ∧ inc x = x' := fun x' hx' => by
    obtain ⟨x, hx⟩ := hF Ω' i (E x') (by rw [← map_pow, hx', map_one])
    have e : inc x = x' := hext _ _ (by rw [hinc, ← hx, hE])
    exact ⟨x, hinj (by rw [map_pow, e, hx', map_one]), e⟩
  have hpow : ∀ x, x ^ n = 1 → inc x ^ n = 1 := fun x hx => by rw [← map_pow, hx, map_one]
  refine ⟨fun k _ a g hg => ?_, fun e hW => ?_⟩
  · obtain ⟨Ek, hEk⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (Over.mk (spMap a ≫ ξ')) (spMap (a.comp i) ≫ ξ) (hdk a)
    obtain ⟨x, hx⟩ := hF k (a.comp i) (Ek g) (by rw [← map_pow, hg, map_one])
    refine ⟨inc x, hp.1.hom_ext ?_ ?_⟩
    · rw [← hEk, hx, Category.assoc, hinc, hsp, Category.assoc]
    · rw [Category.assoc, Over.w, Over.w]; rfl
  let r := Function.invFun inc
  have hr : ∀ x, r (inc x) = x := Function.leftInverse_invFun hinj
  refine ⟨fun x' g' => Units.map i.toMonoidHom (e (r x') (r g')), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hW.finite
    refine Finite.of_surjective (fun x : {x : Over.mk ξ ⟶ G // x ^ n = 1} => (⟨inc x, hpow _ x.2⟩ :
      {x : Over.mk ξ' ⟶ G' // x ^ n = 1})) fun x' => ?_
    obtain ⟨x, hx, e⟩ := hsurj _ x'.2
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  · intro x y g hx hy hg
    obtain ⟨x, hx₀, rfl⟩ := hsurj x hx
    replace hx := hx₀
    obtain ⟨y, hy₀, rfl⟩ := hsurj y hy
    replace hy := hy₀
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    simp only [← map_mul, hr]
    rw [hW.mul_left x y g hx hy hg]
  · intro x y g hx hy hg
    obtain ⟨x, hx₀, rfl⟩ := hsurj x hx
    replace hx := hx₀
    obtain ⟨y, hy₀, rfl⟩ := hsurj y hy
    replace hy := hy₀
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    simp only [← map_mul, hr]
    rw [hW.mul_right x y g hx hy hg]
  · intro χ' hχ'
    let T : Subgroup (Over.mk ξ ⟶ G) := (powMonoidHom n : (Over.mk ξ ⟶ G) →* (Over.mk ξ ⟶ G)).ker
    have hT : ∀ t : T, t.1 ^ n = 1 := fun t => t.2
    have : Finite T := hW.finite
    obtain ⟨χ, hχ⟩ := char_descend (T := T) i (fun t ht => Subtype.ext (hW.nondeg t.1 (hT t) fun x hx =>
        ht (MonoidHom.mk' (fun s => e x s.1) fun s s' => hW.mul_right x _ _ hx (hT s) (hT s'))))
      (MonoidHom.mk' (fun t => χ' (inc t.1)) fun s t => by
        rw [← hχ' _ _ (hpow _ (hT s)) (hpow _ (hT t)), ← map_mul]; rfl)
    classical
    obtain ⟨x, hx, hxe⟩ := hW.perfect (fun g => if h : g ^ n = 1 then χ ⟨g, h⟩ else 1) fun g g' hg hg' => by
      have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
      rw [dite_eq_left hg, dite_eq_left hg', dite_eq_left hgg, ← map_mul]; rfl
    refine ⟨inc x, hpow x hx, fun g hg => ?_⟩
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    have h1 := hxe g hg
    rw [dite_eq_left hg] at h1
    rw [hr, hr, ← h1]
    exact Units.ext (hχ ⟨g, hg⟩)
  · intro g hg h
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    rw [hW.nondeg g hg fun x hx => ?_, map_one]
    have h1 := congrArg Units.val (h (inc x) (hpow x hx))
    rw [hr, hr] at h1
    exact Units.ext (i.injective (h1.trans (map_one i).symm))
  · intro x g hx hg k _ _ a xk gk c hxk hgk
    obtain ⟨x, hx₀, rfl⟩ := hsurj x hx
    replace hx := hx₀
    obtain ⟨g, hg₀, rfl⟩ := hsurj g hg
    replace hg := hg₀
    rw [hr, hr]
    obtain ⟨Ek, hEk⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (Over.mk (spMap a ≫ ξ')) (spMap (a.comp i) ≫ ξ) (hdk a)
    have key : ∀ (z : Spec (CommRingCat.of k) ⟶ X) (hz : z = (spMap a ≫ ξ') ≫ f) (x₀ g₀ : Over.mk z ⟶ G),
        x₀.left = xk.left ≫ φ → g₀.left = gk.left ≫ φ →
          (Out.WeilIs G' L' n xk gk (unitOn c) ↔ Out.WeilIs G L n x₀ g₀ (unitOn c)) := by
      intro z hz x₀ g₀ h1 h2
      subst hz
      exact GlobalTheory.weilIs_grpPullback_of_comm _ _ G G' f φ L L' hL hL' hp hw _ n xk gk x₀ g₀ _ h1 h2
    rw [key _ (hdk a) (Ek xk) (Ek gk) (hEk _) (hEk _)]
    have hcomp : ∀ (y : Over.mk ξ ⟶ G) (yk : Over.mk (spMap a ≫ ξ') ⟶ G'), yk.left = spMap a ≫ (inc y).left →
        (Ek yk).left = spMap (a.comp i) ≫ y.left := fun y yk h =>
      (hEk yk).trans ((congrArg (· ≫ φ) h).trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap a ≫ ·) (hinc y)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ y.left) (hsp a).symm)))))
    exact hW.weil x g hx hg k (a.comp i) (Ek xk) (Ek gk) c (hcomp x xk hxk) (hcomp g gk hgk)
  · intro x g x' g' _ _ h1 h2
    obtain rfl : inc x = x' := hext _ _ ((hinc x).trans h1.symm)
    obtain rfl : inc g = g' := hext _ _ ((hinc g).trans h2.symm)
    simp only [hr]
    rfl

end PositivityTheory.HtPt.Mk
end
end

section

namespace PositivityTheory.HtPt.Ktw

theorem a52 :
    GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.proof
    GroundTheory.Heights₂.Heights.Kleiman.GlobalFunctionsIntegral.proof

theorem a53 :
    GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.proof a52

theorem a54 :
    GroundTheory.Heights₂.Heights.Kleiman.CutComponent.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutComponent.proof
    GroundTheory.Heights₂.Heights.Kleiman.CutZeroNotLe.proof a53
    GroundTheory.Heights₂.Heights.Kleiman.CutDimLower.proof

theorem a55 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.proof hR
    GroundTheory.Heights₂.Heights.Kleiman.PointDegreePos.proof a54
    GroundTheory.Heights₂.Heights.Kleiman.CutMultPos.proof

theorem a56 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.proof
    GroundTheory.Heights₂.Heights.Kleiman.ZeroIdealChart.proof

theorem a57 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.Exists.proof

theorem a58 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.proof a57
    GroundTheory.Heights₂.Heights.Kleiman.QuotTrans.proof
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Piece.proof

theorem a59 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimVanish.Statement.{0, 0} :=
  PositivityTheory.HtPt.KtwS.ClaimVanish.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof a56

theorem a60 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Statement.{0, 0, 0} :=
  PositivityTheory.HtPt.KtwS.StepTwo.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof

theorem a61 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.proof a56 a59 a60

theorem a62 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.proof a4
    GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated.proof

theorem a63 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

theorem a72 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

end PositivityTheory.HtPt.Ktw
end
