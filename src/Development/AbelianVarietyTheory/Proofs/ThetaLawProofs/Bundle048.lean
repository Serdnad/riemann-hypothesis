module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfTwoTorsionTranslate
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle047
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle036
public import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.Cardinality
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.PolVanishing

variable {X : Scheme.{0}} {L : LB X}

theorem lbIso_pw_tw (hL : L.IsLB) (b N t : ℤ) :
    LBIso (AbLaw.pw L (b + N * t)) (tw (AbLaw.pw L b) (AbLaw.pw L N) t) := by
  refine lbIso_of_chartPull ⟨fun i => (i, i), fun i y hy => ⟨hy, hy⟩, fun y i j hi hj => ?_⟩
    (isLB_tw (isLB_pw hL b) (isLB_pw hL N) t)
  refine Eq.trans ?_ (gm_div (AbLaw.pw (AbLaw.pw L N) (-t)) (AbLaw.pw L b) (𝟙 X) y (i, i) (j, j)
    ⟨⟨hi, hi⟩, hj, hj⟩).symm
  change gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ (b + N * t)) =
    gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j ^ b) * (gm (𝟙 X) y (L.U i ⊓ L.U j) ((L.g i j ^ N) ^ (-t)))⁻¹
  rw [← map_inv, ← map_mul, zpow_neg, inv_inv, ← zpow_mul, ← zpow_add]

theorem lbIso_pull_pw (μ' : X ⟶ X) (d l : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1])) (hα : α.IsGen) :
    LBIso ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) := by
  let A := LB.LinComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1]
  have le : ∀ p : L.ι × (PUnit → L.ι), L.U p.1 ⊓ ((AbLaw.pw L l).pull μ').U p.2 ≤
      LB.wchart L (K := Fin 2) ![𝟙 X, μ'] ![p.1, p.2 PUnit.unit] := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hy.1, mem_pull.1 hy.2]
  refine gen_chartPull (A' := LB.div (AbLaw.pw L (d * l)) ((AbLaw.pw L l).pull μ')) (h := 𝟙 X)
    (A := AbLaw.pw A l) ⟨fun p => ![p.1, p.2 PUnit.unit], le, fun y p q hp hq => ?_⟩
    ⟨fun j => α.s j ^ l⟩ fun i j => ?_
  · refine (gm_div ((AbLaw.pw L l).pull μ') (AbLaw.pw L (d * l)) (𝟙 X) y p q ⟨hp, hq⟩).trans ?_
    rw [gm_pull_g (AbLaw.pw L l) μ' (𝟙 X) y p.2 q.2 hp.2 hq.2]
    refine Eq.trans ?_ ((map_zpow _ _ l).trans (congrArg (· ^ l)
      (gm_linComb L (K := Fin 2) ![𝟙 X, μ'] ![d, -1] (𝟙 X) y _ _ (le p hp) (le q hq)))).symm
    rw [Fin.prod_univ_two]
    change gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1 ^ (d * l)) *
        (gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit) ^ l))⁻¹ =
      (gm (𝟙 X) y (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ d *
        gm (𝟙 X ≫ μ') y (L.U (p.2 PUnit.unit) ⊓ L.U (q.2 PUnit.unit))
          (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)) ^ (-1 : ℤ)) ^ l
    rw [map_zpow, map_zpow, mul_zpow, zpow_neg_one, inv_zpow, zpow_mul]
  · have h := congrArg (· ^ l) (hα i j)
    simp only [mul_zpow, ← map_zpow] at h
    exact h

variable {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)}

theorem exactAt_of_lbIso {M M' : LB X} (hM : M.IsLB) (hM' : M'.IsLB) (h : LBIso M M')
    {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M' D)).ExactAt p := by
  obtain ⟨w, hw⟩ := h
  exact hp.of_iso ((cubeFunctor κ R).mapIso (secCubeCongr f D hM hM' w hw))

theorem exactAt_of_affine_covers [IsSeparated f] {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → X.Opens}
    {κ' : Type} [LinearOrder κ'] [Fintype κ'] {D' : κ' → X.Opens}
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hD' : ∀ i, IsAffineOpen (D' i)) (hc' : ⨆ i, D' i = ⊤) {p : ℕ}
    (hp : (cubeComplex (secCube f M D)).ExactAt p) : (cubeComplex (secCube f M D')).ExactAt p := by
  match p with
  | 0 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').1
  | 1 => exact (secCube_exactAt_zero_and_one R X f M κ' D' hc').2
  | p + 2 =>
    rw [← cechComplex_exactAt_succ_iff_cube, HomologicalComplex.exactAt_iff_isZero_homology,
      ModuleCat.isZero_iff_subsingleton] at hp ⊢
    obtain ⟨e⟩ := cechLB_homology_equiv_of_affine_covers R X f M κ D κ' D' hM inferInstance
      hD hc hD' hc' (p + 1)
    exact @Equiv.subsingleton _ _ e.symm.toEquiv hp

theorem exists_forall_le_exactAt [IsNoetherianRing R] (hL : L.IsLB) {N : ℤ} (hN : 0 < N) {m : ℕ}
    {s : Fin (m + 1) → LB.Sec (AbLaw.pw L N)} (hs : VeryAmpleBy f (AbLaw.pw L N) s) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p,
      (cubeComplex (secCube f (AbLaw.pw L n) (fun i => Out.nonzeroLocus (s i)))).ExactAt p := by
  choose t₀ ht₀ using fun b : ℤ =>
    GlobalTheory.T.serre_vanishing_cubeTotalComplex_exactAt R X f (AbLaw.pw L N) m s (AbLaw.pw L b) (isLB_pw hL N) (isLB_pw hL b) hs
  obtain ⟨T, hT⟩ := ((Set.finite_Ico (0 : ℤ) N).image t₀).bddAbove
  refine ⟨T * N, fun n hn p => ?_⟩
  have h₁ : t₀ (n % N) ≤ n / N :=
    (hT ⟨n % N, ⟨Int.emod_nonneg n hN.ne', Int.emod_lt_of_pos n hN⟩, rfl⟩).trans
      (Int.le_ediv_of_mul_le hN hn)
  have h₂ := exactAt_of_lbIso (isLB_tw (isLB_pw hL _) (isLB_pw hL N) _) (isLB_pw hL _)
    (lbIso_pw_tw hL (n % N) N (n / N)).symm (ht₀ (n % N) (n / N) h₁ p)
  rwa [Int.emod_add_mul_ediv] at h₂

theorem exists_le_natCast_ne_zero (K : Type) [Field K] (B : ℕ) : ∃ m : ℕ, B ≤ m ∧ (m : K) ≠ 0 := by
  by_cases h : (B : K) = 0
  · exact ⟨B + 1, Nat.le_succ B, by simp [h]⟩
  · exact ⟨B, le_rfl, h⟩

theorem exactAt_secCube_pw : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℤ) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens), 1 ≤ l → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ p, (cubeComplex (secCube P.A.hom (pw P.L l) D)).ExactAt p := by
  intro hLaw K _ _ P l I _ _ D hl hD hc p
  have := P.isAb.proper
  obtain ⟨N, hN, r, s, -, hs⟩ := veryAmpleBy_of_relAmple P.isLB P.ample (𝟙 P.A.left)
    (Category.id_comp _) P.isLB (lbIso_pull_id P.isLB).symm
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_exactAt P.isLB (by exact_mod_cast hN) hs
  obtain ⟨m, hm, hmK⟩ := exists_le_natCast_ne_zero K n₀.toNat
  have hm₁ : 1 ≤ m := Nat.pos_of_ne_zero fun h => hmK (by simp [h])
  have hle : n₀ ≤ (m : ℤ) ^ 2 * l := by
    have h₁ : n₀ ≤ m := by omega
    have h₂ : (1 : ℤ) ≤ m := by exact_mod_cast hm₁
    nlinarith [mul_nonneg (sq_nonneg (m : ℤ)) (sub_nonneg.2 hl)]
  obtain ⟨α, hα⟩ := hLaw.mulPull _ P m
  have := (hLaw.mulN _ P m hm₁).1
  refine GlobalTheory.T.exactAt_sectionCube_of_mul_pullback hLaw K P m _ I D p hmK (isLB_pw P.isLB l) ?_
  refine exactAt_of_lbIso (isLB_pw P.isLB _) (LB.isLB_pull (isLB_pw P.isLB l) _)
    (lbIso_pull_pw _ _ l α hα).symm ?_
  refine exactAt_of_affine_covers (isLB_pw P.isLB _) (fun i => (hs.2 i).1) hs.1
    (fun i => (hD i).preimage _) ?_ (hn₀ _ hle p)
  rw [← Scheme.Hom.preimage_iSup, hc]
  rfl

end GlobalTheory.PolVanishing
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.keyDatumConnectedFamily_of_polarizedArithmeticFamily : Out.Laws → Out.Laws2 → PolFam → GlobalTheory.KeyKa.ConnFam := by
  first | exact @GlobalTheory.KeyFam.connFam_of_polFam | exact GlobalTheory.KeyFam.connFam_of_polFam | (intros; apply GlobalTheory.KeyFam.connFam_of_polFam <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_twoTorsion_translate : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A), IsMonHom e.hom → t ^ 2 = 1 → LBIso y'.P.L (y.P.L.pull (e.hom ≫ ((toUnit y.P.A ≫ t) * 𝟙 y.P.A)).left) → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownTwist.known_of_translate | exact GlobalTheory.KnownTwist.known_of_translate | (intros; apply GlobalTheory.KnownTwist.known_of_translate <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.keyData_descend_countable_subrings : Out.Laws → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] [CharZero R] (x : KeyIn R) (s : Set R), s.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype) ∧ KeyDesc := by
  first | exact @GlobalTheory.KeyCountableDescent.keyIn_descends_countable | exact GlobalTheory.KeyCountableDescent.keyIn_descends_countable | (intros; apply GlobalTheory.KeyCountableDescent.keyIn_descends_countable <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyHouse


open Cardinal in
theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    have hK : #K ≤ 𝔠 := Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem g_eq_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, _⟩ := h
  exact hg

def NormalValue (g n : ℕ) (κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ) : Prop :=
  ∀ (x : KeyIn ℂ) (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c₀ : ℂ), x.P.g = g →
    charHalf x.P.g a b → c₀ ≠ 0 → Mx.det ≠ 0 → NormalAt x τ Mx a b c₀ → (κ ℂ x : ℂ) = (Mx.det ^ 4 / c₀ ^ 8) ^ n

theorem pow_eq_pow (hU : ThetaUnifAV) (hD : KeyDesc) {g n n' M M' : ℕ}
    {κ κ' : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ} (h : KaRuleK g n M κ) (h' : KaRuleK g n' M' κ')
    (hn : NormalValue g n κ) (hn' : NormalValue g n' κ') (K : Type) [Field K] [CharZero K] (x : KeyIn K)
    (hx : x.P.g = g) : (κ K x : K) ^ n' = (κ' K x : K) ^ n := by
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := hD K x
  have hg₀ : x₀.P.g = g := (g_eq_of_keyPB hx₀).symm.trans hx
  obtain ⟨σ⟩ := nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  have hgy : y.P.g = g := (g_eq_of_keyPB hy).trans hg₀
  obtain ⟨⟨τ, Mx, a, b, c, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt hU y
  have e : (κ ℂ y : ℂ) ^ n' = (κ' ℂ y : ℂ) ^ n := by
    rw [hn y τ Mx a b c hgy hab hc hM hN, hn' y τ Mx a b c hgy hab hc hM hN, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h.2.1 K₀ ℂ σ x₀ y hg₀ hy, h'.2.1 K₀ ℂ σ x₀ y hg₀ hy, ← map_pow, ← map_pow] at e
  rw [h.2.1 K₀ K _ x₀ x hg₀ hx₀, h'.2.1 K₀ K _ x₀ x hg₀ hx₀, ← map_pow, ← map_pow, σ.injective e]

theorem exists_unit_of_pow {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {z : K} {n : ℕ} (hn : 1 ≤ n) {u : Rˣ} (h : z ^ n = algebraMap R K u) :
    ∃ w : Rˣ, z = algebraMap R K w := by
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K) (x := z) hn
    (h ▸ isIntegral_algebraMap)
  rw [← map_pow] at h
  have hr : IsUnit (r ^ n) := (IsFractionRing.injective R K h) ▸ u.isUnit
  obtain ⟨w, rfl⟩ := (isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hn)).1 hr
  exact ⟨w, rfl⟩

theorem exists_prime_of_not_isUnit {R : Type} [CommRing R] [IsLocalRing R] {M : ℕ} (hM : 1 ≤ M)
    (h : ¬ IsUnit (M : R)) : ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → IsUnit (m : R) := by
  let k := IsLocalRing.ResidueField R
  have key : ∀ m : ℕ, IsUnit (m : R) ↔ ¬ ringChar k ∣ m := fun m => by
    rw [← ringChar.spec, ← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
  refine ⟨ringChar k, (CharP.char_is_prime_or_zero k _).resolve_right fun h0 => ?_, fun m hm => (key m).2 hm⟩
  rw [key, not_not, h0, zero_dvd_iff] at h
  omega

theorem isUnit_of_surjective {R k : Type} [CommRing R] [IsLocalRing R] [Field k] [CharZero k] {r : R →+* k}
    (hr : Function.Surjective r) {M : ℕ} (hM : 1 ≤ M) : IsUnit (M : R) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr),
    RingHom.mem_ker, map_natCast, Nat.cast_eq_zero]
  omega

theorem keyRule_of_kaSt : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → KaSt → KeyDesc → ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  intro hL hU hI hP hT hK hD
  have hall : ∀ g p : ℕ, p.Prime → ∃ (n M : ℕ) (κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ),
      1 ≤ n ∧ 1 ≤ M ∧ (1 ≤ g → ¬ p ∣ M ∧ KaRuleK g n M κ ∧ NormalValue g n κ) := by
    intro g p hp
    by_cases hg : 1 ≤ g
    · obtain ⟨c, M, hc, hM, hpM, hr⟩ := hK (2 * g) p (by omega) hp
      obtain ⟨κ, h₁, h₂⟩ := GlobalTheory.T.exists_normalised_key_invariant_rule_char_zero hL hU hI hP hT g c M hg hr
      exact ⟨2 * c, M, κ, by omega, hM, fun _ => ⟨hpM, h₁, h₂⟩⟩
    · exact ⟨1, 1, fun _ _ _ _ => 1, le_rfl, le_rfl, fun h => absurd h hg⟩
  choose N M κ hN hM hκ using fun g => hall g 2 Nat.prime_two
  refine ⟨N, hN, fun K _ _ x => κ x.P.g K x, ?_, ?_, ?_, ?_⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx h₁
    exact (hκ P.g h₁).2.1.1 K P hg rig hr th hth v hv th' hth' v' hv' a Mx rfl
  · intro K K' _ _ _ _ f x x' hg h
    dsimp only
    rw [show κ x'.P.g K' x' = κ x.P.g K' x' by rw [g_eq_of_keyPB h]]
    exact (hκ _ hg).2.1.2.1 K K' f x x' rfl h
  · intro R K _ _ _ _ _ _ _ x xK hg h
    dsimp only
    rw [show κ xK.P.g K xK = κ x.P.g K xK by rw [g_eq_of_keyPB h]]
    obtain ⟨-, h₁, h₂⟩ := hκ _ hg
    by_cases hu : IsUnit (M x.P.g : R)
    · obtain ⟨u, hu₁, hu₂⟩ := h₁.2.2.1 R K x xK rfl hu h
      refine ⟨u, hu₁, fun k _ _ r xk hr hk => ?_⟩
      rw [show κ xk.P.g k xk = κ x.P.g k xk by rw [g_eq_of_keyPB hk]]
      exact hu₂ k r xk hr hk
    · obtain ⟨p, hp, hpu⟩ := exists_prime_of_not_isUnit (hM _) hu
      obtain ⟨n', M', κ', hn', -, h'⟩ := hall x.P.g p hp
      obtain ⟨hpM, h₁', h₂'⟩ := h' hg
      obtain ⟨u, hu₁, -⟩ := h₁'.2.2.1 R K x xK rfl (hpu _ hpM) h
      have e := pow_eq_pow hU hD h₁ h₁' h₂ h₂' K xK (g_eq_of_keyPB h)
      rw [hu₁, ← map_pow, ← Units.val_pow_eq_pow_val u] at e
      obtain ⟨w, hw⟩ := exists_unit_of_pow hn' e
      exact ⟨w, hw, fun k _ _ r xk hr _ => absurd (isUnit_of_surjective hr (hM _)) hu⟩
  · intro x τ a b hg hab hx
    have := (hκ _ hg).2.2 x τ 1 a b 1 rfl hab one_ne_zero (by simp) hx
    apply Units.ext
    simpa using this

end GlobalTheory.KeyHouse
end
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.thetaKeyRule_exists_of_algebraic_invariants : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → KaSt → KeyDesc → ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  first | exact @GlobalTheory.KeyHouse.keyRule_of_kaSt | exact GlobalTheory.KeyHouse.keyRule_of_kaSt | (intros; apply GlobalTheory.KeyHouse.keyRule_of_kaSt <;> assumption)

end
end
