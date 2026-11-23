module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
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
import Mathlib.NumberTheory.Harmonic.Bounds
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.SemistableReduction.Bundle014
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SplitCoord

theorem map_spec {F E K : Type} [CommRing F] [CommRing E] [CommRing K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] {D N : ℕ} (s : Fin D → Fin N → E) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    map (algebraMap E K) (spec s f) = spec (fun i j => algebraMap E K (s i j)) f := by
  unfold spec
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X]
    congr 1
    obtain ⟨a, b⟩ := i
    refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [join]

theorem map_lin_smul {E K : Type} [CommRing E] [CommRing K] (φ : E →+* K) {N : ℕ} (c : E) (y : Fin N → E) :
    map φ (lin (c • y)) = C (φ c) * lin fun j => φ (y j) := by

  simp only [lin, map_sum, map_mul, map_X, map_C, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_eq_C_mul {E K σ : Type} [Field E] [Field K] (φ : E →+* K) {P Q : MvPolynomial σ E} (hP : P ≠ 0) {c : K}
    (hc : c ≠ 0) (h : map φ Q = C c * map φ P) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * P := by
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hP
  have e : φ (AddMonoidAlgebra.coeff Q m) = c * φ (AddMonoidAlgebra.coeff P m) := by
    simpa only [coeff_map, coeff_C_mul] using congrArg (AddMonoidAlgebra.coeff · m) h
  have e' : φ (AddMonoidAlgebra.coeff Q m / AddMonoidAlgebra.coeff P m) = c := by
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero φ).2 hm)]
  refine ⟨AddMonoidAlgebra.coeff Q m / AddMonoidAlgebra.coeff P m, fun h0 => hc (by rw [← e', h0, map_zero]), map_injective φ φ.injective ?_⟩
  rw [map_mul, map_C, e', h]

theorem exists_eq_C_mul_prod {E K ι : Type} [Field E] [Field K] [Fintype ι] (φ : E →+* K) {N : ℕ}
    {Q : MvPolynomial (Fin 1 × Fin N) E} {y v : ι → Fin N → E} {z : ι → Fin N → K} {a : ι → E} (hy : ∀ p, y p ≠ 0)
    (ha : ∀ p, a p ≠ 0) (ea : ∀ p, y p = a p • v p) (hz : ∀ p, z p = fun j => φ (v p j)) {c : K} (hc : c ≠ 0)
    (h : map φ Q = C c * ∏ p, lin (z p)) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * ∏ p, lin (y p) := by
  have hA : (∏ p, φ (a p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => (map_ne_zero _).2 (ha p)
  refine exists_eq_C_mul φ (Finset.prod_ne_zero_iff.2 fun p _ => Check.lin_ne (hy p)) (div_ne_zero hc hA) ?_
  rw [h, map_prod]
  simp only [ea, hz, map_lin_smul]
  rw [Finset.prod_mul_distrib, ← map_prod C, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hA]

theorem exists_coord_spec_eq : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin G.D → Fin G.N → E) (hs : (G.baseChange E).IsGood s) (δ : ℕ) (f : MvPolynomial (Fin (G.D + 1) × Fin G.N) F), Split G.toTuple E s → SimpleAt G.toTuple δ f E s → ∃ (Co : Coord (G.baseChange E) hs δ) (c : E), c ≠ 0 ∧ spec s f = C c * ∏ p, lin (Co.y p) := by
  intro F _ _ G E _ _ _ s hs δ f h hS
  obtain rfl := hS.card
  obtain ⟨x, Co, hCo, -⟩ := h.exists_coord hs
  obtain ⟨c, hc, e⟩ := hS.fac
  choose a ha ea using fun p => G.exists_coords_baseChange E (x p).pt.1
  have h₅ (p) : G.coords (LinSys.toBase (RatPt.geomPt G E s (x p))).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords ((x p).pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  have h₇ : ∏ᶠ z ∈ G.geomPts E (G.linSection E s), lin (G.coords (LinSys.toBase z : G.Pt (AlgebraicClosure E)).1) =
      ∏ p, lin (G.coords (LinSys.toBase (RatPt.geomPt G E s (x p)) : G.Pt (AlgebraicClosure E)).1) := by
    refine (finprod_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
    rw [finprod_mem_range (RatPt.geomPt_injective hs), ← finprod_comp_equiv x, finprod_eq_prod_of_fintype]
  obtain ⟨c₀, h₀, e₀⟩ := exists_eq_C_mul_prod (N := G.N) (algebraMap E (AlgebraicClosure E)) (Q := spec s f) (y := Co.y)
    (fun p h0 => (G.baseChange E).geom.alg.bpf.coords_ne_zero _ ((hCo p).2.1.symm.trans h0)) ha
    (fun p => (hCo p).2.1.trans (ea p)) h₅ hc ((map_spec s f).trans (e.trans (congrArg (C c * ·) h₇)))
  exact ⟨Co, c₀, h₀, e₀⟩

end GlobalTheory.HSShort.SplitCoord
end
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

theorem det_symbolBlock {E ι κ : Type} [Field E] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (w : κ → E) (e : ℕ) (r : κ → κ → E) :
    (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0).det =
      (∏ p, w p) ^ (e * Fintype.card ι) *
        (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0).det := by
  have h : (Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then w i.2 ^ e * r i'.2 i.2 else 0) =
      Matrix.diagonal (fun i : ι × κ => w i.2 ^ e) *
        Matrix.of fun (i i' : ι × κ) => if i.1 = i'.1 then r i'.2 i.2 else 0 := by
    ext i i'
    simp only [Matrix.of_apply, Matrix.diagonal_mul]
    split_ifs <;> simp
  rw [h, Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp only [Finset.prod_pow, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (Fintype.card ι)]

theorem det_rational_eq_pow : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → S.deepRank s ≤ (Finset.univ.filter fun k => (col k).j = S.D).card → ∃ γ : E, ∀ l : Fin S.N → E, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = γ * (∏ p, ∑ k, l k * Φ.y p k) ^ S.expo := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc col m ix hsh hrank
  classical
  obtain ⟨c', -, hev⟩ := GlobalTheory.T.hermitianMultiplicationFlat_columns_eval F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d b c hc
  have hsym := GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem F A S hS E A' (fun i k => algebraMap F E (s i k)) δ Φ d col m ix hsh
  obtain ⟨hfd, hfr, -⟩ := GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational F A S hS E A' s δ Φ
  obtain ⟨hcard, -, -⟩ := GlobalTheory.T.monomial_counts_degree_and_weighted_sum S.D S.T hS.one_le hS.le_T
  let v : (Fin S.N → E) → Fin d → A' := fun l k =>
    word Φ.mul (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) (Φ.ι (col k).x)
  let ω : A' [⋀^Fin d]→ₗ[E] E := (Matrix.detRowAlternating).compLinearMap (LinearMap.pi c')
  have hdet : ∀ l, aeval (join (fun i k => algebraMap F E (s i k)) l) (S.det c col) = ω (v l) := by
    intro l
    rw [Sys.det, AlgHom.map_det, AlternatingMap.compLinearMap_apply]
    change _ = Matrix.det (fun k i => c' i (v l k))
    rw [← Matrix.det_transpose]
    congr 1
    ext i k
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply]
    exact (hev (col i) (join (fun i k => algebraMap F E (s i k)) l)).2 k

  let ix' : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ) ↪ Fin d :=
    (Equiv.sigmaProdDistrib (fun a : Fin (S.T - S.D) => MonoDeg (Fin S.D) a) (Fin δ)).symm.toEmbedding.trans ix
  have hix' : ∀ q, ix' q = ix (⟨q.1, q.2.1⟩, q.2.2) := fun q => rfl

  have hind : ∀ l k, k ∉ Set.range ix → v l k = v 0 k := by
    intro l k hk
    have hL : (fun q j => join (fun i k => algebraMap F E (s i k)) l ((col k).β q, j)) = (fun q j => join (fun i k => algebraMap F E (s i k)) 0 ((col k).β q, j)) := by
      rcases hsh.rest k hk with ⟨-, hβ⟩ | hj
      · funext q j
        obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr (hβ q)
        rw [← hi]
        simp [join]
      · have ht : (col k).t = 0 := by have := (col k).add; omega
        funext q
        exact absurd q.isLt (by omega)
    show word Φ.mul _ _ = word Φ.mul _ _
    rw [hL]

  have hzq : ∀ q : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a × Fin δ),
      ∃ x : A', ∃ hx : x ∈ Φ.U q.1, Φ.sym q.1 ⟨x, hx⟩ = Pi.single q.2 1 := by
    rintro ⟨a, α, p⟩
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp (Φ.y_ne p)
    have hk₀' : Φ.y p k₀ ≠ 0 := hk₀
    have ht : Φ.y p k₀ ^ (S.T - (a : ℕ)) ≠ 0 := pow_ne_zero _ hk₀'
    have hmem : (Pi.single p (Φ.y p k₀ ^ (S.T - (a : ℕ)))⁻¹ : Fin δ → E) ∈
        (Submodule.span E (Φ.ι '' S.V 0)).map Φ.res := by
      rw [Φ.onto]; exact Submodule.mem_top
    obtain ⟨m₀, hm₀, hres⟩ := hmem
    obtain ⟨h, hh⟩ := Φ.mono a a.2 α (fun _ => Pi.single k₀ 1) m₀ hm₀
    refine ⟨_, h, ?_⟩
    funext i
    obtain ⟨α', p'⟩ := i
    rw [hh, hres]
    by_cases hp : p' = p
    · rw [hp]
      by_cases hα : α' = α
      · rw [hα]
        simp [Finset.prod_const, Pi.single_apply, ht]
      · have hα' : α'.1 ≠ α.1 := fun e => hα (Subtype.ext e)
        simp [hα', hα]
    · simp [hp, Pi.single_apply]
  choose zq hzqU hzqS using hzq
  let z : Fin d → A' := Function.extend ix' zq (v 0)
  have hz_ix : ∀ q, z (ix' q) = zq q := fun q => ix'.injective.extend_apply zq (v 0) q
  have hz : ∀ q, z (ix' q) ∈ Φ.U q.1 := fun q => (hz_ix q).symm ▸ hzqU q
  have hzs : ∀ q, Φ.sym q.1 ⟨z (ix' q), hz q⟩ = Pi.single q.2 1 := by
    intro q
    have e : (⟨z (ix' q), hz q⟩ : Φ.U q.1) = ⟨zq q, hzqU q⟩ := Subtype.ext (hz_ix q)
    rw [e]; exact hzqS q
  have hzout : ∀ l k, k ∉ Set.range ix' → z k = v l k := by
    intro l k hk
    show Function.extend ix' zq (v 0) k = _
    rw [Function.extend_apply' _ _ _ hk]
    have hk' : k ∉ Set.range ix := by
      rintro ⟨q, rfl⟩; exact hk ⟨(Equiv.sigmaProdDistrib _ _) q, rfl⟩
    exact (hind l k hk').symm

  let J : Finset (Fin d) := Finset.univ.filter fun k => (col k).j = S.D
  have hnotix : ∀ k, (col k).j = S.D → k ∉ Set.range ix := by
    rintro k hk ⟨q, rfl⟩
    have := hsh.x_j q
    have := hS.one_le
    omega
  have hv : ∀ l q, v l (ix' q) ∈ Φ.U q.1 := fun l q => ((hsym l).1 q.1 q.2.1 q.2.2).fst
  have hJ : ∀ l, ∀ k ∈ J, k ∉ Set.range ix' ∧ v l k ∈ Φ.U (S.T - S.D) := by
    intro l k hk
    have hk' : (col k).j = S.D := (Finset.mem_filter.mp hk).2
    refine ⟨?_, (hsym l).2 k (hnotix k hk') hk'⟩
    rintro ⟨q, hq⟩
    exact hnotix k hk' ⟨_, (hix' q).symm.trans hq⟩
  haveI := hfd
  have hrank' : Module.finrank E (Φ.U (S.T - S.D)) ≤ J.card := hfr ▸ hrank
  let B : ∀ a : Fin (S.T - S.D), Matrix (MonoDeg (Fin S.D) a × Fin δ) (MonoDeg (Fin S.D) a × Fin δ) E :=
    fun a => Matrix.of fun i i' => if i.1 = i'.1 then Φ.res (Φ.ι (m i'.2)) i.2 else 0
  have hexp : ∑ a : Fin (S.T - S.D), (S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a) = S.expo := by
    rw [Sys.expo, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.card_eq_fintype_card, hcard, mul_comm]
  refine ⟨(∏ a, (B a).det) * ω z, fun l => ?_⟩
  rw [hdet]
  have key := GlobalTheory.T.alternatingMap_det_filtration_with_symbols E A' (S.T - S.D) d (fun a => MonoDeg (Fin S.D) a × Fin δ) Φ.U (fun a => Φ.sym a)
    Φ.le (fun a x => Φ.ker a a.2 x) ix' J (v l) (hv l) (hJ l) hrank' z hz hzs (hzout l) ω
  rw [key]
  have hblock : ∀ a : Fin (S.T - S.D),
      (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i).det =
        (∏ p, ∑ k, l k * Φ.y p k) ^ ((S.T - (a : ℕ)) * Fintype.card (MonoDeg (Fin S.D) a)) * (B a).det := by
    intro a
    have hM : (Matrix.of fun i i' : MonoDeg (Fin S.D) a × Fin δ => Φ.sym a ⟨v l (ix' ⟨a, i'⟩), hv l ⟨a, i'⟩⟩ i) =
        Matrix.of fun (i i' : MonoDeg (Fin S.D) a × Fin δ) =>
          if i.1 = i'.1 then (∑ k, l k * Φ.y i.2 k) ^ (S.T - (a : ℕ)) * Φ.res (Φ.ι (m i'.2)) i.2 else 0 := by
      ext i i'
      refine (((hsym l).1 a i'.1 i'.2).snd i.1 i.2).trans ?_
      simp only [Matrix.of_apply, Subtype.val_inj]
    rw [hM, det_symbolBlock (ι := MonoDeg (Fin S.D) a) (fun p => ∑ k, l k * Φ.y p k) (S.T - (a : ℕ))
      (fun p' p => Φ.res (Φ.ι (m p')) p)]
  simp only [hblock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hexp]
  ring

end GlobalTheory.HSShort
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HtLowProof

theorem eval_blockScale_multi {B N : ℕ} {a : Fin B → ℕ} {h : MvPolynomial (Fin B × Fin N) ℂ}
    (hh : IsMultiHomogeneous a h) (r : Fin B → ℂ) (v : Fin B × Fin N → ℂ) :
    eval (fun q => r q.1 * v q) h = (∏ i, r i ^ a i) * eval v h := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hr : ∏ q : Fin B × Fin N, r q.1 ^ s q = ∏ i, r i ^ a i := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    show ∏ y, r i ^ s (i, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hh s hs i]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hr]
  ring

theorem frameNorm_sum_le {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : Fin n → ℂ) (u : Fin n → Fin N → ℂ)
    (Λ : ℝ) (hc : ∀ k, ‖c k‖ ≤ 1) (hu : ∀ k, frameNorm A (u k) ≤ Λ) :
    frameNorm A (∑ k, c k • u k) ≤ n * Λ := by
  let T : (Fin N → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap ∘ₗ A⁻¹.mulVecLin
  have hT : ∀ z, frameNorm A z = ‖T z‖ := fun z => by
    rw [frameNorm, EuclideanSpace.norm_eq]; rfl

  rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _k : Fin n, Λ := Finset.sum_le_sum fun k _ => by
        rw [map_smul, norm_smul, ← hT]
        exact (mul_le_of_le_one_left (GlobalTheory.MaxPoint.frameNorm_nonneg' _ _) (hc k)).trans (hu k)
    _ = n * Λ := by simp

theorem norm_eval_le {B N : ℕ} {a : Fin B → ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (hN : 0 < N)
    {h : MvPolynomial (Fin B × Fin N) ℂ} (hh : IsMultiHomogeneous a h) (R : ℝ) (hR : 0 ≤ R)
    (u : Fin B × Fin N → ℂ) (hu : ∀ i, frameNorm A (fun j => u (i, j)) ≤ R) :
    ‖eval u h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) + (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) *
      R ^ (∑ i, a i) := by
  set r : Fin B → ℝ := fun i => frameNorm A (fun j => u (i, j)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => GlobalTheory.MaxPoint.frameNorm_nonneg' _ _
  set e : Fin N → ℂ := A.mulVec (Pi.single ⟨0, hN⟩ 1) with he'
  have he : frameNorm A e = 1 := by
    rw [he', GlobalTheory.MaxPoint.frameNorm_mulVec hA]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N) (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  let p : Fin B × Fin N → ℂ := fun q => if r q.1 = 0 then e q.2 else ((r q.1)⁻¹ : ℂ) * u q
  have hp : ∀ i, frameNorm A (fun j => p (i, j)) = 1 := fun i => by
    by_cases h0 : r i = 0
    · have : (fun j => p (i, j)) = e := by funext j; simp [p, h0]
      rw [this, he]
    · have : (fun j => p (i, j)) = ((r i)⁻¹ : ℂ) • (fun j => u (i, j)) := by
        funext j; simp [p, h0]
      rw [this, GlobalTheory.MaxPoint.frameNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
      exact inv_mul_cancel₀ h0
  have hup : u = fun q => ((r q.1 : ℝ) : ℂ) * p q := by
    funext q
    by_cases h0 : r q.1 = 0
    · have hz : (fun j => u (q.1, j)) = 0 := GlobalTheory.MaxPoint.eq_zero_of_frameNorm_eq_zero hA h0
      have := congrFun hz q.2
      simp only [Pi.zero_apply] at this
      simp [h0, this]
    · simp only [p, if_neg h0]
      rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_mul]
  have hval : ‖eval u h‖ = (∏ i, r i ^ a i) * ‖eval p h‖ := by
    rw [hup, eval_blockScale_multi hh (fun i => ((r i : ℝ) : ℂ)) p, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
  have hprod : ∏ i, r i ^ a i ≤ R ^ (∑ i, a i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hr0 i) _) fun i _ => pow_le_pow_left₀ (hr0 i) (hu i) _
  rw [hval]
  by_cases hz : eval p h = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hR _)
  · have harch := GlobalTheory.T.log_eval_sub_le_blockSphereMean_multidegree B N a A h hA hh p hp hz
    have hle : ‖eval p h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) +
        (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 hz)]
      exact Real.exp_le_exp.2 (by linarith)
    rw [mul_comm]
    exact mul_le_mul hle hprod (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _) (Real.exp_pos _).le

theorem eval₂_linSubst {F : Type} [Field F] {B N n : ℕ} (s : F →+* ℂ) (w : Matrix (Fin N) (Fin n) F)
    (G : MvPolynomial (Fin B × Fin N) F) (z : Fin B × Fin n → ℂ) :
    eval₂ s z (linSubst w G) = eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k)) (MvPolynomial.map s G) := by
  have e : ((eval₂Hom s z).comp (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
      MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom) =
      (eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k))).comp (MvPolynomial.map s) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun q => ?_)

    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_sum, map_mul,
    coe_eval₂Hom, eval₂_C, eval₂_X, map_X, eval_X]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  exact RingHom.congr_fun e G

theorem htLow : HtLow := by
  intro F _ _ B N n w A Λ hL a G hG ha
  obtain ⟨P, hP⟩ := GlobalTheory.HeightUnique.exists_right_inv hL.spans
  have hk : linSubst w G ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hP hG
  have hNn : N ≤ n := by
    have h1 := finrank_range_le_card (R := F) w.col
    unfold Set.finrank at h1
    rw [hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hL.pos.trans_le hNn)
  have hnΛ : (0 : ℝ) < n * Λ := mul_pos (by linarith) (by linarith [hL.one_le])
  set deg : ℝ := ∑ b, (a b : ℝ) with hdeg
  set H : ℝ := (harmonic (N - 1) : ℝ) with hH
  set m : (F →+* ℂ) → ℝ := fun σ => blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ G)) with hm
  have key := GlobalTheory.HSFloor.floor F (Fin B × Fin n) (linSubst w G)
    (fun s => Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) hk (fun s z hz => by
      rw [eval₂_linSubst]
      refine norm_eval_le (hL.det s) hL.pos (isMultiHomogeneous_map_ring a G ha s) _ hnΛ.le _ fun i => ?_
      have e : (fun j => ∑ k, z (i, k) * s (w j k)) = ∑ k, z (i, k) • (fun j => s (w j k)) := by
        funext j; simp [Finset.sum_apply]
      rw [e]
      exact frameNorm_sum_le _ _ _ Λ (fun k => hz _) fun k => hL.le k s)
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    rw [NumberField.Embeddings.card]
  have hlog : ∀ s, Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) =
      m s + (deg * H / 2 + deg * Real.log (n * Λ)) := fun s => by
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hnΛ _).ne', Real.log_exp, Real.log_pow, hdeg]
    push_cast
    ring
  have hmean : mean F (fun s => Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b))) =
      mean F m + (deg * H / 2 + deg * Real.log (n * Λ)) := by
    simp only [hlog, mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hht : ht w A G = finPart (linSubst w G) + mean F m := by
    simp only [ht, formHeight, finPart, mean, hm]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hHle : H ≤ Real.log n + 1 := by
    have h1 : H ≤ 1 + Real.log ((N - 1 : ℕ) : ℝ) := by
      rw [hH]; exact_mod_cast harmonic_le_one_add_log (N - 1)
    have h2 : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (N - 1) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hn1
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : N - 1 ≤ n))
    linarith
  have hdeg0 : 0 ≤ deg := Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  rw [hmean] at key
  rw [hht, cst]
  nlinarith [mul_le_mul_of_nonneg_left hHle hdeg0]

end GlobalTheory.HtLowProof
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_realSubfield_negative_twoPlaces_normEverywhere : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : M →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (ε a).re < 0 ∧ (ε' a).re < 0 ∧ (∀ φ : M →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  first | (exact @GlobalTheory.NormSign.exists_neg_two_norm_away) | (exact GlobalTheory.NormSign.exists_neg_two_norm_away) | (intros; apply GlobalTheory.NormSign.exists_neg_two_norm_away <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem _root_.GlobalTheory.T.detFactorDepthInChart_chart_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch' X f k := by
  first | exact @GlobalTheory.FactorDepth.nuFacC_chart_indep | exact GlobalTheory.FactorDepth.nuFacC_chart_indep | (intros; apply GlobalTheory.FactorDepth.nuFacC_chart_indep <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.absHalf_blockDet_integralGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  first | exact @GlobalTheory.BCT.absHalf_blockDet_KGL_invariant | exact GlobalTheory.BCT.absHalf_blockDet_KGL_invariant | (intros; apply GlobalTheory.BCT.absHalf_blockDet_KGL_invariant <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsSplitAt w →
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w (n := n)) := by
  first | exact @GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | exact GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | (intros; apply GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level <;> assumption)
end
