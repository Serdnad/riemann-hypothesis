module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle058
public import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem adm6_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  intro D L P X C tf hC
  refine ⟨?_, ?_⟩
  · intro i hi π hπ
    have hk := ((hC.kill i hi).1 π hπ).2
    show (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + TwistedPlaces.epsL (D.nd.l i) ≤ _
    unfold TwistedPlaces.epsL at hk ⊢
    have : (2 : ℝ) / (D.nd.l i : ℝ) ^ 2 = 1 / (D.nd.l i : ℝ) ^ 2 + 1 / (D.nd.l i : ℝ) ^ 2 := by ring
    rw [this]
    linarith
  · intro j _ l _
    show TwistedPlaces.epsL l + TwistedPlaces.epsL l ≤ 2 / (l : ℝ) ^ 2
    unfold TwistedPlaces.epsL
    apply le_of_eq
    ring

end GlobalTheory.NLink
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowBSize

open Classical

theorem ratIn_lt {x y : ℝ} (h : x < y) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) < y := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_left h]
  exact (exists_rat_btwn h).choose_spec.2

theorem ratIn_of_not_lt {x y : ℝ} (h : ¬ x < y) : Formalism.MainNotions.N.ratIn x y = 0 := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_right h]

theorem x_pos' {D : D7} (L : SizeData₂ D) : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]

theorem one_le_b' {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem one_le_Lg {D : D7} (L : SizeData₂ D) : 1 ≤ Formalism.MainNotions.TwistedPlaces.large₂ L := by
  unfold Formalism.MainNotions.TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem hB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L := by
  unfold Formalism.MainNotions.TwistedPlaces.hB
  have := one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem GP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ Formalism.MainNotions.TwistedPlaces.GP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := x_pos' L
    have := one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := x_pos' L
    positivity
  unfold Formalism.MainNotions.TwistedPlaces.GP Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.eta₃ Formalism.MainNotions.TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h3 := L.Sc_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreB_pos {D : D7} (L : SizeData₂ D) {l : ℕ} (hl : 2 ≤ l) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreB L l lam := by
  unfold Formalism.MainNotions.N.coreB
  have hr : (0:ℝ) < D.R.r := by
    have : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hl1 : (0:ℝ) < (l : ℝ) - 1 := by
    have : (2:ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hh : 0 ≤ Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) := by
    exact div_nonneg (hB_nonneg L) (pow_nonneg hl1.le _)
  have hg : 0 ≤ (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) := by
    have := GP_nonneg L; positivity
  have hL := one_le_Lg L
  have hin : 0 < Formalism.MainNotions.TwistedPlaces.hB L / ((l : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L l + 1) +
      (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L l : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L := by linarith
  have hn : (0:ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  positivity

theorem lenRowB_le {D : D7} (L : SizeData₂ D) {C₂ C : ℝ} (hC : 3 * C₂ + 1 ≤ C) {l : ℕ} (hl : 2 ≤ l)
    (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    ((Formalism.MainNotions.N.lenRowB L C₂ l lam : ℚ) : ℝ) ≤ C * Formalism.MainNotions.N.coreB L l lam := by
  have hc := coreB_pos L hl lam
  unfold Formalism.MainNotions.N.lenRowB
  have hlt : 3 * C₂ * Formalism.MainNotions.N.coreB L l lam < (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam := by nlinarith
  have := ratIn_lt hlt
  have : (3 * C₂ + 1) * Formalism.MainNotions.N.coreB L l lam ≤ C * Formalism.MainNotions.N.coreB L l lam :=
    mul_le_mul_of_nonneg_right hC hc.le
  linarith

end GlobalTheory.NLink.RowBSize

theorem GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admB L (tabX L X) C := by
  intro D L P HW X R C hD hR
  intro i _ hrow lam _
  obtain ⟨hI, hA, hO, _⟩ := hrow
  have hl2 : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
  have hC1 : (1:ℝ) ≤ C := hR.2.2.2.2.1
  have hC3 : 3 * R.C₂ + 1 ≤ C := hR.2.2.2.2.2.1
  have hrowB := hD.rowB i hI ⟨hA, hO⟩
  have key : (tabX L X).len i lam = KillingConditions.supZ i (fun _ => ((Formalism.MainNotions.N.lenRowB L R.C₂ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hrowB]
  have hcore : C * ((TwistedPlaces.nLam D lam : ℝ) + 1) * D.R.r * (TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (TwistedPlaces.jA L (D.nd.l i) + 1) +
      (TwistedPlaces.GP L + 1) * ((TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + TwistedPlaces.large₂ L) = C * Formalism.MainNotions.N.coreB L (D.nd.l i) lam := by
    unfold Formalism.MainNotions.N.coreB; ring
  rw [key, hcore]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    exact GlobalTheory.NLink.RowBSize.lenRowB_le L hC3 hl2 lam
  · have := GlobalTheory.NLink.RowBSize.coreB_pos L hl2 lam
    positivity
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLinkMono

theorem mul_rpow_self_mono {x C C' : ℝ} (hx : 1 ≤ x) (h : C ≤ C') (h0 : 0 ≤ C') :
    C * x ^ C ≤ C' * x ^ C' := by
  have hxp : 0 < x := lt_of_lt_of_le one_pos hx
  rcases le_or_gt 0 C with hC | hC
  · exact mul_le_mul h (Real.rpow_le_rpow_of_exponent_le hx h) (Real.rpow_nonneg hxp.le _) h0
  · have : C * x ^ C ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (Real.rpow_nonneg hxp.le _)
    exact this.trans (mul_nonneg h0 (Real.rpow_nonneg hxp.le _))

theorem rpow_mono {x C C' : ℝ} (hx : 1 ≤ x) (h : C ≤ C') : x ^ C ≤ x ^ C' :=
  Real.rpow_le_rpow_of_exponent_le hx h

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C C' : ℝ), C ≤ C' → 0 ≤ C' → (StarF L X.ρ C → StarF L X.ρ C') ∧ (StarH L C → StarH L C') ∧ (KillingConditions.BBLe L X C → KillingConditions.BBLe L X C') ∧ (TwistedPlaces.ParametersPolynomiallyBounded L C P → TwistedPlaces.ParametersPolynomiallyBounded L C' P) := by
  intro D L P X C C' h h0
  have hx : 1 ≤ L.sc.x := L.sc.one_lt_alt.le
  have hxp : 0 < L.sc.x := lt_of_lt_of_le one_pos hx
  have hCx := mul_rpow_self_mono hx h h0
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hLg : 0 ≤ TwistedPlaces.large₂ L := Real.rpow_nonneg hxp.le _
  have he : 0 ≤ L.etaSz := L.etaSz_pos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨tf, hF, hB⟩
    refine ⟨tf, ?_, hB⟩
    intro i hi hl
    refine (hF i hi hl).trans ?_
    have h1 : C * (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x ≤
        C' * (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by
      have hk : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * Real.log L.sc.x := by positivity
      have := mul_le_mul_of_nonneg_right h hk
      simpa only [mul_assoc] using this
    have h2 : C * L.sc.x ^ C * TwistedPlaces.large₂ L ^ 2 ≤ C' * L.sc.x ^ C' * TwistedPlaces.large₂ L ^ 2 :=
      mul_le_mul_of_nonneg_right hCx (sq_nonneg _)
    linarith
  · intro hH j hj l hl
    refine (hH j hj l hl).trans ?_
    have hk : 0 ≤ Real.log l * (L.dZ0 j : ℝ) :=
      mul_nonneg (Real.log_natCast_nonneg l) (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hk
    have := mul_le_mul_of_nonneg_right hCx he
    linarith
  · intro hB i hi hg hr π hπ
    refine (hB i hi hg hr π hπ).trans ?_
    have hk : 0 ≤ (D.R.f : ℝ) * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h hk
    simpa only [mul_assoc] using this
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hr := rpow_mono hx h
    refine ⟨h1.trans h, h2.trans h, h3.trans hr, h4.trans hr, h5.trans hr, h6, h7.trans hCx, h8.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hCx hLg

end GlobalTheory.NLinkMono
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.Adm4Tab

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty :=
  by apply _root_.UpperTheory.Reformulated.B.Qk8.exists_place <;> assumption

theorem sumOver_const (D : D7) (l : ℕ) (hl : l ≠ 0) (k : ℝ) :
    TwistedPlaces.sumOver D l (fun _ => k) = ((placesOver D.host.E l).ncard : ℝ) * k := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.sum_const, Set.ncard_eq_toFinset_card _ hf,
    nsmul_eq_mul]

theorem sumOver_mono (D : D7) (l : ℕ) (hl : l ≠ 0) {f g : HeightOneSpectrum (𝓞 D.host.E) → ℝ}
    (h : ∀ lam, f lam ≤ g lam) : TwistedPlaces.sumOver D l f ≤ TwistedPlaces.sumOver D l g := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  exact Finset.sum_le_sum fun lam _ => h lam

theorem le_supZ {D : D7} (i : D.nd.Loc) (f : D.nd.X i → ℝ) {π : D.nd.X i} (hπ : π ∈ D.nd.Zgood i) :
    f π ≤ KillingConditions.supZ i f := by
  unfold KillingConditions.supZ
  rw [dite_eq_left ⟨π, hπ⟩]
  exact Finset.le_sup' f hπ

end GlobalTheory.NLink.Adm4Tab


open GlobalTheory.NLink.Adm4Tab in
theorem GlobalTheory.NLink.admissible_table_of_conclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i,
      Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  intro D L P X C tf hC h23 i hi hg π hπ
  have key : ∀ b, Bd X.ρ i π b → b ≤ TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i →
      (D.nd.vcc i π : ℝ) ≤ (tab L X tf C).s i π + TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + (tab L X tf C).BB i + TwistedPlaces.epsL (D.nd.l i) := by
    intro b hb hle
    unfold Bd at hb
    have hs : (tab L X tf C).s i π = (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) := rfl
    rw [hs]
    linarith
  have hl0 : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hq3 : D.host.q ≠ 3 := D.host.q_ne_three
  have hd3 : D.host.d ≠ 3 := by have := D.host.hyp.2.2.2.1; omega
  have hzero : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
    rw [sumOver_const D _ hl0, mul_zero]
  by_cases h2 : D.nd.l i ∈ D.host.small
  · apply key _ (h23 i hi (Or.inl h2) π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    rw [hlen, hzero, hBB, zero_add]
  by_cases h3 : D.nd.l i = 3
  · apply key _ (h23 i hi (Or.inr h3) π hπ)
    have hBB : (tab L X tf C).BB i = 0 := by
      have hq : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by
        rw [h3]; rintro (h | h) <;> [exact hq3 h.symm; exact hd3 h.symm]
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg hq, if_neg hR]
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    rw [hBB, hlen, h3, sumOver_const D 3 (by norm_num)]
    have hf3 := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
    have hpos : 0 < (placesOver D.host.E 3).ncard :=
      (Set.ncard_pos hf3).2 (placesOver_nonempty D.host.E 3 Nat.prime_three)
    have hpos' : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_div_cancel₀ _ hpos', add_zero]
  by_cases hqd : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d
  · apply key _ (hC.ram i hi hqd π hπ)
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hqd
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, if_neg h2, if_pos hqd]
    rw [hlen, hzero, hBB, zero_add]
  by_cases hR : KillingConditions.RangeAD L X.exc (D.nd.l i)
  · have hm := hC.mid i hi hg hR π hπ
    have hb : Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) + X.errorBoundHub i π) := by
      unfold Bd
      linarith
    apply key _ hb
    have hlen : (tab L X tf C).len i = KillingConditions.lenR X.len0 i := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_pos hR]
    have hBB : (tab L X tf C).BB i = KillingConditions.supZ i (X.errorBoundHub i) := by
      simp only [tab, if_neg h2, if_neg hqd, if_pos hR]
    rw [hlen, hBB]
    have h1 : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) ≤ TwistedPlaces.sumOver D (D.nd.l i) (KillingConditions.lenR X.len0 i) :=
      sumOver_mono D _ hl0 fun lam => le_supZ i (fun π => X.len0 i π lam) hπ
    have h2' : X.errorBoundHub i π ≤ KillingConditions.supZ i (X.errorBoundHub i) := le_supZ i (X.errorBoundHub i) hπ
    linarith
  · have hlt : TwistedPlaces.lStar L < (D.nd.l i : ℝ) ∧ D.nd.l i ∉ X.exc := by
      by_contra hc
      exact hR ⟨fun h => h.elim h2 h3, hqd, hc⟩
    apply key _ (hC.large i hi hlt.1 hg hlt.2 π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = 0 := by
      simp only [tab, if_neg h2, if_neg hqd, if_neg hR]
    rw [hlen, hzero, hBB, add_zero]

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowA

theorem two_eA_le {D : D7} (L : SizeData₂ D) {CA C : ℝ} (hCA : 0 ≤ CA) (hC : 2 * (3 * CA + 1) ≤ C)
    {l : ℕ} (hl : 5 ≤ l) : 2 * (eA L CA l : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eP L C l := by
  have h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L := Formalism.MainNotions.TwistedPlaces.one_le_hB L
  set h := Formalism.MainNotions.TwistedPlaces.hB L with hh
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  set a : ℝ := ((hN L : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have haN : a ≤ h := Nat.floor_le (by linarith)
  have hlog1 : 0 ≤ Real.logb l (a + a + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlh : 0 ≤ Real.logb l h := Real.logb_nonneg hl1 h1
  have hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h := by
    have hle : a + a + 1 ≤ l * h := by nlinarith
    calc Real.logb l (a + a + 1) ≤ Real.logb l (l * h) :=
          Real.logb_le_logb_of_le hl1 (by linarith) hle
      _ = 1 + Real.logb l h := by
          rw [Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]
  have hdiv : (a + a) / l ≤ 2 * (h / l) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl0.le
  have hhl : 0 ≤ h / l := div_nonneg (by linarith) hl0.le
  have hY : 1 ≤ 1 + h / l + Real.logb l h := by linarith
  have hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h) := by
    linarith
  have hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) := by
    apply mul_nonneg hCA
    have : 0 ≤ (a + a) / l := div_nonneg (by linarith) hl0.le
    linarith
  have hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1 := by
    unfold eA
    push_cast
    exact Nat.ceil_lt_add_one hnn
  have harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤
      CA * (3 * (1 + h / l + Real.logb l h)) := mul_le_mul_of_nonneg_left hin hCA
  have hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h) := by nlinarith
  unfold Formalism.MainNotions.TwistedPlaces.eP
  rw [← hh]
  nlinarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admA L (tabX L X) C := by
  intro D L P HW X R C hD hR i _htw hcond
  obtain ⟨h5, hsp, _, _⟩ := hcond
  obtain ⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩ := hR
  have hl0 : D.nd.l i ≠ 0 := by omega
  have hfin := FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0
  have he := two_eA_le L hCA hCC h5
  have heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i) := Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lam _
  have hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1 := by positivity
  have hconst : (fun π => X.len0 i π lam) =
      fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ) := by
    funext π
    rw [hD.len0S i hsp π lam, hD.eS i hsp]
  show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _
  rw [hconst]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenA
    split_ifs
    · push_cast
      have : (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ) := rfl
      rw [← this]
      nlinarith
    · push_cast; nlinarith
  · nlinarith

end GlobalTheory.NLink.RowA
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation (GlobalTheory.T.weilRepresentationEtale_of_quadraticField h) GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer GlobalTheory.T.weilConstantStandardHermitian_eq_one

end GlobalTheory.JR
end
