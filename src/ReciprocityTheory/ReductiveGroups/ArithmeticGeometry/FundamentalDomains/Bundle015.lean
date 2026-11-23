module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma herm_add_right' (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, HermitianPairingAlgebra.cc_add, mul_add, Finset.sum_add_distrib]

lemma herm_sum_left' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) : herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianPairingAlgebra.herm_add_left, ih]

lemma herm_sum_right' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) : herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm, cc]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right', ih]

def hxi (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x ξ
  map_add' x y := HermitianTraceFormVanishing.herm_add_left G x y ξ
  map_smul' a x := HermitianTraceFormVanishing.herm_smul_left G a x ξ

theorem exists_beta (X : Data E r) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0) :
    ∃ β : Fin (r - 2) → Fin r → E, (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 →
        ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) := by
  classical
  set f := hxi X.Gm ξ with hf
  have hfx : ∀ x, f x = herm X.Gm x ξ := fun _ => rfl

  have hw : (fun b => cc (ξ b)) ≠ 0 := by
    intro h
    apply hξ0
    funext b
    have hb := congrFun h b
    simp only [Pi.zero_apply, cc] at hb
    simpa using hb
  obtain ⟨a, ha⟩ : ∃ a, (X.Gm *ᵥ fun b => cc (ξ b)) a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det (funext h))
  have hfa : f (Pi.single a 1) ≠ 0 := by
    rw [hfx]
    convert ha using 1
    simp [herm, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsurj : Function.Surjective f := fun y =>
    ⟨(y / f (Pi.single a 1)) • Pi.single a 1, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa]⟩
  set K := LinearMap.ker f with hK
  have hξK : ξ ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hξξ
  have hrange : Module.finrank E (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hKr : Module.finrank E K = r - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, Module.finrank_fin_fun] at this
    have h2 : 1 + Module.finrank E K = r := this
    omega
  have hKpos : 0 < Module.finrank E K := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    apply hξ0
    have : ξ ∈ (⊥ : Submodule E (Fin r → E)) := h ▸ hξK
    simpa using this
  have hr2 : 2 ≤ r := by omega
  set ξK : K := ⟨ξ, hξK⟩ with hξKdef
  have hξK0 : ξK ≠ 0 := fun h => hξ0 (congrArg Subtype.val h)
  set S : Submodule E K := E ∙ ξK with hS
  have hQ : Module.finrank E (K ⧸ S) = r - 2 := by
    have h0 := Submodule.finrank_quotient_add_finrank S
    have h1 : Module.finrank E S = 1 := by rw [hS]; exact finrank_span_singleton hξK0
    rw [h1, hKr] at h0
    have h2 : Module.finrank E (K ⧸ S) + 1 = r - 1 := h0
    omega
  let bQ := Module.finBasisOfFinrankEq E (K ⧸ S) hQ
  let βK : Fin (r - 2) → K := fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose
  have hβK : ∀ k, Submodule.Quotient.mk (p := S) (βK k) = bQ k := fun k =>
    (Submodule.Quotient.mk_surjective S (bQ k)).choose_spec
  have hdecK : ∀ y : K, ∃ (c : Fin (r - 2) → E) (e : E), y = ∑ k, c k • βK k + e • ξK := by
    intro y
    set c := bQ.repr (Submodule.Quotient.mk y) with hc
    refine ⟨c, ?_⟩
    have hmk : Submodule.Quotient.mk (p := S) (∑ k, c k • βK k) = ∑ k, c k • bQ k := by
      have h := map_sum S.mkQ (fun k => c k • βK k) Finset.univ
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hβK] at h
      exact h
    have hq : Submodule.Quotient.mk (p := S) y = Submodule.Quotient.mk (∑ k, c k • βK k) := by
      rw [hmk, hc, bQ.sum_repr]
    rw [Submodule.Quotient.eq] at hq
    have hq' : y - ∑ k, c k • βK k ∈ E ∙ ξK := hq
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hq'
    exact ⟨e, by rw [he]; abel⟩
  refine ⟨fun k => (βK k : Fin r → E), fun k => (βK k).2, ?_, ?_⟩
  · have hspan : ⊤ ≤ Submodule.span E (Set.range (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) := by
      intro y _
      obtain ⟨c, e, rfl⟩ := hdecK y
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span ⟨k.succ, by simp⟩
      · exact Submodule.subset_span ⟨0, by simp⟩
    have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_fin, hKr]; omega)
    have hmap := hli.map' K.subtype (Submodule.ker_subtype K)
    have heq : (K.subtype ∘ (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) =
        (Fin.cons ξ (fun k => (βK k : Fin r → E)) : Fin (r - 2 + 1) → Fin r → E) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [ξK]
    exact heq ▸ hmap
  · intro x hx
    have hxK : x ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hx
    obtain ⟨c, e, he⟩ := hdecK ⟨x, hxK⟩
    refine ⟨c, e, ?_⟩
    have := congrArg Subtype.val he
    simpa [ξK] using this

variable (X : DataX E r)

def LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {c | ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L'}
  add_mem' := by
    rintro c c' ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨e + e', ?_⟩
    have h : ∑ k, (c + c') k • β k + (e + e') • ξ =
        (∑ k, c k • β k + e • ξ) + (∑ k, c' k • β k + e' • ξ) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
    rw [h]
    exact X.L'.add_mem he he'
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨e, he⟩
    refine ⟨(a : E) * e, ?_⟩
    have h : ∑ k, (a • c) k • β k + ((a : E) * e) • ξ = a • (∑ k, c k • β k + e • ξ) := by
      rw [integer_smul_eq_coe_smul a c, integer_smul_eq_coe_smul a (∑ k, c k • β k + e • ξ)]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]
    rw [h]
    exact X.L'.smul_mem a he

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem minors_iff {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    (∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re) ↔
      0 < 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have hG := MajorantFamilyNorms.hG_of X τ
  have hdet : (mat x τ).det ≠ 0 := (hx τ).1
  have hsg := MajorantFamilyNorms.hsg_of X hx τ
  have he0 := (he τ).1
  have key : ∀ i : Fin (r + 1), (dmin X.Gm (X.flowV e s x) τ i).re =
      (dmin X.Gm x τ i).re * (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i) := by
    intro i
    rw [MajorantFamilyNorms.dmin_eq X (X.flowV e s x), MajorantFamilyNorms.dmin_flow X hx e τ he0 s,
      ← MajorantFamilyNorms.dmin_eq X x, Complex.re_mul_ofReal]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := (hx τ).2
  have hb := fun (i : ℕ) (hi : i ≤ r) =>
    mN_bounds hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 i hi
  have hmp := mN_pos hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 (he τ).2
  constructor
  · intro h
    have h0 := h ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    rw [key, ← mul_assoc] at h0
    exact pos_of_mul_pos_right h0 (hpos _).le
  · intro h i
    rw [key, ← mul_assoc]
    refine mul_pos (hpos i) ?_
    obtain ⟨h0, h1⟩ := hb i (Nat.le_of_lt_succ i.isLt)
    rcases le_or_gt 0 (2 * X.c τ * (s τ).im) with hk | hk
    · nlinarith [mul_nonneg hk h0]
    · nlinarith [mul_le_mul_of_nonpos_left h1 hk.le]

theorem flowDomainCriterion_holds : FlowDomainCriterion (E := E) := by
  intro r X e he x hx s
  have hmp : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (MajorantFamilyNorms.hsg_of X hx τ) (e τ)
      (he τ).1 (he τ).2
  have hm : ∀ τ, 1 + (s τ).im / X.ttV e x τ =
      1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
    intro τ
    rw [Data.ttV, MajorantFamilyNorms.maj_eq X hx e τ (he τ).1, one_div, div_inv_eq_mul]
    ring
  have hdom : X.flowV e s x ∈ X.dom ↔
      ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re := by
    constructor
    · intro h τ
      exact (h τ).2
    · intro h τ
      refine ⟨?_, h τ⟩
      show (X.flowMatV (e τ) τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, MajorantFamilyNorms.det_flowMat X (e τ) τ (s τ) (he τ).1, one_mul]
      exact (hx τ).1
  refine ⟨?_, ?_⟩
  · rw [hdom]
    refine forall_congr' fun τ => ?_
    rw [hm τ]
    exact minors_iff X e he hx s τ
  · intro hf τ
    have hpos := (minors_iff X e he hx s τ).1 (hdom.1 hf τ)
    have hc := MajorantFamilyNorms.c_pos X τ
    have hm0 := hmp τ
    simp only [Data.ttV]
    rw [MajorantFamilyNorms.maj_flow X hx e τ (he τ).1 s hpos.ne', MajorantFamilyNorms.maj_eq X hx e τ (he τ).1]
    field_simp

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Lattice

variable (X : Data E r) (la : Wt X.Ψ r)

noncomputable def perB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (perL X la)) ℝ (X.Ψ → ℝ) :=
  (Module.Free.chooseBasis ℤ (perL X la)).ofZLatticeBasis ℝ (perL X la)

theorem perB_span : (Submodule.span ℤ (Set.range (perB X la))).toAddSubgroup = X.periods la := by
  rw [perB, Module.Basis.ofZLatticeBasis_span]
  rfl

instance periods_countable : Countable (X.periods la) := inferInstanceAs (Countable (perL X la))

theorem fd_exists : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧
    IsAddFundamentalDomain (X.periods la) D volume ∧ 0 < volume D ∧ volume D < ⊤ := by
  refine ⟨ZSpan.fundamentalDomain (perB X la), ZSpan.fundamentalDomain_measurableSet _, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain (perB X la) volume
    rw [← perB_span X la]
    exact h
  · exact pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero _)
  · exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

theorem compact_reps : ∃ K : Set (X.Ψ → ℝ), IsCompact K ∧ ∀ s, ∃ p ∈ X.periods la, s - p ∈ K := by
  refine ⟨closure (ZSpan.fundamentalDomain (perB X la)),
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure, fun s => ?_⟩
  refine ⟨(ZSpan.floor (perB X la) s : X.Ψ → ℝ), ?_, subset_closure ?_⟩
  · rw [← perB_span X la]
    exact (ZSpan.floor (perB X la) s).prop
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _

end Lattice

section Glue

variable (X : Data E r) (u : Fin 2 → Fin r → E)

def e00 (s : X.Ψ → ℝ) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => if i = 0 ∧ k = 0 then (s τ : ℂ) else 0

theorem diag_unit_family_hermitian (s : X.Ψ → ℝ) : IsHermFam (e00 X s) := by
  intro τ i k
  unfold e00
  by_cases h : i = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬ (k = 0 ∧ i = 0) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem flow_eq_Zb (s : X.Ψ → ℝ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) y = X.Zb u (e00 X s) y := by
  funext τ
  simp only [Data.flow, Data.Zb]
  congr 1
  ext a j
  simp [Data.flowMat, Data.zmat, e00, Fin.sum_univ_two, Data.emb, cR]
  ring

theorem real_pairing_diag_unit (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (s : X.Ψ → ℝ) :
    X.pairR χ (e00 X s) = ∑ τ, (χ τ 0 0).re * s τ := by
  simp [Data.pairR, e00, Fin.sum_univ_two, Complex.re_sum]

theorem flow_Zb_comm (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) (s : X.Ψ → ℝ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) (X.Zb u b y) = X.Zb u b (X.flow (u 0) (cR X s) y) := by
  funext τ
  obtain ⟨W, hW⟩ : ∃ W : Fin 2 → Fin r → ℂ,
      W = fun k j => ∑ l, τ.1 (X.Gm j l) * conj (τ.1 (u k l)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Fin 2 → Fin r → ℂ, V = fun i a => τ.1 (u i a) := ⟨_, rfl⟩

  have hk : ∀ i k : Fin 2, ∑ j, W k j * V i j = 0 := by
    intro i k
    have h := congrArg τ.1 (hu i k)

    simp only [herm, map_sum, map_mul, emb_cc, map_zero] at h
    rw [← h, hW, hV]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  set α : ℂ := I * X.c τ * cR X s τ
  set γ : ℂ := I * X.c τ
  let A : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => α * V 0 a * W 0 j
  let B : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => γ * ∑ i, ∑ k, b τ i k * V i a * W k j
  have hF : X.flowMat (u 0) τ (cR X s τ) = 1 - A := by
    ext a j
    simp only [Data.flowMat, A, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, α]
  have hZ : X.zmat u b τ = 1 - B := by
    ext a j
    simp only [Data.zmat, B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, γ,
      Data.emb]
  have hAB : A * B = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, α * V 0 a * W 0 m * (γ * ∑ i, ∑ k, b τ i k * V i m * W k j)
        = ∑ i, ∑ k, (α * V 0 a * γ * b τ i k * W k j) * ∑ m, W 0 m * V i m := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have hBA : B * A = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, γ * (∑ i, ∑ k, b τ i k * V i a * W k m) * (α * V 0 m * W 0 j)
        = ∑ i, ∑ k, (γ * b τ i k * V i a * α * W 0 j) * ∑ m, W k m * V 0 m := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have key : X.flowMat (u 0) τ (cR X s τ) * X.zmat u b τ =
      X.zmat u b τ * X.flowMat (u 0) τ (cR X s τ) := by
    rw [hF, hZ]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hAB, hBA]
    abel
  show X.flowMat (u 0) τ (cR X s τ) * (X.zmat u b τ * mat y τ) =
    X.zmat u b τ * (X.flowMat (u 0) τ (cR X s τ) * mat y τ)
  rw [← Matrix.mul_assoc, key, Matrix.mul_assoc]

theorem Zb_cont (y : Frame X.Ψ r) : Continuous fun b : X.Ψ → Fin 2 → Fin 2 → ℂ => X.Zb u b y := by
  refine continuous_pi fun τ => ?_
  simp only [Data.Zb, Data.zmat]
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end Glue

end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
end
