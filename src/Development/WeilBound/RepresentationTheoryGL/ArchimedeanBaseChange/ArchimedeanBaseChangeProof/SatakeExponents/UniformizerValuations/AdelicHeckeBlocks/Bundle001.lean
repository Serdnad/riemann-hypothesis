module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.GlobalTheory
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Word

theorem wdVal_append {A Γ : Type} [Monoid A] [Star A] (gen : Γ → A) (u v : List (Γ × Bool)) :
    wdVal gen (u ++ v) = wdVal gen u * wdVal gen v := by
  simp [wdVal, List.map_append, List.prod_append]

theorem wdVal_star {A Γ : Type} [Monoid A] [StarMul A] (gen : Γ → A) (w : List (Γ × Bool)) :
    star (wdVal gen w) = wdVal gen (w.map fun p => (p.1, !p.2)).reverse := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    have e : wdVal gen (p :: w) = (if p.2 then star (gen p.1) else gen p.1) * wdVal gen w := by
      simp [wdVal]
    rw [e, star_mul, ih, List.map_cons, List.reverse_cons, wdVal_append]
    congr 1
    obtain ⟨x, b⟩ := p
    cases b <;> simp [wdVal]

theorem pow_eq {A Γ J : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype J] (gen : Γ → A) (c : J → ℂ)
    (w : J → List (Γ × Bool)) (k : ℕ) :
    (∑ j, c j • wdVal gen (w j)) ^ k =
      ∑ f : Fin k → J, (∏ i, c (f i)) • wdVal gen (List.ofFn fun i => w (f i)).flatten := by
  induction k with
  | zero => simp [wdVal]
  | succ k ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum, ← (Fin.consEquiv fun _ => J).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.flatten_cons, wdVal_append, smul_mul_smul_comm]

end Word

theorem adjWords : AdjWords := by
  intro A Γ _ _ _ _ gen a ha
  suffices h : ∃ (J : Type) (_ : Fintype J) (c : J → ℂ) (w : J → List (Γ × Bool)) (L : ℕ),
      (∀ j, (w j).length ≤ L) ∧ a = ∑ j, c j • wdVal gen (w j) by
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := h
    exact ⟨J, inferInstance, c, w, L, hL, rfl, Word.pow_eq gen c w⟩
  induction ha using StarAlgebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨Unit, inferInstance, fun _ => 1, fun _ => [(i, false)], 1, fun _ => le_rfl, by simp [wdVal]⟩
  | algebraMap r =>
    exact ⟨Unit, inferInstance, fun _ => r, fun _ => [], 0, fun _ => le_rfl, by
      simp [wdVal, Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := hx
    obtain ⟨J', _, c', w', L', hL', rfl⟩ := hy
    refine ⟨J ⊕ J', inferInstance, Sum.elim c c', Sum.elim w w', max L L', ?_, ?_⟩
    · rintro (j | j)
      · exact (hL j).trans (le_max_left _ _)
      · exact (hL' j).trans (le_max_right _ _)
    · simp [Fintype.sum_sum_type]
  | mul x y _ _ hx hy =>
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := hx
    obtain ⟨J', _, c', w', L', hL', rfl⟩ := hy
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => w p.1 ++ w' p.2, L + L', ?_, ?_⟩
    · rintro ⟨j, j'⟩
      simpa using Nat.add_le_add (hL j) (hL' j')
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      dsimp only
      rw [smul_mul_smul_comm, Word.wdVal_append]
  | star x _ hx =>
    obtain ⟨J, _, c, w, L, hL, rfl⟩ := hx
    refine ⟨J, inferInstance, fun j => star (c j), fun j => ((w j).map fun p => (p.1, !p.2)).reverse, L, ?_, ?_⟩
    · intro j
      simpa using hL j
    · simp [star_sum, star_smul, Word.wdVal_star]

namespace Word

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E}

theorem sc_inl (c : ℂ) (w : List (BGen B)) : BGen.sc (Sum.inl c :: w) = c * BGen.sc w := by
  simp [BGen.sc]

theorem sc_inr (s : PT B) (w : List (BGen B)) : BGen.sc (Sum.inr s :: w) = BGen.sc w := by
  simp [BGen.sc]

end Word

theorem blkWord (h : BlockOperatorsProductAdjoint) : BlockWordOperators := by
  intro E _ _ _ B w t₀ R hw ht₀ hR hs
  have hadj : ∀ g : BGen B, g.Ok → g.adj.Ok ∧ g.adj.op = ContinuousLinearMap.adjoint g.op := by
    rintro (c | s) hg
    · refine ⟨trivial, ?_⟩
      show (starRingEnd ℂ c) • (1 : B.Hb →L[ℂ] B.Hb) = ContinuousLinearMap.adjoint (c • 1)
      rw [LinearIsometryEquiv.map_smulₛₗ]
      congr 1
      exact ContinuousLinearMap.adjoint_id.symm
    · exact ⟨(h E B s s hg hg).2.2.2.2.1, (h E B s s hg hg).2.2.2.2.2.1⟩
  suffices main : (BGen.wd w t₀).Ok ∧ (w.map BGen.op).prod * t₀.op = BGen.sc w • (BGen.wd w t₀).op ∧
      (BGen.wd w t₀).T ≤ t₀.T + w.length * R ∧ (BGen.wd w t₀).r ≤ t₀.r + w.length * R ∧
      ∀ χa χb, (BGen.wd w t₀).val χa χb =
        (w.map (Sum.elim (fun _ => 1) fun s => s.val χa χb)).prod * t₀.val χa χb by
    obtain ⟨m1, m2, m3, m4, m5⟩ := main
    exact ⟨m1, m2, m3, m4, hadj, m5⟩
  induction w with
  | nil => simp [BGen.wd, BGen.sc, ht₀]
  | cons g w ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (fun g hg => hw g (List.mem_cons_of_mem _ hg))
      (fun s hs' => hs s (List.mem_cons_of_mem _ hs'))
    have hg := hw g List.mem_cons_self
    rcases g with c | s
    · have ew : BGen.wd (Sum.inl c :: w) t₀ = BGen.wd w t₀ := rfl
      rw [ew, Word.sc_inl]
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.prod_cons, mul_assoc, h2]
        show (c • (1 : B.Hb →L[ℂ] B.Hb)) * _ = _
        rw [smul_mul_assoc, one_mul, smul_smul]
      · simp only [List.length_cons]; push_cast; nlinarith
      · simp only [List.length_cons]; push_cast; nlinarith
      · intro χa χb
        simp [h5]
    · have ew : BGen.wd (Sum.inr s :: w) t₀ = s.mul (BGen.wd w t₀) := rfl
      have hsR := hs s List.mem_cons_self
      have hop := h E B s (BGen.wd w t₀) hg h1
      rw [ew, Word.sc_inr]
      refine ⟨hop.2.2.1, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.prod_cons, mul_assoc, h2, hop.2.2.2.1]
        show s.op * _ = _
        rw [mul_smul_comm]
      · show s.T + (BGen.wd w t₀).T ≤ _
        simp only [List.length_cons]; push_cast; linarith [hsR.1]
      · show s.r + (BGen.wd w t₀).r + B.c ≤ _
        simp only [List.length_cons]; push_cast; linarith [hsR.2]
      · intro χa χb
        rw [hop.2.2.2.2.2.2.1, h5]
        simp [mul_assoc]

end PositivityTheory.Rg.BcB.F

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Op

theorem bsG (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

theorem bsF (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] bsG bsF

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem logSize_inv {n : ℕ} (g : GA E n) : logSize g⁻¹ = logSize g := by
  rw [logSize, logSize, inv_inv, add_comm]

theorem adjVal_spec (h2 : MultAlg) {n : ℕ} (μ : Measure (G n)) [μ.IsHaarMeasure] {M : Mods E n} (k : Kers M)
    (val : InfinitePlace E → Inf n → ℂ) (T : ℝ) (v : InfinitePlace E) (hk : IsMult μ (M v) (k v) (val v) T) :
    IsMult μ (M v) (adjK k v) (adjVal μ k val T v) T ∧
      ∀ χ, IsHerm χ → adjVal μ k val T v χ = starRingEnd ℂ (val v χ) := by
  have hex : ∃ val₁, IsMult μ (M v) (adjK k v) val₁ T ∧ ∀ χ, IsHerm χ → val₁ χ = starRingEnd ℂ (val v χ) := by
    obtain ⟨-, -, h, -⟩ := h2 n μ (M v) (k v) (k v) (val v) (val v) T T hk hk
    exact h
  have e : adjVal μ k val T v = hex.choose := dif_pos hex
  rw [e]
  exact hex.choose_spec

variable (B : Block E)

theorem opOf_eq (h1 : OpEx) {Φ : Matrix B.I B.I (H E B.a B.b → ℂ)} {T : B.Hb →L[ℂ] B.Hb} (hΦ : IsTestM Φ)
    (hT : IsROp B.D Φ T) : B.opOf Φ = T := by
  have hex : ∃ T, IsROp B.D Φ T := ⟨T, hT⟩
  have e : B.opOf Φ = hex.choose := dif_pos hex
  rw [e]
  exact ((h1 E B.a B.b B.D B.I).1 Φ hΦ).unique hex.choose_spec hT

theorem test (h3 : TensTest) (t : PT B) (ht : t.Ok) : IsTestM t.Φ := by
  haveI := B.ha; haveI := B.hb
  exact (h3 E B.a B.b B.μa B.μb B.Ma B.Mb B.κ t.ka t.kb t.va t.vb t.T t.ψ ht.ka ht.kb ht.ψ).1

theorem rop (h1 : OpEx) (h3 : TensTest) (t : PT B) (ht : t.Ok) : IsROp B.D t.Φ t.op := by
  have hex := ((h1 E B.a B.b B.D B.I).1 t.Φ (test B h3 t ht)).exists
  have e : B.opOf t.Φ = hex.choose := dif_pos hex
  show IsROp B.D t.Φ (B.opOf t.Φ)
  rw [e]
  exact hex.choose_spec

theorem mulOk (h2 : MultAlg) (h4 : TensMul) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok) : (t.mul t').Ok := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  refine ⟨add_nonneg ht.T ht'.T, add_nonneg (add_nonneg ht.r ht'.r) B.c_nonneg, fun v => ?_, fun v => ?_, ?_, ?_⟩
  · exact (h2 B.a B.μa (B.Ma v) (t.ka v) (t'.ka v) (t.va v) (t'.va v) t.T t'.T (ht.ka v) (ht'.ka v)).1
  · exact (h2 B.b B.μb (B.Mb v) (t.kb v) (t'.kb v) (t.vb v) (t'.vb v) t.T t'.T (ht.kb v) (ht'.kb v)).1
  · exact (h4 E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb t.T t'.T t.ψ t'.ψ
      B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ).1
  · intro x y g hg
    have hg' : ∑ z, ∫ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ∂B.ν ≠ 0 := hg
    obtain ⟨z, hz⟩ : ∃ z, ∫ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ∂B.ν ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hg' (Finset.sum_eq_zero fun z _ => hc z)
    obtain ⟨h, hh⟩ : ∃ h, t.ψ x z h * t'.ψ z y (h⁻¹ * g) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hz (by simp [hc])
    have s1 := ht.size x z h (left_ne_zero_of_mul hh)
    have s2 := ht'.size z y (h⁻¹ * g) (right_ne_zero_of_mul hh)
    have e1 : g.1 = h.1 * (h⁻¹ * g).1 := by rw [← Prod.fst_mul, mul_inv_cancel_left]
    have e2 : g.2 = h.2 * (h⁻¹ * g).2 := by rw [← Prod.snd_mul, mul_inv_cancel_left]
    show logSize (finGL E B.a g.1) ≤ t.r + t'.r + B.c ∧ logSize (finGL E B.b g.2) ≤ t.r + t'.r + B.c
    rw [e1, e2, map_mul, map_mul]
    constructor
    · linarith [B.ca (finGL E B.a h.1) (finGL E B.a (h⁻¹ * g).1), s1.1, s2.1]
    · linarith [B.cb (finGL E B.b h.2) (finGL E B.b (h⁻¹ * g).2), s1.2, s2.2]

theorem mulOp (h1 : OpEx) (h3 : TensTest) (h4 : TensMul) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok) :
    (t.mul t').op = t.op * t'.op := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  have hm := h4 E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb t.T t'.T t.ψ t'.ψ
      B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ
  have hΦ : (t.mul t').Φ = mulM B.D.μ t.Φ t'.Φ := hm.2.symm
  have h := (h1 E B.a B.b B.D B.I).2 t.Φ t'.Φ t.op t'.op (test B h3 t ht) (test B h3 t' ht') (rop B h1 h3 t ht)
    (rop B h1 h3 t' ht')
  show B.opOf (t.mul t').Φ = _
  rw [hΦ]
  exact opOf_eq B h1 h.1 h.2.1

theorem adjOk (h2 : MultAlg) (t : PT B) (ht : t.Ok) : t.adj.Ok := by
  haveI := B.ha; haveI := B.hb
  refine ⟨ht.T, ht.r, fun v => (adjVal_spec h2 B.μa t.ka t.va t.T v (ht.ka v)).1,
    fun v => (adjVal_spec h2 B.μb t.kb t.vb t.T v (ht.kb v)).1, fun x y => ⟨?_, ?_⟩, ?_⟩
  · exact Complex.continuous_conj.comp ((ht.ψ y x).1.comp continuous_inv)
  · exact ((ht.ψ y x).2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro x y g hg
    have hg' : t.ψ y x g⁻¹ ≠ 0 := fun h0 => hg (by show starRingEnd ℂ (t.ψ y x g⁻¹) = 0; rw [h0, map_zero])
    have s := ht.size y x g⁻¹ hg'
    rw [Prod.fst_inv, Prod.snd_inv, map_inv, map_inv, logSize_inv, logSize_inv] at s
    exact s

theorem adjOp (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (t : PT B) (ht : t.Ok) :
    t.adj.op = ContinuousLinearMap.adjoint t.op := by
  haveI := B.ha; haveI := B.hb
  have ha := h3 E B.a B.b B.μa B.μb B.Ma B.Mb B.κ t.ka t.kb t.va t.vb t.T t.ψ ht.ka ht.kb ht.ψ
  have hΦ : t.adj.Φ = adjM t.Φ := ha.2.symm
  have h := (h1 E B.a B.b B.D B.I).2 t.Φ t.Φ t.op t.op (test B h3 t ht) (test B h3 t ht) (rop B h1 h3 t ht)
    (rop B h1 h3 t ht)
  have htest : IsTestM (adjM t.Φ) := hΦ ▸ test B h3 t.adj (adjOk B h2 t ht)
  show B.opOf t.adj.Φ = _
  rw [hΦ]
  exact opOf_eq B h1 htest h.2.2

theorem mulVal (t t' : PT B) (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (t.mul t').val χa χb = t.val χa χb * t'.val χa χb := by
  simp only [PT.val, PT.mul, valA, Pi.mul_apply, Finset.prod_mul_distrib]
  ring

theorem adjValEq (h2 : MultAlg) (t : PT B) (ht : t.Ok) (χa : InfinitePlace E → Inf B.a)
    (χb : InfinitePlace E → Inf B.b) (ha : ∀ v, IsHerm (χa v)) (hb : ∀ v, IsHerm (χb v)) :
    t.adj.val χa χb = starRingEnd ℂ (t.val χa χb) := by
  haveI := B.ha; haveI := B.hb
  simp only [PT.val, PT.adj, valA]
  rw [map_mul, map_prod, map_prod]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => (adjVal_spec h2 B.μa t.ka t.va t.T v (ht.ka v)).2 _ (ha v)
  · exact Finset.prod_congr rfl fun v _ => (adjVal_spec h2 B.μb t.kb t.vb t.T v (ht.kb v)).2 _ (hb v)

theorem commPhi (h2 : MultAlg) (t t' : PT B) (ht : t.Ok) (ht' : t'.Ok)
    (hψ : mulF B.ν t.ψ t'.ψ = mulF B.ν t'.ψ t.ψ) : (t.mul t').Φ = (t'.mul t).Φ := by
  haveI := B.ha; haveI := B.hb
  have ea : ∀ v (g : GA E B.a), convK B.μa t.ka t'.ka v (gInf v g).val = convK B.μa t'.ka t.ka v (gInf v g).val :=
    fun v g => (h2 B.a B.μa (B.Ma v) (t.ka v) (t'.ka v) (t.va v) (t'.va v) t.T t'.T (ht.ka v) (ht'.ka v)).2.1 _
      (Matrix.isUnits_det_units _).ne_zero
  have eb : ∀ v (g : GA E B.b), convK B.μb t.kb t'.kb v (gInf v g).val = convK B.μb t'.kb t.kb v (gInf v g).val :=
    fun v g => (h2 B.b B.μb (B.Mb v) (t.kb v) (t'.kb v) (t.vb v) (t'.vb v) t.T t'.T (ht.kb v) (ht'.kb v)).2.1 _
      (Matrix.isUnits_det_units _).ne_zero
  funext i j g
  simp only [PT.Φ, PT.mul, tens, entA, hψ, ea, eb]

end Op

theorem blkOp (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (h4 : TensMul) : BlockOperatorsProductAdjoint := by
  intro E _ _ _ B t t' ht ht'
  exact ⟨Op.test B h3 t ht, Op.rop B h1 h3 t ht, Op.mulOk B h2 h4 t t' ht ht', Op.mulOp B h1 h3 h4 t t' ht ht',
    Op.adjOk B h2 t ht, Op.adjOp B h1 h2 h3 t ht, Op.mulVal B t t', Op.adjValEq B h2 t ht⟩

theorem blkComm (h1 : OpEx) (h2 : MultAlg) (h3 : TensTest) (h4 : TensMul) : BlockPureTensorsCommute := by
  intro E _ _ _ B t t' ht ht' hψ
  show t.op * t'.op = t'.op * t.op
  rw [← Op.mulOp B h1 h3 h4 t t' ht ht', ← Op.mulOp B h1 h3 h4 t' t ht' ht]
  exact congrArg B.opOf (Op.commPhi B h2 t t' ht ht' hψ)

end PositivityTheory.Rg.BcB.F

end
end
