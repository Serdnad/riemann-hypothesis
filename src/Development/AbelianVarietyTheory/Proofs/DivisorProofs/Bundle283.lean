module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.Regroup

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem {I : FractionalIdeal (𝓞 F)⁰ F} (ε : (𝓞 F)ˣ) {a : F} (ha : a ∈ I) :
    ((ε : 𝓞 F) : F) * a ∈ I := by
  have : (ε : 𝓞 F) • a ∈ (I : Submodule (𝓞 F) F) := Submodule.smul_mem _ _ ha
  rwa [Algebra.smul_def] at this

theorem unit_eq_one {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (h.trans (one_mul b).symm)
  apply Units.ext
  apply RingOfIntegers.ext
  simpa using h1

variable (𝔞 𝔟 : Frac F)

theorem mk_eq {p q : LatPair 𝔞 𝔟} (ε : (𝓞 F)ˣ) (h1 : q.1.1 = ((ε : 𝓞 F) : F) * p.1.1)
    (h2 : q.1.2 = ((ε : 𝓞 F) : F) * p.1.2) : Quotient.mk (latRel 𝔞 𝔟) p = Quotient.mk _ q :=
  Quotient.sound (Exists.intro ε ⟨h1, h2⟩)

theorem mkU_eq {I : FractionalIdeal (𝓞 F)⁰ F} {x y : NZ I} (ε : (𝓞 F)ˣ) (h : y.1 = ((ε : 𝓞 F) : F) * x.1) :
    Quotient.mk (unitRel I) x = Quotient.mk _ y :=
  Quotient.sound (Exists.intro ε h)

def leftPt (c : Quotient (unitRel (latM 𝔞))) : LatPair 𝔞 𝔟 :=
  ⟨(c.out.1, 0), c.out.2.1, ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).zero_mem, fun h => c.out.2.2 (congrArg Prod.fst h)⟩

def rightPt (c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) (a : {a : F // a ∈ latM 𝔞}) : LatPair 𝔞 𝔟 :=
  ⟨(a.1, c.out.1), a.2, c.out.2.1, fun h => c.out.2.2 (congrArg Prod.snd h)⟩

def regroupMap : Quotient (unitRel (latM 𝔞)) ⊕
    (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {a : F // a ∈ latM 𝔞}) → Quotient (latRel 𝔞 𝔟)
  | Sum.inl c => Quotient.mk _ (leftPt 𝔞 𝔟 c)
  | Sum.inr s => Quotient.mk _ (rightPt 𝔞 𝔟 s.1 s.2)

theorem regroupMap_injective : Function.Injective (regroupMap 𝔞 𝔟) := by
  rintro (c | ⟨c, a⟩) (c' | ⟨c', a'⟩) h
  · obtain ⟨ε, h1, -⟩ := Quotient.exact h
    congr 1
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact mkU_eq ε h1
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    exact absurd (h2.trans (mul_zero _)) c'.out.2.2
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    dsimp only [leftPt, rightPt] at h2
    have := congrArg (fun x => (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * x) h2
    simp only [← mul_assoc, unit_inv_mul, one_mul, mul_zero] at this
    exact absurd this.symm c.out.2.2
  · obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact mkU_eq ε h2
    subst hc
    have hε : ε = 1 := unit_eq_one c.out.2.2 h2.symm
    subst hε
    have ha : a' = a := Subtype.ext (by simpa [rightPt] using h1)
    subst ha
    rfl

theorem regroupMap_surjective : Function.Surjective (regroupMap 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
  obtain ⟨⟨a, b⟩, ha, hb, hne⟩ := p
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ε, hε⟩ : (unitRel (latM 𝔞)).r ⟨a, ha, ha0⟩ (Quotient.mk (unitRel (latM 𝔞)) ⟨a, ha, ha0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inl (Quotient.mk _ ⟨a, ha, ha0⟩), (mk_eq 𝔞 𝔟 ε hε (mul_zero _).symm).symm⟩
  · obtain ⟨ε, hε⟩ : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r ⟨b, hb, hb0⟩
        (Quotient.mk (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ⟨b, hb, hb0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inr ⟨Quotient.mk _ ⟨b, hb, hb0⟩, ⟨_, unit_mul_mem ε ha⟩⟩, (mk_eq 𝔞 𝔟 ε rfl hε).symm⟩

theorem g_out {g : F × F → ℂ}
    (hg : ∀ (ε : (𝓞 F)ˣ) (a b : F), g (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = g (a, b))
    (p : LatPair 𝔞 𝔟) : g (Quotient.mk (latRel 𝔞 𝔟) p).out.1 = g p.1 := by
  obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
  have : p.1 = (((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1,
      ((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2) := Prod.ext h1 h2
  rw [this, hg]

end GlobalTheory.HeckeTwo.Regroup

theorem GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  intro F _ _ 𝔞 𝔟 g hg hs
  open GlobalTheory.HeckeTwo.Regroup in
  let e := Equiv.ofBijective _ ⟨regroupMap_injective 𝔞 𝔟, regroupMap_surjective 𝔞 𝔟⟩
  let h : Quotient (unitRel (latM 𝔞)) ⊕
      (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) → ℂ :=
    Sum.elim (fun c => g (c.out.1, 0)) (fun s => g (s.2.1, s.1.out.1))
  have hfe : (fun c : Quotient (latRel 𝔞 𝔟) => g c.out.1) ∘ e = h := by
    funext x
    rcases x with c | ⟨c, a⟩
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
  have hsh : Summable h := hfe ▸ (e.summable_iff).2 hs
  have hl : Summable (h ∘ Sum.inl) := hsh.comp_injective Sum.inl_injective
  have hr : Summable (h ∘ Sum.inr) := hsh.comp_injective Sum.inr_injective
  have hr' : Summable (fun s : (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)),
      {a : F // a ∈ latM 𝔞}) => g (s.2.1, s.1.out.1)) := hr
  refine ⟨hl, fun c => hr'.sigma_factor c, hr'.sigma, ?_⟩
  rw [← e.tsum_eq, show (∑' x, g (e x).out.1) = ∑' x, h x from congrArg tsum hfe, hl.tsum_sum hr]
  exact congrArg₂ (· + ·) rfl hr'.tsum_sigma
end
end

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EigenSubEval

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
  {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_rsmul (b : S → Int0 v) (N : ℕ) (r : RS b) (z : Fin N → RS b) (s : S) (i : Fin N) :
    evalVec b N (r • z) s i = ((ev b s r : Int0 v) : C) * evalVec b N z s i := by
  simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, Subring.coe_mul]

theorem mem_eigSub_iff (b : S → Int0 v) (N : ℕ) (τ : S) (z : Fin N → RS b) :
    z ∈ eigSub b τ (Fin N → RS b) ↔ lin b τ • z = 0 := Iff.rfl

theorem eigenSub_iff_eval (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S) (ha : Function.Injective a)
    (hinj : Function.Injective (evalVec (liftA hv a) N))
    (hrange : ∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (y : Fin N → C) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      ∃ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  have hev : ∀ s t, ((ev (liftA hv a) s (lin (liftA hv a) t) : Int0 v) : C) = (a s : C) - a t := by
    intro s t
    rw [ev_lin]; rfl
  have hne : ∀ s, s ≠ τ → (a s : C) - a τ ≠ 0 := by
    intro s hs h
    exact hs (ha (Subtype.ext (sub_eq_zero.1 h)))
  have hmem : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      (Pi.single τ y : S → Fin N → C) ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (hrange _).1 h
    refine ⟨x, ?_, ?_⟩
    · rw [mem_eigSub_iff]
      apply hinj
      funext s i
      rw [evalVec_rsmul, hev, hx]
      have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
        simp [evalVec]
      rw [h0]
      by_cases e : s = τ
      · subst e; simp
      · simp [e]
    · rw [comp_coe, hx]; simp
  · rintro ⟨z, hz, rfl⟩
    rw [mem_eigSub_iff] at hz
    have key : evalVec (liftA hv a) N z = Pi.single τ (evalVec (liftA hv a) N z τ) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp
      · have h1 := congrFun (congrFun (congrArg (evalVec (liftA hv a) N) hz) s) i
        rw [evalVec_rsmul, hev] at h1
        have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
          simp [evalVec]
        rw [h0] at h1
        rw [Pi.single_eq_of_ne e]
        exact (mul_eq_zero.1 h1).resolve_left (hne s e)
    rw [comp_coe, ← key]
    exact (hrange _).2 ⟨z, rfl⟩

end GlobalTheory.EigenSubEval
end

section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge

open Polynomial

theorem prod_X_sub_C_dvd_of_eval_zero {O S : Type} [CommRing O] [IsDomain O] [Fintype S]
    (b : S → O) (hb : Function.Injective b) (g : O[X]) (hg : ∀ s, g.eval (b s) = 0) :
    (∏ s, (X - C (b s))) ∣ g := by
  by_cases h0 : g = 0
  · simp [h0]
  have hprod : (∏ s, (X - C (b s))) = ((Finset.univ.val.map b).map (fun t => X - C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots h0]
  rw [Multiset.le_iff_subset (Multiset.Nodup.map hb Finset.univ.nodup)]
  intro t ht
  obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 ht
  exact (mem_roots h0).2 (hg s)

theorem evalVec_injective_of_injective (C : Type) [Field C] (w : Valuation C ℝ≥0)
    (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring)
    (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) :
    Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  intro ha
  have hinj : Function.Injective (liftA hv a) := by
    intro s t hst
    apply ha
    apply Subtype.ext
    have := congrArg (fun u : Int0 v => (u : C)) hst
    exact this
  have key : ∀ x : Fin N → RS (liftA hv a), evalVec (liftA hv a) N x = 0 → x = 0 := by
    intro x hx
    funext i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    rw [Pi.zero_apply, ← hg, AdjoinRoot.mk_eq_zero]
    apply prod_X_sub_C_dvd_of_eval_zero _ hinj
    intro s
    have h1 := congrFun (congrFun hx s) i
    simp only [evalVec, Pi.zero_apply, ← hg] at h1
    apply Subtype.ext
    rw [show ((0 : Int0 v) : C) = 0 from rfl, ← h1]
    congr 1
  intro x y hxy
  have := key (x - y) (by rw [evalVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

end GlobalTheory.HerbrandBridge
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.PartialZetaSum

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ J : Ideal (𝓞 F), (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [← FractionalIdeal.le_one_iff_exists_coeIdeal]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
      ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 b.2.1) _
    _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

def idealOf (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : Ideal (𝓞 F) := (exists_ideal 𝔟 b).choose

theorem idealOf_coe (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
  (exists_ideal 𝔟 b).choose_spec

theorem span_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [idealOf_coe, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem idealOf_mem (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : idealOf 𝔟 b ∈ (Ideal (𝓞 F))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have h1 := span_eq 𝔟 b
  rw [h] at h1
  simp at h1
  exact b.2.2 h1

theorem idealOf_class (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ = (ClassGroup.mk F 𝔟)⁻¹ := by
  rw [← ClassGroup.mk_mk0 F, ← map_inv]
  have hb : (b.1 : F) ≠ 0 := b.2.2
  have h : FractionalIdeal.mk0 F ⟨idealOf 𝔟 b, idealOf_mem 𝔟 b⟩ =
      toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb) * 𝔟⁻¹ := by
    apply Units.ext
    rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, idealOf_coe]
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 b.1 hb)) = 1 := by
    rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  rw [h, map_mul, hp, one_mul]

theorem rel_of_idealOf_eq (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : idealOf 𝔟 b = idealOf 𝔟 b') : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b' := by
  have h2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ b'.1 := by
    rw [span_eq, span_eq, h]
  obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h2
  exact ⟨z, by rw [← hz, Units.smul_def, Algebra.smul_def]⟩

theorem idealOf_eq_of_rel (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b') : idealOf 𝔟 b = idealOf 𝔟 b' := by
  obtain ⟨ε, hε⟩ := h
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe, idealOf_coe, hε]
  congr 1
  exact FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, by rw [Units.smul_def, Algebra.smul_def]⟩

theorem exists_of_class (𝔟 : Frac F) (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹) :
    ∃ b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), idealOf 𝔟 b = J.1 := by
  have h1 : ClassGroup.mk F (FractionalIdeal.mk0 F J * 𝔟) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hJ, inv_mul_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hx' : ((FractionalIdeal.mk0 F J * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    beta_reduce
    rw [FractionalIdeal.coe_spanSingleton]; exact hx
  rw [Units.val_mul, FractionalIdeal.coe_mk0] at hx'
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx'
    exact (mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero J)) (Units.ne_zero 𝔟)) hx'
  have hxm : x ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
    have : FractionalIdeal.spanSingleton (𝓞 F)⁰ x ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [← hx']
      calc ((J.1 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
          ≤ 1 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
        _ = _ := one_mul _
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 this
  let b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := ⟨x, hxm, hx0⟩
  refine ⟨b, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := F)
  beta_reduce
  rw [idealOf_coe]
  show FractionalIdeal.spanSingleton (𝓞 F)⁰ x * _ = _
  rw [← hx', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem norm_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    |((Algebra.norm ℚ b.1 : ℚ) : ℝ)| = (Ideal.absNorm (idealOf 𝔟 b) : ℝ) * nrm 𝔟 := by
  have h2 := congrArg FractionalIdeal.absNorm (span_eq 𝔟 b)
  rw [FractionalIdeal.absNorm_span_singleton, map_mul, FractionalIdeal.coeIdeal_absNorm] at h2
  unfold nrm
  rw [← Rat.cast_abs, h2]; push_cast; ring

theorem nrm_nonneg (𝔟 : Frac F) : 0 ≤ nrm 𝔟 := by
  unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _

theorem hasSum_norm_cpow : ∀ (F : Type) [Field F] [NumberField F] (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ s : ℂ, 1 < s.re → HasSum (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-s)) (((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔟 : ℝ) : ℂ) ^ (-s) * Zb s) := by
  intro F _ _ 𝔟 Zb hZ s hs
  let e : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) →
      {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹} :=
    fun c => ⟨⟨idealOf 𝔟 c.out, idealOf_mem 𝔟 c.out⟩, idealOf_class 𝔟 c.out⟩
  have he : Function.Bijective e := by
    constructor
    · intro c c' h
      have h' : idealOf 𝔟 c.out = idealOf 𝔟 c'.out := congrArg (fun J => (J.1.1 : Ideal (𝓞 F))) h
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact Quotient.sound (rel_of_idealOf_eq 𝔟 h')
    · intro J
      obtain ⟨b, hb⟩ := exists_of_class 𝔟 J.1 J.2
      refine ⟨Quotient.mk _ b, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show idealOf 𝔟 (Quotient.mk _ b).out = J.1.1
      rw [← hb]; exact idealOf_eq_of_rel 𝔟 (Quotient.exact (Quotient.out_eq _))
  have key := (hZ.2 s hs).mul_left (((nrm 𝔟 : ℝ) : ℂ) ^ (-s))
  rw [← (Equiv.ofBijective e he).hasSum_iff] at key
  refine (congrArg (fun f => HasSum f _) ?_).mpr key
  funext c
  simp only [Function.comp_apply, Equiv.ofBijective_apply, e]
  rw [norm_eq 𝔟 c.out, ofReal_mul, mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (nrm_nonneg 𝔟), mul_comm,
    ofReal_natCast]

end GlobalTheory.PartialZetaSum
end
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem phi_ofReal_mul (σ : ℂ) (y : ℝ) (w : ℂ) :
    phi σ ((y : ℂ) * w) = (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    mul_cpow_ofReal_nonneg (abs_nonneg y) (norm_nonneg w)]
  have h : ((y : ℂ))⁻¹ ^ 2 = ((|y| : ℝ) : ℂ)⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, ← ofReal_pow, ← ofReal_pow, sq_abs]
  rw [mul_inv, mul_pow, h]
  ring

theorem hTrans_zero_eq (σ : ℂ) (y : ℝ) (hy : y ≠ 0) :
    hTrans σ 0 y = cConst σ * ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) := by
  have h0 : hTrans σ 0 y = ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) := by simp [hTrans]
  have h1 : cConst σ = ∫ t : ℝ, phi σ ((t : ℂ) + I) := by simp [cConst, hTrans]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) y
  have h2 : (∫ u : ℝ, phi σ (((y * u : ℝ) : ℂ) + (y : ℂ) * I)) =
      (((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) * ∫ u : ℝ, phi σ ((u : ℂ) + I) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    ext u
    rw [← phi_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [h2] at hsub
  have hya : (|y| : ℝ) ≠ 0 := abs_ne_zero.mpr hy
  have hyc : ((|y| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hya
  have h3 : (∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I)) =
      ((|y| : ℝ) : ℂ) * ((((|y| : ℝ) : ℂ)⁻¹ ^ 2 * ((|y| : ℝ) : ℂ) ^ (-2 * σ)) *
        ∫ u : ℝ, phi σ ((u : ℂ) + I)) := by
    rw [hsub, abs_inv, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hyc, one_mul]
  have hc : ((|y| : ℝ) : ℂ) ^ (-1 - 2 * σ) = ((|y| : ℝ) : ℂ)⁻¹ * ((|y| : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [show (-1 - 2 * σ) = -1 + -2 * σ by ring, cpow_add _ _ hyc, cpow_neg_one]
  rw [h0, h3, ← h1, hc]
  field_simp

end GlobalTheory.HeckeTwo
end
end
