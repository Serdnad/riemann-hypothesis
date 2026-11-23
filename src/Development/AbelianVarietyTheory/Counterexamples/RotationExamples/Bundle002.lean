module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
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

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature

namespace GlobalTheory.ConjLiftCounterexample

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {σ : D.what₂.LL →+* ℂ}

theorem inner_of_unitary {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (U : X ≃ₗᵢ[ℂ] X) (g : X → X)
    (hg : ∀ a b, ⟪g a, g b⟫_ℂ = ⟪a, b⟫_ℂ) {κ : ℂ} (hκ : ‖κ‖ = 1) {p p' q q' : X} (h : U p = κ • g q) (h' : U p' = κ • g q') :
    ⟪p, p'⟫_ℂ = ⟪q, q'⟫_ℂ := by
  have key : ⟪U p, U p'⟫_ℂ = ⟪κ • g q, κ • g q'⟫_ℂ := by rw [h, h']
  rw [LinearIsometryEquiv.inner_map_map, inner_smul_left, inner_smul_right, hg, ← mul_assoc,
    RCLike.conj_mul, hκ] at key
  simpa using key



theorem gram_of_conjAt {ph : ℂ} {c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W} (h : ConjAt R i σ ph c₀)
    {μ' η' : (AE D)ˣ →* Circle} {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W}
    {H : HMod (Bridge.Gf (Vc D i) → c.W)} {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} {th : H.H →ₗ[ℂ] (R.HW i σ).H}
    (hd : IsConjDatum R i σ c₀ μ' η' c c₁ H j th) {x x' : A.fam.amb.FL i A.μ0} {y y' : Fin (R.nW i) → D.what₂.LL}
    (hy : IsRatLift R i ph x y) (hy' : IsRatLift R i ph x' y') :
    @inner ℂ (R.HW i σ).H _ ((R.FW i).j σ y) ((R.FW i).j σ y') = @inner ℂ (R.HW i σ).H _ (th (j x)) (th (j x')) := by
  obtain ⟨-, -, u, U, z, ζ, -, -, hz, hall⟩ := h
  obtain ⟨-, κ, hκ, hlift⟩ := hall μ' η' c c₁ H j th hd
  exact inner_of_unitary U (fun w => R.gW i σ z w) hz.unitary hκ (hlift x y hy) (hlift x' y' hy')

end GlobalTheory.ConjLiftCounterexample

end
end

section

noncomputable section
open NumberField
open scoped TensorProduct
namespace GlobalTheory.PhaseRationalDegenerate
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

def IsRat (F : GA D (Wc D i) → ℂ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
    F h = ∑ k, D.what₂.embLL (a k) *
      ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)

theorem IsRat.zero : IsRat O κ cc 0 := ⟨0, Fin.elim0, Fin.elim0, fun _ => by simp⟩

theorem IsRat.add {F F' : GA D (Wc D i) → ℂ} (h : IsRat O κ cc F) (h' : IsRat O κ cc F') : IsRat O κ cc (F + F') := by
  obtain ⟨n, a, f, hf⟩ := h
  obtain ⟨n', a', f', hf'⟩ := h'
  refine ⟨n + n', Fin.append a a', Fin.append f f', fun x => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.add_apply, hf x, hf' x]

theorem IsRat.mul (b : D.what₂.LL) {F : GA D (Wc D i) → ℂ} (h : IsRat O κ cc F) : IsRat O κ cc (D.what₂.embLL b • F) := by
  obtain ⟨n, a, f, hf⟩ := h
  refine ⟨n, fun k => b * a k, f, fun x => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hf x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]; ring

theorem levChi_flag (k : GA D (Wc D i)) :
    Formalism.IndefR.Lev.levChi (Wc D i) (R.βW i) (Formalism.IndefR.Lev.flagL (R.datWp i R.triv)) k = 1 := by
  unfold Formalism.IndefR.Lev.levChi levFn
  have h1 : ∀ x, ext1 (Formalism.IndefR.Lev.flagL (R.datWp i R.triv)).P.H (Formalism.IndefR.Lev.flagL (R.datWp i R.triv)).P.chi x = 1 := by
    intro x
    unfold ext1
    split_ifs <;> rfl
  rw [h1, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul, Units.val_one]
  · intro PP hP; exact absurd hP (Finset.notMem_empty _)
  · intro PP _; exact Finset.prod_eq_one fun c hc => absurd hc (Finset.notMem_empty _)

theorem IsRat.act (hE : O.EquivAt κ cc) (hχ : R.grp_chiW) (g : G) {F : GA D (Wc D i) → ℂ} (h : IsRat O κ cc F) :
    IsRat O κ cc (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F) := by
  show IsRat O κ cc (Formalism.IndefR.Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F)
  unfold Formalism.IndefR.Lev.actG0
  split_ifs with hk
  · obtain ⟨n, a, f, hf⟩ := h
    have e := hE g _ hk.choose_spec
    refine ⟨n, fun k => a k * ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL),
      fun k => ⟨_, (e _ (f k).2).1⟩, fun x => ?_⟩
    rw [levChi_flag, inv_one]
    beta_reduce
    rw [one_mul, hf]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e2 := (e _ (f k).2).2 x
    rw [← hχ i g] at e2
    have e3 : D.what₂.embLL ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) *
        D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    show _ = _ * (_ * O.phi cc (actLev C.Q.c O.lev2 g (f k : C.R ((i : ℕ) + 1))) x)
    rw [e2, map_mul]
    linear_combination (-(D.what₂.embLL (a k) * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi cc (f k : C.R ((i : ℕ) + 1)) (x * hk.choose))) * e3
  · exact IsRat.zero O κ cc



theorem of_before_projector (hE : O.EquivAt κ cc) (hχ : R.grp_chiW) (hG : R.thP_thG) (ph : ℂ)
    (h : ∀ x : A.fam.amb.FL i A.μ0, IsRat O κ cc (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀)) : O.PhRat κ v₀ cc ph := by
  intro x
  have key : IsRat O κ cc (R.eWf i (sg0 D A) (ph • R.thF i A.μ0 (jVx R i A.μ0 x) v₀)) := by
    unfold RealDat.eWf gaL
    rw [LinearMap.sum_apply]
    refine Finset.sum_induction _ (IsRat O κ cc) (fun _ _ => IsRat.add O κ cc) (IsRat.zero O κ cc) fun g _ => ?_
    have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
    have : RealDat.eC (A := A) (sg0 D A) g = D.what₂.embLL ((idemOf A.X).coeff g) :=
      RingHom.congr_fun hs ((idemOf A.X).coeff g)
    have h2 := IsRat.mul O κ cc ((idemOf A.X).coeff g) (IsRat.act O κ cc hE hχ g (h x))
    rw [← this] at h2
    exact h2
  obtain ⟨n, a, f, hf⟩ := key
  refine ⟨n, a, f, fun y => ?_⟩
  rw [← hf y, hG i A.μ0, map_smul]
  rfl

end GlobalTheory.PhaseRationalDegenerate
end
end
