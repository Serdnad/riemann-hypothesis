module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle518
import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Linear

variable {R : Type} [CommRing R] {d : ℕ}


open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
theorem _root_.GlobalTheory.LawDer.Linear.invDer_linear : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ u : Fin d → R, (∀ F G : MvPowerSeries (Fin d) R, _root_.GlobalTheory.LawDer.invDer μ u (F + G) = _root_.GlobalTheory.LawDer.invDer μ u F + _root_.GlobalTheory.LawDer.invDer μ u G) ∧ (∀ (a : R) (F : MvPowerSeries (Fin d) R), _root_.GlobalTheory.LawDer.invDer μ u (a • F) = a • _root_.GlobalTheory.LawDer.invDer μ u F) ∧ ∀ a : R, _root_.GlobalTheory.LawDer.invDer μ u (C a) = 0 := by
  intro R _ d μ hμ u
  have hμs : HasSubst μ := hasSubst_of_constantCoeff_nilpotent fun i ↦ by simp [hμ i]
  have hzero : HasSubst (Sum.elim (fun i : Fin d ↦ (X i : MvPowerSeries (Fin d) R))
      fun _ : Fin d ↦ (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_nilpotent fun s ↦ by cases s <;> simp
  refine ⟨fun F G ↦ ?_, fun a F ↦ ?_, fun a ↦ ?_⟩
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [subst_add hμs, map_add (f := _), subst_add hzero, smul_add]
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [subst_smul hμs, Derivation.map_smul_of_tower, subst_smul hzero, smul_comm]
  · unfold _root_.GlobalTheory.LawDer.invDer _root_.GlobalTheory.LawDer.atZero
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [subst_C, pderiv_C]
    simpa using congrArg (u i • ·) (subst_C (a := Sum.elim
      (fun j : Fin d ↦ (X j : MvPowerSeries (Fin d) R))
      fun _ : Fin d ↦ (0 : MvPowerSeries (Fin d) R)) (0 : R))

end GlobalTheory.LawDer.Linear
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

theorem map_pderiv_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) s f) = MvPowerSeries.pderiv (R := S) s (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map,
    map_mul, map_add, map_natCast, map_one]

theorem map_atZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) : map f (atZero H) = atZero (map f H) := by
  unfold atZero
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp))]
  congr 1
  funext s
  cases s <;> simp

theorem map_smul_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R)
    (H : MvPowerSeries σ R) : map f (a • H) = f a • map f H := by
  ext m
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul]

theorem map_invDer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (F : MvPowerSeries (Fin d) R) :
    map f (invDer μ u F) = invDer (fun i => map f (μ i)) (fun i => f (u i)) (map f F) := by
  unfold invDer

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_coeffChange, map_atZero, map_pderiv_coeffChange, map_subst (hasSubst_of_constantCoeff_zero hμ)]

theorem map_invDer_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R),
    map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  intro R S _ _ f d μ hμ u k F
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_invDer f μ hμ, ih]

end GlobalTheory.LawDer
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def IterFrobBase (K : Type) (p r : ℕ) : Type := K

namespace IterFrobBase

variable (K : Type) (p r : ℕ) [Field K]

instance : Field (IterFrobBase K p r) := inferInstanceAs (Field K)

variable [hp : Fact p.Prime] [CharP K p]

instance : Algebra (IterFrobBase K p r) K :=
  (SS.FrobField.powHom K p r hp.out (CharP.cast_eq_zero K p)).toAlgebra

instance (H : Type) [CommRing H] [HopfAlgebra K H] : HopfAlgebra (IterFrobBase K p r) H :=
  inferInstanceAs (HopfAlgebra K H)

end IterFrobBase

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H]
  [HopfAlgebra K H] (r : ℕ)

omit hp in
theorem natCast_eq_zero_of_charP_algebra (A : Type) [CommRing A] [Algebra K A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap K A), CharP.cast_eq_zero, map_zero]

def iterFrobSemi : SemiBialgHom (algebraMap (IterFrobBase K p r) K) H H where
  toRingHom := SS.FrobField.powHom H p r hp.out (natCast_eq_zero_of_charP_algebra p K H)
  smul_map c a := by
    change (c • a) ^ p ^ r = ((c : K) ^ p ^ r) • a ^ p ^ r
    rw [smul_pow]
  counit_map a := by
    change counit (R := K) (a ^ p ^ r) = (counit (R := K) a) ^ p ^ r
    rw [counit_pow]
  comul_map a := by
    have key : ∀ c : H ⊗[IterFrobBase K p r] H,
        SS.FrobField.powHom (H ⊗[K] H) p r hp.out (natCast_eq_zero_of_charP_algebra p K _)
          (@id (H ⊗[K] H) c) =
        TensorProduct.map (σ₁₂ := algebraMap (IterFrobBase K p r) K)
          ⟨⟨SS.FrobField.powHom H p r hp.out (natCast_eq_zero_of_charP_algebra p K H),
            map_add _⟩, fun c a => by
              change (c • a) ^ p ^ r = ((c : K) ^ p ^ r) • a ^ p ^ r
              rw [smul_pow]⟩
          ⟨⟨SS.FrobField.powHom H p r hp.out (natCast_eq_zero_of_charP_algebra p K H),
            map_add _⟩, fun c a => by
              change (c • a) ^ p ^ r = ((c : K) ^ p ^ r) • a ^ p ^ r
              rw [smul_pow]⟩ c := by
      intro c
      induction c with
      | add x y hx hy =>
        rw [map_add (f := _), ← hx, ← hy]
        exact map_add _ (@id (H ⊗[K] H) x) (@id (H ⊗[K] H) y)
      | tmul x y =>
        change (x ⊗ₜ[K] y) ^ p ^ r = (x ^ p ^ r) ⊗ₜ[K] (y ^ p ^ r)
        exact Algebra.TensorProduct.tmul_pow x y _
    change comul (R := K) (a ^ p ^ r) = _
    rw [comul_pow]
    exact key (comul a)

def iterRelFrob : K ⊗[IterFrobBase K p r] H →ₐc[K] H := (iterFrobSemi p K H r).liftBC

theorem iterRelFrob_tmul (c : K) (a : H) : iterRelFrob p K H r (c ⊗ₜ a) = c • a ^ p ^ r :=
  SemiBialgHom.liftBC_tmul (iterFrobSemi p K H r) c a

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

theorem finrank_le_frobKer_mul_span_pow (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] (r : ℕ) :
    Module.finrank K H ≤ Module.finrank K (H ⧸ frobKerIdeal (p ^ r) K H) *
      Module.finrank K (Submodule.span K (Set.range fun a : H => a ^ p ^ r)) := by
  set f := iterRelFrob p K H r
  rw [finrank_eq_ker_mul_range K H _ f]
  refine Nat.mul_le_mul ?_ ?_
  · have hle : frobKerIdeal (p ^ r) K H ≤ kerIdeal f := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      have ha' : counit (R := IterFrobBase K p r) a = 0 := ha
      have hb : (1 : K) ⊗ₜ[IterFrobBase K p r] a ∈
          augIdeal K (K ⊗[IterFrobBase K p r] H) := by
        change counit (R := K) ((1 : K) ⊗ₜ[IterFrobBase K p r] a) = 0
        rw [TensorProduct.counit_tmul, ha', zero_smul]
      have e : f ((1 : K) ⊗ₜ a) = a ^ p ^ r := by
        rw [iterRelFrob_tmul, one_smul]
      show a ^ p ^ r ∈ _
      rw [← e]
      exact Ideal.mem_map_of_mem _ hb
    exact LinearMap.finrank_le_finrank_of_surjective
      (f := (Ideal.Quotient.factorₐ K hle).toLinearMap)
      (Ideal.Quotient.factor_surjective hle)
  · refine Submodule.finrank_mono ?_
    rintro _ ⟨x, rfl⟩
    induction x with
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | tmul c a =>
      change f (c ⊗ₜ a) ∈ _
      rw [iterRelFrob_tmul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.PDiv
end
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

theorem _root_.GlobalTheory.T.imaginary_lattice_scaling_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), Unr E → 1 ≤ r → (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) = r ^ fdeg E := by
  first | exact @GlobalTheory.LieDisc.relIndex_mulLeft_imLat | exact GlobalTheory.LieDisc.relIndex_mulLeft_imLat | (intros; apply GlobalTheory.LieDisc.relIndex_mulLeft_imLat <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => x a * ∑ k, G b k * cc (y k)

theorem rankOne_mulVec (G : Matrix (Fin r) (Fin r) E) (x y v : Fin r → E) :
    rankOne G x y *ᵥ v = herm G v y • x := by
  ext a
  simp only [rankOne, mulVec, dotProduct, of_apply, herm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem trace_rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    (rankOne G x y).trace = herm G x y := by
  simp only [Matrix.trace, diag, rankOne, of_apply, herm, Finset.mul_sum, mul_assoc]

def traceIdeal (Λ : Submodule (𝓞 E) (Fin r → E)) : Ideal (𝓞 E) where
  carrier := {s | ∃ Z ∈ endLat Λ, Z.trace = (s : E)}
  zero_mem' := ⟨0, (endLat Λ).zero_mem, by simp⟩
  add_mem' {s t} hs ht := by
    obtain ⟨Z, hZ, e⟩ := hs
    obtain ⟨Z', hZ', e'⟩ := ht
    exact ⟨Z + Z', (endLat Λ).add_mem hZ hZ', by rw [trace_add, e, e']; push_cast; rfl⟩
  smul_mem' c {s} hs := by
    obtain ⟨Z, hZ, e⟩ := hs
    refine ⟨(c : E) • Z, smul_mem_endLat c.isIntegral_coe hZ, ?_⟩
    rw [trace_smul, e, smul_eq_mul, smul_eq_mul]
    push_cast; rfl

theorem exists_endLat_trace_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hr : 1 ≤ r)
    (h : SelfDualLat G Λ) : ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := fun x hx => (h.2.2.2.2 x).2 hx
  have htop : traceIdeal Λ = ⊤ := by
    by_contra hT
    refine GlobalTheory.UCls.Det.exists_herm_notMem hr h (traceIdeal Λ) hT fun x hx y hy =>
      ⟨⟨herm G x y, hint x hx y hy⟩, ⟨rankOne G x y, fun v hv => ?_, trace_rankOne G x y⟩, rfl⟩
    rw [rankOne_mulVec]
    exact smul_mem_of_isIntegral (hint v hv y hy) hx
  have h1 : (1 : 𝓞 E) ∈ traceIdeal Λ := htop ▸ Submodule.mem_top
  obtain ⟨Z, hZ, e⟩ := h1
  exact ⟨Z, hZ, by rw [e]; simp⟩

end GlobalTheory.LieDisc
end
end

section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp only [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_map_mulVec (M : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((M.map cc *ᵥ y) b)) = M *ᵥ fun b => cc (y b) := by
  funext b

  simp only [mulVec, dotProduct, map_apply, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]

theorem herm_mulVec_left_eq (G Y : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x y : Fin r → E) :
    herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
  rw [herm_eq_dotProduct, herm_eq_dotProduct, hAdj, cc_map_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul,
    ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact (dotProduct_mulVec _ _ _).symm

theorem hAdj_mem_endLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (Y : Matrix (Fin r) (Fin r) E) (h : SelfDualLat G Λ) (hY : Y ∈ endLat Λ) : hAdj G Y ∈ endLat Λ := by
  obtain ⟨hGh, hdet, -, -, hsd⟩ := h
  intro y hy
  refine (hsd _).1 fun x hx => ?_
  have h1 : IsIntegral ℤ (herm G x (hAdj G Y *ᵥ y)) := by
    rw [← herm_mulVec_left_eq G Y hdet]
    exact (hsd (Y *ᵥ x)).2 (hY x hx) y hy
  rw [← GlobalTheory.UCls.Det.herm_symm G hGh]
  exact h1.map (IsCMField.complexConj E)

end GlobalTheory.LieDisc

theorem GlobalTheory.LieDisc.hAdj_mem_endLat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ :=
  fun _ _ _ _ r G Λ Y h hY => GlobalTheory.LieDisc.hAdj_mem_endLat G Λ Y h hY
end
end

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankFour_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top | exact GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top | (intros; apply GlobalTheory.IntBall.Fin4.lintegral_hB_four_lt_top <;> assumption)
end

section

open ValuativeRel Matrix

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hν1 i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0
  set g : Matrix A D k → ℂ := boxFn ϖ C (fun _ => m) with hg
  set g' : Matrix A D k → ℂ := boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) with hg'
  set lam : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) * apow ϖ (-(Fintype.card D : ℂ) / 2) with hlam
  set N : ℕ := Fintype.card (Fin r → GlobalTheory.SplitFlip.Res k 1) with hN
  let F : (Fin r → GlobalTheory.SplitFlip.Res k 1) → Matrix A D k → ℂ := fun b => boxFn ϖ (Matrix.updateRow C i₀
    ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m)

  have hz := GlobalTheory.T.box_function_diagonal_action k A D ϖ ν β i₀ C hC0 m (m - 1)
  have hupd : Function.update (fun _ : A => m) i₀ m = fun _ => m := Function.update_eq_self _ _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hupd] at hz
  have h3 : lam • g - g' ∈ twistSpan ν β := by
    rw [hlam, hg, ← hz]; exact sub_mem_twistSpan ν β _ (boxFn_mem_SB _ _ _)

  have h1 : g' - ∑ b, F b ∈ lowRank (r + 1) :=
    GlobalTheory.T.integral_box_bounded_valuation k A D ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0

  have hv1 : valuation k (ϖ : k) ≤ 1 := by rw [hϖ]; exact (uniformizer_lt_one (R := k)).le
  have h2 : ∀ b, F b - g ∈ twistSpan ν β := by
    intro b
    have ht : ∀ l, valuation k ((ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
      intro l
      have hout : valuation k ((Quotient.out (b l) : 𝒪[k]) : k) ≤ 1 := (Quotient.out (b l)).2
      rw [map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
      exact (mul_le_of_le_one_right' hout).trans (pow_le_pow_right_of_le_one' hv1 (by omega))
    have hu := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C H _ hH0 hHv ht
    have hrow : C i₀ = 0 := funext hC0
    rw [hrow, zero_add] at hu
    exact hu

  have key : (lam - (N : ℂ)) • g ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    have e : (lam - (N : ℂ)) • g = (g' - ∑ b, F b) + ∑ b, (F b - g) + (lam • g - g') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, sub_smul, Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    exact add_mem (add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun b _ => h2 b))) (Submodule.mem_sup_right h3)

  have hne : lam - (N : ℂ) ≠ 0 := by
    intro h
    have hl : lam = N := sub_eq_zero.1 h
    set a : ℝ := nabs k ϖ ^ (-(Fintype.card D : ℝ) / 2) with ha_def
    have hapos : 0 < a := Real.rpow_pos_of_pos (nabs_pos ϖ) _
    have ha : apow ϖ (-(Fintype.card D : ℂ) / 2) = (a : ℂ) := by
      rw [apow, ha_def, Complex.ofReal_cpow (nabs_pos ϖ).le]
      push_cast; ring_nf
    set u : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) with hu_def
    have hua : u * a = N := by rw [← ha]; exact hl
    have hu : u = ((N / a : ℝ) : ℂ) := by
      have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hapos.ne'
      rw [Complex.ofReal_div, Complex.ofReal_natCast, ← hua, mul_div_cancel_right₀ _ ha0]
    have hnorm : ‖u‖ = 1 := by
      rw [hu_def, Units.val_inv_eq_inv_val, norm_inv, hν, inv_one]
    rw [hu, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hapos.le)] at hnorm
    have hu1 : u = 1 := by rw [hu, hnorm]; simp
    apply hν1
    have : (ν ϖ)⁻¹ = 1 := Units.ext (by simpa [hu_def] using hu1)
    exact inv_eq_one.1 this
  exact (Submodule.smul_mem_iff _ hne).1 key
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.clopen_integrability_full_rank_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  first | exact @GlobalTheory.FullRankCoinv.Reduce.reduce_support | exact GlobalTheory.FullRankCoinv.Reduce.reduce_support | (intros; apply GlobalTheory.FullRankCoinv.Reduce.reduce_support <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U), extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  first | (exact @GlobalTheory.EtC.extSh_sec_eq_zero_loc) | (exact GlobalTheory.EtC.extSh_sec_eq_zero_loc) | (intros; apply GlobalTheory.EtC.extSh_sec_eq_zero_loc  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U), Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.ExtOnto.ext_onto) | (exact GlobalTheory.EtC.ExtOnto.ext_onto) | (intros; apply GlobalTheory.EtC.ExtOnto.ext_onto  <;> assumption)
end
