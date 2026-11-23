module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle009
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbFund
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion

@[expose] public section

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_hopf_order_fundamental_character : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS σ hσ g hg
  have sum_Icc_pow_eq_mul_sum_range (ζ : R) (n : ℕ) :
      ∑ m ∈ Finset.Icc 1 n, ζ ^ m = ζ * ∑ m ∈ Finset.range n, ζ ^ m := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, mul_add, pow_succ']
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have : IsDomain R := Function.Injective.isDomain (algebraMap R C) hinj
  obtain ⟨h0, w, hw⟩ := PositivityTheory.HtPt.Rb.exists_inv_card (F := F) hv hp hc
  have hgA : g ∈ AA.carrier := (Submodule.mem_inf.1 hg).1
  have hg0 : g 0 = 0 := by simpa using LinearMap.mem_ker.1 (Submodule.mem_inf.1 hg).2
  refine ⟨fun χ => ⟨PositivityTheory.HtPt.Rb.proj_mem hw AA.carrier χ g (fun a => hFS a g hgA),
      fun a x => PositivityTheory.HtPt.Rb.proj_smul_apply χ g hg0 a x⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hord, -, -, -, hsep⟩ := FundGen.main p C v R hv hp F f hc σ hσ
    have hcardU : Fintype.card Fˣ = p ^ f - 1 := by rw [Fintype.card_units, hc]
    have hσq : σ ^ (p ^ f - 1) = 1 := hord ▸ pow_orderOf_eq_one σ
    have hz : ∀ a : Fˣ, ∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F) =
        if a = 1 then ((p ^ f - 1 : ℕ) : R) else 0 := by
      intro a
      have hpow : ∀ m : ℕ, (σ ^ m)⁻¹ (a : F) = (σ⁻¹ (a : F)) ^ m := fun m => by
        rw [← inv_pow, MulChar.pow_apply_coe]
      simp only [hpow]
      split_ifs with ha
      · subst ha
        simp
      · have hroot : (σ⁻¹ (a : F)) ^ (p ^ f - 1) = 1 := by
          rw [← MulChar.pow_apply_coe, inv_pow, hσq, inv_one, MulChar.one_apply_coe]
        have hneRoot : σ⁻¹ (a : F) ≠ 1 := by
          intro h1
          have hne : (a : F) ≠ 1 := fun h => ha (Units.val_eq_one.1 h)
          have hs := hsep (a : F) 1 hne
          have hsa : σ (a : F) = 1 := by
            have := PositivityTheory.HtPt.Rb.inv_mul_apply σ a
            rwa [h1, one_mul] at this
          rw [hsa, MulChar.map_one, sub_self, map_zero, map_zero] at hs
          exact zero_ne_one hs
        rw [sum_Icc_pow_eq_mul_sum_range]
        have hgeom := geom_sum_mul (σ⁻¹ (a : F)) (p ^ f - 1)
        rw [hroot, sub_self] at hgeom
        rw [(mul_eq_zero.1 hgeom).resolve_right (sub_ne_zero.2 hneRoot), mul_zero]
    funext x
    have hsum : (∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g) x =
        (Fintype.card Fˣ : C)⁻¹ * ∑ a : Fˣ, algebraMap R C
          (∑ m ∈ Finset.Icc 1 (p ^ f - 1), (σ ^ m)⁻¹ (a : F)) * g ((a : F) • x) := by
      rw [Finset.sum_apply]
      simp only [proj]
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_

      rw [map_sum, Finset.sum_mul]
    rw [hsum]
    simp only [hz, apply_ite (algebraMap R C), ite_mul, map_zero, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, Units.val_one, one_smul, map_natCast]
    rw [← hcardU, inv_mul_cancel_left₀ h0]
  · intro haf χ
    have hA : g ∈ AA.carrier := (Submodule.mem_inf.1 haf).1
    have hadd : ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := (Submodule.mem_inf.1 haf).2
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => Submodule.mem_inf.2 ⟨hFS a g hA, fun x y => ?_⟩
    simpa [smul_add] using hadd (a • x) (a • y)
  · intro K hK χ
    obtain ⟨hA, hinv⟩ := hK
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => ⟨hFS a g hA, fun y k hk => ?_⟩
    simp only [smul_add]
    exact hinv (a • y) (a • k) (K.smul_mem a hk)
  · intro hsq χ
    refine PositivityTheory.HtPt.Rb.proj_mem hw _ χ g fun a => ?_
    let L : (N → C) →ₗ[R] (N → C) := LinearMap.funLeft R C (fun x : N => a • x)
    have haug (u : N → C) (hu : u ∈ augIdeal AA.carrier) : L u ∈ augIdeal AA.carrier := by
      obtain ⟨huA, hu0⟩ := Submodule.mem_inf.1 hu
      refine Submodule.mem_inf.2 ⟨hFS a u huA, LinearMap.mem_ker.2 ?_⟩
      have huZero : u 0 = 0 := by simpa using LinearMap.mem_ker.1 hu0
      simpa [L, smul_zero] using huZero
    have hle : sqIdeal (augIdeal AA.carrier) ≤ (sqIdeal (augIdeal AA.carrier)).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, u', hu', rfl⟩
      exact Submodule.subset_span ⟨L u, haug u hu, L u', haug u' hu', rfl⟩
    exact hle hsq
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open PositivityTheory.HtPt.Ri
open scoped Matrix

theorem _root_.GlobalTheory.T.fundamental_character_ideal_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ m, xIdeal AA.carrier (σ ^ m) = Ideal.span {c m}) → augIdeal AA.carrier = Submodule.span R ((fun m (a : F) => algebraMap R C (c m * (σ ^ m) a)) '' (Finset.Icc 1 (p ^ f - 1) : Set ℕ)) ∧ AA.carrier = Submodule.span R {(1 : F → C)} ⊔ augIdeal AA.carrier ∧ HasColen R v AA.carrier (∏ m ∈ Finset.Icc 1 (p ^ f - 1), v (algebraMap R C (c m))) :=
  @_root_.PositivityTheory.HtPt.Ri.r_decomp
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem idealD_pow_mem : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) :=
  @PositivityTheory.HtPt.Rd.a_pow

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS K t ht hGen χ hχ
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hval : ∀ g ∈ AA.carrier, ∀ x, ∃ r : R, algebraMap R C r = g x := fun g hg =>
    (show ∀ x, ∃ r : R, algebraMap R C r = g x from AA.le_int hg)
  have hle : ∀ g ∈ AA.carrier, ∀ x, v (g x) ≤ 1 := by
    intro g hg x
    obtain ⟨r, hr⟩ := hval g hg x
    rw [← hr]
    exact hv.map_le_one r
  have hpv : ∀ z ∈ pInt (C := C) R p, v z < 1 := by
    intro z hz
    unfold pInt at hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Algebra.smul_def, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hv.map_le_one a)) hp
  have hinv : ∀ g, g ∈ invFun AA.carrier K.toAddSubgroup →
      g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x := fun g hg => hg
  have hinvI : ∀ g, (g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x) →
      g ∈ invFun AA.carrier K.toAddSubgroup := fun g hg => hg
  have hadd : ∀ g, g ∈ addFun (C := C) R p N →
      ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := fun g hg => hg
  have h1 : (1 : R) ∈ idealX AA.carrier K t χ := by
    rw [hχ]
    exact Submodule.mem_top
  obtain ⟨g0, hg0, hg0e⟩ := Submodule.mem_map.1
    (show LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) 1 ∈
      stepOrder AA.carrier K t from h1)
  have hg0a : ∀ a : F, g0 (a • t) = algebraMap R C (χ a) := by
    intro a
    have := congrFun hg0e a
    simpa [LinearMap.funLeft_apply, LinearMap.toSpanSingleton_apply] using this
  have hg0t : g0 t = 1 := by simpa using hg0a 1
  have hg0z : g0 0 = 0 := by
    have e := hg0a 0
    rwa [zero_smul, MulChar.map_zero, map_zero] at e
  obtain ⟨h, hA, hh⟩ : ∃ h ∈ afFun p (invFun AA.carrier K.toAddSubgroup),
      ¬ v (h t - h 0) < 1 := by
    by_contra hcon
    push Not at hcon
    have key : ∀ φ ∈ Algebra.adjoin R
        ((afFun p (invFun AA.carrier K.toAddSubgroup) : Submodule R (N → C)) : Set (N → C)),
        φ ∈ AA.carrier ∧ v (φ t - φ 0) < 1 := by
      intro φ hφ
      induction hφ using Algebra.adjoin_induction with
      | mem x hx =>
        have hx' := Submodule.mem_inf.1 (SetLike.mem_coe.1 hx)
        exact ⟨(hinv x hx'.1).1, hcon x (SetLike.mem_coe.1 hx)⟩
      | algebraMap r =>
        refine ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact AA.carrier.smul_mem r AA.one_mem
        · simp
      | add x y _ _ hx hy =>
        refine ⟨AA.carrier.add_mem hx.1 hy.1, ?_⟩
        have e : (x + y) t - (x + y) 0 = (x t - x 0) + (y t - y 0) := by
          simp only [Pi.add_apply]
          ring
        rw [e]
        exact v.map_add_lt hx.2 hy.2
      | mul x y _ _ hx hy =>
        refine ⟨AA.mul_mem x y hx.1 hy.1, ?_⟩
        have e : (x * y) t - (x * y) 0 = x t * (y t - y 0) + y 0 * (x t - x 0) := by
          simp only [Pi.mul_apply]
          ring
        rw [e]
        refine v.map_add_lt ?_ ?_
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle x hx.1 t)) hy.2
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle y hy.1 0)) hx.2
    have hk := (key g0 ((show invFun AA.carrier K.toAddSubgroup ≤ _ from hGen) hg0)).2
    rw [hg0t, hg0z, sub_zero, map_one] at hk
    exact lt_irrefl _ hk
  have hAi := Submodule.mem_inf.1 hA
  obtain ⟨hM, hK⟩ := hinv h hAi.1
  have hAd := hadd h hAi.2
  obtain ⟨r0, hr0⟩ := hval h hM 0
  have h0p : h 0 ∈ pInt (C := C) R p := by
    have h00 := hAd 0 0
    rw [add_zero, show h 0 - h 0 - h 0 = -h 0 by ring] at h00
    simpa using (pInt (C := C) R p).neg_mem h00
  obtain ⟨h', h'apply, h'M⟩ : ∃ h' : N → C, (∀ x, h' x = h x - h 0) ∧ h' ∈ AA.carrier :=
    ⟨h - r0 • (1 : N → C), fun x => by
      show h x - (r0 • (1 : N → C)) x = h x - h 0
      rw [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, hr0],
      AA.carrier.sub_mem hM (AA.carrier.smul_mem r0 AA.one_mem)⟩
  have h'z : h' 0 = 0 := by rw [h'apply, sub_self]
  have h'inv : h' ∈ invFun AA.carrier K.toAddSubgroup :=
    hinvI h' ⟨h'M, fun x k hk => by rw [h'apply, h'apply, hK x k hk]⟩
  have h'add : h' ∈ addFun (C := C) R p N := by
    show ∀ x y, h' (x + y) - h' x - h' y ∈ pInt (C := C) R p
    intro x y
    have e : h' (x + y) - h' x - h' y = (h (x + y) - h x - h y) + h 0 := by
      rw [h'apply, h'apply, h'apply]
      ring
    rw [e]
    exact (pInt (C := C) R p).add_mem (hAd x y) h0p
  have h'af : h' ∈ afFun p AA.carrier := by
    unfold afFun
    exact Submodule.mem_inf.2 ⟨h'M, h'add⟩
  have h'aug : h' ∈ augIdeal AA.carrier := by
    unfold augIdeal
    exact Submodule.mem_inf.2 ⟨h'M, by simp [LinearMap.mem_ker, h'z]⟩
  have h't : ¬ v (h' t) < 1 := by
    rw [h'apply]
    exact hh
  obtain ⟨σ, hσ⟩ := PositivityTheory.HtPt.Rb.fund_ex p C v R hv hp F f hc
  obtain ⟨P1, P2, P3, P4, -⟩ :=
    PositivityTheory.HtPt.Rb.proj_props p C v R hv hp F f hc N AA hFS σ hσ h' h'aug
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.Icc 1 (p ^ f - 1), ¬ v (proj (σ ^ m) h' t) < 1 := by
    by_contra hcon
    push Not at hcon
    apply h't
    rw [P2, Finset.sum_apply]
    exact v.map_sum_lt one_ne_zero hcon
  have hτ : IsFund p (σ ^ m) := by
    by_contra hnf
    have hpf := PositivityTheory.HtPt.Rb.proj_nf p C v R hv hp F f hc N AA hFS h' h'af (σ ^ m) hnf
    exact hm (hpv _ (PositivityTheory.HtPt.Rb.mem_pFun.1 hpf t))
  refine ⟨σ ^ m, hτ, ?_⟩
  have hgE : proj (σ ^ m) h' ∈ AA.carrier ∧ ∀ (a : F) x,
      proj (σ ^ m) h' (a • x) = algebraMap R C ((σ ^ m) a) * proj (σ ^ m) h' x := P1 (σ ^ m)
  have hgI := hinv _ (P4 K h'inv (σ ^ m))
  have hgA : proj (σ ^ m) h' ∈ afFun p AA.carrier := P3 h'af (σ ^ m)
  generalize proj (σ ^ m) h' = g at hgE hgI hgA hm
  obtain ⟨u, hu⟩ := hval g hgE.1 t
  have hvu : v (algebraMap R C u) = 1 := by
    rw [hu]
    exact le_antisymm (hle g hgE.1 t) (not_lt.1 hm)
  have huU : IsUnit u := by
    refine hv.isUnit_of_one (isUnit_iff_ne_zero.2 ?_) hvu
    intro h0
    rw [h0, map_zero] at hvu
    exact zero_ne_one hvu
  have hg0' : g 0 = 0 := by
    have e := hgE.2 0 0
    rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at e
  refine (Ideal.eq_top_iff_one _).2 ?_
  show ∃ G ∈ afFun p AA.carrier,
    (∀ (a : F) x, G (a • x) - algebraMap R C ((σ ^ m) a) * G x ∈ pInt (C := C) R p) ∧
    (∀ k ∈ K, G k ∈ pInt (C := C) R p) ∧ G t - algebraMap R C 1 ∈ pInt (C := C) R p
  refine ⟨(↑huU.unit⁻¹ : R) • g, (afFun p AA.carrier).smul_mem _ hgA, ?_, ?_, ?_⟩
  · intro a x
    have e : ((↑huU.unit⁻¹ : R) • g) (a • x) - algebraMap R C ((σ ^ m) a) *
        ((↑huU.unit⁻¹ : R) • g) x = 0 := by
      simp only [Pi.smul_apply, hgE.2 a x, Algebra.smul_def]
      ring
    rw [e]
    exact Submodule.zero_mem _
  · intro k hk
    have hgk : g k = 0 := by
      have e := hgI.2 0 k hk
      rwa [zero_add, hg0'] at e
    simp [hgk]
  · have e : ((↑huU.unit⁻¹ : R) • g) t - algebraMap R C 1 = 0 := by
      rw [Pi.smul_apply, Algebra.smul_def, ← hu, ← map_mul, huU.val_inv_mul, sub_self]
    rw [e]
    exact Submodule.zero_mem _
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem eigencomponents_scalars : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ g ∈ augIdeal AA.carrier, (∀ χ : MulChar F R, proj χ g ∈ eig AA.carrier χ) ∧ g = ∑ m ∈ Finset.Icc 1 (p ^ f - 1), proj (σ ^ m) g ∧ (g ∈ afFun p AA.carrier → ∀ χ : MulChar F R, proj χ g ∈ afFun p AA.carrier) ∧ (∀ K : Submodule F N, g ∈ invFun AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, proj χ g ∈ invFun AA.carrier K.toAddSubgroup) ∧ (g ∈ sqIdeal (augIdeal AA.carrier) → ∀ χ : MulChar F R, proj χ g ∈ sqIdeal (augIdeal AA.carrier)) :=
  @PositivityTheory.HtPt.Rb.proj_props

end GlobalTheory.CompanionTheory.Ar.GR
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
open PositivityTheory.HtPt.Ri in

theorem _root_.GlobalTheory.T.dual_hopf_order_gauss_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ ψ : AddChar F C, ψ ≠ 1 → ∀ AD : HopfOrder (C := C) R F, AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a : F => ψ (h * a)) → FStable (F := F) AD.carrier ∧ ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R, xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} → v (algebraMap R C c) * v (algebraMap R C cD) = v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) :=
  @_root_.PositivityTheory.HtPt.Ri.r_dual
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem orbit_map_pow {A B : Type} (e : A → B) (a : Equiv.Perm A) (b : Equiv.Perm B)
    (he : ∀ t, e (a t) = b (e t)) (n : ℕ) (t : A) : e ((a ^ n) t) = (b ^ n) (e t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he, ih]

theorem local_comparison_of_orbits : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  intro O _ _ _ K _ _ ι _ Sg _ _ P d p hp φ r s lie om hrel k hk Q hQ τ
  obtain ⟨Sg', hfin, e, φ', ⟨t0, ht0⟩, hcomm, hR⟩ := hrel τ
  subst ht0
  haveI : Fintype Sg' := Fintype.ofFinite Sg'
  obtain ⟨h, h1, h2⟩ := hR k hk Q hQ
  obtain ⟨La, hLa⟩ : ∃ La : Sg → ℝ, La = fun σ => ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := ⟨_, rfl⟩
  have hLa' : ∀ σ, La σ = ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := fun σ => by rw [hLa]
  have h1' : ∀ t, (((lie (e t)).ck P k Q : ℤ) : ℝ) + (((om (e t)).ck P k Q : ℤ) : ℝ)
      = h t - ((laNum P (p : O) (lie (e t)).x k Q : ℤ) : ℝ) / ((p : ℝ) - 1) := fun t => h1 t
  have h2' : ∀ t, (p : ℝ) ^ k * h t = h (φ' t) + La (e (φ' t)) := by
    intro t
    rw [hLa']
    exact h2 t
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have hpk0 : (p : ℝ) ^ k ≠ 0 := (zero_lt_one.trans hpk).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((p : ℝ) ^ k)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact inv_nonneg.mpr (zero_lt_one.trans hpk).le
  have hc1 : c < 1 := by
    rw [hc]
    exact inv_lt_one_of_one_lt₀ hpk
  have hrec : ∀ t, h t = c * (h (φ' t) + La (e (φ' t))) := by
    intro t
    rw [hc, ← h2' t, ← mul_assoc, inv_mul_cancel₀ hpk0, one_mul]
  have hpart : ∀ N t, h t = (∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t)))
      + c ^ N * h ((φ' ^ N) t) := by
    intro N
    induction N with
    | zero => intro t; simp
    | succ N ih =>
      intro t
      have hstep : φ' ((φ' ^ N) t) = (φ' ^ (N + 1)) t := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [ih t, Finset.sum_range_succ, hrec ((φ' ^ N) t), hstep]
      ring
  have hbd : ∀ f : Sg' → ℝ, ∀ t, |f t| ≤ ∑ u, |f u| := fun f t =>
    Finset.single_le_sum (f := fun u => |f u|) (fun u _ => abs_nonneg (f u)) (Finset.mem_univ t)
  have hsum : Summable (fun n : ℕ => c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0))) := by
    have hg : Summable (fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) := by
      refine ((summable_geometric_of_lt_one hc0 hc1).mul_left ((∑ u, |La (e u)|) * c)).congr
        (fun n => ?_)
      ring
    refine Summable.of_norm_bounded (g := fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) hg
      (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |La (e u)|)]
    exact mul_le_mul_of_nonneg_left (hbd (fun u => La (e u)) _) (pow_nonneg hc0 _)
  have hlim1 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hz : Filter.Tendsto (fun N : ℕ => c ^ N * h ((φ' ^ N) t0)) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun N : ℕ => (∑ u, |h u|) * c ^ N) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (∑ u, |h u|)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm (fun N => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |h u|)]
    exact mul_le_mul_of_nonneg_left (hbd h _) (pow_nonneg hc0 _)
  have hlim2 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (h t0)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => h t0) Filter.atTop (nhds (h t0)) := tendsto_const_nhds
    have := hconst.sub hz
    rw [sub_zero] at this
    refine this.congr (fun N => ?_)
    rw [hpart N t0]
    ring
  have hh : h t0 = ∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)) := tendsto_nhds_unique hlim2 hlim1
  have hh2 : h t0 = ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) (e t0)) := by
    rw [hh, hc]
    refine tsum_congr (fun n => ?_)
    rw [orbit_map_pow e φ' φ hcomm]
  have key := (co_series_three_step).1 Sg φ p k hp hk La (e t0)
  have final : (((lie (e t0)).ck P k Q : ℤ) : ℝ) + (((om (e t0)).ck P k Q : ℤ) : ℝ)
      = ∑ σ, GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (e t0) σ * La σ := by
    rw [key, h1' t0, hh2, hLa' (e t0)]
  subst hLa
  exact final

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

theorem _root_.GlobalTheory.T.invariant_open_chart_preimage : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ (V' : X.Opens), V' ≤ V → a ⁻¹ᵁ V' = b ⁻¹ᵁ V' → ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | exact GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

theorem _root_.GlobalTheory.T.chart_restrict_preimage_open : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V) (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme), IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue

theorem _root_.GlobalTheory.T.pullback_of_glued_charts : ∀ {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type} (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y') [∀ j, IsOpenImmersion (em j)], (∀ j, IsChart a b (V j) (q j)) → (∀ j, (V j).ι ≫ π = q j ≫ em j) → (∀ j, π ⁻¹ᵁ (em j).opensRange = V j) → (∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) → IsPullback a b π π := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart <;> assumption)
end
