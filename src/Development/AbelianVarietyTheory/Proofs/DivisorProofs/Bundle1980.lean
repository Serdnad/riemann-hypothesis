module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1935
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewLatticeMoverWithDeterminant
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.TransExp

theorem hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    Hf D T y x = (starRingEnd ℂ) (Hf D T x y) := by

  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem wd_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ)
    (z : VC D N N') : Wd D T x (Wd D T y F) z = Formalism.MainNotions.TaylorLogMetric.kap D T x y * Wd D T y (Wd D T x F) z := by
  have key : Complex.exp (-(Real.pi : ℂ) * Hf D T x y) =
      Formalism.MainNotions.TaylorLogMetric.kap D T x y * Complex.exp (-(Real.pi : ℂ) * Hf D T y x) := by
    rw [Formalism.MainNotions.TaylorLogMetric.kap, ← Complex.exp_add, hf_swap D T x y]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  have e1 : ∀ u v c : ℂ, Complex.exp (-(Real.pi : ℂ) * (u + v) - c) =
      Complex.exp (-(Real.pi : ℂ) * u - c) * Complex.exp (-(Real.pi : ℂ) * v) := by
    intro u v c; rw [← Complex.exp_add]; congr 1; ring
  simp only [Wd, U, VacMove.hf_add_left]
  rw [show z + y + x = z + x + y from add_right_comm _ _ _, e1 (Hf D T z y) (Hf D T x y),
    e1 (Hf D T z x) (Hf D T y x), key]
  ring

theorem wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type*} (x : VC D N N') (c : ℂ) (s : Finset ι)
    (f : ι → VC D N N' → ℂ) (z : VC D N N') :
    Wd D T x (fun w => c * ∑ q ∈ s, f q w) z = c * ∑ q ∈ s, Wd D T x (f q) z := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem wd_iop_of (D : D7) (T : Tor D) {N N' : ℕ} (A B : AddSubgroup (VC D N N')) (e0 : VC D N N' → ℂ)
    (x : VC D N N') (hB : ∀ y ∈ B, ∀ F, Wd D T y F = fun z => al D T y * U D T y F z)
    (hfix : Wd D T x e0 = e0) :
    Wd D T x (Iop D T A B e0) = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Formalism.MainNotions.TaylorLogMetric.kap D T x ((Quotient.out q : B) : VC D N N') *
        Wd D T ((Quotient.out q : B) : VC D N N') e0 z := by
  have hI : Iop D T A B e0 = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') e0 z := by
    funext z
    unfold Iop
    congr 1
    refine finsum_congr fun q => ?_
    rw [hB _ (Quotient.out q).2]
  funext z
  rw [hI]
  by_cases h0 : (A.addSubgroupOf B).index = 0
  · simp [Wd, U, h0]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h0
    haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    simp only [finsum_eq_sum_of_fintype]
    rw [wd_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [wd_comm, hfix]

theorem wd_iop_expand : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), Wd D (tor0 D ⊤ δ) x (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = fun z => ((Real.sqrt (((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index : ℝ))⁻¹ : ℂ) * ∑ᶠ q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) * Wd D (tor0 D ⊤ δ) ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) e0 z := by
  intro D δ hc 𝔪 h𝔪 a d e0 he x hx
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D a), GlobalTheory.T.selfDualSkewIdealLattice_isSelfDual D 𝔪 d h𝔪, rfl⟩
  exact wd_iop_of D _ _ _ e0 x (GlobalTheory.T.theta_space_selfDual_pair_at_most_line D h1 ⊤ δ hc a d _ kp).2.1 (VacMove.wd_fix h1 hc k0 he hx)

end GlobalTheory.FunObj.TransExp
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_ideal_matrix_congr_adelicMatrix_mod_nat : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (Y : Matrix (Fin d) (Fin a) (AE D)),
    (∀ i j, Y i j ∈ hatId D 𝔪) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E,
      (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ ∀ i j, ∃ y ∈ IhE D ⊤, (w.map (inc D) - Y) i j = (m : AE D) * y := by
  first | exact @GlobalTheory.FunObj.CosetApprox.matrix_approx | exact GlobalTheory.FunObj.CosetApprox.matrix_approx | (intros; apply GlobalTheory.FunObj.CosetApprox.matrix_approx <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall.CongApprox

theorem approx_two_moduli : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)), 𝔫 ≠ ⊥ → ∀ (a d : ℕ) (M : Matrix (Fin d) (Fin a) (AE D)) (m : ℕ), 0 < m → ∃ z : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, ∃ y ∈ IhE D ⊤, (z.map (inc D) - M) i l = (m : AE D) * y) ∧ ∀ i l, (M - z.map (inc D)) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 h𝔫 a d M m hm
  obtain ⟨n, hn, hnI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D ⊤
  have hN : 0 < Ideal.absNorm 𝔫 := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨z, hz⟩ := GlobalTheory.NormSum.VacMove.MI_approx (D := D) (cc := ⊤) top_ne_bot M (m * (n * Ideal.absNorm 𝔫))
    (Nat.mul_pos hm (Nat.mul_pos hn hN))
  refine ⟨z, GlobalTheory.NormSum.VacMove.MI.of_dvd (dvd_mul_right m _) hz, fun i l => ?_⟩
  obtain ⟨y, hy, e⟩ := hz i l
  have hny : (n : AE D) * y ∈ OhE D := hnI y hy
  have hmny : (m : AE D) * ((n : AE D) * y) ∈ OhE D := mul_mem (natCast_mem _ m) hny
  have h2 := GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔫 hmny
  have e2 : (M - z.map (inc D)) i l = -((Ideal.absNorm 𝔫 : AE D) * ((m : AE D) * ((n : AE D) * y))) := by
    rw [← neg_sub, Matrix.neg_apply, e]; push_cast; ring
  rw [e2]
  exact neg_mem h2

end GlobalTheory.BotPairSmall.CongApprox
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

theorem GlobalTheory.card_congRep_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (a : ℕ) (R : Finset (GA D a)), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → R.card ≤ Ideal.absNorm 𝔪 ^ (a ^ 2) := by
  intro D 𝔪 h𝔪 a R hR huniq
  classical
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 a
  let Q := intG D a ⧸ (congLev D 𝔪 a).subgroupOf (intG D a)
  haveI : Finite Q := Nat.finite_of_card_ne_zero hne
  let f : R → Q := fun r => QuotientGroup.mk (⟨(r : GA D a), hR r r.2⟩ : intG D a)
  have hf : Function.Injective f := by
    rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : r⁻¹ * r' ∈ congLev D 𝔪 a := h1
    have h3 := ((mem_congLev_iff D 𝔪 a _).1 h2).2
    have h4 : CongOne D 𝔪 (r'⁻¹ * r') := by
      rw [inv_mul_cancel]; exact congOne_one 𝔪 a
    obtain ⟨s, -, hs⟩ := huniq r' (hR r' hr')
    have e1 := hs r ⟨hr, h3⟩
    have e2 := hs r' ⟨hr', h4⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  calc R.card ≤ Nat.card Q := hc
    _ = (congLev D 𝔪 a).relIndex (intG D a) := rfl
    _ ≤ _ := hle

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.IdemChoice

open GlobalTheory.FunObj.StdDatum

theorem exists_idem_of_limit : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  intro hB1 D 𝔪 hsup δ u hδu
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have gen : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → ∀ {y : AE D}, y ∈ OhE D → inc D (b : D.host.E) * y ∈ hatId D 𝔫 :=
    fun {b} hb {y} hy => AddSubgroup.subset_closure ⟨b, hb, y, hy, rfl⟩
  have gen1 : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → inc D (b : D.host.E) ∈ hatId D 𝔫 := fun hb => by
    simpa using gen hb (one_mem (OhE D))
  by_cases hδ : δ = 0
  · subst hδ
    refine ⟨0, zero_mem _, 0, zero_mem _, by simp, by simp, by simp, ?_⟩
    have : inc D ((0 * u : 𝓞 D.host.E) : D.host.E) - 1 = -1 := by simp
    rw [this] at hδu
    simpa using neg_mem hδu
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ 𝔫 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have h𝔫0 : 𝔫 ≠ ⊥ := by
    intro e
    have h𝔪 : 𝔪 = ⊥ := by
      by_contra h
      exact GlobalTheory.BotPairSmall.conj_smul_ne_bot D h e
    rw [e, h𝔪, sup_bot_eq] at hsup
    exact bot_ne_top hsup
  set x : 𝓞 D.host.E := s * δ * u with hx
  set X : AE D := inc D (x : D.host.E) with hX
  have hXO : X ∈ OhE D := GlobalTheory.CongIdx.inc_int_mem x

  have h1X : 1 - X ∈ hatId D 𝔫 := by
    have e : 1 - X = inc D (t : D.host.E) + inc D (s : D.host.E) * (-(inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1)) := by
      have e1 : inc D (s : D.host.E) + inc D (t : D.host.E) = 1 := by
        rw [← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
      rw [hX, hx]
      push_cast
      simp only [map_mul]
      linear_combination -e1
    rw [e]
    exact add_mem (gen1 ht) (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.CongIdx.inc_int_mem s) (neg_mem hδu))

  have hxm : x ∈ 𝔪 := by rw [hx, mul_assoc]; exact Ideal.mul_mem_right _ _ hs
  have hsX : sgA D X ∈ hatId D 𝔫 := by
    rw [hX, GlobalTheory.NormSum.PtsMem.sgA_inc]
    exact gen1 (Ideal.smul_mem_pointwise_smul _ _ _ hxm)
  have hsXO : sgA D X ∈ OhE D := VacMove.sgA_mem D hXO

  have hN₁ : 0 < Ideal.absNorm (Ideal.span {δ}) := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hδ
  have hN₂ : 0 < Ideal.absNorm 𝔫 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫0
  set N := Ideal.absNorm (Ideal.span {δ}) * Ideal.absNorm 𝔫 with hN
  have hNδ : (N : 𝓞 D.host.E) ∈ Ideal.span {δ} := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hN𝔫 : (N : 𝓞 D.host.E) ∈ 𝔫 := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hNδ
  have hNinc : (N : AE D) = inc D ((N : 𝓞 D.host.E) : D.host.E) := by simp
  obtain ⟨e, heO, hee, hlim⟩ := hB1 D x
  obtain ⟨n, hn, w, hwO, hew⟩ := hlim N (Nat.mul_pos hN₁ hN₂)
  set ē := sgA D e with hē
  have hēO : ē ∈ OhE D := VacMove.sgA_mem D heO
  have hēē : ē * ē = ē := by rw [hē, ← map_mul, hee]
  refine ⟨e * (1 - ē), mul_mem heO (sub_mem (one_mem _) hēO), ?_⟩

  have hXd : X = inc D (δ : D.host.E) * inc D ((s * u : 𝓞 D.host.E) : D.host.E) := by
    rw [hX, hx, ← map_mul]; congr 1; push_cast; ring
  have hNd : (N : AE D) = inc D (δ : D.host.E) * inc D (c : D.host.E) := by
    rw [hNinc, ← hc, ← map_mul]; congr 1; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hed : e = inc D (δ : D.host.E) *
      (inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) := by
    rw [hew, pow_succ, hNd, ← hX]
    linear_combination X ^ m * hXd
  refine ⟨(inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) * (1 - ē),
    mul_mem (add_mem (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) (pow_mem hXO m))
      (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) hwO)) (sub_mem (one_mem _) hēO), ?_, ?_, ?_, ?_⟩
  · linear_combination (1 - ē) ^ 2 * hee + e * hēē
  · have hs2 : sgA D (e * (1 - ē)) = ē * (1 - e) := by
      rw [map_mul, map_sub, map_one, hē, GlobalTheory.NormSum.VacMove.sgA_sgA]
    rw [hs2]
    linear_combination (-(1 - ē) * ē) * hee
  · conv_lhs => rw [hed]
    ring
  ·
    have e1 : 1 - e * (1 - ē) = (1 - X ^ (m + 1)) - (N : AE D) * w + e * ē := by rw [hew, ← hX]; ring
    rw [e1]
    refine add_mem (sub_mem ?_ ?_) ?_
    · rw [← mul_neg_geom_sum]
      rw [mul_comm]
      exact GlobalTheory.CongIdx.mul_mem_hatId (sum_mem fun i _ => pow_mem hXO i) h1X
    · rw [hNinc]; exact gen hN𝔫 hwO
    · refine GlobalTheory.CongIdx.mul_mem_hatId heO ?_
      rw [hē, hew, ← hX, map_add (f := _), map_pow, map_mul, pow_succ, map_natCast]
      refine add_mem ?_ ?_
      · exact GlobalTheory.CongIdx.mul_mem_hatId (pow_mem hsXO m) hsX
      · rw [hNinc]; exact gen hN𝔫 (VacMove.sgA_mem D hwO)

end GlobalTheory.BotPairSmall.IdemChoice
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongApprox

theorem inc_mem_OhE (D : D7) (x : 𝓞 D.host.E) : inc D (x : D.host.E) ∈ OhE D :=
  Formalism.UG.P.easyc_inclE_mem _ _ _ (RingHom.mem_range.2 ⟨x, rfl⟩)

theorem exists_int_approx (D : D7) (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ b : 𝓞 D.host.E, ∃ w ∈ OhE D, s = inc D (b : D.host.E) + (n : AE D) * w := by
  rw [← GlobalTheory.AdelicApprox.levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨b, t, ht, h⟩

theorem OhE_le_IhE_top (D : D7) (s : AE D) (hs : s ∈ OhE D) : s ∈ IhE D ⊤ := by
  have h := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ s hs
  simpa [Ideal.absNorm_top] using h

theorem mul_mem_hatId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (x : AE D) (hx : x ∈ OhE D)
    (t : AE D) (ht : t ∈ hatId D 𝔪) : x * t ∈ hatId D 𝔪 := by
  unfold hatId at ht ⊢
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (t : AE D)
    (ht : t ∈ hatId D 𝔪) :
    ∃ b ∈ 𝔪, ∃ y ∈ IhE D ⊤, inc D (b : D.host.E) - t = (m : AE D) * y := by
  unfold hatId at ht
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    obtain ⟨c, w, hw, hsw⟩ := exists_int_approx D m hm s hs
    refine ⟨b * c, Ideal.mul_mem_right c 𝔪 hb, -(inc D (b : D.host.E) * w),
      OhE_le_IhE_top D _ (neg_mem (mul_mem (inc_mem_OhE D b) hw)), ?_⟩
    rw [hsw]
    push_cast
    rw [map_mul]
    ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    obtain ⟨b', hb', u', hu', h'⟩ := hy'
    refine ⟨b + b', add_mem hb hb', u + u', add_mem hu hu', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination h + h'
  | neg y _ hy =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    refine ⟨-b, neg_mem hb, -u, neg_mem hu, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -h

end GlobalTheory.CongApprox

namespace GlobalTheory.CongApprox

theorem exists_closeTo_congOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  intro D 𝔪 _ a d k hk hcong z _ m hm
  have hinv : CongOne D 𝔪 k⁻¹ := congOne_inv hk hcong
  set K : Matrix (Fin a) (Fin a) (AE D) := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  set T : Matrix (Fin d) (Fin a) (AE D) := z.map (inc D) * (K - 1) with hT
  have hTmem : ∀ i j, T i j ∈ hatId D 𝔪 := by
    intro i j
    rw [hT, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    obtain ⟨b, hb⟩ := ‹∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)› i l
    rw [Matrix.map_apply, hb]
    exact mul_mem_hatId D 𝔪 _ (inc_mem_OhE D b) _ (hinv l j)
  choose b hb y hy hby using fun i j => exists_mem_approx D 𝔪 m hm (T i j) (hTmem i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have hKinv : (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = K := by
    rw [hK, Subgroup.coe_inv]
  have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
  have hzK : z.map (inc D) * K = z.map (inc D) + T := by
    rw [hT, Matrix.mul_sub, Matrix.mul_one]; abel
  have key : ∀ i j, ((z + Matrix.of fun i j => (b i j : D.host.E)).map (inc D) -
      (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * z.map (inc D) *
        (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j =
      inc D (b i j : D.host.E) - T i j := by
    intro i j
    rw [e1, Matrix.one_mul, hKinv, hzK, Matrix.map_add _ (map_add (inc D))]
    simp [Matrix.map_apply]
  unfold CloseTo
  exact fun i j => ⟨y i j, hy i j, (key i j).trans (hby i j)⟩

end GlobalTheory.CongApprox
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

theorem _root_.GlobalTheory.T.finprod_nu_values_twist_only_ramified_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T), ∏ᶠ (w : HeightOneSpectrum (𝓞 D.host.E)) (_ : ¬ (Lc.xiH t).UnrAt w ∧ (nuH G μ₀ i j).UnrAt w), (((nuH G μ₀ i j).val w : ℂˣ) : ℂ) = 1 := by
  first | exact @GlobalTheory.TwistPairs.finprod_val_nu_eq_one | exact GlobalTheory.TwistPairs.finprod_val_nu_eq_one | (intros; apply GlobalTheory.TwistPairs.finprod_val_nu_eq_one <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.latticeIntertwiner_standard_to_skew_mem_thetaSpace : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (𝔪 : Ideal (𝓞 D.host.E)), SD D (skewLat D 𝔪 d) → Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈ ThSp D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) := by
  first | exact @GlobalTheory.SkewTheta.iop_mem_thSp | exact GlobalTheory.SkewTheta.iop_mem_thSp | (intros; apply GlobalTheory.SkewTheta.iop_mem_thSp <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.index_standard_inf_skewThetaLattice_eq_absNorm_pow : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  first | exact @GlobalTheory.SkewIndex.index_inter_skew | exact GlobalTheory.SkewIndex.index_inter_skew | (intros; apply GlobalTheory.SkewIndex.index_inter_skew <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_skew_lattice_mover_with_determinant : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ d : ℕ,
    ∃ (g' : GA D d) (x' : (AE D)ˣ), SuppSplit D (g' : GL (Fin d) (AE D)) ∧ Moves D (g' : GL (Fin d) (AE D)) (skewLat D 𝔪 d) ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x' : AE D) - 1)) ∧
      x' = Matrix.GeneralLinearGroup.det (g' : GL (Fin d) (AE D)) * sgU D x' ∧ ∀ h : GA D d, h * g' = g' * h := by
  first | exact @GlobalTheory.SkewCentral.exists_central_skew_move | exact GlobalTheory.SkewCentral.exists_central_skew_move | (intros; apply GlobalTheory.SkewCentral.exists_central_skew_move <;> assumption)
end
