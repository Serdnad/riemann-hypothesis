module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
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
import Mathlib.RingTheory.PiTensorProduct
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatIn

@[expose] public section

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum

variable (D : D7)

def cosetV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def congLev (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {k | k ∈ intG D N ∧ CongOne D 𝔪 k}

def blockLev (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : Subgroup (GA D d) :=
  Subgroup.closure {h | h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪}

variable {D}

def stdSum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ)
    (R : Finset (GA D a)) : VC D a d → ℂ :=
  ∑ r ∈ R, W.Om r 1 (cosetV D δ 𝔪 o a d e0)

theorem congLev_le (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : congLev D 𝔪 N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem blockLev_le (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : blockLev D 𝔪 d a ≤ intG D d :=
  (Subgroup.closure_le _).2 fun _ h => h.1

end GlobalTheory.FunObj.StdDatum

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

namespace GlobalTheory.FunObj.SqNum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem condE_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), condE P ⊔ D.host.conj • condE P = ⊤ := by
  intro D T L P
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hne : ∀ v ∈ P.S0, ∀ v' ∈ P.S0, (P.w v).asIdeal ≠ D.host.conj • (P.w v').asIdeal := by
    intro v hv v' hv' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv (P.w v') (P.w v) := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    by_cases e : v' = v
    · subst e
      obtain ⟨f, hf⟩ := P.w_split v' hv'
      exact GlobalTheory.GridChars.not_conjPl_self hf hcc hc
    · apply e
      have h1 := (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D)
        (P.w v') (P.w v)).2 (Or.inr hc)
      rw [P.under_w hv, P.under_w hv'] at h1
      exact h1.symm
  have hmax' : ∀ v, (D.host.conj • (P.w v).asIdeal).IsMaximal := by
    intro v
    have := (P.w v).isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v).ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  rw [condE, Finset.smul_prod']
  simp only [smul_pow']
  refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun v' hv' => ?_
  exact Ideal.pow_sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal (hmax' v') (hne v hv v' hv'))

end GlobalTheory.FunObj.SqNum
end
end

section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.CongSplitFactor

variable {D : D7} {N : ℕ}

noncomputable def phi (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D) :=
  e • A + (1 - e) • (1 : Matrix (Fin N) (Fin N) (AE D))

theorem phi_apply (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) (i j : Fin N) :
    phi e A i j = e * A i j + (1 - e) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
  simp [phi, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem phi_sub_one (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A - 1 = e • (A - 1) := by
  rw [phi, sub_smul, one_smul, smul_sub]; abel

theorem phi_one (e : AE D) : phi e (1 : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  rw [phi, ← add_smul, add_sub_cancel, one_smul]

theorem phi_mul {e : AE D} (he : e * e = e) (A B : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi e B = phi e (A * B) := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem phi_mul_compl {e : AE D} (he : e * e = e) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi (1 - e) A = A := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

noncomputable def phiHom {e : AE D} (he : e * e = e) :
    Matrix (Fin N) (Fin N) (AE D) →* Matrix (Fin N) (Fin N) (AE D) where
  toFun := phi e
  map_one' := phi_one e
  map_mul' A B := (phi_mul he A B).symm

theorem phi_map (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).map (sgA D) = phi (sgA D e) (A.map (sgA D)) := by
  ext i j
  simp only [Matrix.map_apply, phi_apply, map_add (f := _), map_mul, map_sub, map_one]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem phi_transpose (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).transpose = phi e A.transpose := by
  simp [phi, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem phi_mem_OhE {e : AE D} (he : e ∈ OhE D) {A : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : phi e A i j ∈ OhE D := by
  rw [phi_apply]
  refine add_mem (mul_mem he (hA i j)) (mul_mem (sub_mem (one_mem _) he) ?_)
  by_cases h : i = j
  · simp [Matrix.one_apply, h, one_mem]
  · simp [Matrix.one_apply, h, zero_mem]

theorem hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D 𝔪) {s : AE D}
    (hs : s ∈ OhE D) : s * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

noncomputable def part {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) : GA D N :=
  ⟨Units.map (phiHom he) (k : GL (Fin N) (AE D)), by
    rw [PtsMem.mem_GA]
    have hk := (PtsMem.mem_GA D (k : GL (Fin N) (AE D))).1 k.2
    show ((phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).map (sgA D)).transpose *
      phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1
    rw [phi_map, hse, phi_transpose, phi_mul he, hk, phi_one]⟩

theorem part_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_inv_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    ((((part he hse k : GA D N) : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) =
      phi e (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_intG {e : AE D} (he : e * e = e) (hse : sgA D e = e) (heO : e ∈ OhE D) {k : GA D N}
    (hk : k ∈ intG D N) : part he hse k ∈ intG D N := by
  rw [mem_intG] at hk ⊢
  intro i j
  refine ⟨?_, ?_⟩
  · rw [part_val]; exact phi_mem_OhE heO (fun a b => (hk a b).1) i j
  · rw [part_inv_val]; exact phi_mem_OhE heO (fun a b => (hk a b).2) i j

theorem part_sub_one_apply {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) (i j : Fin N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j =
      e * ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j) := by
  rw [← Matrix.sub_apply, part_val, phi_sub_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_split_inert_factor : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N},
    k ∈ intG D N → CongOne D 𝔪 k →
    ∃ ks ki : GA D N, k = ks * ki ∧ ks ∈ intG D N ∧ ki ∈ intG D N ∧ CongOne D 𝔪 ks ∧
      SuppSplit D (ks : GL (Fin N) (AE D)) ∧ SuppInert D (ki : GL (Fin N) (AE D)) := by
  intro D N 𝔪 k hk hc
  obtain ⟨ε, hεO, hεε, hεs, hq⟩ := VacMove.exists_half_idem D
  set e := ε + sgA D ε with he_def
  have heO : e ∈ OhE D := add_mem hεO (VacMove.sgA_mem D hεO)
  have hse : sgA D e = e := by rw [he_def, map_add (f := _), VacMove.sgA_sgA, add_comm]
  have hee : e * e = e := by
    have h2 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, hεε]
    have h3 : sgA D ε * ε = 0 := by rw [mul_comm, hεs]
    rw [he_def, add_mul, mul_add, mul_add, hεε, hεs, h3, h2, zero_add, add_zero]
  have hfO : 1 - e ∈ OhE D := sub_mem (one_mem _) heO
  have hsf : sgA D (1 - e) = 1 - e := by rw [map_sub, map_one, hse]
  have hff : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  refine ⟨part hee hse k, part hff hsf k, ?_, part_intG hee hse heO hk, part_intG hff hsf hfO hk,
    ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        phi (1 - e) ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    rw [phi_mul_compl hee]
  · intro i j
    show ((((part hee hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j ∈ hatId D 𝔪
    rw [Matrix.sub_apply, part_sub_one_apply]
    exact hatId_mul (hc i j) heO
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).1 hin) _
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).2 hin) _

end GlobalTheory.CongSplitFactor
end

section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSelfDual

open GlobalTheory.FunObj.SqNum

variable {D : D7}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

theorem star_eq_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_smul_conj_smul (𝔞 : Ideal (𝓞 D.host.E)) : D.host.conj • (D.host.conj • 𝔞) = 𝔞 := by
  rw [smul_smul]
  have : D.host.conj * D.host.conj = 1 := AlgEquiv.ext (VacMove.conj_conj D)
  rw [this, one_smul]

theorem conj_smul_ne_bot {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : D.host.conj • 𝔞 ≠ ⊥ := by
  intro h'
  apply h
  rw [← conj_smul_conj_smul 𝔞, h']
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

theorem coe_ne_zero {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : ((𝔞 : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem conj_mem_div {A B : Ideal (𝓞 D.host.E)} (hB : B ≠ ⊥) {x : D.host.E}
    (hx : x ∈ ((A : FI D) / (B : FI D))) :
    D.host.conj x ∈ (((D.host.conj • A : Ideal (𝓞 D.host.E)) : FI D) / ((D.host.conj • B : Ideal (𝓞 D.host.E)) : FI D)) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hB)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (conj_smul_ne_bot hB))]
  intro y hy
  obtain ⟨β, hβ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hβ' : D.host.conj • β ∈ B := by
    have := Ideal.smul_mem_pointwise_smul D.host.conj β _ hβ
    rwa [conj_smul_conj_smul] at this
  obtain ⟨α, hα, hαe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hβ', rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨D.host.conj • α, Ideal.smul_mem_pointwise_smul _ _ _ hα, ?_⟩
  have e1 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • α) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E α) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • β) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E β) := rfl
  rw [e1, hαe, e2, map_mul, VacMove.conj_conj]

theorem mem_skewLat {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (v : Fin N → D.host.E) :
    v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ ((𝔪 : FI D) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FI D)) := by
  simp [skewLat, Submodule.mem_pi]

theorem skewLat_SD {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : SD D (skewLat D 𝔪 N) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := conj_smul_ne_bot h𝔪
  have h𝔪𝔫 : D.host.conj • 𝔫 = 𝔪 := conj_smul_conj_smul 𝔪
  set I : FI D := (𝔪 : FI D) / (𝔫 : FI D) with hIdef
  set J : FI D := (𝔫 : FI D) / (𝔪 : FI D) with hJdef
  have hI0 : I ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hJ0 : J ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hJI : J * I = 1 := by
    rw [hIdef, hJdef, div_mul_div_comm, mul_comm (𝔫 : FI D), div_self]
    exact mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hIJ' : 1 / J = I := by rw [hJdef, hIdef, one_div_div]
  have cI : ∀ x ∈ I, D.host.conj x ∈ J := fun x hx => by
    have := conj_mem_div h𝔫0 hx
    rwa [h𝔪𝔫] at this
  have cJ : ∀ z ∈ J, D.host.conj z ∈ I := fun z hz => by
    have := conj_mem_div h𝔪 hz
    rwa [h𝔪𝔫] at this
  have memL : ∀ v : Fin N → D.host.E, v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ I := mem_skewLat
  letI := D.host.cmStar
  show IsSDLat D.host.E N (skewLat D 𝔪 N)
  refine ⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (I : Submodule (𝓞 D.host.E) D.host.E))
      (fun h => hI0 (FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i : Fin N, (Pi.single i a : Fin N → D.host.E) ∈ skewLat D 𝔪 N := fun i => by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    rw [Submodule.eq_top_iff']
    intro x
    have : x = ∑ i, (x i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · rw [memL] at hx hy
    unfold Formalism.BasicNotions.stdH
    refine Subring.sum_mem _ fun i _ => ?_
    have hm : star (x i) * y i ∈ J * I := by
      rw [star_eq_conj]
      exact FractionalIdeal.mul_mem_mul (cI _ (hx i)) (hy i)
    rw [hJI] at hm
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    exact ⟨a, ha⟩
  · rw [memL]
    intro i
    rw [← hIJ', FractionalIdeal.mem_div_iff_of_ne_zero hJ0]
    intro z hz
    have hx : (Pi.single i (D.host.conj z) : Fin N → D.host.E) ∈ skewLat D 𝔪 N := by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using cJ z hz
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    have h1 := h _ hx
    unfold Formalism.BasicNotions.stdH at h1
    have e : (∑ j, star ((Pi.single i (D.host.conj z) : Fin N → D.host.E) j) * y j) = y i * z := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, star_eq_conj, VacMove.conj_conj, mul_comm]
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    rw [e] at h1
    obtain ⟨a, ha⟩ := h1
    exact (FractionalIdeal.mem_one_iff _).2 ⟨a, ha⟩

end GlobalTheory.SkewLatSelfDual
end
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem isCoprime_of_natCast_mem {D : D7} {I : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : Nat.Coprime N (D.host.QS * D.host.q))
    (hI : (N : 𝓞 D.host.E) ∈ I) : IsCoprime I D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  exact GlobalTheory.HalfCompare.not_mem_of_coprime P hN (GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb))
    (hle (Ideal.mem_sup_left hI))

theorem coprime_of_mod {a b m : ℕ} (h : a % m = 1) (hb : b ∣ m) : Nat.Coprime a b := by
  have : Nat.Coprime a m := by rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact this.coprime_dvd_right hb

theorem exists_nat_mem_place_coprime {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ∃ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hg : ∀ k, Nat.Coprime (D.host.g k) (D.host.QS * D.host.q) := fun k =>
    coprime_of_mod (D.ntypes.g_cond k) (dvd_mul_right _ _)
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
  · exact ⟨q0 D, coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
      (Dvd.dvd.mul_left ⟨D.host.d, rfl⟩ _), P.basePlace_over_qZero⟩
  · rcases (S1_mem_OmF D).1 h1 with h' | h' | h' | h'
    · exact ⟨_, hg 0, h'⟩
    · exact ⟨_, hg 1, h'⟩
    · exact ⟨_, h.1, h'⟩
    · exact ⟨_, h.2, h'⟩

theorem exists_nat_mem_condE {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ N : ℕ, Nat.Coprime N (D.host.QS * D.host.q) ∧ (N : 𝓞 D.host.E) ∈ SqNum.condE P := by
  classical
  choose! p hp hm using fun v (hv : v ∈ P.S0) => exists_nat_mem_place_coprime P h hv
  refine ⟨∏ v ∈ P.S0, p v ^ condExp P v, Nat.Coprime.prod_left fun v hv => (hp v hv).pow_left _, ?_⟩
  unfold SqNum.condE
  push_cast
  refine Ideal.prod_mem_prod fun v hv => Ideal.pow_mem_pow ?_ _
  have h1 : ((p v : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by
    rw [P.under_w hv]; exact hm v hv
  simpa using Ideal.mem_comap.1 h1

theorem condE_isCoprime_halfDifferent {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    IsCoprime (SqNum.condE P) D.host.𝔟 ∧ IsCoprime (D.host.conj • SqNum.condE P) D.host.𝔟 := by
  obtain ⟨N, hN, hm⟩ := exists_nat_mem_condE P h
  refine ⟨isCoprime_of_natCast_mem hN hm, isCoprime_of_natCast_mem hN ?_⟩
  have h1 := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  have h2 : D.host.conj • (N : 𝓞 D.host.E) = N := map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) N
  rwa [h2] at h1

end GlobalTheory.FunObj.StdDatum.HalfDiff

end
end
