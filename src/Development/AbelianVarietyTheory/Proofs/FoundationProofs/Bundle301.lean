module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle295
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormSqExpHermSubOneLeBlockMat
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OfDualFamilies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle186
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem branchesAlong_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N) (lam : DomWeight N)
    (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0) :
    BranchesAlong ι h lam := by
  classical
  have iso : Nonempty ((sumRep ι h lam).Equiv (resRep ι h lam)) := by
    refine GlobalTheory.nonempty_directSum_equiv_of_finrank_le ℂ H (Below h lam) _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1) _
      (fun mu => hirr mu.1) (fun i j hij => hz i.1 j.1 fun e => hij (Subtype.ext e)) (fun mu => ?_) (GlobalTheory.Branching.finrank_le_finrank_directSum_below n N h lam)
    obtain ⟨φ, hφ⟩ := GlobalTheory.Branching.exists_intertwining_ne_zero n N h lam mu.1 mu.2
    refine ⟨⟨φ.toLinearMap, fun y => φ.isIntertwining' (ι y)⟩, fun e => hφ ?_⟩
    have e' := congrArg Representation.IntertwiningMap.toLinearMap e
    exact Representation.IntertwiningMap.ext e'
  refine ⟨iso, fun mu => ?_⟩
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).1
  have h0 : ∀ nu : DomWeight n, mu ≠ nu →
      Module.finrank ℂ ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι mu).IntertwiningMap (smallRep ι nu)) :=
      ⟨fun a b => (hz mu nu hne a).trans (hz mu nu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · unfold mult
    rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e.symm)
    · simp
  · unfold mult
    rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem intertwining_unitary_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (unitaryIncl n) mu).IntertwiningMap (smallRep (unitaryIncl n) nu)) : φ = 0 := by
  have := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Branching.exists_ne_zero_map_eq_zero_of_weight_ne n mu nu hne
    ⟨φ.toLinearMap, fun g => LinearMap.ext fun f => GlobalTheory.Branching.intertwining_gl_of_unitary n mu nu φ g f⟩
  refine (Representation.IsIrreducible.injective_or_eq_zero φ).resolve_left fun hi => hf (hi ?_)
  rw [map_zero]; exact h0

theorem isIrreducible_smallRep_id (n : ℕ) (mu : DomWeight n) : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  let r : Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu) → Subrepresentation (smallRep (unitaryIncl n) mu) :=
    fun S => ⟨S.toSubmodule, fun u _ hv => S.apply_mem_toSubmodule (unitaryIncl n u) hv⟩
  have hnt : Nontrivial (Subrepresentation (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (r S) with e | e
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inl (Subrepresentation.ext e')
  · have e' := congrArg Subrepresentation.toSubmodule e
    exact Or.inr (Subrepresentation.ext e')

theorem intertwining_id_eq_zero (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu).IntertwiningMap (smallRep (MonoidHom.id (GL (Fin n) ℂ)) nu)) :
    φ = 0 := by
  have := intertwining_unitary_eq_zero n mu nu hne ⟨φ.toLinearMap, fun u => φ.isIntertwining' (unitaryIncl n u)⟩
  have e' := congrArg Representation.IntertwiningMap.toLinearMap this
  exact Representation.IntertwiningMap.ext e'

theorem branchesAlong_all (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) :
    BranchesAlong (MonoidHom.id (GL (Fin n) ℂ)) h lam ∧ BranchesAlong (unitaryIncl n) h lam :=
  ⟨branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n),
    branchesAlong_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n)⟩

theorem comult_of_irreducible {H : Type} [Group H] {n N : ℕ} (ι : H →* GL (Fin n) ℂ) (h : n + 1 = N)
    (lam : DomWeight N) (hirr : ∀ mu : DomWeight n, (smallRep ι mu).IsIrreducible)
    (hz : ∀ mu nu : DomWeight n, mu ≠ nu → ∀ φ : (smallRep ι mu).IntertwiningMap (smallRep ι nu), φ = 0)
    (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep ι h lam).IntertwiningMap (smallRep ι mu)) = 0) := by
  classical
  have iso := (branchesAlong_of_irreducible ι h lam hirr hz).1
  letI : Fintype (Below h lam) := Fintype.ofFinite _
  have hm := (GlobalTheory.IntertwinerSum.finrank_intertwiningMap_directSum ℂ H (Below h lam) _ _ (fun mu => nablaSq ℂ n mu.1) (fun mu => smallRep ι mu.1)
    (smallRep ι mu) (resRep ι h lam) iso).2
  have h0 : ∀ nu : DomWeight n, nu ≠ mu →
      Module.finrank ℂ ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) = 0 := fun nu hne => by
    have : Subsingleton ((smallRep ι nu).IntertwiningMap (smallRep ι mu)) :=
      ⟨fun a b => (hz nu mu hne a).trans (hz nu mu hne b).symm⟩
    exact Module.finrank_zero_of_subsingleton
  refine ⟨fun hI => ?_, fun hI => ?_⟩
  · rw [hm, Finset.sum_eq_single (⟨mu, hI⟩ : Below h lam)]
    · have := hirr mu
      exact Representation.IsIrreducible.finrank_intertwiningMap_self _
    · intro b _ hb
      exact h0 b.1 fun e => hb (Subtype.ext e)
    · simp
  · rw [hm]
    exact Finset.sum_eq_zero fun b _ => h0 b.1 fun e => hI (e ▸ b.2)

theorem comult_id (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
        (smallRep (MonoidHom.id (GL (Fin n) ℂ)) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_id n) (intertwining_id_eq_zero n) mu

theorem comult_unitary (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) :
    (Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 1) ∧
      (¬ Interlace h lam mu → Module.finrank ℂ ((resRep (unitaryIncl n) h lam).IntertwiningMap
        (smallRep (unitaryIncl n) mu)) = 0) :=
  comult_of_irreducible _ h lam (isIrreducible_smallRep_unitary n) (intertwining_unitary_eq_zero n) mu

end GlobalTheory.Branching

namespace GlobalTheory.Published

theorem weylBranching_holds : WeylBranching := fun n N h _ lam => GlobalTheory.Branching.branchesAlong_all n N h lam

end GlobalTheory.Published
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem _root_.GlobalTheory.T.sum_norm_sq_exp_herm_sub_one_le_blockMat : ∀ (p q : ℕ) (H H' : Mat p q), Hᴴ = H → H'ᴴ = H' → ∑ a, ∑ b, ‖(NormedSpace.exp (-(Complex.I • H')) * NormedSpace.exp (Complex.I • H) - 1) a b‖ ^ 2 ≤ ∑ a, ∑ b, ‖(H - H') a b‖ ^ 2 := by
  first | exact @GlobalTheory.CartanLip.exp_mul_exp_sub_one_le | exact GlobalTheory.CartanLip.exp_mul_exp_sub_one_le | (intros; apply GlobalTheory.CartanLip.exp_mul_exp_sub_one_le <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ConjNorm.Inter

open GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)

  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  have hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨c, -, rfl⟩ := hw; exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨k', rfl⟩ := hb
      exact ⟨k + k', by simp [mul_add]⟩
    | neg a _ ha =>
      obtain ⟨k, rfl⟩ := ha
      exact ⟨-k, by simp⟩
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, -, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hl w hw
    exact ⟨k • B, by rw [embV_smul h, smul_smul]⟩
  | zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨B', rfl⟩ := hb
    exact ⟨B + B', by rw [embV_add, smul_add]⟩
  | neg a _ ha =>
    obtain ⟨B, rfl⟩ := ha
    exact ⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  have hA' := hA
  obtain ⟨S, hS, hAS⟩ := klat_gen hA'
  have hB : B ∈ Submodule.span D.host.K S := hS ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB =>
    refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩
    rw [hAS]
    refine AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ,
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩
    rw [← smul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨1, one_pos, by simp [embV_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, ha⟩ := ha
    obtain ⟨n, hn, hb⟩ := hb
    refine ⟨m * n, by positivity, ?_⟩
    rw [embV_add, smul_add, smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem ha _
    · rw [mul_smul]; exact A.nsmul_mem hb _
  | smul k B _ hB =>
    obtain ⟨m, hm, hB⟩ := hB
    obtain ⟨n, hn, hk⟩ := exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)
    have hk' : IsIntegral ℤ (n.natAbs • k) := by
      have := hk k (Finset.mem_singleton_self k)
      rcases Int.natAbs_eq n with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    refine ⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩
    convert klat_smul_mem hA ⟨_, hk'⟩ hB using 1
    rw [embV_smul h]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    change _ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _
    simp
    ring

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ConjNorm.Line.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ConjNorm.Inter


open GlobalTheory.ThetaInter GlobalTheory.ConjNorm.Inter in
theorem GlobalTheory.ConjNorm.unitary_all : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := klat_facts hc h₂
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GalExist

theorem exists_sum_of_mem_La (D : D7) (T : Tor D) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (y : VC D N N') (hy : y ∈ La D T L L') :
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Fin r → ℂ),
      (∀ j, b j ∈ YYl D L L') ∧ (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  first
  | exact @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | (apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum ..)

theorem galEx_of_galStar (D : D7) (hS : galStar D) : galEx D := by
  intro cc δ hc M ρ hK hD hM N N' L L' _ _ x n hx hn
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨r, b, w, hb, hw, hsum⟩ := exists_sum_of_mem_La D _ L L' _ hmx
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw' : ∀ j, w j ∈ lamOf D cc δ := hw
  have hmul : ∀ j, ((m * n : ℕ) : ℂ) * (w j / m / n) ∈ lamOf D cc δ := by
    intro j
    have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
    rw [this]; exact hw' j
  have hex : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
    intro j
    have hq : InRationalLattice (lamOf D cc δ) (w j / m / n) := ⟨m * n, Nat.mul_pos hm hn, hmul j⟩
    refine h1 _ hq ?_
    by_cases h : w j / m / n ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  choose t' ht' using hex
  refine ⟨∑ j, ((n : ℂ) * t' j) • embV D (torConj D (tor0 D cc δ) M ρ) (b j),
    ⟨r, b, fun j => w j / m, fun j => (n : ℂ) * t' j, hb, ?_, ?_, rfl, ?_⟩, m, hm, ?_⟩
  · intro j
    refine ⟨m, hm, ?_⟩
    have : (m : ℂ) * (w j / m) = w j := by field_simp
    rw [this]; exact hw j
  · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [hx, hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← div_eq_inv_mul]
  · intro j
    have : (n : ℂ) * t' j / n = t' j := by field_simp
    show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
    rw [this]; exact ht' j
  · rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    refine AddSubgroup.subset_closure ⟨((m * n : ℕ) : ℂ) * t' j, (h6 _ _ _ (ht' j)).1 (hmul j), b j, hb j, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast; ring

theorem galEx_all : ∀ D : D7, galEx D := fun D => galEx_of_galStar D (GlobalTheory.T.galStar_complexMultiplication_points D)

end GlobalTheory.GalExist
end
