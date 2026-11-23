module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CosetTheta

variable {D : D7}

theorem homL_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ homL D L L₁) : M • A ∈ homL D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    refine Submodule.subset_span fun x hx => ?_
    rw [Matrix.smul_mulVec]
    exact hM _ (hA x hx)
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

theorem YYl_nsmul_mem {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ YYl D L L₁) : M • A ∈ YYl D L L₂ := by
  induction hA using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M • A, homL_nsmul_mem M hM hA, smul_comm _ _ _⟩
  | zero => simp
  | add A B _ _ hA hB => rw [smul_add]; exact add_mem hA hB
  | smul c A _ hA => rw [smul_comm]; exact Submodule.smul_mem _ c hA

theorem La_nsmul_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (M : ℕ) (hM : ∀ y ∈ L₁, M • y ∈ L₂)
    {x : VC D N N'} (hx : x ∈ La D (tor0 D cc δ) L L₁) : M • x ∈ La D (tor0 D cc δ) L L₂ := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨w, hw, M • A, YYl_nsmul_mem M hM hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem skewLat_nsmul_le (𝔫 : Ideal (𝓞 D.host.E)) (h : D.host.conj • 𝔫 ≠ ⊥) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ skewLat D 𝔫 N, M • y ∈ stdL D N := by
  refine ⟨Ideal.absNorm (D.host.conj • 𝔫), Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using h),
    fun y hy => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  rw [Pi.smul_apply]
  have hyi := hy i
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero
    (by simpa using h)] at hyi
  have hmem := hyi (algebraMap (𝓞 D.host.E) D.host.E (Ideal.absNorm (D.host.conj • 𝔫) : 𝓞 D.host.E))
    ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.absNorm_mem _, rfl⟩)
  obtain ⟨x', -, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  rw [Submodule.mem_one]
  refine ⟨x', ?_⟩
  rw [hx', nsmul_eq_mul, mul_comm, map_natCast]

end GlobalTheory.BotPairSmall.CosetTheta

namespace GlobalTheory.BotPairSmall.CosetTheta

theorem iop_mem_TT {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {B : AddSubgroup (VC D a d)} {M : ℕ} (hM : 0 < M)
    (hB : ∀ x ∈ B, M • x ∈ La0 D (tor0 D ⊤ δ) a d) {e0 : VC D a d → ℂ} (heT : e0 ∈ TT D (tor0 D ⊤ δ) a d) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) B e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  set T := tor0 D ⊤ δ
  set A := La0 D T a d
  have h0 : (0 : VC D a d → ℂ) ∈ TT D T a d := by
    have := hlc.2.2.2 0 e0 heT
    rwa [zero_smul] at this
  by_cases hfin : Finite (B ⧸ A.addSubgroupOf B)
  · haveI := Fintype.ofFinite (B ⧸ A.addSubgroupOf B)
    have e : Iop D T A B e0 = ∑ q : B ⧸ A.addSubgroupOf B,
        ((((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) * al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) e0) := by
      funext z
      simp only [Iop, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Wd]
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
      field_simp
    rw [e]
    refine Finset.sum_induction _ (· ∈ TT D T a d) (fun F G hF hG => hlc.2.2.1 F hF G hG) h0 fun q _ => ?_
    exact hlc.2.2.2 _ _ (GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT hc hM (hB _ (Quotient.out q : B).2) heT)
  · have hi : (A.addSubgroupOf B).index = 0 :=
      AddSubgroup.index_eq_zero_iff_infinite.2 (not_finite_iff_infinite.1 hfin)
    have e : Iop D T A B e0 = 0 := by
      funext z
      simp [Iop, hi]
    rw [e]; exact h0

end GlobalTheory.BotPairSmall.CosetTheta

theorem GlobalTheory.BotPairSmall.cvec_conj_mem_TT : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), GlobalTheory.BotPairSmall.cvec D δ (D.host.conj • 𝔪) o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho
  have hlc := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have s0 := VacMove.sd_of_moves (VacMove.moves_one D a)
  have s0' := VacMove.sd_of_moves (VacMove.moves_one D d)
  have heT : e0 ∈ TT D (tor0 D ⊤ δ) a d := hlc.1 _ _ s0 s0' e0 hv.1
  have hne : D.host.conj • (D.host.conj • 𝔪) ≠ ⊥ :=
    GlobalTheory.BotPairSmall.conj_smul_ne_bot D (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm)
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.BotPairSmall.CosetTheta.skewLat_nsmul_le (D := D) (D.host.conj • 𝔪) hne d
  have hI := GlobalTheory.BotPairSmall.CosetTheta.iop_mem_TT hc hM
    (fun x hx => GlobalTheory.BotPairSmall.CosetTheta.La_nsmul_mem (L := stdL D a) ⊤ δ M hMs hx) heT
  unfold GlobalTheory.BotPairSmall.cvec
  exact hlc.2.2.2 _ _ (hlc.2.1 _ _ hI)
end
end

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {s x : AE D} (hs : s ∈ OhE D) (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem mem_hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {s x : AE D} (hs : s ∈ OhE D) (hx : x ∈ hatId D 𝔪) :
    x * s ∈ hatId D 𝔪 := by
  rw [mul_comm]; exact mul_mem_hatId hs hx

theorem congOne_mul {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k k' : GA D N} (hk' : k' ∈ intG D N)
    (h : CongOne D 𝔪 k) (h' : CongOne D 𝔪 k') : CongOne D 𝔪 (k * k') := by
  intro i j
  have hi := (mem_intG k').1 hk'
  have e : (((k * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) *
        ((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) +
      ((((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) := by
    simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  exact add_mem (sum_mem fun l _ => mem_hatId_mul (hi l j).1 (h i l)) (h' i j)

theorem congOne_inv {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k : GA D N} (hk : k ∈ intG D N)
    (h : CongOne D 𝔪 k) : CongOne D 𝔪 k⁻¹ := by
  intro i j
  have hi := (mem_intG k).1 hk
  have e : (((k⁻¹ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      -((((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1)) := by
    rw [Subgroup.coe_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [e, Matrix.neg_apply, Matrix.mul_apply]
  exact neg_mem (sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j))

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : GA D N) := by
  intro i j
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]
  exact zero_mem _

theorem mem_congLev_iff : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (k : GA D N),
    k ∈ congLev D 𝔪 N ↔ k ∈ intG D N ∧ CongOne D 𝔪 k := by
  intro D 𝔪 N k
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem _, congOne_one 𝔪 N⟩
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, congOne_mul hy.1 hx.2 hy.2⟩
  | inv x _ hx => exact ⟨inv_mem hx.1, congOne_inv hx.1 hx.2⟩

end GlobalTheory.FunObj.StdDatum

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.CongIdx

variable {D : D7}

theorem inc_int_mem (a : 𝓞 D.host.E) : inc D (a : D.host.E) ∈ OhE D :=
  Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem ohE_approx (N : ℕ) (hN : 1 ≤ N) (x : AE D) (hx : x ∈ OhE D) :
    ∃ a ∈ Formalism.UG.intOE D.host.E, ∃ z ∈ OhE D, x = inc D a + (N : AE D) * z := by
  first
  | exact @_root_.GlobalTheory.AdeleTensorModule.main
  | exact _root_.GlobalTheory.AdeleTensorModule.main
  | (apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdeleTensorModule.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdeleTensorModule.main ..)

theorem exists_rep {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {x : AE D} (hx : x ∈ OhE D) :
    ∃ a : 𝓞 D.host.E, x - inc D (a : D.host.E) ∈ hatId D 𝔪 := by
  have hN : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  obtain ⟨a0, ⟨a, rfl⟩, z, hz, e⟩ := ohE_approx _ hN x hx
  refine ⟨a, ?_⟩
  have e2 : x - inc D (algebraMap (𝓞 D.host.E) D.host.E a) = (Ideal.absNorm 𝔪 : AE D) * z := by
    rw [e]; ring
  have e3 : inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) = (Ideal.absNorm 𝔪 : AE D) := by
    simp
  rw [show ((a : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E a from rfl, e2, ← e3]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, z, hz, rfl⟩

theorem inv_mul_mem {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k k' : GA D N} (hk : k ∈ intG D N) (hk' : k' ∈ intG D N)
    (h : ∀ i j, ((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k⁻¹ * k' ∈ congLev D 𝔪 N := by
  refine Subgroup.subset_closure ⟨mul_mem (inv_mem hk) hk', fun i j => ?_⟩
  have hi := (mem_intG k).1 hk
  have e : (((k⁻¹ * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) := by
    rw [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  rw [e, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j)

end GlobalTheory.CongIdx


open GlobalTheory.CongIdx in
theorem GlobalTheory.congLev_relIndex_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    (congLev D 𝔪 N).relIndex (intG D N) ≠ 0 ∧ (congLev D 𝔪 N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 N
  classical
  have hrep : ∀ x : AE D, ∃ a : 𝓞 D.host.E, x ∈ OhE D → x - inc D (a : D.host.E) ∈ hatId D 𝔪 := fun x => by
    by_cases hx : x ∈ OhE D
    · obtain ⟨a, ha⟩ := exists_rep h𝔪 hx
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hrep
  let f : intG D N → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := fun k i j =>
    Ideal.Quotient.mk 𝔪 (r ((((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j))
  let g : intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q => f q.out
  have hg : Function.Injective g := by
    intro q1 q2 h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hk := (q1.out).2
    have hk' := (q2.out).2
    refine (show ((q1.out⁻¹ * q2.out : intG D N) : GA D N) = (q1.out : GA D N)⁻¹ * q2.out from rfl) ▸
      inv_mul_mem hk hk' fun i j => ?_
    have h1 := hr _ ((mem_intG _).1 hk i j).1
    have h2 := hr _ ((mem_intG _).1 hk' i j).1
    have h3 : r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) -
        r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ 𝔪 :=
      Ideal.Quotient.eq.1 (congr_fun (congr_fun h i) j).symm
    have h4 : inc D (((r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) -
        r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) : 𝓞 D.host.E) : D.host.E)) * 1 ∈
        hatId D 𝔪 := AddSubgroup.subset_closure ⟨_, h3, 1, one_mem _, rfl⟩
    have h5 := add_mem (sub_mem h2 h1) h4
    convert h5 using 1
    push_cast
    simp only [map_sub, mul_one]
    ring
  have hfin : Ideal.absNorm 𝔪 ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 h𝔪
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  haveI : Finite (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := Finite.of_injective g hg
  have hle := Nat.card_le_card_of_injective g hg
  rw [Nat.card_fun, Nat.card_fun, hcard, Nat.card_fin, ← pow_mul] at hle
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · calc (congLev D 𝔪 N).relIndex (intG D N) = Nat.card (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := rfl
      _ ≤ _ := hle
      _ = _ := by rw [sq]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.BotFormula

theorem toFinE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = GlobalTheory.CuspRep.conjFin (D.host.conj : D.host.E ≃+* D.host.E) (toFinE D y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul x a =>
    change GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] D.host.conj x) =
      GlobalTheory.CuspRep.conjFin _ (GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ[ℚ] x))
    rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_mul,
      GlobalTheory.DefU.ClassFin.conjFin_adMap _ (fun q => D.host.conj.commutes q), GlobalTheory.CuspRep.conjFin_algebraMap]
    rfl

def toAfE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D ≃+* TensorProduct D.host.F (Af D.host.F) D.host.E :=
  (toFinE D).trans (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm

theorem toAfE_sgA (D : D7) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    toAfE D (Formalism.MainNotions.StandardLatticesGL3.sgA D y) = sigR (Af D.host.F) D.sp.cm.sig (toAfE D y) := by
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun x => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D x)]
  simp only [toAfE, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  exact toFinE_sgA D y

theorem exists_isFinPt_of_gram_one : ∀ {D : D7} (WW : HSp D), WW.gram = 1 → ∀ {n : ℕ} (h : GA D n), WW.rank = n →
    ∃ g : GA D WW, GlobalTheory.BotFormula.IsFinPt WW g h := by
  intro D WW hG n h hr
  subst hr
  let x' : GL (Fin WW.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := Formalism.UG.bc (toAfE D).toRingHom h.1
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * h.1 = 1 := by
    have h2 := h.2
    change Formalism.UG.cT _ (h.1 : Matrix (Fin WW.rank) (Fin WW.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hx' : x' ∈ HR (Af D.host.F) D.sp.cm.sig WW.gram := by
    show Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) *
      JR (Af D.host.F) WW.gram * (x' : Matrix (Fin WW.rank) (Fin WW.rank) _) = JR (Af D.host.F) WW.gram
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact GlobalTheory.DefU.ClassFin.unitary_map (toAfE D).toRingHom (Formalism.MainNotions.StandardLatticesGL3.sgA D) _ (toAfE_sgA D) _ hh
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue WW 1 x' (one_mem _) hx'
  refine ⟨k, k1, rfl, fun i j => ?_⟩
  rw [k2]
  exact (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply _

end GlobalTheory.BotFormula
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix

namespace GlobalTheory.BotRealInv

theorem substF_minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (H : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) (fun τ => (H τ)ᵀ) (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (H τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF (rfl : a = a) (rfl : d = d) T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  have one : ∀ (τ : D.what₂.Tau) (s : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) (fun τ => (H τ)ᵀ)
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (H τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, s i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ s
    rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_transpose ((MvPolynomial.C : ℂ →+* _).mapMatrix (H τ)), mul_comm,
      ← Matrix.det_mul]
    congr 1
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, GlobalTheory.CompactHowe.substF_X,
      RingHom.mapMatrix_apply, Matrix.transpose_apply]
    rw [Finset.sum_eq_single (s i)]
    · simp only [Matrix.one_apply_eq, one_mul]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [GlobalTheory.NormSum.minorPol, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod]
  simp only [one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

theorem succ_mul_succ_sub_one_div_succ {G : Type*} [CommGroup G] (a e c : G) : a * e / (c * e) = a / c := mul_div_mul_right_eq_div _ _ _

end GlobalTheory.BotRealInv

end
end
