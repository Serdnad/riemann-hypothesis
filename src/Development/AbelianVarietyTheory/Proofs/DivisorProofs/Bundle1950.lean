module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors
open GlobalTheory.InertSign

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem exists_nat_mul_mem_one (𝔪 : Ideal (𝓞 D.host.E)) : ∃ M : ℕ, 0 < M ∧ ∀ y : D.host.E,
    y ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) →
    (M : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪
  by_cases h : 𝔫 = ⊥
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have h0 : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
      rw [h]; exact FractionalIdeal.coeIdeal_bot
    rw [h0, div_zero, FractionalIdeal.coe_zero, Submodule.mem_bot] at hy
    rw [hy, mul_zero]; exact Submodule.zero_mem _
  · refine ⟨Ideal.absNorm 𝔫, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
    have hM : ((Ideal.absNorm 𝔫 : ℕ) : D.host.E) ∈ ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨(Ideal.absNorm 𝔫 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔫, by simp⟩
    have hne : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hm := FractionalIdeal.mul_mem_mul hy hM
    rw [div_mul_cancel₀ _ hne] at hm
    have h1 := FractionalIdeal.coeIdeal_le_one (I := 𝔪) (P := D.host.E) hm
    rw [mul_comm]
    rwa [FractionalIdeal.mem_one_iff, ← Submodule.mem_one] at h1

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem skewLat_smul (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d := by
  obtain ⟨M, hM, h⟩ := exists_nat_mul_mem_one (D := D) 𝔪
  refine ⟨M, hM, fun v hv => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro i
  have := h _ (hv i)
  simpa [Pi.smul_apply, Algebra.smul_def] using this

theorem homL_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    homL D (stdL D a) (skewLat D 𝔪 d) ≤ (homL D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun A hA => ?_
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  refine Submodule.subset_span fun x hx => ?_
  have e : ((M : 𝓞 D.host.E) • A).mulVec x = (M : 𝓞 D.host.E) • A.mulVec x := by
    funext i; simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]
  rw [e]
  exact hM _ (hA x hx)

theorem YYl_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    YYl D (stdL D a) (skewLat D 𝔪 d) ≤ (YYl D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun B hB => ?_
  obtain ⟨c, hc, A, hA, rfl⟩ := hB
  have hA' := homL_smul (a := a) hM hA
  simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  rw [Nat.cast_smul_eq_nsmul] at hA' ⊢
  rw [smul_comm]
  exact Submodule.subset_span ⟨c, hc, _, hA', rfl⟩

theorem la_skew_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d), M • x ∈ La0 D (tor0 D cc δ) a d := by
  obtain ⟨M, hM0, hM⟩ := skewLat_smul (D := D) 𝔪 d
  refine ⟨M, hM0, fun x hx => ?_⟩
  have key : La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d) ≤
      (La0 D (tor0 D cc δ) a d).comap (DistribSMul.toAddMonoidHom (VC D a d) M) := by
    refine (AddSubgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    have hA' := YYl_smul (a := a) hM hA
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
    refine AddSubgroup.subset_closure ⟨w, hw, _, hA', ?_⟩
    funext τ i j
    simp [embV, tor0, Algebra.smul_def, nsmul_eq_mul]
    ring
  exact key hx

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem sd_stdL (n : ℕ) : SD D (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
  rw [← h2]; exact (h1 _).2

theorem wd_mem_TT_of_nsmul {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {x : VC D a d}
    {M : ℕ} (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) a d) {F : VC D a d → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) a d) : Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) a d := by
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) := Or.inr ⟨_, _, sd_stdL a, sd_stdL d, rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  obtain ⟨hd, m, hm, hF⟩ := hF
  refine ⟨GlobalTheory.ThetaLevels.wd_entire D _ _ hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have hmy := AddSubgroup.nsmul_mem _ hy m
  have h1 : bc D (tor0 D cc δ) ((m * M) • y) x = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_left, ← GlobalTheory.ThetaLevels.bc_nsmul_right]
    exact n0.2.1 _ hmy _ hx
  have h2 : bc D (tor0 D cc δ) x ((m * M) • y) = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_right, ← GlobalTheory.ThetaLevels.bc_nsmul_left]
    exact n0.2.1 _ hx _ hmy
  have h3 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hy M)
  have h4 := Wd_Wd D (tor0 D cc δ) x ((m * M) • y) F
  rw [h3, h2, add_comm] at h4
  rw [Wd_Wd, h1, h4]

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ}
    (B : AddSubgroup (VC D a d)) (hB : ∀ x ∈ B, ∃ M : ℕ, 0 < M ∧ M • x ∈ La0 D (tor0 D cc δ) a d)
    {F : VC D a d → ℂ} (hF : F ∈ TT D (tor0 D cc δ) a d) :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) B F ∈ TT D (tor0 D cc δ) a d := by
  set T := tor0 D cc δ
  set A := La0 D T a d
  by_cases hn : (A.addSubgroupOf B).index = 0
  · have h0 : Iop D T A B F = 0 := by funext z; simp [Iop, hn]
    rw [h0]; exact (GlobalTheory.FinWeil.TTs D T a d).zero_mem
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero hn
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    have hI : Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
        ∑ q : B ⧸ A.addSubgroupOf B, (al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) F := by
      funext z
      simp only [Iop, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have h0 : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := Complex.exp_ne_zero _
      simp only [Wd]
      rw [mul_assoc, inv_mul_cancel_left₀ h0]
    rw [hI]
    refine (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ (Submodule.sum_mem _ fun q _ => (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ ?_)
    obtain ⟨M, hM, hx⟩ := hB _ (Quotient.out q : B).2
    exact wd_mem_TT_of_nsmul hc hM hx hF

theorem cosetV_mem_TT : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ →
    ∀ (o a d : ℕ) (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
      cosetV D δ 𝔪 o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ hc 𝔪 _ o a d e0 he
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D (tor0 D ⊤ δ) a d := hT.1 _ _ (sd_stdL a) (sd_stdL d) e0 he
  obtain ⟨M, hM, hx⟩ := la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hI := iop_mem_TT hc (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) (fun x hx' => ⟨M, hM, hx x hx'⟩) he'
  exact hT.2.2.2 _ _ (hT.2.1 _ _ hI)

end GlobalTheory.FunObj.CosetTT
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def finRepl (v : Pl (F := F)) (z : κ → Af F) (x : κ → Fv F v) : κ → Af F :=
  fun i => z i - GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) + GlobalTheory.AdelicU.singleFin v (x i)

def finProj (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (g : (κ → Af F) → ℂ) :
    (κ → Af F) → ℂ :=
  fun z => φ₀ (fun i => evalV F v (z i)) * l fun x => g (finRepl v z x)

theorem evalV_finRepl (v : Pl (F := F)) (z : κ → Af F) (x : κ → Fv F v) (i : κ) :
    evalV F v (finRepl v z x i) = x i := by
  simp [finRepl, GlobalTheory.AdelicU.evalV_singleFin_self]

theorem finRepl_finRepl (v : Pl (F := F)) (z : κ → Af F) (x : κ → Fv F v) :
    finRepl v (finRepl v z x) (fun i => evalV F v (z i)) = z := by
  funext i
  have := evalV_finRepl v z x i
  simp only [finRepl] at this ⊢
  rw [this]; abel

theorem continuous_finRepl (v : Pl (F := F)) :
    Continuous fun p : (κ → Af F) × (κ → Fv F v) => finRepl v p.1 p.2 := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.1 i := (continuous_apply i).comp continuous_fst
  have h2 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.2 i := (continuous_apply i).comp continuous_snd
  exact (h1.sub ((GlobalTheory.AdelicU.continuous_singleFin v).comp ((RestrictedProduct.continuous_eval v).comp h1))).add
    ((GlobalTheory.AdelicU.continuous_singleFin v).comp h2)

theorem finProj_mem_SB [Fintype κ] (v : Pl (F := F)) {φ₀ : (κ → Fv F v) → ℂ} (hφ₀ : φ₀ ∈ SB (κ → Fv F v))
    (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    finProj v φ₀ l g ∈ SB (κ → Af F) := by
  have : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have he : Continuous fun z : κ → Af F => fun i => evalV F v (z i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hs : Continuous fun z : κ → Af F => fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) :=
    continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp
      ((RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro z₀
    let δ : (κ → Af F) → (κ → Af F) := fun z =>
      (z₀ - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z₀ i))) -
        (z - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)))
    have hδ : Filter.Tendsto δ (nhds z₀) (nhds 0) := by
      have hc : Continuous δ := continuous_const.sub (continuous_id.sub hs)
      simpa [δ] using hc.tendsto z₀
    have hφe : ∀ᶠ z in nhds z₀, φ₀ (fun i => evalV F v (z i)) = φ₀ (fun i => evalV F v (z₀ i)) :=
      (hφ₀.1.comp_continuous he).eventually_eq z₀
    filter_upwards [hδ.eventually (GlobalTheory.SBConv.eventually_translate hg), hφe] with z hz h1
    simp only [finProj]
    rw [h1]
    congr 2
    funext x
    have e : finRepl v z x = finRepl v z₀ x - δ z := by
      funext i; simp only [finRepl, δ, Pi.sub_apply]; abel
    rw [e, hz]
  · refine HasCompactSupport.intro ((hg.2.isCompact.prod hφ₀.2.isCompact).image (continuous_finRepl v)) ?_
    intro z hz
    by_contra h
    apply hz
    simp only [finProj] at h
    have h1 : φ₀ (fun i => evalV F v (z i)) ≠ 0 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    obtain ⟨x, hx⟩ : ∃ x, g (finRepl v z x) ≠ 0 := by
      by_contra hc
      push Not at hc
      apply h2
      have : (fun x => g (finRepl v z x)) = 0 := funext hc
      rw [this, map_zero]
    refine ⟨(finRepl v z x, fun i => evalV F v (z i)), ⟨subset_tsupport _ hx, subset_tsupport _ h1⟩, ?_⟩
    exact finRepl_finRepl v z x

theorem proj_pureA [Fintype κ] (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    proj v φ₀ l (pureA F f g) = pureA F f (finProj v φ₀ l g) := by
  funext y
  have e : (fun x => pureA F f g (repl v y x)) =
      f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) • fun x => g (finRepl v (fun i => (y i).2) x) := by
    funext x
    have a1 : ∀ i, (repl v y x i).1 = (y i).1 := fun i => by
      show (y i).1 - (0 : Ainf F) + 0 = (y i).1
      rw [sub_zero, add_zero]
    have a2 : ∀ i, (repl v y x i).2 = finRepl v (fun i => (y i).2) x i := fun i => rfl
    show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (repl v y x i).1) * g (fun i => (repl v y x i).2) = _
    simp only [a1, a2, Pi.smul_apply, smul_eq_mul]
  rw [proj_apply, e, map_smul]
  simp only [pureA, finProj, smul_eq_mul]
  change φ₀ (fun i => evalV F v (y i).2) * _ = _
  ring

theorem proj_schA_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  intro F _ _ κ _ v φ₀ hφ₀ l
  refine ⟨fun Φ hΦ => ?_, fun L hL => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      rw [proj_pureA]
      exact Submodule.subset_span ⟨f, _, finProj_mem_SB v hφ₀ l hg, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · intro g hg
    obtain ⟨T, hT⟩ := hL _ (finProj_mem_SB v hφ₀ l hg)
    exact ⟨T, fun f => by rw [LinearMap.comp_apply, proj_pureA, hT]⟩

end GlobalTheory.MixedForm

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.IndOSelf

open ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

local instance borelFvAt (v : Pl (F := F)) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem mem_int_iff {v : Pl (F := F)} (x : Fv F v) : x ∈ 𝒪[Fv F v] ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem exists_nat_mul_mem (v : Pl (F := F)) (x : Fv F v) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : Fv F v) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · have h1 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc
    rw [map_mul, map_natCast] at h1
    rw [← h1, mul_assoc, mul_comm _ x]
    exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v c) hbx

theorem norm_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem v x
  have h1 : GlobalTheory.LatVac.psiAt ψ v ((N : Fv F v) * x) = 1 := by
    have := ((hψ 1).2 (one_mem _)) _ hx
    rwa [one_mul] at this
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  exact Complex.norm_eq_one_of_pow_eq_one h1 hN

def psiC (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) : AddChar (Fv F v) Circle where
  toFun x := ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (norm_psiAt ψ v hψ x)⟩
  map_zero_eq_one' := Subtype.ext (AddChar.map_zero_eq_one _)
  map_add_eq_mul' x y := Subtype.ext (AddChar.map_add_eq_mul _ x y)

theorem coe_psiC (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ((psiC ψ v hψ x : Circle) : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := rfl

theorem hasConductor_psiC (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.HasConductor (psiC ψ v hψ) 1 := by
  intro x
  have e1 : ∀ y, psiC ψ v hψ y = 1 ↔ GlobalTheory.LatVac.psiAt ψ v y = 1 := fun y =>
    ⟨fun h => by rw [← coe_psiC ψ v hψ, h]; rfl, fun h => Circle.ext (by rw [coe_psiC ψ v hψ, h]; rfl)⟩
  rw [Units.val_one, map_one, ← Valuation.mem_integer_iff, mem_int_iff, ← hψ x]
  simp only [e1]
  constructor
  · intro h y hy
    apply h
    rw [map_mul]
    have : valuation (Fv F v) y ≤ 1 := (Valuation.mem_integer_iff _ _).1 ((mem_int_iff y).2 hy)
    exact mul_le_of_le_one_right' this
  · intro h y hy
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, le_zero_iff, map_eq_zero] at hy
      subst hy
      exact AddChar.map_zero_eq_one _
    · have hyx : y / x ∈ v.adicCompletionIntegers F := by
        rw [← mem_int_iff, Valuation.mem_integer_iff, map_div₀,
          div_le_one₀ (by rw [zero_lt_iff, Ne, map_eq_zero]; exact hx)]
        exact hy
      have := h _ hyx
      rwa [mul_div_cancel₀ _ hx] at this

theorem indO_mem_SB (v : Pl (F := F)) (κ : Type) [Fintype κ] : GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef
  have hS : S = Set.univ.pi fun _ => ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [S, mem_int_iff]
  have hc : IsCompact S := hS ▸ isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int _
  have ho : IsOpen S := hS ▸ isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_int _
  have hcl : IsClosed S := hc.isClosed
  have hind : GlobalTheory.SympChange.indO (κ := κ) v = S.indicator 1 := rfl
  rw [hind]
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ S
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem exists_selfDual (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) :
    ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv F v)
  have h := GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν (hasConductor_psiC ψ v hψ) hν
  exact ⟨ν, h.1, fun f hf => h.2 f hf⟩

theorem isUnitVol_measV (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.IsUnitVol (measV ψ v) := by
  have hex := exists_selfDual ψ v hψ
  have hm : measV ψ v = hex.choose := by simp only [measV, dif_pos hex]
  have hs := hex.choose_spec
  rw [hm]
  exact (GlobalTheory.SplitWeil.isUnitVol_iff_isSelfDual (hasConductor_psiC ψ v hψ) _).2 ⟨hs.1, fun f hf => hs.2 f hf⟩

theorem fourV_indO (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) (hψ : PsiUnr ψ v) (κ : Type) [Fintype κ] :
    fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v := by
  classical
  have hU := isUnitVol_measV ψ v hψ
  haveI := hU.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have hball : GlobalTheory.SplitWeil.cball (1 : (Fv F v)ˣ) = ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [GlobalTheory.SplitWeil.cball, Valuation.mem_integer_iff]
  have hbox : GlobalTheory.SplitWeil.FourierPi.box κ (1 : (Fv F v)ˣ) = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    ext x; simp [GlobalTheory.SplitWeil.FourierPi.box, hball, ← mem_int_iff]
  have hvol : (Measure.pi fun _ : κ => measV ψ v).real (GlobalTheory.SplitWeil.FourierPi.box κ 1) = 1 := by
    simp [Measure.real, GlobalTheory.SplitWeil.FourierPi.box, Measure.pi_pi, hball, hU.2]
  funext y
  have h := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi (Measure.pi fun _ : κ => measV ψ v)
    (hasConductor_psiC ψ v hψ) 1 y
  rw [mul_inv_cancel, hvol, hbox] at h
  exact h

theorem indO_self_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F))
    (κ : Type) [Fintype κ], GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  intro F _ _ ψ _ v κ _
  exact ⟨indO_mem_SB v κ, fun h => fourV_indO ψ v h κ⟩

end GlobalTheory.WeylFour.IndOSelf
end
end
