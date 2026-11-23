module

public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle039
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalRingCardinality.DataHost
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026

@[expose] public section

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocArith

variable {l : ℕ} [Fact l.Prime]

theorem v_nonneg_iff (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) :
    0 ≤ P.v LL y ↔ ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := by
  rw [P.v_O]
  exact GlobalTheory.mem_integralClosure_padicInt_iff LL.1 y

theorem norm_natCast_prime : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_eq_one_of_v_eq_zero (P : LocPrime l) (LL : FinExt l) (y : ↥LL.1) (hy : P.v LL y = 0) :
    ‖((y : ↥LL.1) : Om l)‖ = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hy
    exact WithTop.top_ne_zero hy
  have h1 : ‖((y : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL y).1 (hy ▸ le_rfl)
  have hinv : P.v LL y⁻¹ = 0 := by
    have h := (P.v LL).map_mul y y⁻¹
    rw [mul_inv_cancel₀ hy0, AddValuation.map_one, hy, zero_add] at h
    exact h.symm
  have h2 : ‖((y⁻¹ : ↥LL.1) : Om l)‖ ≤ 1 := (v_nonneg_iff P LL _).1 (hinv ▸ le_rfl)
  have hc : ((y : ↥LL.1) : Om l) ≠ 0 := by simpa using hy0
  have hpos : 0 < ‖((y : ↥LL.1) : Om l)‖ := norm_pos_iff.2 hc
  rw [IntermediateField.coe_inv, norm_inv, inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h2

theorem norm_of_v_eq (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (r : ℚ)
    (hx : P.v LL x = ((r : ℚ) : WithTop ℚ)) :
    ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(r : ℝ)) := by
  set n := r.den with hn
  set a := r.num.toNat with ha
  set b := (-r.num).toNat with hb
  have hkab : (r.num : ℚ) = (a : ℚ) - (b : ℚ) := by
    have : r.num = (a : ℤ) - (b : ℤ) := by simp [ha, hb]
    exact_mod_cast this
  have hnr : (n : ℚ) * r = (a : ℚ) - b := by rw [mul_comm, hn, Rat.mul_den_eq_num, hkab]
  have hL0 : ((l : ℕ) : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := x ^ n * (l : ↥LL.1) ^ b / (l : ↥LL.1) ^ a with hy
  have hya : y * (l : ↥LL.1) ^ a = x ^ n * (l : ↥LL.1) ^ b := div_mul_cancel₀ _ (pow_ne_zero _ hL0)
  have hvy : P.v LL y = 0 := by
    have h := congrArg (P.v LL) hya
    rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
      AddValuation.map_pow, P.v_l, hx] at h
    have e1 : (n • ((r : ℚ) : WithTop ℚ)) = (((n : ℚ) * r : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_nsmul, nsmul_eq_mul]
    have e2 : ∀ m : ℕ, m • (1 : WithTop ℚ) = (((m : ℚ) : ℚ) : WithTop ℚ) := fun m => by
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
    rw [e1, e2, e2, hnr] at h
    by_cases ht : P.v LL y = ⊤
    · rw [ht, WithTop.top_add] at h
      exact absurd h.symm (WithTop.coe_ne_top)
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
      rw [← hs] at h ⊢
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at h
      have : s = 0 := by linarith
      rw [this, WithTop.coe_zero]
  have hN := congrArg (fun z : ↥LL.1 => ‖((z : ↥LL.1) : Om l)‖) hya
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow,
    norm_mul, norm_pow] at hN
  have hc : (((l : ℕ) : ↥LL.1) : Om l) = ((l : ℕ) : Om l) := map_natCast (IntermediateField.val LL.1) l
  rw [norm_eq_one_of_v_eq_zero P LL y hvy, hc, norm_natCast_prime] at hN
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn0 : n ≠ 0 := r.den_nz
  have hxn : ‖((x : ↥LL.1) : Om l)‖ ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [inv_pow, inv_pow, one_mul] at hN
    have hb0 : (0 : ℝ) < (l : ℝ) ^ b := pow_pos hpos b
    have ha0 : (0 : ℝ) < (l : ℝ) ^ a := pow_pos hpos a
    field_simp at hN ⊢
    linarith
  have hrn : ((l : ℝ) ^ (-(r : ℝ))) ^ n = (l : ℝ) ^ b / (l : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    have : -(r : ℝ) * (n : ℝ) = (b : ℝ) - (a : ℝ) := by
      have h2 : ((n : ℚ) * r : ℚ) = (a : ℚ) - b := hnr
      have h3 : ((n : ℝ) * (r : ℝ)) = (a : ℝ) - b := by exact_mod_cast h2
      linarith
    rw [this, Real.rpow_sub hpos, Real.rpow_natCast, Real.rpow_natCast]
  rw [← hrn] at hxn
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpos.le _) hn0).1 hxn

theorem v_eq_iff (P : LocPrime l) (LL : FinExt l) (x : ↥LL.1) (q : ℚ) :
    P.v LL x = ((q : ℚ) : WithTop ℚ) ↔ ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  refine ⟨norm_of_v_eq P LL x q, fun h => ?_⟩
  have hpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (l : ℝ) ^ (-(q : ℝ)) := Real.rpow_pos_of_pos hpos _
    simp at h
    linarith
  have ht : P.v LL x ≠ ⊤ := fun ht => hx0 ((P.v LL).top_iff.1 ht)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ht
  have h2 := norm_of_v_eq P LL x s hs.symm
  rw [h2] at h
  have hqs : (q : ℝ) = (s : ℝ) := by
    have := le_antisymm ((Real.rpow_le_rpow_left_iff hl1).1 h.le) ((Real.rpow_le_rpow_left_iff hl1).1 h.ge)
    linarith
  rw [← hs, show q = s by exact_mod_cast hqs]

theorem arithTied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), Formalism.L2.ArithTied P := fun l _ P =>
  ⟨fun LL x q => v_eq_iff P LL x q⟩

end GlobalTheory.LocArith
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.PsiExist

section General

variable {L : Type} [Field L] [NumberField L]


theorem trivOn_pow {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F) (n : ℕ) :
    (χ ^ n).TrivOn F := by
  induction n with
  | zero => rw [pow_zero, ← mul_inv_cancel χ]; exact h.mul h.inv
  | succ n ih => rw [pow_succ]; exact ih.mul h


end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)



end GlobalTheory.Mem.PsiExist
end
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConjugateType

def ConjSp (E : Type) : Type := E

namespace ConjSp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

instance : NormedAddCommGroup (ConjSp E) := inferInstanceAs (NormedAddCommGroup E)

def out (x : ConjSp E) : E := x

def mk (x : E) : ConjSp E := x

instance : Module ℂ (ConjSp E) := Module.compHom E (starRingEnd ℂ)

instance : NormedSpace ℂ (ConjSp E) where
  norm_smul_le z x := by
    show ‖starRingEnd ℂ z • out x‖ ≤ ‖z‖ * ‖out x‖
    rw [norm_smul, RCLike.norm_conj]

instance : InnerProductSpace ℂ (ConjSp E) where
  inner x y := inner ℂ (out y) (out x)
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (out x)
  conj_inner_symm x y := inner_conj_symm (𝕜 := ℂ) (out y) (out x)
  add_left x y z := inner_add_right (𝕜 := ℂ) (out z) (out x) (out y)
  smul_left x y r := inner_smul_right (𝕜 := ℂ) (out y) (out x) (starRingEnd ℂ r)

def mkL (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : E →ₛₗ[starRingEnd ℂ] ConjSp E where
  toFun := mk
  map_add' _ _ := rfl
  map_smul' z x := by
    show z • x = starRingEnd ℂ (starRingEnd ℂ z) • x
    rw [Complex.conj_conj]

instance [FiniteDimensional ℂ E] : FiniteDimensional ℂ (ConjSp E) :=
  Module.Finite.of_surjective (mkL E) fun x => ⟨out x, rfl⟩

def map (f : E →L[ℂ] E) : ConjSp E →L[ℂ] ConjSp E where
  toFun x := mk (f (out x))
  map_add' x y := f.map_add (out x) (out y)
  map_smul' z x := f.map_smul (starRingEnd ℂ z) (out x)
  cont := f.cont

def unsub (V : Submodule ℂ (ConjSp E)) : Submodule ℂ E where
  carrier := {x | mk x ∈ V}
  add_mem' hx hy := V.add_mem hx hy
  zero_mem' := V.zero_mem
  smul_mem' z x hx := by
    have h := V.smul_mem (starRingEnd ℂ z) hx
    have e : mk (z • x) = starRingEnd ℂ z • mk x := (mkL E).map_smul' z x
    show mk (z • x) ∈ V
    rw [e]; exact h

end ConjSp

theorem map_star_mul {k : ℕ} (a b : Matrix (Fin k) (Fin k) ℂ) :
    (a * b).map star = a.map star * b.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_one {k : ℕ} : (1 : Matrix (Fin k) (Fin k) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem map_star_star {k : ℕ} (a : Matrix (Fin k) (Fin k) ℂ) : (a.map star).map star = a := by
  ext i j; simp

theorem map_star_conjTranspose {k : ℕ} (a : Matrix (Fin k) (Fin k) ℂ) : (a.map star)ᴴ = aᴴ.map star := by
  ext i j; simp

theorem map_star_Jm {k : ℕ} (ε : Fin k → Bool) : (Formalism.REAL.Jm ε).map star = Formalism.REAL.Jm ε := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_star_mem_UJ {k : ℕ} {ε : Fin k → Bool} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset ε) :
    g.map star ∈ UJset ε := by
  have h := congrArg (fun a : Matrix (Fin k) (Fin k) ℂ => a.map star) (show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε from hg)
  simp only [map_star_mul, map_star_Jm, ← map_star_conjTranspose] at h
  exact h

theorem map_star_mem_K {k : ℕ} {ε : Fin k → Bool} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g.map star ∈ Formalism.REAL.Kset ε := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h1 ⊢
    rw [map_star_conjTranspose, ← map_star_mul, h1, map_star_one]
  · have h := congrArg (fun a : Matrix (Fin k) (Fin k) ℂ => a.map star) h2
    simpa only [map_star_mul, map_star_Jm] using h

theorem star_exp_mul_I (x : ℝ) :
    starRingEnd ℂ (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  simp

theorem map_star_diag {k : ℕ} (θ : Fin k → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star =
      Matrix.diagonal fun a => Complex.exp ((((-θ) a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  exact star_exp_mul_I (θ a)

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def conjRep (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) :
    Matrix (Fin k) (Fin k) ℂ → (ConjSp H →L[ℂ] ConjSp H) :=
  fun g => ConjSp.map (σ (g.map star))

theorem sum_neg (μ θ : Fin k → ℝ) : ∑ a, μ a * (-θ) a = -∑ a, μ a * θ a := by
  simp

theorem isWtOn_conjRep_iff (ε : Fin k → Bool) (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (μ : Fin k → ℝ)
    (v : ConjSp H) :
    IsWtOn (Formalism.REAL.Kset ε) (conjRep σ) μ v ↔ IsWtOn (Formalism.REAL.Kset ε) σ μ (ConjSp.out v) := by
  constructor
  · intro h θ hθ
    have h1 := map_star_mem_K hθ
    rw [map_star_diag] at h1
    have h2 : σ ((Matrix.diagonal fun a => Complex.exp ((((-θ) a : ℝ) : ℂ) * Complex.I)).map star) (ConjSp.out v) =
        starRingEnd ℂ (Complex.exp (((∑ a, μ a * (-θ) a : ℝ) : ℂ) * Complex.I)) • ConjSp.out v := h (-θ) h1
    rw [map_star_diag, star_exp_mul_I, sum_neg, neg_neg, neg_neg] at h2
    exact h2
  · intro h θ hθ
    have h1 := map_star_mem_K hθ
    rw [map_star_diag] at h1
    have h2 := h (-θ) h1
    show σ ((Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star) (ConjSp.out v) =
        starRingEnd ℂ (Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I)) • ConjSp.out v
    rw [map_star_diag, star_exp_mul_I, ← sum_neg]
    exact h2

theorem isURepOn_conjRep {ε : Fin k → Bool} {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}
    (h : IsURepOn (UJset ε) σ) : IsURepOn (UJset ε) (conjRep σ) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (map_star_mem_UJ hg) (ConjSp.out v), fun v => ?_⟩
  · ext v
    show σ ((1 : Matrix (Fin k) (Fin k) ℂ).map star) (ConjSp.out v) = ConjSp.out v
    rw [map_star_one, h1]; rfl
  · ext v
    show σ ((a * b).map star) (ConjSp.out v) = σ (a.map star) (σ (b.map star) (ConjSp.out v))
    rw [map_star_mul, h2 _ (map_star_mem_UJ ha) _ (map_star_mem_UJ hb)]; rfl
  · have hc : Continuous fun g : Matrix (Fin k) (Fin k) ℂ => g.map star :=
      continuous_id.matrix_map continuous_star
    exact (h4 (ConjSp.out v)).comp hc.continuousOn fun g hg => map_star_mem_UJ hg

theorem isKTypeOf_conjRep [FiniteDimensional ℂ H] {ε : Fin k → Bool} {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}
    {Λ : Fin k → ℝ} (h : IsKTypeOf ε σ Λ ⊤) : IsKTypeOf ε (conjRep σ) Λ ⊤ := by
  obtain ⟨-, -, h3, ⟨v, -, hv0, hv⟩, h5⟩ := h
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_,
    ⟨ConjSp.mk v, trivial, hv0, (isWtOn_conjRep_iff ε σ Λ _).2 hv⟩,
    fun μ w _ hw0 hw => h5 μ (ConjSp.out w) trivial hw0 ((isWtOn_conjRep_iff ε σ μ w).1 hw)⟩
  have hst : IsKStableOn ε σ (ConjSp.unsub S) := by
    intro g hg w hw
    have h1 : ConjSp.mk (σ ((g.map star).map star) w) ∈ S := hS _ (map_star_mem_K hg) (ConjSp.mk w) hw
    rw [map_star_star] at h1
    exact h1
  rcases h3 _ le_top hst with h0 | h0
  · left
    rw [eq_bot_iff]
    intro w hw
    have : ConjSp.out w ∈ ConjSp.unsub S := hw
    rw [h0] at this
    exact this
  · right
    rw [eq_top_iff]
    intro w _
    have : ConjSp.out w ∈ ConjSp.unsub S := by rw [h0]; trivial
    exact this

theorem exists_conjugate_type : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : FiniteDimensional ℂ E) (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (J : H →ₛₗ[starRingEnd ℂ] E), Function.Bijective J ∧ IsURepOn (UJset (allPos k)) π ∧ IsKTypeOf (allPos k) π Λ ⊤ ∧ ∀ g u, π g (J u) = J (σ (g.map star) u) := by
  intro k Λ H _ _ _ σ h1 h2
  exact ⟨ConjSp H, inferInstance, inferInstance, inferInstance, conjRep σ, ConjSp.mkL H,
    Function.bijective_id, isURepOn_conjRep h1, isKTypeOf_conjRep h2, fun _ _ => rfl⟩

end GlobalTheory.ConjugateType
end
end

section

namespace GlobalTheory.AnalyticNormality

open IsLocalRing

theorem completion_isDomain_and_isIntegrallyClosed :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧
        IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  have hnoeth := GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian
  have hquot := GlobalTheory.T.nonempty_adicCompletion_quotient_ringEquiv
  have hengine := GlobalTheory.T.associated_prime_localization_dvr
  have hclosed := GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
  have hdom := GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
  have hred := GlobalTheory.T.adic_completion_reduced_of_jacobson
  have hcond := GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType
  intro A _ _ _ _ _ _
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  set m := maximalIdeal A with hm
  let R := AdicCompletion m A
  haveI : IsNoetherianRing R := hnoeth A m
  haveI : Module.Flat A R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsReduced R := hred A m (IsLocalRing.maximalIdeal_le_jacobson _)
  obtain ⟨x, hx0, hx⟩ := hcond A
  have hxR : algebraMap A R x ∈ nonZeroDivisors R := by
    have hxA : IsSMulRegular A x := IsSMulRegular.of_ne_zero hx0
    have h : IsSMulRegular R (algebraMap A R x) := hxA.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    refine h ?_
    simpa [smul_eq_mul, mul_comm] using hy
  have hredq : ∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R)) := by
    intro q hq _
    obtain ⟨e⟩ := hquot A m q
    haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
    haveI : Algebra.EssFiniteType A (A ⧸ q) := inferInstance
    haveI hess : @Algebra.EssFiniteType ℤ (A ⧸ q) _ _ (Ring.toIntAlgebra _) := by
      letI := Ring.toIntAlgebra (A ⧸ q)
      haveI : IsScalarTower ℤ A (A ⧸ q) := .of_algebraMap_eq fun z => by simp
      exact Algebra.EssFiniteType.comp ℤ A (A ⧸ q)
    have hj : m.map (Ideal.Quotient.mk q) ≤ Ideal.jacobson (⊥ : Ideal (A ⧸ q)) := by
      haveI : IsLocalRing (A ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      refine Ideal.mem_comap.mpr (IsLocalRing.maximalIdeal_le_jacobson _ ?_)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (hu.unit⁻¹ : (A ⧸ q)ˣ).1
      have h1 : Ideal.Quotient.mk q (a * b) = 1 := by
        rw [map_mul, hb]; exact hu.mul_val_inv
      have h2 : a * b - 1 ∈ q := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
      have h3 : a * b - 1 ∈ m := IsLocalRing.le_maximalIdeal hq.ne_top h2
      have h4 : (1 : A) ∈ m := by
        have := m.sub_mem (m.mul_mem_right b ha) h3
        simpa using this
      exact (Ideal.ne_top_iff_one m).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top h4
    haveI := hred (A ⧸ q) _ hj
    exact isReduced_of_injective e.toRingHom e.injective
  have hcl : IsIntegrallyClosed R := by
    refine hclosed R (algebraMap A R x) hxR ?_ hx
    intro P _ hP
    obtain ⟨h1, h2⟩ := hengine A R x hx0 hredq P hP
    exact ⟨h1, inferInstance⟩
  exact ⟨hdom R hcl, hcl⟩

end GlobalTheory.AnalyticNormality
end
