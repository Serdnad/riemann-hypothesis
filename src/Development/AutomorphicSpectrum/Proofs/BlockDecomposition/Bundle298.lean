module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle226
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle274
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle290
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle028
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle021
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle022
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle291
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.LimSmooth

theorem tendstoLocallyUniformlyOn_frame {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] {A : ι → Mat n → CLof (Mat n) ℝ} (hA : ∀ p, ContinuousOn (A p) (GLs n))
    {u : ι → ℕ → Mat n → V} {U : ι → Mat n → V}
    (hu : ∀ p, TendstoUniformlyOn (u p) (U p) atTop (GLs n)) :
    TendstoLocallyUniformlyOn
      (fun (k : ℕ) (z : Mat n) => (∑ p, (A p z).smulRight (u p k z) : CLof (Mat n) V))
      (fun z => (∑ p, (A p z).smulRight (U p z) : CLof (Mat n) V)) atTop (GLs n) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set M : ℝ := ∑ p, (‖A p x‖ + 1) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun p _ => by positivity
  have hnear : ∀ᶠ y in 𝓝[GLs n] x, ∀ p, ‖A p y‖ < ‖A p x‖ + 1 := by
    rw [Filter.eventually_all]
    intro p
    exact Filter.Tendsto.eventually_lt_const (lt_add_one _) (hA p x hx).norm
  have hpos : 0 < ε / (M + 1) := by positivity
  refine ⟨{y | ∀ p, ‖A p y‖ < ‖A p x‖ + 1} ∩ GLs n,
    Filter.inter_mem hnear self_mem_nhdsWithin, ?_⟩
  have hev : ∀ᶠ k in atTop, ∀ p, ∀ y ∈ GLs n, dist (U p y) (u p k y) < ε / (M + 1) := by
    rw [Filter.eventually_all]
    intro p
    exact Metric.tendstoUniformlyOn_iff.1 (hu p) _ hpos
  filter_upwards [hev] with k hk y hy
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  have hterm : ∀ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖
      ≤ (‖A p x‖ + 1) * (ε / (M + 1)) := by
    intro p
    have he : (A p y).smulRight (U p y) - (A p y).smulRight (u p k y)
        = (A p y).smulRight (U p y - u p k y) := by
      ext v
      simp [smul_sub]
    rw [he, ContinuousLinearMap.norm_smulRight_apply]
    have h1 := hk p y hy.2
    rw [dist_eq_norm] at h1
    exact mul_le_mul (hy.1 p).le h1.le (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖ := norm_sum_le _ _
    _ ≤ ∑ p, (‖A p x‖ + 1) * (ε / (M + 1)) := Finset.sum_le_sum fun p _ => hterm p
    _ = M * (ε / (M + 1)) := by rw [Finset.sum_mul]
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

theorem sum_smulRight_apply {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] (B : ι → CLof (Mat n) ℝ) (c : ι → V) (v : Mat n) :
    (∑ q, (B q).smulRight (c q) : CLof (Mat n) V) v = ∑ q, B q v • c q := by
  simp

theorem limit_smooth : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) →
    (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) →
    ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V,
      (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧
      ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  intro n V _ _ _ g hg hc
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  have hopen : IsOpen (GLs n) := isOpen_GLs
  let Gf : List (Bool × Fin n × Fin n) → Mat n → V :=
    fun w z => limUnder atTop (fun k => Rw w (g k) z)
  have hpt : ∀ w, ∀ z ∈ GLs n, Tendsto (fun k => Rw w (g k) z) atTop (𝓝 (Gf w z)) := by
    intro w z hz
    have hcs : CauchySeq (fun k => Rw w (g k) z) := (hc w).cauchy_map hz
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
    have he : Gf w z = x := hx.limUnder_eq
    rwa [he]
  have hu : ∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n) := fun w =>
    (hc w).tendstoUniformlyOn_of_tendsto (hpt w)
  have hsm : ∀ k w, ContDiffOn ℝ ∞ (Rw w (g k)) (GLs n) := fun k w =>
    GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
  have hderiv : ∀ k w, ∀ z ∈ GLs n, fderiv ℝ (Rw w (g k)) z
      = (∑ p, (A p z).smulRight (Rw (p :: w) (g k) z) : CLof (Mat n) V) := by
    intro k w z hz
    exact hA V (fderiv ℝ (Rw w (g k)) z) z hz
  have hhas : ∀ w, ∀ z ∈ GLs n, HasFDerivAt (Gf w)
      (∑ p, (A p z).smulRight (Gf (p :: w) z) : CLof (Mat n) V) z := by
    intro w z hz
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun k => Rw w (g k))
      (f' := fun (k : ℕ) (y : Mat n) =>
        (∑ p, (A p y).smulRight (Rw (p :: w) (g k) y) : CLof (Mat n) V))
      (g' := fun y => (∑ p, (A p y).smulRight (Gf (p :: w) y) : CLof (Mat n) V))
      hopen (tendstoLocallyUniformlyOn_frame (u := fun p k => Rw (p :: w) (g k))
        (U := fun p => Gf (p :: w)) (fun p => hAc p |>.continuousOn) (fun p => hu (p :: w)))
      ?_ (hpt w) hz
    intro k y hy
    have hd : DifferentiableAt ℝ (Rw w (g k)) y :=
      ((hsm k w).contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
    have h2 := hd.hasFDerivAt
    rwa [hderiv k w y hy] at h2
  have hRd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Gf w) z = Gf (p :: w) z := by
    intro w p z hz
    have h1 : Rd (bs p) (Gf w) z
        = (∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p) := by
      have h0 := (hhas w z hz).fderiv
      exact congrArg (fun L : CLof (Mat n) V => L (z * bs p)) h0
    have h2 : Tendsto (fun k => Rw (p :: w) (g k) z) atTop
        (𝓝 ((∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p))) := by
      have h3 : ∀ k, Rw (p :: w) (g k) z
          = ∑ q, (A q z (z * bs p)) • Rw (q :: w) (g k) z := by
        intro k
        have h4 : Rw (p :: w) (g k) z
            = (∑ q, (A q z).smulRight (Rw (q :: w) (g k) z) : CLof (Mat n) V) (z * bs p) :=
          congrArg (fun L : CLof (Mat n) V => L (z * bs p)) (hderiv k w z hz)
        rw [h4, sum_smulRight_apply]
      rw [sum_smulRight_apply]
      simp only [h3]
      exact tendsto_finsetSum _ fun q _ => (hpt (q :: w) z hz).const_smul _
    rw [h1]
    exact tendsto_nhds_unique h2 (hpt (p :: w) z hz)
  have hfam : ∀ v, ContDiffOn ℝ ∞ (Gf v) (GLs n) :=
    GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) Gf (fun p w => p :: w)
      (fun v z hz => (hhas v z hz).differentiableAt) (fun v p z hz => hRd v p z hz)
  refine ⟨Gf, hu, hfam [], ?_⟩
  intro w
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    exact (Rd_congr ih (bs p) z hz).trans (hRd w p z hz)

end GlobalTheory.CompanionTheory.PresSobA.LimSmooth
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem glue_r : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hM hC K _ E U₁ ι _ _ V W hV hW h₁ h₂ hK
  refine GlobalTheory.T.cosieve_pairing_family_compat hM hC E.F₂ E.F₃ (fun a => CH.cx (U₁.ι ⋙ E.F₁ a))
    (fun U U' => (∀ T, U' T → U₁ (E.L₁.obj T)) ∧ (∀ T, U' T → U (E.L₂.obj T)))
    (fun U U' r {a a' c} ha => E.pr U₁ U U' r.1 r.2 ha) ?_ V W hV hW (fun S => ⟨h₁ S, h₂ S⟩)
    (fun S hS => hK S hS)
  intro A B A' B' r₁ r₂ k k' a a' c ha i j n hn x y
  have h := GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 (le_refl U₁) k k' ha hn x y
  rw [GlobalTheory.T.restrict_self_pullC_eq] at h
  exact h

end GlobalTheory.CompanionTheory.KunGlue
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral

def IntW (l K : ℕ) {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop :=
  ∀ m, ∃ z : ℤ, (l : ℚ) ^ K * v m = z

theorem IntW.succ {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) : IntW l (K + 1) v := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨l * z, ?_⟩
  push_cast
  rw [← hz, pow_succ]
  ring

theorem IntW.mono {l K K' r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (hK : K ≤ K') :
    IntW l K' v := by
  induction K', hK using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ

theorem IntW.neg_one_pow_mul {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (c : ℕ) :
    IntW l K (fun m => (-1 : ℚ) ^ c * v m) := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨(-1) ^ c * z, ?_⟩
  push_cast
  rw [← hz]
  ring

theorem int_sum {α : Type} (s : Finset α) (q : ℚ) (f : α → ℚ)
    (h : ∀ a ∈ s, ∃ z : ℤ, q * f a = z) : ∃ z : ℤ, q * ∑ a ∈ s, f a = z := by
  classical
  choose! g hg using h
  refine ⟨∑ a ∈ s, g a, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hg

theorem partialSum_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) :
    IntW l K (partialSum i v) :=
  fun m => int_sum _ _ _ fun k _ => h _

theorem intW_partialSumMean {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (meanP l i v) := by
  intro m
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨z, hz⟩ := int_sum (Finset.range l) ((l : ℚ) ^ K)
    (fun k => partialSum i v (Function.update m i k)) (fun k _ => partialSum_int h _)
  refine ⟨z, ?_⟩
  rw [← hz, meanP, pow_succ]
  field_simp

theorem aop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Aop l i v) := by
  intro m
  obtain ⟨a, ha⟩ := (partialSum_int (i := i) h).succ (m + Pi.single i 1)
  obtain ⟨b, hb⟩ := intW_partialSumMean (i := i) hl h m
  refine ⟨a - b, ?_⟩
  push_cast
  rw [← ha, ← hb, Aop]
  ring

theorem bop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Bop l i v) := by
  intro m
  by_cases h0 : m i = 0
  · simpa [Bop, h0] using intW_partialSumMean (i := i) hl h m
  · exact ⟨0, by simp [Bop, h0]⟩

theorem iterate_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : ℕ) : IntW l (K + c) ((Aop l i)^[c] v) := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact aop_int hl ih

theorem uW_int {l N K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : Fin (N + 1)) : IntW l (K + (N + 1)) (OneVar.uW l N i v c) := by
  unfold OneVar.uW
  split_ifs with hc
  · have h1 : IntW l (K + c + 1) (Bop l i ((Aop l i)^[c] v)) := bop_int hl (iterate_int hl h c)
    exact (h1.mono (by omega)).neg_one_pow_mul _
  · exact ((iterate_int hl h N).mono (by omega)).neg_one_pow_mul _

theorem abel_oneVar_uW (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hg : GoodAt l i v)
    (hb : BddW v) :
    (∀ c : Fin (N + 1), BddW (OneVar.uW l N i v c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → GoodAt l k v → GoodAt l k (OneVar.uW l N i v c)) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m =
        ∑ c : Fin (N + 1), ∑' m, (OneVar.uW l N i v c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  refine ⟨fun c => ?_, fun c => ?_, fun c k hk hgk => ?_, fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · have hc := OneVar.iterate_good_bdd hl hg hb c
      exact OneVar.bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact OneVar.bddW_sign _ (OneVar.iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [OneVar.uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · exact OneVar.goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (OneVar.iterate_good_other hk hgk c)).2
    · exact OneVar.goodAt_smul _ (OneVar.iterate_good_other hk hgk N)
  · intro m hm
    unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (OneVar.iterate_supp_other hk hsk c)).2 m hm]
    · simp [OneVar.iterate_supp_other hk hsk N m hm]
  · rw [OneVar.tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, mul_assoc]

theorem expansion_on_finset_int (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (hz : ∀ m, ∃ z : ℤ, w m = z) (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q, IntW l K (u q)) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w, 0,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun _ m => ?_, fun g _ => by simp [DL]⟩
    obtain ⟨z, hz⟩ := hz m
    exact ⟨z, by simp [hz]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, K, hb, hg, hs, hi, hid⟩ := ih
    have hP := fun q => abel_oneVar_uW r l N a (u q) hl (hg q a ha).1 (hb q)
    have h1 := fun q => (hP q).1
    have h2 := fun q => (hP q).2.1
    have h3 := fun q => (hP q).2.2.1
    have h4 := fun q => (hP q).2.2.2.1
    have h5 := fun q => (hP q).2.2.2.2
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => OneVar.uW l N a (u p.1) p.2, K + (N + 1), fun p => h1 p.1 p.2, ?_, ?_,
      fun p => uW_int hl (hi p.1) p.2, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables_int : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    (∀ m, ∃ z : ℤ, w m = z) →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw hz
  obtain ⟨Q, iQ, cs, u, K, hb, -, hs, hi, hid⟩ := expansion_on_finset_int r l N w hl hw hz Finset.univ
  exact ⟨Q, iQ, cs, u, K, hb, fun q i => hs q i (Finset.mem_univ i), hi, hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

theorem mem_span_pow_of_factorial_mul_eq {S : Type} [CommRing S] (hS : R.TF S) {l : ℕ}
    (hl : l.Prime) (n : ℕ) {x : S} (hx : x ∈ Ideal.span {(l : S) ^ n}) {k : ℕ} (hk : k ≠ 0)
    {y : S} (e : (k.factorial : S) * y = x ^ k) : y ∈ Ideal.span {(l : S) ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨x', rfl⟩ := Ideal.mem_span_singleton'.1 hx
  haveI := Fact.mk hl
  obtain ⟨v, m, hlm, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd k.factorial_ne_zero l hl.ne_one
  have hv : v < k := by
    have h1 : v ≤ multiplicity l k.factorial :=
      (Nat.pow_dvd_iff_le_multiplicity hl.ne_one k.factorial_ne_zero).1 ⟨m, hm⟩
    exact lt_of_le_of_lt h1 (multiplicity_factorial_lt_of_ne_zero l hk)
  obtain ⟨t, ht⟩ : ∃ t, n * k = n + v + t := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    refine ⟨n * k' - v, ?_⟩
    have : v ≤ n * k' := by nlinarith [Nat.lt_succ_iff.1 hv]
    rw [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one]
    omega
  have hfac : (k.factorial : S) = (l : S) ^ v * (m : S) := by rw [hm]; push_cast; rfl
  have e2 : (l : S) ^ v * ((m : S) * y) = (l : S) ^ v * ((l : S) ^ n * ((l : S) ^ t * x' ^ k)) := by
    rw [← mul_assoc, ← hfac, e, mul_pow, ← pow_mul, ht, pow_add, pow_add]
    ring
  have hr : (l : S) ^ v ∈ nonZeroDivisors S := pow_mem (hS l hl.ne_zero) v
  have e3 : (m : S) * y = (l : S) ^ n * ((l : S) ^ t * x' ^ k) := by
    have h0 : (l : S) ^ v * ((m : S) * y - (l : S) ^ n * ((l : S) ^ t * x' ^ k)) = 0 := by
      rw [mul_sub, e2, sub_self]
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hr) _ (by rwa [mul_comm] at h0))
  have hc : IsCoprime (m : ℤ) ((l : ℤ) ^ n) := by
    apply IsCoprime.pow_right
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hl).2 hlm).symm
  obtain ⟨a, b, hab⟩ := hc
  have hab' : (a : S) * (m : S) + (b : S) * (l : S) ^ n = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → S) hab
  have hy : y = ((a : S) * ((l : S) ^ t * x' ^ k) + (b : S) * y) * (l : S) ^ n := by
    calc y = ((a : S) * (m : S) + (b : S) * (l : S) ^ n) * y := by rw [hab', one_mul]
      _ = (a : S) * ((m : S) * y) + (b : S) * (l : S) ^ n * y := by ring
      _ = _ := by rw [e3]; ring
  rw [hy]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_dividedPowers_map_mkAcr {l : ℕ} [hl : Fact l.Prime] (A : PAlg l) (n : ℕ)
    (I : Ideal A.Acr0) (hI : R.PdI I) (K : Ideal (A.Acr n)) (hK : K = I.map (A.mkAcr n)) :
    ∃ δ : DividedPowers K, R.IsPd (A.mkAcr n) I δ := by
  subst hK
  exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient A.acris_torsion_free I
    (Ideal.span {(l : A.Acr0) ^ n}) hI
    fun x _ hx k hk y e => mem_span_pow_of_factorial_mul_eq A.acris_torsion_free hl.out n hx hk e

theorem exists_dividedPowers_fil_pfil : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ),
    (∃ δ : DividedPowers (A.Fil n 1), R.IsPd (A.mkAcr n) (A.Fil0 1) δ) ∧
      ∃ δ : DividedPowers (A.PFil n), R.IsPd (A.mkAcr n) A.PFil0 δ := by
  intro l _ A n
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.filtration_divided_power_structures A
  exact ⟨exists_dividedPowers_map_mkAcr A n _ p1 _ (h1 n 1),
    exists_dividedPowers_map_mkAcr A n _ p2 _ (h2 n)⟩

end GlobalTheory.CompanionTheory.PerfFil
end
