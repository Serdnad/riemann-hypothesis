module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CoherentDense

open MvPolynomial

theorem eq_zero_of_hasSum_pow (a : ℕ → ℂ) (h : ∀ t : ℂ, HasSum (fun n => t ^ n * a n) 0) : a = 0 := by
  have h1 : HasFPowerSeriesAt (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun t => by
      simpa [FormalMultilinearSeries.coeff_ofScalars] using h t
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 h1.eq_zero

theorem eq_zero_of_hasSum_monomial {σ : Type} [Fintype σ] (c : (σ →₀ ℕ) → ℂ)
    (h : ∀ x : σ → ℂ, HasSum (fun α : σ →₀ ℕ => c α * α.prod fun l k => x l ^ k) 0) : c = 0 := by
  classical
  let S : ℕ → Finset (σ →₀ ℕ) := fun n => (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
  have hS : ∀ n α, α ∈ S n ↔ α.degree = n := fun n α => by simp [S]
  have key : ∀ n, (∑ α ∈ S n, monomial α (c α) : MvPolynomial σ ℂ) = 0 := by
    intro n
    refine MvPolynomial.funext fun x => ?_
    have h1 : (fun m => eval x (∑ α ∈ S m, monomial α (c α) : MvPolynomial σ ℂ)) = 0 := by
      refine eq_zero_of_hasSum_pow _ fun t => ?_
      have h2 := (h (t • x)).tsum_fiberwise (fun α => α.degree)
      refine h2.congr_fun fun m => ?_
      have e : ((fun α : σ →₀ ℕ => α.degree) ⁻¹' {m}) = (S m : Set (σ →₀ ℕ)) := by
        ext α; simp [hS]

      rw [e, Finset.tsum_subtype' (S m) (fun α : σ →₀ ℕ => c α * α.prod fun l k => (t • x) l ^ k), map_sum,
      Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [eval_monomial, ← (hS m α).1 hα, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
      ring
    simpa using congrFun h1 n
  funext α
  have h3 := congrArg (AddMonoidAlgebra.coeff · α) (key α.degree)
  rw [coeff_sum, Finset.sum_eq_single α (fun β _ hβ => by simp [coeff_monomial, hβ])
    (fun hα => absurd ((hS _ α).2 rfl) hα)] at h3
  simpa using h3

theorem factorial_mul_coeff_expPS {σ : Type} [Fintype σ] (x : σ → ℂ) (α : σ →₀ ℕ) :
    α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (expPS (∑ l, x l • X l)) =
      α.prod fun l k => x l ^ k := by
  classical
  have hdeg : (α.sum fun _ e => e) = α.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [MvPowerSeries.coeff_apply, expPS, Finset.sum_eq_single α.degree]
  · rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : (α.prod fun _ k => k.factorial) * α.multinomial = α.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : α.prod (fun _ k => (k.factorial : ℂ)) * (α.multinomial : ℂ) = (α.degree.factorial : ℂ) := by
      rw [← hs]; simp [Finsupp.prod]
    have h0 : (α.degree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
  · intro k _ hk
    rw [coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

theorem eq_zero_of_inner_monomial {σ : Type} [DecidableEq σ] (F : Fock σ) (u : F.H)
    (h : ∀ α, inner ℂ u (F.ι (monomial α 1)) = 0) : u = 0 := by
  refine F.dense.eq_zero_of_inner_left ℂ ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add (f := _), inner_add_right, hf, hg, add_zero]
  | monomial β c =>
    have e : (monomial β c : MvPolynomial σ ℂ) = c • monomial β 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_right, h, mul_zero]

theorem hasSum_inner {σ : Type} [DecidableEq σ] (F : Fock σ) (u v : F.H) :
    HasSum (fun α : σ →₀ ℕ => inner ℂ u (F.ι (monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ)) *
      inner ℂ (F.ι (monomial α 1)) v) (inner ℂ u v) := by
  let m : (σ →₀ ℕ) → ℝ := fun α => α.prod fun _ k => (k.factorial : ℝ)
  have hm : ∀ α, 0 < m α := fun α => Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)
  have hm' : ∀ α : σ →₀ ℕ, α.prod (fun _ k => (k.factorial : ℂ)) = (m α : ℂ) := fun α => by
    simp [m, Finsupp.prod]
  let r : (σ →₀ ℕ) → ℂ := fun α => (((√(m α))⁻¹ : ℝ) : ℂ)
  have hr : ∀ α, (starRingEnd ℂ) (r α) = r α := fun α => Complex.conj_ofReal _
  have hr2 : ∀ α, r α * r α = (m α : ℂ)⁻¹ := fun α => by
    simp only [r]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hm α).le, Complex.ofReal_inv]
  have hm0 : ∀ α, (m α : ℂ) ≠ 0 := fun α => by exact_mod_cast (hm α).ne'
  have hr0 : ∀ α, r α ≠ 0 := fun α h => inv_ne_zero (hm0 α) (by rw [← hr2, h, mul_zero])
  let b : (σ →₀ ℕ) → F.H := fun α => r α • F.ι (monomial α 1)
  have hb : Orthonormal ℂ b := by
    rw [orthonormal_iff_ite]
    intro α β
    simp only [b, inner_smul_left, inner_smul_right, F.fockIP, hr]
    split_ifs with h
    · subst h
      rw [← mul_assoc, hr2, hm', inv_mul_cancel₀ (hm0 α)]
    · simp
  have hsp : (Submodule.span ℂ (Set.range b))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    refine eq_zero_of_inner_monomial F w fun α => ?_
    have := Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self α)) hw
    simpa [b, inner_smul_right, hr0] using this
  have h := (HilbertBasis.mkOfOrthogonalEqBot hb hsp).hasSum_inner_mul_inner u v
  refine h.congr_fun fun α => ?_
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  simp only [b, inner_smul_left, inner_smul_right, hr, hm', div_eq_mul_inv, ← hr2]
  ring

end GlobalTheory.CoherentDense


open GlobalTheory.CoherentDense in
theorem GlobalTheory.dense_span_coherent : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  intro P Q F e he
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hg : ∀ x : Ix P Q → ℂ, gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x = ∑ l, x l • MvPolynomial.X l := fun x => by
    simp [gaussPoly, MvPolynomial.smul_eq_C_mul]
  have h := eq_zero_of_hasSum_monomial
    (fun α => inner ℂ u (F.ι (MvPolynomial.monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ))) fun x => by
      have h1 := hasSum_inner F u (e x)
      rw [Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self x)) hu] at h1
      simpa only [he x _, hg, factorial_mul_coeff_expPS] using h1
  refine eq_zero_of_inner_monomial F u fun α => ?_
  have h2 := congrFun h α
  have h0 : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simpa [h0] using h2

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscExpDeriv

theorem coeff_pow_eq_zero_of_degree_lt {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (n : ℕ) :
    ∀ γ : σ →₀ ℕ, γ.degree < n → AddMonoidAlgebra.coeff (q ^ n) γ = 0 := by
  induction n with
  | zero => intro γ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro γ h
    rw [pow_succ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx' : x.1 + x.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h2 : x.2 = 0
    · rw [h2, hq, mul_zero]
    · have hd : x.2.degree ≠ 0 := fun h0 => h2 ((Finsupp.degree_eq_zero_iff _).1 h0)
      have hs : x.1.degree + x.2.degree = γ.degree := by rw [← hx', map_add (f := _)]
      rw [ih x.1 (by omega), zero_mul]

theorem coeff_expPS_eq_sum {σ : Type} [DecidableEq σ] (q : MvPolynomial σ ℂ)
    (hq : AddMonoidAlgebra.coeff q 0 = 0) (γ : σ →₀ ℕ) (N : ℕ) (hN : γ.degree < N) :
    MvPowerSeries.coeff γ (expPS q) =
      ∑ n ∈ Finset.range N, AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) := by
  change ∑ n ∈ Finset.range (γ.degree + 1), AddMonoidAlgebra.coeff (q ^ n) γ / (n.factorial : ℂ) = _
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun n _ hn => ?_
  rw [coeff_pow_eq_zero_of_degree_lt q hq n γ (by simp only [Finset.mem_range] at hn; omega),
    zero_div]

theorem coeff_deriv_expPS : ∀ (σ : Type) [DecidableEq σ] (q : MvPolynomial σ ℂ),
    AddMonoidAlgebra.coeff q 0 = 0 → ∀ (l : σ) (α : σ →₀ ℕ),
      ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS q) =
        MvPowerSeries.coeff α
          (((MvPolynomial.pderiv l q : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) * expPS q) := by
  intro σ _ q hq l α
  rw [coeff_expPS_eq_sum q hq _ (α.degree + 1 + 1)
    (by rw [map_add (f := _), Finsupp.degree_single]; omega), Finset.mul_sum, MvPowerSeries.coeff_mul]
  have h1 : ∀ n : ℕ, ((α l : ℂ) + 1) *
      (AddMonoidAlgebra.coeff (q ^ n) (α + Finsupp.single l 1) / (n.factorial : ℂ)) =
      AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ n)) α / (n.factorial : ℂ) := by
    intro n
    rw [MvPolynomial.coeff_pderiv]
    ring
  simp only [h1]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_div, add_zero]
  have h2 : ∀ n : ℕ, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l (q ^ (n + 1))) α /
      (((n + 1).factorial : ℕ) : ℂ) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal α, AddMonoidAlgebra.coeff (MvPolynomial.pderiv l q) x.1 *
        (AddMonoidAlgebra.coeff (q ^ n) x.2 / (n.factorial : ℂ)) := by
    intro n
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, mul_comm, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_mul, Nat.factorial_succ, nsmul_eq_mul]
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    push_cast
    field_simp
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hs : x.1.degree + x.2.degree = α.degree := by rw [← hx', map_add (f := _)]
  rw [coeff_expPS_eq_sum q hq x.2 (α.degree + 1) (by omega), MvPolynomial.coeff_coe, Finset.mul_sum]

end GlobalTheory.OscExpDeriv
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix
open scoped ComplexOrder

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

theorem classSum_gram_posDef (s : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hpos : ∀ w, w ≠ 0 → 0 < B w w) (hsym : ∀ w w', star (B w w') = B w' w)
    (ψ : C.V → W) (hψ : ∀ x, ψ x = 0 → x = 0) (hs : ∀ x y, s (C.pair x y) = B (ψ x) (ψ y)) :
    (C.H.map s).PosDef := by
  classical
  have hnn : ∀ w, 0 ≤ B w w := fun w => by
    by_cases h : w = 0
    · simp [h]
    · exact (hpos w h).le
  have hw : ∀ c, (0 : ℂ) < ((C.wt c : ℂ))⁻¹ := fun c => inv_pos.2 (by exact_mod_cast C.wt_pos c)
  have hc : ∀ f g : C.Cl → C.V, s (C.csum f g) = ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ (f c)) (ψ (g c)) := by
    intro f g

    simp only [CSD.csum, map_sum, map_mul, map_inv₀, map_natCast, hs]
  have hsemi : (C.H.map s).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, CSD.H, Matrix.of_apply, hc, star_sum, star_mul', hsym,
        star_inv₀, star_natCast]
    · intro x
      have e : star x ⬝ᵥ (C.H.map s) *ᵥ x = ∑ c, ((C.wt c : ℂ))⁻¹ *
          B (∑ i, x i • ψ ((C.basis i : C.Cl → C.V) c)) (∑ j, x j • ψ ((C.basis j : C.Cl → C.V) c)) := by

        simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, CSD.H, Matrix.of_apply, hc, map_sum, LinearMap.sum_apply,
        LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Pi.star_apply,
        starRingEnd_apply, RingHom.id_apply]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (hw c).le (hnn _)
  rw [hsemi.posDef_iff_det_ne_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h1 : C.csum (C.I v) (C.I v) = 0 := by
    rw [C.csum_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ j, C.H i j * v j = 0 := congrFun hv0 i
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h2, mul_zero]
  have h2 := hc (C.I v) (C.I v)
  rw [h1, map_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun c _ => mul_nonneg (hw c).le (hnn _)] at h2
  apply hv
  apply C.I_injective
  rw [map_zero]
  funext c
  refine hψ _ ?_
  by_contra hne
  exact (mul_pos (hw c) (hpos _ hne)).ne' (h2 c (Finset.mem_univ c))

theorem majAt_stdFrame_classSum (v : InfinitePlace K) (hv : ∀ a, v.embedding (star a) = starRingEnd ℂ (v.embedding a))
    (hH : (C.H.map v.embedding).PosDef) (x y : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y = v.embedding (C.csum x.1 y.1) := by
  have hI : ∀ z : C.Forms, C.I (C.basis.equivFun z) = z.1 := fun z => by simp [CSD.I_apply]
  have h1 : Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin C.dim)) (stdFrame C.H) v (C.basis.equivFun x) (C.basis.equivFun y) := by
    have h2 : ∀ z : C.Forms, Formalism.HermitianLatticesTheory.vecAt C.basis v z =
        Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin C.dim)) v (C.basis.equivFun z) := by
      intro z; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h2]
  have hm : metOf (stdFrame C.H v) = C.H.map v.embedding := (frameOfSpec _ _ hH).2
  rw [h1, majAt_eq, hm, ← hI x, ← hI y, C.csum_sum]

  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, hv, Finset.mul_sum, Pi.star_apply,
  starRingEnd_apply, mul_assoc]

end ClassSum

section Pair

variable {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ}

theorem map_pairVr_one (emb : ι → E →+* K) (lam : ι → DomWeight n) (s : K →+* ℂ)
    (hs : ∀ a, s (star a) = starRingEnd ℂ (s a)) (F F' : VV K lam) :
    s (pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) F F') = _root_.Formalism.L2.Col.nfL lam (MvPolynomial.map s F.1) (MvPolynomial.map s F'.1) := by
  have h := _root_.Formalism.L2.Col.pairVr_nfAll emb (1 : Matrix (Fin n) (Fin n) E) lam s (_root_.Formalism.L2.Col.stdFrC (_root_.Formalism.L2.Col.embAt s emb))
    (fun τ => by simp [_root_.Formalism.L2.Col.stdFrC, gramC]) F F' (fun m => hs _)
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (_root_.Formalism.L2.Col.stdFrC (n := n) (_root_.Formalism.L2.Col.embAt s emb)).1 = AlgHom.id ℂ _ := blockAct_one
  rw [h, e, _root_.Formalism.L2.Col.nfL_apply]
  simp [_root_.Formalism.L2.Col.stdFrC]

end Pair

theorem GStep.lawNorm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h [Fintype S.Cl], S.LawNorm emb σ lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF _ h inst x
  have hv : ∀ a, (InfinitePlace.mk σ).embedding (star a) = starRingEnd ℂ ((InfinitePlace.mk σ).embedding a) := by
    intro a
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e, hF.sig_star]
    · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hF.sig_star]
  have hre : ∀ a, ((InfinitePlace.mk σ).embedding a).re = (σ a).re := by
    intro a
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  have hH : ((S.csd emb lam h).H.map (InfinitePlace.mk σ).embedding).PosDef :=
    classSum_gram_posDef (S.csd emb lam h) _ (_root_.Formalism.L2.Col.nfL lam) (ps_nfL_pos lam) (ps_nfL_symm lam)
      (fun F : VV K lam => MvPolynomial.map (InfinitePlace.mk σ).embedding F.1)
      (fun F hF0 => Subtype.ext (MvPolynomial.map_injective _ (RingHom.injective _) (hF0.trans (map_zero _).symm)))
      (fun F F' => map_pairVr_one emb lam _ hv F F')
  have h1 := majAt_stdFrame_classSum (S.csd emb lam h) (InfinitePlace.mk σ) hv hH x x
  refine (congrArg Complex.re h1).trans ?_
  rw [hre]
  congr 1
  have hi : inst = (S.csd emb lam h).finCl := Subsingleton.elim _ _
  subst hi
  unfold CSD.csum

  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  have h2 : (S.csd emb lam h).wt c = Nat.card (S.Stab c) := (@Nat.card_eq_fintype_card _ (_)).symm
  rw [h2]
  congr 1
  exact (_root_.Formalism.L2.Col.ipFr_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (fr0 emb σ n) (fun τ => by simp [fr0, _root_.Formalism.L2.Col.stdFrC, gramC]) _ _
    (fun m => hF.sig_star _)).symm

end GlobalTheory.Mem.Col2
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem valC_finiteDimensional {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (ValC (Gr emb σ n) lam) := by
  classical
  have h := _root_.Formalism.L2.Col.span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ
  have h2 : ValC (Gr emb σ n) lam ≤
      Submodule.span ℂ (Set.range fun i => _root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i)) := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨F, rfl⟩

    rw [← (bVV K lam).sum_repr F, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range fun i => _root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))
  exact Submodule.finiteDimensional_of_le h2

theorem GStep.fi_finiteDimensional {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K]
    [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (_hF : FOk emb σ) (hS : S.Ok) : FiniteDimensional ℂ (S.Fi emb σ lam) := by
  haveI := hS.fin_orb
  haveI := valC_finiteDimensional emb σ lam
  let f : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam) :=
    { toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun a b hab => ?_
  apply Subtype.ext
  funext c
  exact congrArg Subtype.val (congrFun hab c)

end GlobalTheory.Mem.Col2
end

section

namespace GlobalTheory.Mem.Col2.DiaLat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem evV_rho_tr (b : S.β) (g : S.G b) (v : VV K lam) :
    _root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (_root_.Formalism.L2.Col.evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine _root_.Formalism.L2.Col.evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem exists_pull (hf : S.Free) (h : (S.fam emb lam).Ok) (p : ∀ c : S.Cl, S.D c.1)
    (hp : ∀ c, S.Lsh c.1 (p c) = S.Lsh c.1 (S.rep c)) (x : S.FormsK emb lam h) (hx : x ∈ (S.hlat emb lam h).L) :
    ∃ y ∈ (S.hlat emb lam h).L, ∀ c, S.embF emb σ lam h y c =
      S.trTo emb σ c.1 (p c) (S.embF emb σ lam h x (S.cl c.1 (p c))) := by
  refine ⟨⟨fun c => S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))), fun c g => ?_⟩, fun c => ?_, fun c => ?_⟩
  · have hg : (g.1 : S.G c.1) = 1 := hf c.1 g.1 (S.rep c) g.2
    show S.rho emb lam c.1 g.1 _ = _
    rw [hg, map_one]
    rfl
  · have h1 : delAtr emb lam (S.Lsh c.1 (S.mv c.1 (p c) • S.rep (S.cl c.1 (p c)))) =
        (delAtr emb lam (S.Lsh c.1 (S.rep (S.cl c.1 (p c))))).map
          ((S.rho emb lam c.1 (S.mv c.1 (p c))).restrictScalars (𝓞 K)) :=
      (h c.1).del_smul (S.mv c.1 (p c)) (S.rep (S.cl c.1 (p c)))
    rw [S.mv_smul, hp] at h1
    show S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))) ∈ delAtr emb lam (S.Lsh c.1 (S.rep c))
    rw [h1]
    exact Submodule.mem_map_of_mem (hx (S.cl c.1 (p c)))
  · exact evV_rho_tr S emb σ lam c.1 _ _

end General

theorem dia_lat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ hJ hF P a x hx
  obtain ⟨y, hy, e⟩ := exists_pull (I.S 0) emb σ (lamT hc 0) hJ.free0 hF (fun c => (J.A 0).diaPt P a c)
    (fun c => (hJ.lev 0).dia_Lsh c.1 P a _) x hx
  exact ⟨y, hy, funext e⟩

end GlobalTheory.Mem.Col2.DiaLat
end
