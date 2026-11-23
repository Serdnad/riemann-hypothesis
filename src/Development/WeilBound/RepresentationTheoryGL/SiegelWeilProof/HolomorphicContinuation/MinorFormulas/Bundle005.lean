module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle003
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.SP.Mi

variable {n : ℕ}

def alMn (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

def cMn (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def phi (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : Pm (Polynomial ℂ) ρ →ₐ[Polynomial ℂ] Fm n :=
  rename fun pq => (b, J pq.1, I pq.2)

theorem phi_X (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) : phi b I J (X (p, q)) = yv b (J p) (I q) := by
  simp [phi, yv, rename_X]


theorem deriv_part (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) = phi b I J (del p q f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    simp [phi, del]
  | add f g hf hg =>
    simp only [map_add (f := _), Derivation.leibniz, mul_add, Finset.sum_add_distrib, hf, hg]
  | mul_X f pq hf =>
    have e : phi b I J (f * X pq) = phi b I J f * yv b (J pq.1) (I pq.2) := by rw [map_mul, phi_X]
    have hdx : del p q (X pq : Pm (Polynomial ℂ) ρ) = X (pq.1, p) * X (q, pq.2) := by simp [del, mkDerivation_X]
    rw [e, Derivation.leibniz (del p q), smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, ← hf, hdx, map_mul,
      phi_X, phi_X, phi_X]
    have hsplit : ∀ a d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f * yv b (J pq.1) (I pq.2)) =
        yv b (J pq.1) (I pq.2) * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) +
          phi b I J f * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) := by
      intro a d
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hpart : (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) =
        yv b (J pq.1) (I p) * yv b (J q) (I pq.2) := by
      rw [Finset.sum_eq_single (J pq.1), Finset.sum_eq_single (I pq.2)]
      · simp only [yv, pderiv_X, Pi.single_eq_same, mul_one]
      · intro d _ hd
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => hd (congrArg (fun x : Bool × Fin n × Fin n => x.2.2) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun d _ => ?_
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => ha (congrArg (fun x : Bool × Fin n × Fin n => x.2.1) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hpart, add_comm]


theorem opH_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    opH s m b (I p) (J q) (phi b I J f) = (-(cMn s b)) • phi b I J (opE (alMn m b) p q f) := by
  have h := deriv_part s m b I J p q f
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, opE, map_add, map_mul]
  have hs : (∑ a : Fin n, ∑ d : Fin n, (-(if b = true then Complex.I * s else -(Complex.I * s))) •
      (yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f))) =
      (-(if b = true then Complex.I * s else -(Complex.I * s))) • ∑ a : Fin n, ∑ d : Fin n,
        yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f) := by
    simp only [Finset.smul_sum]
  have h1 : phi b I J (C (alMn m b)) = C (if b = true then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) := by
    simp only [phi, rename_C, alMn]
  rw [hs, h, ← smul_add, h1, phi_X]
  rfl

theorem foldr_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ))
    (f : Pm (Polynomial ℂ) ρ) :
    (L.foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id) (phi b I J f) =
      (-(cMn s b)) ^ L.length • phi b I J ((L.foldr (fun k g => opE (alMn m b) k (σ k) ∘ₗ g) LinearMap.id) f) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, ih, map_smul, opH_phi, smul_smul, List.length_cons, pow_succ]

theorem minorOp_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (f : Pm (Polynomial ℂ) ρ) :
    minorOp s m b I J (phi b I J f) = (-(cMn s b)) ^ ρ • phi b I J (detE (alMn m b) f) := by

  simp only [minorOp, detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_phi, List.length_finRange, map_sum,
  map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, smul_comm]

theorem iter_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (N : ℕ) (f : Pm (Polynomial ℂ) ρ) :
    (minorOp s m b I J)^[N] (phi b I J f) = ((-(cMn s b)) ^ ρ) ^ N • phi b I J ((detE (alMn m b))^[N] f) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, minorOp_phi, smul_smul, Function.iterate_succ_apply', pow_succ,
      mul_comm]

theorem prodId (a : Polynomial ℂ) (c : ℂ) (ρ N : ℕ) :
    Polynomial.C (((-c) ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) =
      Polynomial.C ((c ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (-a - Polynomial.C ((l : ℂ) - i)) := by
  have e : ∀ l i : ℕ, (-a - Polynomial.C ((l : ℂ) - i)) = (-1) * (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) := by
    intro l i
    simp only [map_sub, map_natCast]
    ring
  simp_rw [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [map_pow, map_neg]
  ring

theorem minorFormula : MinorFormula := by
  intro n s hs m b ρ N I J
  have h1 : (1 : Fm n) = phi b I J 1 := (map_one _).symm
  rw [h1, iter_phi, iter]
  have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ,
      (MvPolynomial.C (alMn m b) + (l : Pm (Polynomial ℂ) ρ) - (i : Pm (Polynomial ℂ) ρ))) =
      MvPolynomial.C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (alMn m b + (l : Polynomial ℂ) - (i : Polynomial ℂ))) := by
    simp [map_prod]
  have hdet : phi b I J ((Xm (Polynomial ℂ) ρ).det) = Matrix.det (fun p q : Fin ρ => yv b (J p) (I q)) := by
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [Xm, phi_X]
  rw [hc, map_mul, map_pow, hdet]
  simp only [phi, rename_C]
  rw [Algebra.smul_def, ← mul_assoc]
  congr 1
  rw [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← map_mul]
  congr 1
  exact prodId _ _ ρ N

end PositivityTheory.Rg.Sw.SP
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

def Sop (s : ℂ) (m n : ℕ) : Set (Module.End ℂ (Fm n)) :=
  Set.range fun x : Bool × Fin n × Fin n => opH s m x.1 x.2.1 x.2.2

theorem list_prod_eq_foldr {ρ : ℕ} (f : Fin ρ → Module.End ℂ (Fm n)) (L : List (Fin ρ)) :
    (L.map f).prod = L.foldr (fun k g => f k ∘ₗ g) LinearMap.id := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Module.End.mul_eq_comp]; rfl

theorem rcp_adjoin (s : ℂ) (m : ℕ) {T : Module.End ℂ (Fm n)} (hT : T ∈ Algebra.adjoin ℂ (Sop s m n)) : RCP T := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact opH_rcp s m _ _ _
  | algebraMap r =>
    intro R q
    simp only [Module.algebraMap_end_apply, smul_mul_assoc]
  | add x y _ _ hx hy => exact rcp_add hx hy
  | mul x y _ _ hx hy => rw [Module.End.mul_eq_comp]; exact rcp_comp hx hy

theorem divZ_mono {i j : ℕ} {Q : Fm n} (hQ : DivZ i Q) (h : j ≤ i) : DivZ j Q := fun e =>
  (pow_dvd_pow _ h).trans (hQ e)

theorem cayDiv_of : CayDivOf := by
  intro hC hMZ hMZ' hNull n m s hs hm
  classical
  have hcomm : ∀ a ∈ Sop s m n, ∀ b ∈ Sop s m n, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hC n s m x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2
  letI : IsMulCommutative (Algebra.adjoin ℂ (Sop s m n)) :=
    Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing (Algebra.adjoin ℂ (Sop s m n)) := by
    open scoped IsMulCommutative in exact inferInstance
  let g : Bool × Fin n × Fin n → Algebra.adjoin ℂ (Sop s m n) :=
    fun x => ⟨opH s m x.1 x.2.1 x.2.2, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let φ : PAB n →ₐ[ℂ] Algebra.adjoin ℂ (Sop s m n) := MvPolynomial.aeval g
  have hφX : ∀ x, ((φ (X x) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = opH s m x.1 x.2.1 x.2.2 :=
    fun x => by simp [φ, g]
  have hcoe_det : ∀ {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) (Algebra.adjoin ℂ (Sop s m n))),
      ((M.det : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) =
        ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (List.finRange ρ).foldr (fun k g => ((M k (σ k) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) ∘ₗ g)
            LinearMap.id := by
    intro ρ M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    change (Algebra.adjoin ℂ (Sop s m n)).val _ = _

    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, Fin.prod_univ_def, map_list_prod, List.map_map,
      ← list_prod_eq_foldr]
    rfl
  have hcoe_minor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n),
      ((φ (minorPolynomial b I J) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = minorOp s m b I J := by
    intro b ρ I J
    rw [show minorPolynomial b I J = Matrix.det (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n)) from rfl,
      AlgHom.map_det, hcoe_det]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hφX]
    rfl
  have hcoe_cay : ((φ (Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))) :
      Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = cayF s m := by
    rw [show Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) =
        Matrix.det (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) from rfl,
      AlgHom.map_det, hcoe_det]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_add (f := _), Subalgebra.coe_add, hφX]
    rfl
  have hpow : ∀ (x : Algebra.adjoin ℂ (Sop s m n)) (N : ℕ) (Q : Fm n),
      ((x ^ N : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) Q = (x : Module.End ℂ (Fm n))^[N] Q := by
    intro x N Q
    rw [SubmonoidClass.coe_pow, Module.End.pow_apply]
  have hdivA : ∀ (x : Algebra.adjoin ℂ (Sop s m n)) {i : ℕ} {Q : Fm n}, DivZ i Q →
      DivZ i ((x : Module.End ℂ (Fm n)) Q) := fun x _ _ hQ => divZ_of_rcp (rcp_adjoin s m x.2) hQ
  have hr0 : 0 < n - m := Nat.sub_pos_of_lt hm
  obtain ⟨N₁, hN₁⟩ := hNull n m hm (n - m)
  refine ⟨N₁, fun N hN => ?_⟩
  have hmem := Ideal.mul_mem_left _
    ((Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))) ^ (N - N₁)) hN₁
  rw [pow_sub_mul_pow _ hN] at hmem
  have H := Submodule.span_induction
    (p := fun x _ => DivZ (n - m) (((φ x : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) 1))
    ?mem ?zero ?add ?smul hmem
  · rw [map_pow, hpow, hcoe_cay] at H
    exact H
  case mem =>
    intro x hx
    obtain ⟨i, j, hij, hcase⟩ := hx
    rcases hcase with ⟨hi, hj, rfl⟩ | ⟨hi, hj, I, J, rfl⟩ | ⟨hi, hj, I, J, rfl⟩ | ⟨hi, hj, I, J, I', J', rfl⟩
    · omega
    · rw [map_pow, hpow, hcoe_minor]
      exact divZ_mono (hMZ' n s hs m j (n - m) (by omega) I J) (by omega)
    · rw [map_pow, hpow, hcoe_minor]
      exact divZ_mono (hMZ n s hs m i (n - m) (by omega) I J) (by omega)
    · rw [map_mul, map_pow, map_pow, Subalgebra.coe_mul, Module.End.mul_apply, hpow, hpow, hcoe_minor, hcoe_minor]
      have hAT : (minorOp s m true I' J')^[n - m] 1 ∈ AT n :=
        iterate_AT (fun Q hQ => minorOp_true_AT s m I' J' hQ) _ (Subalgebra.one_mem _)
      have hpd := pderiv_false_AT hAT
      rw [← mul_one ((minorOp s m true I' J')^[n - m] 1), lcp_iterate (minorOp_false_lcp s m I J hpd)]
      exact divZ_mono (divZ_mul (hMZ' n s hs m j (n - m) (by omega) I' J') (hMZ n s hs m i (n - m) (by omega) I J))
        (by omega)
  case zero => simp [divZ_zero]
  case add =>
    intro x y _ _ hx hy
    rw [map_add (f := _), Subalgebra.coe_add, LinearMap.add_apply]
    exact divZ_add hx hy
  case smul =>
    intro a x _ hx
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]
    exact hdivA _ hx

end PositivityTheory.Rg.Sw.SP
end
end

section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem evQ_mul (s z : ℂ) (P Q : Fm n) (B : MC n) : evQ s z (P * Q) B = evQ s z P B * evQ s z Q B := by
  simp [evQ]

theorem evQ_add (s z : ℂ) (P Q : Fm n) (B : MC n) : evQ s z (P + Q) B = evQ s z P B + evQ s z Q B := by
  simp [evQ]

theorem evQ_sum (s z : ℂ) {ι : Type} (t : Finset ι) (P : ι → Fm n) (B : MC n) :
    evQ s z (∑ i ∈ t, P i) B = ∑ i ∈ t, evQ s z (P i) B := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evQ, map_sum]

theorem evQ_CC (s z a : ℂ) (B : MC n) : evQ s z (MvPolynomial.C (Polynomial.C a)) B = a := by
  simp [evQ]

theorem evQ_C (s z : ℂ) (p : Polynomial ℂ) (B : MC n) : evQ s z (MvPolynomial.C p) B = p.eval z := by
  simp [evQ]

theorem evQ_yv (s z : ℂ) (b : Bool) (i j : Fin n) (B : MC n) : evQ s z (yv b i j) B = vals s B (b, i, j) := by
  simp [evQ, yv]

theorem evQ_multPart (s z : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (multPart s m b k l Q) B = -(cB s b) * ((alB m b).eval z * vals s B (b, l, k) * evQ s z Q B) := by
  rw [multPart_apply, evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_C, evQ_yv]

theorem evQ_derPart (s z : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) (B : MC n) :
    evQ s z (derPart s b k l Q) B = ∑ a : Fin n, ∑ d : Fin n,
      -(cB s b) * (vals s B (b, a, k) * vals s B (b, l, d) * evQ s z (MvPolynomial.pderiv (b, a, d) Q) B) := by
  rw [derPart_apply, evQ_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [evQ_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [evQ_mul, evQ_CC, evQ_mul, evQ_mul, evQ_yv, evQ_yv]

theorem trace_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (Y * Matrix.of (eU k l)).trace = Y l k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hb]
  · simp

theorem sandwich_eU (Y : Matrix (Fin n) (Fin n) ℂ) (k l a d : Fin n) :
    (Y * Matrix.of (eU k l) * Y) a d = Y a k * Y l d := by
  simp only [Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    · simp
    intro j _
    simp [hb]
  · simp

end PositivityTheory.Rg.Sw.SP
end
end
