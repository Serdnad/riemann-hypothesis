module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueConjugationOfEllipticCMTheorems
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.hermitianLineBundle_isNef_shift_monotone : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' → (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.NefShift.isNef_shift_mono | exact GlobalTheory.NefShift.isNef_shift_mono | (intros; apply GlobalTheory.NefShift.isNef_shift_mono <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.SelfInterGrowth

open MvPolynomial

theorem expand (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Φ ((X 0 + C t * X 1) ^ (D + 1)) = ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) := by

  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (a : ℝ), L.IsSelfInter a → ∃ α : ℕ → ℝ, (∀ n, ((L.pow n).tens A).IsSelfInter (α n)) ∧ Tendsto (fun n : ℕ => α n / (n : ℝ) ^ (D + 1)) atTop (𝓝 a) := by
  intro hC k _ Y _ p D hX L A a ha
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).1
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  refine ⟨fun n => Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)), fun n => ?_, ?_⟩
  · exact (hiso n).isSelfInter hX (hΦ.1 _)
  have h0 : Φ (X 0 ^ (D + 1)) = a :=
    HermLB.IsSelfInter.unique hX ((((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1 0)) ha
  set f : ℝ → ℝ := fun t => Φ ((X 0 + C t * X 1) ^ (D + 1)) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1 + 1),
      t ^ (D + 1 - m) * Φ (X 0 ^ m * X 1 ^ (D + 1 - m) * ((D + 1).choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Φ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = a := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = Φ (lin (fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) ^ (D + 1)) / (n : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hlin, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.SelfInterGrowth
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.DegGrowth

open MvPolynomial

theorem expand (Ψ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Ψ ((X 0 + C t * X 1) ^ D) = ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) := by

  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_pow, ← map_pow, ← smul_eq_mul (a := t ^ _), ← map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  ring

theorem main : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, Tendsto (fun n : ℕ => gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D) atTop (𝓝 (gdeg L D)) := by
  intro hC k _ Y _ p D hX L A
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![L, A]).2
  have hlin (n : ℕ) : (lin fun i => (((![(n : ℤ), 1] : Fin 2 → ℤ) i : ℤ) : ℝ)) = C (n : ℝ) * X 0 + C 1 * X 1 := by
    simp [lin, Fin.sum_univ_two]
  have hiso (n : ℕ) : (comb ![L, A] ![(n : ℤ), 1]).Isometric ((L.pow n).tens A) := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, HermLB.icls_tens, HermLB.icls_pow, Fin.sum_univ_two, natCast_zsmul]
  have hiso0 : (comb ![L, A] ![1, 0]).Isometric L := by
    refine HermLB.icls_eq_iff.1 ?_
    simp [icls_comb, Fin.sum_univ_two]
  have hlin0 : (lin fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℝ)) = (X 0 : MvPolynomial (Fin 2) ℝ) := by
    simp [lin, Fin.sum_univ_two]
  have h0 : Ψ (X 0 ^ D) = gdeg L D := by
    rw [← hlin0, hΨ.1, hiso0.gdeg_eq]
  have hn_eq (n : ℕ) : gdeg ((L.pow n).tens A) D = Ψ ((C (n : ℝ) * X 0 + C 1 * X 1) ^ D) := by
    rw [← (hiso n).gdeg_eq, ← hΨ.1, hlin]
  set f : ℝ → ℝ := fun t => Ψ ((X 0 + C t * X 1) ^ D) with hf
  have hfc : Continuous f := by
    have : f = fun t => ∑ m ∈ Finset.range (D + 1),
      t ^ (D - m) * Ψ (X 0 ^ m * X 1 ^ (D - m) * (D.choose m : MvPolynomial (Fin 2) ℝ)) :=
      funext fun t => expand Ψ D t
    rw [this]
    fun_prop
  have hf0 : f 0 = gdeg L D := by simp [hf, h0]
  have hev : ∀ᶠ n : ℕ in atTop, f (1 / (n : ℝ)) = gdeg ((L.pow n).tens A) D / (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    have e : C (n : ℝ) * X 0 + C 1 * X 1 = C (n : ℝ) * (X 0 + C (1 / (n : ℝ)) * X 1 : MvPolynomial (Fin 2) ℝ) := by
      rw [mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hn']
    rw [hn_eq, e, mul_pow, ← map_pow, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hn')]
  have ht := (hfc.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  rw [hf0] at ht
  exact ht.congr' hev

end GlobalTheory.DegGrowth
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.PolForm

def expv {ι : Type} {n : ℕ} (c : Fin n → ι) : ι →₀ ℕ := ∑ a, Finsupp.single (c a) 1

theorem prod_X_eq {ι : Type} {n : ℕ} (c : Fin n → ι) :
    (∏ a, X (c a) : MvPolynomial ι ℝ) = monomial (expv c) 1 := by
  rw [expv, monomial_sum_one]; rfl

theorem expv_apply {ι : Type} [DecidableEq ι] {n : ℕ} (c : Fin n → ι) (i : ι) :
    expv c i = Fintype.card {a // c a = i} := by
  rw [expv, Finsupp.finsetSum_apply, Fintype.card_subtype]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole]
  simp

theorem weight_expv {ι : Type} {n : ℕ} (c : Fin n → ι) : Finsupp.weight 1 (expv c) = n := by

  simp [expv, map_sum, Finsupp.weight_apply, Finsupp.sum_single_index]

theorem exists_perm_of_expv_eq {ι : Type} {n : ℕ} {c c' : Fin n → ι} (h : expv c = expv c') :
    ∃ e : Equiv.Perm (Fin n), ∀ a, c' a = c (e a) := by
  classical
  have hc : ∀ i, Fintype.card {a // c' a = i} = Fintype.card {a // c a = i} := fun i => by
    have := congrArg (fun s => s i) h
    simp only [expv_apply] at this
    convert this.symm
  let E : ∀ i, {a // c' a = i} ≃ {a // c a = i} := fun i => Fintype.equivOfCardEq (hc i)
  refine ⟨(Equiv.sigmaFiberEquiv c').symm.trans ((Equiv.sigmaCongrRight E).trans (Equiv.sigmaFiberEquiv c)),
    fun a => ?_⟩
  show c' a = c (E (c' a) ⟨a, rfl⟩).1
  exact (E (c' a) ⟨a, rfl⟩).2.symm

end GlobalTheory.MixHt.PolForm

namespace GlobalTheory.MixHt


open PolForm in
theorem exists_linear_of_multiadditive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (d : ℕ) (F : (Fin (d + 1) → HermLB p) → ℝ), (∀ L M, (∀ a, (L a).Isometric (M a)) → F L = F M) → (∀ L (e : Equiv.Perm (Fin (d + 1))), F (fun a => L (e a)) = F L) → (∀ (A B : HermLB p) (L : Fin d → HermLB p), F (Fin.cons (A.tens B) L) = F (Fin.cons A L) + F (Fin.cons B L)) → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, (∀ n : Fin (d + 1) → ι → ℤ, Φ (∏ a, lin fun i => (n a i : ℝ)) = F fun a => comb L (n a)) ∧ ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d + 1 → P.IsHomogeneous e → Φ P = 0 := by
  intro k _ X p d F hiso hsymm hadd ι _ L
  classical
  let rep : HermLB.IsomClass p → HermLB p := fun x => Quotient.out (s := HermLB.isometrySetoid p) x
  have hrepcls : ∀ x, (rep x).icls = x := fun x => Quotient.out_eq (s := HermLB.isometrySetoid p) x
  let G' : (Fin (d + 1) → HermLB.IsomClass p) → ℝ := fun v => F fun a => rep (v a)
  have hG : ∀ M : Fin (d + 1) → HermLB p, G' (fun a => (M a).icls) = F M :=
    fun M => hiso _ _ fun a => HermLB.icls_eq_iff.1 (hrepcls _)
  have hGs : ∀ v (e : Equiv.Perm (Fin (d + 1))), G' (fun a => v (e a)) = G' v :=
    fun v e => hsymm (fun a => rep (v a)) e
  have hG0 : ∀ (x y : HermLB.IsomClass p) (w : Fin d → HermLB.IsomClass p),
      G' (Fin.cons (x + y) w) = G' (Fin.cons x w) + G' (Fin.cons y w) := by
    intro x y w
    have hc : ∀ z, (fun a => rep ((Fin.cons z w : Fin (d + 1) → HermLB.IsomClass p) a)) =
        Fin.cons (rep z) (fun a => rep (w a)) := fun z => by
      funext a; exact Fin.cases rfl (fun _ => rfl) a
    show F (fun a => rep ((Fin.cons (x + y) w : Fin (d + 1) → HermLB.IsomClass p) a)) =
      F (fun a => rep ((Fin.cons x w : Fin (d + 1) → HermLB.IsomClass p) a)) +
        F (fun a => rep ((Fin.cons y w : Fin (d + 1) → HermLB.IsomClass p) a))
    rw [hc, hc, hc, ← hadd]
    refine hiso _ _ fun a => Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero]
      exact HermLB.icls_eq_iff.1 (by rw [HermLB.icls_tens, hrepcls, hrepcls, hrepcls])
    · simp only [Fin.cons_succ]; exact HermLB.Isometric.refl _
  have h0 : ∀ (q : Fin (d + 1) → HermLB.IsomClass p) (x y : HermLB.IsomClass p),
      G' (Function.update q 0 (x + y)) = G' (Function.update q 0 x) + G' (Function.update q 0 y) := by
    intro q x y
    rw [← Fin.cons_self_tail q, Fin.update_cons_zero, Fin.update_cons_zero, Fin.update_cons_zero]
    exact hG0 x y _
  have hGi : ∀ (m : Fin (d + 1) → HermLB.IsomClass p) (i : Fin (d + 1)) (x y : HermLB.IsomClass p),
      G' (Function.update m i (x + y)) = G' (Function.update m i x) + G' (Function.update m i y) := by
    intro m i x y
    have key : ∀ z, G' (Function.update m i z) = G' (Function.update (m ∘ Equiv.swap 0 i) 0 z) := fun z => by
      rw [← hGs (Function.update m i z) (Equiv.swap 0 i)]
      show G' (Function.update m i z ∘ Equiv.swap 0 i) = _
      rw [Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
    rw [key, key, key]
    exact h0 _ x y
  let Mlt : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => HermLB.IsomClass p) ℝ :=
    { toFun := G'
      map_update_add' := by
        intro inst m i x y
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact hGi m i x y
      map_update_smul' := by
        intro inst m i c x
        obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun z => G' (Function.update m i z)) (hGi m i)) c x }
  let g : ι → HermLB.IsomClass p := fun i => (L i).icls
  let f : (Fin (d + 1) → ι) → ℝ := fun c => G' fun a => g (c a)
  have hf : ∀ c (e : Equiv.Perm (Fin (d + 1))), f (fun a => c (e a)) = f c := fun c e => hGs (fun a => g (c a)) e
  have hF : ∀ n : Fin (d + 1) → ι → ℤ, F (fun a => comb L (n a)) =
      ∑ c : Fin (d + 1) → ι, (∏ a, (n a (c a) : ℝ)) * f c := by
    intro n
    rw [← hG]
    simp only [icls_comb]
    have e1 := Mlt.map_sum (fun a i => n a i • g i)
    have e2 : ∀ c : Fin (d + 1) → ι, Mlt (fun a => n a (c a) • g (c a)) = (∏ a, (n a (c a) : ℝ)) * f c := by
      intro c
      rw [Mlt.map_smul_univ (fun a => n a (c a)) (fun a => g (c a)), zsmul_eq_mul, Int.cast_prod]
      rfl
    simp only [e2] at e1
    exact e1
  let φ : (ι →₀ ℕ) → ℝ := fun s => if h : ∃ c : Fin (d + 1) → ι, expv c = s then f h.choose else 0
  have hφ : ∀ c, φ (expv c) = f c := by
    intro c
    have h : ∃ c' : Fin (d + 1) → ι, expv c' = expv c := ⟨c, rfl⟩
    simp only [φ, dif_pos h]
    obtain ⟨e, he⟩ := exists_perm_of_expv_eq h.choose_spec
    rw [← hf h.choose e]
    exact congrArg f (funext fun a => (he a).symm)
  let Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ := (basisMonomials ι ℝ).constr ℝ φ
  have hΦ : ∀ s, Φ (monomial s 1) = φ s := by
    intro s
    have := (basisMonomials ι ℝ).constr_basis ℝ φ s
    rwa [coe_basisMonomials] at this
  refine ⟨Φ, fun n => ?_, fun P e he hP => ?_⟩
  · rw [hF]
    simp only [lin]

    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, prod_X_eq, C_mul', map_smul, hΦ, hφ, smul_eq_mul]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hm : monomial s (AddMonoidAlgebra.coeff P s) = AddMonoidAlgebra.coeff P s • monomial s (1 : ℝ) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, hΦ, smul_eq_mul]
    refine mul_eq_zero_of_right _ (dif_neg ?_)
    rintro ⟨c, rfl⟩
    have := hP (mem_support_iff.1 hs)
    rw [weight_expv] at this
    exact he this.symm

end GlobalTheory.MixHt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.Published

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem ArFormExists.exists_isArithHeight (H : ArFormExists) (hX : IsArithVar p D) (L : HermLB p) :
    ∃ h, L.IsArithHeight h := by
  obtain ⟨Φ, hΦ⟩ := H k X p D hX Unit fun _ => L
  obtain ⟨h, hh, -⟩ := hΦ.1 (Pi.single () 1)
  exact ⟨h, (isometric_comb_single (fun _ : Unit => L) ()).isArithHeight hX hh⟩

theorem ArMix.fnB_of_height (H : ArMix) (hX : IsArithVar p D) {ι : Type} [Fintype ι] {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) D Φ) (n : ι → ℤ) {h : X → ℝ}
    (hh : (comb L n).IsArithHeight h) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  have := hX.isLocallyNoetherian
  have hr : IsRatSec (ArInt.fnB u hu hc).B fun _ => 1 := fun a b h =>
    (map_one _).symm.trans (mul_one _).symm
  have he (z : X) : ((ArInt.fnB u hu hc).div hr).IsEqn z 1 :=
    (presents_divOfRatSec _ hr).isEqn PUnit.unit z trivial
  have h₁ (z : X) : ((ArInt.fnB u hu hc).div hr).mult z = 0 := (he z).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) : offSupp p σ ((ArInt.fnB u hu hc).div hr) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => (he _).mem_supp_iff.1 hy (unitAt_one _)
  have h₃ (σ) : logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ => 1) = fun y => -(1 / 2) * u σ y := funext fun y => by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    change 0 - u σ y / 2 = _
    ring
  rw [(H k X p D hX ι _ L Φ hΦ n h hh _ hr).2, HermLB.archInt, chInt]
  simp only [h₁, h₂, h₃, Weight.chernInt_const_mul, Int.cast_zero, zero_mul, finsum_zero, ← mul_finsum]
  ring

theorem arExists_of_form_of_mix : ArFormExists → ArMix → ArExists := by
  intro HF HM k _ X _ p D hX
  refine ⟨HF.exists_isArithHeight hX, fun ι _ L => ⟨HF k X p D hX ι L, ?_⟩⟩
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => (2 : ℝ)) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => (2 : ℝ)).IsConj
      (Weight.ofFun (σ := σ') fun _ => (2 : ℝ)) := fun _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := HF k X p D hX _ fun o : Option ι => o.elim (ArInt.fnB (fun _ _ => 2) hu hc) L
  refine ⟨Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (rename (R := ℝ) (some : ι → Option ι)).toLinearMap,
    fun n => ?_, fun P d hd hP => ?_⟩
  · obtain ⟨h, hh⟩ := HF.exists_isArithHeight hX (comb L n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, LinearMap.mulLeft_apply,
      HM.fnB_of_height hX hΦ n hh, gdeg, chInt, chInt, mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← Weight.chernInt_const_mul]
    norm_num
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
    exact hΦ.2 _ (1 + d) (by omega) ((isHomogeneous_X ℝ none).mul hP.rename_isHomogeneous)

end GlobalTheory.Published
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory

namespace HermLB

theorem Isometric.semiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  intro k _ X p L M D h hL σ a c y hy ξ
  have hb := mem_pick (L.φ σ).isLB y
  have hL' := hL σ _ c y ⟨hy.1, hb⟩ ξ
  have e := h.hess_eq c hy.1 hy.2 hb
  have hM : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((M.φ σ).φ a (c.e.symm v) : ℂ)) (c.e y) ξ =
      ∑ j, ∑ l, c.hess (M.φ σ) a y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  have hL₂ : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((L.φ σ).φ (pick (L.φ σ).isLB y) (c.e.symm v) : ℂ))
      (c.e y) ξ = ∑ j, ∑ l, c.hess (L.φ σ) (pick (L.φ σ).isLB y) y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  rw [hM, e, ← hL₂]
  exact hL'

end HermLB

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GdegPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_comb_unit (L : HermLB p) (n : ℕ) :
    (comb (fun _ : Unit => L) fun _ => (n : ℤ)).Isometric (L.pow n) :=
  HermLB.icls_eq_iff.1 (by rw [icls_comb, HermLB.icls_pow, Fintype.sum_unique, natCast_zsmul])

theorem lin_unit (c : ℝ) : (lin fun _ : Unit => c) = c • (MvPolynomial.X () : MvPolynomial Unit ℝ) := by
  rw [lin, Fintype.sum_unique, MvPolynomial.C_mul']

theorem gdeg_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), gdeg (L.pow n) D = (n : ℝ) ^ D * gdeg L D := by
  intro hC k _ X _ p D hX L n
  obtain ⟨Ψ, hΨ, -⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).2
  have key (m : ℕ) : gdeg (L.pow m) D = (m : ℝ) ^ D * Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (isometric_comb_unit L m).gdeg_eq, ← hΨ fun _ => (m : ℤ)]
    simp only [Int.cast_natCast]
    rw [lin_unit, smul_pow, map_smul, smul_eq_mul]
  have h1 : gdeg L D = Ψ ((MvPolynomial.X () : MvPolynomial Unit ℝ) ^ D) := by
    rw [← (HermLB.icls_eq_iff.1 (by rw [HermLB.icls_pow, one_smul]) : (L.pow 1).Isometric L).gdeg_eq, key 1]
    simp
  rw [key n, h1]

end GlobalTheory.GdegPow
end
end

section

namespace GlobalTheory.Published

theorem arShift_of_arChange : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  intro hE hC k _ X _ p D hX L a t ha
  have h := GlobalTheory.TwistTop.isSelfInter_shift hE hC k X p D hX L a (fun _ => t) (fun _ => rfl) ha
  rw [← mul_finsum, ← mul_assoc] at h
  exact h

end GlobalTheory.Published
end

section


theorem _root_.GlobalTheory.T.latticeValueConjugation_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatConj := by
  first | exact @GlobalTheory.LatConjEll.latConj | exact GlobalTheory.LatConjEll.latConj | (intros; apply GlobalTheory.LatConjEll.latConj <;> assumption)
end

section


theorem _root_.GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  first | exact @GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | exact GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | (intros; apply GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen <;> assumption)
end
