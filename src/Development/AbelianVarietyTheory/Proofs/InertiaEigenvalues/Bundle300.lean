module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle274
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

variable {l : ℕ} [Fact l.Prime]

theorem acris_lim_pt (s : ℕ → Per.Acris0 l)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris0 l, s n - s (l ^ r) = ((l : ℕ) : Per.Acris0 l) ^ r * z) :
    ∃ y : Per.Acris l, ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris l,
      y - algebraMap (Per.Acris0 l) (Per.Acris l) (s n) = ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨y, hy⟩ := Model.pc_lim (l := l) (Per.Acris0 l) s hs
  refine ⟨e.symm y, fun r n hn => ?_⟩
  obtain ⟨z, hz⟩ := hy r n hn
  refine ⟨e.symm z, e.injective ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, e.apply_symm_apply, e.apply_symm_apply, he]
  exact hz

theorem frobenius_surjective_modP : Function.Surjective (frobenius (ModP (Per.OC l) l) l) := by
  apply _root_.GlobalTheory.MemLoc.ThetaD.frob_surj <;> assumption

theorem θ_surjective : Function.Surjective (Per.θ l) :=
  surjective_fontaineTheta frobenius_surjective_modP

theorem exists_divPow {w : Per.Ainf l} (hw : InJ w) (k : ℕ) :
    ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) w ^ k := by
  obtain ⟨c, hc⟩ := hw
  obtain ⟨a, ha⟩ := θ_surjective (l := l) c
  have hz : Per.θ l (w - (l : Per.Ainf l) * a) = 0 := by
    rw [map_sub, map_mul, map_natCast, ha, hc, sub_self]
  have hd : ∀ j : ℕ, ∃ d : Per.AinfP l, d ∈ Per.Acris0 l ∧ ((j.factorial : ℕ) : Per.AinfP l) * d =
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
    intro j
    obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ j.factorial_ne_zero).exists_right_inv
    have e : ((j.factorial : ℕ) : Per.AinfP l) *
        (u * algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) ^ j := by
      rw [← mul_assoc, hu, one_mul]
    exact ⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l _ j _ hz e, e⟩
  choose d hdm hdd using hd
  choose q hq using fun m : ℕ => GlobalTheory.RingBasics.exists_pow_div_factorial l m
  let ζ : ℤ_[l] →+* Per.AinfP l := (algebraMap (Per.Ainf l) (Per.AinfP l)).comp (Per.zA l)
  have hq' : ∀ m : ℕ, ((m.factorial : ℕ) : Per.AinfP l) * ζ (q m) = ((l : ℕ) : Per.AinfP l) ^ m := by
    intro m
    have h := congrArg ζ (hq m)
    rwa [map_mul, map_natCast, map_pow, map_natCast] at h
  have hg : (∑ m ∈ Finset.range (k + 1), ζ (q m) * algebraMap (Per.Ainf l) (Per.AinfP l) a ^ m *
      d (k - m)) ∈ Per.Acris0 l := by
    refine Subalgebra.sum_mem _ fun m _ => mul_mem (mul_mem ?_ (pow_mem (Subalgebra.algebraMap_mem _ _) _))
      (hdm _)
    exact Subalgebra.algebraMap_mem _ (Per.zA l (q m))
  refine ⟨⟨_, hg⟩, ?_⟩
  have hw' : algebraMap (Per.Ainf l) (Per.AinfP l) w = ((l : ℕ) : Per.AinfP l) * algebraMap (Per.Ainf l) (Per.AinfP l) a +
      algebraMap (Per.Ainf l) (Per.AinfP l) (w - (l : Per.Ainf l) * a) := by
    rw [map_sub, map_mul, map_natCast]
    ring
  show _ * ∑ m ∈ Finset.range (k + 1), _ = _
  rw [hw', add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hf : ((k.factorial : ℕ) : Per.AinfP l) = ((k.choose m : ℕ) : Per.AinfP l) *
      ((m.factorial : ℕ) : Per.AinfP l) * (((k - m).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hmk]
  rw [hf, mul_pow, ← hq' m, ← hdd (k - m)]
  ring

theorem exists_isLogJ : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l), InJ w → ∃ y : Per.Acris l, IsLogJ w y := by
  intro l _ w hw
  have hl : l.Prime := Fact.out
  choose g hg using exists_divPow hw
  let s : ℕ → Per.Acris0 l := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)
  obtain ⟨y, hy⟩ := acris_lim_pt s (by
    intro r n hn
    have : ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r) := by
      simp only [s]
      rw [← Finset.sum_Ico_eq_sub _ hn]
      refine Finset.dvd_sum fun k hk => ?_
      have h1 : l ^ r ∣ k.factorial := Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1
      have h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l) := by
        exact_mod_cast Nat.cast_dvd_cast (α := Per.Acris0 l) h1
      exact (h2.mul_left _).mul_right _
    exact this)
  refine ⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩
  simp only [s]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.AinfP l) h1
  rw [← hg (k + 1), Nat.factorial_succ]
  generalize ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢
  rw [h2]
  push_cast
  ring

end GlobalTheory.LogU
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

variable {l : ℕ} [Fact l.Prime]

theorem coe_emb_algebraMap (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (x : ℤ_[l]) :
    algebraMap (Om l) (PadicComplex l) (τ ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1)) = zC x := by
  have h : ((algebraMap ℤ_[l] ↥(OL LL) x : ↥(OL LL)) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (x : ℚ_[l]) := by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl
  rw [h, AlgHom.commutes]; rfl

theorem exists_evEmb (LL : FinExt l) (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) :
    ∃ ev : OCO LL →+* PadicComplex l, ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)) := by
  letI : Algebra ℤ_[l] (PadicComplex l) :=
    ((algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom).toAlgebra
  let u : OC l →ₐ[ℤ_[l]] PadicComplex l :=
    { (PadicComplexInt l).subtype with commutes' := fun x => rfl }
  let v : ↥(OL LL) →ₐ[ℤ_[l]] PadicComplex l :=
    { (algebraMap (Om l) (PadicComplex l)).comp (τ.toRingHom.comp (OL LL).val.toRingHom) with
      commutes' := fun x => coe_emb_algebraMap LL τ x }
  exact ⟨(Algebra.TensorProduct.productMap u v).toRingHom, fun c a => rfl⟩

theorem evEmb_eq_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (τ : ↥LL.1 →ₐ[ℚ_[l]] Om l) (ev : OCO LL →+* PadicComplex l)
    (hev : ∀ (c : OC l) (a : ↥(OL LL)),
      ev (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) * algebraMap (Om l) (PadicComplex l) (τ (a : ↥LL.1)))
    (x : OCO LL) :
    ev x = ∑ k, kap o x k * algebraMap (Om l) (PadicComplex l) (τ (o k : ↥LL.1)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, kap_zero, zero_mul, Finset.sum_const_zero]
  | add x y hx hy =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add ev, kap_add, hx, hy, add_mul, Finset.sum_add_distrib]
  | tmul c a =>
    rw [hev]
    simp only [kap_tmul, mul_assoc, ← Finset.mul_sum]
    congr 1
    conv_lhs => rw [← o.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
      map_mul, coe_emb_algebraMap]

theorem exists_emb_det_ne_zero {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) :
    ∃ τ : Fin f → (↥LL.1 →ₐ[ℚ_[l]] Om l),
      (Matrix.of fun i j => τ j (o i : ↥LL.1) : Matrix (Fin f) (Fin f) (Om l)).det ≠ 0 := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  haveI := IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  let b := o.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) ↥LL.1
  have hb : ∀ i, b i = (o i : ↥LL.1) := fun i =>
    Module.Basis.localizationLocalization_apply _ _ _ _ i
  have hc : Fintype.card (Fin f) = Fintype.card (↥LL.1 →ₐ[ℚ_[l]] Om l) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b]
  let e := Fintype.equivOfCardEq hc
  refine ⟨e, fun h0 => ?_⟩
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ_[l] (Om l) b e
  have h2 : Algebra.embeddingsMatrixReindex ℚ_[l] (Om l) b e =
      Matrix.of fun i j => e j (o i : ↥LL.1) := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, hb]
  rw [h2, h0, zero_pow two_ne_zero, map_eq_zero] at h1
  exact Algebra.discr_not_zero_of_basis ℚ_[l] b h1

theorem kap_idem_algebraic {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (e : OCO LL) (he : IsIdempotentElem e) (k : Fin f) :
    ∃ x : Om l, algebraMap (Om l) (PadicComplex l) x = kap o e k := by
  obtain ⟨τ, hτ⟩ := exists_emb_det_ne_zero o
  set M : Matrix (Fin f) (Fin f) (Om l) := Matrix.of fun i j => τ j (o i : ↥LL.1) with hM
  have hy : ∀ j, ∃ y : Om l, algebraMap (Om l) (PadicComplex l) y =
      ∑ k, kap o e k * algebraMap (Om l) (PadicComplex l) (M k j) := by
    intro j
    obtain ⟨ev, hev⟩ := exists_evEmb LL (τ j)
    have h1 := evEmb_eq_sum o (τ j) ev hev e
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 (he.map ev) with h | h
    · exact ⟨0, by rw [map_zero, ← h, h1]; rfl⟩
    · exact ⟨1, by rw [map_one, ← h, h1]; rfl⟩
  choose y hy using hy
  refine ⟨∑ j, y j * M⁻¹ j k, ?_⟩
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (Ne.isUnit hτ)

  simp only [map_sum, map_mul, hy, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

  simp only [← Finset.mul_sum, ← map_mul, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply]
  simp [apply_ite (algebraMap (Om l) (PadicComplex l))]

theorem kap_idem_mem_inC (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l))
    (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL)
    (hact : IsActC act) (he : IsIdempotentElem e)
    (hfix : ∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) (k : Fin f) : kap o e k ∈ inC K.1 := by
  obtain ⟨x, hx⟩ := kap_idem_algebraic o e he k
  refine ⟨x, ?_, hx⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1]
  rintro ⟨g, hg⟩
  have h1 := hfix g hg k
  rw [← hx] at h1
  apply (algebraMap (Om l) (PadicComplex l)).injective
  exact (hact.1 g x).symm.trans h1

end GlobalTheory.Cyc.Decomp
end
end

section

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem actMat_props {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t)
    [CommRing C] (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N)
    (A : O → Matrix (Fin d) (Fin d) C) (hA : ∀ a i j, A a i j = φ (b.repr (a • b j) i)) :
    (∀ a a', A (a + a') = A a + A a') ∧ (∀ (x : Z) a, A (x • a) = φ x • A a) ∧ A 1 = 1 ∧
      ∀ a a', A (a * a') = A a * A a' := by
  have hc : ∀ (a : O) (x : Z) (t : N), a • (x • t) = x • (a • t) := by
    intro a x t
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  refine ⟨fun a a' => ?_, fun x a => ?_, ?_, fun a a' => ?_⟩
  · ext i j
    simp only [hA, Matrix.add_apply, add_smul, map_add (f := _), Finsupp.add_apply]
  · ext i j
    have hx : (x • a) • b j = x • (a • b j) := by
      rw [Algebra.smul_def, mul_smul, ← hs]
    simp only [hA, Matrix.smul_apply, hx, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  · ext i j
    rw [hA, one_smul, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [Finsupp.single_apply, Matrix.one_apply, h, Ne.symm h]
  · ext i j
    rw [Matrix.mul_apply, hA, mul_smul]
    conv_lhs => rw [← b.sum_repr (a' • b j)]
    rw [Finset.smul_sum]

    simp only [hc, map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
    smul_eq_mul, map_mul, hA]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {l : ℕ} [Fact l.Prime]

theorem lamMul_lam_add {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x y : OCO LL) :
    lam o A (x + y) = lam o A x + lam o A y := by
  simp only [lam, kap_add, add_smul, Finset.sum_add_distrib]

theorem lamMul_lam_zero {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) :
    lam o A 0 = 0 := by
  simp only [lam, kap_zero, zero_smul, Finset.sum_const_zero]

theorem lam_mul_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  intro l _ K LL T d f M A o h
  letI := zlMod LL T
  obtain ⟨b, -, hA⟩ := h
  let φ : ℤ_[l] →+* PadicComplex l := (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, φ x = zC x := fun _ => rfl
  obtain ⟨Pa, Ps, P1, Pm⟩ := actMat_props (Z := ℤ_[l]) (O := ↥(OL LL)) (N := ↥T.L.T)
    (fun _ _ => rfl) φ b A (fun a i j => hA a i j)
  have hsum : ∀ a, A a = ∑ k, zC (o.repr a k) • A (o k) := by
    intro a
    have e := map_sum (AddMonoidHom.mk' A Pa) (fun k => o.repr a k • o k) Finset.univ
    simp only [AddMonoidHom.mk'_apply, o.sum_repr] at e
    rw [e]
    simp only [Ps, hφ]
  have ht : ∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a := by
    intro c a
    rw [hsum a, Finset.smul_sum]
    simp only [lam, kap_tmul, mul_smul]
  refine ⟨ht, P1, Pm, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp [lamMul_lam_zero]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero => simp [lamMul_lam_zero]
    | tmul c' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, ht, ht, ht, Pm, smul_mul_smul_comm]
      rfl
    | add y₁ y₂ h₁ h₂ => rw [mul_add, lamMul_lam_add, lamMul_lam_add, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, lamMul_lam_add, lamMul_lam_add, h₁, h₂, add_mul]

end GlobalTheory.Cyc.Decomp
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

theorem card_eq_finrank_mul_card {Z O R T : Type} [CommRing Z] [Nontrivial Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing R] [Nontrivial R] [Algebra O R]
    [AddCommGroup T] [Module O T] [Module.Free O T] [Module Z T] [IsScalarTower Z O T]
    {d : ℕ} (b : Module.Basis (Fin d) Z T) {ι : Type} [Fintype ι] (v : ι → R ⊗[O] T)
    (h1 : LinearIndependent R v) (h2 : Submodule.span R (Set.range v) = ⊤) :
    d = Module.finrank Z O * Fintype.card ι := by
  have e1 : Module.finrank Z T = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have e2 : Module.finrank R (R ⊗[O] T) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk h1 h2.ge)
  rw [← e1, ← e2, Module.finrank_baseChange, Module.finrank_mul_finrank]

theorem nontrivial_tensor_of_free {Z O S : Type} [CommRing Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing S] [Nontrivial S] [Algebra Z S] :
    Nontrivial (O ⊗[Z] S) := by
  haveI : Module.FaithfullyFlat Z O := inferInstance
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem rank_count : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  intro l _ K LL T d M A ι _ v hM h1 h2
  haveI := freeOL LL
  haveI := finiteOL LL
  letI := zlMod LL T
  obtain ⟨b, -, -⟩ := hM
  haveI : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  haveI : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : Nontrivial (RW LL) := nontrivial_tensor_of_free
  have h := card_eq_finrank_mul_card (R := RW LL) b v h1 h2
  refine ⟨Module.finrank ℤ_[l] ↥(OL LL), Module.finBasis _ _, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simpa using h

end GlobalTheory.Cyc.Decomp
end
end

section

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem ringHom_padicInt_OC_ext (f g : ℤ_[l] →+* OC l) (x : ℤ_[l]) : f x = g x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn : ‖((l : ℕ) : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
    have h := norm_zC ((l : ℕ) : ℤ_[l])
    rw [PadicInt.norm_p] at h
    rw [← h]
    simp [zC]
  have key : ∀ k : ℕ, ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ ((l : ℝ)⁻¹) ^ k := by
    intro k
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + y * (l : ℤ_[l]) ^ k := by rw [hy]; ring
    have h1 : f x - g x = (f y - g y) * ((l : ℕ) : OC l) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    have h2 : ((f x - g x : OC l) : PadicComplex l) =
        ((f y - g y : OC l) : PadicComplex l) * ((l : ℕ) : PadicComplex l) ^ k := by
      rw [h1]; push_cast; rfl
    rw [h2, norm_mul, norm_pow, hn]
    exact mul_le_of_le_one_left (by positivity) ((mem_OC _).1 (f y - g y).2)
  have h0 : ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hl)) key
  have h3 : f x - g x = 0 := Subtype.ext (norm_le_zero_iff.1 h0)
  exact sub_eq_zero.1 h3

theorem map_frobeniusEquiv_symm_OCb (e : OCb l →+* OCb l) (x : OCb l) :
    e ((frobeniusEquiv (OCb l) l).symm x) = (frobeniusEquiv (OCb l) l).symm (e x) := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]

theorem exists_thetaShift_ringHom {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) :
    ∃ θ : Ainf l →+* OC l,
      (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
        AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
      ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n) := by
  induction n with
  | zero =>
    obtain ⟨θ, -, -, h1, -, h2⟩ := exists_isTheta l P AI
    exact ⟨θ, h1, h2⟩
  | succ n ih =>
    obtain ⟨θ, h1, h2⟩ := ih
    refine ⟨θ.comp (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom), fun g a => ?_,
      fun j => ?_⟩
    · have e : WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.actW g a) =
          AI.actW g (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom a) :=
        WittVector.ext fun k =>
          (map_frobeniusEquiv_symm_OCb (AI.actT g).toRingHom (a.coeff k)).symm
      rw [RingHom.comp_apply, RingHom.comp_apply, e, h1]
    · have e : (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.εroot j) = AI.εroot (j + 1) := by
        rw [LocAinf.εroot, LocAinf.εroot, Function.iterate_succ_apply']
        rfl
      rw [RingHom.comp_apply, WittVector.map_teichmuller, e, h2, add_assoc, add_comm 1 n]

theorem exists_isThetaShift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ),
    ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  intro l _ P AI n
  obtain ⟨θ, h1, h2⟩ := exists_thetaShift_ringHom AI n
  exact ⟨{ toRingHom := θ
           commutes' := fun x => ringHom_padicInt_OC_ext (θ.comp (algebraMap ℤ_[l] (Ainf l)))
             (algebraMap ℤ_[l] (OC l)) x }, fun g a => h1 g a, h2⟩

end GlobalTheory.Cyc.Decomp
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels : ∀ (l : ℕ) [Fact l.Prime] (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s j n : ℕ, 1 ≤ j → j ≤ s → ¬ l ∣ n → ∃ lam : ℕ → ℤ, (∑ a ∈ primeTo l s, lam a = if j = 1 then (l : ℤ) ^ (s - 1) else 0) ∧ ∀ i, 1 ≤ i → i ≤ s → ∑ a ∈ primeTo l s, (lam a : Om l) * ζ i ^ a = if i = j then (l : Om l) ^ (if j = 1 then s - 1 else s - j + 1) * ζ j ^ n else 0 := by
  first | exact @GlobalTheory.LevelSums.exists_weights | exact GlobalTheory.LevelSums.exists_weights | (intros; apply GlobalTheory.LevelSums.exists_weights <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_series_limit_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (M : ℕ) (c : ℕ → P.R.BdR), (∀ k, c k ∈ FilB P 0) → (∀ n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, c k ∈ Lat AI M n) → ∃ b ∈ FilB P 0, ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - ∑ k ∈ Finset.range R, c k ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.exists_series_limit_Lat | exact GlobalTheory.ExpImage.exists_series_limit_Lat | (intros; apply GlobalTheory.ExpImage.exists_series_limit_Lat <;> assumption)
end
