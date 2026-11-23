module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle123
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.AdeleSquarefree

theorem mem_span_of_forall_prime {A : Type} [CommRing A] [IsDedekindDomain A] (x : A) (hx : x ≠ 0)
    (hsq : ∀ Q : HeightOneSpectrum A, x ∈ Q.asIdeal → x ∉ Q.asIdeal ^ 2) (a : A)
    (ha : ∀ Q : HeightOneSpectrum A, x ∈ Q.asIdeal → a ∈ Q.asIdeal) : a ∈ Ideal.span {x} := by
  have h0 : (Ideal.span {x} : Ideal A) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hsf : Squarefree (Ideal.span {x} : Ideal A) := by
    refine (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero h0).2 fun P hP hd => ?_
    have hPp : Prime P := hP.prime
    have hPb : P ≠ ⊥ := hPp.ne_zero
    have hle : Ideal.span {x} ≤ P ^ 2 := by
      rw [pow_two]; exact Ideal.dvd_iff_le.1 hd
    have hx2 : x ∈ P ^ 2 := hle (Ideal.mem_span_singleton_self x)
    exact hsq ⟨P, (Ideal.prime_iff_isPrime hPb).1 hPp, hPb⟩ (Ideal.pow_le_self two_ne_zero hx2) hx2
  have hrad : a ∈ (Ideal.span {x} : Ideal A).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJb : J ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hJ))
    exact ha ⟨J, hJp, hJb⟩ (hJ (Ideal.mem_span_singleton_self x))
  obtain ⟨n, hn⟩ := hrad
  have hd : (Ideal.span {x} : Ideal A) ∣ (Ideal.span {a}) ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 := hsf.isRadical n _ hd
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  exact h2

theorem zmod_of_forall_resS_eq_zero : ∀ (I : AutInst) (g : ℕ), g ≠ 0 →
    (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → (g : 𝓞 I.E) ∉ Q.asIdeal ^ 2) →
    ∀ s : Formalism.L2.Herm.intAf I.F I.E, (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → resS I.F Q s = 0) → ZMod' I g s := by
  intro I g hg hsq s hs
  have hg' : (g : 𝓞 I.E) ≠ 0 := by exact_mod_cast hg
  have h0 : (Ideal.span {(g : 𝓞 I.E)} : Ideal (𝓞 I.E)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hg
  have hid : idS I.F (Ideal.span {(g : 𝓞 I.E)}) = Ideal.span {oToS I.F I.E (g : 𝓞 I.E)} := by
    rw [idS, Ideal.map_span, Set.image_singleton]
  obtain ⟨q, hq⟩ := (cmpS_bij (F := I.F) _ h0).2 (Ideal.Quotient.mk _ s)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hq' : Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) (oToS I.F I.E a) =
      Ideal.Quotient.mk (idS I.F (Ideal.span {(g : 𝓞 I.E)})) s := hq
  have hm := Ideal.Quotient.eq.1 hq'.symm
  rw [hid, Ideal.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  have hsu : s = oToS I.F I.E a + oToS I.F I.E (g : 𝓞 I.E) * u := by rw [← hu]; ring
  have ha : a ∈ Ideal.span {(g : 𝓞 I.E)} := by
    refine mem_span_of_forall_prime _ hg' hsq a fun Q hQ => ?_
    have h1 := hs Q hQ
    rw [hsu, map_add (f := _), map_mul, resS_oToS, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hQ, zero_mul, add_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 ha
  have hfin : s = (g : Formalism.L2.Herm.intAf I.F I.E) * (oToS I.F I.E b + u) := by
    rw [hsu, hb, map_mul, map_natCast]; ring
  refine ⟨((oToS I.F I.E b + u : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F), (oToS I.F I.E b + u).2, ?_⟩
  conv_lhs => rw [hfin]
  push_cast
  rfl

end GlobalTheory.AdeleSquarefree
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnitTorus

theorem hform_mulVec_two {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M M' : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M' *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M') x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

theorem hform_single {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N : Matrix n n A) (i j : n) :
    Formalism.UG.hform σ N (Pi.single i 1) (Pi.single j 1) = N i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

theorem matrix_eq_of_hform {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (N N' : Matrix n n A) (h : ∀ x y, Formalism.UG.hform σ N x y = Formalism.UG.hform σ N' x y) : N = N' := by
  ext i j
  rw [← hform_single σ N i j, ← hform_single σ N' i j, h]

theorem unit_of_proj {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J P : Matrix n n A) (c : A) (hPP : P * P = P) (hSA : Formalism.UG.cT σ P * J = J * P) (hc : c * σ c = 1) :
    (c • 1 + (1 - c) • P) * (σ c • 1 + (1 - σ c) • P) = 1 ∧
    (σ c • 1 + (1 - σ c) • P) * (c • 1 + (1 - c) • P) = 1 ∧
    Formalism.UG.cT σ (c • 1 + (1 - c) • P) * J * (c • 1 + (1 - c) • P) = J := by
  have hcT : Formalism.UG.cT σ (c • (1 : Matrix n n A) + (1 - c) • P) = σ c • 1 + (1 - σ c) • Formalism.UG.cT σ P := by
    ext i j
    by_cases h : j = i
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, h, Ne.symm h]
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPP, smul_smul]
    calc _ = (c * σ c) • (1 : Matrix n n A) + (1 - c * σ c) • P := by module
      _ = 1 := by rw [hc, sub_self, zero_smul, add_zero, one_smul]
  · rw [hcT]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hSA,
      Matrix.mul_assoc, hPP, smul_smul]
    calc _ = (c * σ c) • J + (1 - c * σ c) • (J * P) := by module
      _ = J := by rw [hc, sub_self, zero_smul, add_zero, one_smul]

end GlobalTheory.UnitTorus

open GlobalTheory.UnitTorus in
theorem GlobalTheory.unitTorus_unit : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  intro I P c hP hSA hc
  have hPP : P * P = P := by
    ext i j
    have := congrFun (hP (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hSA' : Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) =
      I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P := by
    have := matrix_eq_of_hform (sigA I) (Formalism.UG.cT (sigA I) P * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * 1)
      (Formalism.UG.cT (sigA I) 1 * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * P) (fun x y => by
        rw [← hform_mulVec_two, ← hform_mulVec_two, one_mulVec, one_mulVec]
        exact hSA x y)
    simpa [Formalism.UG.cT_one] using this
  obtain ⟨h1, h2, h3⟩ := unit_of_proj (sigA I) _ P c hPP hSA' hc
  exact ⟨⟨⟨_, _, h1, h2⟩, h3⟩, rfl, rfl⟩
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusCop

theorem natCoprime_of_zmod_mul_one_sub : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g →
    ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  intro I g T M hg hMg hz
  obtain ⟨t, ht, hc⟩ := hz
  obtain ⟨-, hint, hu, -⟩ := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef
  have hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E)) := by
    have : (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ)) := by
      rw [hqdef]; field_simp; push_cast; ring
    have := congrArg (fun x : ℚ => (x : I.E)) this
    simpa using this
  have key : Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E) = t := by
    apply hu.mul_left_cancel
    rw [← hc]
    calc (g : I.E ⊗[I.F] Af I.F) * Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E)
        = Formalism.UG.inclE (F := I.F) (Af I.F) ((g : I.E) * (q : I.E)) := by rw [map_mul, map_natCast]
      _ = Formalism.UG.inclE (F := I.F) (Af I.F) ((M : I.E) * (1 - (T : I.E))) := by rw [hgq]
      _ = _ := by rw [map_mul, map_sub, map_one, map_natCast, map_natCast]
  have hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := (hint _).1 (key ▸ ht)
  obtain ⟨b, hb⟩ := hq
  have h1 : IsIntegral ℤ (algebraMap ℚ I.E q) := by
    rw [eq_ratCast, ← hb]; exact RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n := by
    have hn' : (n : ℚ) = q := by simpa using hn
    have : (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ) := by
      rw [hqdef] at hn'
      push_cast
      rw [hn']
      field_simp
      push_cast; ring
    exact_mod_cast this
  have h5 : (g : ℤ) ∣ 1 - (T : ℤ) := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hMg.symm
  have hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 := by
    have a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5
    have := dvd_add b a
    simpa using this
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))

end GlobalTheory.TorusCop
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree : ∀ (I : AutInst) (g : ℕ), g ≠ 0 → (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → (g : 𝓞 I.E) ∉ Q.asIdeal ^ 2) → ∀ s : Formalism.L2.Herm.intAf I.F I.E, (∀ Q : Pl I.E, (g : 𝓞 I.E) ∈ Q.asIdeal → resS I.F Q s = 0) → ZMod' I g s := by
  first | exact @GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero | exact GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero | (intros; apply GlobalTheory.AdeleSquarefree.zmod_of_forall_resS_eq_zero <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitary_scalarBlend_selfAdjoint_idempotent : ∀ (I : AutInst) (P : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (c : I.E ⊗[I.F] Af I.F), (∀ y, P *ᵥ (P *ᵥ y) = P *ᵥ y) → (∀ x y, hA I (P *ᵥ x) y = hA I x (P *ᵥ y)) → c * sigA I c = 1 → ∃ h : I.Gf, I.fmat h = c • 1 + (1 - c) • P ∧ I.fmat h⁻¹ = sigA I c • 1 + (1 - sigA I c) • P := by
  first | exact @GlobalTheory.unitTorus_unit | exact GlobalTheory.unitTorus_unit | (intros; apply GlobalTheory.unitTorus_unit <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g → ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  first | exact @GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | (intros; apply GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub <;> assumption)

end
end
