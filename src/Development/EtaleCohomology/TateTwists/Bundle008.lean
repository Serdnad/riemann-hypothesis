module

public import Development.EtaleCohomology.TateTwists.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.TateTwists.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleKummerChernClassCochainOfLineBundle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) α 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) α 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) α 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def ExistsEtaleKummerChernClassCochain : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α

def EtaleKummerChernClassCochainIsCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α → δ 2 3 α = 0

def EvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def ExistsNaturalEtaleKummerChernClassDegreeOneValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def ExistsNaturalEtaleKummerChernClassDegreeTwoValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

noncomputable def vals {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 2 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 0, _, _, _, _ => 0
  | Nat.succ 0, s, h, U, x => (show (1 : ℤ) = s by omega) ▸ a1 U x
  | Nat.succ (Nat.succ 0), s, h, U, x => (show (0 : ℤ) = s by omega) ▸ a2 U x
  | Nat.succ (Nat.succ (Nat.succ _)), _, _, _, _ => 0

theorem vals_nat {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a1 U x) = a1 V (x.res g))
    (h2 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a2 U x) = a2 V (x.res g)) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (vals a1 a2 p s h U x) = vals a1 a2 p s h V (x.res g) := by
  intro p
  match p with
  | 0 =>
    intro s h V U g x
    simp [vals]
  | Nat.succ 0 =>
    intro s h V U g x
    subst s
    exact h1 V U g x
  | Nat.succ (Nat.succ 0) =>
    intro s h V U g x
    subst s
    exact h2 V U g x
  | Nat.succ (Nat.succ (Nat.succ _)) =>
    intro s h V U g x
    simp [vals]

theorem exists_etale_kummer_chern_class_cochain_of_degree_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) : ExistsEtaleKummerChernClassCochain := by
  intro q _ E L hi
  obtain ⟨a1, n1, e1⟩ := h1 q L hi
  obtain ⟨a2, n2, e2⟩ := h2 q L hi
  obtain ⟨α, hα⟩ := hmk (ZMod q) (vals a1 a2) (vals_nat a1 a2 n1 n2)
  refine ⟨α, ?_, ?_, ?_⟩
  · intro U x; rw [hα]; rfl
  · intro U x v hv; rw [hα]; exact e1 U x v hv
  · intro U x v w hv hw; rw [hα]; exact e2 U x v w hv hw

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) (hd : EtaleKummerChernClassCochainIsCocycle) :
    LateralTheory.EtaleFoundations.first_chern_class_exists := by
  intro q _ E L hi
  obtain ⟨α, hα⟩ := exists_etale_kummer_chern_class_cochain_of_degree_values hmk h1 h2 q L hi
  exact ⟨Cocycle.mk α 3 (by norm_num) (hd q L hi α hα), hα⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwFInj

theorem prim_field {q : ℕ} {k : Type} [Field k] (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int] using h

theorem pow_mod_eq {k : Type} [Field k] {q : ℕ} {z : k} (hz : IsPrimitiveRoot z q) (n : ℕ) :
    z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

theorem unit_unique {k : Type} [Field k] {q : ℕ} [NeZero q] {z : k} (hz : IsPrimitiveRoot z q)
    {u v : (ZMod q)ˣ} (h : z ^ (u : ZMod q).val = z ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective _ (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_unit {k : Type} [Field k] {q : ℕ} [NeZero q] {z x : k} (hz : IsPrimitiveRoot z q)
    (hx : IsPrimitiveRoot x q) : ∃ u : (ZMod q)ˣ, x = z ^ (u : ZMod q).val := by
  obtain ⟨j, hj, hjx⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : j.Coprime q := (hz.pow_iff_coprime (NeZero.pos q) j).1 (hjx ▸ hx)
  refine ⟨ZMod.unitOfCoprime j hc, ?_⟩
  rw [← hjx]
  congr 1
  simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

end LateralTheory.EtaleFoundations.TwFInj

namespace LateralTheory.EtaleFoundations.TwFInj

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] {k : Type} [Field k] (π : B →+* k) {z : k}
  (hz : IsPrimitiveRoot z q)

noncomputable def ex (ξ : Prim q B) : (ZMod q)ˣ := Classical.choose (exists_unit hz (prim_field (ξ.map π)))

theorem ex_spec (ξ : Prim q B) : π ξ.1 = z ^ (ex π hz ξ : ZMod q).val :=
  Classical.choose_spec (exists_unit hz (prim_field (ξ.map π)))

theorem ex_rel {ζ ξ : Prim q B} {a : (ZMod q)ˣ} (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ex π hz ξ = ex π hz ζ * a := by
  apply unit_unique hz
  rw [← ex_spec, h, map_pow, ex_spec π hz ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_mod_eq hz]

noncomputable def L (i : ℤ) : (Prim q B →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (((ex π hz ξ) ^ i : (ZMod q)ˣ) : ZMod q))

theorem twRel_le_ker (i : ℤ) : twRel q i B ≤ LinearMap.ker (L π hz i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
  apply ULift.ext
  simp [ex_rel π hz h, mul_zpow, mul_comm]

end LateralTheory.EtaleFoundations.TwFInj

theorem LateralTheory.EtaleFoundations.twF_gen_inj_of : LateralTheory.EtaleFoundations.twF_gen_inj := by
  intro q _ B _ hB i ζ c1 c2 hc
  simp only at hc
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  have hz := LateralTheory.EtaleFoundations.TwFInj.prim_field (ζ.map π)
  let Φ := Submodule.liftQ _ (LateralTheory.EtaleFoundations.TwFInj.L π hz i) (LateralTheory.EtaleFoundations.TwFInj.twRel_le_ker π hz i)
  have h2 := congrArg Φ hc
  simp only [Φ, map_nsmul, Submodule.liftQ_apply, LateralTheory.EtaleFoundations.TwFInj.L, Finsupp.linearCombination_single, one_smul] at h2
  have h3 := congrArg ULift.down h2
  have h4 : (c1.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) =
      (c2.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) := by
    simp only [nsmul_eq_mul] at h3
    exact h3
  simpa [ZMod.natCast_zmod_val] using (Units.mul_left_inj _).1 h4
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_twpair_ex : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j))), IsTwPair μ

def t_pair_assoc : Prop :=
  ∀ (q : ℕ) [NeZero q] (E : Spc) {i j l k₁ k₂ k : ℤ} (_ : i + j = k₁) (_ : j + l = k₂) (_ : i + k₂ = k)
    (μ₁ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k₁)))
    (μ₂ : Pair (res _ (tw q k₁)) (res _ (tw q l)) (res _ (tw q k)))
    (ν₁ : Pair (res _ (tw q j)) (res _ (tw q l)) (res _ (tw q k₂)))
    (ν₂ : Pair (res _ (tw q i)) (res _ (tw q k₂)) (res _ (tw q k))),
    IsTwPair μ₁ → IsTwPair μ₂ → IsTwPair ν₁ → IsTwPair ν₂ →
    ∀ {n m p s₁ s₂ s : ℤ} (h₁ : n + m = s₁) (h₂ : s₁ + p = s) (h₃ : m + p = s₂) (h₄ : n + s₂ = s)
      (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E p l),
      μ₂.cup E h₂ (μ₁.cup E h₁ a b) c = ν₂.cup E h₄ a (ν₁.cup E h₃ b c)

theorem cast_pair_cup {q : ℕ} {E : Spc} {i j k k' n m s s' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (hk : n + m = s) (hs : s = s')
    (a : Ht q E n i) (b : Ht q E m j) :
    Ht.cast hs e (μ.cup E hk a b : Ht q E s k) = (e ▸ μ : Pair _ _ (res _ (tw q k'))).cup E (hk.trans hs) a b := by
  subst e; subst hs; rfl

theorem isTwPair_cast {q : ℕ} {i j k k' : ℤ}
    (μ : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k))) (e : k = k') (h : IsTwPair μ) :
    IsTwPair (e ▸ μ : Pair _ _ (res _ (tw q k'))) := by
  subst e; exact h

theorem etale_twisted_cup_assoc_of_twisted_pairing_exists_assoc (hex : t_twpair_ex) (has : t_pair_assoc) : EtaleTwistedCupProductAssociative := by
  intro q _ E n m k i j l a b c
  have hp : ∀ i j : ℤ, IsTwPair (twPair q i j) := fun i j => pick_spec (hex q i j)
  have e : i + (j + l) = i + j + l := by ring
  have hs : n + (m + k) = n + m + k := by ring
  show (twPair q (i + j) l).cup E rfl ((twPair q i j).cup E rfl a b) c =
    Ht.cast hs e ((twPair q i (j + l)).cup E rfl a ((twPair q j l).cup E rfl b c))
  rw [cast_pair_cup]
  exact has q E rfl rfl e _ _ _ _ (hp i j) (hp (i + j) l) (hp j l) (isTwPair_cast _ e (hp i (j + l)))
    rfl rfl rfl (rfl.trans hs) a b c

end LateralTheory.EtaleFoundations
end
