module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionGenus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_eq_iff (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ y, a = b + n • y := by
  rw [tateIso_ev_eq_iff I hn]
  unfold Datum.ModN
  exact exists_congr fun y => sub_eq_iff_eq_add'

theorem exists_lift (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  have hs : ∀ a, ∃ b, I'.ev n b = I.ev n a := fun a => (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
  choose s hs using hs
  let N : Submodule (𝓞 E) D'.La := LinearMap.range (n • (LinearMap.id : D'.La →ₗ[𝓞 E] D'.La))
  have hN : ∀ a b : D'.La, N.mkQ a = N.mkQ b ↔ I'.ev n a = I'.ev n b := by
    intro a b
    rw [tateIso_ev_eq_iff I' hn, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  let φ : D.La →ₗ[𝓞 E] D'.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add (f := _), hN, I'.add, hs, hs, hs, I.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, hN, I'.lin, hs, hs, I.lin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ φ N.mkQ_surjective
  refine ⟨f, fun a => ?_⟩
  have h : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [(hN _ _).1 h, hs]

theorem genus_of_tateIso
    (he : ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c')
    (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      ((∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
      ∀ n, 0 < n → I.ζ n = I'.ζ n ^ ν n ∧ ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := exists_lift I' I h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · have : NeZero n := ⟨h.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n h).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n h).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, ν, ⟨?_, ?_, ?_⟩, fun n hn => ⟨hν n hn, hf n hn⟩⟩
  · intro n m hn hm a
    rw [← ev_eq_iff I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun x => ?_, fun x' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨x, hx⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn x')
      refine ⟨x, (ev_eq_iff I' hn _ _).1 ?_⟩
      rw [← hf n hn, hx]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ hn (tateIso_ev_pow I' hn _) (tateIso_ev_pow I' hn _) e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun a b h => by
  have h1 := congrArg (fun x : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x.val) h
  apply Units.ext
  simpa [unitOn] using h1

noncomputable def expRoot (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem expRoot_zpow (n : ℕ) (m : ℤ) :
    ((expRoot n ^ m : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expRoot, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem expRoot_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expRoot n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rw [← Complex.exp_neg] at h
  rw [expRoot, Units.val_mk0, neg_div]
  exact h

theorem expRoot_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expRoot (n * m) ^ m = expRoot n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, expRoot, expRoot, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

section

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

end

noncomputable def periodTateIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H)
    {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (act : OAct (𝓞 E) A)
    (Q : D'.La →+ (Fin g → ℂ)) (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range)
    (hact : ∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a)
    (hW : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs A L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c)) :
    TateIso D' ℂ (𝟙_ (Over (Sp ℂ)) ⟶ A) (fun c y => y ≫ act.act c)
      (fun n y y' c => Out.WeilIs A L n y y' (unitOn c)) where
  ζ := expRoot
  ζ_prim _ hn := expRoot_prim hn
  ζ_pow _ _ hn hm := expRoot_pow hn hm
  ev n x := u.ex ((n : ℂ)⁻¹ • Q x)
  add n a b := by rw [map_add (f := _), smul_add, u.ex_add]
  lin n c a := hact c n a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [u.ker, hΛ]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hQ ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [← ex_nsmul, u.ker, hΛ] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, smul_smul, inv_mul_cancel₀ hn', one_smul]⟩
    · rintro ⟨a, rfl⟩
      rw [← ex_nsmul, u.ker, hΛ, smul_smul, mul_inv_cancel₀ hn', one_smul]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← ex_nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hW n a b _ hn (expRoot_zpow n _)

theorem period_lattice_in_genus :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), D'.p = D.p → D'.q = D.q → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ ∀ n : ℕ, 0 < n → (I.ζ n : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) ∧ ∀ x, (I.ev n x).left = (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' P u Hm χ act Q hp hq hAH hQ hΛ hE hact I
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hT hU P u Hm χ hAH
  have hW' : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c) := by
    intro n a b c hn hc
    refine hW n ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
    have h := hEf ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [hE] at h
    rw [Int.cast_injective h]
    exact hc
  obtain ⟨f, ν, ⟨h1, h2, h3⟩, h4⟩ := genus_of_tateIso (D := D) (D' := D')
    (fun n x y c c' _ hx hy ha hb =>
      unitOn_injective (((hL.weil _ P n (Over.mk (𝟙 (Sp ℂ)))).1 x y hx hy).unique ha hb))
    (periodTateIso D' u act Q hQ hΛ hact hW') I
  refine ⟨f, ν, ⟨hp, hq, h1, h2, h3⟩, fun n hn => ⟨?_, fun x => ?_⟩⟩
  · rw [(h4 n hn).1]
    exact expRoot_zpow n _
  · rw [(h4 n hn).2]
    rfl

end GlobalTheory.TorsionGenus
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_const_mul_of_isFnPow_ne_zero (hH : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    (θ : (Fin P.g → ℂ) → ℂ) (hθ : θ ≠ 0) (s : (lbPow P.L 1).Sec) (hs : u.IsFnPow 1 s θ) (t : (lbPow P.L 1).Sec) :
    ∃ a : ℂ, ∀ j, t.f j = constFn P.A.hom _ a * s.f j := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hH ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  obtain ⟨a, ha, -⟩ := hβ s
  obtain ⟨b, hb, -⟩ := hβ t
  have hc : ∀ U : P.A.left.Opens, ∃ e : ℂ →+* Γ(P.A.left, U), ∀ x, constFn P.A.hom U x = e x := fun U =>
    ⟨((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ P.A.hom.appLE ⊤ U (fun _ _ => trivial)).hom, fun _ => rfl⟩
  have ha0 : a i₀ ≠ 0 := by
    intro h0
    apply hθ
    funext z
    have hm : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ (⊤ : P.A.left.Opens) := trivial
    rw [← P.isLB.cover] at hm
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    have hi₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i := (top_le_preimage_iff_mem _ _).2 hi
    have hi₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => hi)
    have e := hs (fun _ => i) z hi₂
    obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U (fun _ => i))
    have e0 := (ha (fun _ => i)).trans (su _)
    rw [h0, hc', map_zero, zero_mul] at e0
    have e1 := e.symm.trans ((congrArg (valAt' _ _) e0).trans (valAt'_zero _ _))
    rw [pow_one] at e1
    exact (mul_eq_zero.1 e1).resolve_right (u.fr_ne i z hi₁)
  refine ⟨b i₀ / a i₀, fun j => ?_⟩
  obtain ⟨c, hc'⟩ := hc ((lbPow P.L 1).U j)
  rw [ha, hb, su, su, hc', hc', hc', ← _root_.mul_assoc, ← map_mul, div_mul_cancel₀ _ ha0]

theorem exists_isGenSec_of_isThetaFn : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → ∃ th : LB.Sec (Out.LPow P.A P.L 1 T), Out.IsGenSec P.A P.L 1 th ∧ (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L 1 T).U j) (th.f j) = θ z * u.fr (j 0) z ^ (1 : ℤ)) := by
  intro hL hL2 hG hU P u Hm χ θ T _ p hAH hθ hne
  obtain ⟨-, -, -, -, -, -, -, hsec, -⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hG hU P u Hm χ hAH
  obtain ⟨s, hs, -⟩ := (hsec 1).2 θ hθ
  have hT : ∀ {X : Over (Sp ℂ)} (f g : X ⟶ T), f = g := fun f g =>
    Over.OverMorphism.ext ((cancel_mono T.hom).1 ((Over.w f).trans (Over.w g).symm))
  let ρ : P.A ⟶ T ⊗ P.A := lift (toUnit _ ≫ p) (𝟙 _)
  have r₂ : ρ ≫ snd T P.A = 𝟙 _ := lift_snd _ _
  have r₃ : snd T P.A ≫ ρ = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, Category.id_comp])
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) r₂
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := congrArg (fun q => q.left) r₃
  have ρ₁ : ρ.left ≫ (fst T P.A).left ≫ T.hom = P.A.hom := Over.w (ρ ≫ fst T P.A)
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  obtain ⟨th, hth⟩ := PowSec.down_surjective P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) s
  refine ⟨th, fun t => ?_, fun j z hz => ?_⟩
  · obtain ⟨a, ha⟩ := exists_const_mul_of_isFnPow_ne_zero hL.globalSectionsRank P u θ hne s hs
      (PowSec.down P.L (snd T P.A).left ρ.left ρ₂ ((1 : ℕ) : ℤ) t)
    refine ⟨T.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a), fun j => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    refine PowSec.appLE_injective ρ.left _ _ hch ?_
    refine (ha (fun _ => k)).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (map_mul (ρ.left.appLE _ _ hch.le).hom _ _).symm)
    · have h0 : (T.hom.appTop ≫ (fst T P.A).left.appTop ≫ (T ⊗ P.A).left.presheaf.map (homOfLE le_top).op) =
          ((fst T P.A).left ≫ T.hom).appLE ⊤ (LB.wchart P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => k))
            (fun _ _ => trivial) := by
        rw [← Category.assoc, ← Scheme.Hom.comp_appTop]; rfl
      have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left ((fst T P.A).left ≫ T.hom) ⊤ _ _ (fun _ _ => trivial)
        hch.le).trans (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
      rw [← h0] at h1
      exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) h1).symm
    · rw [← hth]; rfl
  · obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have hch := PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)
    have hz₂ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L 1).U (fun _ => k) :=
      (top_le_preimage_iff_mem _ _).2 (Set.mem_iInter.2 fun _ => (top_le_preimage_iff_mem _ _).1 hz)
    have e := hs (fun _ => k) z hz₂
    have e₁ : lift p (u.ex z) = u.ex z ≫ ρ :=
      CartesianMonoidalCategory.hom_ext _ _ (hT _ _) (by rw [Category.assoc, r₂, Category.comp_id, lift_snd])
    have e₂ := valAt'_appLE (u.ex z).left ρ.left _ _ hch.le (th.f (fun _ => k)) hz₂
    rw [e₁, zpow_one]
    rw [← hth, pow_one] at e
    exact e₂.symm.trans e

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SharpObj

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem

def exHom : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
  MonoidHom.mk' (fun z => u.ex z.toAdd) fun z w => u.ex_add _ _

theorem ex_zsmul (n : ℤ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  have h := map_zpow (exHom u) (Multiplicative.ofAdd z) n
  rw [← ofAdd_zsmul] at h
  simpa [exHom] using h

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum [IsCommMonObj A] {I : Type} [Fintype I] (z : I → Fin g → ℂ) : u.ex (∑ i, z i) = ∏ i, u.ex (z i) := by
  classical
  have key : ∀ s : Finset I, u.ex (∑ i ∈ s, z i) = ∏ i ∈ s, u.ex (z i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact ex_zero u
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, u.ex_add, ih]
  exact key Finset.univ

end Unif

variable (laws : Out.Laws) (laws2 : Out.Laws2)
  (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
  (hT : ThetaUnifAV)
include laws laws2 hc hT

theorem hom_ext_of_lin (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (f f' : P.A ⟶ P'.A) (hf : ∀ z, u'.ex (F z) = u.ex z ≫ f)
    (hf' : ∀ z, u'.ex (F z) = u.ex z ≫ f') (h1 : IsMonHom f) : f = f' := by
  have e : ∀ B : Over (Sp ℂ), ∀ [GrpObj B], (η[B] : 𝟙_ _ ⟶ B) = 1 := fun B _ => by rw [Hom.one_def]; simp
  have h2 : IsMonHom f' := laws.rigidity _ _ _ P.isAb P'.isAb f' (by
    rw [e, e, ← ex_zero u, ← hf', map_zero, ex_zero])
  refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P' _ _ u u' F fun z hz => ?_).unique ⟨h1, hf⟩ ⟨h2, hf'⟩
  rw [← u'.ker, hf, (u.ker z).2 hz, MonObj.one_comp]

theorem exists_proj (P P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u₀ : HolUnif P₀.A P₀.L P₀.g)
    {I : Type} [Fintype I] (σ : I × Fin P₀.g ≃ Fin P.g)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ) :
    ∃ pr : I → (P.A ⟶ P₀.A), (∀ i, IsMonHom (pr i)) ∧ (∀ i z, u₀.ex (fun j => z (σ (i, j))) = u.ex z ≫ pr i) ∧
      ∀ (T : Over (Sp ℂ)) (y : I → (T ⟶ P₀.A)), ∃! x : T ⟶ P.A, ∀ i, x ≫ pr i = y i := by
  classical
  letI := P.isAb.comm
  letI := P₀.isAb.comm
  let R : I → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  let S : I → (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := fun i =>
    LinearMap.pi fun a => if (σ.symm a).1 = i then LinearMap.proj (σ.symm a).2 else 0
  have hRS : ∀ i i' z, R i (S i' z) = if i = i' then z else 0 := fun i i' z => by
    ext j
    by_cases e : i = i' <;> simp [R, S, LinearMap.funLeft_apply, e]
  have hSR : ∀ z, ∑ i, S i (R i z) = z := fun z => by
    ext a
    obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective a
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [R, S, LinearMap.funLeft_apply]
    · intro b _ hb
      simp [S, hb.symm]
    · simp
  choose pr hpr using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P P₀ _ _ u u₀ (R i) fun z hz => (hΛ z).1 hz i).exists
  choose inc hinc using fun i => (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim laws laws2 hc hT P₀ P _ _ u₀ u (S i) fun z hz => (hΛ _).2 fun i' => by
    change R i' (S i z) ∈ _
    rw [hRS]
    split_ifs
    exacts [hz, u₀.Λ.zero_mem]).exists
  haveI := fun i => (hpr i).1
  haveI := fun i => (hinc i).1
  have e1 : ∀ i, inc i ≫ pr i = 𝟙 _ := fun i =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ LinearMap.id _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i).2, hRS]; simp) (fun z => by simp) inferInstance
  have e2 : ∀ i i', i ≠ i' → inc i ≫ pr i' = 1 := fun i i' hi =>
    hom_ext_of_lin laws laws2 hc hT P₀ P₀ u₀ u₀ 0 _ _ (fun z => by
      rw [← Category.assoc, ← (hinc i).2, ← (hpr i').2, hRS]; simp [hi.symm])
      (fun z => by simp [ex_zero]) inferInstance
  have e3 : 𝟙 P.A = ∏ i, pr i ≫ inc i :=
    hom_ext_of_lin laws laws2 hc hT P P u u LinearMap.id _ _ (fun z => by simp) (fun z => by
      rw [PowMatrixLinear.comp_prod]
      simp only [← Category.assoc, ← (hpr _).2, ← (hinc _).2]
      rw [← ex_sum, hSR]; rfl) inferInstance
  refine ⟨pr, fun i => (hpr i).1, fun i => (hpr i).2, fun T y => ⟨∏ i, y i ≫ inc i, fun i => ?_, fun x hx => ?_⟩⟩
  · rw [PowMatrixLinear.prod_comp, Finset.prod_eq_single i]
    · rw [Category.assoc, e1, Category.comp_id]
    · intro b _ hb
      rw [Category.assoc, e2 _ _ hb, MonObj.comp_one]
    · simp
  · rw [← Category.comp_id x, e3, PowMatrixLinear.comp_prod]
    simp only [← Category.assoc, hx]

end GlobalTheory.SharpObj

end
end
