module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Definitions.Foundations.TracePowApply
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle083
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle656
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle923
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Formalism.BranchSandwichDivisors.StatementR
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.DivP

open WithConv

variable {p : ℕ} {k : Type} [Field k]

theorem conv_eq_one_of_succ {G H : PDivGroup p k} (f : G ⟶ H) (n : ℕ) (h : f.conv (n + 1) = 1) :
    f.conv n = 1 := by
  have h1 : ∀ b, f.app (n + 1) b = algebraMap k _ (counit b) := fun b => by
    have := DFunLike.congr_fun (congrArg ofConv h) b
    simpa using this
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  change f.app n (H.res n b) = algebraMap k _ (counit (H.res n b))
  rw [← res_app, h1, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

theorem conv_eq_one_of_le {G H : PDivGroup p k} (f : G ⟶ H) {m n : ℕ} (hmn : m ≤ n)
    (h : f.conv n = 1) : f.conv m = 1 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (conv_eq_one_of_succ f n h)

theorem app_kill {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) (n : ℕ) :
    ∀ {E : Type} [CommRing E] [Algebra k E] (x : G.A (n + 1) →ₐ[k] E), toConv x ^ p = 1 →
      ∀ c, x (f.app (n + 1) c) = algebraMap k E (counit c) := by
  induction n with
  | zero =>
    intro E _ _ x _ c
    have h1 : f.app 1 c = algebraMap k _ (counit c) := by
      have := DFunLike.congr_fun (congrArg ofConv hf) c
      simpa using this
    rw [h1, AlgHom.commutes]
  | succ n ih =>
    intro E _ _ x hx c
    have hx' : toConv x ^ p ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, hx, one_pow]
    obtain ⟨y, hy⟩ := (G.exists_comp_res_iff (n + 1) x).2 hx'
    have hy' : toConv y ^ p = 1 := by
      have e : pointsMap E (G.res (n + 1)) (toConv y ^ p) = 1 := by
        rw [map_pow]
        change (toConv (y.comp (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)))) ^ p = 1
        rw [hy, hx]
      apply ofConv_injective
      refine AlgHom.ext fun a => ?_
      obtain ⟨b, rfl⟩ := G.res_surjective (n + 1) a
      have e2 := DFunLike.congr_fun (congrArg ofConv e) b
      rw [ptsMap_ofConv, AlgHom.comp_apply] at e2
      refine e2.trans ?_
      show algebraMap k E (counit b) = algebraMap k E (counit (G.res (n + 1) b))
      rw [CoalgHomClass.counit_comp_apply]
    rw [← hy, AlgHom.comp_apply]
    change y (G.res (n + 1) (f.app (n + 2) c)) = _
    rw [res_app, ih y hy', CoalgHomClass.counit_comp_apply]

theorem exists_factor [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1)
    (n : ℕ) : ∃ g : H.A (n + 1) →ₐc[k] G.A n, ∀ b, G.mulP n (g b) = f.app (n + 1) b := by
  obtain ⟨r, hrs, hrk⟩ := G.exists_res_le (m := 1) (n := n + 1) (by omega)
  rw [pow_one] at hrk
  obtain ⟨B, _, _, _, _, j, hji, hjk, hjr⟩ := GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup k (G.A (n + 1)) (G.A 1) r hrs
  have hP : kerIdeal (G.mulP n) = RingHom.ker r := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective n), mulP_comp_res, hrk]
  have h1 : ∀ a, G.mulP n a ∈ Set.range j := hjr (G.A n) (G.mulP n) hP.le
  have hmk : toConv (Ideal.Quotient.mkₐ k (torsionIdeal (R := k) (A := G.A (n + 1)) p)) ^ p = 1 :=
    (torsionIdeal_le_ker_iff p _).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h2 : ∀ b, f.app (n + 1) b ∈ Set.range j := by
    refine hjr (H.A (n + 1)) (f.app (n + 1)) ?_
    rw [hrk]
    intro a ha
    have := (kerIdeal_le_ker_iff (f.app (n + 1)) (Ideal.Quotient.mkₐ k _)).2
      (fun c => app_kill f hf n _ hmk c) ha
    rw [RingHom.mem_ker] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  let jl := (j : B →ₐ[k] G.A (n + 1)).toLinearMap
  let ml := (G.mulP n : G.A n →ₐ[k] G.A (n + 1)).toLinearMap
  have hle : LinearMap.range ml ≤ LinearMap.range jl := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := h1 a
    exact ⟨b, hb⟩
  have e1 := finrank_eq_ker_mul_range k (G.A (n + 1)) (G.A n) (G.mulP n)
  have e2 := finrank_eq_ker_mul_range k (G.A (n + 1)) B j
  rw [hP] at e1
  rw [hjk] at e2
  have hpos : 0 < Module.finrank k (G.A (n + 1) ⧸ RingHom.ker r) := by
    apply Nat.pos_of_ne_zero
    intro h0
    have : Nontrivial (G.A (n + 1)) := (counitAlgHom k (G.A (n + 1))).domain_nontrivial
    have h3 := Module.finrank_pos (R := k) (M := G.A (n + 1))
    rw [e1, h0, zero_mul] at h3
    exact lt_irrefl _ h3
  have heq : LinearMap.range ml = LinearMap.range jl :=
    Submodule.eq_of_le_of_finrank_eq hle (Nat.eq_of_mul_eq_mul_left hpos (e1.symm.trans e2))
  have h3 : ∀ b, f.app (n + 1) b ∈ Set.range (G.mulP n) := by
    intro b
    obtain ⟨c, hc⟩ := h2 b
    have : f.app (n + 1) b ∈ LinearMap.range ml := by
      rw [heq]
      exact ⟨c, hc⟩
    obtain ⟨a, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective ml
    (LinearMap.ker_eq_bot.2 (Test.mulP_injective G n))
  exact GlobalTheory.bialgHom_factor_through_split k (G.A (n + 1)) (G.A n) (H.A (n + 1)) (G.mulP n) ρ
    (f.app (n + 1)) (fun a => LinearMap.congr_fun hρ a) h3

theorem exists_eq_p_smul [Fact p.Prime] {G H : PDivGroup p k} (f : G ⟶ H) (hf : f.conv 1 = 1) :
    ∃ g : G ⟶ H, f = (p : ℤ_[p]) • g := by
  choose g' hg' using exists_factor f hf
  have hker : ∀ n, RingHom.ker (H.res n) ≤ RingHom.ker (g' n) := by
    intro n
    rw [H.ker_res]
    refine (kerIdeal_le_ker_iff _ (g' n : H.A (n + 1) →ₐ[k] G.A n)).2 fun c => ?_
    change g' n (mulBy k _ (p ^ n) c) = _
    rw [map_mulBy, G.mulBy_pow_self, CoalgHomClass.counit_comp_apply]
  let gapp : ∀ n, H.A n →ₐc[k] G.A n := fun n =>
    liftSurj (H.res n) (H.res_surjective n) (g' n) (hker n)
  have hg : ∀ n b, gapp n (H.res n b) = g' n b := fun n b => liftSurj_apply ..
  have hcomm : ∀ n, (G.res n).comp (gapp (n + 1)) = (gapp n).comp (H.res n) := by
    intro n
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective (n + 1) a
    apply Test.mulP_injective G n
    change G.mulP n (G.res n (gapp (n + 1) (H.res (n + 1) b))) =
      G.mulP n (gapp n (H.res n (H.res (n + 1) b)))
    rw [hg, hg, mulP_res, hg' n, ← res_app, ← hg' (n + 1) b, res_mulP]
  refine ⟨⟨gapp, hcomm⟩, hom_ext_conv fun n => ?_⟩
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self n _)]
  have hfa : f.app n = (mulBy k (G.A n) p).comp (gapp n) := by
    refine BialgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := H.res_surjective n a
    rw [← res_app, ← hg' n b, res_mulP, BialgHom.comp_apply, hg]
  change toConv (f.app n) = toConv (gapp n) ^ p
  rw [hfa, mulBy_comp, toConv_ofConv]

theorem conv_eq_one_of_p_smul [Fact p.Prime] {G H : PDivGroup p k} (g : G ⟶ H) (m : ℕ)
    (h : ((p : ℤ_[p]) • g).conv (m + 1) = 1) : g.conv m = 1 := by
  rw [smul_conv, pow_digit_natCast (H.hom_pow_self _ _)] at h
  have h' : ∀ b, mulBy k (G.A (m + 1)) p (g.app (m + 1) b) = algebraMap k _ (counit b) := by
    intro b
    have e := DFunLike.congr_fun (congrArg ofConv h) b
    have e2 := DFunLike.congr_fun (mulBy_comp (g.app (m + 1)) p) b
    rw [BialgHom.comp_apply] at e2
    rw [e2]
    simpa using e
  apply ofConv_injective
  refine BialgHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := H.res_surjective m a
  apply Test.mulP_injective G m
  change G.mulP m (g.app m (H.res m b)) = G.mulP m (algebraMap k _ (counit (H.res m b)))
  rw [← res_app, mulP_res, h', CoalgHomClass.counit_comp_apply]
  exact (AlgHomClass.commutes (G.mulP m) _).symm

theorem exists_eq_pow_smul [Fact p.Prime] {G H : PDivGroup p k} (m : ℕ) :
    ∀ f : G ⟶ H, f.conv m = 1 → ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g := by
  induction m with
  | zero => exact fun f _ => ⟨f, by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    intro f hf
    obtain ⟨g, rfl⟩ := exists_eq_p_smul f (conv_eq_one_of_le f (by omega) hf)
    obtain ⟨g2, rfl⟩ := ih g (conv_eq_one_of_p_smul g m hf)
    exact ⟨g2, by rw [smul_smul, ← pow_succ']⟩

theorem divisible_of_conv_eq_one : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (m : ℕ) (f : G ⟶ H), f.conv m = 1 →
      ∃ g : G ⟶ H, f = (p : ℤ_[p]) ^ m • g :=
  fun _ _ _ _ _ _ _ m f hf => exists_eq_pow_smul m f hf

end GlobalTheory.PDivGroup.DivP
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem rowDiv_succ_rec (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) (k : ℕ) :
    ((k : MvPolynomial (Fin r × Fin m) R) + 1) * rowDiv R a b (k + 1) f +
      (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) R) * rowDiv R a b k f =
      rowE R r m a b (rowDiv R a b k f) := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    have h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [h]
    cases k with
    | zero => simp [rowE_C, Polynomial.coeff_C]
    | succ k => simp
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.coeff_add, ← hp, ← hq]
    ring
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy
    have hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) =
        Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X := by
      rw [rowGen, aeval_X, hy]
      by_cases h : b = c
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]
    have hx : rowE R r m a b (X (c, s)) = y := rowE_X R r m a b c s
    have hy' : rowE R r m a b y = (if a = b then 1 else 0) * y := by
      rw [hy]
      split_ifs with h1 h2 h2
      · rw [rowE_X, if_pos h2.symm, one_mul]
      · rw [rowE_X, if_neg (Ne.symm h2), zero_mul]
      · simp
      · simp
    have hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) =
        (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y := by
      intro j
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_C]
    have h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s) := by
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C,
        add_zero]
    cases k with
    | zero =>
      rw [hs, h0, rowE_mul, hx, ← hp]
      push_cast
      ring
    | succ k =>
      rw [hs (k + 1), hs k, map_add (f := rowE R r m a b), rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]
      push_cast
      ring

theorem rowDiv_mem_of_rowE {K : Type} [Field K] [CharZero K] {r m : ℕ} (a b : Fin r)
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K)) (h : ∀ f ∈ M, rowE K r m a b f ∈ M) (k : ℕ)
    {f : MvPolynomial (Fin r × Fin m) K} (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  induction k with
  | zero => rw [(rowE_eq_rowDiv K r m a b f).2]; exact hf
  | succ k ih =>
    have hrec := rowDiv_succ_rec K a b f k
    have h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M := by
      split_ifs
      · rw [one_mul, ← nsmul_eq_mul]; exact nsmul_mem ih k
      · simp
    have h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]
      exact M.sub_mem (h _ ih) h1
    exact (M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2

theorem dualWeyl_le_of_rowE_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M →
      (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  intro K _ _ n ν hν M h0 hE
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih

end GlobalTheory.BrCompare
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GaloisLBDescent

theorem lbIso_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [IsCommMonObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left) (φ : A.left ⟶ B.left) (PA : RigLB A) (PB : RigLB B) (L' : LB A'.left), IsAbelianScheme A → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ → IsGrpPullback A B f φ → L'.IsLB → LBIso L' (PA.L.pull φ₁) → LBIso L' (PB.L.pull (φ₁ ≫ φ)) → LBIso PA.L (PB.L.pull φ) := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ _ φ₁ φ PA PB L' hA hG h₁ h hL' i₁ i₂
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hPA := PA.isLB
  have h₂ := pull_isLB PB.isLB φ
  have hN := LB.isLB_div h₂ hPA
  have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ PB.isLB) - CechPic.cls _ hPA :=
    CechPic.cls_div h₂ hPA hN
  have zA : CechPic.pull (eSec A) (CechPic.cls _ PA.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PA.isLB _)).2 ⟨_, PA.rigGen⟩
  have zB : CechPic.pull (eSec B) (CechPic.cls _ PB.isLB) = 0 :=
    (CechPic.cls_eq_zero_iff (pull_isLB PB.isLB _)).2 ⟨_, PB.rigGen⟩
  have c₁ : CechPic.cls _ hL' = CechPic.pull φ₁ (CechPic.cls _ PA.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PA.isLB _)).2 i₁
  have c₂ : CechPic.cls _ hL' = CechPic.pull (φ₁ ≫ φ) (CechPic.cls _ PB.isLB) :=
    (CechPic.cls_eq_iff hL' (pull_isLB PB.isLB _)).2 i₂
  refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns S S₁ π₁ A _ hA hN
    inferInstance inferInstance inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · have he : eSec A ≫ φ = f ≫ eSec B := GlobalTheory.PolBaseChange.eSec_comm h
    rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, zA, he, CechPic.pull_comp, zB, map_zero,
      sub_zero]
  · rw [CechPic.cls_pull hN, cN, ← h₁.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub,
      ← CechPic.pull_comp φ₁ φ, ← c₁, ← c₂, sub_self, map_zero]

end GlobalTheory.GaloisLBDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DescPolKer

theorem pow_eq_one_of_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ e hG hA hA₀ hφ hsq hP hP₀ hw hker T x ⟨t, ht⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact pow_zero x
  let T₁ : Over X := Over.mk (pullback.snd T.hom π)
  let ε : T₁.left ⟶ T.left := pullback.fst T.hom π
  have hε : Epi ε := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG T.hom
  let x₁ : T₁ ⟶ A := Over.homMk (hφ.1.lift (ε ≫ x.left) (pullback.snd T.hom π)
    (by simp [ε, pullback.condition])) (hφ.1.lift_snd _ _ _)
  have hx₁ : x₁.left ≫ φ = ε ≫ x.left := hφ.1.lift_fst _ _ _

  have p₀ : IsPullback (snd A₀ T).left (fst A₀ T).left T.hom A₀.hom :=
    (IsPullback.of_hasPullback A₀.hom T.hom).flip
  have w₀ : ((snd A T₁).left ≫ ε) ≫ T.hom = ((fst A T₁).left ≫ φ) ≫ A₀.hom := by
    have a₁ := Over.w (snd A T₁)
    have a₂ := Over.w (fst A T₁)
    simp only [T₁, Over.mk_hom] at a₁
    rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (fst A T₁).left, a₂, ← a₁, Category.assoc]
    simp [ε, pullback.condition]
    rfl
  let hm : (A ⊗ T₁).left ⟶ (A₀ ⊗ T).left := p₀.lift _ _ w₀
  have hc : (lift (snd A T₁ ≫ x₁) (fst A T₁)).left ≫ φ₂ = hm ≫ (lift (snd A₀ T ≫ x) (fst A₀ T)).left := by
    have p₂ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom :=
      (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
    apply p₂.hom_ext
    · rw [Category.assoc, hsq.2, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_snd, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_snd, p₀.lift_snd]
    · rw [Category.assoc, hsq.1, ← Category.assoc, GlobalTheory.TripleDescent.lift_left_fst, Category.assoc,
        GlobalTheory.TripleDescent.lift_left_fst, Over.comp_left, Over.comp_left, Category.assoc, hx₁,
        ← Category.assoc, ← Category.assoc, p₀.lift_fst]
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t', ht', -⟩ := GlobalTheory.FamFieldPull.exists_genPull w hwg hP₀ hP (K := PUnit)
    (fun _ => (lift (snd A T₁ ≫ x₁) (fst A T₁)).left) (fun _ => (lift (snd A₀ T ≫ x) (fst A₀ T)).left)
    (fun _ => 1) hm (fun _ => hc) t ht
  have h₁ : x₁ ^ e = 1 := hker T₁ x₁ ⟨t', ht'⟩

  let j : Over.mk (T₁.hom ≫ π) ⟶ T := Over.homMk ε (by simp [T₁, ε, pullback.condition])
  have hj : (j ≫ x).left = x₁.left ≫ φ := by simp [j, hx₁]
  have hpow : ∀ n : ℕ, ((j ≫ x) ^ (n + 1)).left = (x₁ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      rw [pow_succ, pow_succ x₁]
      exact hφ.2 T₁ (x₁ ^ (n + 1)) x₁ _ _ ih hj
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hy : (j ≫ x) ^ (k + 1) * (j ≫ x) ^ (k + 1) = (j ≫ x) ^ (k + 1) := by
    apply Over.OverMorphism.ext
    rw [← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, hpow, hpow,
      show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add, h₁, _root_.one_mul]
  have hy1 := mul_eq_left.1 hy
  apply Over.OverMorphism.ext
  rw [← cancel_epi ε]
  have e₁ : ε ≫ (x ^ (k + 1)).left = (j ≫ x ^ (k + 1)).left := by rw [Over.comp_left]; rfl
  have e₂ : ε ≫ (1 : T ⟶ A₀).left = (j ≫ (1 : T ⟶ A₀)).left := by rw [Over.comp_left]; rfl
  rw [e₁, e₂, MonObj.comp_pow, hy1, MonObj.comp_one]

end GlobalTheory.DescPolKer
end
end

section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_permMatrix_rep_parabolic_doubleCoset : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ), Monotone b → Monotone b' → ∀ g : GL (Fin r) F, ∃ (w : Equiv.Perm (Fin r)) (p' : blockTri (κ := F) b') (p : blockTri (κ := F) b), g = (p' : GL (Fin r) F) * permGL F w * (p : GL (Fin r) F) := by
  first | exact @GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | exact GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri | (intros; apply GlobalTheory.FinGL.Bruhat.exists_perm_rep_blockTri <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CosocleComp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def subrepOfComp (ρ : Representation ℂ G V) (s : H →* G) (hs : Function.Surjective s) :
    Subrepresentation (ρ.comp s : Representation ℂ H V) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hs g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule (s h) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {ρ : Representation ℂ G V} {s : H →* G} (hs : Function.Surjective s)
    (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp s : Representation ℂ H V) :=
  (subrepOfComp ρ s hs).isSimpleOrder_iff.2 h

theorem isCosocle_comp : ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ G W) (π : Representation ℂ G V) (s : H →* G), Function.Surjective s →
    IsCosocle σ π → IsCosocle (σ.comp s) (π.comp s) := by
  intro G H V W _ _ _ _ _ _ σ π s hs h
  obtain ⟨hi, f, hf, hS⟩ := h
  let f' : Representation.IntertwiningMap (π.comp s : Representation ℂ H V) (σ.comp s : Representation ℂ H W) := ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩
  refine ⟨isIrreducible_comp hs hi, f', hf, fun S hS' => ?_⟩
  have h1 := hS (subrepOfComp π s hs S) ((OrderIso.isCoatom_iff (subrepOfComp π s hs) S).2 hS')
  have h2 := congrArg Subrepresentation.toSubmodule h1
  have inj : Function.Injective (Subrepresentation.toSubmodule (ρ := (π.comp s : Representation ℂ H V))) := by
    rintro ⟨a, _⟩ ⟨b, _⟩ rfl; rfl
  exact inj h2

end GlobalTheory.CosocleComp
end
end
