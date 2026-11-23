module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle007
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s → (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧ (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧ ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → mangoldt s P = 0 := by
  first | exact @GlobalTheory.CuspGL.mangoldt_conv_spec | exact GlobalTheory.CuspGL.mangoldt_conv_spec | (intros; apply GlobalTheory.CuspGL.mangoldt_conv_spec <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ φ : Module.End F V → ℂ, IsPrimitive φ → ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | exact GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | (intros; apply GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.monicFactorizationConvolution_cancel_of_one : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 → (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  first | exact @GlobalTheory.CuspGL.ConvCancel.conv_cancel | exact GlobalTheory.CuspGL.ConvCancel.conv_cancel | (intros; apply GlobalTheory.CuspGL.ConvCancel.conv_cancel <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : Module.End F V) (p q : F[X]) (hp : Irreducible p)
    (hd : p ∣ LinearMap.charpoly T) (hq : aeval T q = 0) : p ∣ q := by
  have : Fact (Irreducible p) := ⟨hp⟩
  have hroot : (LinearMap.charpoly (T.baseChange (AdjoinRoot p))).IsRoot (AdjoinRoot.root p) := by
    rw [LinearMap.charpoly_baseChange]
    obtain ⟨r, hr⟩ := hd
    rw [hr, Polynomial.map_mul, IsRoot, eval_mul, AdjoinRoot.algebraMap_eq,
      (AdjoinRoot.isRoot_root p).eq_zero, zero_mul]
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot).exists_hasEigenvector
  have h0 : aeval (T.baseChange (AdjoinRoot p)) (q.map (algebraMap F (AdjoinRoot p))) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    change aeval (Module.End.baseChangeHom F (AdjoinRoot p) V T) q = 0
    rw [Polynomial.aeval_algHom_apply, hq, map_zero]
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap F (AdjoinRoot p))) hv
  rw [h0, LinearMap.zero_apply] at h1
  have hz : (q.map (algebraMap F (AdjoinRoot p))).eval (AdjoinRoot.root p) = 0 := by
    rcases smul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hv.2
  rw [Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at hz
  exact hz

theorem eq_zero_of_not_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V →
    ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
      LinearMap.charpoly g = f ^ m) → φ g = 0 := by
  intro F _ _ V _ _ _ φ hcl hpr hdim g hg
  have hmon : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hne0 : LinearMap.charpoly g ≠ 0 := hmon.ne_zero
  have hnu : ¬ IsUnit (LinearMap.charpoly g) := by
    intro hu
    have h := LinearMap.charpoly_natDegree g
    rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at h
    omega
  obtain ⟨f, hfm, hf, hfd⟩ := Polynomial.exists_monic_irreducible_factor _ hnu
  obtain ⟨m, Q, hnd, hfac⟩ := WfDvdMonoid.max_power_factor hne0 hf
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero, one_mul] at hfac
      exact absurd (hfac ▸ hfd) hnd
    · exact h
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hfac
    exact hne0 hfac
  have hQ : ¬ IsUnit Q := by
    intro hu
    have hQm : Q.Monic := (hfm.pow m).of_mul_monic_left (hfac ▸ hmon)
    have h1 : Q = 1 := hQm.eq_one_of_isUnit hu
    exact hg ⟨f, m, hfm, hf, hm, by rw [hfac, h1, mul_one]⟩
  have hcop : IsCoprime (f ^ m) Q := ((hf.coprime_iff_not_dvd).mpr hnd).pow_left
  have hPQ : aeval g (f ^ m) * aeval g Q = 0 := by
    rw [← map_mul, ← hfac, LinearMap.aeval_self_charpoly]
  have hgA : ∀ x ∈ LinearMap.ker (aeval g (f ^ m)), g x ∈ LinearMap.ker (aeval g (f ^ m)) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hc : aeval g (f ^ m) * g = g * aeval g (f ^ m) := by
      calc aeval g (f ^ m) * g = aeval g (f ^ m * X) := by rw [map_mul, aeval_X]
        _ = aeval g (X * f ^ m) := by rw [mul_comm]
        _ = g * aeval g (f ^ m) := by rw [map_mul, aeval_X]
    have h := congrArg (fun u : Module.End F V => u x) hc
    simp only [Module.End.mul_apply] at h
    rw [h, hx, map_zero]
  set A := LinearMap.ker (aeval g (f ^ m)) with hAdef
  have hPA : aeval (g.restrict hgA) (f ^ m) = 0 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have h := intertwine_aeval_apply A.subtype (g.restrict hgA) g (fun _ => rfl) (f ^ m) x
    rw [Submodule.subtype_apply, Submodule.subtype_apply] at h
    rw [h, LinearMap.zero_apply, Submodule.coe_zero]
    exact LinearMap.mem_ker.mp x.2
  have hQq : aeval (A.mapQ A g (fun x hx => hgA x hx)) Q = 0 := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := A.mkQ_surjective y
    have h := intertwine_aeval_apply A.mkQ g (A.mapQ A g (fun x hx => hgA x hx)) (fun _ => rfl) Q x
    rw [← h, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      hAdef, LinearMap.mem_ker, ← Module.End.mul_apply, hPQ, LinearMap.zero_apply]
  have hcp : IsCoprime (LinearMap.charpoly (g.restrict hgA))
      (LinearMap.charpoly (A.mapQ A g (fun x hx => hgA x hx))) := by
    refine isCoprime_of_irreducible_dvd (fun h => (LinearMap.charpoly_monic _).ne_zero h.1) ?_
    intro z hz hzA hzQ
    have h1 : z ∣ f ^ m :=
      irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero (g.restrict hgA) z (f ^ m) hz hzA hPA
    have h2 : z ∣ Q := irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ z Q hz hzQ hQq
    exact hz.not_isUnit (hcop.isUnit_of_dvd' h1 h2)
  have hAbot : A ≠ ⊥ := by
    intro hA
    have hsup := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime g hcop
    rw [← hAdef, hA, bot_sup_eq, ← hfac, LinearMap.aeval_self_charpoly, LinearMap.ker_zero] at hsup
    have hQ0' : aeval g Q = 0 := LinearMap.ker_eq_top.mp hsup
    exact hnd (irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero g f Q hf hfd hQ0')
  have hAtop : A ≠ ⊤ := by
    intro hA
    have hP0 : aeval g (f ^ m) = 0 := LinearMap.ker_eq_top.mp hA
    obtain ⟨z, hz, hzQ⟩ := WfDvdMonoid.exists_irreducible_factor hQ hQ0
    have hzc : z ∣ LinearMap.charpoly g := hzQ.trans ⟨f ^ m, by rw [hfac, mul_comm]⟩
    have h1 : z ∣ f ^ m := irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero g z (f ^ m) hz hzc hP0
    exact hz.not_isUnit (hcop.isUnit_of_dvd' h1 hzQ)
  have hconj := exists_conj_eq_add_of_isCoprime F V A g hgA hcp
  have hsum := hpr A hAbot hAtop g hgA
  have hconst : ∀ h ∈ nilRad A, φ (g + h) = φ g := by
    intro h hh
    obtain ⟨e, he⟩ := hconj h hh
    rw [← he, hcl]
  rw [finsum_mem_congr rfl hconst] at hsum
  have : Finite V := Module.finite_of_finite F
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun u : Module.End F V => (u : V → V)) DFunLike.coe_injective
  have hfin : (nilRad A).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul] at hsum
  have h0 : (0 : Module.End F V) ∈ nilRad A := ⟨fun _ => A.zero_mem, fun _ _ => rfl⟩
  have hcard : (hfin.toFinset.card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨0, hfin.mem_toFinset.mpr h0⟩)
  exact (mul_eq_zero.mp hsum).resolve_left hcard

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P := by
  first | exact @GlobalTheory.CuspGL.conv_basic | exact GlobalTheory.CuspGL.conv_basic | (intros; apply GlobalTheory.CuspGL.conv_basic <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V), (∀ x ∈ A, g x ∈ A) → W ⊓ A ≠ ⊥ → ¬ W ≤ A → ∀ φ : Module.End F W → ℂ, IsPrimitive φ → ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}, φ ((g + h.1).restrict h.2.2) = 0 := by
  first | exact @GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | exact GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | (intros; apply GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical : ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (nilRad A) := by
  first | exact @GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | exact GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad | (intros; apply GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A), LinearMap.charpoly g = LinearMap.charpoly (g.restrict hg) * LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)) ∧ ∀ h ∈ nilRad A, LinearMap.charpoly (g + h) = LinearMap.charpoly g := by
  first | exact @GlobalTheory.CuspGL.charpoly_block | exact GlobalTheory.CuspGL.charpoly_block | (intros; apply GlobalTheory.CuspGL.charpoly_block <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.ker_aeval_add_stabilizerNilradical_socle : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g h : Module.End F V) (f : F[X]), h ∈ nilRad (LinearMap.ker (aeval g f)) → LinearMap.ker (aeval g f) ≤ LinearMap.ker (aeval (g + h) f) ∧ (LinearMap.ker (aeval (g + h) f) = LinearMap.ker (aeval g f) → ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = Module.finrank F (LinearMap.ker (aeval (g + h) (f ^ j)))) := by
  first | exact @GlobalTheory.CuspGL.ker_aeval_add_nilRad | exact GlobalTheory.CuspGL.ker_aeval_add_nilRad | (intros; apply GlobalTheory.CuspGL.ker_aeval_add_nilRad <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧ ∀ k : ℕ, rootSum θ k (minpoly F α ^ (n / (minpoly F α).natDegree)) = ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  first | exact @GlobalTheory.CuspGL.torus_minpoly | exact GlobalTheory.CuspGL.torus_minpoly | (intros; apply GlobalTheory.CuspGL.torus_minpoly <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem charpoly_eq_finsum_psi (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (g : Module.End F V) :
    s (LinearMap.charpoly g) =
      ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  haveI := Fintype.ofFinite {W : Submodule F V // ∀ x ∈ W, g x ∈ W}
  haveI := Fintype.ofFinite {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}
  let T : {W : Submodule F V // ∀ x ∈ W, g x ∈ W} := ⟨⊤, fun _ _ => Submodule.mem_top⟩
  have hT : psi s T.1 (g.restrict T.2) = psi s V g := by
    rw [← psi_conj F s T.1 V Submodule.topEquiv (g.restrict T.2)]
    congr 1
  rw [finsum_eq_sum_of_fintype, ← Finset.add_sum_erase _ _ (Finset.mem_univ T), hT, psi_eq,
    finsum_eq_sum_of_fintype]
  rw [sub_add, eq_comm, sub_eq_self, sub_eq_zero]
  refine Finset.sum_bij (fun W _ => ⟨W.1, W.2.2⟩) ?_ ?_ ?_ ?_
  · intro W _
    refine Finset.mem_erase.2 ⟨fun h => W.2.1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a _ b _ h
    exact Subtype.ext (Subtype.mk.inj h)
  · intro b hb
    exact ⟨⟨b.1, fun h => (Finset.mem_erase.1 hb).1 (Subtype.ext h), b.2⟩, Finset.mem_univ _, rfl⟩
  · intro a _
    rfl

end GlobalTheory.CuspGL
end

section

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  first | exact @GlobalTheory.CuspGL.psi_of_irreducible_charpoly | exact GlobalTheory.CuspGL.psi_of_irreducible_charpoly | (intros; apply GlobalTheory.CuspGL.psi_of_irreducible_charpoly <;> assumption)
end
