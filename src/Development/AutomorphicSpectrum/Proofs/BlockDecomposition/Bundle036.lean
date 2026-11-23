module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dual.Basis

@[expose] public section

section

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem exists_rho {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (hx : C.Comp x) :
    ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  obtain ⟨e, z, hz⟩ := hC.lift j x hx
  haveI := hC.fin j
  have hunit : IsUnit (C.ℓ : B) := by
    first
    | exact hC.unit
    | simpa using hC.unit.map C.ι
    | simpa using hC.unit.map C.o
    | simpa using (hC.unit.map C.lam).map C.ι
  obtain ⟨u, hu⟩ := hunit
  let w : C.W j := ((u⁻¹ : Bˣ) : B) ^ e • C.b j z
  let bs₀ := Module.finBasis K (C.V j)
  obtain ⟨g, hg, -⟩ := hC.basis j bs₀ w
  let f : Module.Dual K (C.V j) →+ B :=
    { toFun := fun φ => ∑ t, C.o (φ (bs₀ t)) * g t
      map_zero' := by simp
      map_add' := fun φ ψ => by simp [add_mul, Finset.sum_add_distrib] }
  refine ⟨f, fun k φ => ?_, e, z, hz, fun {m} bs => ?_⟩
  · simp [f, Finset.mul_sum, mul_assoc]
  · have key : ∑ s, f (bs.coord s) • C.μ j (bs s) = w := by
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_smul]
      rw [Finset.sum_comm, hg]
      refine Finset.sum_congr rfl fun t _ => ?_
      conv_rhs => rw [← bs.sum_repr (bs₀ t)]

      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_smul, Module.Basis.coord_apply, mul_comm]
    rw [key, ← hu, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]

end GlobalTheory.CompanionTheory.KapRho
end

section

set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem semilinear_eq_sum_coord {K B : Type*} {V : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] (o : K →+* B) (f : Module.Dual K V →+ B)
    (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ) {m : ℕ} (bs : Module.Basis (Fin m) K V)
    (φ : Module.Dual K V) : f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_cup :
    ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K)
      (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j)
      (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B)
      (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g →
      C.Rho (fun n => P.cS n i j (x n) (y n)) h →
      ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j))
        (φ : Module.Dual K (C.V (i + j))),
        h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
          C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  intro Λ A B K _ _ _ _ C hC P hP i j x y f g h hf hg hh m m' bs bs' φ
  obtain ⟨-, e, z, hzr, hzb⟩ := hf
  obtain ⟨-, e', w, hwr, hwb⟩ := hg
  obtain ⟨hh1, e'', u, hur, hub⟩ := hh
  haveI := hC.fin (i + j)
  let b := Module.finBasis K (C.V (i + j))
  have hv : ∀ n, C.red n (i + j) (P.cZ i j z w) =
      ((C.ℓ : A) ^ (e + e')) • C.r n (i + j) (P.cS n i j (x n) (y n)) := by
    intro n
    rw [hP.red, hzr, hwr, hP.r, map_smul, LinearMap.map_smul₂, smul_smul, pow_add, mul_comm]
  have hd : C.b (i + j) (((C.ℓ : A) ^ (e + e')) • u - ((C.ℓ : A) ^ e'') • P.cZ i j z w) = 0 := by
    refine hC.sep _ _ fun n => ?_
    have hu := hur n
    simp only at hu
    rw [map_sub, map_smul, map_smul, hu, hv n, smul_smul, smul_smul, mul_comm, sub_self]
  have key : ((C.ℓ : B) ^ (e + e')) • C.b (i + j) u =
      ((C.ℓ : B) ^ e'') • C.b (i + j) (P.cZ i j z w) := by
    rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, sub_eq_zero] at hd
    simpa only [map_pow, map_natCast] using hd
  let c : Fin (Module.finrank K (C.V (i + j))) → B := fun t =>
    ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
      C.o (b.coord t (P.cV i j (bs s) (bs' s')))
  have hμ : ∀ s s', P.cW i j (C.μ i (bs s)) (C.μ j (bs' s')) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) • C.μ (i + j) (b t) := by
    intro s s'
    rw [← hP.μ]
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]

    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.coord_apply]
  have hcup : P.cW i j (∑ s, f (bs.coord s) • C.μ i (bs s))
      (∑ s', g (bs'.coord s') • C.μ j (bs' s')) = ∑ t, c t • C.μ (i + j) (b t) := by

    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hμ, c,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hcoef : ∑ t, h (b.coord t) • C.μ (i + j) (b t) = ∑ t, c t • C.μ (i + j) (b t) := by
    have hu : IsUnit ((C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'') :=
      (hC.unit.pow _).mul (hC.unit.pow _)
    refine (hu.smul_left_cancel).1 ?_
    rw [hP.b, ← hub b, ← hzb bs, ← hwb bs', map_smul, LinearMap.map_smul₂, hcup, smul_smul,
      smul_smul, smul_smul] at key
    have hl : (C.ℓ : B) ^ e'' * (C.ℓ : B) ^ e' * (C.ℓ : B) ^ e =
        (C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'' := by ring
    rwa [hl] at key
  have hc : ∀ t, h (b.coord t) = c t := by
    obtain ⟨g₀, -, hg₀⟩ := hC.basis (i + j) b (∑ t, c t • C.μ (i + j) (b t))
    have h1 := hg₀ c rfl
    have h2 := hg₀ (fun t => h (b.coord t)) hcoef.symm
    exact fun t => congrFun (h2.trans h1.symm) t
  have hφ : ∀ s s', C.o (φ (P.cV i j (bs s) (bs' s'))) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) * C.o (φ (b t)) := by
    intro s s'
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]

    simp only [map_sum, map_smul, smul_eq_mul, map_mul, Module.Basis.coord_apply]
  refine (semilinear_eq_sum_coord C.o h hh1 b φ).trans ?_
  simp only [hc, c, hφ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.KapRho
end

section

open Module CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUniq

theorem eq_of_unit_smul_combination {K B V M : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup M] [Module B M]
    (o : K →+* B) (μ : V → M) (c : B) (hc : IsUnit c)
    (hind : ∀ (m : ℕ) (bs : Basis (Fin m) K V) (g : Fin m → B),
      ∑ s, g s • μ (bs s) = 0 → ∀ s, g s = 0)
    (f f' : Dual K V →+ B)
    (hf : ∀ (k : K) (φ : Dual K V), f (k • φ) = o k * f φ)
    (hf' : ∀ (k : K) (φ : Dual K V), f' (k • φ) = o k * f' φ)
    (h : ∀ (m : ℕ) (bs : Basis (Fin m) K V),
      c • ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0) :
    f = f' := by
  classical
  let bs := Module.finBasis K V
  have h0 : ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0 := by
    obtain ⟨u, rfl⟩ := hc
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) • x) (h _ bs)
    simpa [smul_smul] using this
  have hco : ∀ s, f (bs.coord s) = f' (bs.coord s) :=
    fun s => sub_eq_zero.mp (hind _ bs _ h0 s)
  have key : ∀ F : Dual K V →+ B, (∀ (k : K) (φ : Dual K V), F (k • φ) = o k * F φ) →
      ∀ φ : Dual K V, F φ = ∑ s, F (bs.coord s) * o (φ (bs s)) := by
    intro F hF φ
    have e : ∑ s, φ (bs s) • bs.coord s = φ := bs.sum_dual_apply_smul_coord φ
    calc F φ = F (∑ s, φ (bs s) • bs.coord s) := by rw [e]
      _ = _ := by

        rw [map_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [hF, mul_comm]
  ext φ
  rw [key f hf, key f' hf']
  exact Finset.sum_congr rfl fun s _ => by rw [hco]

theorem rho_unique {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j)
    (f f' : Module.Dual K (C.V j) →+ B) : C.Rho x f → C.Rho x f' → f = f' := by
  rintro ⟨hfs, e, z, hz, hzb⟩ ⟨hfs', e', z', hz', hzb'⟩
  haveI := hC.fin j
  have hw : C.b j (((C.ℓ : A) ^ e) • z' - ((C.ℓ : A) ^ e') • z) = 0 := by
    apply hC.sep
    intro n
    rw [map_sub, map_smul, map_smul, hz n, hz' n, smul_smul, smul_smul, mul_comm, sub_self]
  have hb : ∀ (a : A) (y : C.Z j), C.b j (a • y) = C.ι a • C.b j y :=
    fun a y => (C.b j).map_smulₛₗ a y
  refine (eq_of_unit_smul_combination C.o (C.μ j) ((C.ℓ : B) ^ (e + e')) (hC.unit.pow _) ?_
    f' f hfs' hfs ?_).symm
  · intro m bs g hg s
    obtain ⟨g0, _, hu⟩ := hC.basis j bs 0
    have h1 := hu g hg.symm
    have h2 := hu 0 (by simp)
    exact congrFun (h1.trans h2.symm) s
  · intro m bs
    have h := hw
    rw [map_sub, hb, hb, ← hzb bs, ← hzb' bs] at h
    simp only [map_pow, map_natCast, smul_smul] at h
    simp_rw [sub_smul, Finset.sum_sub_distrib, smul_sub]
    rw [← h, pow_add, mul_comm ((C.ℓ : B) ^ e') ((C.ℓ : B) ^ e)]

end GlobalTheory.CompanionTheory.KapUniq
end

section

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUnit

theorem rho_one_eval : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  intro Λ A B K _ _ _ _ C hC P hP h hR φ
  obtain ⟨hsem, e, z, hz, hb⟩ := hR
  have hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV := by
    have h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0 := hC.sep 0 _ (fun n => by
      rw [map_sub, map_smul, hP.one_r, hz, sub_self])
    rw [map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero] at h0
    rw [h0]
    simp
  haveI := hC.fin 0
  let bs := Module.finBasis K (C.V 0)
  have h1 := hb bs
  rw [hw] at h1
  have h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV := by
    obtain ⟨u, hu⟩ := hC.unit.pow e
    rw [← hu] at h1
    have h1' := congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1
    simpa only [smul_smul, Units.inv_mul, one_smul] using h1'
  have h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ]
    rfl
  have h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV) :=
    (hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3
  have h5 : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  have h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]

    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl

  rw [h6, map_sum]
  conv_lhs => rw [h5]

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsem, map_mul, mul_comm]
  exact congrArg (· * C.o (φ (bs s))) (congrFun h4 s)

end GlobalTheory.CompanionTheory.KapUnit
end

section

open CrystallineSemistableComparison.Pb.Kap

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.KapRhoHom

private theorem dual_expand {K B : Type} {V : Type*} [Field K] [CommRing B] [AddCommGroup V] [Module K V]
    (o : K →+* B) (f : Module.Dual K V →+ B) (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ)
    {m : ℕ} (bs : Module.Basis (Fin m) K V) (φ : Module.Dual K V) :
    f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]

  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_hom :
    ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ']
      [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K)
      (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j)
      (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
        C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  intro Λ A B K Λ' A' B' _ _ _ _ _ _ _ C C' h hC hC' hh j x f hR
  obtain ⟨hs, e, z, hz, hW⟩ := hR
  have htr : ∀ φ : Module.Dual K (C'.V j),
      h.tr j f φ = h.sB (f (Module.Dual.transpose (R := K) (h.fV j) φ)) := fun φ => rfl
  refine ⟨fun k φ => ?_, e, h.fZ j z, fun n => ?_, ?_⟩
  · rw [htr, htr, map_smul, hs, map_mul, hh.o]
  · rw [← hh.red, hz, map_smulₛₗ, hh.r, map_pow, map_natCast, hh.ℓ]
  · intro m bs'
    haveI := hC.fin j
    have bs := Module.finBasis K (C.V j)
    have hE := congrArg (h.fW j) (hW bs)

    rw [hh.b, map_smulₛₗ, map_sum, map_pow, map_natCast] at hE
    rw [← hE, hh.ℓ]
    congr 1
    have hexp : ∀ t, h.tr j f (bs'.coord t) =
        ∑ s, h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s))) := by
      intro t

      rw [htr, dual_expand C.o f hs bs, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, hh.o]
      rfl
    have hμ : ∀ s, C'.μ j (h.fV j (bs s)) =
        ∑ t, C'.o (bs'.coord t (h.fV j (bs s))) • C'.μ j (bs' t) := by
      intro s
      conv_lhs => rw [← bs'.sum_repr (h.fV j (bs s))]

      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smulₛₗ]
      rfl
    calc ∑ t, h.tr j f (bs'.coord t) • C'.μ j (bs' t)
        = ∑ t, ∑ s, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hexp, Finset.sum_smul]
      _ = ∑ s, ∑ t, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) :=
          Finset.sum_comm
      _ = ∑ s, h.fW j (f (bs.coord s) • C.μ j (bs s)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smulₛₗ, hh.μ, hμ, Finset.smul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_smul]

end GlobalTheory.CompanionTheory.KapRhoHom
end

section

set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatDp

theorem mul_divPow_succ {B : Type} [CommRing B] [Algebra ℚ B] (c η : B) (i : ℕ) :
    (c * η) * (((i.factorial : ℚ)⁻¹) • η ^ i) =
      (c * ((i : B) + 1)) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) := by
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have key : ((i : B) + 1) * ((((i + 1).factorial : ℚ)⁻¹) • η ^ (i + 1)) =
      ((i.factorial : ℚ)⁻¹) • η ^ (i + 1) := by
    have h1 : ((i : B) + 1) = algebraMap ℚ B ((i : ℚ) + 1) := by simp
    rw [h1, ← Algebra.smul_def, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [mul_assoc c ((i : B) + 1), key, mul_assoc c η]
  simp only [Algebra.mul_smul_comm, pow_succ]
  congr 2
  ring

theorem natPow_mul_inv_smul {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) :
    (l : B) ^ M * ((((l : ℚ) ^ M)⁻¹) • x) = x := by
  have h0 : ((l : ℚ) ^ M) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl)
  have h1 : ((l : B) ^ M) = algebraMap ℚ B ((l : ℚ) ^ M) := by simp
  rw [h1, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem mul_divPow_eq_elem {B : Type} [CommRing B] [Algebra ℚ B] (x : B) (l M : ℕ) (hl : l ≠ 0) (i : ℕ) :
    x * (((i.factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ i) =
      ((l : B) ^ M * ((i : B) + 1)) *
        ((((i + 1).factorial : ℚ)⁻¹) • ((((l : ℚ) ^ M)⁻¹) • x) ^ (i + 1)) := by
  have h := mul_divPow_succ ((l : B) ^ M) ((((l : ℚ) ^ M)⁻¹) • x) i
  rwa [natPow_mul_inv_smul x l M hl] at h

theorem mul_divPow_eq : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ), l ≠ 0 → ∀ i : ℕ,
    f ξ * Lat.dpE f ξ l M i = ((l : B) ^ M * ((i : B) + 1)) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M hl i
  simp only [Lat.dpE, Lat.η]
  exact mul_divPow_eq_elem (f ξ) l M hl i

end GlobalTheory.CompanionTheory.LatDp
end
end

section

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapChain

theorem rho_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ}
    (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
    C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  intro Λ A B K _ _ _ _ C j c x f hf
  obtain ⟨h1, e, z, h2, h3⟩ := hf
  refine ⟨?_, e, C.lam c • z, ?_, ?_⟩
  · intro k φ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, h1]
    ring
  · intro n
    rw [map_smul, h2 n, Pi.smul_apply, LinearMap.map_smulₛₗ, smul_comm]
  · intro m bs
    rw [LinearMap.map_smulₛₗ, ← h3 bs]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

end GlobalTheory.CompanionTheory.KapChain
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplReg

theorem isCompl_nonZeroDivisor : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := by
  intro B _ T _ π g hC hπ
  exact nonZeroDivisor_of_dense_of_strict π g hC.compl.toIsHausdorff hC.surj hC.inj hπ

end GlobalTheory.CompanionTheory.ComplReg
end
