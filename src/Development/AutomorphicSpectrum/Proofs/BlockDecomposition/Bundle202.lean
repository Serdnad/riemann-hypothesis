module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle195
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle196
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle197
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShDesc

universe w

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

def cechMap (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S) (n : ℕ) : P.cech.X n →ₗ[R] Q.cech.X n :=
  LinearMap.pi fun i => (e (ent i)).comp (LinearMap.proj i)

theorem cechMap_d (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (n : ℕ) (x : P.cech.X n) :
    Q.cech.d n (cechMap P Q e n x) = cechMap P Q e (n + 1) (P.cech.d n x) := by

  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (hn _ _).symm

theorem cechMap_aug (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (x : P.M ∅) :
    Q.aug (e ∅ x) = cechMap P Q e 0 (P.aug x) := by
  funext t
  exact (hn _ _).symm

theorem ex_of_equiv (P Q : PM.{w} R ι) (e : ∀ S, Q.M S ≃ₗ[R] P.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (Q.res h x) = P.res h (e S x)) (hP : P.Ex) : Q.Ex := by
  have hn' : ∀ {S T : Finset ι} (h : S ⊆ T) x, (e T).symm (P.res h x) = Q.res h ((e S).symm x) := by
    intro S T h x
    apply (e T).injective
    rw [hn]
    simp
  let f : ∀ S, P.M S →ₗ[R] Q.M S := fun S => ((e S).symm : P.M S →ₗ[R] Q.M S)
  let g : ∀ S, Q.M S →ₗ[R] P.M S := fun S => ((e S) : Q.M S →ₗ[R] P.M S)
  have hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x) := hn'
  have hg : ∀ {S T : Finset ι} (h : S ⊆ T) x, g T (Q.res h x) = P.res h (g S x) := hn
  have fg : ∀ n (y : Q.cech.X n), cechMap P Q f n (cechMap Q P g n y) = y := by
    intro n y
    funext t
    exact (e _).symm_apply_apply _
  have gf0 : ∀ n (y : P.cech.X n), cechMap Q P g n (cechMap P Q f n y) = y := by
    intro n y
    funext t
    exact (e _).apply_symm_apply _
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · have : Q.aug y = cechMap P Q f 0 (P.aug (g ∅ y)) := by
      rw [← cechMap_aug P Q f hf]
      congr 1
      exact ((e ∅).symm_apply_apply y).symm
    change Q.cech.d 0 (Q.aug y) = 0
    rw [this, cechMap_d P Q f hf, show P.cech.d 0 (P.aug (g ∅ y)) = 0 from h0 _, map_zero]
  · have h := h1 (g ∅ y) (by
      have := cechMap_aug Q P g hg y
      rw [this]
      change cechMap Q P g 0 (Q.aug y) = 0 at *
      rw [hy, map_zero])
    rw [one_smul] at h ⊢
    exact (e ∅).injective (by rw [map_zero]; exact h)
  · obtain ⟨x, hx⟩ := h2 (cechMap Q P g 0 y) (by
      change P.cech.d 0 _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d 0 y = 0 := hy
      rw [hy', map_zero])
    refine ⟨f ∅ x, ?_⟩
    rw [one_smul] at hx ⊢
    rw [cechMap_aug P Q f hf]
    have hx' : P.aug x = cechMap Q P g 0 y := hx
    rw [hx', fg]
  · obtain ⟨x, hx⟩ := h3 n (cechMap Q P g (n + 1) y) (by
      change P.cech.d (n + 1) _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d (n + 1) y = 0 := hy
      rw [hy', map_zero])
    refine ⟨cechMap P Q f n x, ?_⟩
    rw [one_smul] at hx ⊢
    change Q.cech.d n _ = y
    rw [cechMap_d P Q f hf]
    have hx' : P.cech.d n x = cechMap Q P g (n + 1) y := hx
    rw [hx', fg]

theorem ex_of_subsingleton (P : PM.{w} R ι) (h : ∀ S, Subsingleton (P.M S)) : P.Ex := by
  have hX : ∀ n, Subsingleton (P.cech.X n) := fun n =>
    inferInstanceAs (Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)))
  refine ⟨fun x => Subsingleton.elim (α := P.cech.X 1) _ _, fun x _ => Subsingleton.elim _ _,
    fun y _ => ⟨0, Subsingleton.elim (α := P.cech.X 0) _ _⟩, fun n y _ => ⟨0, Subsingleton.elim (α := P.cech.X (n + 1)) _ _⟩⟩

variable {K : Type} [Field K]

def shEv (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m :=
  LinearEquiv.ofBijective
    (LinearMap.proj (φ := fun p : {p : ℕ // p + k = n} => C.X p.1) ⟨m, h⟩) (by
    constructor
    · intro y y' hyy
      funext ⟨p, hp⟩
      obtain rfl : p = m := by omega
      exact hyy
    · intro x
      refine ⟨fun p => (show m = p.1 by have := p.2; omega) ▸ x, rfl⟩)

theorem shSy_desc {ς : ℤˣ} {k : ℕ} {A : Sy.{w} K ι} (hA : A.Desc) : (shSy ς k A).Desc := by
  intro n
  by_cases hk : k ≤ n
  · have h : n - k + k = n := by omega
    exact ex_of_equiv (A.term (n - k)) ((shSy ς k A).term n) (fun S => shEv ς k (A.K S) h)
      (fun _ _ => rfl) (hA (n - k))
  · refine ex_of_subsingleton _ fun S => ?_
    have : IsEmpty {m : ℕ // m + k = n} := ⟨fun p => hk (by have := p.2; omega)⟩
    exact inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, (A.K S).X m.1))

theorem sh_desc : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι),
    A.Desc → (shSy ς k A).Desc :=
  fun _ _ _ h => shSy_desc h

end GlobalTheory.CompanionTheory.KunGlue.ShDesc
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

abbrev Idx.swap {c n : ℕ} (t : Idx c n) : Idx c n :=
  ⟨t.a', t.j, t.a, t.i, by have := t.ha; omega, by have := t.h; omega⟩

def swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) :
    (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) →ₗ[K]
      (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) :=
  DirectSum.toModule K _ _ fun t =>
    ((-1 : ℤ) ^ (t.i * t.j)) •
      ((DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap).comp
        (TensorProduct.comm K ((P t.a).H t.i) ((Q t.a').H t.j)).toLinearMap)

theorem swapSum_lof (P Q : ℕ → Cx.{w} K) (c n : ℕ) (t : Idx c n) (u : (P t.a).H t.i) (v : (Q t.a').H t.j) :
    swapSum P Q c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t (u ⊗ₜ v)) =
      ((-1 : ℤ) ^ (t.i * t.j)) •
        DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap (v ⊗ₜ u) := by
  unfold swapSum
  rw [DirectSum.toModule_lof]
  rfl

theorem swapSum_swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) (z) :
    swapSum Q P c n (swapSum P Q c n z) = z := by
  have key : (swapSum Q P c n).comp (swapSum P Q c n) = LinearMap.id := by
    refine DirectSum.linearMap_ext K fun t => TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, swapSum_lof, map_zsmul]
    have hs : ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.swap.i * t.swap.j)) = 1 := by
      change ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.j * t.i)) = 1
      rw [Nat.mul_comm t.j t.i, ← mul_pow]
      simp
    refine (congrArg (fun w => ((-1 : ℤ) ^ (t.i * t.j)) • w) (swapSum_lof Q P c n t.swap v u)).trans ?_
    dsimp only
    rw [smul_smul, hs, one_smul]
  exact LinearMap.congr_fun key z

theorem kunE_swap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (h : KunE pr) :
    KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  intro c n
  obtain ⟨e, he⟩ := h c n
  let σ : (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) ≃ₗ[K]
      (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) :=
    LinearEquiv.ofLinear (swapSum Q P c n) (swapSum P Q c n)
      (LinearMap.ext fun z => swapSum_swapSum P Q c n z) (LinearMap.ext fun z => swapSum_swapSum Q P c n z)
  refine ⟨σ.trans e, fun t x y hx hy hz => ?_⟩
  have hz' : (T c).d n ((pr (show t.a' + t.a = c by have := t.ha; omega)).μ (show t.j + t.i = n by have := t.h; omega) y x) = 0 := by
    have e0 := (pr (show t.a' + t.a = c by have := t.ha; omega)).leib (show t.j + t.i = n by have := t.h; omega) y x
    rw [e0, hx, hy]
    simp
  have e1 := he t.swap y x hy hx hz'
  change e (swapSum Q P c n (DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t
    ((Q t.a).cls x hx ⊗ₜ (P t.a').cls y hy))) = _
  rw [swapSum_lof]
  change e.toLinearMap (((-1 : ℤ) ^ (t.i * t.j)) •
    DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t.swap
      ((P t.a').cls y hy ⊗ₜ (Q t.a).cls x hx)) = _
  rw [map_zsmul e.toLinearMap]
  refine (congrArg _ e1).trans ?_
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.Transfer

variable {K : Type} [Field K]

theorem exCls (C : Cx.{1} K) {n : ℕ} (c : C.H n) : ∃ (x : C.X n) (hx : C.d n x = 0), C.cls x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨x, hx, rfl⟩

theorem sub_mem_of_cls_eq {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : C.cls x hx = C.cls y hy) : x - y ∈ C.B n :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).1 h

theorem cls_eq_of_sub_mem {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : x - y ∈ C.B n) : C.cls x hx = C.cls y hy :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).2 h

theorem d_map_cocycle {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} {x : C.X n} (hx : C.d n x = 0) :
    D.d n (φ.f n x) = 0 := by
  rw [φ.comm, hx, map_zero]

theorem d_mu_cocycle {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y : B.X q}
    (hx : A.d p x = 0) (hy : B.d q y = 0) : M.d n (pr.μ h x y) = 0 := by
  rw [pr.leib, hx, hy]
  simp

theorem cls_mu_left {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x x' : A.X p} {y : B.X q}
    {hx : A.d p x = 0} {hx' : A.d p x' = 0} (hy : B.d q y = 0) {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x' y) = 0} (e : A.cls x hx = A.cls x' hx') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x' y) hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← LinearMap.sub_apply, ← map_sub]
  cases p with
  | zero =>
    have h0 : x - x' = 0 := hb
    rw [h0, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | succ p =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨pr.μ rfl w y, ?_⟩
    rw [pr.leib, hw, hy]
    simp

theorem cls_mu_right {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y y' : B.X q}
    (hx : A.d p x = 0) {hy : B.d q y = 0} {hy' : B.d q y' = 0} {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x y') = 0} (e : B.cls y hy = B.cls y' hy') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x y') hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← map_sub]
  cases q with
  | zero =>
    have h0 : y - y' = 0 := hb
    rw [h0, map_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨(-1 : ℤ) ^ p • pr.μ rfl x w, ?_⟩
    rw [map_zsmul, pr.leib, hw, hx]
    simp [smul_smul, ← mul_pow]

def sumCongr {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) : (⨁ i, A i) ≃ₗ[K] ⨁ i, B i :=
  DFinsupp.mapRange.linearEquiv e

theorem sumCongr_lof {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) (i : I) (x : A i) :
    sumCongr e (DirectSum.lof K I A i x) = DirectSum.lof K I B i (e i x) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (e i))

theorem kunE_iff : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  intro K _ P P' Q Q' T T' pr pr' p f g hp hf hg hc
  let eP : ∀ a n, (P a).H n ≃ₗ[K] (P' a).H n := fun a n => LinearEquiv.ofBijective ((p a).mapH n) (hp a n)
  let eQ : ∀ a n, (Q a).H n ≃ₗ[K] (Q' a).H n := fun a n => LinearEquiv.ofBijective ((f a).mapH n) (hf a n)
  let eT : ∀ a n, (T a).H n ≃ₗ[K] (T' a).H n := fun a n => LinearEquiv.ofBijective ((g a).mapH n) (hg a n)
  let eS : ∀ c n : ℕ, (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K]
      ⨁ t : Idx c n, (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j :=
    fun c n => sumCongr fun t => TensorProduct.congr (eP t.a t.i) (eQ t.a' t.j)
  have hS : ∀ (c n : ℕ) (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0)
      (hy : (Q t.a').d t.j y = 0),
      eS c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t
        ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
      DirectSum.lof K _ (fun t : Idx c n => (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j) t
        ((P' t.a).cls ((p t.a).f t.i x) (d_map_cocycle _ hx) ⊗ₜ (Q' t.a').cls ((f t.a').f t.j y) (d_map_cocycle _ hy)) := by
    intro c n t x y hx hy
    exact sumCongr_lof _ t _
  have hG : ∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j)
      (hz : (T c).d n ((pr ha).μ h x y) = 0) (hz' : (T' c).d n ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) = 0),
      eT c n ((T c).cls ((pr ha).μ h x y) hz) = (T' c).cls ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) hz' := by
    intro a a' c ha i j n h x y hz hz'
    have e0 := hc ha h x y
    change (T' c).cls ((g c).f n ((pr ha).μ h x y)) (d_map_cocycle _ hz) = _
    exact cls_eq_of_sub_mem (by rw [e0, sub_self]; exact zero_mem _)
  constructor
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨(eS c n).symm ≪≫ₗ e ≪≫ₗ eT c n, ?_⟩
    intro t x y hx hy hz
    obtain ⟨x0, hx0, e1⟩ := exCls (P t.a) ((eP t.a t.i).symm ((P' t.a).cls x hx))
    obtain ⟨y0, hy0, e2⟩ := exCls (Q t.a') ((eQ t.a' t.j).symm ((Q' t.a').cls y hy))
    have e1' : (P' t.a).cls ((p t.a).f t.i x0) (d_map_cocycle _ hx0) = (P' t.a).cls x hx := by
      have := congrArg (eP t.a t.i) e1
      rwa [LinearEquiv.apply_symm_apply] at this
    have e2' : (Q' t.a').cls ((f t.a').f t.j y0) (d_map_cocycle _ hy0) = (Q' t.a').cls y hy := by
      have := congrArg (eQ t.a' t.j) e2
      rwa [LinearEquiv.apply_symm_apply] at this
    have hS' := hS c n t x0 y0 hx0 hy0
    rw [e1', e2'] at hS'
    have hz0 := d_mu_cocycle (pr t.ha) t.h hx0 hy0
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx0) (d_map_cocycle (f t.a') hy0)
    have hz2 := d_mu_cocycle (pr' t.ha) t.h hx (d_map_cocycle (f t.a') hy0)
    simp only [LinearEquiv.trans_apply]
    rw [← hS', LinearEquiv.symm_apply_apply, he t x0 y0 hx0 hy0 hz0, hG t.ha t.h x0 y0 hz0 hz1,
      cls_mu_left (pr' t.ha) t.h (d_map_cocycle (f t.a') hy0) (hz' := hz2) e1',
      cls_mu_right (pr' t.ha) t.h hx (hz' := hz) e2']
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨eS c n ≪≫ₗ e ≪≫ₗ (eT c n).symm, ?_⟩
    intro t x y hx hy hz
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx) (d_map_cocycle (f t.a') hy)
    simp only [LinearEquiv.trans_apply]
    rw [hS c n t x y hx hy, he t _ _ _ _ hz1, ← hG t.ha t.h x y hz hz1, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.KunGlue.Transfer
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem row_iso_of_columns : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  intro R _ K a hK j
  have hab : ∀ p q, a < q → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_gt h)
  have hbe : ∀ p q, q < a → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_lt h)
  have hs := GlobalTheory.T.double_complex_class_surjective K a j hab
  have hk := GlobalTheory.T.double_complex_lead_zero_of_class_zero K a j hab
  have hi := GlobalTheory.T.double_complex_class_zero_of_lead_zero K a j hbe
  have hl := GlobalTheory.T.double_complex_lead_surjective K a j hbe
  let c := clsZ K (a + j) j
  let ψ : Zf K (a + j) j →ₗ[R] (colH K a).H j := leadE K j a
  have hle : LinearMap.ker c ≤ LinearMap.ker ψ := fun z hz => hk z hz
  let L := (LinearMap.ker c).liftQ ψ hle
  have hL : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun x hx => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      have hz : ψ z = 0 := by simpa [L] using hx
      have hc : c z = 0 := hi z hz
      exact (Submodule.Quotient.mk_eq_zero _).2 hc
    · intro y
      obtain ⟨z, rfl⟩ := hl y
      exact ⟨Submodule.Quotient.mk z, Submodule.liftQ_apply _ _ _⟩
  let e0 := c.quotKerEquivOfSurjective hs
  refine ⟨e0.symm.trans (LinearEquiv.ofBijective L hL), fun z => ?_⟩
  have h0 : e0.symm (c z) = Submodule.Quotient.mk z :=
    e0.symm_apply_eq.2 (LinearMap.quotKerEquivOfSurjective_apply_mk c hs z).symm
  change L (e0.symm (c z)) = ψ z
  rw [h0]
  exact Submodule.liftQ_apply _ _ _

end GlobalTheory.CompanionTheory.CechSerre
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_map_surjective_ker {l : ℕ} [Fact l.Prime] (A : PAlg l) :
    Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  constructor
  · intro y
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, A.sharpMap_coeff x⟩
  · ext a
    rw [RingHom.mem_ker]
    constructor
    · intro h
      rw [A.sharpMap_eq, Ideal.Quotient.eq_zero_iff_mem, pow_one] at h
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
      have h0 : A.th (WittVector.teichmuller l a - y * (l : A.W)) = 0 := by
        rw [map_sub, map_mul, map_natCast]
        exact sub_eq_zero.2 hu.symm
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
      have h1 := congrArg (WittVector.constantCoeff : A.W →+* A.A) hc
      rw [map_mul, map_sub, map_mul, map_natCast, A.natCast_l, mul_zero, sub_zero,
        WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, A.xi_coeff_zero] at h1
      exact Ideal.mem_span_singleton'.2 ⟨-c.coeff 0, by rw [← h1, neg_mul, mul_neg]⟩
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      rw [map_mul, A.sharpMap_eq A.pi, A.sharp_pi,
        Ideal.Quotient.eq_zero_iff_mem.2 (by
          rw [pow_one]; exact Ideal.mem_span_singleton_self _), mul_zero]

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.noether_normalization_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), letI := (strV q V).toAlgebra; ∀ a, IsIntegral (torusS K (fun k => (ht k).unit) S) (evV i (yS y S) V hS a) := by
  first | exact @GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | exact GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS | (intros; apply GlobalTheory.CompanionTheory.GeoInteg.isIntegral_torusS <;> assumption)
end
