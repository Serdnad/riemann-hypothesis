module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle005
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private theorem isDec_surj {A : Test l} {S : Fam A} (h : IsDec S) (i : S.ι) :
    Function.Surjective (PAlg.Hom.f (S.f i).hom) := by
  classical
  intro b
  obtain ⟨a, ha⟩ := h.2 (Pi.single i b)
  exact ⟨a, by simpa using congrFun ha i⟩

private theorem exists_idem {A : Test l} {S : Fam A} (h : IsDec S) :
    ∃ e : S.ι → A.obj.A, CompleteOrthogonalIdempotents e ∧
      (∀ i, PAlg.Hom.f (S.f i).hom (e i) = 1) ∧
      ∀ i a, PAlg.Hom.f (S.f i).hom a = 0 → a * e i = 0 := by
  classical
  choose e he using fun i => h.2 (Pi.single i (1 : (S.B i).obj.A))
  have hv : ∀ i j, PAlg.Hom.f (S.f j).hom (e i) = (Pi.single i 1 : ∀ k, (S.B k).obj.A) j :=
    fun i j => congrFun (he i) j
  have ext' : ∀ x y : A.obj.A, (∀ j, PAlg.Hom.f (S.f j).hom x = PAlg.Hom.f (S.f j).hom y) → x = y :=
    fun x y hxy => h.1 (funext hxy)
  have hsame : ∀ i, PAlg.Hom.f (S.f i).hom (e i) = 1 := fun i => by rw [hv, Pi.single_eq_same]
  have hne : ∀ i j, j ≠ i → PAlg.Hom.f (S.f j).hom (e i) = 0 := fun i j hji => by
    rw [hv, Pi.single_eq_of_ne hji]
  refine ⟨e, ⟨⟨?_, ?_⟩, ?_⟩, hsame, ?_⟩
  · intro i
    refine ext' _ _ fun j => ?_
    rw [map_mul]
    by_cases hji : j = i
    · subst hji; rw [hsame, one_mul]
    · rw [hne i j hji, zero_mul]
  · intro i i' hii
    refine ext' _ _ fun j => ?_
    rw [map_mul, map_zero]
    by_cases hji : j = i
    · subst hji; rw [hne i' j hii, mul_zero]
    · rw [hne i j hji, zero_mul]
  · refine ext' _ _ fun j => ?_

    rw [map_sum, map_one, Finset.sum_eq_single j, hsame]
    · intro i _ hij
      exact hne i j hij.symm
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i a ha
    refine ext' _ _ fun j => ?_
    rw [map_mul, map_zero]
    by_cases hji : j = i
    · subst hji; rw [ha, zero_mul]
    · rw [hne i j hji, mul_zero]

private theorem pullback_decomposition {A A' : Test l} (φ : A ⟶ A') (S : Fam A) (h : IsDec S) :
    ∃ (B' : S.ι → Test l) (f' : ∀ i, A' ⟶ B' i) (ψ : ∀ i, S.B i ⟶ B' i),
      IsDec (⟨S.ι, B', f'⟩ : Fam A') ∧ ∀ i, S.f i ≫ ψ i = φ ≫ f' i := by
  obtain ⟨e, he, h1, h0⟩ := exists_idem h
  obtain ⟨B', f', hd, hf⟩ := decEx l A' S.ι (fun i => PAlg.Hom.f φ.hom (e i))
    (he.map (PAlg.Hom.f φ.hom))
  have key : ∀ i, RingHom.ker (PAlg.Hom.f (S.f i).hom) ≤
      RingHom.ker ((PAlg.Hom.f (f' i).hom).comp (PAlg.Hom.f φ.hom)) := by
    intro i a ha
    have ha0 : a * e i = 0 := h0 i a ha
    have h2 : PAlg.Hom.f (f' i).hom (PAlg.Hom.f φ.hom a) * 1 = 0 := by
      have h3 := hf i
      rw [← h3, ← map_mul, ← map_mul, ha0, map_zero, map_zero]
    simpa [RingHom.mem_ker] using h2
  let g : ∀ i, (S.B i).obj.A →+* (B' i).obj.A := fun i =>
    (PAlg.Hom.f (S.f i).hom).liftOfRightInverse (Function.surjInv (isDec_surj h i))
      (Function.rightInverse_surjInv _) ⟨_, key i⟩
  have hg : ∀ i a, g i (PAlg.Hom.f (S.f i).hom a) = PAlg.Hom.f (f' i).hom (PAlg.Hom.f φ.hom a) :=
    fun i a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hcomm : ∀ i, (g i).comp (S.B i).obj.s = (B' i).obj.s := by
    intro i
    refine RingHom.ext fun x => ?_
    have c1 : PAlg.Hom.f (S.f i).hom (A.obj.s x) = (S.B i).obj.s x :=
      RingHom.congr_fun (PAlg.Hom.comm (S.f i).hom) x
    have c2 : PAlg.Hom.f φ.hom (A.obj.s x) = A'.obj.s x :=
      RingHom.congr_fun (PAlg.Hom.comm φ.hom) x
    have c3 : PAlg.Hom.f (f' i).hom (A'.obj.s x) = (B' i).obj.s x :=
      RingHom.congr_fun (PAlg.Hom.comm (f' i).hom) x
    rw [RingHom.comp_apply, ← c1, hg, c2, c3]
  refine ⟨B', f', fun i => ObjectProperty.homMk (⟨g i, hcomm i⟩ : PAlg.Hom _ _), hd, fun i => ?_⟩
  apply ObjectProperty.hom_ext
  apply PAlg.Hom.ext
  exact RingHom.ext fun a => hg i a

theorem partsEx :
    UpperTheory.Ru.crystallineComparison.PartsEx := by
  intro l _
  refine ⟨{ Cov := fun S => IsDec S, triv := ?_, pull := ?_, trans := ?_, epi := ?_, disj := ?_ },
    fun _ _ => Iff.rfl⟩
  · intro A
    constructor
    · intro a b hab
      exact congrFun hab ()
    · intro b
      exact ⟨b (), funext fun _ => rfl⟩
  · intro A A' φ S h
    exact pullback_decomposition φ S h
  · intro A S T hS hT
    constructor
    · intro a b hab
      refine hS.1 (funext fun i => (hT i).1 (funext fun j => ?_))
      exact congrFun hab ⟨i, j⟩
    · intro c
      choose b hb using fun i => (hT i).2 (fun j => c ⟨i, j⟩)
      obtain ⟨a, ha⟩ := hS.2 b
      refine ⟨a, funext fun x => ?_⟩
      obtain ⟨i, j⟩ := x
      have h1 : PAlg.Hom.f (S.f i).hom a = b i := congrFun ha i
      have h2 := congrFun (hb i) j
      simp only at h2
      rw [← h1] at h2
      exact h2
  · intro A S h i
    refine ⟨fun {X} u v huv => ?_⟩
    apply ObjectProperty.hom_ext
    apply PAlg.Hom.ext
    refine RingHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := isDec_surj h i b
    have := congrArg (fun w => PAlg.Hom.f w.hom a) huv
    exact this
  · intro A S h i j hij X u v huv
    classical
    obtain ⟨a, ha⟩ := h.2 (Pi.single i 1)
    have hi : PAlg.Hom.f (S.f i).hom a = 1 := by
      have := congrFun ha i
      simpa using this
    have hj : PAlg.Hom.f (S.f j).hom a = 0 := by
      have := congrFun ha j
      simpa [Pi.single_eq_of_ne hij.symm] using this
    have h10 : (1 : X.obj.A) = 0 := by
      have h3 : PAlg.Hom.f u.hom (PAlg.Hom.f (S.f i).hom a) = PAlg.Hom.f v.hom (PAlg.Hom.f (S.f j).hom a) :=
        congrArg (fun w => PAlg.Hom.f w.hom a) huv
      rw [hi, hj, map_one, map_zero] at h3
      exact h3
    have hs : Subsingleton X.obj.A := subsingleton_of_zero_eq_one h10.symm
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro b
      exact ⟨0, funext fun e => e.elim⟩

end UpperTheory.Ru.crystallineComparison
end
end

section


set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}


variable (l) in
def tA : Acris l := ACris.periodT (untilt_epsilon (p := l))


variable (l) in
def phiA : Acris l →+* Acris l := ACris.phi (K := ℂ_[l]) (p := l)

def galA (g : K.fixingSubgroup) : Acris l →+* Acris l := ACris.galCris (IntermediateField.fixingSubgroupEquiv K g)


variable (l) in
def zA : ℤ_[l] →+* Acris l := (algebraMap (Ainf l) (Acris l)).comp (IsPerfectoidField.padicIntToWitt l)

structure PBg (l : ℕ) [Fact l.Prime] {A Γ : Type} [CommRing A] (t : A) (φA : A →+* A) (σA : Γ → (A →+* A)) (z : ℤ_[l] →+* A) : Type 1 where
  C : Type
  [ring : CommRing C]
  [alg : Algebra ℚ_[l] C]
  c : A →+* C
  φ : C →ₐ[ℚ_[l]] C
  σ : Γ → (C →ₐ[ℚ_[l]] C)
  t_unit : IsUnit (c t)
  loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a
  ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0
  φ_c : ∀ a, φ (c a) = c (φA a)
  σ_c : ∀ g a, σ g (c a) = c (σA g a)
  z_c : ∀ x : ℤ_[l], algebraMap ℚ_[l] C x = c (z x)

attribute [instance] PBg.ring PBg.alg


variable (l K) in
abbrev PB : Type 1 := PBg l (tA l) (phiA l) (galA (K := K)) (zA l)

variable (B : PB l K)

def IsInv (M : Model l K) (j : ℕ) (x : M.V j ⊗[ℚ_[l]] B.C) : Prop :=
  ∀ g : K.fixingSubgroup, TensorProduct.map (M.act j g) (B.σ g).toLinearMap x = x

def vec (M : Model l K) (j r : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) : M.V j ⊗[ℚ_[l]] B.C :=
  ∑ k, M.toV j (v k) ⊗ₜ (B.c (c k) * Ring.inverse (B.c (tA l)) ^ r)

def evE (e : E.EtFam l K) (M : Model l K) (j n : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) : M.MH n j :=
  ∑ k, c k • e M n j ((v k).lev n)

def InjE (e : E.EtFam l K) (M : Model l K) (j : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (u : ℕ), (∀ n, tA l ^ u • evE e M j n v c = 0) → vec B M j 0 v c = 0

def AbsInv (e : E.EtFam l K) (M : Model l K) (j f : ℕ) (ϖ : OK l K) : Prop :=
  ∃ (m N : ℕ) (g : OK l K →+* Qo l) (F : PQ M.p g ⟶ PQ M.p g) (ρ : M.P ⟶ PQ M.p g), g ϖ = 0 ∧ (∀ x, g x ^ l ^ f = g x) ∧ IsFr f F ∧ IsRd m ρ ∧
    ∀ (ι : Type) [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), IsInv B M j (vec B M j r v c) →
      ∃ (a u : ℕ) (x : ∀ n, MH (PQ M.p g) n j), ∀ n, (phiH _ n j)^[f] (x n) = pullH F n j (x n) ∧
        ((l : Acris l) ^ a * tA l ^ u) • evE e M j n v (fun k => (phiA l)^[f * N] (c k)) = tA l ^ (u + r) • pullH ρ n j (x n)

def IsHk (M : Model l K) (T : Corr l M.X) (hr : T.r ≫ M.p = T.p ≫ M.p) (j : ℕ) (A : M.V j →ₗ[ℚ_[l]] M.V j) : Prop :=
  ∀ (W : Model l K) (w : W.X ⟶ M.X) (hw : w ≫ M.p = W.p) (z : Fin T.d → (W.X ⟶ T.Z)) (hz : ∀ i, z i ≫ T.p = w),
    (∀ (X : Scheme.{0}) (y : X ⟶ W.X), IsUnit (l : Γ(X, ⊤)) → SplitOn T.p (y ≫ w) fun i => y ≫ z i) →
    ∀ v, Model.pullV w hw j (A v) =
      ∑ i, Model.pullV (z i ≫ T.r) (by rw [Category.assoc, hr, ← Category.assoc, hz, hw]) j v

def SiteAnn : Prop := ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (Y : Scheme.{0}) (q : Y ⟶ Spec (CommRingCat.of O)) (g : O →+* Qo l)
  (Q P : PAlg l ⥤ Type) (ρ : P ⟶ PQ q g) (F : PQ q g ⟶ PQ q g) (f : ℕ) (I : Type) [Fintype I] (a : I → ℤ) (t : I → (Q ⟶ P)) (k : I → ℕ),
  (TZero a fun i => t i ≫ ρ ≫ itE F (k i)) → ∀ (n j : ℕ) (x : MH (PQ q g) n j), (phiH _ n j)^[f] x = pullH F n j x →
  ∑ i, a i • pullH (t i) n j ((phiH P n j)^[f * k i] (pullH ρ n j x)) = 0

def VecZero : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (B : PB l K) (e : E.EtFam l K), e.Good →
  ∀ (M : Model l K) (j : ℕ) (ι : Type) [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), vec B M j r v c = 0 →
  ∃ a u : ℕ, ∀ n, ((l : Acris l) ^ a * tA l ^ u) • evE e M j n v c = 0

def Top : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)]
  (ϖ : OK l K), Irreducible ϖ → ∀ (e : E.EtFam l K), e.Good → ∀ (M : Model l K), Smooth M.p → QuasiCompact M.p → AffFin M.X →
  ∀ (f n j : ℕ), 0 < f → ∀ (T : Fin (n + 1) → Corr l M.X) (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B : PB l K, InjE B e M j → AbsInv B e M j f ϖ →
  ∃ N : ℕ, ∀ x, IsInv B M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) • TensorProduct.map (A i) (B.φ.toLinearMap ^ (f * (n - i + N))) x = 0

end UpperTheory.Ru.crystallineComparison
end
end
