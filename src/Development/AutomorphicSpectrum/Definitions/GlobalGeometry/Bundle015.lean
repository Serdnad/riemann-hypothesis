module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import GroundTheory.FunctionField.PlaceDefs
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Top

def IsFFCurve (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K]
    (C : ACurve K) : Prop :=
  ∃ e : C.I ≃ GroundTheory.FunctionField.Place k K, ∀ i, C.v i = (e i).valuation ∧ C.w i = (e i).deg

def segre {B Ω : Type} [Fintype B] [CommRing Ω] {J : B → Type} (y : (Σ k, J k) → Ω) : ((k : B) → J k) → Ω :=
  fun c => ∏ k, y ⟨k, c k⟩

structure DRTie {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (j p : ℕ) {E : Type} [Field E] [NumberField E]
    [IsCMField E] (H : Host E) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of M.Ω) ⟶ X
  tie : CoordTie ℤ ξ (segre M.y)

  t : SAB H X
  pow : PowFns t
  fib : ∀ q : Cpt ξ, InFibre ξ p q → FibPF t q.1

  V : Type
  [acg : AddCommGroup V]
  [mod : Module M.Ω V]

  L : LieModel t.G ξ V

  r : 𝓞 E →+* Module.End M.Ω V
  act : L.IsActOf t.act.act r

  σ : Ψ ⊕ Ψ → (𝓞 E →+* M.Ω)
  σ_inj : Function.Injective σ
  card : 2 * Fintype.card Ψ = Module.finrank ℚ E
  conj : ∀ τ a, σ (Sum.inr τ) a = σ (Sum.inl τ) (H.bar a)
  reg : ∀ q : Cpt ξ, InFibre ξ p q → ∀ s a, σ s a ∈ regAt ξ q
  unram : ¬ (p : ℤ) ∣ NumberField.discr E

  b₁ : Ψ → Fin j → V

  b₂ : Ψ → Fin (N - j) → V
  ind₁ : ∀ τ, LinearIndependent M.Ω (b₁ τ) ∧ Submodule.span M.Ω (Set.range (b₁ τ)) = eigSp r (σ (Sum.inl τ))
  ind₂ : ∀ τ, LinearIndependent M.Ω (b₂ τ) ∧ Submodule.span M.Ω (Set.range (b₂ τ)) = eigSp r (σ (Sum.inr τ))
  flag₁ : ∀ τ, (L.eigLat r (σ (Sum.inl τ))).IsFlagVBOn {q | InFibre ξ p q} (b₁ τ)
  flag₂ : ∀ τ, (L.eigLat r (σ (Sum.inr τ))).IsFlagVBOn {q | InFibre ξ p q} (b₂ τ)
  deg₁ : ∀ τ (i : Fin N) (h : (i : ℕ) < j), ∃ e₀ : M.Ω,
    ((L.eigLat r (σ (Sum.inl τ))).gr (b₁ τ) ⟨i, h⟩).IsDegOn {q | InFibre ξ p q} M.y (M.xdeg (τ, i)) e₀
  deg₂ : ∀ τ (i : Fin N) (h : N - 1 - (i : ℕ) < N - j), j ≤ (i : ℕ) → ∃ e₀ : M.Ω,
    ((L.eigLat r (σ (Sum.inr τ))).gr (b₂ τ) ⟨N - 1 - i, h⟩).IsDegOn {q | InFibre ξ p q} M.y (-M.xdeg (τ, i)) e₀

attribute [instance] DRTie.acg DRTie.mod

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.Test

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Frames

variable {S : Scheme.{0}} {R : Type} [CommRing R] {O : Type} [CommRing O]

theorem lieMult_iff_exists_frame {k : Type} [Field k] {G : Over S} [GrpObj G] (act : OAct O G) (t : Sp k ⟶ S)
    (τ : O →+* k) (n : ℕ) : LieMult act t τ n ↔ ∃ v : Fin n → (epsAt t ⟶ G), IsEigFrame act t τ v := Iff.rfl

variable {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {V : Type} [AddCommGroup V] [Module R V]

theorem pt_zero (M : LieModel G x V) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_sum (M : LieModel G x V) {n : ℕ} (e : Fin n → V) :
    M.pt (∑ i, e i) = (List.ofFn fun i => M.pt (e i)).prod := by
  induction n with
  | zero => simp [pt_zero]
  | succ n ih => rw [Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]

theorem isComb_iff (M : LieModel G x V) {n : ℕ} (c : Fin n → R) (e : Fin n → V) (w : V) :
    IsComb c (fun i => M.pt (e i)) (M.pt w) ↔ w = ∑ i, c i • e i := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have : u = fun i => M.pt (c i • e i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [this, ← pt_sum] at hw
    exact M.inj hw
  · rintro rfl
    exact ⟨fun i => M.pt (c i • e i), fun i => M.smul _ _, pt_sum M _⟩

theorem isEigVec_iff (M : LieModel G x V) (act : OAct O G) (ρ : O →+* Module.End R V) (h : M.IsActOf act.act ρ)
    (τ : O →+* R) (e : V) : IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  simp only [IsEigVec, M.tan, true_and, eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  rw [← h a e]
  constructor
  · intro H
    exact M.inj (Over.OverMorphism.ext (H.trans (M.smul _ _).symm))
  · intro H
    rw [H]; exact M.smul _ _

theorem isEigFrame_iff (M : LieModel G x V) (act : OAct O G) (ρ : O →+* Module.End R V) (h : M.IsActOf act.act ρ)
    (τ : O →+* R) {n : ℕ} (e : Fin n → V) : IsEigFrame act x τ (fun i => M.pt (e i)) ↔
      LinearIndependent R e ∧ Submodule.span R (Set.range e) = eigSp ρ τ := by
  simp only [IsEigFrame, isEigVec_iff M act ρ h]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc => ?_, le_antisymm ?_ fun w hw => ?_⟩
    · obtain ⟨c0, -, hu⟩ := h2 (M.pt 0) ((isEigVec_iff M act ρ h τ 0).2 (Submodule.zero_mem _))
      have a := hu c ((isComb_iff M c e 0).2 hc.symm)
      have b := hu 0 ((isComb_iff M 0 e 0).2 (by simp))
      exact fun i => congrFun (a.trans b.symm) i
    · rintro _ hw
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h1 i) hw
    · obtain ⟨c, hc, -⟩ := h2 (M.pt w) ((isEigVec_iff M act ρ h τ w).2 hw)
      rw [(isComb_iff M c e w).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h2 ▸ Submodule.subset_span ⟨i, rfl⟩, fun w hw => ?_⟩
    obtain ⟨w, rfl⟩ := M.onto w hw.1
    have hw' := (isEigVec_iff M act ρ h τ w).1 hw
    rw [← h2, Submodule.mem_span_range_iff_exists_fun] at hw'
    obtain ⟨c, hc⟩ := hw'
    refine ⟨c, (isComb_iff M c e w).2 hc.symm, fun d hd => ?_⟩
    have hd' := (isComb_iff M d e w).1 hd
    have := Fintype.linearIndependent_iff.1 h1 (d - c) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hc, ← hd', sub_self])
    exact funext fun i => sub_eq_zero.1 (this i)


open GlobalTheory.Diag in
def torusModel (x : Sp R ⟶ S) (X : Type) [AddCommGroup X] : LieModel (splitTorus S X) x (X →+ R) where
  pt c := epsVec _ c
  tan c := (reduces_iff (by rw [← Category.assoc, fstHom_base, Category.id_comp]) _).2
    ((exists_epsVec_iff _).1 ⟨c, rfl⟩)
  inj := epsVec_injective
  onto v hv := (exists_epsVec_iff _).2
    ((reduces_iff (by rw [← Category.assoc, fstHom_base, Category.id_comp]) _).1 hv)
  add := epsVec_add
  smul a c := (left_eq_epsScaleR_iff a (by rw [← Category.assoc, ← epsScaleR_base]) c _).2 rfl

end Frames

section Gram

end Gram

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem trace_basis_mul_sesq (D : Datum H) (x y : D.La) (j) :
    Algebra.trace ℚ E ((RingOfIntegers.basis E j : E) * sesq D x y) = D.EF (RingOfIntegers.basis E j • x) y := by
  classical
  have key : ∀ k, Algebra.trace ℚ E ((RingOfIntegers.basis E j : E) * HT.dualInt E k) = if j = k then 1 else 0 := by
    intro k
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E) (traceForm_nondegenerate ℚ E)
      (integralBasis E) k j
    rw [Algebra.traceForm_apply, integralBasis_apply, mul_comm] at this
    convert this
    unfold HT.dualInt
    congr!

  simp only [sesq, Finset.mul_sum, map_sum]
  have : ∀ k, Algebra.trace ℚ E ((RingOfIntegers.basis E j : E) *
      ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k)) =
      (D.EF (RingOfIntegers.basis E k • x) y : ℚ) * if j = k then 1 else 0 := by
    intro k
    rw [mul_left_comm, ← zsmul_eq_mul, map_zsmul, key, zsmul_eq_mul]
  simp [this]

theorem trace_mul_sesq (D : Datum H) (x y : D.La) (a : 𝓞 E) :
    Algebra.trace ℚ E ((a : E) * sesq D x y) = D.EF (a • x) y := by
  have h : a ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by simp
  induction h using Submodule.span_induction with
  | mem b hb => obtain ⟨j, rfl⟩ := hb; exact trace_basis_mul_sesq D x y j
  | zero => simp
  | add b c _ _ hb hc => simp [add_mul, add_smul, hb, hc]
  | smul m b _ hb =>
    have e : ((m • b : 𝓞 E) : E) * sesq D x y = m • ((b : E) * sesq D x y) := by
      simp only [zsmul_eq_mul, ← _root_.mul_assoc]; simp
    rw [e, map_zsmul, hb, smul_assoc]; simp

theorem eq_of_trace {s t : E} (h : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * s) = Algebra.trace ℚ E ((a : E) * t)) :
    s = t := by
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun z => ?_
  have : (Algebra.traceForm ℚ E) (s - t) = 0 := (integralBasis E).ext fun k => by
    rw [Algebra.traceForm_apply, integralBasis_apply, sub_mul, map_sub, mul_comm s, mul_comm t]
    exact sub_eq_zero.2 (h _)
  simp [this]

theorem sesq_smul_left (D : Datum H) (c : 𝓞 E) (x y : D.La) : sesq D (c • x) y = c * sesq D x y :=
  eq_of_trace fun a => by
    rw [trace_mul_sesq, ← _root_.mul_assoc, ← mul_smul, ← trace_mul_sesq]; simp

theorem sesq_smul_right (D : Datum H) (c : 𝓞 E) (x y : D.La) : sesq D x (H.bar c • y) = c * sesq D x y :=
  eq_of_trace fun a => by
    rw [trace_mul_sesq, ← D.adj, ← mul_smul, ← trace_mul_sesq, ← _root_.mul_assoc, mul_comm (a : E)]; simp


end Form

end GlobalTheory.CompanionTheory.Ar.Fl.Test
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω]

def stdLat (A : Subring Ω) {d : ℕ} (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)) :
    Submodule A ((Fin d → Ω) × (Fin d → Ω)) :=
  Submodule.span A {y | ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ y = T y₀}

structure GermSys (t : SAB H X) (ξ : Spec (CommRingCat.of Ω) ⟶ X) {d : ℕ} (M : LieModel t.G ξ (Fin d → Ω)) where

  g₀ : GermAt t ξ d
  dir₀ : ∀ l, (M.pt (Pi.single l 1)).left = g₀.tg l
  act₀ : ∀ a v, M.pt ((rho g₀.B a).mulVec v) = M.pt v ≫ t.act.act a

  g : ∀ p : Cpt ξ, GermAt t (S := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) d

  BK : Cpt ξ → Germ.FB Ω d (𝓞 E)
  mapK : ∀ p, IsMapOf (genMap ξ p) (g p).B (BK p)

  φ : Cpt ξ → Germ.Pt Ω 1 d

  ψ : Cpt ξ → Germ.Pt Ω 1 d

  lam : Cpt ξ → Germ.PS Ω 2 d
  iso : ∀ p, IsIso g₀.B (BK p) (φ p) (ψ p) (lam p)
  dir : ∀ p l, (M.pt ((lin (φ p) 1).mulVec (Pi.single l 1))).left =
    Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ (g p).tg l
  gen : ∀ (p q : Cpt ξ) (h : q.1 ⤳ p.1), ∃ (B' : Germ.FB (X.presheaf.stalk q.1) d (𝓞 E))
    (φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d) (lam' : Germ.PS (X.presheaf.stalk q.1) 2 d),
    IsMapOf (X.presheaf.stalkSpecializes h).hom (g p).B B' ∧ IsIso (g q).B B' φ' ψ' lam' ∧
      transH (φ p) (ψ p) (lam p) = transH (φ q) (ψ q) (lam q) ∘ₗ
        transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
          (MvPowerSeries.map (genMap ξ q) lam')
  loc : ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
    stdLat (regAt ξ q) (transH (φ p) (ψ p) (lam p)) = stdLat (regAt ξ q) (transH (φ q) (ψ q) (lam q))

def HFree {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (r : ℕ) : Prop :=
  ∃ x : Fin r → (Fin d → R) × (Fin d → R),
    LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def HChar {R : Type} [CommRing R] [Nontrivial R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (r : ℕ) : Prop :=
  ∀ a : 𝓞 E, (rhoH B a).charpoly =
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom R)) ^ r

def GermSys.Gives {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {r : ℕ} (𝓗 : HodgeLat M.lat ρ H.bar r) : Prop :=
  (∀ a y, 𝓗.ρH a (y.1, dotProductBilin Ω Ω y.2) =
    ((rhoH S.g₀.B a y).1, dotProductBilin Ω Ω (rhoH S.g₀.B a y).2)) ∧
  ∀ (p : Cpt ξ) (y : (Fin d → Ω) × (Fin d → Ω)), (y.1, dotProductBilin Ω Ω y.2) ∈ 𝓗.HL p ↔
    y ∈ stdLat (regAt ξ p) (transH (S.φ p) (S.ψ p) (S.lam p))

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def FibreLatVec {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) {A₀ : Type} (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) : Prop :=
  ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ t.G.left) (u : HolUnif A (t.PP.L.pull φ) g) (χ : u.Λ → ℂ),
    IsGrpPullback A t.G z φ ∧ u.IsAH R.Hm χ ∧
    (∀ a p, (u.ex (R.B a p)).left ≫ φ = (u.ex p).left ≫ φ ≫ (t.act.act a).left) ∧
    Function.Injective R.P ∧ (∀ p, p ∈ u.Λ ↔ p ∈ Set.range R.P) ∧
    ∀ i, ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ = (v i).left ∧ u.IsDiff (x i) v'

def FibreLat {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : RiemLat E g Λ) : Prop :=
  FibreLatVec t z R (A₀ := Empty) (fun i => i.elim) fun i => i.elim

def AbPart.IsCochars {S : Scheme.{0}} {t : SAB H S} {K : Type} [Field K] {z : Sp K ⟶ S} (P : AbPart t z) {V : Type}
    [AddCommGroup V] [Module K V] (MV : LieModel P.tK.G (𝟙 (Sp K)) V) (I : AddSubgroup V) : Prop :=
  letI := P.τ.addCommGroup
  ∃ MT : LieModel (splitTorus (Sp K) P.τ.X) (𝟙 _) (P.τ.X →+ K), IsCocharLie MT ∧
    ∀ x, x ∈ I ↔ ∃ δ : P.τ.X →+ ℤ, MV.pt x = MT.pt ((Int.castAddHom K).comp δ) ≫ P.τ.i

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

namespace HodgeCpt

variable {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

def LabVal {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ 𝔐.X) {A₀ : Type} (lab : A₀ → CMType H ⊕ CMType H)
    (σ : A₀ → (𝓞 E →+* R)) : Prop :=
  ∀ i a, ValAt 𝔐.ξ z (𝔐.emb (lab i) a) (σ i a)

def IsCuspWeight (sm : CMType H → CMType H ⊕ CMType H) (U : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Sp ℂ ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
    ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (σ : CMType H → (𝓞 E →+* ℂ)),
      FibreLat 𝔐.t z R ∧ 𝔐.LabVal z sm σ ∧ U w = R.cuspW σ

def GeoPhi (sm : CMType H → CMType H ⊕ CMType H) (z : Sp ℂ ⟶ 𝔐.X) {m : ℕ} (b : CMType H → Fin m → 𝔐.Li) (ν : ℝ) : Prop :=
  ∃ (P : AbPart 𝔐.t z) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (MV : LieModel P.tK.G (𝟙 (Sp ℂ)) V)
    (ρ : 𝓞 E →+* Module.End ℂ V) (I : AddSubgroup V) (hb : V → V → ℂ) (σ : CMType H → (𝓞 E →+* ℂ))
    (bz : CMType H → Fin m → V),
    MV.IsActOf P.tK.act.act ρ ∧ P.IsCochars MV I ∧ 𝔐.LabVal z sm σ ∧
    (∀ x x', HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (MV.pt x ≫ P.τ.q ≫ P.e.hom) (MV.pt x' ≫ P.τ.q ≫ P.e.hom) (hb x x')) ∧
    (∀ τ k, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (b τ k) v ∧ (MV.pt (bz τ k)).left ≫ P.m.φ = v.left) ∧
    PhiNormSq ρ hb I (4 * Real.pi)⁻¹ σ bz ν

def VS (S' : Finset ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := Lat.patch S' (𝔐.dR s) fun p => 𝔐.HT p s

def withS (S' : Finset ℕ) (hp : ∀ p ∈ S', p.Prime) (hR : ∀ p ∈ S', 4 ≤ 𝔐.R p)
    (ht : ∀ p ∈ S', FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) (hvb : ∀ s, (𝔐.VS S' s).IsVB (labelRk D s) (𝔐.Vgen s)) :
    HodgeCpt Y S' y :=
  { 𝔐 with S_prime := hp, R_ge := hR, tors := ht, vb := hvb }

variable {L : Type} [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]

def FibLat (Vl : Lat 𝔐.ξ 𝔐.Li) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z))
    (MV : LieModel P.tK.G (𝟙 (Sp L)) V) : Submodule (𝓞 L) V :=
  ⨅ 𝔭 : PrimeSpectrum (𝓞 L), Submodule.span (𝓞 L) {x | ∃ s ∉ 𝔭.asIdeal, s • x ∈ Submodule.span (𝓞 L)
    {x' | ∃ e ∈ Vl ⟨z 𝔭, 𝔐.all _⟩, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ 𝔐.t.G,
      𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (MV.pt x').left ≫ P.m.φ = v.left}}

def IsLinPtOf [IsScalarTower (𝓞 L) L V] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z))
    (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) : Prop :=
  MV.IsActOf P.tK.act.act A.ρ ∧ 𝔐.LabVal (spMap (algebraMap (𝓞 L) L) ≫ z) id A.σ ∧
    (∀ x, x ∈ A.Λ ↔ ∃ v : epsAt z ⟶ 𝔐.t.G, IsTanAt 𝔐.t.G z v ∧
      (MV.pt x).left ≫ P.m.φ = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ v.left) ∧
    P.IsCochars MV A.I ∧ IsPrincipal P.tB ∧
    ∃ (t' : SAB H (Sp (𝓞 L))) (m' : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L)))
      (MB : LieModel t'.G (𝟙 _) A.Bq.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧
      ∀ x : A.Λ, ((MV.pt x ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (A.f x)).left)

end HodgeCpt

variable {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Y : Model Xo c β}
  {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd)

def CptOrigin.IsSmallPart {w : (Σ k, J k) → ℂ} (d : MuFrameAt Hd w) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) : Prop :=
  ∀ τ k, s τ k ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (d.b τ (tailIdx Dc.j_le_N k)) - s τ k ∈ Or.𝔐.Vgen (Or.bg τ)

def CptOrigin.PhiWeight (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (x : ℝ) : Prop :=
  ∃ (d : MuFrameAt Hd w) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (ν : ℝ), Or.IsSmallPart d s ∧
    Or.𝔐.GeoPhi Or.sm z s ν ∧ 0 < ν ∧
    x = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + Real.log ν / 2

def CptOrigin.Good : Prop := (∀ p ∈ S₀, HT.HTFree Or.𝔐 p) ∧ ∀ p ∈ Dc.S, HT.HTFree Or.𝔐 p

end GlobalTheory.CompanionTheory.Ar
end
end
