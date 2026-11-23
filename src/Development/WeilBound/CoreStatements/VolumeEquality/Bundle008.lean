module

public import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def VecAt {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ) : Prop :=
  ∀ (m : ℕ) (s : Fin m → 𝔐.Li), (∀ a, ∃ v, 𝔐.M.ValAt (z t₀) (s a) v) →
    ∃ x : Fin m → (Fin n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ 𝔐.t.G),
      (∀ a, 𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec 𝔐.t (z t) (R t) (fun a => x a t) v

structure KUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) where
  ι : Type
  fin : Finite ι
  Di : ι → Datum H
  sig : ∀ k, (Di k).p = D.p ∧ (Di k).q = D.q
  F : ∀ k, UnivFam E (CMType H) j j' n g (Di k).La
  q_eq : ∀ k, (F k).q = q
  form_eq : ∀ k, (F k).form = (Di k).EF ∨ (F k).form = -(Di k).EF
  σ_eq : ∀ k τ, (F k).σ τ = κ.comp (labelEmb c (sm τ))
  Γ : ∀ k, Subgroup ((Di k).La ≃ₗ[𝓞 E] (Di k).La)
  mem_Γ : ∀ k γ, γ ∈ Γ k ↔ InLevel l (Di k) γ
  arith : ∀ k, (F k).IsArith (Γ k)
  pt : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Y.X)
  hol : ∀ k, IsHolTo (ballDom q) (pt k)
  comp_s_eq_spMap_of_isOver : ∀ k, ∀ t ∈ ballDom q, pt k t ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))
  interior : ∀ k, ∀ t ∈ ballDom q, centre (pt k t) ∈ abLocus Y.t.G
  disj : ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k' t' → k = k'
  fibre : ∀ k, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k t' ↔ (F k).Eqv (Γ k) t t'
  onto : ∀ p : Sp ℂ ⟶ Y.X, centre p ∈ abLocus Y.t.G → p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) →
    ∃ k, ∃ t ∈ ballDom q, pt k t = p
  lat : ∀ k, ∀ t ∈ ballDom q, FibreLat Y.t (pt k t) ((F k).R t)
  vec : ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (k : ι) (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), IsOpen V → V ⊆ ballDom q →
    IsHolTo V z → (∀ t ∈ V, z t ≫ 𝔐.f = pt k t) → ∀ t₀ ∈ V, VecAt 𝔐 (F k).R z t₀
  locc : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → (∀ b ∈ T, y b ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) →
    ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, y b = pt k t → y b' = pt k' t' → k = k'

def VecOfPeriods : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (κ : c.F →+* ℂ) (σ : KA l →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (n : ℕ) (V : Set (Fin n → ℂ))
    (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (xF : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c))
    (R : (Fin n → ℂ) → RiemLat E g (FU.Di i).La) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
    (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V → IsHolTo V z → IsHolTo V xF → IsHolPeriods (FU.Di i) ty V P →
    (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V) →
    (∀ t ∈ V, (R t).form = (FU.Di i).EF ∧ IsUnit (h t).det ∧ (∀ x, P t x = h t *ᵥ (R t).P x) ∧
      xF t ≫ Y.j = z t ≫ 𝔐.f ∧ xF t ≫ pullback.fst _ _ = FU.u i (P t) ∧ xF t ≫ pullback.snd _ _ = spMap κ) →
    ∀ t₀ ∈ V, VecAt 𝔐 R z t₀

def KUnifConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ),
    Nonempty (KUnif Y sm j j' n g q κ) → Nonempty (KUnif Y sm j j' n g q ((starRingEnd ℂ).comp κ))

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open Filter Topology Polynomial

theorem eval_monicOf {d : ℕ} (a : Fin d → ℂ) (x : ℂ) : (monicOf a).eval x = x ^ d + ∑ i, a i * x ^ (i : ℕ) := by
  simp [monicOf, eval_finsetSum]

theorem degree_low_lt {d : ℕ} (a : Fin d → ℂ) : (∑ i, C (a i) * X ^ (i : ℕ) : ℂ[X]).degree < d :=
  degree_sum_fin_lt a

theorem monic_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).Monic :=
  monic_X_pow_add (degree_low_lt a)

theorem natDegree_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).natDegree = d := by
  apply natDegree_eq_of_degree_eq_some
  unfold monicOf
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_low_lt a

theorem root_branch {d : ℕ} (a₀ : Fin d → ℂ) (x₀ : ℂ) (h0 : (monicOf a₀).IsRoot x₀)
    (h1 : (derivative (monicOf a₀)).eval x₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, ψ a₀ = x₀ ∧ ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℂ ψ a ∧ (monicOf a).IsRoot (ψ a) := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun u => u.2 ^ d + ∑ i, u.1 i * u.2 ^ (i : ℕ) with hf
  have cdf : ContDiffAt ℂ 1 f (a₀, x₀) := by
    rw [hf]
    fun_prop
  have hD : fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ ((derivative (monicOf a₀)).eval x₀) := by
    have e1 : HasFDerivAt (f ∘ fun x : ℂ => (a₀, x))
        (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) x₀ :=
      HasFDerivAt.comp x₀ (cdf.differentiableAt one_ne_zero).hasFDerivAt (hasFDerivAt_prodMk_right a₀ x₀)
    have e2 : (f ∘ fun x : ℂ => (a₀, x)) = fun x => (monicOf a₀).eval x := by
      funext x
      simp [hf, eval_monicOf]
    rw [e2] at e1
    exact e1.unique ((monicOf a₀).hasDerivAt x₀).hasFDerivAt
  have if₂ : (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hD]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self one_ne_zero if₂, ?_⟩
  have hc := cdf.contDiffAt_implicitFunction one_ne_zero if₂
  have hv := cdf.eventually_apply_implicitFunction one_ne_zero if₂
  filter_upwards [hc.eventually (by simp), hv] with a ha hb
  refine ⟨ha.differentiableAt one_ne_zero, ?_⟩
  have : f (a₀, x₀) = 0 := by
    have := h0
    rw [IsRoot.def, eval_monicOf] at this
    exact this
  rw [this] at hb
  rw [IsRoot.def, eval_monicOf]
  exact hb

theorem root_iff_of_injective {d : ℕ} (a : Fin d → ℂ) (r : Fin d → ℂ) (hr : Function.Injective r)
    (h : ∀ i, (monicOf a).IsRoot (r i)) (x : ℂ) : (monicOf a).IsRoot x ↔ ∃ i, x = r i := by
  classical
  refine ⟨fun hx => ?_, fun ⟨i, hi⟩ => hi ▸ h i⟩
  by_contra hne
  push Not at hne
  have hsub : insert x (Finset.univ.image r) ⊆ (monicOf a).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact h i
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
    intro hz
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
    exact hne i hi.symm), Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := (Multiset.toFinset_card_le (monicOf a).roots).trans (card_roots' (monicOf a))
  rw [natDegree_monicOf] at h2
  omega

theorem exists_roots {d : ℕ} (a : Fin d → ℂ) (hs : (monicOf a).Separable) :
    ∃ r : Fin d → ℂ, Function.Injective r ∧ ∀ i, (monicOf a).IsRoot (r i) := by
  classical
  have hc : (monicOf a).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, natDegree_monicOf]
  let e := Finset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩
  have := (e.symm i).2
  rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero] at this
  exact this

theorem rootBranches : RootBranches := by
  intro n d T a hT ha hs t₀ ht₀
  obtain ⟨r, hr, hroot⟩ := exists_roots (a t₀) (hs t₀ ht₀)
  have hder : ∀ i, (derivative (monicOf (a t₀))).eval (r i) ≠ 0 := fun i => by
    have := (hs t₀ ht₀).aeval_derivative_ne_zero (x := r i) (by simpa using hroot i)
    simpa using this
  choose ψ hψ0 hψ using fun i => root_branch (a t₀) (r i) (hroot i) (hder i)
  have hca : ContinuousAt a t₀ := (ha.differentiableAt (hT.mem_nhds ht₀)).continuousAt
  have hcθ : ∀ i, ContinuousAt (fun t => ψ i (a t)) t₀ := fun i =>
    ContinuousAt.comp (f := a) (hψ i).self_of_nhds.1.continuousAt hca
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ T ∧ (∀ i, DifferentiableAt ℂ (ψ i) (a t) ∧ (monicOf (a t)).IsRoot (ψ i (a t))) ∧
      ∀ i j, i ≠ j → ψ i (a t) ≠ ψ j (a t) := by
    refine (hT.eventually_mem ht₀).and (Eventually.and (eventually_all.mpr fun i => hca.tendsto.eventually (hψ i)) ?_)
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have : ∀ᶠ t in 𝓝 t₀, ψ i (a t) - ψ j (a t) ≠ 0 :=
        ((hcθ i).sub (hcθ j)).eventually_ne (by
          show ψ i (a t₀) - ψ j (a t₀) ≠ 0
          rw [hψ0, hψ0]
          exact sub_ne_zero.mpr (hr.ne hij))
      filter_upwards [this] with t ht _ using sub_ne_zero.mp ht
  obtain ⟨V, hV, hVo, hVt⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, fun i t => ψ i (a t), hVo, hVt, fun t ht => (hV t ht).1, fun i t ht => ?_, fun t ht => ?_⟩
  · exact (((hV t ht).2.1 i).1.comp t (ha.differentiableAt (hT.mem_nhds (hV t ht).1))).differentiableWithinAt
  · have hi : Function.Injective fun i => ψ i (a t) := fun i j h => by
      by_contra hij
      exact (hV t ht).2.2 i j hij h
    exact ⟨hi, root_iff_of_injective (a t) _ hi fun i => ((hV t ht).2.1 i).2⟩

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {sm : CMType H → CMType H ⊕ CMType H} {j j' n : ℕ}

def BaseUnif.Locc (B : BaseUnif Y sm j j' n) : Prop :=
  ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q,
      ∀ t' ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k').q, y b = B.pt k t → y b' = B.pt k' t' → k = k'

end

def BaseUnifEx2 : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ), 1 ≤ D.p + D.q →
    (sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p) → n = Fintype.card (CMType H) * j * j' →
    ∃ B : BaseUnif Y sm j j' n, B.Locc

def OnePiece : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ)
    (B : BaseUnif Y sm j j' n) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Sp Ω₀ ⟶ Y.X) (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] (ξ₁ : Sp Ω₁ ⟶ Y.X)
    (g : Ω₁ →+* Ω₂) (cst : c.F →+* Ω₂) (U : Y.X.Opens), B.Locc → IsCptGen ξ₀ → genPt ξ₁ = genPt ξ₀ →
    spMap g ≫ ξ₁ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → (∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) →
    genPt ξ₀ ∈ U → (∀ p : Sp ℂ ⟶ Y.X, ⊤ ≤ p ⁻¹ᵁ U → genPt ξ₀ ⤳ centre p) →
    ∀ κ : c.F →+* ℂ, ∃! k, B.κ k = κ ∧ ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U

def BallVolEq : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (n : ℕ) (B : BaseUnif Y Sum.inr D.p D.q n)
    (FF : Fin B.np → Set (Fin n → ℂ)), 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → (∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) →
    ∀ k k', ∫ t in FF k, ballDens (B.F k).q t = ∫ t in FF k', ballDens (B.F k').q t

def DegPush : Prop :=
  ∃ c₀ : ℕ → ℕ → ℕ → ℝ, (∀ f p q, c₀ f p q ≠ 0) ∧ (PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem),
      Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → ∀ (a : T.Comp) (K : Type) [Fintype K]
      (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)]
      [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (Or : CptOrigin Y T.bad Dc Hd),
      Or.bg = Sum.inl → Or.sm = Sum.inr → Or.𝔐.OmVB → Or.Good → Dc.S = ∅ → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf →
      degMu Hd = c₀ (Fintype.card (CMType H)) D.p D.q * Or.deg * Module.finrank ℚ c.F * T.vol a)

end SheetDecomposition
end
end
