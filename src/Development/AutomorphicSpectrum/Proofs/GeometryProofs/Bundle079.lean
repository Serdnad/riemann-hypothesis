module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle068
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle069
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldEigenBasisDescends
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.graded_degree_formula : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (r : ℕ) (A : SatFlag B r) (i : Fin r) (f : Fin i → B.carrier) (s : B.carrier), (∀ a, f a ∈ A.F i.castSucc) → LinearIndependent (𝓞 L) f → s ∈ A.F i.succ → s ∉ A.F i.castSucc → A.grDeg i = (Module.finrank ℚ L : ℝ)⁻¹ * (Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) - (1 / 2) * ∑ σ : L →+* ℂ, (Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ - Real.log ‖B.gramDet σ f‖)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrLine.grDeg_eq | exact GlobalTheory.CompanionTheory.Ar.GrLine.grDeg_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GrLine.grDeg_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace ChartFrame

theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b : F} (ha : a ∈ R) (hb : b ∈ R)
    (h0 : a * b ≠ 0) : locSub R a ≤ locSub R (a * b) := by
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub
  rw [Subring.closure_le]
  rintro y (hy | hy)
  · exact Subring.subset_closure (Set.mem_union_left _ hy)
  · rw [Set.mem_singleton_iff] at hy
    rw [hy, show a⁻¹ = b * (a * b)⁻¹ by rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hb0, mul_one]]
    exact mul_mem (Subring.subset_closure (Set.mem_union_left _ hb))
      (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_mul' {p : Cpt ξ} {f g : Ω} (hf : unitAt ξ p f) (hg : unitAt ξ p g) :
    unitAt ξ p (f * g) := by
  unfold GlobalTheory.CompanionTheory.Ar.unitAt at hf hg ⊢
  obtain ⟨hf0, hf1, hf2⟩ := hf
  obtain ⟨hg0, hg1, hg2⟩ := hg
  refine ⟨mul_ne_zero hf0 hg0, mul_mem hf1 hg1, ?_⟩
  rw [mul_inv]
  exact mul_mem hf2 hg2

theorem unitAt_prod' {p : Cpt ξ} {ι : Type} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    unfold GlobalTheory.CompanionTheory.Ar.unitAt
    refine ⟨one_ne_zero, one_mem _, ?_⟩
    rw [inv_one]
    exact one_mem _
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul' (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_dual_family {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {β : Fin r → E}
    (hβ : LinearIndependent Ω β) :
    ∃ w : Fin r → Module.Dual Ω E, ∀ l l', w l (β l') = (1 : Matrix (Fin r) (Fin r) Ω) l l' := by
  classical
  have hext : ∀ l : Fin r, ∃ g : Module.Dual Ω E,
      g.comp (Submodule.span Ω (Set.range β)).subtype = (Module.Basis.span hβ).coord l :=
    fun l => LinearMap.exists_extend ((Module.Basis.span hβ).coord l)
  choose w hw using hext
  refine ⟨w, fun l l' => ?_⟩
  have h1 : w l (β l') = (Module.Basis.span hβ).coord l (Module.Basis.span hβ l') := by
    rw [← hw l, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  rcases eq_or_ne l l' with rfl | hne
  · simp
  · simp [hne, hne.symm]

end ChartFrame


open ChartFrame ChartTie in
theorem exists_chart_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (r : ℕ) (V : Submodule Ω E) (L : Lat ξ E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (c : κ) (p : Cpt ξ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → IsTwistGen ξ x L m φ → (LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = V) → InChart ξ x c p → ∃ g ∈ chartSub x c, unitAt ξ p g ∧ ∃ (T : Matrix (Fin r) (Fin r) Ω) (M : Matrix (Fin n) (Fin r) Ω) (N : Matrix (Fin r) (Fin n) Ω), T.det ≠ 0 ∧ (∀ j l, M j l ∈ locSub (chartSub x c) g) ∧ (∀ l j, N l j ∈ locSub (chartSub x c) g) ∧ N * M = 1 ∧ ∀ j l, φ j (b l) = x c ^ m * (M * T) j l := by
  intro X Ω _ ξ E _ _ κ x r V L m n φ b c p hCT _hgen hVB hTw hb hIn
  classical
  obtain ⟨hbli, hbV⟩ := hb
  have hx0 : x c ≠ 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.InChart at hIn
    exact hIn.1
  have hxm : x c ^ m ≠ 0 := pow_ne_zero m hx0
  unfold GlobalTheory.CompanionTheory.Ar.FlagBun.IsTwistGen at hTw
  obtain ⟨hTw1, hTw2⟩ := hTw
  unfold GlobalTheory.CompanionTheory.Ar.Lat.IsVB GlobalTheory.CompanionTheory.Ar.Lat.IsVBOn at hVB
  obtain ⟨U, hpU, b', hb'V, hfr⟩ := hVB p (Set.mem_univ p)
  have hF := hfr p (Set.mem_univ p) hpU
  unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt at hF
  obtain ⟨hb'li, hLp⟩ := hF
  obtain ⟨w, hw⟩ := exists_dual_family hb'li
  have hcoord : ∀ e ∈ Submodule.span Ω (Set.range b'), e = ∑ k, w k e • b' k := by
    intro e he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
    have hwc : ∀ k, w k (∑ i, cf i • b' i) = cf k := by
      intro k
      simp [hw, Matrix.one_apply]
    exact (Finset.sum_congr rfl fun k _ => by rw [hwc k]).symm
  have hbexp : ∀ l, b l = ∑ k, w k (b l) • b' k := fun l =>
    hcoord _ (by rw [hb'V, ← hbV]; exact Submodule.subset_span ⟨l, rfl⟩)
  have hdet : (Matrix.of fun k l => w k (b l)).det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
    apply hv0
    have hsum : ∑ l, v l • b l = 0 := by
      calc ∑ l, v l • b l = ∑ l, v l • ∑ k, w k (b l) • b' k :=
            Finset.sum_congr rfl fun l _ => by rw [← hbexp l]
        _ = ∑ l, ∑ k, (v l * w k (b l)) • b' k := by simp only [Finset.smul_sum, smul_smul]
        _ = ∑ k, ∑ l, (v l * w k (b l)) • b' k := Finset.sum_comm
        _ = ∑ k, (Matrix.mulVec (Matrix.of fun k l => w k (b l)) v) k • b' k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.sum_smul]
            congr 1
            simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
            exact Finset.sum_congr rfl fun l _ => mul_comm _ _
        _ = 0 := by simp [hTv]
    exact funext (Fintype.linearIndependent_iff.1 hbli v hsum)
  have hb'Lp : ∀ k, b' k ∈ L p := fun k => by
    rw [hLp]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hMreg : ∀ j k, φ j (b' k) / x c ^ m ∈ regAt ξ p := fun j k =>
    hTw1 j p c hIn (b' k) (hb'Lp k)
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hLp] at he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he

    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Subring.smul_def, map_smul, hw, smul_eq_mul]
    refine mul_mem (cf i).2 ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hN : ∀ l, ∃ gv : Fin n → Ω, (∀ j, gv j ∈ regAt ξ p) ∧
      ∀ e ∈ L p, w l e = ∑ j, gv j * (φ j e / x c ^ m) := fun l =>
    hTw2 p c hIn (w l) (hwreg l)
  choose gv hgvreg hgv using hN
  have hNM : (Matrix.of fun l j => gv l j) * (Matrix.of fun j k => φ j (b' k) / x c ^ m) = 1 := by
    ext l l'
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [← hgv l (b' l') (hb'Lp l'), hw]
  have hreg : ∀ a ∈ regAt ξ p, ∃ s ∈ chartSub x c, unitAt ξ p s ∧ a ∈ locSub (chartSub x c) s := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hCT c p hIn a).1 ha
    have hs0 : s ≠ 0 := by
      unfold GlobalTheory.CompanionTheory.Ar.unitAt at hsu
      exact hsu.1
    refine ⟨s, by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hs, hsu, ?_⟩
    unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub
    rw [show a = s * a * s⁻¹ by rw [mul_comm s a, mul_assoc, mul_inv_cancel₀ hs0, mul_one]]
    exact mul_mem
      (Subring.subset_closure (Set.mem_union_left _ (by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hsa)))
      (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))
  have hent : ∀ i : (Fin n × Fin r) ⊕ (Fin r × Fin n),
      Sum.elim (fun jk => φ jk.1 (b' jk.2) / x c ^ m) (fun lj => gv lj.1 lj.2) i ∈ regAt ξ p := by
    rintro (⟨j, k⟩ | ⟨l, j⟩)
    · exact hMreg j k
    · exact hgvreg l j
  choose s hsR hsU hsloc using fun i => hreg _ (hent i)
  have hgU : unitAt ξ p (∏ i, s i) := unitAt_prod' _ _ fun i _ => hsU i
  have hgR : (∏ i, s i) ∈ chartSub x c := prod_mem fun i _ => hsR i
  have hg0 : (∏ i, s i) ≠ 0 := by
    have h := hgU
    unfold GlobalTheory.CompanionTheory.Ar.unitAt at h
    exact h.1
  have hmono : ∀ i, locSub (chartSub x c) (s i) ≤ locSub (chartSub x c) (∏ i, s i) := by
    intro i
    have hsplit := Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)
    rw [← hsplit]
    exact locSub_le_of_mul (hsR i) (prod_mem fun j _ => hsR j) (by rw [hsplit]; exact hg0)
  refine ⟨∏ i, s i, hgR, hgU, Matrix.of fun k l => w k (b l),
    Matrix.of fun j k => φ j (b' k) / x c ^ m, Matrix.of fun l j => gv l j, hdet, ?_, ?_, hNM, ?_⟩
  · intro j k
    simp only [Matrix.of_apply]
    exact hmono _ (hsloc (Sum.inl (j, k)))
  · intro l j
    simp only [Matrix.of_apply]
    exact hmono _ (hsloc (Sum.inr (l, j)))
  · intro j l
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    conv_lhs => rw [hbexp l]

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    first
      | (rw [div_mul_eq_mul_div, mul_div_assoc', mul_comm (x c ^ m), mul_div_assoc, div_self hxm,
          mul_one, mul_comm])
      | (field_simp; ring)
      | field_simp

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.dvr_specialization_lie_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Em : Type) [AddCommGroup Em] [Module Ω Em]
    (M : LieModel G ξ Em) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (x : Sp K ⟶ X) (z : Sp V ⟶ X) (h₁ : genPt ξ ⤳ centre x) (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K) (g : ℕ)
    (ℓ : Fin g → Em) (MX : LieModel G x (Fin g → K)) (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ z) (Fin g → K)),
    spMap (algebraMap V K) ≫ z = x → (∀ e, (MC.pt e).left = (MX.pt e).left) → IsCptGen ξ →
    regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ →
    (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) →
    M.lat.IsFrameAt ℓ ⟨_, h₂⟩ →
    (∀ w : Fin g → regAt ξ ⟨_, h₁⟩, M.ValAt x (comb ℓ w) (MX.pt (fun i => ψ (w i)))) →
    M.fibAt M.lat z MC = stdLat V K g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.fibAt_lat_eq_stdLat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isAdapted_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g p q ℓ ψ ρH ρHC HL ev σ σC b₁ b₂ u x₁ x₂ hu hE hσ hcl hA hb₁ hb₂
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IsEval at hE
  unfold GlobalTheory.CompanionTheory.Ar.Flat.IsAdapted at hA ⊢
  obtain ⟨hE1, hE2, hE3⟩ := hE
  obtain ⟨hA1, hA2, hA3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show ev ⟨u i, hu i⟩ ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρHC σC
    have hui := hA1 i
    rw [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf] at hui ⊢
    intro a
    have h1 := hui a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change ρH a (u i) = σ (a : E) • u i at h1
    show ρHC a (ev ⟨u i, hu i⟩) = σC (a : E) • ev ⟨u i, hu i⟩
    obtain ⟨hσa, hψ⟩ := hσ (a : E)
    have hmem : ρH a (u i) ∈ HL := hcl a (u i) (hu i)
    have e1 : ev ⟨ρH a (u i), hmem⟩ = ρHC a (ev ⟨u i, hu i⟩) := hE1 a ⟨u i, hu i⟩ hmem
    have e2 : (⟨ρH a (u i), hmem⟩ : HL) = (⟨σ a, hσa⟩ : R') • (⟨u i, hu i⟩ : HL) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subring.smul_def]
      exact h1
    rw [← e1, e2, map_smulₛₗ, hψ]
  · intro i
    exact hE2 ⟨u (Fin.castAdd q i), hu _⟩ (x₁ i) ((hA2 i).trans (hb₁ i))
  · intro j
    obtain ⟨hj1, hj2⟩ := hA3 j
    constructor
    · have hc : (u (Fin.natAdd p j)).1 = comb ℓ (fun _ => (0 : R')) := by
        rw [hj1]
        simp [GlobalTheory.CompanionTheory.Ar.Flat.CPoint.comb]
      have h3 := hE2 ⟨u (Fin.natAdd p j), hu _⟩ (fun _ => 0) hc
      refine h3.trans ?_
      funext k
      simp
    · intro j'
      have hc : (u (Fin.natAdd p j)).2 (comb ℓ (x₂ j')) = ((if j = j' then 1 else 0 : R') : Ω) := by
        rw [← hb₂ j', hj2 j']
        split_ifs <;> simp
      have h3 := hE3 ⟨u (Fin.natAdd p j), hu _⟩ (x₂ j') (if j = j' then 1 else 0) hj1 hc
      refine h3.trans ?_
      split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.cp_embedding_factors_through_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : Nat.Primes)
    (κ : c.F →+* ℂ_[p]) (s : E →+* ℂ_[p]), ∃ τ : E →+* ℂ, s = κ.comp (inE c τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_emb_through_coeff | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_emb_through_coeff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_emb_through_coeff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.number_field_embeddings_into_cp_integral : ∀ (E : Type) [Field E] [NumberField E] (p : Nat.Primes),
    (∀ (s : E →+* ℂ_[p]) (a : 𝓞 E), s (a : E) ∈ (algebraMap (OCp p) ℂ_[p]).range) ∧
      Nat.card (E →+* ℂ_[p]) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.embeddings_padicComplex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.finrank_eigSp_eq_of_lattice_specialization : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    Module.finrank C (HT.eigSp ρC σC) = Module.finrank Ω (HT.eigSp ρ σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.finrank_eigSp_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.finrank_eigSp_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.finrank_eigSp_eval <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.cp_integers_valuation_ring : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ocp_integers <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.hodge_lattice_stable_under_action : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.hodge_lattice_eval_eigProj_comm : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj.ev_eigProj | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj.ev_eigProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj.ev_eigProj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.tied_action_compose_residue_map : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs K C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field K] [Field C]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* K) (j : K →+* C)
    (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C)),
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρK → Tied ℓ (j.comp ψ) ρ ρC →
    ∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap.tied_map_comp | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap.tied_map_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap.tied_map_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.fraction_field_eigen_basis_descends : ∀ (E : Type) [Field E] [NumberField E] (K C V A : Type) [Field K] [CharZero K] [Field C] [CharZero C] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra V K] [IsFractionRing V K] [CommRing A] [IsDomain A] [Algebra A C]
    (j : K →+* C) (g n : ℕ) (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (σ : E →+* K) (b : Fin n → Fin g → K),
    (∀ a : K, a ∈ (algebraMap V K).range → j a ∈ (algebraMap A C).range) →
    (∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i)) →
    LinearIndependent K b → Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) →
    LinearIndependent C (fun i k => j (b i k)) ∧
      Submodule.span C (Set.range fun i k => j (b i k)) = HT.eigSp ρC (j.comp σ) ∧
      Submodule.span A (Set.range fun i k => j (b i k)) = HT.eigSub ρC (j.comp σ) (stdLat A C g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange <;> assumption)
end
