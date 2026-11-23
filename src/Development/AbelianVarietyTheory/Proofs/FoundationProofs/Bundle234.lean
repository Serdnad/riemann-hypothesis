module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle008
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle210
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle217
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle218
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle220
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.smallTraces_subgroup_galois_towerTop : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n → ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧ ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.K5.small_traces_subgroup | exact GlobalTheory.K5.small_traces_subgroup | (intros; apply GlobalTheory.K5.small_traces_subgroup <;> assumption)
end

section

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem conv_dirac_sub_sum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (b : G → ℂ) (x : G) :
    conv (dirac - ∑ i ∈ s, a i) b x = b x - ∑ i ∈ s, conv (a i) b x := by
  unfold conv dirac
  simp only [Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  rw [Finset.sum_eq_single (1 : G)]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem sum_goodSet_le_one (g : ℕ) [Fact g.Prime] (N m : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ) :
    ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤ 1 := by
  have h1 : ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
      ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun F _ _ => ?_
    exact Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  refine h1.trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => sqSet g N) fun _ f => ((torusCard g f : ℝ))⁻¹]
  have h2 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  have h3 := mass_nonneg (g := g) N fun _ => True
  simp only [mass, Finset.filter_true] at h2 h3
  exact Finset.prod_le_one₀ (fun _ _ => h3) fun _ _ => h2

theorem badWeight_le : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  intro g _ N m q d ι _ L τ ch hN hP hτ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hg⟩ := hP
  have hS := GlobalTheory.T.goodSquarefreeLabelTuples_weight_ge g N m q d ι ch hN hg ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hS1 := sum_goodSet_le_one g N m ι ch
  have hS0 : 0 ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ :=
    Finset.sum_nonneg fun F _ => Finset.prod_nonneg fun v _ => inv_nonneg.2 (Nat.cast_nonneg _)
  choose! w hw1 hw2 using fun v => GlobalTheory.T.series_representation_weight_lower_bound g N (L v) (τ v) (hτ v)
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨1 - ∑ F ∈ goodSet g N ch, ∏ v, w v (F v), ?_, ?_⟩
  · unfold eGood
    rw [conv_dirac_sub_sum]
    push_cast
    rw [sub_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [(tens_calculus ι (GG g N) (GG g N)).1]
    unfold tens
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => hw1 v (F v) (hmem F hF v)
  · have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_le
    have hg0 : (0 : ℝ) < g := by linarith
    have hinv : 1 / (g : ℝ) ≤ 1 := by rw [div_le_one hg0]; exact hg1
    have hinv0 : 0 ≤ 1 / (g : ℝ) := by positivity
    have hA : (1 - 1 / (g : ℝ)) ^ Fintype.card ι * ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ ≤
        ∑ F ∈ goodSet g N ch, ∏ v, w v (F v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun F hF => ?_
      rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => ?_) fun v _ => hw2 v (F v) (hmem F hF v)
      exact mul_nonneg (by linarith) (inv_nonneg.2 (Nat.cast_nonneg _))
    have hB : 1 - (Fintype.card ι : ℝ) / g ≤ (1 - 1 / (g : ℝ)) ^ Fintype.card ι := by
      have := one_add_mul_le_pow (a := -(1 / (g : ℝ))) (by linarith) (Fintype.card ι)
      rw [← sub_eq_add_neg] at this
      refine le_trans (le_of_eq ?_) this
      ring
    have hC : 0 ≤ (Fintype.card ι : ℝ) / g := by positivity
    have hD := mul_le_mul_of_nonneg_right hB hS0
    have hE := mul_le_mul_of_nonneg_left hS1 hC
    nlinarith

end GlobalTheory.BadShare
end
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.FinWeil

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj

theorem coe_sgO (D : D7) (r : 𝓞 D.host.E) : ((sgO D r : 𝓞 D.host.E) : D.host.E) = D.host.conj (r : D.host.E) := rfl

abbrev XA (D : D7) (N N' : ℕ) : Type := Matrix (Fin N') (Fin N) (AE D)

theorem smul_AE (D : D7) (r : 𝓞 D.host.E) (y : AE D) : r • y = inc D (r : D.host.E) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul']
    simp [inc, Formalism.UG.inclE, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem ihE_mul (D : D7) (cc : Ideal (𝓞 D.host.K)) {s t : AE D} (hs : s ∈ OhE D) (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s', hs', rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * s', mul_mem hs hs', by ring⟩
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

def latA (D : D7) (cc : Ideal (𝓞 D.host.K)) (N N' : ℕ) : Submodule (𝓞 D.host.E) (XA D N N') where
  carrier := {ζ | ∀ i j, ζ i j ∈ IhE D cc}
  add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r ζ h i j => by
    rw [Matrix.smul_apply, smul_AE]
    exact ihE_mul D cc ((AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩) (h i j)

theorem mem_latA {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {ζ : XA D N N'} :
    ζ ∈ latA D cc N N' ↔ ∀ i j, ζ i j ∈ IhE D cc := Iff.rfl

def actA (D : D7) (N N' : ℕ) : GA D N × GA D N' →* Module.End (𝓞 D.host.E) (XA D N N') where
  toFun u :=
    { toFun := fun ζ => ((u.2 : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        (((u.1 : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r x => by
        have h : ∀ {a b : ℕ} (y : Matrix (Fin a) (Fin b) (AE D)), r • y = inc D (r : D.host.E) • y := fun y => by
          ext i j
          rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_eq_mul]
        rw [RingHom.id_apply, h, h, Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := by
    ext1 ζ
    simp
  map_mul' u v := by
    ext1 ζ
    simp [Matrix.mul_assoc]

theorem actA_apply {D : D7} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    actA D N N' (g, g') ζ = ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem wd_add {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem wd_smul {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

def TTs (D : D7) (T : Tor D) (N N' : ℕ) : Submodule ℂ (VC D N N' → ℂ) where
  carrier := TT D T N N'
  add_mem' := by
    rintro F G ⟨hF, m, hm, h⟩ ⟨hG, n, hn, h'⟩
    refine ⟨hF.add hG, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    rw [wd_add]
    congr 1
    · rw [mul_smul]; exact h _ (AddSubgroup.nsmul_mem _ hx n)
    · rw [mul_comm, mul_smul]; exact h' _ (AddSubgroup.nsmul_mem _ hx m)
  zero_mem' := ⟨differentiable_const _, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩
  smul_mem' := by
    rintro c F ⟨hF, m, hm, h⟩
    exact ⟨hF.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

def psi0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : D.host.E) : ℂ :=
  ee (-(‖δ‖ ^ 2 / area (lamOf D cc δ) * (∑ τ, embT D τ a).im))

def IsPsi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (ψ : AE D → ℂ) : Prop :=
  (∀ x y, ψ (x + y) = ψ x * ψ y) ∧ ψ 0 = 1 ∧ (∀ a, ψ (inc D a) = psi0 D cc δ a) ∧ (∀ y, ψ (y + sgA D y) = 1) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, ψ ((m : AE D) * s) = 1

def gamA {D : D7} (ψ : AE D → ℂ) {N N' : ℕ} (ζ η : XA D N N') : ℂ := ψ (∑ i, ∑ j, ζ i j * sgA D (η i j))

def IsModel (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (w : 𝓞 D.host.E) (γ : XA D N N' → XA D N N' → ℂ)
    (WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N') : Prop :=
  IsHeis (sgO D) w γ WA ∧ SelfDual γ (latA D cc N N') ∧
  (∀ u ζ η, γ (actA D N N' u ζ) (actA D N N' u η) = γ ζ η) ∧
  (∀ (z : Matrix (Fin N') (Fin N) D.host.E) (F : TTs D (tor0 D cc δ) N N'),
    (WA (z.map (inc D)) F : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) ∧
  ∀ ζ F, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ latA D cc N N', WA (ζ + m • a) F = WA ζ F

end GlobalTheory.FinWeil
end
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.setIntegral_cexp_im_herm_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  first | exact @GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero | exact GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero | (intros; apply GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero <;> assumption)
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

noncomputable section

namespace GlobalTheory.UnitaryTheta

theorem exists_eigenbasis_of_isPosHerm {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) (a : V →ₗ[ℂ] V) (ha : ∀ z w, H (a z) (a w) = H z w) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
      (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i := by
  first
  | exact @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis
  | (apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthonormalEigenbasis.exists_orthonormal_eigenbasis ..)

theorem unitary_exists_orthonormal_eigenbasis :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H →
      ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) →
        ∃ (n : ℕ) (e : Module.Basis (Fin n) ℂ V) (l : Fin n → ℂ),
          (∀ i j, H (e i) (e j) = if i = j then 1 else 0) ∧ ∀ i, ‖l i‖ = 1 ∧ a (e i) = l i • e i :=
  fun _ _ _ _ H hH a ha => exists_eigenbasis_of_isPosHerm H hH a.toLinearMap ha

end GlobalTheory.UnitaryTheta
end
end

section

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.summable_exp_neg_herm_add_norm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  first | exact @GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | exact GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | (intros; apply GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.ConjRestrict

theorem coeff_taylorDir_embDomain {σ σ' W : Type*} [Fintype σ] [Fintype σ'] [NormedAddCommGroup W]
    [NormedSpace ℂ W] (e : σ ↪ σ') (u : σ' → W) {f : W → ℂ} (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (taylorDir (fun i => u (e i)) f) =
      MvPowerSeries.coeff (Finsupp.embDomain e α) (taylorDir u f) := by
  have h1 : ((α.toMultiset.toList : List σ) : Multiset σ) = Finsupp.toMultiset α := by simp
  have h2 : ((α.toMultiset.toList.map e : List σ') : Multiset σ') =
      Finsupp.toMultiset (Finsupp.embDomain e α) := by
    rw [← Multiset.map_coe, h1, Finsupp.toMultiset_map, Finsupp.embDomain_eq_mapDomain]
  have h3 : ∏ i, ((Finsupp.embDomain e α) i).factorial = ∏ i, (α i).factorial := by
    rw [← Finsupp.prod_fintype (Finsupp.embDomain e α) (fun _ n => n.factorial) (by simp),
      Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ (by simp)]
  rw [coeff_taylorDir_eq_lineDerivList _ hf h1, coeff_taylorDir_eq_lineDerivList _ hf h2, h3,
    List.map_map]
  rfl

def colEmb (D : D7) (N N' m : ℕ) :
    D.what₂.Tau × Fin N' × Fin N ↪ D.what₂.Tau × Fin N' × Fin (N + m) :=
  ⟨fun k => (k.1, k.2.1, Fin.castAdd m k.2.2), by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    simp [h]⟩

theorem colEmb_apply (D : D7) (N N' m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    colEmb D N N' m k = (k.1, k.2.1, Fin.castAdd m k.2.2) := rfl

theorem pad_coordV (D : D7) {N N' : ℕ} (m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    pad D m (coordV D k) = coordV D (colEmb D N N' m k) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [pad_left]; simp [coordV, colEmb_apply]
  · rw [pad_right]
    have : Fin.natAdd N i ≠ Fin.castAdd m k.2.2 := by
      intro h
      have := congrArg Fin.val h
      have := k.2.2.2
      simp at *
      omega
    simp [coordV, colEmb_apply, this]

theorem taylor_pad (D : D7) {N N' : ℕ} (m : ℕ) {G : VC D (N + m) N' → ℂ} (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => G (pad D m z)) α =
      Formalism.MainNotions.TaylorLogMetric.taylor D G (Finsupp.embDomain (colEmb D N N' m) α) := by
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hG)
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← coeff_taylorDir_embDomain _ _ han]
  have h := taylorDir_comp_clm (LinearMap.toContinuousLinearMap (padL D m (N := N) (N' := N')))
    (coordV D) han
  simp only [LinearMap.coe_toContinuousLinearMap', padL_apply, pad_coordV] at h
  rw [h]

theorem mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (α : Mono D N N') (z : VC D N N') :
    mono D (Finsupp.embDomain (colEmb D N N' m) α) (pad D m z) = mono D α z := by
  rw [mono, Finsupp.prod_embDomain]
  simp [mono, colEmb_apply]

theorem mem_range_of_mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (β : Mono D (N + m) N') (z : VC D N N')
    (h : mono D β (pad D m z) ≠ 0) : β ∈ Set.range (Finsupp.embDomain (colEmb D N N' m)) := by
  rw [Finsupp.mem_range_embDomain_iff]
  rintro ⟨τ, a, i⟩ hk
  revert hk
  refine Fin.addCases (fun i _ => ⟨(τ, a, i), rfl⟩) (fun i hk => ?_) i
  refine absurd (Finset.prod_eq_zero hk ?_) h
  have : β (τ, a, Fin.natAdd N i) ≠ 0 := Finsupp.mem_support_iff.1 hk
  simp [this]

theorem fnConj_pad : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  intro D N N' m M ρ G hG
  funext z
  simp only [fnConj]
  rw [← (Finsupp.embDomain_injective (colEmb D N N' m)).tsum_eq
    (f := fun β => ρ (TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.taylor D G β)) * mono D β (pad D m z))
    (fun β hβ => mem_range_of_mono_pad D m β z (right_ne_zero_of_mul hβ))]
  simp only [taylor_pad D m hG, mono_pad]

end GlobalTheory.ConjRestrict
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TwoSidedDet

def sandwich {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ) where
  toFun z := (A * Matrix.of z * B : Matrix _ _ ℂ)
  map_add' z w := by
    change A * (Matrix.of z + Matrix.of w) * B = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    change A * (c • Matrix.of z) * B = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem det_sandwich {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (sandwich A B) = A.det ^ n * B.det ^ m := by
  let e : (Fin m × Fin n → ℂ) ≃ₗ[ℂ] (Fin m → Fin n → ℂ) := LinearEquiv.curry ℂ ℂ (Fin m) (Fin n)
  have h : sandwich A B = (e : _ →ₗ[ℂ] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) A B.transpose)) ∘ₗ (e.symm : _ →ₗ[ℂ] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (A * Matrix.of z * B) i j = (Matrix.kroneckerMap (· * ·) A B.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Matrix.of_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
  simp

theorem det_mulV (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) :
    LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  have h : mulV D M' M = LinearMap.pi (fun τ : D.what₂.Tau =>
      (sandwich (M'.map (embT D τ)) (M.map (embT D τ))) ∘ₗ LinearMap.proj τ) := by
    refine LinearMap.ext fun z => ?_
    rfl
  rw [h, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_sandwich, RingHom.map_det, RingHom.map_det]
  rfl

end GlobalTheory.TwoSidedDet
end
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

theorem _root_.GlobalTheory.T.heckeStableCongruence_conj_diamondMatrix : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r → PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  first | exact @GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | exact GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | (intros; apply GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  first | exact @GlobalTheory.GKSubmodule.exists_submodule | exact GlobalTheory.GKSubmodule.exists_submodule | (intros; apply GlobalTheory.GKSubmodule.exists_submodule <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.stdWeylLattices_fg_and_span_coeffSpace : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (nabStd K lam).FG ∧ (delStd K lam).FG ∧ Submodule.span K (nabStd K lam : Set (Pol K ι n)) = VV K lam ∧ Submodule.span K (delStd K lam : Set (Pol K ι n)) = VV K lam := by
  first | exact @GlobalTheory.StdLatSpan.std_fg_span | exact GlobalTheory.StdLatSpan.std_fg_span | (intros; apply GlobalTheory.StdLatSpan.std_fg_span <;> assumption)
end
