module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialOperatorChainsAcyclicPositiveDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle427
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle522
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LawDer

theorem atZero_subst_of_unit (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hc : ∀ i, constantCoeff (μ i) = 0)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = fun i => X i)
    (F : MvPowerSeries (Fin d) R) : atZero (subst μ F) = F := by
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  unfold atZero
  rw [subst_comp_subst_apply hμ hz]
  have : (fun i => subst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) (μ i))
      = fun i => X i := hu
  rw [this, subst_self]
  rfl

theorem invDer_mul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), invDer μ u (F * G) = invDer μ u F * G + F * invDer μ u G := by
  intro R _ d μ hc hu u F G
  have hμ : HasSubst μ := hasSubst_of_constantCoeff_zero hc
  have hz : HasSubst (Sum.elim (fun i : Fin d => (X i : MvPowerSeries (Fin d) R)) fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero (by intro s; cases s <;> simp)
  have hmul : ∀ H K : MvPowerSeries (Fin d ⊕ Fin d) R, atZero (H * K) = atZero H * atZero K := by
    intro H K; unfold atZero; exact subst_mul hz H K
  have h0 := atZero_subst_of_unit R d μ hc hu
  have key : ∀ i, atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ (F * G))) =
      atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ F)) * G + F * atZero (MvPowerSeries.pderiv (Sum.inr i) (subst μ G)) := by
    intro i
    rw [subst_mul hμ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    unfold atZero
    rw [subst_add hz, subst_mul hz, subst_mul hz]
    have hF := h0 F; have hG := h0 G; unfold atZero at hF hG
    rw [hF, hG]; ring
  unfold invDer
  simp_rw [key, smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

end GlobalTheory.LawDer
end
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ

theorem _root_.GlobalTheory.T.bisimplicialOperatorChains_acyclic_positiveDegree : ∀ a b k : ℕ, 1 ≤ k → ∀ z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) → ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', ∀ c d : ℕ, c + d = k → ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  first | (exact @GlobalTheory.EZ.totChains_acyclic) | (exact GlobalTheory.EZ.totChains_acyclic) | (intros; apply GlobalTheory.EZ.totChains_acyclic <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

theorem _root_.GlobalTheory.T.total_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C] (Y : SimplicialObject (SimplicialObject C)) (a b k : ℕ) (h : a + b = k + 1), (dbl Y).ιTotal (ComplexShape.down ℕ) a b (k + 1) (by simpa only [ComplexShape.π_def] using h) ≫ (tot Y).d (k + 1) k = ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal k).attach, (ev Y).map (dT a b x.1.1 x.1.2) ≫ (dbl Y).ιTotal (ComplexShape.down ℕ) x.1.1 x.1.2 k (by simpa only [ComplexShape.π_def] using Finset.HasAntidiagonal.mem_antidiagonal.1 x.2) := by
  first | (exact @GlobalTheory.EZ.ιTotal_tot_d) | (exact GlobalTheory.EZ.ιTotal_tot_d) | (intros; apply GlobalTheory.EZ.ιTotal_tot_d <;> assumption)
end

section

open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

theorem fc_succ_eq_δ (n i : ℕ) (hi : i < n + 2) :
    fc (n + 1) n i = SimplexCategory.δ (⟨i, hi⟩ : Fin (n + 2)) := by
  ext j
  simp [fc, clampHom, faceFun, SimplexCategory.δ, Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

def diagOp : SimplicialObject BOp := Functor.diag SimplexCategoryᵒᵖ ⋙ Free.embedding ℤ _

theorem dD_succ_eq_objD (n : ℕ) : dD (n + 1) n = AlternatingFaceMapComplex.objD diagOp n := by
  rw [dD, if_pos rfl, AlternatingFaceMapComplex.objD, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fc_succ_eq_δ n i i.2]
  rfl

theorem dD_comp_dD (n m k : ℕ) : dD n m ≫ dD m k = 0 := by
  by_cases h1 : n = m + 1
  · subst h1
    by_cases h2 : m = k + 1
    · subst h2
      rw [dD_succ_eq_objD, dD_succ_eq_objD]
      exact AlternatingFaceMapComplex.d_squared diagOp k
    · rw [show dD m k = 0 from if_neg h2, Limits.comp_zero]
  · rw [show dD n m = 0 from if_neg h1, Limits.zero_comp]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl]
  have h1 : idc 0 0 = 𝟙 _ := Subsingleton.elim _ _
  have h2 : backc 0 0 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, h2]
  rfl

def awThen (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : bo n n ⟶ bo n n :=
  ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n

def awHtpy (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) :
    ∀ n : ℕ, bo n n ⟶ bo (n + 1) (n + 1) := fun n =>
  Nat.rec (motive := fun n => bo n n ⟶ bo (n + 1) (n + 1)) 0
    (fun k K => cone (k + 1) (k + 1) (k + 1) (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ K)) n

theorem awThen_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b) (n : ℕ) :
    awThen G (n + 1) ≫ dD (n + 1) n = dD (n + 1) n ≫ awThen G n := by
  simp only [awThen, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have e1 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
      awO (n + 1) x.1 x.2 ≫ G x.1 x.2 (n + 1) ≫ dD (n + 1) n =
        ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun x hx => by rw [hG _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
  have e2 : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      dD (n + 1) n ≫ awO n y.1 y.2 ≫ G y.1 y.2 n =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun y hy => by
      rw [← Category.assoc, haw _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), Preadditive.sum_comp]
      simp only [Category.assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

theorem awHtpy_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (hcone : ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n)) :
    ∀ n : ℕ, awThen G (n + 1) = 𝟙 _ + awHtpy G cone (n + 1) ≫ dD (n + 1 + 1) (n + 1) +
      dD (n + 1) n ≫ awHtpy G cone n := by
  have h0 : awThen G 0 = 𝟙 _ := by
    simp [awThen, awO_zero, hG0]
  have key : ∀ k : ℕ,
      (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k) ≫ dD (k + 1) k = 0 →
      awThen G (k + 1) = 𝟙 _ + awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) +
        dD (k + 1) k ≫ awHtpy G cone k := by
    intro k hk
    have h := hcone (k + 1) (k + 1) k (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k)
    rw [hk, map_zero, sub_zero] at h
    have h' : awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) =
        awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k := h
    rw [h']
    abel
  intro n
  induction n with
  | zero =>
    apply key
    have hK : awHtpy G cone 0 = 0 := rfl
    rw [hK, Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw 0, h0]
    simp
  | succ j ih =>
    apply key
    rw [Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw (j + 1), ih,
      Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (dD (j + 1 + 1) (j + 1)) (dD (j + 1) j),
      dD_comp_dD, Limits.zero_comp]
    simp only [Category.comp_id, Category.id_comp, Category.assoc, add_zero]
    abel

theorem awThen_homotopic : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ,
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
        𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  intro G hG0 hG
  obtain ⟨cone, ε, -, -, hcone⟩ := GlobalTheory.T.cone_contracting_homotopy
  have haw := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
  refine ⟨fun n m => if h : m = n + 1 then awHtpy G cone n ≫ eqToHom (by rw [h]) else 0, fun n => ?_⟩
  cases n with
  | zero =>
    have h0 : awThen G 0 = 𝟙 _ := by
      simp [awThen, awO_zero, hG0]
    have hK : awHtpy G cone 0 = 0 := rfl
    change awThen G 0 = _
    simp [h0, hK, dD]
  | succ k =>
    change awThen G (k + 1) = _
    simp only [dif_pos, eqToHom_refl, Category.comp_id, Nat.add_sub_cancel]
    exact awHtpy_spec G hG0 hG haw cone hcone k

end GlobalTheory.EZ
end
end

section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

noncomputable section

namespace GlobalTheory.TorusFrame

theorem gram_mul_of_preserves {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (M x : Matrix (Fin r) (Fin r) ℂ)
    (hM : ∀ u w, hermC τ G (M *ᵥ u) (M *ᵥ w) = hermC τ G u w) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * x) = ReciprocityTheory.ChartRestriction.G.FD.gram τ G x := by
  have hc (a : Fin r) : ReciprocityTheory.ChartRestriction.G.FD.col (M * x) a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col x a := by
    ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply, hc, hM]

theorem torus_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  intro E _ _ _ r X x hx
  refine ⟨fun θ => ⟨torusGL hx θ, GlobalTheory.T.torusElementConjugatedByFrame_mem_specialUnitary E r X x hx θ⟩, torusDer x, ?_, ?_, ?_, ?_, fun θ => GlobalTheory.T.torusTangent_mem_specialUnitaryLie_diagonal E r X x hx θ, ?_⟩
  · intro θ; funext τ
    show ((mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))) * (mat x τ)⁻¹ * mat x τ :
      Matrix (Fin r) (Fin r) ℂ) : Fin r → Fin r → ℂ) = (mat x τ * mat (phaseFrame θ) τ : Matrix (Fin r) (Fin r) ℂ)
    rw [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]; rfl
  · intro θ θ'
    refine Subtype.ext (funext fun τ => ?_)
    have hp : phaseU ((θ + θ') τ) = phaseU (θ τ) * phaseU (θ' τ) := by
      refine Units.ext ?_
      simp only [phaseU, Units.val_mul, diagonal_mul_diagonal, Pi.add_apply, angles_add, Complex.ofReal_add,
        mul_add, Complex.exp_add]
    simp only [Subgroup.coe_mul, Pi.mul_apply, torusGL, hp]
    group
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    have hph : Continuous fun φ : Fin (r - 1) → ℝ => phaseU φ := by
      refine Units.continuous_iff.2 ⟨Continuous.matrix_diagonal (continuous_pi fun a => ?_),
        Continuous.matrix_diagonal (continuous_pi fun a => ?_)⟩
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a)))
      · exact Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_angles a))).neg
    exact (continuous_const.mul (hph.comp (continuous_apply τ))).mul continuous_const
  · exact GlobalTheory.T.hasStrictFDerivAt_diagonalTorus_zero E r X.Ψ x
  · rintro g ⟨b, hb, hgb⟩
    have hgx (τ : X.Ψ) : ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat b τ :=
      congrFun hgb τ
    have hdiag (τ : X.Ψ) := GlobalTheory.T.upperTriangular_signForm_diagonal_unimodular r (mat b τ) (fun a => sgn X.p0 a)
      (fun a => by unfold sgn; split_ifs <;> simp) (isUnit_iff_ne_zero.2 (hb τ).1) (fun a c h => (hb τ).2 a c h) (by
        have h1 := gram_mul_of_preserves τ.1 X.Gm _ (mat x τ) ((g.2 τ).2)
        have hJ := hx τ
        rw [gram_eq] at hJ
        rw [hgx τ, gram_eq, gram_eq, transpose_mul, Matrix.map_mul] at h1
        rw [← hJ]; refine Eq.trans ?_ h1; simp only [Matrix.mul_assoc])
    have hbd (τ : X.Ψ) : mat b τ = diagonal fun a => mat b τ a a := by
      ext a c; by_cases h : a = c
      · subst h; simp
      · simp [diagonal_apply_ne _ h, (hdiag τ).1 a c h]
    have hdet (τ : X.Ψ) : ∏ a, mat b τ a a = 1 := by
      have h := congrArg Matrix.det (hgx τ)
      rw [det_mul, det_mul, (g.2 τ).1, one_mul, hbd τ, det_diagonal] at h
      exact (mul_left_cancel₀ (isUnit_det_of_isOrth hx τ).ne_zero (h.symm.trans (mul_one _).symm))
    choose φ hφ using fun τ : X.Ψ => GlobalTheory.T.exists_torusAngles_of_unimodular_prod_one r (fun a => mat b τ a a) (hdiag τ).2 (hdet τ)
    refine ⟨φ, Subtype.ext (funext fun τ => Units.ext ?_)⟩
    show ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) =
      mat x τ * diagonal (fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) * (mat x τ)⁻¹
    have hD : (diagonal fun a => Complex.exp (Complex.I * (angles (φ τ) a : ℂ))) = mat b τ := by
      rw [hbd τ]; congr 1; funext a; exact hφ τ a
    rw [hD, ← hgx τ, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_of_isOrth hx τ), Matrix.mul_one]

end GlobalTheory.TorusFrame
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

theorem _root_.GlobalTheory.T.chartGraphCoordinates_opNorm_le_of_small : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (z : V (nd X)),
    (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  first | exact @GlobalTheory.ChartGraph.zN_graphCoord_le | exact GlobalTheory.ChartGraph.zN_graphCoord_le | (intros; apply GlobalTheory.ChartGraph.zN_graphCoord_le <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box : ∀ {k : Type} [Field k] [ValuativeRel k] (G : Grid k) (ϖ : kˣ) (a a' : ℤ) (e : Vars G), e ∈ box G ϖ a a' → valuation k (phase (0 : ColArgs G) e) ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) := by
  first | exact @GlobalTheory.OriginBox.phase_origin_le | exact GlobalTheory.OriginBox.phase_origin_le | (intros; apply GlobalTheory.OriginBox.phase_origin_le <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.OriginBox GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem _root_.GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) (g : G.VertexGroup), (∀ j, g (G.m, j) = colDiag G ϖ a a' j) → ∀ e : Vars G, Set.indicator {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} (1 : G.Args → ℂ) (G.moveArgs .one g (fill hs 0 0 e)) = (box G ϖ a a').indicator (1 : Vars G → ℂ) e := by
  first | exact @GlobalTheory.OriginBox.indicator_moveArgs_origin | exact GlobalTheory.OriginBox.indicator_moveArgs_origin | (intros; apply GlobalTheory.OriginBox.indicator_moveArgs_origin <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

theorem _root_.GlobalTheory.T.cocycle_local_sections_restrict_compatibly : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ (T : TT s) (p q : Pair (pt T)) (hpq : p ≤ q), Sec.res (algStr R T.obj.B) (Pair.le_fst hpq) (hSec f g T q) = hSec f g T p := by
  first | exact @GlobalTheory.CechDR.AffLoc.hSec_res | exact GlobalTheory.CechDR.AffLoc.hSec_res | (intros; apply GlobalTheory.CechDR.AffLoc.hSec_res <;> assumption)
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.coinvariant_of_locally_constant_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ) (R : Finset (GL (Fin a) k)),
    Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) → IsLocallyConstant χ →
    (∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y) →
    (∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) → Φ ∈ coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | exact GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum | (intros; apply GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum <;> assumption)
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.orbital_integral_vanishes_of_fibre : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by
  first | exact @GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero | exact GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero | (intros; apply GlobalTheory.RankFibreKer.integral_tw_eq_zero_of_fibre_eq_zero <;> assumption)
end

section

open GlobalTheory.WeilM Matrix

theorem _root_.GlobalTheory.T.rank_chart_stack_decomposition : ∀ (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k), Y.rank ≤ Fintype.card R → (Y.submatrix Sum.inl τ).det ≠ 0 → ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  first | exact @GlobalTheory.RankChart.exists_eq_stack | exact GlobalTheory.RankChart.exists_eq_stack | (intros; apply GlobalTheory.RankChart.exists_eq_stack <;> assumption)
end
