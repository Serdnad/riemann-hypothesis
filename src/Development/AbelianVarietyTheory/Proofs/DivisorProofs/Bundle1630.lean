module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512

@[expose] public section

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.ColNorm

theorem csq_equiv {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : κ → ℂ) (v : κ → V) :
    csq h σ (fun i => c (e i)) (fun i => v (e i)) = csq h σ c v := by
  unfold csq
  congr 1
  exact Fintype.sum_equiv e _ _ fun i => Fintype.sum_equiv e _ _ fun k => rfl

theorem cnrm_equiv {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (c : κ → ℂ) (v : κ → V) :
    cnrm h σ (fun i => c (e i)) (fun i => v (e i)) = cnrm h σ c v :=
  congrArg Real.sqrt (csq_equiv h σ e c v)

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (Fin.tail u) := by
  simp only [word, List.ofFn_succ, List.prod_cons]
  rfl

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A]

theorem cnrm_words_le (S : Sys F A) (hS : S.Hyp) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ)
    (hu : ∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) :
    ∀ (t : ℕ) (β : Fin t → Fin (S.D + 1)) (j l : ℕ), j + t = l → l ≤ S.T →
      ∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → S.V j) (g : (Fin t → Fin S.N) × Fin m → S.V l),
      (∀ e i, (g (e, i) : A) = word S.mul (fun q => Pi.single (e q) 1) (f i)) →
      cnrm (S.nm l) σ (fun p => (∏ q, u (β q, p.1 q)) * c p.2) g ≤ Real.sqrt S.beta ^ t * cnrm (S.nm j) σ c f := by
  intro t
  induction t with
  | zero =>
    intro β j l hl _ m c f g hg
    obtain rfl : l = j := by omega
    have e : g = fun p => f p.2 := funext fun p => Subtype.ext (by
      rw [show p = (p.1, p.2) from rfl, hg]
      simp [word])
    subst e
    have := cnrm_equiv (S.nm l) σ (Equiv.uniqueProd (Fin m) (Fin 0 → Fin S.N)).symm
      (fun p => (∏ q, u (β q, p.1 q)) * c p.2) (fun p => f p.2)
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, pow_zero] at this ⊢
    rw [← this]
    rfl
  | succ t ih =>
    intro β j l hl hlT m c f g hg
    obtain rfl : l = j + t + 1 := by omega
    have hmem := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j t (by omega)).1
    let g' : (Fin t → Fin S.N) × Fin m → S.V (j + t) := fun p =>
      ⟨word S.mul (fun q => Pi.single (p.1 q) 1) (f p.2), hmem _ _ (f p.2).2⟩
    have h₀ := ih (Fin.tail β) j (j + t) rfl (by omega) m c f g' (fun _ _ => rfl)
    let eM : (Fin t → Fin S.N) × Fin m ≃ Fin (Fintype.card ((Fin t → Fin S.N) × Fin m)) := Fintype.equivFin _
    let E : Fin S.N × Fin (Fintype.card ((Fin t → Fin S.N) × Fin m)) ≃ (Fin (t + 1) → Fin S.N) × Fin m :=
      { toFun := fun p => (Fin.cons p.1 (eM.symm p.2).1, (eM.symm p.2).2)
        invFun := fun p => (p.1 0, eM (Fin.tail p.1, p.2))
        left_inv := fun p => by simp
        right_inv := fun p => by simp }
    have hE : ∀ k r, E (k, r) = (Fin.cons k (eM.symm r).1, (eM.symm r).2) := fun k r => rfl
    have hb := hS.bound σ (j + t) (by omega) (fun k => u (β 0, k)) _
      (fun r => (∏ q, u (Fin.tail β q, (eM.symm r).1 q)) * c (eM.symm r).2) (fun r => g' (eM.symm r))
      (fun p => g (E p)) (fun k r => by
        rw [hE, hg, word_succ]
        rfl)
    have hq := cnrm_equiv (S.nm (j + t)) σ eM.symm (fun p => (∏ q, u (Fin.tail β q, p.1 q)) * c p.2) g'
    have h1 := cnrm_equiv (S.nm (j + t + 1)) σ E (fun p => (∏ q, u (β q, p.1 q)) * c p.2) g
    have hc : ∀ p, (∏ q, u (β q, (E p).1 q)) * c (E p).2 =
        u (β 0, p.1) * ((∏ q, u (Fin.tail β q, (eM.symm p.2).1 q)) * c (eM.symm p.2).2) := fun p => by
      obtain ⟨k, r⟩ := p
      rw [hE]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      ring
    simp only [hc] at h1
    rw [hu, mul_one, hq] at hb
    rw [← h1]
    calc _ ≤ _ := hb
      _ ≤ Real.sqrt S.beta * (Real.sqrt S.beta ^ t * cnrm (S.nm j) σ c f) :=
        mul_le_mul_of_nonneg_left h₀ (Real.sqrt_nonneg _)
      _ = _ := by ring

end GlobalTheory.HSShort.ColNorm


open GlobalTheory.HSShort.ColNorm in
theorem GlobalTheory.HSShort.cnrm_col_le : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (κ : S.Col) (σ : F →+* ℂ) (u : Fin (S.D + 1) × Fin S.N → ℂ), (∀ i, frameNorm (S.fr σ) (fun j => u (i, j)) = 1) → cnrm (S.nm S.T) σ (fun i => eval₂ σ u (coordP S.mul (c i) κ.β (κ.x : A))) b ≤ Real.sqrt S.beta ^ κ.t * (S.nm κ.j).nrm σ κ.x := by
  intro F A _ _ _ _ _ _ S hS d b c hc κ σ u hu
  obtain ⟨j, t, hjt, β, x⟩ := κ
  have hmem := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j t (by omega)).1
  let g : (Fin t → Fin S.N) × Fin 1 → S.V S.T := fun p =>
    ⟨word S.mul (fun q => Pi.single (p.1 q) 1) (x : A), by rw [← hjt]; exact hmem _ _ x.2⟩
  have key := cnrm_words_le S hS σ u hu t β j S.T hjt le_rfl 1 (fun _ => 1) (fun _ => x) g (fun _ _ => rfl)
  have hr : cnrm (S.nm j) σ (fun _ : Fin 1 => (1 : ℂ)) (fun _ => x) = (S.nm j).nrm σ x := by
    simp [cnrm, csq, HermFam.nrm]
  rw [hr] at key
  refine le_of_eq_of_le ?_ key
  unfold cnrm
  congr 1
  calc _ = csq (S.nm S.T) σ (fun i => ∑ p, ((∏ q, u (β q, p.1 q)) * 1) * σ (b.repr (g p) i)) b := by
        congr 1
        funext i
        simp only [coordP, eval₂_sum, eval₂_mul, eval₂_C, eval₂_prod, eval₂_X, Fintype.sum_prod_type,
          Finset.univ_unique, Finset.sum_singleton, mul_one]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← hc i (g (e, default))]
        simp [g, mul_comm]
    _ = csq (S.nm S.T) σ (fun p => (∏ q, u (β q, p.1 q)) * 1) (fun p => ∑ i, b.repr (g p) i • b i) :=
        (csq_comb _ _ _ _ _).symm
    _ = _ := by simp only [b.sum_repr]
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAwayCpt

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlobalTheory.DenAway

theorem exists_nat_mul_integral_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q →
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  intro p _ Q hQ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hQ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun x hx v => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hxa' : (m a : AfP p) * x ∈ intAfP p := hxa
  have e : ((∏ a ∈ t, m a : ℕ) : AfP p) * x = (k : AfP p) * ((m a : AfP p) * x) := by
    rw [hk, Nat.cast_mul]; ring
  rw [e, eval_natCast_mul]
  exact mul_mem (natCast_mem v.1 k) (hxa' v)

end GlobalTheory.DenAwayCpt
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  first | (exact @GlobalTheory.ratint_away) | (exact GlobalTheory.ratint_away) | (intros; apply GlobalTheory.ratint_away  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.diagonal_sign_of_positive_eigenvector_one_positive : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  first | (exact @GlobalTheory.diag_sign_of_pos_eigenvector) | (exact GlobalTheory.diag_sign_of_pos_eigenvector) | (intros; apply GlobalTheory.diag_sign_of_pos_eigenvector  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eigenvalue_normSq_of_similitude_hermitian_signature : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  first | (exact @GlobalTheory.eig_norm_sq_of_similitude) | (exact GlobalTheory.eig_norm_sq_of_similitude) | (intros; apply GlobalTheory.eig_norm_sq_of_similitude <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.similitude_signature_one_preserves_posDef_form : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  first | (exact @GlobalTheory.similitude_preserves_posDef) | (exact GlobalTheory.similitude_preserves_posDef) | (intros; apply GlobalTheory.similitude_preserves_posDef  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.conjugate_place_lies_over : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ → LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  first | (exact @GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver) | (exact GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver) | (intros; apply GlobalTheory.StabFinOver.liesOver_comp_complexConj_of_not_liesOver  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C), (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  first | (exact @GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero) | (exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero) | (intros; apply GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.embeddings_real_independent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) (e : Fin k → G.C), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => (fun w i l => G.psi w (e j) i l : InfinitePlace G.F → Fin G.n → Fin G.n → ℂ)) := by
  first | (exact @GlobalTheory.LKCx.psi_linearIndependent_real) | (exact GlobalTheory.LKCx.psi_linearIndependent_real) | (intros; apply GlobalTheory.LKCx.psi_linearIndependent_real  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k := by
  first | (exact @GlobalTheory.charpoly_coeff_continuous_GAf) | (exact GlobalTheory.charpoly_coeff_continuous_GAf) | (intros; apply GlobalTheory.charpoly_coeff_continuous_GAf  <;> assumption)
end

section

open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

theorem _root_.GlobalTheory.T.strictNormalCrossings_descent_etale_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  first | exact @GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | exact GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion | (intros; apply GlobalTheory.SncDescent.exists_rsp_of_isEtaleCompletion <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem exists_primeFactor_mem_of_natCast_mem {D : D7} (w : Pl D.host.E) {M : ℕ} (hM : M ≠ 0)
    (h : (M : 𝓞 D.host.E) ∈ w.asIdeal) : ∃ p ∈ M.primeFactors, (p : 𝓞 D.host.E) ∈ w.asIdeal := by
  have e := Nat.prod_factorization_pow_eq_self hM
  rw [← e, Finsupp.prod, Nat.cast_prod] at h
  obtain ⟨p, hp, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  refine ⟨p, by simpa [Nat.support_factorization] using hp, ?_⟩
  rw [Nat.cast_pow] at hmem
  exact w.isPrime.mem_of_pow_mem _ hmem

theorem natCast_mem_of_under_eq {D : D7} (w : Pl D.host.E) {v : Pl D.host.F} (h : w.under (𝓞 D.host.F) = v) (n : ℕ)
    (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  subst h
  have : (n : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hn
  rw [Ideal.mem_comap, map_natCast] at this
  exact this

theorem exists_std_primes : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D T L sc G U hU
  set N : ℕ := D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK with hN
  set A : ℕ := ∏ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal with hA
  set B : ℕ := ∏ t ∈ hU.toFinset, ∏ w' ∈ L.Q t, Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal with hB
  have hN0 : N ≠ 0 := by
    have h1 := D.host.hyp.1.ne_zero
    have h2 := D.host.hyp.2.1.ne_zero
    have h3 := (D.host.g_prime 0).ne_zero
    have h4 := (D.host.g_prime 1).ne_zero
    have h5 : Ideal.absNorm D.host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    have h0 : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4) h5
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hB0 : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    intro t _
    rw [Finset.prod_ne_zero_iff]
    intro w' _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (w'.under (𝓞 D.host.F)).ne_bot
  have hM0 : N * A * B ≠ 0 := mul_ne_zero (mul_ne_zero hN0 hA0) hB0
  refine ⟨(N * A * B).primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro w hw
  have key : ∀ n : ℕ, n ∣ N * A * B → (n : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro n hn hmem
    obtain ⟨k, hk⟩ := hn
    have hM : ((N * A * B : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem
    obtain ⟨p, hp, hpm⟩ := exists_primeFactor_mem_of_natCast_mem w hM0 hM
    exact hw p hp hpm
  refine ⟨fun hv => ?_, fun t ht w' hw' heq => ?_, key N (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)⟩
  · apply key (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _) _
    · exact natCast_mem_of_under_eq w rfl _ (Ideal.absNorm_mem _)
  · apply key (Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem (fun w'' : Pl D.host.E => Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) hw').trans
        (Finset.dvd_prod_of_mem (fun t => ∏ w'' ∈ L.Q t, Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal)
          (hU.mem_toFinset.2 ht))) _
    · exact natCast_mem_of_under_eq w heq _ (Ideal.absNorm_mem _)

end GlobalTheory.FunObj
end
