module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_mul_Sb {g : ℕ} {H Sb : Matrix (Fin g) (Fin g) ℂ} {ev : Fin g → ℂ}
    (h : H * Sb = Sb * Matrix.diagonal ev) (i : ℕ) :
    H ^ i * Sb = Sb * Matrix.diagonal (fun j => ev j ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [_root_.pow_succ, _root_.mul_assoc, h, ← _root_.mul_assoc, ih, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp only [_root_.pow_succ]

private theorem sum_mul_Sb {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {a : 𝓞 F →+* O} {H Sb : Matrix (Fin g) (Fin g) ℂ}
    {ty : Fin g → (F →+* ℂ)} {ev : Fin g → ℂ} (hD : IsDiag a ρ H Sb ty ev) (q : (𝓞 F)[X]) :
    (q.sum fun i b => ρ (a b) * H ^ i) * Sb =
      Sb * Matrix.diagonal (fun j => ((q.map (algebraMap (𝓞 F) F)).map (ty j)).eval (ev j)) := by
  obtain ⟨-, hc, hH⟩ := hD
  have key : ∀ (i : ℕ) (b : 𝓞 F), ρ (a b) * H ^ i * Sb =
      Sb * Matrix.diagonal (fun j => ty j (b : F) * ev j ^ i) := by
    intro i b
    rw [_root_.mul_assoc, pow_mul_Sb hH i, ← _root_.mul_assoc, hc b, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
  simp only [Polynomial.sum_def, Finset.sum_mul, key, ← Finset.mul_sum]
  congr 1
  ext k l
  simp only [Matrix.sum_apply, Matrix.diagonal_apply, Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  split_ifs with hkl
  · subst hkl
    rfl
  · simp

theorem UpperTheory.Gal.W2.rootsFull_of :
    UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.PowSumRat → UpperTheory.Gal.W2.NewtonPoly → UpperTheory.Gal.W2.KillsMat → UpperTheory.Gal.W2.RootsFull := by
  intro hTC hPS hNP hKM F _ _ O _ bar g ρ a n t₀ ε hS D P₀ hP ga H hga Sb ty ev hD χ hχ hdeg τ
  have hcard : ∀ σ, (evFull ty ev σ).card = n :=
    fun σ => (hTC F O bar g ρ a n t₀ ε hS H Sb ty ev hD σ).2
  obtain ⟨ψ, hψm, hψd, hψ⟩ :=
    hNP F n (evFull ty ev) hcard (hPS F O bar g ρ a D P₀ hP ga H hga Sb ty ev hD)
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (𝓞 F)) ψ
  set q := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 F)) ψ
  have hb' : q.map (algebraMap (𝓞 F) F) = Polynomial.C (algebraMap (𝓞 F) F (b : 𝓞 F)) * ψ := by
    rw [hb, Polynomial.C_mul', algebraMap_smul]
  have h0 : (fun j => ((q.map (algebraMap (𝓞 F) F)).map (ty j)).eval (ev j)) = 0 := by
    funext j
    have hmem : ev j ∈ evFull ty ev (ty j) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨j, by simp, rfl⟩))
    rw [hb', Polynomial.map_mul, Polynomial.eval_mul, hψ (ty j), Polynomial.eval_multiset_prod,
      Pi.zero_apply]
    apply mul_eq_zero_of_right
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.2 ⟨ev j, hmem, by simp⟩
  have h1 := sum_mul_Sb hD q
  rw [h0, show Matrix.diagonal (0 : Fin g → ℂ) = 0 from Matrix.diagonal_zero,
    Matrix.mul_zero] at h1
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hD.1
  have hsum : (q.sum fun i c => ρ (a c) * H ^ i) = 0 := by
    rw [← Matrix.mul_one (q.sum fun i c => ρ (a c) * H ^ i), ← Matrix.mul_nonsing_inv Sb hu,
      ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have hk := (hKM F O bar g ρ a D P₀ hP ga H hga q).2 hsum
  have hdvd : χ ∣ ψ := by
    have := (hχ.2 q).1 hk
    rw [hb'] at this
    have hne : algebraMap (𝓞 F) F (b : 𝓞 F) ≠ 0 :=
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbmem)
    exact (Polynomial.dvd_C_mul hne).1 this
  have heq : ψ = χ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hχ.1 hψm hdvd (by rw [hψd, hdeg])
  show (Polynomial.map τ χ).roots = _
  rw [← heq, hψ τ, Polynomial.roots_multiset_prod_X_sub_C]
end

section

noncomputable section

open NumberField Polynomial
open scoped Matrix Classical

namespace UpperTheory.Gal.W2

private theorem emb_eq_of_coeffs {F : Type} [Field F] [NumberField F] (N m : (F →+* ℂ) → ℕ)
    (h : ∀ c : 𝓞 F, ∑ τ : F →+* ℂ, (N τ : ℂ) * τ (c : F) = ∑ τ : F →+* ℂ, (m τ : ℂ) * τ (c : F)) :
    ∀ τ, N τ = m τ := by
  let f : (F →+* ℂ) → (𝓞 F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 F) F)).toMonoidHom
  have hf : Function.Injective f := by
    intro σ τ hστ
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact DFunLike.congr_fun hστ c
  have hli := (linearIndependent_monoidHom (𝓞 F) ℂ).comp f hf
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun τ => (N τ : ℂ) - m τ) (by
    funext c
    have hc := h c
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [f, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact hc)
  intro τ
  have := key τ
  rw [sub_eq_zero] at this
  exact_mod_cast this

theorem typeCount_of : TypeCount := by
  intro F _ _ O _ bar g ρ a n t₀ ε hS H Sb ty ev hD
  obtain ⟨hdet, hρ, -⟩ := hD
  have hU : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have htr : ∀ c : 𝓞 F, (ρ (a c)).trace
      = ∑ τ : F →+* ℂ, ((Finset.univ.filter (fun i => ty i = τ)).card : ℂ) * τ (c : F) := by
    intro c
    have e1 : ρ (a c) = Sb * Matrix.diagonal (fun i => (ty i) (c : F)) * Sb⁻¹ := by
      rw [← hρ c, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
    rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU,
      Matrix.one_mul, Matrix.trace_diagonal]
    rw [← Finset.sum_fiberwise Finset.univ ty (fun i => (ty i) (c : F))]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => τ (c : F)) (fun i hi => by
      rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ τ, (Finset.univ.filter (fun i => ty i = τ)).card = typeMult n t₀ ε τ := by
    refine emb_eq_of_coeffs _ _ (fun c => ?_)
    rw [← htr c, hS.tr c]
  have hcard : ∀ τ, (evAt ty ev τ).card = typeMult n t₀ ε τ := by
    intro τ
    rw [← hcount τ, evAt, Multiset.card_map]
    rfl
  have hconj : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  intro τ
  refine ⟨hcard τ, ?_⟩
  rw [evFull, Multiset.card_add, Multiset.card_map, hcard, hcard]
  have hpos := hS.pos
  by_cases h0 : τ = t₀
  · subst h0
    have hne : ComplexEmbedding.conjugate τ ≠ τ := hS.cx τ
    simp only [typeMult, if_true, if_neg hne]
    omega
  · by_cases h1 : τ = ComplexEmbedding.conjugate t₀
    · subst h1
      rw [hconj]
      simp only [typeMult, if_neg h0, if_true]
      omega
    · have h2 : ComplexEmbedding.conjugate τ ≠ t₀ := by
        intro e; apply h1; rw [← e, hconj]
      have h3 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := by
        intro e; apply h0; rw [← hconj τ, e, hconj]
      simp only [typeMult, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
      rw [← Nat.mul_add, hS.eps τ h0 h1, Nat.mul_one]

end UpperTheory.Gal.W2
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open scoped Classical in
private theorem prod_ty {F : Type} [Field F] {g : ℕ} [Fintype (F →+* ℂ)]
    (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ)
    (f : (F →+* ℂ) → ℂ → ℂ) :
    ∏ i, f (ty i) (ev i) = ∏ τ, ((evAt ty ev τ).map (f τ)).prod := by
  unfold evAt
  simp only [Multiset.map_map, Function.comp_def]
  rw [← Finset.prod_fiberwise Finset.univ ty (fun i => f (ty i) (ev i))]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i hi => ?_
  simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]

open scoped Classical in
theorem UpperTheory.Gal.W2.fibW_of :
    UpperTheory.Gal.W2.FibW := by
  intro F _ _ g n t₀ ε ty ev χ mu hcx hn heps hcard hrts hmu x y
  have invol := ComplexEmbedding.involutive_conjugate F
  obtain ⟨A, hA'⟩ : ∃ A : (F →+* ℂ) → ℂ,
      ∀ τ, A τ = ((evAt ty ev τ).map (fun r => 1 - τ x * (y * r))).prod := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B : (F →+* ℂ) → ℂ, ∀ τ, B τ =
      ((evAt ty ev (ComplexEmbedding.conjugate τ)).map
        (fun r => 1 - τ x * starRingEnd ℂ r)).prod := ⟨_, fun _ => rfl⟩
  have hA : ∏ i, (1 - ty i x * (y * ev i)) = ∏ τ, A τ := by
    simp only [hA']
    exact prod_ty ty ev (fun τ r => 1 - τ x * (y * r))
  have hB : starRingEnd ℂ (∏ i, (1 - ty i x * ev i)) = ∏ τ, B τ := by
    rw [map_prod]
    simp only [map_sub, map_one, map_mul]
    rw [prod_ty ty ev (fun τ r => 1 - starRingEnd ℂ (τ x) * starRingEnd ℂ r)]
    refine (Equiv.prod_comp (invol.toPerm _) _).symm.trans
      (Finset.prod_congr rfl fun τ _ => ?_)
    simp [hB', Function.Involutive.coe_toPerm, ComplexEmbedding.conjugate_coe_eq]
  have hmem : ComplexEmbedding.conjugate t₀ ∈ Finset.univ.erase t₀ :=
    Finset.mem_erase.2 ⟨hcx t₀, Finset.mem_univ _⟩
  have key : ∏ τ, (A τ * B τ) = A t₀ * B t₀ *
      (A (ComplexEmbedding.conjugate t₀) * B (ComplexEmbedding.conjugate t₀) *
        ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), (A τ * B τ)) := by
    rw [Finset.mul_prod_erase _ (fun τ => A τ * B τ) hmem,
      Finset.mul_prod_erase _ (fun τ => A τ * B τ) (Finset.mem_univ t₀)]
  have hrest : ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), (A τ * B τ) =
      ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀),
        ((rts χ τ).map (fun r => 1 - τ x * (y ^ ε τ * r))).prod := by
    refine Finset.prod_congr rfl fun τ hτ => ?_
    have h1 : τ ≠ ComplexEmbedding.conjugate t₀ := (Finset.mem_erase.1 hτ).1
    have h2 : τ ≠ t₀ := (Finset.mem_erase.1 (Finset.mem_erase.1 hτ).2).1
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h1 (by rw [← h, invol])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ :=
      fun h => h2 (invol.injective h)
    have he := heps τ h2 h1
    have hc1 : (evAt ty ev τ).card = n * ε τ := by simp [hcard, typeMult, h1, h2]
    have hc2 : (evAt ty ev (ComplexEmbedding.conjugate τ)).card =
        n * ε (ComplexEmbedding.conjugate τ) := by simp [hcard, typeMult, h3, h4]
    rw [hA', hB', hrts, evFull, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map]
    rcases (by omega : ε τ = 0 ∧ ε (ComplexEmbedding.conjugate τ) = 1 ∨
        ε τ = 1 ∧ ε (ComplexEmbedding.conjugate τ) = 0) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, Nat.mul_zero, Multiset.card_eq_zero] at hc1
      rw [hc1, e1]
      simp [Function.comp_def]
    · rw [e2, Nat.mul_zero, Multiset.card_eq_zero] at hc2
      rw [hc2, e1]
      simp [Function.comp_def]
  have hr0 : (rts χ t₀).erase mu = (evAt ty ev (ComplexEmbedding.conjugate t₀)).map (starRingEnd ℂ) := by
    rw [hrts, evFull, hmu, Multiset.singleton_add, Multiset.erase_cons_head]
  have hpair : A t₀ * B t₀ * (A (ComplexEmbedding.conjugate t₀) * B (ComplexEmbedding.conjugate t₀)) =
      (1 - t₀ x * (y * mu)) * (((rts χ t₀).erase mu).map (fun r => 1 - t₀ x * r)).prod *
        ((1 - starRingEnd ℂ (t₀ x) * starRingEnd ℂ mu) *
          (((rts χ t₀).erase mu).map
            (fun r => 1 - starRingEnd ℂ (t₀ x) * (y * starRingEnd ℂ r))).prod) := by
    rw [hr0, hA', hA', hB', hB', invol t₀, hmu]
    simp only [Multiset.map_map, Function.comp_def, Multiset.map_singleton, Multiset.prod_singleton,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    ring
  rw [hA, hB, ← Finset.prod_mul_distrib, key, hrest]
  unfold fibW
  rw [← hpair]
  ring
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem sep_of_integer {F : Type} [Field F] [NumberField F] {R : Type} [Ring R] [Algebra ℂ R]
    (f : 𝓞 F →+* R) (c : 𝓞 F) : ∃ p : ℂ[X], p.Separable ∧ aeval (f c) p = 0 := by
  have hint : IsIntegral ℤ (c : F) := RingOfIntegers.isIntegral_coe c
  refine ⟨(minpoly ℤ c).map (Int.castRingHom ℂ), ?_, ?_⟩
  · have hq : minpoly ℚ (c : F) = (minpoly ℤ (c : F)).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
    have hsep : (minpoly ℚ (c : F)).Separable := Algebra.IsSeparable.isSeparable ℚ (c : F)
    have hm := hsep.map (f := algebraMap ℚ ℂ)
    rw [hq, Polynomial.map_map, RingOfIntegers.minpoly_coe] at hm
    have e : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e] at hm
    exact hm
  · rw [aeval_def, eval₂_map]
    have e : (algebraMap ℂ R).comp (Int.castRingHom ℂ) = f.comp (algebraMap ℤ (𝓞 F)) :=
      RingHom.ext_int _ _
    rw [e, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem UpperTheory.Gal.W2.diagExists_of :
    UpperTheory.Gal.W2.SimDiag → UpperTheory.Gal.W2.ExtendEmb → UpperTheory.Gal.W2.KillsMat → UpperTheory.Gal.W2.HSep → UpperTheory.Gal.W2.DiagExists := by
  intro hSim hExt hKills hHSep F _ _ O _ bar g ρ a D P₀ hP ga H hH χ hmin hsep
  have hcomm : ∀ c : 𝓞 F, ρ (a c) * H = H * ρ (a c) := by
    intro c
    have hx : ∀ x : D.La, (ρ (a c) * H) *ᵥ P₀ x = (H * ρ (a c)) *ᵥ P₀ x := by
      intro x
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hH x, ← hP.1 (a c) (ga x),
        ← hP.1 (a c) x, ← hH (a c • x), LinearMap.map_smul]
    have hlin := GlobalTheory.PerCoordU.ext_per hP
      (f := ((ρ (a c) * H).mulVecLin).restrictScalars ℝ)
      (f' := ((H * ρ (a c)).mulVecLin).restrictScalars ℝ) (fun x => by simpa using hx x)
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hlin z
    simpa using hz
  obtain ⟨pH, hpHsep, hpH⟩ := hHSep F O bar g ρ a H hcomm χ hmin.1 hsep
    (fun q hq => (hKills F O bar g ρ a D P₀ hP ga H hH q).1 ((hmin.2 q).2 hq))
  obtain ⟨Sb, d, hdet, hM⟩ := hSim g (Option (𝓞 F))
    (fun o => Option.elim o H (fun c => ρ (a c))) (by
      rintro (_ | c) (_ | c')
      · rfl
      · exact (hcomm c').symm
      · exact hcomm c
      · show ρ (a c) * ρ (a c') = ρ (a c') * ρ (a c)
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]) (by
      rintro (_ | c)
      · exact ⟨pH, hpHsep, hpH⟩
      · exact sep_of_integer (ρ.comp a) c)
  have hU : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hdet
  have hMs : ∀ c : 𝓞 F, ρ (a c) * Sb = Sb * Matrix.diagonal (d (some c)) := fun c => hM (some c)
  have hd : ∀ c : 𝓞 F, Sb⁻¹ * ρ (a c) * Sb = Matrix.diagonal (d (some c)) := by
    intro c
    rw [Matrix.mul_assoc, hMs c, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
  have hent : ∀ (c : 𝓞 F) (i : Fin g), d (some c) i = (Sb⁻¹ * ρ (a c) * Sb) i i := by
    intro c i
    rw [hd c, Matrix.diagonal_apply_eq]
  let φ : Fin g → (𝓞 F →+* ℂ) := fun i =>
    { toFun := fun c => d (some c) i
      map_one' := by
        show d (some 1) i = 1
        rw [hent, map_one, map_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ hU, Matrix.one_apply_eq]
      map_mul' := fun c c' => by
        show d (some (c * c')) i = d (some c) i * d (some c') i
        have h1 := hd (c * c')
        have e : Sb⁻¹ * (ρ (a c) * ρ (a c')) * Sb
            = (Sb⁻¹ * ρ (a c) * Sb) * (Sb⁻¹ * ρ (a c') * Sb) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Sb (Sb⁻¹), Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
        rw [map_mul, map_mul, e, hd, hd, Matrix.diagonal_mul_diagonal] at h1
        have h2 := congrFun (congrFun h1 i) i
        simpa using h2.symm
      map_zero' := by
        show d (some 0) i = 0
        rw [hent, map_zero, map_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
      map_add' := fun c c' => by
        show d (some (c + c')) i = d (some c) i + d (some c') i
        rw [hent, hent, hent, map_add (f := _), map_add (f := _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] }
  have hτ := fun i => hExt F (φ i)
  choose ty hty using hτ
  refine ⟨Sb, ty, d none, ?_⟩
  refine ⟨hdet, fun c => ?_, hM none⟩
  rw [hMs c]
  congr 2
  funext i
  exact hty i c
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tspDiag_of :
    UpperTheory.Gal.W2.TspDiag := by
  intro F _ _ g ty t₀ i₀ hc hi hij W hW
  classical
  have hpat : ∀ S : Matrix (Fin g) (Fin g) ℂ, S ∈ W → ∀ i j, S i j ≠ 0 →
      ty j = ComplexEmbedding.conjugate (ty i) := by
    intro S hS i j hne
    have h := ((hW S).1 hS).2
    have hcc : ∀ c : 𝓞 F, ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := fun c =>
      mul_left_cancel₀ hne (by rw [h c i j, mul_comm])
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) ?_
    ext c
    simpa [ComplexEmbedding.conjugate_coe_eq] using hcc c
  have hi₀ : ty i₀ = t₀ := (hi i₀).2 rfl
  have hnot : ∀ j, ty j = ComplexEmbedding.conjugate t₀ → j ≠ i₀ := by
    rintro j hj rfl
    exact hc (by rw [← hj, hi₀])
  constructor
  · intro S S' hSS
    apply Subtype.ext
    have hzero : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → ∀ i j, i ≠ i₀ → j ≠ i₀ → T i j = 0 := by
      intro T hT i j hi' hj'
      by_contra hne
      rcases hij i j (hpat T hT i j hne) with h | h
      · exact hi' h
      · exact hj' h
    have hrow : ∀ j, S.1 i₀ j = S'.1 i₀ j := by
      intro j
      by_cases hj : ty j = ComplexEmbedding.conjugate t₀
      · exact congrFun hSS ⟨j, hj⟩
      · have hz : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → T i₀ j = 0 := by
          intro T hT
          by_contra hne
          exact hj (by rw [hpat T hT i₀ j hne, hi₀])
        rw [hz _ S.2, hz _ S'.2]
    have hsym : ∀ T : Matrix (Fin g) (Fin g) ℂ, T ∈ W → ∀ i j, T i j = T j i := by
      intro T hT i j
      have h := congrFun (congrFun ((hW T).1 hT).1 i) j
      rw [Matrix.transpose_apply] at h
      exact h.symm
    ext i j
    by_cases h1 : i = i₀
    · subst h1; exact hrow j
    · by_cases h2 : j = i₀
      · subst h2
        rw [hsym _ S.2, hsym _ S'.2]; exact hrow i
      · rw [hzero _ S.2 i j h1 h2, hzero _ S'.2 i j h1 h2]
  · intro v
    let T : Matrix (Fin g) (Fin g) ℂ := fun i j =>
      if h : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀ then v ⟨j, h.2⟩
      else if h' : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀ then v ⟨i, h'.2⟩ else 0
    have hT : T ∈ W := by
      refine (hW T).2 ⟨?_, ?_⟩
      · ext i j
        show T j i = T i j
        by_cases h1 : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀
        · have h2 : ¬ (j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀) := fun h => hnot j h1.2 h.1
          simp only [T, dif_pos h1, dif_neg h2]
        · by_cases h2 : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀
          · simp only [T, dif_pos h2, dif_neg h1]
          · simp only [T, dif_neg h1, dif_neg h2]
      · intro c i j
        by_cases h1 : i = i₀ ∧ ty j = ComplexEmbedding.conjugate t₀
        · simp only [T, dif_pos h1]
          have e : ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := by
            rw [h1.2, h1.1, hi₀, ComplexEmbedding.conjugate_coe_eq]
          rw [e, mul_comm]
        · by_cases h2 : j = i₀ ∧ ty i = ComplexEmbedding.conjugate t₀
          · simp only [T, dif_neg h1, dif_pos h2]
            have e : ty j (c : F) = (starRingEnd ℂ) (ty i (c : F)) := by
              rw [h2.2, h2.1, hi₀, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
            rw [e, mul_comm]
          · simp only [T, dif_neg h1, dif_neg h2]
            simp
    refine ⟨⟨T, hT⟩, ?_⟩
    funext j
    show T i₀ j.1 = v j
    have h1 : i₀ = i₀ ∧ ty j.1 = ComplexEmbedding.conjugate t₀ := ⟨rfl, j.2⟩
    simp only [T, dif_pos h1]
end

section

open NumberField

namespace UpperTheory.Gal.W2

theorem extendEmb_of : ExtendEmb := by
  intro F _ _ φ
  have hker : RingHom.ker φ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hn
    rw [Ideal.mem_bot]
    exact_mod_cast hn
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  refine ⟨IsFractionRing.lift (K := F) hinj, fun c => ?_⟩
  exact (IsFractionRing.lift_algebraMap (K := F) hinj c).symm

end UpperTheory.Gal.W2
end
