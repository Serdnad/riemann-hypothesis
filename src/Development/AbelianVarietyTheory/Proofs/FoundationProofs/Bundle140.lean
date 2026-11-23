module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefPosEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnit
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle128
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle134
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) → h ∈ Algebra.adjoin Ω {X.jK} := by
  first | exact @GlobalTheory.KZ.LevelOne.mem_adjoin_j | exact GlobalTheory.KZ.LevelOne.mem_adjoin_j | (intros; apply GlobalTheory.KZ.LevelOne.mem_adjoin_j <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gamma_mul_le (m k : ℕ) : CongruenceSubgroup.Gamma (m * k) ≤ CongruenceSubgroup.Gamma m := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c := fun (x : ℤ) (y : ZMod (m * k)) (e : (x : ZMod (m * k)) = y) =>
    congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ _ h1
  · simpa using c _ _ h2
  · simpa using c _ _ h3
  · simpa using c _ _ h4

theorem inR_cmp : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  intro E g f hE ⟨N, w, hN, hinv, hexp⟩
  obtain ⟨n₁, hn₁, hH⟩ := GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius g
  obtain ⟨n₂, hn₂, hC⟩ := GlobalTheory.T.glTwoPosRat_conj_principal_congruence g
  obtain ⟨mob_hs, mob_mul, mob_one, mob_sl, mob_diff, mob_up⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨cmp_one, cmp_mul, cmp_sl, cmp_up⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨N * n₁ * n₂, w * n₁, by positivity, ?_, ?_⟩
  · intro δ hδ τ
    have hδ' : δ ∈ CongruenceSubgroup.Gamma (N * n₂) := by
      have : N * n₁ * n₂ = N * n₂ * n₁ := by ring
      rw [this] at hδ
      exact gamma_mul_le _ _ hδ
    obtain ⟨δ', hδ'm, hgδ⟩ := hC N δ hδ'
    have e1 : GlobalTheory.FN.cmp (g * ofSL δ) f = fun τ => GlobalTheory.FN.cmp g f (δ • τ) := by
      rw [cmp_mul, cmp_sl]
    have e2 : GlobalTheory.FN.cmp (ofSL δ' * g) f = GlobalTheory.FN.cmp g f := by
      rw [cmp_mul, cmp_sl]
      congr 1
      funext σ
      exact hinv δ' hδ'm σ
    have := congrFun (e1.symm.trans (hgδ ▸ e2)) τ
    exact this
  · intro γ₀
    obtain ⟨γ, a, d, b, had, hmob⟩ := hH γ₀
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have key := GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst E N w a d b (fun τ => f (γ • τ)) hE hN ha hd (hexp γ)
    rw [had] at key
    have hlift := QAll.of_dvd (N := N * n₁) (N' := N * n₁ * n₂) (by positivity) (dvd_mul_right _ _)
      (p := (· ∈ E)) (Subring.zero_mem E) key
    convert hlift using 2 with τ
    congr 1
    have hz : (((a : ℂ) * τ + b) / d).im > 0 := by
      have : (((a : ℂ) * τ + b) / d) = ((a : ℝ) / d : ℝ) * (τ : ℂ) + ((b : ℝ) / d : ℝ) := by
        push_cast; field_simp
      rw [this]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have : (0 : ℝ) < (a : ℝ) / d := by positivity
      have := τ.im_pos
      simp only [UpperHalfPlane.coe_im]
      positivity
    show up f (mob g ((γ₀ • τ : ℍ) : ℂ)) = up (fun τ => f (γ • τ)) (((a : ℂ) * τ + b) / d)
    have hzc : ((UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hm : mob (ofSL γ) (((a : ℂ) * τ + b) / d) =
        ((γ • UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) := by
      rw [← mob_sl, hzc]
    simp only [up]
    rw [hmob τ, hm, UpperHalfPlane.ofComplex_apply]

end GlobalTheory.FN
end

section

open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.UnitPiece Finset

theorem _root_.GlobalTheory.T.primitiveCharacter_entry_sum_eisenstein_product : ∀ (p m N k : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K], 1 ≤ m → 0 < N → ¬ p ∣ N → 3 ≤ k → ∀ (ψ : DirichletCharacter K (p ^ m)), ψ.IsPrimitive → ∀ (ζ : K), IsPrimitiveRoot ζ (N * p ^ m) → ∀ (a₀ b₀ t : ℤ), (p : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∀ (i j : ℕ), ∑ u ∈ primeTo p m, ∑ a : ZMod (p ^ m), ∑ v ∈ primeTo p m, ∑ b : ZMod (p ^ m), ψ (u * b - a * v) * (coefPos (k - 1) (N * p ^ m) ζ (N * u.val + (p : ℤ) ^ m * (a₀ * t)) (N * a.val) i * coefPos 1 (N * p ^ m) ζ (N * v.val + (p : ℤ) ^ m * (b₀ * t)) (N * b.val) j) = if p ^ m ∣ i + j then (p : K) ^ m * gaussS p m ψ (ζ ^ N) * ψ⁻¹ (N : ZMod (p ^ m)) * (((N * p ^ m : ℕ) : K) ^ (k - 2))⁻¹ * (ffMu N p m k ψ a₀ i * eeMu N p m ψ b₀ j) else 0 := by
  first | exact @GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum | exact GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum | (intros; apply GlobalTheory.KummerEisensteinGalois.UnitPieceMu.entry_sum <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem isEig_translate_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  intro G V _ _ _ _ _ π hπ J N₀ N₁ θ z hJ hN hsub hconj hdec u u' hu hu' hd
  have hmul : ∀ (a b : G) (v : V), π a (π b v) = π (a * b) v := fun a b v => by
    rw [map_mul]; rfl
  have hw' : IsEig π N₀ (fun _ => 1) (π z u') := by
    intro y hy
    have h1 : z⁻¹ * y * z ∈ N₁ := (hconj _).2 (by
      have : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [this]; exact hy)
    have h2 := hu' _ h1
    have h3 : y * z = z * (z⁻¹ * y * z) := by group
    rw [hmul, h3, ← hmul, h2, map_smul]
  have hmap : ∀ x ∈ aug π N₁ (fun _ => 1), π z x ∈ aug π N₀ (fun _ => 1) := by
    intro x hx
    have : aug π N₁ (fun _ => 1) ≤ (aug π N₀ (fun _ => 1)).comap (π z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, hh, w, rfl⟩
      refine Submodule.subset_span ⟨z * h * z⁻¹, (hconj h).1 hh, π z w, ?_⟩
      rw [map_sub, map_smul, hmul, hmul]
      congr 3
      group
    exact this hx
  have hww : π z u - π z u' ∈ aug π N₀ (fun _ => 1) := by
    rw [← map_sub]; exact hmap _ hd
  obtain ⟨R, hR1, hRJ, hS⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ J θ hJ (π z u)
  have hterm : ∀ j ∈ R, (θ j)⁻¹ • π j (π z u) - π z u ∈ aug π N₀ (fun _ => 1) := by
    intro j hj
    have hjJ := hRJ j hj
    obtain ⟨y, hy, h1, h2⟩ := hdec j hjJ
    have hne : θ j ≠ 0 := by
      intro h0
      have := hJ.val_mul j hjJ j⁻¹ (hJ.inv j hjJ)
      rw [mul_inv_cancel, hJ.val_one, h0, zero_mul] at this
      exact one_ne_zero this
    have h3 := hu _ h1
    have h4 : j * z = y * (z * (z⁻¹ * (y⁻¹ * j) * z)) := by group
    have h5 : π j (π z u) = θ j • π y (π z u) := by
      rw [hmul, h4, ← hmul, ← hmul, h3, h2, map_smul, map_smul]
    rw [h5, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact Submodule.subset_span ⟨y, hy, π z u, by rw [one_smul]⟩
  set S : V := ∑ j ∈ R, (θ j)⁻¹ • π j (π z u) with hSdef
  have hc : (R.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨1, hR1⟩).ne'
  have hA : S - (R.card : ℂ) • π z u ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.sum_mem _ hterm
    rwa [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ] at this
  have hB : S - (R.card : ℂ) • π z u' ∈ aug π N₀ (fun _ => 1) := by
    have := Submodule.add_mem _ hA (Submodule.smul_mem _ (R.card : ℂ) hww)
    rwa [smul_sub, sub_add_sub_cancel] at this
  have hC : IsEig π N₀ (fun _ => 1) (S - (R.card : ℂ) • π z u') := by
    intro y hy
    rw [map_sub, map_smul, hS y (hsub y hy).1, (hsub y hy).2, hw' y hy]
    simp
  have h0 := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ N₀ _ hN).1 _ hB hC
  have hE : π z u' = (R.card : ℂ)⁻¹ • S := by
    rw [sub_eq_zero.1 h0, smul_smul, inv_mul_cancel₀ hc, one_smul]
  intro j hj
  rw [hE, map_smul, hS j hj, smul_comm]

end GlobalTheory.PsType
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit :
    ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (k : ℕ) (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' →
        (Cong (p := p) k x 0 ↔ ∀ r, Cong (p := p) k (c r) 0) ∧
          ((∃ r, c r ≠ 0 ∧ IsInt (p := p) (c r)⁻¹) → x ≠ 0 ∧ IsInt (p := p) x⁻¹) :=
  GlobalTheory.Glue.ev_cong_iff_and_unit
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  first | exact @GlobalTheory.Glue.isDl_calc | exact GlobalTheory.Glue.isDl_calc | (intros; apply GlobalTheory.Glue.isDl_calc <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P : HahnSeries ℚ Ω), 0 < L → Prim A P → (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → ∃ Q : HahnSeries ℚ Ω, (∀ r, Q.coeff r ∈ A) ∧ (∀ r : ℚ, Q.coeff r ≠ 0 → (r * L).den = 1) ∧ ∀ r, CgA A l n ((Q * P).coeff r) ((1 : HahnSeries ℚ Ω).coeff r) := by
  first | exact @GlobalTheory.prim_inv_mod_pow | exact GlobalTheory.prim_inv_mod_pow | (intros; apply GlobalTheory.prim_inv_mod_pow <;> assumption)
end

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem dehH_mon (w : ℕ) (i : Fin (w + 1)) : deh (mon ℂ w i) = Polynomial.X ^ (i : ℕ) := by
  simp [deh, mon]

theorem dehH_slP_mon (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i : ℕ) :
    deh (slP m (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (w - i))) =
      (Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
        (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [deh, slP, Polynomial.smul_eq_C_mul]

theorem dehH_expand (w : ℕ) (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous w) :
    deh p = ∑ i ∈ Finset.range (w + 1),
      Polynomial.C (AddMonoidAlgebra.coeff p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) * Polynomial.X ^ i := by
  have h := (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp
  conv_lhs => rw [h]

  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (AddMonoidAlgebra.coeff
  p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) * Polynomial.X ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, dehH_mon]
  simp [deh]

theorem dehH_coeff (w : ℕ) (c : ℕ → ℂ) (j : ℕ) (hj : j < w + 1) :
    (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i).coeff j = c j := by
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, hj]

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

theorem dehH_slP_sum (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (c : ℕ → ℂ) :
    GlobalTheory.HeckeFamilyMatrices.slP w m (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i) =
      ∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  rw [GlobalTheory.HeckeFamilyMatrices.slP, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, Polynomial.lcoeff_apply,
    LinearMap.toSpanSingleton_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dehH_coeff w c i (Finset.mem_range.mp hi), Polynomial.smul_eq_C_mul]

theorem dehH_sum_eq (w : ℕ) (q : Polynomial ℂ) (hq : q ∈ Polynomial.degreeLT ℂ (w + 1)) :
    ∑ i ∈ Finset.range (w + 1), Polynomial.C (q.coeff i) * Polynomial.X ^ i = q := by
  ext j
  by_cases hj : j < w + 1
  · exact dehH_coeff w _ j hj
  · rw [Polynomial.finsetSum_coeff]
    rw [Polynomial.mem_degreeLT] at hq
    have h0 : q.coeff j = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hq (by exact_mod_cast not_lt.mp hj))
    rw [h0]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    have : j ≠ i := fun h => hj (h ▸ Finset.mem_range.mp hi)
    simp [this]

theorem deh_homog_iso : ∀ w : ℕ, (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous w → deh (slP m p) = GlobalTheory.HeckeFamilyMatrices.slP w m (deh p)) ∧ (∀ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → deh p ∈ Polynomial.degreeLT ℂ (w + 1)) ∧ (∀ q ∈ Polynomial.degreeLT ℂ (w + 1), ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w ∧ deh p = q) ∧ (∀ p p' : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → p'.IsHomogeneous w → deh p = deh p' → p = p') := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m p hp
    have h := (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp
    rw [dehH_expand w p hp, dehH_slP_sum]
    conv_lhs => rw [h]

    rw [map_sum, map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (AddMonoidAlgebra.coeff
    p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) *
      ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
        (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, MvPolynomial.algHom_C, mon, dehH_slP_mon]
    simp [deh]
  · intro p hp
    rw [dehH_expand w p hp]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Polynomial.mem_degreeLT]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    have := Finset.mem_range.mp hi
    exact_mod_cast this
  · intro q hq
    refine ⟨∑ i : Fin (w + 1), MvPolynomial.C (q.coeff i) * mon ℂ w i, ?_, ?_⟩
    · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
        ((GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.2.1 i).C_mul _
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      simp only [map_mul, dehH_mon]
      simp only [deh, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i)]
      exact dehH_sum_eq w q hq
  · intro p p' hp hp' he
    rw [(GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp, (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p' hp']
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := dehH_coeff w (fun i => AddMonoidAlgebra.coeff p (Finsupp.single 0 i + Finsupp.single 1 (w - i))) i i.2
    have h2 := dehH_coeff w (fun i => AddMonoidAlgebra.coeff p' (Finsupp.single 0 i + Finsupp.single 1 (w - i))) i i.2
    rw [← dehH_expand w p hp, he, dehH_expand w p' hp', h2] at h1
    rw [h1]

end GlobalTheory.KZ.H3
end
end

section

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem relTriv_gamma_of_dvd {N M : ℕ} (h : N ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨a, b, c, d⟩ := hδ
  have e : ∀ x : ℤ, ((x : ZMod M).cast : ZMod N) = (x : ZMod N) := fun x => ZMod.cast_intCast h x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, a]; simp [ZMod.cast_one h]
  · rw [← e, b]; simp
  · rw [← e, c]; simp
  · rw [← e, d]; simp [ZMod.cast_one h]

theorem toZModPow_eval_mulVec {l : ℕ} [Fact l.Prime] (n : ℕ) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n)) (u : Fin 2 → ℤ_[l]) (q : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval
      (((δ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℤ_[l]) *ᵥ u) q) =
      PadicInt.toZModPow n (MvPolynomial.eval u q) := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  obtain ⟨a, b, c, d⟩ := hδ
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval]
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  have e : ∀ x : ℤ, PadicInt.toZModPow n ((x : ℤ_[l])) = (x : ZMod (l ^ n)) := fun x => map_intCast _ x
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, e, a, b, c, d]

theorem rel_triv_eq_zero : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ →
      ∀ b F, Rel X l b F → F ∈ Triv ℤ_[l] w Γ → b = 0 := by
  intro Ω _ _ ε X l _ w Γ M₀ hM₀ hΓ b F hR hF
  obtain ⟨ψ, p, hψ, hFψ⟩ := hF
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, hK, M₁, hM₁, hχ⟩ := hR u n
  change AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n ((0 : X.Fn l) u)
  rw [Pi.zero_apply, map_zero]
  refine GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence Ω ε X l n (b u) χ hK ⟨M₁ * M₀ * l ^ n, ?_, fun δ hδ => ?_⟩
  · have : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    positivity
  have h1 : δ ∈ CongruenceSubgroup.Gamma M₁ := relTriv_gamma_of_dvd ⟨M₀ * l ^ n, by ring⟩ hδ
  have h0 : δ ∈ Γ := hΓ (relTriv_gamma_of_dvd ⟨M₁ * l ^ n, by ring⟩ hδ)
  have hl : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := relTriv_gamma_of_dvd ⟨M₁ * M₀, by ring⟩ hδ
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hδI : mob (ofSL δ) Complex.I ∈ Hs := (GlobalTheory.T.glTwoPosRatMobius_basic_laws).1 _ _ hI
  have key := hχ δ h1 Complex.I hI
  beta_reduce at key
  rw [← key, hFψ _ hδI, hFψ _ hI, ← hψ δ h0 Complex.I hI]
  simp only [map_add (f := _), GlobalTheory.KZ.Betti.eval_slP, add_sub_add_right_eq_sub, map_sub,
    toZModPow_eval_mulVec n hl, sub_self, Pi.zero_apply]

end GlobalTheory.KZ.H3
end
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.integralConjugateSL2Int_laws : (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (M : ℕ), 0 < m.det → ∀ δ ∈ CongruenceSubgroup.Gamma (M * m.det.natAbs), m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (cj m δ : Matrix (Fin 2) (Fin 2) ℤ) * m ∧ cj m δ ∈ CongruenceSubgroup.Gamma M) ∧ (∀ γ δ : SL(2, ℤ), cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ = γ * δ * γ⁻¹) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (δ δ' : SL(2, ℤ)), 0 < m.det → m * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * m → ∀ z ∈ Hs, mob (toGQ m) (mob (ofSL δ) z) = mob (ofSL δ') (mob (toGQ m) z)) := by
  first | exact @GlobalTheory.KZ.cj_laws | exact GlobalTheory.KZ.cj_laws | (intros; apply GlobalTheory.KZ.cj_laws <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.exists_unique_normalizedCyclotomicTrace : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  first | exact @GlobalTheory.NTr.normTrace_exists_unique | exact GlobalTheory.NTr.normTrace_exists_unique | (intros; apply GlobalTheory.NTr.normTrace_exists_unique <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.UnitPow

theorem eq_unit_mul_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∀ b ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), b ≠ 0 → ∃ (n k : ℕ), 1 ≤ n ∧ ∃ u ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), ∃ u' ∈ Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq), u * u' = 1 ∧ b = u * (T.ζ n - 1) ^ k := by
  intro p _ Ω _ _ hclo T b hb hb0
  obtain ⟨n, ι, w, hn, hemb, hw, hmem⟩ := GlobalTheory.T.exists_level_emb_of_mem_adjoin_zeta_qq p Ω hclo T b hb
  obtain ⟨hdom, hdvr, hirr⟩ := GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel p n hn
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hw, map_zero])
  obtain ⟨k, ε, hε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hirr
  refine ⟨n, k, hn, ι (ε : On p n), hmem _, ι ((ε⁻¹ : (On p n)ˣ) : On p n), hmem _, ?_, ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← hw, hε, map_mul, map_pow, map_sub, map_one, hemb.1]

end GlobalTheory.K5.UnitPow
end
