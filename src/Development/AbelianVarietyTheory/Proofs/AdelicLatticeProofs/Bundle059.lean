module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle141
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle034
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle037
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

namespace GlobalTheory.NatMulIntegral

open NumberField

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]
    exact hi
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h', Int.cast_neg, neg_mul]
    exact hi.neg

theorem nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (d : ℕ) {x : Fin n → E} (hx : x ∈ L) :
    (d : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx d

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  apply GlobalTheory.PrincLat.exists_nat_smul_mem <;> assumption

end GlobalTheory.NatMulIntegral
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.descend_blockDiagPart_ratPoly_of_fibre_const : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∀ f : MvPolynomial (ι × ι) ℚ, (∀ x ∈ Γ, ∀ x' ∈ Γ, blk e x = blk e x' → ev f x = ev f x') → ∃ b : MvPolynomial (ι × ι) ℚ, ∀ x ∈ Γ, ev f x = ev b (blk e x) := by
  first | exact @GlobalTheory.ClassFin.descend_blk_rat | exact GlobalTheory.ClassFin.descend_blk_rat | (intros; apply GlobalTheory.ClassFin.descend_blk_rat <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatInvTensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordAlg (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Subalgebra ℂ (Matrix ι ι ℂ → ℂ) :=
  Algebra.adjoin ℂ {φ | ∃ p ∈ S, ∃ b, φ = fun y => ((fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 y) b}

def AllFixed (Γ : Set (Matrix ι ι ℂ)) (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Prop :=
  ∀ p ∈ S, ∀ g ∈ Γ, (fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 g = fun a => ((p.2 a : ℚ) : ℂ)

def Good (Γ : Set (Matrix ι ι ℂ)) (φ : Matrix ι ι ℂ → ℂ) : Prop :=
  ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧ φ ∈ coordAlg S

theorem coordAlg_mono {S T : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))} (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  apply Algebra.adjoin_mono
  rintro φ ⟨p, hp, b, rfl⟩
  exact ⟨p, h hp, b, rfl⟩

theorem good_zero (Γ : Set (Matrix ι ι ℂ)) : Good Γ 0 :=
  ⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩

theorem Good.add {Γ : Set (Matrix ι ι ℂ)} {φ ψ : Matrix ι ι ℂ → ℂ} (h1 : Good Γ φ) (h2 : Good Γ ψ) :
    Good Γ (φ + ψ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  obtain ⟨T, hT, fT, mT⟩ := h2
  refine ⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS)
    (coordAlg_mono Set.subset_union_right mT)⟩
  rintro p (hp | hp)
  · exact fS p hp
  · exact fT p hp

theorem Good.smul {Γ : Set (Matrix ι ι ℂ)} {φ : Matrix ι ι ℂ → ℂ} (c : ℂ) (h1 : Good Γ φ) :
    Good Γ (c • φ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  exact ⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩

theorem good_sum {Γ : Set (Matrix ι ι ℂ)} {β : Type} (s : Finset β) (φ : β → Matrix ι ι ℂ → ℂ)
    (h : ∀ b, Good Γ (φ b)) : Good Γ (∑ b ∈ s, φ b) :=
  Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)

theorem good_coord {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (n : ℕ) (l : (Fin n → ι) → ℂ)
    (hl : ∀ g ∈ Γ, l ᵥ* tpow n g = l) (b : Fin n → ι) : Good Γ (fun y => (l ᵥ* tpow n y) b) := by
  have h := GlobalTheory.T.mem_span_rational_kroneckerInvariants ι Γ hΓ.aut_mem n l hl
  clear hl
  induction h using Submodule.span_induction with
  | mem μ hμ =>
    obtain ⟨h1, h2⟩ := hμ
    choose q hq using h2
    have hμ : μ = fun a => ((q a : ℚ) : ℂ) := funext hq
    subst hμ
    refine ⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩
    rintro p rfl
    exact h1
  | zero =>
    have : (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0 := by
      funext y; simp
    rw [this]; exact good_zero Γ
  | add u v _ _ hu hv =>
    have : (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) =
        (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b := by
      funext y; simp [Matrix.add_vecMul]
    rw [this]; exact hu.add hv
  | smul c u _ hu =>
    have : (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) =
        c • (fun y => (u ᵥ* tpow n y) b) := by
      funext y; simp [Matrix.smul_vecMul]
    rw [this]; exact hu.smul c

theorem good_homog {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) (n : ℕ)
    (F : MvPolynomial (ι × ι) ℂ) (hF : IsInv Γ F) (hn : F.IsHomogeneous n) : Good Γ (evC F) := by
  obtain ⟨l, hl, hev⟩ := GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' ι Γ hΓ hS n F hF hn
  have : evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b := by
    funext y; rw [hev, Finset.sum_apply]
  rw [this]
  exact good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b

theorem exists_finite_family {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) :
    ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧
      ∀ f, IsInv Γ f → evC f ∈ coordAlg S := by
  obtain ⟨Rey, hR⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ hS
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly ι Γ Rey hR
  have hg : ∀ F : s, Good Γ (evC F.1) := fun F => by
    obtain ⟨h1, n, h2⟩ := hs F.1 F.2
    exact good_homog hΓ hS n F.1 h1 h2
  choose S hfin hfix hmem using hg
  refine ⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩
  · intro p hp
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hp
    exact hfix F p hF
  · intro f hf
    have h := hgen f hf
    clear hf
    induction h using Algebra.adjoin_induction with
    | mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)
    | algebraMap c =>
      have : evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c := by
        funext y; simp [evC]
      rw [this]; exact Subalgebra.algebraMap_mem _ c
    | add u v _ _ hu hv =>
      have : evC (u + v) = evC u + evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv =>
      have : evC (u * v) = evC u * evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.mul_mem _ hu hv

theorem exists_rational_invariant_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  intro ι _ _ Γ hΓ hS
  obtain ⟨S, hfin, hfix, hmem⟩ := exists_finite_family hΓ hS
  obtain ⟨m, e, -, he⟩ := hfin.fin_param
  refine ⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩
  · intro g hg
    funext k
    exact congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2
  · intro f hf
    have h := hmem f hf
    generalize evC f = φ at h
    induction h using Algebra.adjoin_induction with
    | mem φ hφ =>
      obtain ⟨p, hp, b, rfl⟩ := hφ
      rw [← he] at hp
      obtain ⟨i, rfl⟩ := hp
      exact ⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩
    | algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P + Q, fun y => by rw [map_add (f := _), ← hP, ← hQ]; rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩

end GlobalTheory.ClassFin.RatInvTensor
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_id_le_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    normSub (RingHom.id F) δ ≤ normSub φ δ := by
  intro x hx
  obtain ⟨a, b, hab⟩ := (mem_normSub _ _ x).1 hx
  refine (mem_normSub _ _ x).2 ⟨φ a, φ b, ?_⟩
  have hab' : (x : F) = a ^ 2 - δ * b ^ 2 := hab
  rw [hab']
  simp [map_sub, map_mul, map_pow]

theorem normSub_id_le_locNorm (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    normSub (RingHom.id F) δ ≤ locNorm F δ S :=
  le_inf (le_iInf₂ fun _ _ => normSub_id_le_normSub _ δ)
    (le_iInf fun _ => normSub_id_le_normSub _ δ)

theorem sUnits_sup_locNorm_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  intro F _ _ δ S hS hδ hsq htop
  obtain ⟨hne, hle⟩ := GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le F δ S hS hδ hsq
  obtain ⟨-, hge⟩ := GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension F (δ : F) S δ.ne_zero
  have h1 : (locNorm F δ S).index = (locNorm F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h2 : (locNorm F δ S).relIndex (sUnits F S) ≤
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) :=
    Subgroup.relIndex_le_of_le_left (normSub_id_le_locNorm F δ S) hne
  omega

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.standardHermitianForm_hostField_inhabitant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ), IsHermForm (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) ∧ Module.finrank (maximalRealSubfield E) E = 2 ∧ (stdLat E n).FG ∧ Submodule.span E (stdLat E n : Set (Fin n → E)) = ⊤ ∧ SplitOff (IsCMField.complexConj E) 1 H.w0 ∧ ¬ IsUnit H.w0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → (Moved (IsCMField.complexConj E) P ↔ P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P)) ∧ ∀ γ : Matrix (Fin n) (Fin n) E, IsUnE (IsCMField.complexConj E) 1 γ ↔ ∀ i j, ∑ b, (IsCMField.complexConj E) (γ b i) * γ b j = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.UnRep.StdInhab.main | exact GlobalTheory.UnRep.StdInhab.main | (intros; apply GlobalTheory.UnRep.StdInhab.main <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_not_mem_not_pow_completion :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (ζ u : F) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → u ≠ 0 → (∀ r : F, r ^ p ≠ u) → ∃ v, v ∉ S₀ ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) u := by
  classical
  intro p F _ _ _ ζ u S₀ hp hζ hu hns
  by_contra hcon
  push Not at hcon
  have hle : ∀ S, finNorm p F u S₀ ≤ finNorm p F u S := by
    intro S x hx
    rw [finNorm] at hx ⊢
    simp only [Subgroup.mem_iInf] at hx ⊢
    intro v _
    by_cases hv : v ∈ S₀
    · exact hx v hv
    · haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      obtain ⟨r, hr⟩ := hcon v hv
      rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F _ _ u r hp.pos hu hr]
      exact Subgroup.mem_top x
  have hidx := (GlobalTheory.T.pow_countPlacesNotLocalPower_le_index p F ζ u S₀ hp hζ).1
  haveI : (finNorm p F u S₀).FiniteIndex := ⟨hidx⟩
  haveI : Fintype (Fˣ ⧸ finNorm p F u S₀) := Fintype.ofFinite _
  obtain ⟨S₁, -, hS₁⟩ := exists_superset_mem_sUnits F
    (insert (Units.mk0 u hu)
      (Finset.univ.image (fun q : Fˣ ⧸ finNorm p F u S₀ => q.out))) S₀
  obtain ⟨S, hS, hadm⟩ := (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).1 S₁
  have hX := hS₁ S hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ (Units.mk0 u hu) S hp hζ hadm
    (hX _ (Finset.mem_insert_self _ _)) hns ?_
  rw [eq_top_iff]
  intro x _
  have hy : (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out ∈ sUnits F S :=
    hX _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hz : ((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x ∈ finNorm p F u S₀ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have hx : x = (QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out *
      (((QuotientGroup.mk x : Fˣ ⧸ finNorm p F u S₀).out)⁻¹ * x) := by
    rw [mul_inv_cancel_left]
  rw [hx]
  exact Subgroup.mul_mem_sup hy (hle S hz)

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_of_mem_sUnits_union_of_mem_finPow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
      [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))),
      p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ →
      ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  intro p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS
  by_contra hne
  have hne' : ∀ r : F, r ^ p ≠ (y : F) := fun r hr => hne ⟨r, hr⟩
  have hadm : AdmP p F (S ∪ T) :=
    (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  unfold finNorm
  refine le_iInf₂ fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · have h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F)) :=
      (iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS
    obtain ⟨r, hr⟩ := h1
    have : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]
    exact le_top
  · exact le_trans
      (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv)
      ((GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1 F (v.adicCompletion F) _ (y : F))

end GlobalTheory.CNorm
end
