module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle137
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareComparisonTorusInvariant
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilLaws

theorem toNat_iff_zpow {R K : Type} [CommRing R] [CommRing K] (ι : R →+* K) (ξ : R) (u : Kˣ)
    (hu : (u : K) = ι ξ) (a : ℤ) (x : K) :
    (∃ y : R, x * ι ξ ^ (-a).toNat = ι (ξ ^ a.toNat * y)) ↔ ∃ y : R, x = ((u ^ a : Kˣ) : K) * ι y := by
  refine exists_congr fun y => ?_
  rw [map_mul, map_pow, ← hu]
  have h : u ^ a * u ^ (-a).toNat = u ^ a.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
    congr 1
    omega
  have h' : ((u ^ a : Kˣ) : K) * (u : K) ^ (-a).toNat = (u : K) ^ a.toNat := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h]
  rw [← h', mul_right_comm]
  exact (u.isUnit.pow _).mul_left_inj

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

variable {l : ℕ} [Fact l.Prime]

theorem σDp_alg (g : Per.Gq l) (x : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) x) :=
  GlobalTheory.RingIface.sigDp_alg l g x

theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

theorem σDp_mem_FilP (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l) (hy : y ∈ Per.FilP l n) :
    Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  have h1 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ∈ Per.kerP l := by
    rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : Per.extP (Per.σA g) (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) ∈ Per.kerP l :=
    Ideal.mem_comap.1 (GlobalTheory.RingBasics.ker_σ g h1)
  rw [hk, Ideal.mem_span_singleton] at h2
  have h3 : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply, σDp_alg]
    exact map_dvd _ h2
  obtain ⟨z, rfl⟩ := (hP n y).1 hy
  rw [hP, map_mul, map_pow]
  exact (pow_dvd_pow_of_dvd h3 n).mul_right _

theorem σDp_xi (e : Per.Fl l) (he : IsEps e) (g : Per.Gq l) :
    ∃ c d : Per.BdRp l, Per.σDp g (aDp l (xi e)) = aDp l (xi e) * c ∧ c * d = 1 := by
  obtain ⟨hP, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have hd : ∀ g : Per.Gq l, aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := fun g => by
    have := (hP 1 _).1 (σDp_mem_FilP g 1 _ hξ)
    rwa [pow_one] at this
  obtain ⟨c, hc⟩ := hd g
  obtain ⟨c', hc'⟩ := hd g⁻¹
  have hinv : Per.σDp g (Per.σDp g⁻¹ (aDp l (xi e))) = aDp l (xi e) := by
    change Per.σDp g (Per.σDp g⁻¹ (algebraMap (Per.AinfP l) (Per.BdRp l) _)) =
      algebraMap (Per.AinfP l) (Per.BdRp l) _
    rw [σDp_alg, σDp_alg, GlobalTheory.RingBasics.extP_inv]
  refine ⟨c, Per.σDp g c', hc, ?_⟩
  rw [hc', map_mul, hc] at hinv
  have := hreg (c * Per.σDp g c' - 1) (by rw [mul_sub, mul_one, ← mul_assoc, hinv, sub_self])
  exact sub_eq_zero.1 this

theorem eq_zero_of_forall_mem_FilP (y : Per.BdRp l) (hy : ∀ n, y ∈ Per.FilP l n) : y = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, hc, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  refine hc.toIsHausdorff.haus y fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (hP n y).1 (hy n)

end GlobalTheory.MemLoc.FilLaws


open GlobalTheory.MemLoc.FilLaws in
theorem GlobalTheory.MemLoc.filD_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hdom, hinj, hfield, hden⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hP, hreg, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l e he
  have hD := GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l e he
  have hden := hden e he
  have hσ := σDp_xi e he
  generalize aDp l (xi e) = ξ at hP hreg hD hden hσ
  have hne : algebraMap (Per.BdRp l) (Per.BdR l) ξ ≠ 0 := by
    intro h
    have h0 : ξ = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero (hreg 1 (by rw [h0, zero_mul]))
  obtain ⟨v, hv⟩ := hfield.mul_inv_cancel hne
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) ξ) := IsUnit.of_mul_eq_one v hv
  have hZ : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔
      ∃ y, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun a x => (hD a x).trans (toNat_iff_zpow _ ξ u hu a x)
  have hlast : ∀ (n : ℕ) (y : Per.BdRp l),
      algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
    intro n y
    rw [hZ, hP, zpow_natCast, Units.val_pow_eq_pow_val, hu]
    refine exists_congr fun z => ?_
    rw [← map_pow, ← map_mul]
    exact hinj.eq_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlast⟩
  · intro a x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 hx
    refine (hZ _ _).2 ⟨ξ * y, ?_⟩
    rw [hy, zpow_add_one, Units.val_mul, hu, map_mul, mul_assoc]
  · exact (hZ _ _).2 ⟨1, by rw [zpow_zero, Units.val_one, map_one, mul_one]⟩
  · intro a b x y hx hy
    obtain ⟨x', rfl⟩ := (hZ _ _).1 hx
    obtain ⟨y', rfl⟩ := (hZ _ _).1 hy
    refine (hZ _ _).2 ⟨x' * y', ?_⟩
    rw [zpow_add, Units.val_mul, map_mul, mul_mul_mul_comm]
  · intro x
    obtain ⟨n, y, hy⟩ := hden x
    refine ⟨-(n : ℤ), (hD _ _).2 ⟨y, ?_⟩⟩
    rw [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, hy]
  · intro x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 (hx 0)
    rw [zpow_zero, Units.val_one, one_mul] at hy
    subst hy
    rw [eq_zero_of_forall_mem_FilP y fun n => (hlast n y).1 (hx n), map_zero]
  · intro g a x hx
    obtain ⟨c, d, hc, hcd⟩ := hσ g
    obtain ⟨y, hy⟩ := (hD _ _).1 hx
    have h1 := congrArg (Per.σD g) hy
    rw [map_mul, map_pow, σD_alg, σD_alg, map_mul (Per.σDp g), map_pow, hc] at h1
    refine (hD _ _).2 ⟨d ^ (-a).toNat * (c ^ a.toNat * Per.σDp g y), ?_⟩
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) ξ =
        algebraMap (Per.BdRp l) (Per.BdR l) (ξ * c) * algebraMap (Per.BdRp l) (Per.BdR l) d := by
      rw [← map_mul, mul_assoc, hcd, mul_one]
    rw [h2, mul_pow, ← mul_assoc, h1, ← map_pow, ← map_mul]
    congr 1
    ring
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PrincLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_mem (c : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * c ∈ intOE E := by
  obtain ⟨y, hy, hint'⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  have hint := hint' c (Finset.mem_singleton_self c)
  have key : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : E) * c) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = ((n : ℤ) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint.neg
  obtain ⟨n, hn, h2⟩ := key
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 h2
  exact ⟨a, ha⟩

theorem exists_nat_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (w : Fin r → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • w ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegralExists.main
  | exact _root_.GlobalTheory.NatMulIntegralExists.main
  | (apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegralExists.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegralExists.main ..)

theorem exists_nat_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose m hm hmem using fun (p : (Fin r → E) × Fin r) => exists_nat_mul_mem (E := E) (p.1 p.2)
  refine ⟨∏ p ∈ s ×ˢ Finset.univ, m p, Finset.prod_pos fun p _ => hm p, ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    intro i
    obtain ⟨k, hk⟩ : m (x, i) ∣ ∏ p ∈ s ×ˢ Finset.univ, m p :=
      Finset.dvd_prod_of_mem _ (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i = (k : E) * ((m (x, i) : E) * x i) := by
      rw [hk]; push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ k) (hmem (x, i))
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * (a • x) i =
        algebraMap (𝓞 E) E a * (((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]; ring
    rw [e]
    exact mul_mem ⟨a, rfl⟩ (hx i)

theorem den_locL (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {d : ℕ}
    (hd : ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E) {y : Fin r → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ Formalism.L2.Herm.locL v Λ) :
    ∀ i, (d : E ⊗[F] v.adicCompletion F) * y i ∈ intV E v := by
  unfold Formalism.L2.Herm.locL latS at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro i
    have e : (d : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (w i) =
        inclE (F := F) (v.adicCompletion F) ((d : E) * w i) := by
      rw [map_mul, map_natCast]
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨⟨_, hd w hw i⟩, rfl⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem a.2 (hx i)

theorem princ_lat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ d : ℕ, 0 < d ∧ ∀ (M : ℕ) (x : Matrix (Fin r) (Fin r) (E ⊗[F] v.adicCompletion F)), (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ, x *ᵥ y - y = ((M * d : ℕ) : E ⊗[F] v.adicCompletion F) • z) → ∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, (x - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c := by
  intro F E _ _ _ _ _ r v Λ hfg hsp
  classical
  choose k hk hkmem using fun b : Fin r => exists_nat_smul_mem Λ hsp (Pi.single b 1)
  obtain ⟨d₂, hd₂, hden⟩ := exists_nat_den Λ hfg
  have hd₁ : 0 < ∏ b, k b := Finset.prod_pos fun b _ => hk b
  have hmem : ∀ b, ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := fun b => by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ b)
    have e : ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) = t • ((k b : E) • (Pi.single b 1 : Fin r → E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, ht, Nat.cast_mul, mul_comm]
    rw [e]
    exact Λ.toAddSubmonoid.nsmul_mem (hkmem b) t
  refine ⟨(∏ b, k b) * d₂, Nat.mul_pos hd₁ hd₂, fun M x hx a b => ?_⟩
  set d₁ := ∏ b, k b with hd₁def
  let y : Fin r → E ⊗[F] v.adicCompletion F :=
    fun i => inclE (F := F) (v.adicCompletion F) (((d₁ : E) • (Pi.single b 1 : Fin r → E)) i)
  have hy : y ∈ Formalism.L2.Herm.locL v Λ := Submodule.subset_span ⟨_, hmem b, rfl⟩
  obtain ⟨z, hz, hxz⟩ := hx y hy
  have hy' : y = (d₁ : E ⊗[F] v.adicCompletion F) • (Pi.single b 1 : Fin r → E ⊗[F] v.adicCompletion F) := by
    funext i
    simp only [y, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    by_cases h : i = b
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : x *ᵥ y - y = (d₁ : E ⊗[F] v.adicCompletion F) • ((x - 1) *ᵥ Pi.single b 1) := by
    rw [hy', Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub]
  have h1 := congrFun hxz a
  rw [hcol, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul,
    smul_eq_mul] at h1
  have hu : IsUnit (d₁ : E ⊗[F] v.adicCompletion F) := by
    have := (IsUnit.mk0 (d₁ : F) (Nat.cast_ne_zero.2 hd₁.ne')).map (algebraMap F (E ⊗[F] v.adicCompletion F))
    rwa [map_natCast] at this
  refine ⟨(d₂ : E ⊗[F] v.adicCompletion F) * z a, den_locL v Λ hden hz a, ?_⟩
  apply hu.mul_left_cancel
  rw [h1]
  push_cast
  ring

end GlobalTheory.PrincLat
end
end

section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbTiePosDef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dotProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem hAt_single_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

theorem posDef_map_of_posAt [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : PosAt H v) : (H.map v.embedding).PosDef := by
  have herm : (H.map v.embedding).IsHermitian := by
    ext i j
    have := h.1 (Pi.single j 1) (Pi.single i 1)
    rw [hAt_single_single, hAt_single_single] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [this]
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have psd : (H.map v.embedding).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun z => ?_
    induction z using hd.induction_on with
    | hp =>
      refine isClosed_le continuous_const ?_
      exact Continuous.dotProduct (continuous_star) (Continuous.matrix_mulVec continuous_const continuous_id)
    | ih y =>
      have hy : Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) y = fun i => v.embedding (y i) := rfl
      rw [hy, ← hAt_eq_dotProduct]
      have hs := h.1 y y
      have him : (hAt H v y y).im = 0 := by
        have := congrArg Complex.im hs
        simp at this
        linarith
      rw [Complex.nonneg_iff]
      refine ⟨?_, him.symm⟩
      by_cases hy0 : y = 0
      · subst hy0
        simp [hAt]
      · exact (h.2 y hy0).le
  rw [psd.posDef_iff_det_ne_zero]
  show (v.embedding.mapMatrix H).det ≠ 0
  rw [← RingHom.map_det]
  intro h0
  rw [map_eq_zero] at h0
  obtain ⟨y, hy0, hHy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : hAt H v y y = 0 := by
    rw [hAt_eq_dotProduct]
    have : (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) = 0 := by
      funext i
      have := RingHom.map_mulVec v.embedding H y i
      rw [hHy] at this
      simpa [Function.comp_def] using this.symm
    rw [this, dotProduct_zero]
  have := h.2 y hy0
  rw [hz] at this
  simp at this

end GlobalTheory.AmbTiePosDef
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_ringEquiv_finExtIntegers_padicIntOf : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) := by
  first | exact @GlobalTheory.IntOfFinExt.exists_ringEquiv_intOf | exact GlobalTheory.IntOfFinExt.exists_ringEquiv_intOf | (intros; apply GlobalTheory.IntOfFinExt.exists_ringEquiv_intOf <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.square_comparison_torus_invariant : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 G).left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t r z N ^ 2 =
        (∏ k : thK.{0}, gv wL (r ≫ thφ G (x3 G) k) z (fun _ => N (r ≫ thφ G (x3 G) k))
          (fun _ => N' (r ≫ thφ G (x3 G) k)) ^ thε k) *
        val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t r z N' ^ 2) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι)
      (N' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z N → Good U'.LG.L z N' →
      val (L := U.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U.symG r z N ^ 2 =
        (∏ k : Fin 2, gv wL (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k) z
          (fun _ => N (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k))
          (fun _ => N' (r ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
        val (L := U'.LG.L) (φ := (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left))) (ε := ![1, -1]) U'.symG r z N' ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∀ u : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull (U'.gt e).pG.left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull (U.gt e).pG.left), u.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw u r z (fun _ => jM) (fun _ _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL')) →
    ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G)
      (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι),
      (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' →
      gw u ((τ ≫ (U.gt e).i) * y).left z (fun _ => jM) (fun _ _ => jM') = gw u y.left z (fun _ => jM) (fun _ _ => jM') := by
  first | exact @GlobalTheory.comparison_sq_torus_invariant | exact GlobalTheory.comparison_sq_torus_invariant | (intros; apply GlobalTheory.comparison_sq_torus_invariant <;> assumption)
end
