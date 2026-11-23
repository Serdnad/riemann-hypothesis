module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle098
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle035

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosets

theorem finite_ncard_cosets {E : Type} [Field E] [NumberField E] {n : ℕ} (A₁ A₀ : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (hc : 0 < c)
    (h : ∀ y ∈ A₁, c • y ∈ A₀) :
    {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}}.Finite ∧
      {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}}.ncard ≤ c ^ (Module.finrank ℚ E * n) := by
  haveI : Module.Finite ℚ (Sp E n) := Module.Finite.trans E (Sp E n)
  have hd : Module.finrank ℚ (Sp E n) = Module.finrank ℚ E * n := by
    rw [← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  obtain ⟨hf, hle⟩ := GlobalTheory.SemilocalClasses.finite_card_le A₁.subtype.toAddMonoidHom (Submodule.subtype_injective _)
    (A₀.comap A₁.subtype).mkQ.toAddMonoidHom (Submodule.mkQ_surjective _) c hc fun x =>
      (Submodule.Quotient.mk_eq_zero _).2 (h x x.2)
  rw [hd] at hle
  let φ : (A₁ ⧸ A₀.comap A₁.subtype) → Set (Sp E n) := fun q => {z | z - ((Quotient.out q : A₁) : Sp E n) ∈ A₀}
  have hsub : {Y : Set (Sp E n) | ∃ y ∈ A₁, Y = {z | z - y ∈ A₀}} ⊆ Set.range φ := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    have h1 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk (p := A₀.comap A₁.subtype) ⟨y, hy⟩)) :
        A₁ ⧸ A₀.comap A₁.subtype) = Submodule.Quotient.mk ⟨y, hy⟩ := Quotient.out_eq _
    have h2 := (Submodule.Quotient.eq _).1 h1
    set w : A₁ := Quotient.out (Submodule.Quotient.mk (p := A₀.comap A₁.subtype) ⟨y, hy⟩) with hw
    have h3 : (w : Sp E n) - y ∈ A₀ := h2
    ext z
    show z - (w : Sp E n) ∈ A₀ ↔ z - y ∈ A₀
    constructor
    · intro hz
      simpa using A₀.add_mem hz h3
    · intro hz
      simpa using A₀.sub_mem hz h3
  refine ⟨(Set.finite_range φ).subset hsub, ((Set.ncard_le_ncard hsub (Set.finite_range φ)).trans ?_).trans hle⟩
  exact Finite.card_range_le φ

theorem finite_ncard_ybSet {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg) (hmu : mu = 1)
    (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n)) :
    (ybSet sel mu cst L).Finite ∧ (ybSet sel mu cst L).ncard ≤ (Pr.g 0 * Pr.g 1) ^ (Module.finrank ℚ X.E * n) := by
  classical
  have hvG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := by
    intro P
    rcases Finset.mem_union.mp P.2 with h | h
    · exact h
    · have h0 : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
        rw [hmu]
        exact twistPrimes_trivialTuple_empty sel Sg
      rw [h0] at h
      simp at h
  refine finite_ncard_cosets _ _ _ (Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos) ?_
  intro y hy
  unfold locLat at hy ⊢
  rw [Submodule.mem_iInf] at hy ⊢
  intro P
  have h1 := hy P
  rw [Submodule.mem_comap] at h1 ⊢
  simp only [hvG P, if_true, zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul, LinearMap.restrictScalars_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] at h1 ⊢
  rcases Finset.mem_union.mp (hvG P) with h | h
  · have hq : Formalism.L2.Col.qOf P.1 = Pr.g 0 := hPr.vG_norm 0 _ h
    rw [hq] at h1
    rw [mul_nsmul]
    exact nsmul_mem h1 _
  · have hq : Formalism.L2.Col.qOf P.1 = Pr.g 1 := hPr.vG_norm 1 _ h
    rw [hq] at h1
    rw [mul_nsmul']
    exact nsmul_mem h1 _

end GlobalTheory.CouplingCosets
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.IndexCount

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem sclLat_anti (hq : q ≠ 0) {N : ℕ} {e e' : ℕ → ℤ} (h : ∀ l, e l ≤ e' l) : sclLat P q N e' ≤ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  intro x hx
  rw [mem_sclLat] at hx ⊢
  intro l
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (h l.1))
  have h1 : IntAt P ((q : E) ^ k) := (intRing P).pow_mem (intAt_natCast P q) k
  convert h1.mul (hx l) using 1
  rw [show e' l.1 = e l.1 + k by omega, zpow_add₀ hq', zpow_natCast]
  field_simp

theorem mem_sclLat_succ (hq : q ≠ 0) {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ sclLat P q N (fun l => e l + 1) ↔ (q : E)⁻¹ • x ∈ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [mem_sclLat, mem_sclLat]
  refine forall_congr' fun l => ?_
  rw [zpow_add₀ hq', zpow_one, Pi.smul_apply, smul_eq_mul, mul_inv, mul_assoc]

theorem mem_stabL_of_cong {N : ℕ} {M₀ M M₁ : Submodule (𝓞 E) (Sp E N)} (h₀ : M₀ ≤ M) (h₁ : M ≤ M₁)
    {κ : Sp E N ≃ₗ[E] Sp E N} (hκ : κ ∈ stabL E N M₁) (hc : ∀ y ∈ M₁, κ y - y ∈ M₀) : κ ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    simpa using M.sub_mem hx (h₀ (hc x ((hκ x).1 (h₁ hx))))
  · intro hx
    simpa using M.add_mem (h₀ (hc x (h₁ hx))) hx

noncomputable def resMat {N : ℕ} (e : ℕ → ℤ) (h : Sp E N ≃ₗ[E] Sp E N) : Fin N × Fin N → 𝓞 E ⧸ P.asIdeal :=
  fun p => redP P (h (eN E N p.2.1) p.1 * (q : E) ^ (e p.2.1 - e p.1.1))

theorem cong_of_resMat_eq (hq : q ≠ 0) (hdiv : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (q : E)))
    {N : ℕ} {e : ℕ → ℤ} {h h' : Sp E N ≃ₗ[E] Sp E N} (hh : h ∈ stabL E N (sclLat P q N e))
    (hh' : h' ∈ stabL E N (sclLat P q N e)) (hres : resMat P q e h = resMat P q e h') :
    ∀ y ∈ sclLat P q N e, (h⁻¹ * h') y - y ∈ sclLat P q N (fun l => e l + 1) := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have a1 := (maps_iff P q hq e e h.toLinearMap).1 fun y hy => (hh y).2 hy
  have a2 := (maps_iff P q hq e e h'.toLinearMap).1 fun y hy => (hh' y).2 hy
  have a3 := (maps_iff P q hq e (fun l => e l + 1) (h'.toLinearMap - h.toLinearMap)).2 fun l l' => by
    have b1 : IntAt P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1) - h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) :=
      (intRing P).sub_mem (a2 l l') (a1 l l')
    have b2 := reduction_add b1 (a1 l l')
    have b3 : redP P (h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) =
      redP P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) := congrFun hres (l, l')
    erw [sub_add_cancel, b3, right_eq_add] at b2
    convert hdiv _ b1 b2 using 1
    rw [show e l'.1 - (e l.1 + 1) = e l'.1 - e l.1 - 1 by ring, zpow_sub_one₀ hq']
    simp only [LinearMap.sub_apply, Pi.sub_apply, LinearEquiv.coe_coe]
    field_simp
  intro y hy
  have a4 := a3 y hy
  rw [mem_sclLat_succ P q hq] at a4 ⊢
  rw [← hh, map_smul, map_sub]
  simpa using a4

theorem mem_JGsym_of_cong (hq : q ≠ 0) (k rS r t n c : ℕ) {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hκ : κ ∈ stabL E (n + c) (lamY P q n c fun i => i + 1))
    (hc : ∀ y ∈ lamY P q n c fun i => i + 1, κ y - y ∈ sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1)) :
    κ ∈ JGsym P q k rS r t n c := by
  have h₀ : ∀ s, sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1) ≤ flagS P q k rS n c s := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  have h₁ : ∀ s, flagS P q k rS n c s ≤ lamY P q n c fun i => i + 1 := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  refine ⟨hκ, fun s _ => mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, fun s _ => ⟨mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, h₀ s (hc _ ?_)⟩⟩
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold lamY bvecS bvecG
  rw [mem_sclLat]
  intro i
  by_cases hi : i.1 = fIdx k c n (symIdxInv k rS s)
  · simp only [Pi.smul_apply, eN, hi, if_true, smul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (zpow_ne_zero _ hq')]
    exact intAt_one P
  · simp only [Pi.smul_apply, eN, hi, if_false, smul_eq_mul, mul_zero]
    exact intAt_zero P

end

end GlobalTheory.IndexCount
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResConjPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_mem_int (τ : E →ₐ[F] E) {s : E ⊗[F] Formalism.L2.Herm.Af F} (hs : s ∈ Formalism.L2.Herm.intAf F E) :
    Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E := by
  have : Formalism.L2.Herm.intAf F E ≤ (Formalism.L2.Herm.intAf F E).comap (Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩)
    · obtain ⟨c', hc'⟩ : ∃ y' : 𝓞 E, (y' : E) = τ (c : E) :=
        ⟨⟨τ (c : E), (c.isIntegral_coe).map ((τ : E →+* E).toIntAlgHom)⟩, rfl⟩
      refine Subring.subset_closure (Or.inl ⟨⟨_, c', rfl⟩, ?_⟩)
      show (c' : E) ⊗ₜ[F] _ = τ (c : E) ⊗ₜ[F] _
      rw [hc']; rfl
    · refine Subring.subset_closure (Or.inr ⟨b, ?_⟩)
      show _ = τ 1 ⊗ₜ[F] _
      rw [map_one]; rfl
  exact this hs

end General

end GlobalTheory.ResConjPlace
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  first | exact @GlobalTheory.NatAtStd.eNat_std | exact GlobalTheory.NatAtStd.eNat_std | (intros; apply GlobalTheory.NatAtStd.eNat_std <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory

theorem latSum_tower_reps (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D G C B : Submodule (𝓞 E) W) (hBC : B ≤ C) (hCG : C ≤ G) (hGD : G ≤ D)
    (hfin : Finite (↥D ⧸ B.comap D.subtype)) :
    ∃ R : Finset W, (∀ x ∈ R, x ∈ G) ∧ R.card = Nat.card (↥G ⧸ C.comap G.subtype) ∧
      ∀ f : W → ℂ, (∀ x, f x ≠ 0 → x ∈ G) → (∀ x y, x - y ∈ B → f x = f y) →
        latSum D B f = ∑ x ∈ R, latSum C B fun y => f (x + y) := by
  classical
  have key : ∀ (P Q : Submodule (𝓞 E) W) (t u : ↥P),
      (Submodule.Quotient.mk t : ↥P ⧸ Q.comap P.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ Q := by
    intro P Q t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  set r : (↥G ⧸ C.comap G.subtype) → ↥G :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap G.subtype)) with hr
  set s : (↥C ⧸ B.comap C.subtype) → ↥C :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap C.subtype)) with hs
  set t : (↥D ⧸ B.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap D.subtype)) with ht
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have ht' : ∀ z, Submodule.Quotient.mk (t z) = z := fun z => Function.surjInv_eq _ z
  have hmem : ∀ p : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype), (r p.1 : W) + s p.2 ∈ D :=
    fun p => hGD (G.add_mem (r p.1).2 (hCG (s p.2).2))
  let φ : (↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype) → (↥D ⧸ B.comap D.subtype) :=
    fun p => Submodule.Quotient.mk ⟨_, hmem p⟩
  have hinj : Function.Injective φ := by
    rintro ⟨x, j⟩ ⟨x', j'⟩ h
    have h1 : (r x : W) + s j - (r x' + s j') ∈ B := (key D B _ _).1 h
    have h2 : x = x' := by
      rw [← hr' x, ← hr' x', key]
      have : (r x : W) - r x' = ((r x : W) + s j - (r x' + s j')) + (s j' - s j) := by abel
      rw [this]
      exact C.add_mem (hBC h1) (C.sub_mem (s j').2 (s j).2)
    subst h2
    have h3 : j = j' := by
      rw [← hs' j, ← hs' j', key]
      simpa using h1
    rw [h3]
  haveI hprod : Finite ((↥G ⧸ C.comap G.subtype) × (↥C ⧸ B.comap C.subtype)) := Finite.of_injective φ hinj
  haveI : Finite (↥G ⧸ C.comap G.subtype) := Finite.prod_left (↥C ⧸ B.comap C.subtype)
  haveI : Finite (↥C ⧸ B.comap C.subtype) := Finite.prod_right (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥G ⧸ C.comap G.subtype)
  letI := Fintype.ofFinite (↥C ⧸ B.comap C.subtype)
  letI := Fintype.ofFinite (↥D ⧸ B.comap D.subtype)
  have hrinj : Function.Injective fun z => (r z : W) := by
    intro z w h
    rw [← hr' z, ← hr' w, Subtype.ext h]
  refine ⟨Finset.univ.image fun z => (r z : W), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
    exact (r z).2
  · rw [Finset.card_image_of_injective _ hrinj, Nat.card_eq_fintype_card, Finset.card_univ]
  · intro f hf0 hf
    rw [Finset.sum_image fun _ _ _ _ h => hrinj h]
    unfold latSum
    simp only [finsum_eq_sum_of_fintype]
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_of_injective φ hinj _ _ ?_ ?_
    · intro z hz
      by_contra hne
      have hG : (t z : W) ∈ G := hf0 _ hne
      apply hz
      have h1 : (r (Submodule.Quotient.mk ⟨_, hG⟩) : W) - t z ∈ C := (key G C _ ⟨_, hG⟩).1 (hr' _)
      have h1' : (t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩) ∈ C := by
        simpa using C.neg_mem h1
      have h2 : (s (Submodule.Quotient.mk ⟨_, h1'⟩) : W) - ((t z : W) - r (Submodule.Quotient.mk ⟨_, hG⟩)) ∈ B :=
        (key C B _ ⟨_, h1'⟩).1 (hs' _)
      refine ⟨(Submodule.Quotient.mk ⟨_, hG⟩, Submodule.Quotient.mk ⟨_, h1'⟩), ?_⟩
      refine Eq.trans ?_ (ht' z)
      refine (key D B _ _).2 ?_
      convert h2 using 1
      simp only
      abel
    · intro p
      apply hf
      exact (key D B ⟨_, hmem p⟩ _).1 (ht' _).symm

theorem thInd_congr_of_sub_mem {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x y : HomE X.E a b)
    (h : x - y ∈ mulLat c (homAt S L L')) : A.thInd S L L' c x = A.thInd S L L' c y := by
  have h1 : A.IsLift S L L' c x = A.IsLift S L L' c y := by
    funext s
    unfold Amb.IsLift
    congr 1
    apply propext
    constructor
    · intro hs
      simpa using Submodule.add_mem _ hs h
    · intro hs
      simpa using Submodule.sub_mem _ hs h
  unfold Amb.thInd Amb.liftW
  rw [h1]

theorem latSum_thInd_regroup : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (L : Submodule (𝓞 X.E) (Sp X.E a)) (L' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c c' : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndAdd a b S (cA * (c * c')) → IsSdLat L → IsSdLat L' → 0 < cA → 0 < c → 0 < c' → (∀ x, Ξ x ≠ 0 → x ∈ homAt S L L') → (∀ x, ∀ y ∈ mulLat c (homAt S L L'), Ξ (x + y) = Ξ x) → ∃ R : Finset (HomE X.E a b), R.card ≤ c ^ (Module.finrank ℚ X.E * a * b) ∧ ∀ z, latSum (divLat cA (homAt S L L')) (mulLat (c * c') (homAt S L L')) (fun x => Ξ x * A.thInd S L L' (c * c') x z) = ∑ x ∈ R, Ξ x * A.thInd S L L' c x z := by
  intro X A a b S L L' cA c c' Ξ hadd hL hL' hcA hc hc' hsupp hinv
  have hdiv : ∀ (n : ℕ) x, x ∈ homAt S L L' → x ∈ divLat n (homAt S L L') := fun n x hx =>
    Submodule.smul_mem (homAt S L L') (n : 𝓞 X.E) hx
  have hone : ∀ x, x ∈ divLat 1 (homAt S L L') → x ∈ homAt S L L' := fun x hx => by
    simpa [divLat] using hx
  have hBC : mulLat (c * c') (homAt S L L') ≤ mulLat c (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(c' : 𝓞 X.E) • x, Submodule.smul_mem _ _ hx, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_smul]
  have hCG : mulLat c (homAt S L L') ≤ divLat 1 (homAt S L L') := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiv 1 _ (Submodule.smul_mem (homAt S L L') (c : 𝓞 X.E) hx)
  have hfin := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' cA (c * c') hL.1 hL'.1 hcA (Nat.mul_pos hc hc')).1
  have hcard := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S L L' 1 c hL.1 hL'.1 Nat.one_pos hc).2
  obtain ⟨R, hR, hRc, hsum⟩ := latSum_tower_reps X.E (HomE X.E a b) (divLat cA (homAt S L L'))
    (divLat 1 (homAt S L L')) (mulLat c (homAt S L L')) (mulLat (c * c') (homAt S L L')) hBC hCG
    (fun x hx => hdiv cA x (hone x hx)) hfin
  refine ⟨R, by rw [hRc]; simpa using hcard, fun z => ?_⟩
  rw [hsum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [hadd L L' c c' x hc hc' ⟨hL, hL', Nat.mul_pos hc hc', Dvd.intro_left _ rfl, hdiv _ x (hone x (hR x hx))⟩ z]
    unfold latSum
    rw [mul_finsum]
    exact finsum_congr fun q => by beta_reduce; rw [hinv x _ (Subtype.property _)]
  · intro x hx
    exact hdiv 1 x (hsupp x (left_ne_zero_of_mul hx))
  · intro x y hxy
    rw [thInd_congr_of_sub_mem A S L L' (c * c') x y hxy]
    have := hinv y _ (hBC hxy)
    rw [add_sub_cancel] at this
    rw [this]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.hermitianLatticeTransport_preserves_selfDual : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → ∀ (n : ℕ), StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat L → StandardLatticesGL3.SD D (s.lat L) := by
  first | exact @GlobalTheory.SeamSelfDual.seam_selfDual | exact GlobalTheory.SeamSelfDual.seam_selfDual | (intros; apply GlobalTheory.SeamSelfDual.seam_selfDual <;> assumption)
end

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology ComplexConjugate

namespace GlobalTheory.CMModel

theorem mem_lattice_of_even_kerReps :
    ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  intro L α a S hα hst hS hev h1 h2
  obtain ⟨m, hm⟩ := hev
  have hc := kerRepsCard L α S hα hst hS
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hst
  have hN : α * conj α = 2 * (m : ℂ) + 1 := by
    rw [Complex.mul_conj, ← hc, hm]
    push_cast
    ring
  have key : a = t • (α * a) - α * (α * a) - m • (2 * a) := by
    rw [zsmul_eq_mul, nsmul_eq_mul, ← ht]
    linear_combination (-a) * hN
  rw [key]
  exact sub_mem (sub_mem (zsmul_mem h1 t) (hst _ h1)) (nsmul_mem h2 m)

end GlobalTheory.CMModel
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_minimal_KType_second_member : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  first | exact @GlobalTheory.FockAlg.min_second | exact GlobalTheory.FockAlg.min_second | (intros; apply GlobalTheory.FockAlg.min_second <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.inertPrimeLossBound_eventually : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  first | exact @GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible | exact GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible | (intros; apply GlobalTheory.InertLossAdm.inertPrimes_loss_log_sum_admissible <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem _root_.GlobalTheory.T.exists_local_spec_finite_free_of_finite_flat : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  first | exact @GlobalTheory.FiniteFlatLocal.exists_finFree_local | exact GlobalTheory.FiniteFlatLocal.exists_finFree_local | (intros; apply GlobalTheory.FiniteFlatLocal.exists_finFree_local <;> assumption)
end
