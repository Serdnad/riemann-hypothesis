module

public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormal
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle335
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle544
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle641
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle595
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  first | exact @GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | exact GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | (intros; apply GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem sst_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → IsDR (P.PD K) ρ := by
  intro l _ P AI T K V _ _ _ ρ hρ
  obtain ⟨ι, -, hι⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_semistable_period_matrix_of_isSemistable l P AI T _ K V b ρ hρ
  refine GlobalTheory.T.isDeRham_of_invertible_periodMatrix l P _ K V b ρ (Matrix.GeneralLinearGroup.map ι.toRingHom Q) ?_
  intro g
  have hmap : ((Matrix.GeneralLinearGroup.map ι.toRingHom Q : GL (Fin (finrank ℚ_[l] V)) P.R.BdR) :
      Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) P.R.BdR)
      = (Q : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P)).map ι := rfl
  have h := congrArg (fun M => M.map ι) (hQ g)
  simp only [Matrix.map_mul, Matrix.map_map] at h
  rw [hmap]
  conv_rhs => rw [← h]
  congr 1
  · ext i j
    exact (ι.commutes _).symm
  · rw [Matrix.map_map]
    congr 1
    funext x
    exact (hι _ x).symm

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChiTame

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k), D.nd.l i ≠ D.host.g k → ∀ s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)), D.nd.chi i 1 s = 1 := by
  intro D i k v hne s hs
  have hwg : D.naut.plGw k v ∈ placesOver D.host.E (D.host.g k) := D.naut.plGw_over k v
  have hpl := D.nd.plOm.2 (D.naut.plGw k v)
  have hI : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) := GlobalTheory.TameGenPowers.wild_mem_Ine hs
  have hcop : (D.nd.l i).Coprime (D.host.g k) :=
    (Nat.coprime_primes (D.nd.lPrime i).out (D.host.g_prime k)).2 hne
  have hgv : (D.nd.plOm.1 (D.naut.plGw k v)).valuation ((D.host.g k : ℕ) : D.nd.Om) < 1 := by
    have h2 := (hpl _).2 hwg
    simpa using h2
  have hvl : D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) := by
    intro hl
    have h2 := (hpl _).2 hl
    exact GlobalTheory.WildKill.not_lt_one_of_coprime _ hcop hgv (by simpa using h2)
  have hl : D.ntw.l (D.ntw.twOf i) = D.nd.l i := D.ntw.twOf_l i
  have ht := D.ntw.twistCharacterFamily_tame (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) k _ hwg (by rw [hl]; exact hvl)
    _ hpl s hI
  obtain ⟨n, hn⟩ := D.ntw.psiL_ord i s
  have h1 : ((Units.map (D.ntw.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i))) s ^ (D.host.g k - 1) = 1 := by
    rw [MonoidHom.comp_apply, ← map_pow, ht, map_one]
  have hpow : D.nd.chi i 1 s ^ ((D.host.g k - 1) * D.nd.l i ^ n) = 1 := by
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, mul_pow, pow_mul, h1, one_pow, one_mul, pow_mul', hn, one_pow]
  have := D.nd.trO i
  exact GlobalTheory.WildSetSQ.char_eq_one_of_wild (D.nd.plOm.1 (D.naut.plGw k v)) (D.nd.O_adic i) (D.nd.chi i 1)
    (D.nd.chi_cont i 1) s hs _
    (GlobalTheory.WildKill.not_lt_one_of_coprime _
      (Nat.Coprime.mul_left (GlobalTheory.WildSetSQ.coprime_pred _ (D.host.g_prime k).one_lt.le)
        (Nat.Coprime.pow_left n hcop)) hgv) hpow

end GlobalTheory.ChiTame
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DcrisExact

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

theorem mapVB_eq_rTensor (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [Formalism.MainNotions.RamifiedCoefficientChains.mapVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_Dcris' (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mapVB_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f (actVB PD ρ g x) =
      actVB PD σ g (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, Formalism.MainNotions.RamifiedCoefficientChains.mapVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mapVB_mem_Dcris (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x ∈ Dcris PD σ := by
  rw [mem_Dcris'] at hx ⊢
  intro g
  rw [← mapVB_act PD ρ σ f hf, hx]

theorem ιV_mapVB (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := W) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) =
      AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, Formalism.MainNotions.RamifiedCoefficientChains.mapVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_mem_FilV (f : V →ₗ[LL] W) (a : ℤ) {y : V ⊗[Qp] BdR}
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := W) a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f (LinearMap.id : ↥((PD.Fil a).restrictScalars Qp) →ₗ[Qp] ↥((PD.Fil a).restrictScalars Qp)) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mapVB_mem_FilCris (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (a : ℤ) {x : V ⊗[Qp] B} (hx : x ∈ FilCris PD ρ a) :
    Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x ∈ FilCris PD σ a := by
  refine ⟨mapVB_mem_Dcris PD ρ σ f hf hx.1, ?_⟩
  show ιV PD (LL := LL) (V := W) (Formalism.MainNotions.RamifiedCoefficientChains.mapVB (B := B) LL f x) ∈ FilV PD (LL := LL) (V := W) a
  rw [ιV_mapVB]
  exact map_mem_FilV PD f a hx.2

end Abstract

end GlobalTheory.Per.DcrisExact

namespace GlobalTheory.Per.DcrisExact

open GlobalTheory.Per.DcrisExact

theorem exactStrict (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict (P.PD K) ↥LL.1 := by
  intro hb V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hinj hsurj hex hc₀ hc₁ hc₂
  have hE : Function.Exact (ι.restrictScalars ℚ_[l]) (π.restrictScalars ℚ_[l]) := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.restrictScalars_apply]
    have := congrArg (fun S : Submodule ↥LL.1 V₁ => x ∈ S) hex
    simpa using this
  have hexT := rTensor_exact P.R.B (f := ι.restrictScalars ℚ_[l]) (g := π.restrictScalars ℚ_[l]) hE hsurj
  have hinjT : Function.Injective ((ι.restrictScalars ℚ_[l]).rTensor P.R.B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hinj
  have hS := GlobalTheory.T.dcris_strict_hodgeFiltration_unramified l P AI hT K LL hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ hx
    apply hinjT
    rw [← mapVB_eq_rTensor, hx, map_zero]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨mapVB_mem_Dcris _ ρ₀ ρ₁ ι hι hx, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, mapVB_eq_rTensor, mapVB_eq_rTensor,
        ← LinearMap.rTensor_comp_apply]
      have : (π.restrictScalars ℚ_[l]).comp (ι.restrictScalars ℚ_[l]) = 0 := by
        ext v
        exact hE.apply_apply_eq_zero v
      rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]
    · rintro y ⟨hy, hk⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, mapVB_eq_rTensor] at hk
      obtain ⟨x, hx⟩ := (hexT y).mp hk
      rw [← mapVB_eq_rTensor] at hx
      refine ⟨x, ?_, hx⟩
      have hy' := (mem_Dcris' _ ρ₁ y).1 hy
      rw [SetLike.mem_coe, mem_Dcris']
      intro g
      apply hinjT
      rw [← mapVB_eq_rTensor, ← mapVB_eq_rTensor, mapVB_act _ ρ₀ ρ₁ ι hι, hx, hy' g]
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mapVB_mem_Dcris _ ρ₁ ρ₂ π hπ hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI hT K LL V₁ ρ₁ V₂ ρ₂ π hπ).2
        hsurj hc₁).2 y hy
      exact ⟨x, hx, hxy⟩
  · intro a
    refine ⟨(hS V₁ ρ₁ V₂ ρ₂ π hπ).1 hsurj hc₁ a, ?_⟩
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, mapVB_mem_FilCris _ ρ₀ ρ₁ ι hι a hx⟩
    · rintro x ⟨hx, hf⟩
      exact (hS V₀ ρ₀ V₁ ρ₁ ι hι).2 hinj a x hx hf

end GlobalTheory.Per.DcrisExact

namespace GlobalTheory.Per.DcrisExact

theorem fontaine_dcris : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  intro D l _ K LL
  refine ⟨exactStrict l (D.loc l) (D.locA l) (D.locT l) K LL, ?_, ?_⟩
  · intro V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hinj hsurj _ hc₁
    exact ⟨(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) (D.locT l) K LL V₀ ρ₀ V₁ ρ₁ ι hι).1
        hinj hc₁,
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) (D.locT l) K LL V₁ ρ₁ V₂ ρ₂ π hπ).2
        hsurj hc₁).1⟩
  · intro hb V _ _ _ _ _ ρ hc
    exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DcrisExact
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecGalois

theorem exists_continuousMulEquiv : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∃ i : ↥(A.decompositionSubgroup F) ≃ₜ*
      (PadicAlgCl p ≃ₐ[↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)))] PadicAlgCl p),
      ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x) := by
  intro p _ F Ω _ _ _ _ _ A j hj
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  let e2 : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K.1] PadicAlgCl p) :=
    e.trans (IntermediateField.fixingSubgroupEquiv K.1)
  refine ⟨{ e2 with continuous_toFun := hf.comp he, continuous_invFun := he'.comp hf' }, fun g x => ?_⟩
  exact hec g x

end GlobalTheory.DecGalois
end
