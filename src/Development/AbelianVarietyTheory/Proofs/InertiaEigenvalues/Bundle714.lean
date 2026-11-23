module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle356
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle697
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeightsoundQdPlacesUniformConst
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.UnramifiedTrivial

theorem unramifiedCocycles_le_blochKatoFinite_trivial {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≤
      finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : P.R.B, ∀ g : ↥(GK K),
      P.actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    GlobalTheory.UnramifiedCrys.exists_rat AI T K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add (f := _)]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩

  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] P.actQ g (b i) := by
    rw [← P.PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

theorem Z1ur_ne_bot {l : ℕ} [Fact l.Prime] (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≠ ⊥ := by
  obtain ⟨δ, hδc, hδa, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  haveI := LL.2
  let c : ↥(GK K) → ↥LL.1 := fun g => algebraMap ℚ_[l] ↥LL.1 (δ g)
  have hcc : Continuous c :=
    (Algebra.linearMap ℚ_[l] ↥LL.1).continuous_of_finiteDimensional.comp hδc
  have hmem : c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) := by
    refine ⟨⟨hcc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · simp [c, hδa, map_add (f := _)]
    · simp [c, hδI g hg]
  intro h
  rw [h] at hmem
  have := congrFun ((Submodule.mem_bot _).1 hmem) g₀
  exact hg₀ (by simpa [c] using this)

end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem finrank_Z1f_trivial {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) =
      finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) := by
  have hB1 : B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob]
  have hc : (B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).comap
      (finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).subtype = ⊥ := by
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  exact (Submodule.quotEquivOfEqBot _ hc).finrank_eq.symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem unrTriv_of_finrank {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l)
    (h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1) :
    UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  have hZ : finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 :=
    (finrank_Z1f_trivial P K LL).trans h1
  haveI : FiniteDimensional ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) :=
    Module.finite_of_finrank_eq_succ hZ
  have hle := unramifiedCocycles_le_blochKatoFinite_trivial AI T K LL
  haveI := Submodule.finiteDimensional_of_le hle
  have hpos : 0 < finrank ↥LL.1 ↥(Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K)) := by
    refine Nat.pos_of_ne_zero fun h0 => Z1ur_ne_bot K LL ?_
    exact Submodule.finrank_eq_zero.1 h0
  unfold UnrTriv
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hZ]; exact hpos)).symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial

theorem unrTriv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  intro l _ P AI T K LL
  haveI := LL.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := 1
      cont := fun x => (continuous_const : Continuous fun _ : ↥(GK K) => x) }
  have hDR : IsDR (P.PD K) A.ρ := GlobalTheory.CrysExt.isDR_trivial (P.PD K)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI T K ↥LL.1 ↥(OL LL) hgood A hDR
  have hH0 : H0V A.ρ = ⊤ := by
    refine eq_top_iff.2 fun x _ => (Submodule.mem_iInf _).2 fun g => ?_
    simp [A, H0V]
  have hFil : DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0 = DdR (P.PD K) A.ρ := by
    refine inf_eq_left.2 fun x hx => ?_
    change x ∈ DdR (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) at hx
    rw [GlobalTheory.CrysExt.ddR_trivial] at hx
    obtain ⟨z, rfl⟩ := hx
    exact GlobalTheory.CrysExt.incl_mem_FilV (P.PD K) le_rfl z
  have e1 : finrank ↥LL.1 ↥(H0V A.ρ) = 1 := by rw [hH0, finrank_top]; exact Module.finrank_self _
  rw [hFil] at hdim
  have h1' : finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) = 1 := by omega
  have h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 := h1'
  exact unrTriv_of_finrank AI T K LL h1

end GlobalTheory.UnramifiedTrivial
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.FilInv

theorem pow_mem_Fil {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {b : ℤ} {x : BdR} (hx : x ∈ PD.Fil b) (n : ℕ) :
    x ^ n ∈ PD.Fil (n * b) := by
  induction n with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact PD.Fil_mul _ _ _ _ ih hx

theorem inv_mem_Fil_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  intro l _ P AI T K a u v huv hu hu1
  obtain ⟨s, hs, hts⟩ := GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K
  have ht := (P.PD K).mem_filtration_one

  obtain ⟨w, w', hw, hw', hww⟩ : ∃ w w' : P.R.BdR, w ∈ (P.PD K).Fil (-a) ∧ w' ∈ (P.PD K).Fil a ∧
      w * w' = 1 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · refine ⟨s ^ n, ((P.PD K).ι (P.PD K).t) ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) hs n
      · simpa using pow_mem_Fil (P.PD K) ht n
      · rw [← mul_pow, mul_comm, hts, one_pow]
    · refine ⟨((P.PD K).ι (P.PD K).t) ^ n, s ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) ht n
      · simpa using pow_mem_Fil (P.PD K) hs n
      · rw [← mul_pow, hts, one_pow]
  have hx0 : u * w ∈ (P.PD K).Fil 0 := by
    simpa using (P.PD K).Fil_mul _ _ _ _ hu hw
  have hx1 : u * w ∉ (P.PD K).Fil 1 := by
    intro h
    apply hu1
    have := (P.PD K).Fil_mul _ _ _ _ h hw'
    rwa [mul_assoc, hww, mul_one, add_comm] at this
  obtain ⟨y, hy, hxy⟩ := ((GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.2) K _ hx0 hx1
  have hv : v = w * y := by
    calc v = v * ((u * w) * y) := by rw [hxy, mul_one]
      _ = (u * v) * (w * y) := by ring
      _ = w * y := by rw [huv, one_mul]
  rw [hv]
  simpa using (P.PD K).Fil_mul _ _ _ _ hw hy

end GlobalTheory.FilInv
end

section

namespace CrystallineMultiplicity
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CompanionTheory.CharInv

theorem isCrys_and_multV_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  intro l _ P AI T K LL μ a hμ hm
  obtain ⟨h1, -, h2⟩ := GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 0
  rw [zpow_zero] at h1
  simp only [zpow_zero] at h2
  have hρ : ∀ g x, charRep (1 : ↥(GK K) →* (↥LL.1)ˣ) g x = (μ g : ↥LL.1) • charRep μ⁻¹ g x :=
    fun g x => by simp [charRep]
  refine ⟨(GlobalTheory.TopSteps.CrysRules.isCrys_iff T K LL _ _ μ hρ hμ).2 h1, fun τ c => ?_⟩
  have hs := GlobalTheory.TopSteps.CrysRules.multV_shift T K LL _ _ μ hρ hμ τ (a τ)
    (fun b => by rw [hm, Multiset.count_singleton]; split_ifs <;> rfl) c
  rw [← hs, h2]
  exact if_congr (by omega) rfl rfl

end GlobalTheory.CompanionTheory.CharInv

end

end CrystallineMultiplicity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
theorem _root_.GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ), IsCrys (P.PD K) (charRep μ) → (∀ τ b, multV (P.PD K) (charRep μ) τ b = if b = a τ then 1 else 0) → IsCrys (P.PD K) (charRep μ⁻¹) ∧ ∀ τ b, multV (P.PD K) (charRep μ⁻¹) τ b = if b = -a τ then 1 else 0 := by
  first | exact @CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | exact CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv | (intros; apply CrystallineMultiplicity.GlobalTheory.CompanionTheory.CharInv.isCrys_and_multV_inv <;> assumption)

end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InvJump

open Module

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def qRep (ρ : Representation LL G V) (p : Submodule LL V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    Representation LL G (V ⧸ p) where
  toFun g := p.mapQ p (ρ g) (fun x hx => hp g x hx)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

end Gen

theorem h0V_eq_bot_of_multV_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ hdR hm
  haveI := K.2
  haveI := LL.2
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hne
  have hinv : ∀ g, ρ g v = v := by
    intro g
    have := (Submodule.mem_iInf _).1 hv g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this

  let σ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) := 1
  let ι : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] V := (LinearMap.proj 0).smulRight v
  have hι : ∀ u, ι u = u 0 • v := fun u => rfl
  have hιeq : ∀ g x, ι (σ g x) = ρ g (ι x) := by
    intro g x
    rw [hι, hι, map_smul, hinv]
    rfl
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, hι] at hu
    have h0 : u 0 = 0 := (smul_eq_zero.1 hu).resolve_right hv0
    funext c
    rw [Subsingleton.elim c 0, h0]
    rfl
  let p : Submodule ↥LL.1 V := LinearMap.range ι
  have hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨σ g u, hιeq g u⟩
  let ρ₂ := GlobalTheory.InvJump.qRep ρ p hp
  have hπeq : ∀ g x, p.mkQ (ρ g x) = ρ₂ g (p.mkQ x) := fun g x => rfl
  obtain ⟨-, -, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T K LL (Fin 1 → ↥LL.1) σ V ρ (V ⧸ p) ρ₂
    ι p.mkQ hιeq hπeq hιinj (Submodule.mkQ_surjective p) (Submodule.ker_mkQ p).symm hdR
  have h1 : multV (P.PD K) σ τ 0 = 1 := by
    have := GlobalTheory.PtCore.multV_cycPow_line (P.PD K) (GlobalTheory.DRFil.isField_dR T)
      (GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K) σ 0 (fun g u => by simp [σ]) τ 0
    simpa using this
  have h2 := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL (V ⧸ p) ρ₂ τ 0).2.1
  have h3 := (hadd τ 0).2.1
  omega

end GlobalTheory.InvJump
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.h1fT_span_card_bound : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ T : LocLat ↥(GK K) ℚ_[l] LL O, IsDR (P.PD K) T.ρ → ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology (P.PD K) T.L ∧ s.card + finrank LL ↥(H0V T.ρ) ≤ finrank LL (FiniteCohomology (P.PD K) T.ρ) + finrank LL T.V := by
  first | exact @GlobalTheory.H1fGeneratorsAlt.h1fT_generators | exact GlobalTheory.H1fGeneratorsAlt.h1fT_generators | (intros; apply GlobalTheory.H1fGeneratorsAlt.h1fT_generators <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HubLoc

open Formalism.FrobeniusOrbits

section Gen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem kw_eq_sup_of_gens (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (g₁ g₂ g₃ : H.E)
    (hgen : ∀ M : IntermediateField ℚ_[l] (Om l), J g₁ ∈ M → J g₂ ∈ M → J g₃ ∈ M → ∀ x : H.E, J x ∈ M) :
    Kw.1 = IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) ⊔
      IntermediateField.adjoin ℚ_[l] {J g₃} := by
  set M := IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) with hM
  set N := M ⊔ IntermediateField.adjoin ℚ_[l] {J g₃} with hN
  have hfM : FiniteDimensional ℚ_[l] ↥M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x
  have hfy : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {J g₃}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) _)
  have hfN : FiniteDimensional ℚ_[l] ↥N := IntermediateField.finiteDimensional_sup _ _
  have hcl : IsClosed ((N : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional N.toSubalgebra.toSubmodule
  have h1 : J g₁ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h2 : J g₂ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h3 : J g₃ ∈ N := le_sup_right (a := M) (IntermediateField.mem_adjoin_simple_self _ _)
  apply le_antisymm
  · intro x hx
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨z, rfl⟩
    exact hgen N h1 h2 h3 z
  · refine sup_le ?_ ?_
    · rw [hM, IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      exacts [hE g₁, hE g₂]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact hE g₃

theorem sq_aE_image : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
  rw [← map_pow, H.sqq_sq]; simp

theorem sq_bE_image : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
  rw [← map_pow, H.sqd_sq]; simp

theorem kw_eq_sup_sqrt (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (hl : l = H.q ∨ l = H.d) :
    ∃ M : IntermediateField ℚ_[l] (Om l), M ≤ MaximalUnramifiedExtension l ∧ ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
  have hh := H.hyp
  have hq2 : H.q % 4 = 3 := by have := hh.2.2.1; omega
  have hd2 : H.d % 4 = 3 := by have := hh.2.2.2.1; omega
  have hqd : H.q ≠ H.d := by have := hh.2.2.1; have := hh.2.2.2.1; omega
  have hlS : ¬ l ∣ H.QS := UpperTheory.Small.not_dvd_QS H Fact.out (UpperTheory.Small.not_mem_of_qd H hl)
  have hθ := theta_mem_Kur H J
  rcases hl with rfl | rfl
  · refine ⟨_, ?_, _, sq_aE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.q) (H.sqd)
      (H.sqq) fun M m1 m2 m3 x => image_le H J hlS M m1 m3 m2 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.d hh.2.1 hd2 hqd.symm _ (sq_bE_image H J)
  · refine ⟨_, ?_, _, sq_bE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.d) (H.sqq)
      (H.sqd) fun M m1 m2 m3 x => image_le H J hlS M m1 m2 m3 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.q hh.1 hq2 hqd _ (sq_aE_image H J)

end Gen

theorem kw_eq_unram_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
      ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  intro D i hl w hw
  exact kw_eq_sup_sqrt D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense hl

end GlobalTheory.HubLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem actO_map_haar : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (μ : Measure (WO S T)),
    μ.IsAddHaarMeasure → μ.map (actO S T g h) = μ := by
  intro D S T g h μ hμ
  haveI : BorelSpace (Mx D T.rank S.rank) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hL : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) :=
    continuous_const.matrix_mul continuous_id
  have hR : Continuous (fun x : Mx D T.rank S.rank =>
      (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) :=
    continuous_id.matrix_mul continuous_const
  have e : actO S T g h =
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) : Mx D T.rank S.rank)) ∘
      (fun x : Mx D T.rank S.rank =>
        (HMul.hMul (mt T h) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) : Mx D T.rank S.rank)) := rfl
  rw [e, ← Measure.map_map hR.measurable hL.measurable, GlobalTheory.T.map_mt_mul_left_adelicMatrix_haar_eq D T S.rank h μ hμ]
  exact GlobalTheory.T.map_mul_right_unitaryAdelicMatrix_addHaar D S T.rank g⁻¹ μ hμ

end GlobalTheory
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.local_comparison_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  first | exact @GlobalTheory.NL.SandJumps.main | exact GlobalTheory.NL.SandJumps.main | (intros; apply GlobalTheory.NL.SandJumps.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.blockBound_qd_places_uniformConst : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := by
  first | exact @GlobalTheory.TheoremBTB.main | exact GlobalTheory.TheoremBTB.main | (intros; apply GlobalTheory.TheoremBTB.main <;> assumption)
end
