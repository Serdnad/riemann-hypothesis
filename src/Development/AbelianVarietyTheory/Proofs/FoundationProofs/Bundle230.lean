module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle223
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle002
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle214
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle135
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

open scoped UpperHalfPlane nonZeroDivisors Real

theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 : eisG Λ k = ∑' z : ℂ, ({w : ℂ | w ∈ Λ ∧ w ≠ 0}).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, eisG]
    exact tsum_congr fun w => one_div _
  have h2 : L.G (2 * k) = ∑' z : ℂ, (L.lattice : Set ℂ).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, PeriodPair.G]
    rfl
  rw [h1, h2]
  refine tsum_congr fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hz, h]

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha

theorem indep_of_tau : LinearIndependent ℝ ![a * (τ : ℂ), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t e
  have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
    simp only [Complex.real_smul] at e
    linear_combination e)
  have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
  exact ⟨e3, by simpa [e3] using e2⟩

include h

omit ha in
theorem eq_closure_of_tau : Λ = AddSubgroup.closure {a * (τ : ℂ), a} := by
  ext x
  rw [h, AddSubgroup.mem_closure_pair]
  refine exists_congr fun m => exists_congr fun n => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, show (m : ℂ) * (a * τ) + n * a = a * (m * τ + n) by ring]

theorem discr_of_tau : TaylorLogMetric.discr Λ = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  let L : PeriodPair := ⟨a * τ, a, indep_of_tau ha⟩
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := fun x => by
    rw [PeriodPair.mem_lattice]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [show (m : ℂ) * L.ω₁ + n * L.ω₂ = a * (m * τ + n) by simp only [L]; ring]
  have hh : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by rw [h, hL]
  rw [← latticeCurve_Δ_eq_discriminant ha hL, latticeCurve_Δ, TaylorLogMetric.discr, g2, g3,
    eisG_eq_G L Λ hh (by norm_num), eisG_eq_G L Λ hh (by norm_num)]
  rfl

theorem area_of_tau : area Λ = ‖a‖ ^ 2 * τ.im := by
  apply GlobalTheory.LatticeAreaBound.area_eq <;> assumption

end

theorem mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) :
    w ∈ lamOf D cc δ ↔ ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem finrank_hostK (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K D.host.hyp.2.1.pos (D.host.sqd_sq)

theorem discr_hostK (D : D7) : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_hostK D) D.host.hyp.2.1.squarefree
    (by have := D.host.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq))

theorem exists_tau (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ (Ideal.absNorm cc : ℝ) = 2 * ‖a‖ ^ 2 * τ.im / √(D.host.d) ∧
      ∀ δ x : ℂ, x ∈ lamOf D cc δ ↔ ∃ m n : ℤ, δ * a * (m * (τ : ℂ) + n) = x := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let I : (Ideal (𝓞 D.host.K))⁰ := ⟨cc, mem_nonZeroDivisors_of_ne_zero hcc⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_hostK D) (discr_hostK D) σ
    (FractionalIdeal.mk0 D.host.K I)
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have h' : ∀ z, z ∈ σ '' (cc : FractionalIdeal (𝓞 D.host.K)⁰ D.host.K) ↔
      ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = z := fun z => by
    rw [← h, ← SetLike.mem_coe, hL]
    rfl
  have hN := QuadraticZeta.absNorm_eq_of_image (finrank_hostK D) (discr_hostK D) σ ha h'
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at hN
  refine ⟨a, τ, ha, hN, fun δ x => ?_⟩
  rw [mem_lamOf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := (h' _).1 ⟨(c : D.host.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
    exact ⟨m, n, by rw [mul_assoc, e]; rfl⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨y, hy, e⟩ := (h' _).2 ⟨m, n, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, by rw [mul_assoc, ← e]; rfl⟩

theorem lattice_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  intro D _ cc δ ⟨⟨hcc, _⟩, hδ⟩
  obtain ⟨a, τ, ha, hN, h⟩ := exists_tau D cc hcc
  have h1 := discr_of_tau (by simpa using ha) (h 1)
  rw [one_mul] at h1
  have hδ' : δ ^ 12 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := hδ.trans h1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have := ModularForm.discriminant_ne_zero τ
    have := Real.pi_ne_zero
    simp [*] at hδ'
  have hda : δ * a ≠ 0 := mul_ne_zero hδ0 ha
  refine ⟨⟨_, _, indep_of_tau (τ := τ) hda, eq_closure_of_tau (h δ)⟩, hδ0, ?_, ?_, ?_⟩
  · rw [discr_of_tau hda (h δ), show (2 * π / (δ * a) : ℂ) ^ 12 * ModularForm.discriminant τ =
      ((2 * π / a) ^ 12 * ModularForm.discriminant τ) / δ ^ 12 by field_simp, ← hδ',
      div_self (pow_ne_zero _ hδ0)]
  · have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    rw [area_of_tau hda (h δ), hN, norm_mul]
    field_simp
  · intro b w hw
    obtain ⟨c, hc, rfl⟩ := (mem_lamOf D cc δ w).1 hw
    exact (mem_lamOf D cc δ _).2 ⟨b * c, cc.mul_mem_left b hc, by simp; ring⟩

end GlobalTheory.CurveLattice
end

section

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Bases

variable {Z O R M J ι : Type} [CommRing Z] [CommRing O] [CommRing R] [Algebra Z O] [Algebra Z R]
  [AddCommGroup M] [Module O M] [Fintype J] [Fintype ι] (o : Module.Basis J Z O) {r : ℕ}
  (e : Fin r ≃ ι × J)

end Bases

section Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {Z R RA : Type} [CommRing Z] [CommRing R] [CommRing RA] [Algebra Z O]
    [Algebra Z R] [Algebra O RA] {inclR : RA →ₐ[O] O ⊗[Z] R} {φR : O ⊗[Z] R →ₐ[O] O ⊗[Z] R}
    {gR : G → (O ⊗[Z] R →ₐ[O] O ⊗[Z] R)} {πA : RA}
    (E : EtTie W RA (O ⊗[Z] R) inclR φR gR πA) (A : Subring R)
    (hA : ∀ (lam : O →ₗ[Z] Z) a, cf lam (sc E a) ∈ A) {Y : LocLat G Qp LL O}
    {J ι : Type} [Fintype J] [Fintype ι] (o : Module.Basis J Z O)



end Module

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}


end Transport

section RankOne

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))


end RankOne

section Situation

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_levelFieldFiniteExtension (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℚ_[l] ↥(K0 (levelField K s)) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h1 : Ks (levelField K s) s = Ks K s := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le_sup_right ?_ _)
    exact le_inf le_sup_left inf_le_right
  have h2 := GlobalTheory.Cyc.finrank_Ks (levelField K s) s hs
  rw [h1, GlobalTheory.Cyc.finrank_Ks K s hs] at h2
  have h3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (pow_pos (by omega) _)) h2).symm

theorem val_le_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (s : ℕ) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ s * y := ⟨((l : ℚ_[l]) ^ s)⁻¹ * x, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l,
    norm_mul, norm_pow, Padic.norm_p, nsmul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
    mul_le_iff_le_one_right (zpow_pos hl1 _)]
  have h1 : (s : WithTop ℚ) ≤ s + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔
      0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    conv_lhs => lhs; rw [← add_zero (s : WithTop ℚ)]
    exact WithTop.add_le_add_iff_left (WithTop.natCast_ne_top s)
  rw [h1, P.v_O]
  change IsIntegral ℤ_[l] _ ↔ _
  rw [isIntegral_algebraMap_iff , IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩

theorem absoluteGalois_mem_fixingSubgroup_maxUnramified {K : FinExt l} (g : ↥(GK K)) : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
  fun x => g.2 ⟨x.1, x.2.1⟩

section Wach

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}

theorem mem_GKs (hs : W.s = s) (g : ↥(GK K)) : g ∈ W.GKs ↔ (g : GQ l) ∈ GK (levelField K s) := by
  rw [W.GKs_def, hs, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, val_le_iff]
  exact (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g (absoluteGalois_mem_fixingSubgroup_maxUnramified g)).1 s).symm

theorem prim_ζQ (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h : ∀ j, P.ζQ (j + 1) ^ l ^ j = P.ζQ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [h]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, h, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem resΓ_eq_one (g : ↥(GK K)) (hg : ∀ j : ℕ, (g : GQ l) (P.ζQ j) = P.ζQ j) : W.resΓ g = 1 := by
  have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ := GlobalTheory.Cyc.exists_zpow_neg_lt (l := l) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have h2 := GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim P.χQ_cyc g _ (prim_ζQ P m) (hg _)
    have h3 : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(m : ℤ)) :=
      zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le) (by push_cast; omega)
    exact absurd (h2.trans h3) (not_le.mpr hm)
  apply W.χΓ_inj
  apply Units.ext
  apply Subtype.val_injective
  have h2 := W.χΓ_res g
  rw [P.PD_χ, h1, map_one] at h2
  rw [map_one]
  exact h2

variable (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

end Wach

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.LiftSizeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

theorem telescope (a k b : ℕ) (hb : b ≤ a) :
    (∏ c ∈ Finset.range b, (a - c - 1 + (k + 1) + 1)) * (a - b + k + 1) =
      (∏ c ∈ Finset.range b, (a - c - 1 + k + 1)) * (a + k + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have h1 : a - b - 1 + (k + 1) + 1 = a - b + k + 1 := by omega
    have h2 : a - (b + 1) + k + 1 = a - b - 1 + k + 1 := by omega
    rw [h1, h2, ih (by omega)]
    ring

theorem row_hook (ν : ℕ → ℕ) (r k : ℕ) (hν : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x) :
    (∏ c ∈ Finset.range (ν r),
        ((ν r - c - 1) + ((Finset.Ioo r (r + 1 + k)).filter (fun r' => c < ν r')).card + 1)) *
      ∏ l ∈ Finset.Ioo r (r + 1 + k), (ν r - ν l + (l - r)) = (ν r + k).factorial := by
  induction k with
  | zero =>
    have he : Finset.Ioo r (r + 1 + 0) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.prod_empty, mul_one, Nat.add_zero]
    simp only [Finset.filter_empty, Finset.card_empty, add_zero]
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    omega
  | succ k ih =>
    have hν' : ∀ x y, x ≤ y → y < r + 1 + k → ν y ≤ ν x := fun x y hxy hy => hν x y hxy (by omega)
    have IH := ih hν'
    set m := r + 1 + k with hm
    have hIns : Finset.Ioo r (r + 1 + (k + 1)) = insert m (Finset.Ioo r m) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hmn : m ∉ Finset.Ioo r m := by simp
    have hba : ν m ≤ ν r := hν r m (by omega) (by omega)
    have hcardIoo : (Finset.Ioo r m).card = k := by rw [Nat.card_Ioo]; omega
    rw [hIns, Finset.prod_insert hmn]
    rw [← Finset.prod_range_mul_prod_Ico _ hba] at IH ⊢
    have hlow : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + (k + 1) + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem (by simp),
        Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hlow' : ∀ c ∈ Finset.range (ν m),
        ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + k + 1 := by
      intro c hc
      rw [Finset.mem_range] at hc
      rw [Finset.filter_true_of_mem (fun l hl => ?_), hcardIoo]
      rw [Finset.mem_Ioo] at hl
      exact lt_of_lt_of_le hc (hν l m hl.2.le (by omega))
    have hhigh : ∀ c ∈ Finset.Ico (ν m) (ν r),
        ν r - c - 1 + ((insert m (Finset.Ioo r m)).filter (fun r' => c < ν r')).card + 1 =
          ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1 := by
      intro c hc
      rw [Finset.mem_Ico] at hc
      rw [Finset.filter_insert, if_neg (by omega)]
    rw [Finset.prod_congr rfl hlow, Finset.prod_congr rfl hhigh]
    rw [Finset.prod_congr rfl hlow'] at IH
    have hT := telescope (ν r) k (ν m) hba
    have hd : ν r - ν m + (m - r) = ν r - ν m + k + 1 := by omega
    rw [hd, show ν r + (k + 1) = (ν r + k) + 1 by ring, Nat.factorial_succ, ← IH]
    calc (∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ((ν r - ν m + k + 1) * ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)))
        = ((∏ c ∈ Finset.range (ν m), (ν r - c - 1 + (k + 1) + 1)) * (ν r - ν m + k + 1)) *
          (∏ c ∈ Finset.Ico (ν m) (ν r),
            (ν r - c - 1 + ((Finset.Ioo r m).filter (fun r' => c < ν r')).card + 1)) *
          ∏ l ∈ Finset.Ioo r m, (ν r - ν l + (l - r)) := by ring
      _ = _ := by rw [hT]; ring

theorem hookProd_mul (n : ℕ) (ν : ℕ → ℕ) (hν : ∀ x y, x ≤ y → y < n → ν y ≤ ν x) :
    hookProd n ν * ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (ν r - ν l + (l - r)) =
      ∏ r ∈ Finset.range n, (ν r + n - 1 - r).factorial := by
  unfold hookProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  have e : r + 1 + (n - 1 - r) = n := by omega
  have h := row_hook ν r (n - 1 - r) (fun x y hxy hy => hν x y hxy (by omega))
  rw [e] at h
  rw [h]
  congr 1
  omega

variable (D : D7) (L : SizeData₂ D)

variable {eps : ℝ} (Fm : FamP eps)

end GlobalTheory.LiftSizeCompare

end
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  first | exact @GlobalTheory.FockMinorExtremal.delta_extremal | exact GlobalTheory.FockMinorExtremal.delta_extremal | (intros; apply GlobalTheory.FockMinorExtremal.delta_extremal <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  first | exact @GlobalTheory.DeltaHighest.delta_mem_hwSub | exact GlobalTheory.DeltaHighest.delta_mem_hwSub | (intros; apply GlobalTheory.DeltaHighest.delta_mem_hwSub <;> assumption)
end
