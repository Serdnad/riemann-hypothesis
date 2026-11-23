module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle391
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle310
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle395
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.twisted_representation_kills_small_subgroup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  first | exact @GlobalTheory.NewPrime.SmallActs.small_acts | exact GlobalTheory.NewPrime.SmallActs.small_acts | (intros; apply GlobalTheory.NewPrime.SmallActs.small_acts <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.JSW

theorem tsum_fibre_entrySum_eq {m : ℕ} {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (F : (Fin m → ℕ) → E) (d : ℕ) :
    ∑' b : (fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}, F b.1.1 =
      ∑ l ∈ antiParts m d, F l := by
  rw [← Finset.tsum_subtype (antiParts m d) F]
  let e : ((fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}) ≃
      {x // x ∈ antiParts m d} :=
    { toFun := fun b => ⟨b.1.1, mem_antiParts.2 ⟨b.2, b.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_antiParts.1 x.2).2⟩, (mem_antiParts.1 x.2).1⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  exact e.tsum_eq (fun x => F x.1)

theorem regroup_antiParts {m : ℕ} (G : (Fin m → ℕ) → ℂ)
    (hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) :
    Summable (fun d => ‖∑ l ∈ antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  set σ : {l : Fin m → ℕ // Antitone l} → ℕ := fun l => ∑ i, l.1 i with hσ
  have h1 := hG.hasSum.tsum_fiberwise σ
  have h1' : Summable (fun d => ∑ l ∈ antiParts m d, ‖G l‖) := by
    refine h1.summable.congr fun d => ?_
    exact tsum_fibre_entrySum_eq (fun l => ‖G l‖) d
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sum_le _ _) h1', ?_⟩
  intro s hs
  have hg : Summable fun l : {l : Fin m → ℕ // Antitone l} => G l.1 := hG.of_norm
  have h2 := hg.hasSum.tsum_fiberwise σ
  have h2' : HasSum (fun d => ∑ l ∈ antiParts m d, G l) (∑' l : {l : Fin m → ℕ // Antitone l}, G l.1) :=
    h2.congr_fun fun d => (tsum_fibre_entrySum_eq G d).symm
  rw [hs.unique h2']
  exact hg.hasSum

end GlobalTheory.JSW
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isDualLat1_dual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) (GlobalTheory.Pass.LocDirect.latDual i w hw M hM) (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  intro D i w hw k M hM
  refine ⟨GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) (Br.loc D.nbr i w hw M) (dualMat i w hw M)
    (fun g => dualMat_apply i w hw M g), fun y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩ _ ⟨z', rfl⟩
    exact ⟨_, GlobalTheory.BKLatticeCochain.incl_dot z' z⟩
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun a => ?_
    obtain ⟨o, ho⟩ := h (GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw))) ⟨_, rfl⟩
    refine ⟨o, ?_⟩
    rw [← ho]
    change GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw)) ⬝ᵥ
      (y : Fin k → Br.LL D.nbr i w hw) = y a
    simp [GlobalTheory.BKLatticeCochain.incl_apply, dotProduct, Pi.single_apply,
      apply_ite (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw))]
    exact (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ a))

theorem isCrys_dual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.Udual i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hF i w hw k M hM K' h hcrys
  haveI := isTopRing i w hw
  have hi : Continuous (Subgroup.inclusion (GK_le h)) := continuous_subtype_val.subtype_mk _
  have hU : Continuous ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM).comp hi
  have hU' : Continuous ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (continuous_dualMat i w hw M hM).comp hi
  have hc : ∀ g : ↥(GK K'), ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)
        (Subgroup.inclusion (GK_le h) g) : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    intro g
    simp only [cycLL, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    congr 1
    rw [(D.loc (D.nd.l i)).PD_χ, Br.PD, (D.loc (D.nd.l i)).PD_χ]
    rfl
  have hd : IsDual1 ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (matRep ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
    refine GlobalTheory.PotDual.isDual1_of_eq _ _ _ fun g => ?_
    rw [hc]
    rfl
  exact (hF (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU)
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU') _ hd hcrys

theorem finrank_H1fT_eq : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL] (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ), (∀ y : G → A.V, Continuous y → ∃ m : O, m ≠ 0 ∧ ∀ g, m • y g ∈ L.T) → finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD A.ρ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ _ A L hT
  have h := GlobalTheory.BlochKatoRank.rank_subquotient_eq (O := O) (K := LL) (X := G → A.V) (Y := G → A.V)
    LinearMap.id (latticeCocycles L) (latticeCoboundaries L) (latticeFiniteCocycles PD L) (finiteCocycles PD A.ρ) (Formalism.WeaklyAdmissibleFiltrations.B1 A.ρ)
    (fun a ha => ha.2) ?_ ?_ ?_
  · exact congrArg Cardinal.toNat h
  · rintro b ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, rfl⟩
    obtain ⟨m, hm, hx⟩ := hT (fun _ => x) continuous_const
    refine ⟨m, hm, m • x, hx Classical.ofNonempty, ?_⟩
    change cob A.ρ (m • x) = m • cob A.ρ x
    exact LinearMap.map_smul_of_tower _ _ _
  · intro y hy
    obtain ⟨m, hm, hy'⟩ := hT y hy.1.1
    have hZ : m • y ∈ latticeCocycles L :=
      ⟨(continuousCocycles A.ρ).smul_of_tower_mem m hy.1, Submodule.mem_pi.2 fun g _ => hy' g⟩
    exact ⟨m, hm, m • y, hZ, ⟨hZ, (finiteCocycles PD A.ρ).smul_of_tower_mem m hy⟩, rfl⟩

theorem latDual_bounded {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) (y : Br.G D.nbr i w hw → (Udual i w hw M hM).V) (hy : Continuous y) :
    ∃ m : Br.OLL D.nbr i w hw, m ≠ 0 ∧ ∀ g, m • y g ∈ (latDual i w hw M hM).T := by
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  obtain ⟨N, hN⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL (D.nbr i w hw).LL
    (m := k) y hy
  refine ⟨(D.nd.l i : Br.OLL D.nbr i w hw) ^ N, ?_, fun g => ?_⟩
  · intro h0
    have := congrArg (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) h0
    rw [map_pow, map_natCast, map_zero] at this
    exact (Fact.out : (D.nd.l i).Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun j => ⟨⟨_, hN g j⟩, ?_⟩
    change _ = ((D.nd.l i : Br.OLL D.nbr i w hw) ^ N) • (y g : Fin k → Br.LL D.nbr i w hw) j
    rw [Algebra.smul_def, map_pow, map_natCast]
    rfl

theorem dualLat_rank : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  intro D hF hBK hPDR i w hw hdeg k M hM K' h hcrys
  refine ⟨Udual i w hw M hM, latDual i w hw M hM, dotProductBilin _ _, isDualLat1_dual D i w hw M hM, ?_⟩
  have hcrys' := isCrys_dual D hF i w hw M hM K' h hcrys
  have hdR : IsDR (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM).ρ :=
    hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h (Udual i w hw M hM) hcrys'
  have hle := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw
    (D.nbr i w hw).LL hdeg (hBK (D.nd.l i) _) (Udual i w hw M hM) hdR
  haveI : IsFractionRing (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) :=
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).1.2.2
  haveI : IsDomain (Br.OLL D.nbr i w hw) := inferInstance
  rw [finrank_H1fT_eq (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM) (latDual i w hw M hM) (latDual_bounded i w hw M hM)]
  refine hle.trans (le_of_eq ?_)
  exact Module.finrank_fin_fun _

end GlobalTheory.Pass.LocDirect

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ThetaFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

def fil0 : Subring P.R.BdR :=
  (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)).range.comap T.eD.toRingHom

theorem mem_deRhamFilZeroSubringPreimage_iff (x : P.R.BdR) : x ∈ fil0 T ↔ x ∈ Fil P 0 := by
  change (∃ z, algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) z = T.eD x) ↔ _
  exact (GlobalTheory.ThetaTie.fil_zero T x).symm

def theta : ↥(fil0 T) →+* ℂ_[l] where
  toFun x := (GlobalTheory.ThetaTie.thetaL T).θ x
  map_one' := (GlobalTheory.ThetaTie.thetaL T).θ_one
  map_mul' x y := (GlobalTheory.ThetaTie.thetaL T).θ_mul _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2) _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 y.2)
  map_zero' := by
    have h0 : (0 : P.R.BdR) ∈ Fil P 0 := (mem_deRhamFilZeroSubringPreimage_iff T 0).1 (zero_mem _)
    have h := (GlobalTheory.ThetaTie.thetaL T).θ_add _ h0 _ h0
    rw [add_zero] at h
    change (GlobalTheory.ThetaTie.thetaL T).θ 0 = 0
    exact left_eq_add.1 h
  map_add' x y := (GlobalTheory.ThetaTie.thetaL T).θ_add _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2) _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 y.2)

theorem theta_apply (x : ↥(fil0 T)) : theta T x = (GlobalTheory.ThetaTie.thetaL T).θ x := rfl

theorem act_mem (g : GQ l) (x : P.R.BdR) (hx : x ∈ fil0 T) : P.actQdR g x ∈ fil0 T := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨Formalism.Per.σDp g a, ?_⟩
  change _ = T.eD (P.actQdR g x)
  rw [T.actD]
  change _ = Formalism.Per.σD g (T.eD x)
  have ha' : algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) a = T.eD x := ha
  rw [← ha']
  exact (GlobalTheory.MemLoc.ActLaws.σD_alg g a).symm

end GlobalTheory.PMon.ThetaFil

namespace GlobalTheory.PMon


open GlobalTheory.PMon.ThetaFil in
theorem exists_theta_deRhamFilZero_surjective_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ Function.Surjective θ ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ y : Om l, ∃ h, θ ⟨algebraMap (Om l) P.R.BdR y, h⟩ = (y : ℂ_[l])) ∧
      ∀ (g : GQ l) (x : ↥S), ∃ h, θ ⟨P.actQdR g x, h⟩ = Formalism.Per.σC g (θ x) := by
  intro l _ P AI T
  refine ⟨fil0 T, theta T, mem_deRhamFilZeroSubringPreimage_iff T, ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨x, hx, e⟩ := (GlobalTheory.ThetaTie.thetaL T).θ_onto c
    exact ⟨⟨x, (mem_deRhamFilZeroSubringPreimage_iff T x).2 hx⟩, e⟩
  · intro x
    exact (GlobalTheory.ThetaTie.thetaL T).θ_ker _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2)
  · intro y
    obtain ⟨z, h1, -⟩ := T.om y
    exact ⟨⟨z, h1.symm⟩, (GlobalTheory.ThetaTie.thetaL T).θ_Om y⟩
  · intro g x
    refine ⟨act_mem T g x x.2, ?_⟩
    rw [theta_apply, theta_apply, (GlobalTheory.ThetaTie.thetaL T).θ_act g _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2)]
    exact GlobalTheory.ThetaTie.actC_eq AI g _

end GlobalTheory.PMon
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.galoisFixedTensorWitt_complete_piAdic_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  first | exact @GlobalTheory.Decompl.fixSub_nearPi_complete | exact GlobalTheory.Decompl.fixSub_nearPi_complete | (intros; apply GlobalTheory.Decompl.fixSub_nearPi_complete <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  first | exact @GlobalTheory.Decompl.near_ioE | exact GlobalTheory.Decompl.near_ioE | (intros; apply GlobalTheory.Decompl.near_ioE <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LevelType
open Matrix

theorem exists_stdVec_of_parVec : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  intro p _ r α _ _ m _ _ e a θ U _ _ ρ v hm hv hpar
  obtain ⟨k0⟩ : Nonempty (m a) := Fintype.card_pos_iff.1 (by omega)
  let σ := Tuple.sort (blk e)
  let i₀ := e ⟨a, k0⟩
  have hi₀ : blk e i₀ = a := blk_apply e a k0
  have hmono := Tuple.monotone_sort (blk e)
  have hlt : ∀ i, blk e i < a → σ.symm i < σ.symm i₀ := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i)) < blk e (σ (σ.symm i₀))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hgt : ∀ i, a < blk e i → σ.symm i₀ < σ.symm i := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i₀)) < blk e (σ (σ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hlo : ∀ i, (σ.symm i).val ≤ (σ.symm i₀).val → blk e i ≤ a := fun i h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hgt i (not_le.1 h'))))
  have hhi : ∀ j, (σ.symm i₀).val ≤ (σ.symm j).val → a ≤ blk e j := fun j h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hlt j (not_le.1 h'))))
  refine ⟨(σ.symm i₀).val, ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm) v, (σ.symm i₀).isLt, ?_, ?_⟩
  · intro h0
    apply hv
    have := congrArg (ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this
  · intro x hx
    set y := (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹ * x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm with hy
    have hyij : ∀ i j, ¬ (blk e i ≤ a ∧ a ≤ blk e j) → y.val i j = if i = j then 1 else 0 := by
      intro i j hij
      have hyv : y.val i j = x.val (σ.symm i) (σ.symm j) := by
        rw [← GlobalTheory.Parabolic.conj_permGL_apply σ.symm y i j, hy]
        congr 2
        group
      rw [hyv, hx _ _ (fun h => hij ⟨hlo i h.1, hhi j h.2⟩)]
      simp
    have hyP : y ∈ parab (ZMod p) e := mem_parab.2 fun i j hji => by
      rw [hyij i j (fun h => absurd (h.1.trans h.2) (not_le.2 hji)), if_neg]
      rintro rfl
      exact lt_irrefl _ hji
    have hlev : ∀ b, b ≠ a → leviProj (ZMod p) e ⟨y, hyP⟩ b = 1 := by
      intro b hb
      refine Units.ext (Matrix.ext fun k l => ?_)
      rw [leviProj_apply, Units.val_one]
      rw [hyij _ _ (fun h => hb (le_antisymm (by simpa using h.1) (by simpa using h.2)))]
      simp [Matrix.one_apply]
    have h1 := hpar ⟨y, hyP⟩ hlev
    change ρ y v = (θ (GeneralLinearGroup.det y) : ℂ) • v at h1
    have hdet : GeneralLinearGroup.det y = GeneralLinearGroup.det x := by
      rw [hy, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    have hxP : x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm = GlobalTheory.Parabolic.permGL (ZMod p) σ.symm * y := by rw [hy]; group
    rw [← Module.End.mul_apply, ← map_mul, hxP, map_mul, Module.End.mul_apply, h1, hdet, map_smul]

end GlobalTheory.LevelType
end
end

section

namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open scoped Formalism.Per

theorem dvd_of_isHausdorff {R : Type} [CommRing R] (p : ℕ) (x a : R)
    (H : IsHausdorff (Ideal.span {(p : R ⧸ Ideal.span {x})}) (R ⧸ Ideal.span {x}))
    (h : ∀ n : ℕ, ∃ c : R, x ∣ a - (p : R) ^ n * c) : x ∣ a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  obtain ⟨c, hc⟩ := h n
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hc
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    hc, map_mul, map_pow, map_natCast]
  exact dvd_mul_right _ _

theorem mem_FilB_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (b : P.R.BdR) (hb : ∀ n : ℕ, b ∈ Lat AI M n) :
    b ∈ FilB P (M : ℤ) := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.deRham_fil_quotient_xi_power_ainf l P AI T (GlobalTheory.ThetaTie.thetaL T) M
  obtain ⟨-, h3⟩ := GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l AI.ε (GlobalTheory.ThetaTie.isEps AI) M
  obtain ⟨a₀, ha₀⟩ := hb 0
  rw [pow_zero, one_mul] at ha₀
  have hd : AI.ξ ^ M ∣ a₀ := by
    refine dvd_of_isHausdorff l _ _ h3.toIsHausdorff fun n => ?_
    obtain ⟨a, ha⟩ := hb n
    refine ⟨a, (h2 _).1 ?_⟩
    have := sub_mem ha ha₀
    rw [← io_apply, map_sub]
    convert this using 1
    ring
  have := add_mem ha₀ ((h2 a₀).2 hd)
  rwa [← io_apply, sub_add_cancel] at this

end GlobalTheory.ExpImage
end

section

namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.MemLoc GlobalTheory.ThetaTie
open scoped Formalism.Per

theorem exists_inv_io_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  intro l _ P AI T
  obtain ⟨-, -, hun, hth, -⟩ := thetaD_props l
  have hθ : _root_.Formalism.Per.θ l AI.π₁ ≠ 0 := by
    have h : _root_.Formalism.Per.θ l AI.π₁ = PreTilt.untilt AI.ε1 - 1 := by
      rw [LocAinf.π₁, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
    rw [h]
    exact sub_ne_zero.2 (isEps AI).2
  have hne : _root_.Formalism.Per.θD l (aDp l AI.π₁) ≠ 0 := by
    rw [hth]
    exact fun h0 => hθ (Subtype.ext h0)
  obtain ⟨v, hv⟩ := (hun _ hne).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (_root_.Formalism.Per.BdRp l) (_root_.Formalism.Per.BdR l) v),
    (fil_zero T _).2 ⟨v, (T.eD.apply_symm_apply _).symm⟩, T.eD.injective ?_⟩
  rw [map_mul, io_apply, eD_ιA, T.eD.apply_symm_apply, ← map_mul, hv, map_one, map_one]

end GlobalTheory.ExpImage
end

section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem norm_le_of_qB_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M n : ℕ) (hM : 1 ≤ M) (z : ℚ_[l]) (hz : qB P z ∈ Lat AI M n) :
    ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  let J : ThetaL P AI := GlobalTheory.ThetaTie.thetaL T
  obtain ⟨a, ha⟩ := hz
  have hq : ∀ c : ℚ_[l], ‖J.θ (qB P c)‖ = ‖c‖ := by
    intro c
    have e : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ c
    rw [e, J.θ_Om]
    exact (PadicComplex.norm_extends _ _).trans (PadicAlgCl.norm_extends _ _)
  have h1 := FilB_anti (P := P) (a := 1) (b := (M : ℤ)) (by exact_mod_cast hM) ha
  have h0 := FilB_anti (P := P) (a := 0) (b := 1) (by norm_num) h1
  have hk := (J.θ_ker _ h0).2 h1
  have hadd := J.θ_add _ h0 _ (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  rw [sub_add_cancel, hk, zero_add] at hadd
  have e2 : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    simp only [map_mul, map_pow, map_natCast]
  rw [e2, J.θ_mul _ (qB_mem _) _ (io_mem AI a)] at hadd
  rw [← hq z, hadd, norm_mul, hq, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end GlobalTheory.ExpImage
end
end
