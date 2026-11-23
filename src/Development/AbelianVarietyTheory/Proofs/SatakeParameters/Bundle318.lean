module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle788
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle295
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle303
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle271
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle282
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle304
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle556
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.GalOfCusp
open TensorProduct Module

noncomputable section

namespace GlobalTheory.SstTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem ineTriv_of_isSst [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V) (hV : IsPst P ρ)
    (hs : IsSst P ρ) : GlobalTheory.PstLaws.IneTriv P ρ := by
  intro g hg
  have hcl := mem_closure_mulV_of_finrank_eq l P K L V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun h => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ h c c (mem_GK.mp h.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx h]) hs
  refine LinearMap.ext fun x => Subtype.ext ?_
  refine AddSubgroup.closure_induction (p := fun y _ => stRep P ρ g y = y) ?_ (map_zero _) ?_ ?_ (hcl x x.2)
  · rintro _ ⟨c, s, hs', rfl⟩
    rw [← Module.End.mul_apply, stRep_mulV P ρ g c c ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ c.2),
      Module.End.mul_apply, (mem_Dst P ρ).mp hs' g]
  · intro y z _ _ hy hz; rw [map_add (f := _), hy, hz]
  · intro y _ hy; rw [map_neg, hy]

end GlobalTheory.SstTwist

namespace GlobalTheory.SstTwist

open GlobalTheory.Pst.TwistLetters GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) {K L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isSst_twist (T : LocTied l P AI) [FiniteDimensional ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V)
    (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    (hs : IsSst P ρs) (hc : Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) ρm) : IsSst P ρt := by
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  have hPs : IsPst P ρs := GlobalTheory.GalCut.IwaAll.isPst_of_isSst P AI T ρs hs
  have hPm : IsPst P ρm := GlobalTheory.PstOfCrys.isPst_of_isCrys T ρm hc
  have hIs := ineTriv_of_isSst P ρs hPs hs
  have hIm := GlobalTheory.PstLaws.ineTriv_of_isCrys P ρm hPm hc
  obtain ⟨y, hy, y', hyy'⟩ := GlobalTheory.Pst.UnitLetter.exists_unit_Dpst P AI ⟨T⟩ ρm χ hm hPm
  let y₀ : ↥(Dpst P ρm) := ⟨y, hy⟩
  have hsurj := GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv P ρs ρt ρm χ hm ht y₀ y' hyy'

  let Φ : DpstUr P ρs →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρt :=
    { toFun := fun x => toUr P ρt (dmul P ρs ρt ρm χ hm ht ((toUr P ρs).symm x) y₀)
      map_add' := fun x x' => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c x => dmul_mulD_left P ρs ρt ρm χ hm ht c _ y₀ }
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have h1 : mulB (L := L) P V y' (mulB (L := L) P V y ((toUr P ρs).symm x : V ⊗[ℚ_[l]] Bst P)) =
        mulB (L := L) P V y' (mulB (L := L) P V y ((toUr P ρs).symm x' : V ⊗[ℚ_[l]] Bst P)) :=
      congrArg (fun z : ↥(Dpst P ρt) => mulB (L := L) P V y' (z : V ⊗[ℚ_[l]] Bst P)) hxx
    rw [mulB_assoc, mulB_assoc, hyy', one_mulB, one_mulB] at h1
    exact (toUr P ρs).symm.injective (Subtype.ext h1)
  have hsur : Function.Surjective Φ := by
    intro z
    obtain ⟨x, hx⟩ := hsurj ((toUr P ρt).symm z)
    exact ⟨toUr P ρs x, by
      change toUr P ρt (dmul P ρs ρt ρm χ hm ht ((toUr P ρs).symm (toUr P ρs x)) y₀) = z
      rw [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]⟩
  have hPt : IsPst P ρt := by
    rw [IsPst, ← (LinearEquiv.ofBijective Φ ⟨hinj, hsur⟩).rank_eq]
    exact hPs
  refine GlobalTheory.PstLaws.isSst_of_ineTriv P ρt hPt fun g hg => LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := hsurj z
  rw [actD_dmul, LinearMap.congr_fun (hIs g hg) x, LinearMap.congr_fun (hIm g hg) y₀]
  rfl

end GlobalTheory.SstTwist

open GlobalTheory.Pst.TwistLetters

theorem GlobalTheory.SstTwist.isSstAt_twist : GlobalTheory.Published.DeRhamPotSemistable → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), (Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → (Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) → IsSstAt P Bw r → IsCrysAt P Bw c → IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) := by
  intro _ l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hr hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₁, r₁, hm₁, hs₁⟩ := hr
  obtain ⟨L₂, c₂, hm₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  set L := supExt L₁ L₂
  set s := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁
  set m := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂
  refine ⟨L, _, GlobalTheory.TwistParamAbove.isModel_twist (hm₁.enlarge l₁) (hm₂.enlarge l₂), ?_⟩
  have hsL : IsSst P (Bw.repE L s) := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hs₁
  have hcL : Bw.IsCrysE P L m := (GlobalTheory.Pst.local_ext P Bw l₂ c₂).1.2 hc₂
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v =
      χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  exact GlobalTheory.SstTwist.isSst_twist P AI T (Bw.repE L s) _ (Bw.repE L m) χ hχm hχt hsL hcL
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

namespace GlobalTheory.CRTFrame

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) (M : 𝓞 E) (hM : M ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P ((algebraMap (𝓞 E) E M)⁻¹ * algebraMap (𝓞 E) E z) := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {M} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hM
  have hex : ∃ m : ℕ, ¬ I ≤ P.asIdeal ^ m := by
    by_contra h
    push Not at h
    apply hI
    have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
    have := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal hP
    rw [eq_bot_iff, ← this]
    exact le_iInf h
  set m0 := Nat.find hex with hm0
  have hm0pos : m0 ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm0, h0, pow_zero] at this
    exact this (by rw [Ideal.one_eq_top]; exact le_top)
  refine ⟨m0 - 1, ?_⟩
  have hle : I ≤ P.asIdeal ^ (m0 - 1) := by
    have := Nat.find_min hex (show m0 - 1 < m0 by omega)
    push Not at this
    exact this
  have hnle : ¬ I ≤ P.asIdeal ^ (m0 - 1 + 1) := by
    rw [show m0 - 1 + 1 = m0 by omega]; exact Nat.find_spec hex
  obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.mpr hle
  have hQP : ¬ Q ≤ P.asIdeal := by
    intro h
    apply hnle
    rw [hQ, pow_succ]
    exact Ideal.mul_mono_right h
  obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.mp hQP
  intro z hz
  have hmem : z * s ∈ I := by
    rw [hQ]; exact Ideal.mul_mem_mul hz hsQ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  have hM' : algebraMap (𝓞 E) E M ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hM
  refine ⟨a, s, hsP, ?_⟩
  have h2 : algebraMap (𝓞 E) E a * algebraMap (𝓞 E) E M = algebraMap (𝓞 E) E z * algebraMap (𝓞 E) E s := by
    rw [← map_mul, ← map_mul, ha]
  field_simp
  linear_combination -h2

theorem approx_frames (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E)))
    (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ) :
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  classical
  set w : SB → Sp E n := fun P => f P (y0 P) with hwdef
  set c : SB → Fin n → Fin n → E := fun P j l => (f P).symm (Pi.single j 1) l with hcdef
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    ((Finset.univ.image (fun x : SB × Fin n × Fin n => c x.1 x.2.1 x.2.2)) ∪
      (Finset.univ.image (fun x : SB × Fin n => w x.1 x.2)))
  set D : 𝓞 E := (b : 𝓞 E) with hDdef
  have hD : D ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hc : ∀ P j l, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * c P j l := by
    intro P j l
    obtain ⟨r, hr⟩ := hb (c P j l) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(P, j, l), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  have hw : ∀ P j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = algebraMap (𝓞 E) E D * w P j := by
    intro P j
    obtain ⟨r, hr⟩ := hb (w P j) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(P, j), Finset.mem_univ _, rfl⟩))
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose cr hcr using hc
  choose wr hwr using hw
  have hN : ∀ P : SB, ((qOf P.1 : ℕ) : 𝓞 E) ≠ 0 := by
    intro P
    rw [Ne, Nat.cast_eq_zero]
    show Ideal.absNorm P.1.asIdeal ≠ 0
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  set M : SB → 𝓞 E := fun P => ((qOf P.1 : ℕ) : 𝓞 E) ^ (e P) * D * D with hMdef
  have hM : ∀ P, M P ≠ 0 := fun P => mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hN P)) hD) hD
  choose k hk using fun P : SB => exists_pow_intAt_div P.1 (M P) (hM P)
  set kk : HeightOneSpectrum (𝓞 E) → ℕ := fun P => if h : P ∈ SB then k ⟨P, h⟩ else 0 with hkkdef
  have crt : ∀ j : Fin n, ∃ z : 𝓞 E, ∀ (P : HeightOneSpectrum (𝓞 E)) (hP : P ∈ SB),
      z - wr ⟨P, hP⟩ j ∈ P.asIdeal ^ kk P := fun j =>
    IsDedekindDomain.exists_forall_sub_mem_ideal (fun P : HeightOneSpectrum (𝓞 E) => P.asIdeal) kk
      (fun i _ => i.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun P => wr P j)
  choose z hz using crt
  have hD' : algebraMap (𝓞 E) E D ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hD
  refine ⟨fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j), ?_⟩
  intro P l
  have hexp : ∀ v : Sp E n, (f P).symm v l = ∑ j, v j * c P j l := by
    intro v
    have hv : v = ∑ j, v j • (Pi.single j 1 : Sp E n) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]

    simp [map_sum, map_smul, Finset.sum_apply, c]
  have hmem : (∑ j, (z j - wr P j) * cr P j l) ∈ P.1.asIdeal ^ k P := by
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ ?_
    have := hz j P.1 P.2
    simpa [kk, P.2] using this
  have key := hk P _ hmem
  convert key using 1
  have h1 : (f P).symm (fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - y0 P
      = (f P).symm ((fun j => (algebraMap (𝓞 E) E D)⁻¹ * algebraMap (𝓞 E) E (z j)) - w P) := by
    rw [map_sub]; simp [w]

  rw [h1, hexp, Finset.mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 := hcr P j l
  have e2 := hwr P j
  simp only [M, map_mul, map_sub, map_pow, map_natCast, Pi.sub_apply]
  rw [e1, e2]
  have hq : ((qOf P.1 : ℕ) : E) ≠ 0 := by
    have := hN P
    intro h; apply this
    exact (IsFractionRing.injective (𝓞 E) E) (by rw [map_natCast, h, map_zero])
  field_simp

theorem approx_frames_target : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) :=
  fun E _ _ n SB f y0 e => approx_frames E n SB f y0 e

end GlobalTheory.CRTFrame
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

noncomputable section

namespace GlobalTheory.SatExists

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : TrivOutside {v} (1 : GAf L n) := by
  intro v' _
  show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v') = 1
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem trivOutside_mul {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {v} y) : TrivOutside {v} (x * y) := by
  intro v' hv'
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1
  rw [Units.val_mul, Matrix.map_mul, hx v' hv', hy v' hv', Matrix.one_mul]

theorem trivOutside_inv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n}
    (hx : TrivOutside {v} x) : TrivOutside {v} x⁻¹ := by
  intro v' hv'
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v') = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v' hv', Matrix.mul_one] at e

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  intro L _ _ _ n π v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hNf⟩ := π.irrS.1.le hf₀S
  let U : Subgroup (GAf L n) :=
    Subgroup.closure ({κ | NG.Cong L n N κ} ∪ {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ})
  have hUmax : U ≤ Umax L n := (Subgroup.closure_le _).2 (by
    rintro κ (hκ | hκ)
    · exact hκ.1
    · exact hκ.1)
  have hUv : ∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n) := fun κ hκ =>
    ⟨fun h => hUmax h, fun h => Subgroup.subset_closure (Or.inr ⟨h, hκ⟩)⟩
  have hCU : ∀ κ, NG.Cong L n N κ → κ ∈ U := fun κ hκ => Subgroup.subset_closure (Or.inl hκ)
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := by
    intro κ hκ
    induction hκ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact funext fun g => hNf x hx g
      · exact hf₀K x hx.1 hx.2
    | one => exact funext fun g => by change f₀ (g * 1) = f₀ g; rw [mul_one]
    | mul x y _ _ hx hy =>
      refine funext fun g => ?_
      change f₀ (g * (x * y)) = f₀ g
      have h1 : f₀ (g * x * y) = f₀ (g * x) := congrFun hy (g * x)
      have h2 : f₀ (g * x) = f₀ g := congrFun hx g
      rw [← mul_assoc, h1, h2]
    | inv x _ hx =>
      refine funext fun g => ?_
      change f₀ (g * x⁻¹) = f₀ g
      have h1 : f₀ (g * x⁻¹ * x) = f₀ (g * x⁻¹) := congrFun hx (g * x⁻¹)
      rw [← h1, inv_mul_cancel_right]
  have hdec : ∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨a, b, e, ha, hat, hb, hc⟩ := GlobalTheory.T.congruence_element_decompose L n v N x hx
        exact ⟨a, b, e, (hUv a hat).2 ha, hat, hCU b hb, hc⟩
      · exact ⟨x, 1, (mul_one x).symm, Subgroup.subset_closure (Or.inr hx), hx.2, one_mem _,
          fun y _ => by rw [mul_one, one_mul]⟩
    | one => exact ⟨1, 1, (mul_one 1).symm, one_mem _, trivOutside_one v, one_mem _,
        fun y _ => by rw [mul_one, one_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      obtain ⟨a', b', rfl, ha', hat', hb', hbc'⟩ := hy
      refine ⟨a * a', b * b', ?_, mul_mem ha ha', trivOutside_mul hat hat', mul_mem hb hb', fun z hz => ?_⟩
      · simp only [mul_assoc]
        rw [← mul_assoc b a', ← hbc a' hat', mul_assoc]
      · rw [← mul_assoc, hbc z hz, mul_assoc, hbc' z hz, ← mul_assoc]
    | inv x _ hx =>
      obtain ⟨a, b, rfl, ha, hat, hb, hbc⟩ := hx
      refine ⟨a⁻¹, b⁻¹, ?_, inv_mem ha, trivOutside_inv hat, inv_mem hb, fun z hz => ?_⟩
      · rw [mul_inv_rev, eq_mul_inv_iff_mul_eq, mul_assoc, hbc a⁻¹ (trivOutside_inv hat), inv_mul_cancel_left]
      · rw [mul_inv_eq_iff_eq_mul, mul_assoc, hbc z hz, inv_mul_cancel_left]
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      add_mem' := fun ha hb => ⟨π.S.add_mem ha.1 hb.1, fun κ hκ => by rw [map_add (f := _), ha.2 κ hκ, hb.2 κ hκ]⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI : FiniteDimensional ℂ V := by
    have := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) ?_
    rintro f ⟨hfS, hfU⟩
    exact ⟨(π.irrS.1.le hfS).1, fun κ hκ g => congrFun (hfU κ (hCU κ hκ)) g⟩
  have hf₀V : f₀ ∈ V := ⟨hf₀S, hf₀U⟩
  haveI : Nontrivial V := ⟨⟨⟨f₀, hf₀V⟩, 0, fun e => hf₀0 (congrArg Subtype.val e)⟩⟩
  let T : Hecke ℂ (KU Dv.σw n) → Module.End ℂ V := fun h =>
    { toFun := fun f => ⟨heckeFunI L n U Dv h.1 f.1,
        GlobalTheory.T.inertHeckeOperator_preserves_rightTranslationStable L n v w Dv U hUv π.W π.S π.irrS.1.stable h.1 h.2 f.1 f.2.1,
        GlobalTheory.T.inertHeckeOperator_preserves_levelInvariants L n v w Dv U hUv hdec π.W h.1 h.2 f.1 f.2.2⟩
      map_add' := fun f f' => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 1 f.1 f'.1).2.2.1)
      map_smul' := fun c f => Subtype.ext ((GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.2.2) }
  have hT : ∀ h (f : V), ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h.1 f.1 := fun _ _ => rfl
  have hcomm : ∀ a b, T a * T b = T b * T a := fun a b => LinearMap.ext fun f => Subtype.ext (by
    change heckeFunI L n U Dv a.1 (heckeFunI L n U Dv b.1 f.1) = heckeFunI L n U Dv b.1 (heckeFunI L n U Dv a.1 f.1)
    rw [← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W a.1 a.2 b.1 b.2 f.1 f.2.2,
      ← GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W b.1 b.2 a.1 a.2 f.1 f.2.2,
      GlobalTheory.UnitarySwap.heckeCommU _ Dv.ϖ Dv.σw _ n ℂ Dv.unram a.1 a.2 b.1 b.2])
  obtain ⟨f, hf0, hμ⟩ := GlobalTheory.exists_common_eigenvector_of_commute T hcomm
  choose μ hμ using hμ
  have ev : ∀ h : Hecke ℂ (KU Dv.σw n), heckeFunI L n U Dv h.1 f.1 = μ h • f.1 := fun h =>
    congrArg Subtype.val (hμ h)
  have hf'0 : (f : GAf L n → π.W) ≠ 0 := fun e => hf0 (Subtype.ext e)
  have inj := smul_left_injective ℂ hf'0
  let l : Hecke ℂ (KU Dv.σw n) →ₗ[ℂ] ℂ :=
    { toFun := μ
      map_add' := fun h h' => inj (by
        change μ (h + h') • f.1 = (μ h + μ h') • f.1
        rw [← ev, add_smul, ← ev, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 1 f.1 f.1).1)
      map_smul' := fun c h => inj (by
        change μ (c • h) • f.1 = (c * μ h) • f.1
        rw [← ev, mul_smul, ← ev]
        exact (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 c f.1 f.1).2.1) }
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq Dv.unram l
    (inj (by
      change μ _ • f.1 = (1 : ℂ) • f.1
      rw [← ev, one_smul]
      exact GlobalTheory.T.inertHeckeOperator_sphericalUnit_eq_id L n v w Dv U hUv π.W f.1 f.2.2))
    (fun h h' => inj (by
      change μ _ • f.1 = (μ h * μ h') • f.1
      rw [← ev]
      change heckeFunI L n U Dv (conv (KU Dv.σw n) h.1 h'.1) f.1 = _
      rw [GlobalTheory.T.inertHeckeOperator_comp_spherical_convolution L n v w Dv U hUv π.W h.1 h.2 h'.1 h'.2 f.1 f.2.2, ev h',
        (GlobalTheory.T.inertHeckeOperator_bilinear L n v w Dv U hUv π.W h.1 h.2 h.1 h.2 (μ h') f.1 f.1).2.2.2, ev h, smul_smul, mul_comm]))
  refine ⟨fun i => (α i : ℂ), f.1, f.2.1, hf'0, U, f.2.2, hUv, fun h hh => ?_⟩
  rw [ev ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.SatExists
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem adm_seam_lat_rd_pair : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ i j c c'
  rw [← t.O_lat, ← t.O_lat]
  exact ⟨Formalism.L2.Ker.even_rankN _ _, Formalism.L2.Ker.even_rankN _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat j c').2⟩

end GlobalTheory.TwV
end
