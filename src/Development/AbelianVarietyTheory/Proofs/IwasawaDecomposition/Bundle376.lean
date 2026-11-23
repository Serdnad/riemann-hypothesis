module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGLocIdGChiTied
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Formalism.LocalToGlobal.Columns.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle352
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCBase
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.TwistRamLoc

def Disc (M : Type) : Type := M

instance (M : Type) [CommGroup M] : CommGroup (Disc M) := ‹CommGroup M›
instance (M : Type) : TopologicalSpace (Disc M) := ⊥
instance (M : Type) : DiscreteTopology (Disc M) := ⟨rfl⟩
instance (M : Type) [CommGroup M] : IsTopologicalGroup (Disc M) := inferInstance

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

end GlobalTheory.TwistRamLoc

namespace GlobalTheory.TwistRamLoc

theorem twist_ram_and_trivial_at_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  intro D cf C tp w hGAR _ hTied hTw hVal hAdm
  classical
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex (D.what₂.places.resChar w)
  have hP : IsPsi (D.what₂.places.resChar w) (C.Q w) (tp.psi w) := tp.psi_is w hTw
  obtain ⟨a, hord⟩ := hP.ord
  have hm : 0 < D.what₂.places.resChar w ^ a := pow_pos (D.what₂.places.resChar_prime w).pos a
  obtain ⟨r, hr, hL⟩ :=
    GlobalTheory.HeckeGal.IsGlobalArtin.exists_isLAdicOf ha ι (GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd hm hord)
  set Ψ := (C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)) with hΨ
  let φ : D.ntw.Ok (C.twI w) (C.k' w) →+* FractionRing (C.Oe w) :=
    (algebraMap (C.Oe w) (FractionRing (C.Oe w))).comp (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w))
  have hφ : Function.Injective φ :=
    (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))).comp (C.Oe_inj w)
  let Γ : Subgroup ((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) :=
    { carrier := {p | ∃ y : D.what₂.LL, ((p.1 : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) =
          ι.symm (D.what₂.embLL y) ∧ φ (p.2 : D.ntw.Ok (C.twI w) (C.k' w)) = C.embW w y}
      mul_mem' := by
        rintro p q ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
        exact ⟨y * y', by simp [h1, h1'], by simp [h2, h2']⟩
      one_mem' := ⟨1, by simp, by simp⟩
      inv_mem' := by
        rintro p ⟨y, h1, h2⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · rw [Prod.fst_inv, Units.val_inv_eq_inv_val, h1, map_inv₀, map_inv₀]
        · rw [Prod.snd_inv, map_units_inv φ, h2, map_inv₀] }
  let Φ : G D.host.E D.nd.Om →* Disc (((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) ⧸ Γ) :=
    (QuotientGroup.mk' Γ).comp (r.prod Ψ)
  have hrm : ∀ g, r g ^ (D.what₂.places.resChar w ^ a) = 1 := fun g => by
    have := DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hord) g
    rwa [MonoidHom.pow_apply] at this
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hr hm hrm
  have hΨo : IsOpen (Ψ.ker : Set (G D.host.E D.nd.Om)) := hAdm.2.2.1
  have hΦc : Continuous Φ := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' Φ (Subgroup.isOpen_mono (H₁ := r.ker ⊓ Ψ.ker) ?_ ?_)
    · intro g hg
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' Γ (r g, Ψ g) = 1
      rw [hg.1, hg.2]
      exact map_one _
    · rw [Subgroup.coe_inf]
      exact hro.inter hΨo
  let S : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
    C.Q w ∪ (finite_placesOver D.host.E (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w).ne_zero).toFinset
  have hΦ1 : Φ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha _ Φ hΦc S fun v hv A hA σ hσ => ?_
    have hvQ : v ∉ C.Q w := fun h => hv (Finset.mem_union_left _ h)
    have hvl : v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun h =>
      hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hu : (tp.psi w).UnrAt v := (hP.ram v).2 hvQ
    obtain ⟨y0, hy0⟩ := hVal v hu
    have hy0' : D.what₂.embLL y0 = (((tp.psi w).val v : ℂˣ) : ℂ) := by simpa [HChar.valTw] using hy0
    have hy : D.what₂.embLL y0⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by
      rw [map_inv₀, hy0', Units.val_inv_eq_inv_val]
    have h2 := hTied w hTw v hvQ hvl A σ hA hσ y0⁻¹ hy
    have h1 := hL.frob_unr ha (Or.inr rfl) hu hA hσ
    show QuotientGroup.mk' Γ (r σ, Ψ σ) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨y0⁻¹, ?_, h2.symm⟩
    show ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _
    rw [h1, map_inv₀, hy0', map_inv₀]
  have hmem : ∀ σ, (r σ, Ψ σ) ∈ Γ := fun σ => by
    have := DFunLike.congr_fun hΦ1 σ
    exact (QuotientGroup.eq_one_iff _).1 this
  have key : ∀ σ, r σ = 1 ↔ Ψ σ = 1 := fun σ => by
    obtain ⟨y, h1, h2⟩ := hmem σ
    constructor
    · intro h
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective,
        map_eq_one_iff _ D.what₂.embLL.injective] at h1
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h1, map_one, ← map_one φ] at h2
      exact Units.ext (hφ h2)
    · intro h
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h, Units.val_one, map_one, eq_comm, map_eq_one_iff _ (C.embW w).injective] at h2
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h2, map_one, map_one] at h1
      exact Units.ext h1
  refine ⟨fun v hv A hA => ?_, fun v hv A hA σ hσ => ?_⟩
  · have hnu : ¬ (tp.psi w).UnrAt v := fun h => (hP.ram v).1 h hv
    rw [← hL.unr_iff ha (Or.inr rfl) hA] at hnu
    push_neg at hnu
    obtain ⟨σ, hσ, hne⟩ := hnu
    exact ⟨σ, hσ, fun h => hne ((key σ).2 h)⟩
  · have hloc : (tp.psi w).loc v = 1 := MonoidHom.ext (hP.atl v hv)
    exact (key σ).1 (((hL.dec_triv ha hr (Or.inr rfl) hA).2 hloc) σ hσ)

end GlobalTheory.TwistRamLoc
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
open scoped Pointwise

namespace GlobalTheory.TypePrimeSplit

theorem exists_intCast_of_card {K : Type} [CommRing K] {p : ℕ} (hp : p.Prime) (h : Nat.card K = p) (x : K) :
    ∃ n : ℤ, x = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 (h ▸ hp.one_lt)
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := K) h (g := 1) (g' := x) one_ne_zero
  exact ⟨n, by simpa using hn.symm⟩

theorem isSplitPl_of_card {R : Ranks} (H : Host R) (v : PlE H) {p : ℕ} (hp : p.Prime)
    (h : Nat.card (𝓞 H.E ⧸ v.asIdeal) = p) : IsSplitPl H v := by
  by_contra hn
  have key : ∀ x ∈ v.asIdeal, (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x ∈ v.asIdeal := by
    intro x hx
    by_contra hy'
    refine hn ⟨x, hx, fun z hz => ?_⟩
    have : z = (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x := RingOfIntegers.ext hz
    rwa [this]
  apply H.der.unramEF v.asIdeal v.isPrime v.ne_bot
  intro x
  show (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x ∈ v.asIdeal
  obtain ⟨n, hx⟩ := exists_intCast_of_card hp h (Ideal.Quotient.mk v.asIdeal x)
  have ha : x - n ∈ v.asIdeal := Ideal.Quotient.eq.1 (by rw [hx, map_intCast])
  have h3 := key _ ha
  have hf : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • (n : 𝓞 H.E) = n :=
    map_intCast (MulSemiringAction.toRingHom _ (𝓞 H.E) (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H)) n
  rw [smul_sub, hf] at h3
  have h4 : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x = ((PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - n) - (x - n) := by ring
  rw [h4]
  exact sub_mem h3 ha

theorem typePrime_split :
    ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v :=
  fun D k v hv => isSplitPl_of_card D.host v (D.host.g_prime k)
    (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hv)

end GlobalTheory.TypePrimeSplit
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem conjO_piG_ne (hPr : Pr.Ok) (a : Fin 2) : X.conjO (Pr.piG a) ≠ 0 := by
  intro h0
  have := hPr.piG_norm a
  rw [h0, mul_zero] at this
  exact (Nat.cast_ne_zero.2 (hPr.g_prime a).ne_zero) this.symm

theorem mem_vG_iff (hPr : Pr.Ok) (a : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Pr.vG a ↔ X.conjO (Pr.piG a) ∈ P.asIdeal := mem_divs (conjO_piG_ne hPr a) P

theorem g_mem_of_isOver {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)}
    (hv : IsOver v P) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ((Pr.g a : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [hv, Ideal.mem_comap, map_natCast] at h
  exact h

theorem eq_of_isOver (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) {P Q : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) (hQ : Q ∈ Pr.vGs)
    (hPv : IsOver v P) (hQv : IsOver v Q) : Q = P := by
  rcases rll_over_cases hc hPv hQv with e | e
  · exact e
  exfalso
  have hPa := mem_vG_of_g_mem hPr hP (g_mem_of_isOver hPv h)
  have hQa := mem_vG_of_g_mem hPr hQ (g_mem_of_isOver hQv h)
  rw [mem_vG_iff hPr] at hPa hQa
  rw [e, mem_conjP] at hQa
  have h2 : cO X.E (X.conjO (Pr.piG a)) = Pr.piG a := RingOfIntegers.ext (star_star _)
  rw [h2] at hQa
  obtain ⟨x, y, hxy⟩ := hPr.piG_cop a
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ hQa) (Ideal.mul_mem_left _ _ hPa)

theorem exists_over_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ∃ w : {w // w ∈ Pr.vGs}, IsOver v w.1 := by
  have h01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  have hv : v ∈ plUnder X.F Pr.vGs := by
    rw [plUnder_vGs hc hPr v]
    rcases h01 a with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨P, hP, hPv⟩ := hv
  exact ⟨⟨P, hP⟩, hPv⟩

theorem isOver_of_under {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : P.under (𝓞 X.F) = v) :
    IsOver v P := by
  subst h
  rfl

theorem under_of_isOver {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : IsOver v P) :
    P.under (𝓞 X.F) = v :=
  HeightOneSpectrum.ext h.symm

end GlobalTheory.Mem.TypePrimes

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem residue_natCast (hPr : Pr.Ok) {a : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG a)
    (c : 𝓞 X.E ⧸ w.asIdeal) : ∃ k : ℕ, c = k := by
  haveI : NeZero (Pr.g a) := ⟨(hPr.g_prime a).ne_zero⟩
  have e := (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime a) (by
    rw [← hPr.vG_norm a w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  exact ⟨(e.symm c).val, by rw [← map_natCast e, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]⟩

theorem vG_disjoint (hPr : Pr.Ok) : Disjoint (Pr.vG 0) (Pr.vG 1) := by
  rw [Finset.disjoint_left]
  intro w h0 h1
  have hc : IsCoprime ((Pr.g 0 : ℕ) : 𝓞 X.E) ((Pr.g 1 : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime 0) (hPr.g_prime 1)).2 hPr.g_ne)
  obtain ⟨x, y, hxy⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h0)) (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h1))

theorem primes_over_places : ∀ (X : Fields) (Pr : Primes X) (hc : Formalism.BasicNotions.CMData X.F X.E), Pr.Ok →
    ∃ wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs},
      (∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h) ∧
      (∀ a v h, (∀ P : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = v → X.conjO (Pr.piG a) ∈ P.asIdeal →
          P = (wOf a v h).1) ∧ (wOf a v h).1.under (𝓞 X.F) = v ∧
        ∀ c : 𝓞 X.E ⧸ (wOf a v h).1.asIdeal, ∃ k : ℕ, c = k) ∧
      ∀ φ : {w // w ∈ Pr.vGs} → ℂ, ∏ w, φ w =
        ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) := by
  intro X Pr hc hPr
  classical
  let wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs} :=
    fun a v h => (exists_over_vGs hc hPr h).choose
  have hspec : ∀ a v h, IsOver v (wOf a v h).1 := fun a v h => (exists_over_vGs hc hPr h).choose_spec
  have h1 : ∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h := by
    intro a v h w
    constructor
    · intro hw
      exact Subtype.ext (eq_of_isOver hc hPr h (wOf a v h).2 w.2 (hspec a v h) hw)
    · rintro rfl
      exact hspec a v h
  have hin : ∀ a v h, (wOf a v h).1 ∈ Pr.vG a := fun a v h =>
    mem_vG_of_g_mem hPr (wOf a v h).2 (g_mem_of_isOver (hspec a v h) h)
  refine ⟨wOf, h1, fun a v h => ⟨?_, under_of_isOver (hspec a v h), residue_natCast hPr (hin a v h)⟩, ?_⟩
  · intro P hPu hP
    have hPa : P ∈ Pr.vG a := (mem_vG_iff hPr a P).2 hP
    exact eq_of_isOver hc hPr h (wOf a v h).2 (mem_vGs hPa) (hspec a v h) (isOver_of_under hPu)
  · intro φ
    let φ' : HeightOneSpectrum (𝓞 X.E) → ℂ := fun w => if hw : w ∈ Pr.vGs then φ ⟨w, hw⟩ else 1
    have hL : ∏ w, φ w = ∏ w ∈ Pr.vGs, φ' w := by
      rw [← Finset.prod_coe_sort Pr.vGs φ']
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [φ', dif_pos w.2]
    have hA : ∀ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) =
        ∏ w ∈ Pr.vG a, φ' w := by
      intro a
      let f : HeightOneSpectrum (𝓞 X.F) → ℂ := fun v => if h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal then φ (wOf a v h) else 1
      have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h)) = ∏ᶠ v, f v := by
        refine finprod_congr fun v => ?_
        exact finprod_eq_dif _
      have hsupp : Function.mulSupport f ⊆ ((Pr.vG a).image fun w => w.under (𝓞 X.F) : Finset _) := by
        intro v hv
        have h' : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal := by
          by_contra hn
          exact hv (by simp only [f, dif_neg hn])
        rw [Finset.coe_image]
        exact ⟨(wOf a v h').1, hin a v h', under_of_isOver (hspec a v h')⟩
      rw [e1, finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_image]
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        have hw' : w ∈ Pr.vGs := mem_vGs hw
        have e2 : wOf a (w.under (𝓞 X.F)) hg = ⟨w, hw'⟩ :=
          ((h1 a _ hg ⟨w, hw'⟩).1 (isOver_of_under rfl)).symm
        simp only [f, φ', dif_pos hg, dif_pos hw', e2]
      · intro w hw w' hw' he
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        exact (eq_of_isOver hc hPr hg (mem_vGs hw) (mem_vGs hw') (isOver_of_under rfl) (isOver_of_under he.symm)).symm
    rw [hL, Fin.prod_univ_two, hA 0, hA 1]
    unfold Primes.vGs
    exact Finset.prod_union (vG_disjoint hPr)

end GlobalTheory.Mem.TypePrimes
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.moveDown_point_preserves_index_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F)), IsOver v P.1 → conjPrime₂ P.1 ≠ P.1 → IsOver v (conjPrime₂ P.1) → (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧ Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  first | exact @GlobalTheory.Mem.Col2.PtY.mv_dn_facts | exact GlobalTheory.Mem.Col2.PtY.mv_dn_facts | (intros; apply GlobalTheory.Mem.Col2.PtY.mv_dn_facts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVector_maximalCompact_basis_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  first | exact @GlobalTheory.FockSubst.pureTensorO_subst | exact GlobalTheory.FockSubst.pureTensorO_subst | (intros; apply GlobalTheory.FockSubst.pureTensorO_subst <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem

theorem rieszProd_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hI v v' a a' ha ha'
  classical
  have hp : GlobalTheory.DefLift.AllPlus R.MX := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hbij := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => by haveI := (m τ).1; infer_instance
  let b := fun τ => stdOrthonormalBasis ℂ (R.MX.sm τ)
  let c : R.MX.Vec → (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))) → ℂ := fun u f => ∏ τ, ⟪(b τ (f τ)), u τ⟫_ℂ
  have hexp : ∀ u : R.MX.Vec, PiTensorProduct.tprod ℂ u =
      ∑ f, c u f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := by
    intro u
    conv_lhs => rw [show u = fun τ => ∑ i, ⟪b τ i, u τ⟫_ℂ • b τ i from funext fun τ => ((b τ).sum_repr' (u τ)).symm]

    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    exact MultilinearMap.map_smul_univ _ (fun τ => ⟪b τ (f τ), u τ⟫_ℂ) (fun τ => b τ (f τ))
  let B := Basis.piTensorProduct (fun τ => (b τ).toBasis)
  have hB' : ∀ f, B f = PiTensorProduct.tprod ℂ (fun τ => b τ (f τ)) := fun f => by
    simp [B, Basis.piTensorProduct_apply]

  have hw : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∃ w, ∀ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX w (PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = if f = g then 1 else 0 := by
    intro g
    obtain ⟨w, hw⟩ := hbij.2 (B.coord g)
    refine ⟨w, fun f => ?_⟩
    rw [hw, ← hB', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hcoef : ∀ g : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), R.prX a (PiTensorProduct.tprod ℂ (fun τ => b τ (g τ))) = starRingEnd ℂ (c v g) := by
    intro g
    haveI : Nonempty (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))) := ⟨g⟩
    obtain ⟨w, hw⟩ := hw g
    have h1 := hI (fun τ => Fin (Module.finrank ℂ (R.MX.sm τ))) b w a
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [hw f, if_neg hf]; simp) (by simp), hw g, if_pos rfl,
      map_one, one_mul] at h1

    rw [← h1, ← inner_conj_symm, ← ha w, hexp v, map_sum]
    rw [Finset.sum_eq_single g (fun f _ hf => by rw [map_smul, hw f, if_neg hf]; simp) (by simp)]
    rw [map_smul, hw g, if_pos rfl, smul_eq_mul, mul_one]
  have h2 := ha' a

  rw [← h2, hexp v', map_sum]
  have hr : ∀ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ i, ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ := fun τ =>
    (Submodule.coe_inner (R.MX.sm τ) (v τ) (v' τ)).symm.trans ((b τ).sum_inner_mul_inner (v τ) (v' τ)).symm
  have hprod : ∏ τ, ⟪((v τ : R.MX.sm τ) : R.MX.H τ), ((v' τ : R.MX.sm τ) : R.MX.H τ)⟫_ℂ =
      ∑ f : (∀ τ, Fin (Module.finrank ℂ (R.MX.sm τ))), ∏ τ, (⟪v τ, b τ (f τ)⟫_ℂ * ⟪b τ (f τ), v' τ⟫_ℂ) := by
    exact (Finset.prod_congr rfl fun τ _ => hr τ).trans
      (Fintype.prod_sum (fun τ (i : Fin (Module.finrank ℂ (R.MX.sm τ))) => ⟪v τ, b τ i⟫_ℂ * ⟪b τ i, v' τ⟫_ℂ))
  refine Eq.trans ?_ hprod.symm
  refine Finset.sum_congr rfl fun f _ => ?_
  have e1 : R.prX a (c v' f • PiTensorProduct.tprod ℂ (fun τ => b τ (f τ))) = c v' f * starRingEnd ℂ (c v f) :=
    ((R.prX a).map_smul _ _).trans ((congrArg (c v' f • ·) (hcoef f)).trans (smul_eq_mul _ _))
  refine e1.trans ?_
  have e2 : starRingEnd ℂ (c v f) = ∏ τ, ⟪v τ, b τ (f τ)⟫_ℂ :=
    (map_prod (starRingEnd ℂ) _ _).trans (Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _)
  refine (congrArg (c v' f * ·) e2).trans ?_
  refine (Finset.prod_mul_distrib).symm.trans ?_
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.Mem
end
