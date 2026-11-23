module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle304
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle307
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle044
import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle138
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle308
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupExistsOfInterlaced
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle224
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.PeriodIntegrals.Bundle020
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009

@[expose] public section

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.CyclicDisc

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this

omit [IsScalarTower (𝓞 K) K V] in
theorem pd_of_ortho (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, he⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (by simp [hn])
  have e1 : h (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, star (c i) * c i := by

    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, he,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
    simp [mul_comm]

  rw [e1, map_sum, Complex.re_sum]
  have e2 : ∀ i, (τ (star (c i) * c i)).re = Complex.normSq (τ (c i)) := fun i => by
    rw [map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  simp only [e2]
  obtain ⟨i, hi⟩ := hc
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)⟩

omit [NumberField K] in
theorem star_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (starRingEnd K (algebraMap (𝓞 K) K r)) :=
    map_isIntegral_int _ (RingOfIntegers.isIntegral_coe r)
  exact ⟨⟨_, this⟩, rfl⟩

def Over (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V) : Prop :=
  Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
    Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))

omit [NumberField K] in
theorem over_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L M : Submodule (𝓞 K) V)
    (H : Over h 𝔓 L M) : Over h 𝔓 (g • L) (g • M) := by
  obtain ⟨h1, h2, h3, ⟨e⟩⟩ := H
  have A := final_isomAct (𝓞 K) K V h g.1 g.2 M
  refine ⟨A.2.2.2.2.2 h1, A.2.2.2.1.2 h2, Submodule.map_mono h3, ⟨?_⟩⟩
  let g' : V ≃ₗ[𝓞 K] V := (g : V ≃ₗ[K] V).restrictScalars (𝓞 K)
  let f : M ≃ₗ[𝓞 K] ↥(g • M) := g'.submoduleMap M
  refine (Submodule.Quotient.equiv _ _ f ?_).symm.trans e
  ext ⟨x, hx⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y.1, hy, congrArg Subtype.val hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, h3 hy⟩, hy, Subtype.ext hxy⟩


noncomputable def up (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V := sSup {M | Over h 𝔓 L M}

omit [NumberField K] in
theorem up_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L : Submodule (𝓞 K) V) :
    up h 𝔓 (g • L) = g • up h 𝔓 L := by
  have key : ∀ (g : isom h) (L : Submodule (𝓞 K) V), g • up h 𝔓 L ≤ up h 𝔓 (g • L) := by
    intro g L
    change Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup (over_smul h 𝔓 g L M hM)
  refine le_antisymm ?_ (key g L)
  have h1 := key g⁻¹ (g • L)
  rw [inv_smul_smul] at h1
  have h2 : g • g⁻¹ • up h 𝔓 (g • L) ≤ g • up h 𝔓 L := Submodule.map_mono h1
  rwa [smul_inv_smul] at h2

omit [NumberField K] in
theorem up_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V)
    (hu : ∃! M, Over h 𝔓 L M) (hM : Over h 𝔓 L M) : up h 𝔓 L = M := by
  have : {M | Over h 𝔓 L M} = {M} := by
    ext N
    exact ⟨fun hN => hu.unique hN hM, fun hN => by rw [Set.mem_singleton_iff.1 hN]; exact hM⟩
  rw [up, this, sSup_singleton]

end

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → mass h L = mass h' I * (((T : ℝ) ^ Module.finrank K V - 1) / ((T : ℝ) - 1)) ^ fDeg K := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hn V' _ _ _ _ _ h' hs' I hI T hT hsp L hL hLq
  have hnd := nondeg_of_pd h hp
  have hp' := pd_of_ortho hK h' I _ hI
  have hnd' := nondeg_of_pd h' hp'
  obtain ⟨⟨s, hcard, hsP, hcop, hprod⟩, hgen⟩ := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V h hK hs hnd T hT hsp
  have hT0 : (T : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hP0 : (∏ P ∈ s, P) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hprod
    exact hT0 hprod
  obtain ⟨o1, o2⟩ := GlobalTheory.T.exists_unimodular_overlattice_cyclic_split_discriminant K V h hK hs hnd _ hP0 hcop
  rw [hprod] at o1 o2
  have hex : ∀ N ∈ genus h L, ∃! M, Over h (∏ P ∈ s, P) N M := by
    intro N hN
    obtain ⟨M, hM, hu⟩ := o1 N ((hgen L N hL hLq).1 hN).1 ((hgen L N hL hLq).1 hN).2
    refine ⟨M, ⟨hM.1.toIsLattice, hM.2⟩, ?_⟩
    intro M' hM'
    letI := hN.1
    letI := hM'.1
    exact hu M' ⟨Submodule.IsFullLattice.of_le K hM'.2.2.1, hM'.2⟩
  obtain ⟨M0, hM0, -⟩ := o1 L hL hLq
  have hM0full : Submodule.IsFullLattice K M0 := by
    letI := hL.1
    letI := hM0.1
    exact Submodule.IsFullLattice.of_le K hM0.2.2.1
  obtain ⟨-, m2, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨-, m2', m3'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨c, hc⟩ := hMM K hK _ hn
  obtain ⟨iL, iU, iR⟩ := m3' I _ hI
  have iLfull : Submodule.IsFullLattice K I := by
    obtain ⟨e, -, he, hIeq, -⟩ := hI
    refine { toIsLattice := iL, span_eq_top := ?_ }
    rw [hIeq, Submodule.span_span_of_tower (𝓞 K), he]
  have e0 : mass h M0 = mass h' I := by
    rw [hc V h hs hp rfl M0 (m2 M0 hM0.1 hM0.2.1).1, (m2 M0 hM0.1 hM0.2.1).2.2,
      hc V' h' hs' hp' iR I (m2' I iLfull iU).1, (m2' I iLfull iU).2.2]
  obtain ⟨b1, b2, b3, b4, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L hL.1
  obtain ⟨a1, a2, a3, -, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M0 hM0full
  have hmaps : Set.MapsTo (up h (∏ P ∈ s, P)) (genus h L) (genus h M0) := by
    intro N hN
    obtain ⟨M, hM, -⟩ := hex N hN
    rw [up_eq h _ N M (hex N hN) hM]
    exact (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M0 M (m2 M0 hM0.1 hM0.2.1).1).2 (m2 M (by
      letI := hN.1
      letI := hM.1
      exact Submodule.IsFullLattice.of_le K hM.2.2.1) hM.2.1).1
  have hfib := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ (genus h L) (genus h M0) (up h (∏ P ∈ s, P))
    (up_smul h _) b3 a3 hmaps (fun y hy => b4 y hy.1)
  set B : ℕ := (∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card with hB
  have hconst : ∀ M ∈ genus h M0,
      ((((genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M}).encard : ℕ∞) : ℝ≥0∞) = (B : ℝ≥0∞) := by
    intro M hM
    have hU : IsUnimodular h M :=
      (((final_genusBasic (𝓞 K) K V h hs star_mem_range).2.2 M0 M hM0.1.fg hM.1.fg hM.2).1).1 hM0.2.1
    have hset : (genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M} = {N : Submodule (𝓞 K) V | N ≤ M ∧
        Nonempty ((↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))} := by
      ext N
      constructor
      · rintro ⟨hN, hNM⟩
        obtain ⟨M1, hM1, -⟩ := hex N hN
        have : M1 = M := (up_eq h _ N M1 (hex N hN) hM1).symm.trans hNM
        subst this
        exact hM1.2.2
      · rintro ⟨h1, h2⟩
        have hN : N ∈ genus h L := (hgen L N hL hLq).2 (o2 M N hM.1 hU h1 h2)
        exact ⟨hN, up_eq h _ N M (hex N hN) ⟨hM.1.toIsLattice, hU, h1, h2⟩⟩
    rw [hset, GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes K V M hM.1 T s hT hsP]
    exact ENat.toENNReal_coe _
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have hsum : orbMass (isom h) (genus h L) = (B : ℝ≥0∞) * orbMass (isom h) (genus h M0) := by
    rw [hfib, ← p2]
    exact le_antisymm (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).le)
      (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).ge)
  rw [← b1, ← a1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff b2.le (by positivity)] at hsum
  have hT1 : (T : ℝ) ≠ 1 := by exact_mod_cast hT.one_lt.ne'
  rw [hsum, e0, hB, hcard, mul_comm, ← geom_sum_eq hT1]
  push_cast
  rfl

end GlobalTheory.Mass.CyclicDisc
end

section

namespace GlobalTheory

theorem hermRepUnram : Formalism.HermitianLattices.Ext.L3.HermRepUnram := GlobalTheory.T.binaryHermitianForm_represents_totallyPositive

instance : Fact (Formalism.HermitianLattices.Ext.L3.HermRepUnram) := ⟨hermRepUnram⟩

end GlobalTheory
end

section

namespace GlobalTheory.DecTransport

theorem decLow_main : Formalism.FourierDecayAlt.ThreeDimData.DecLow := decLow_holds

end GlobalTheory.DecTransport
end

section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem capParam_of_isHCTypeW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → (∀ i : Fin k, U (i.val + 1) = u i) → Q.CapParam k r z π U := by
  intro k r z u U Wp _ _ _ π hz hT hπ hU
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', hu'⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  intro Bs hB w v
  rw [hu'.2.2.2.2.2 Bs hB w v]
  congr 1
  have key : ∀ f : ℕ → ℝ, ∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (f i : ℂ)) =
      ∏ s : Fin k, (w - (k : ℂ) / 2 + 1 / 2 + (f (s.val + 1) : ℂ)) := by
    intro f
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Fin.prod_univ_eq_prod_range (fun i => w - (k : ℂ) / 2 + 1 / 2 + (f (1 + i) : ℂ))]
    exact Finset.prod_congr rfl fun s _ => by rw [add_comm 1 s.val]
  rw [key, key, ← GlobalTheory.SupNonzero.prod_eq hu' hπ']
  simp only [hU]

end GlobalTheory.ThA
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem rowMap_surjective_of_primitiveRows_alt : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 Ps ψs Zs)) (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (s : ℕ), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → PrimRows3 R (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3) → (R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).zs = Zs → HEq ((R.toCx3 (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3)).data (⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ : Face3 D A3).cr true) S1 → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I Dcf Spf Zscf s hD hOk hSep hW hP hzs hS1
  obtain ⟨h1, h2⟩ := GlobalTheory.T.primitiveRows_map_bijective_columnLevel D G Pl0 I0 T A3 Ks R ⟨P0, ψ0, Ps, ψs, Dcf, Spf, Zscf⟩ s hOk hSep hW hP Zs S1 hzs hS1
  exact GlobalTheory.T.V0_map_iota_eq_top_definite D G Pl0 I0 (List ℕ) T D.R.m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD ⟨s, hOk.ok2⟩ h1 h2

end GlobalTheory
end

section

open scoped Classical ComplexConjugate ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

noncomputable section

namespace GlobalTheory.GxConj

variable {r n : ℕ}

theorem hJ_adj (ε : Fin n → Bool) (A Ai : Matrix (Fin n) (Fin n) ℂ)
    (hU : Aiᴴ * Formalism.REAL.Jm ε * Ai = Formalism.REAL.Jm ε) (h1 : Ai * A = 1) (x y : Fin n → ℂ) :
    hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y := by
  have e : Aiᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * A := by
    calc Aiᴴ * Formalism.REAL.Jm ε = Aiᴴ * Formalism.REAL.Jm ε * (Ai * A) := by rw [h1, Matrix.mul_one]
      _ = (Aiᴴ * Formalism.REAL.Jm ε * Ai) * A := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * A := by rw [hU]
  have e2 : Aiᴴ *ᵥ (Formalism.REAL.Jm ε *ᵥ y) = Formalism.REAL.Jm ε *ᵥ (A *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e]
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, e2]

theorem hJ_sum_left {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ c, s c • x c) y = ∑ c, conj (s c) * hJ ε (x c) y := by
  unfold hJ
  simp only [star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_sum_right {ι : Type*} [Fintype ι] (ε : Fin n → Bool) (s : ι → ℂ) (x : Fin n → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ c, s c • y c) = ∑ c, s c * hJ ε x (y c) := by
  unfold hJ
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem mulVec_lin {ι : Type*} [Fintype ι] (B : Matrix (Fin n) (Fin n) ℂ) (s : ι → ℂ) (y : ι → Fin n → ℂ) :
    B *ᵥ ∑ c, s c • y c = ∑ c, s c • (B *ᵥ y c) := by
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem zhat_conj (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (A Ai B C : Matrix (Fin n) (Fin n) ℂ)
    (hadj : ∀ x y, hJ ε x (A *ᵥ y) = hJ ε (Ai *ᵥ x) y) (L M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hL : ∀ a, Ai *ᵥ f a = ∑ c, L a c • f c) (hM : ∀ b, C *ᵥ f' b = ∑ d, M b d • f' d) :
    Zhat ε f f' (A * B * C) = L.map (starRingEnd ℂ) * Zhat ε f f' B * Mᵀ := by
  ext a b
  have e1 : (A * B * C) *ᵥ f' b = A *ᵥ (B *ᵥ (C *ᵥ f' b)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  simp only [Formalism.L2.SG.RealObj.Zhat, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [e1, hadj, hL, hM, mulVec_lin, hJ_sum_left]
  simp only [hJ_sum_right, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.GxConj

namespace GlobalTheory

open GlobalTheory.GxConj

end GlobalTheory
end
end

section

namespace GlobalTheory

theorem capelliDiscreteSeriesInfChar : PI.DSInfCharCap.DSInfCharCap :=
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end GlobalTheory
end
