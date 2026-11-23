module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle476
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle375
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isLanglandsClassification_add_of_irreducible_product : LanglandsMultisegments → StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (r t : ℕ) (σ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k)) (π : IrrRep (GL (Fin (r + t)) k)) (𝔪 𝔫 : Multiset (Segment k)), IsL 𝔪 σ.ρ → IsL 𝔫 τ.ρ → Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → IsL (𝔪 + 𝔫) π.ρ := by
  first | exact @GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ | exact GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ | (intros; apply GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ <;> assumption)
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualFin

theorem ko_torsion : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ), (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ a : KO O, ∃ r : ℕ, (p : O) ^ r • a = 0 := by
  intro O _ _ _ p hp a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨o, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hϖ
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hp)
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu0 : algebraMap O (FractionRing O) (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  refine ⟨m, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨o * t ^ m * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, hu, ht]
  simp only [map_mul, map_pow]
  have hui : algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = (algebraMap O (FractionRing O) (u : O))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [hui]
  field_simp
  ring


open GlobalTheory.TateFin GlobalTheory.TateTop GlobalTheory.Cyc.TwistLift ReciprocityTheory.Neutral.Bridge in
theorem exists_cocycle_cup_not_cob : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (_root_.Formalism.RepresentationBoundsCohomology.LOC.twist D.ε (KO O)) := by
  intro hTate p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hOr hOc hOt hOa hpm hp0
    hemb i D hcyc hlat hperf hcontT hTo hT2 hT2' hcs hcs' ϖ hϖ c hc hcB r hr n hrn
  by_contra H
  push_neg at H
  apply hcB
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI : ContinuousMul G := ⟨by
    have h := i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))
    refine h.congr fun q => ?_
    show i.symm (i q.1 * i q.2) = q.1 * q.2
    rw [← map_mul, ContinuousMulEquiv.symm_apply_apply]⟩
  let χ : G →* ℤ_[p]ˣ := ((cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))).comp (i : G →* Formalism.GaloisCohomology.GK p K)
  have hχ : Continuous fun g => (χ g : ℤ_[p]) :=
    Units.continuous_val.comp ((cyclotomicCharacter.continuous p K (PadicAlgCl p)).comp i.continuous)
  have hT' : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (p ^ (k + 1))) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (p ^ (k + 1))) G M)
      (hrho : ContAction rho), DualityFor (redChar χ (k + 1)) rho hrho := by
    intro k M _ _ _ _ _ rho hrho
    refine DualityFor.of_comp i.symm _ hrho ?_
    have h1 : (redChar χ (k + 1)).comp (i.symm : Formalism.GaloisCohomology.GK p K →* G) = Formalism.GaloisCohomology.cycK p K (k + 1) :=
      MonoidHom.ext fun g => congrArg (Formalism.GaloisCohomology.cycK p K (k + 1)) (i.apply_symm_apply g)
    rw [h1]
    exact hTate p K hK (k + 1) M _ (Nat.succ_pos _) (contAction_comp i.symm hrho)
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_padicInt_ringHom_congr_toZModPow hOr hOc hOt hOa hpm
  have hspan : Ideal.span {(p : O)} ≠ ⊤ := fun h =>
    (IsLocalRing.mem_maximalIdeal _).1 hpm (Ideal.span_singleton_eq_top.1 h)
  have hkrull : ∀ a b : O, (∀ k : ℕ, a - b ∈ Ideal.span {(p : O) ^ k}) → a = b := by
    intro a b h
    have h0 := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {(p : O)}) hspan
    have h1 : a - b ∈ ⨅ k, Ideal.span {(p : O)} ^ k :=
      Ideal.mem_iInf.2 fun k => by rw [Ideal.span_singleton_pow]; exact h k
    rw [h0, Ideal.mem_bot, sub_eq_zero] at h1
    exact h1
  have hιε : ∀ g, ι (χ g : ℤ_[p]) = (D.ε g : O) := by
    intro g
    refine hkrull _ _ fun k => ?_
    obtain ⟨ζ, hζ, hζa⟩ := GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow K (i g) k
    obtain ⟨a, ha, hεa⟩ := hcyc g k ζ hζ
    have e1 : (a : ZMod (p ^ k)) = PadicInt.toZModPow k (χ g : ℤ_[p]) := hζa a ha
    have e2 := hι (χ g : ℤ_[p]) k
    rw [← e1, ZMod.val_natCast] at e2
    have e3 : ((a : ℕ) : O) - ((a % p ^ k : ℕ) : O) ∈ Ideal.span {(p : O) ^ k} := by
      have h : ((a : ℕ) : O) = ((a / p ^ k : ℕ) : O) * (p : O) ^ k + ((a % p ^ k : ℕ) : O) := by
        have h' := congrArg (Nat.cast : ℕ → O) (Nat.div_add_mod' a (p ^ k)).symm
        push_cast at h'
        exact h'
      exact Ideal.mem_span_singleton'.2 ⟨((a / p ^ k : ℕ) : O), by rw [h]; ring⟩
    have e4 : ι (χ g : ℤ_[p]) - (D.ε g : O) = (ι (χ g : ℤ_[p]) - ((a % p ^ k : ℕ) : O)) -
        (((a : ℕ) : O) - ((a % p ^ k : ℕ) : O)) - ((D.ε g : O) - (a : O)) := by ring
    rw [e4]
    exact sub_mem (sub_mem e2 e3) hεa
  letI : Module ℤ_[p] (KO O) := Module.compHom (KO O) ι
  have hsmul : ∀ (u : ℤ_[p]) (y : KO O), u • y = ι u • y := fun _ _ => rfl
  have htor : ∀ a : KO O, ∃ r : ℕ, (p : ℤ_[p]) ^ r • a = 0 := fun a => by
    obtain ⟨r, hr⟩ := ko_torsion p hpm a
    exact ⟨r, by rw [hsmul, map_pow, map_natCast]; exact hr⟩
  have hKOd : DiscreteTopology (KO O) :=
    QuotientAddGroup.discreteTopology (N := (1 : Submodule O (FractionRing O)).toAddSubgroup) (by
      have : ((1 : Submodule O (FractionRing O)).toAddSubgroup : Set (FractionRing O)) =
          Set.range (algebraMap O (FractionRing O)) := by
        ext x; simp [Submodule.mem_one, eq_comm]
      rw [this]; exact hemb.isOpen_range)
  have hVd : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hTo
  have hclc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hc.1
  set X := LinearMap.ker (LinearMap.lsmul O (VT ⧸ D.T) (ϖ ^ n)) with hXdef
  have memX : ∀ x : VT ⧸ D.T, x ∈ X ↔ ϖ ^ n • x = 0 := fun x => by
    rw [hXdef, LinearMap.mem_ker, LinearMap.lsmul_apply]
  haveI : Finite X := GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient D.T hOr hOc hOa hlat ϖ hϖ n
  obtain ⟨hcT', hopen, -⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hOc hemb hlat hperf hT2' ϖ hϖ
  haveI : CompactSpace ↥D.T' := hcT'
  haveI : Finite (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    AddSubgroup.quotient_finite_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n)
  haveI hNd : DiscreteTopology (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    QuotientAddGroup.discreteTopology (N := (powSub (M := ↥D.T') ϖ n).toAddSubgroup) (hopen n)
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hpm)
  have hpow : ∀ {M : Type} [AddCommGroup M] [Module O M] (y : M), p ^ n • y = t ^ n • ϖ ^ n • y :=
    fun y => by rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ht, mul_pow, mul_comm, mul_smul]
  have hX : ∀ x : X, p ^ n • x = 0 := fun x => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, hpow, (memX _).1 x.2, smul_zero]; rfl)
  have hN : ∀ y : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n, p ^ n • y = 0 := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hpow, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_comm]
    exact smul_mem_powSub ϖ n _
  let a : G → X → X := fun g x => ⟨D.ρA g x, by rw [memX, ← map_smul, (memX _).1 x.2, map_zero]⟩
  let a' : G → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    fun g => (quotRep D.ρTl' ϖ n g).toAddMonoidHom
  have h1 : ∀ y, a' 1 y = y := fun y => by
    show quotRep D.ρTl' ϖ n 1 y = y
    rw [map_one]; rfl
  have hm : ∀ g h y, a' (g * h) y = a' g (a' h y) := fun g h y => by
    show quotRep D.ρTl' ϖ n (g * h) y = quotRep D.ρTl' ϖ n g (quotRep D.ρTl' ϖ n h y)
    rw [map_mul]; rfl
  have hlc : ∀ y, IsLocallyConstant fun g => a' g y := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [IsLocallyConstant.iff_continuous]
    show Continuous fun g => (Submodule.Quotient.mk (D.ρTl' g t0) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n)
    exact continuous_quot_mk.comp ((sub_contAction D.contT' D.T' D.stT').comp
      (continuous_id.prodMk continuous_const))
  let βf : X → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := fun x =>
    ((powSub (M := ↥D.T') ϖ n).liftQ (pairKO D.bT D.T (x : VT ⧸ D.T)) (fun t0 ht0 => by
      rw [LinearMap.mem_ker]; exact pairKO_eq_zero_of_mem D ((memX _).1 x.2) ht0)).toAddMonoidHom
  let β : X →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := AddMonoidHom.mk' βf (fun x x' => by
    ext y
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T ((x + x' : X) : VT ⧸ D.T) t0 =
      pairKO D.bT D.T (x : VT ⧸ D.T) t0 + pairKO D.bT D.T (x' : VT ⧸ D.T) t0
    rw [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
  have he : ∀ g x y, β (a g x) (a' g y) = (χ g : ℤ_[p]) • β x y := fun g x y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T (D.ρA g x) (D.ρTl' g t0) = ι (χ g : ℤ_[p]) • pairKO D.bT D.T (x : VT ⧸ D.T) t0
    rw [D.pairKO_equiv, _root_.Formalism.RepresentationBoundsCohomology.LOC.twist_apply, hιε]
  have hs : toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) ≠ 0 := by
    intro h0
    rw [toKO, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
    obtain ⟨o, ho⟩ := h0
    apply hϖ.not_isUnit
    have hinj := IsFractionRing.injective O (FractionRing O)
    have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    refine IsUnit.of_mul_eq_one (b := o) (hinj ?_)
    rw [map_mul, ho, map_one, mul_inv_cancel₀ hπ]
  have hβ1 : ∀ x : X, x ≠ 0 → ∃ y, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro x hx
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer D hlat hperf ϖ hϖ (x : VT ⧸ D.T) (fun h => hx (Subtype.ext h))
    exact ⟨Submodule.Quotient.mk f, hf⟩
  have hβ2 : ∀ y, y ≠ 0 → ∃ x : X, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hf : f ∉ powSub (M := ↥D.T') ϖ n := fun h => hy ((Submodule.Quotient.mk_eq_zero _).2 h)
    obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer D ϖ hϖ n f hf
    exact ⟨⟨x, (memX x).2 hx1⟩, hx2⟩
  have hcX : ∀ g, c g ∈ X := fun g => (memX _).2 (by
    rw [← Nat.sub_add_cancel hrn, pow_add, mul_smul, hr, smul_zero])
  let c₀ : G → X := fun g => ⟨c g, hcX g⟩
  obtain ⟨x, hx⟩ := (nondeg_torsion hχ hT' htor hX hN a a' h1 hm hlc β he hs hβ1 hβ2).1 c₀
    (IsLocallyConstant.desc _ Subtype.val hclc Subtype.val_injective)
    (fun g h => Subtype.ext (hc.2 g h)) (by
      intro c' hc'l hc'c
      obtain ⟨b, hbc, hbe⟩ := (separated_dvr_second_cohomology_mem _ _).1 (H c' ⟨hc'l.continuous, fun g h => hc'c g h⟩)
      refine ⟨b, (IsLocallyConstant.iff_continuous b).2 hbc, fun q => ?_⟩
      obtain ⟨g, h⟩ := q
      have e := congrFun hbe (g, h)
      have e2 : β (c₀ g) (a' g (c' h)) = cupMod D c ϖ n c' (g, h) := by
        conv_lhs => rw [← mk_qlift (c' h)]
        rfl
      rw [e2, ← e]
      show _ = ι (χ g : ℤ_[p]) • b h - b (g * h) + b g
      rw [hιε]
      rfl)
  exact (mem_coboundaries1 _ _).2 ⟨x, fun g => congrArg Subtype.val (hx g)⟩

end GlobalTheory.LocDualFin
end
end

section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_H2_le_of_local_duality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT l K hK r M rho hr hrho).2
  obtain ⟨⟨e⟩, -, -, -, h20⟩ := hT l K hK r M rho hr hrho
  refine ⟨hfin, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Subtype.finite
  haveI : Finite (H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  calc Nat.card (H2 rho)
      ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
          H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        Nat.card_le_card_of_injective _ h20.1
    _ = Nat.card (Module.Dual (ZMod (l ^ r))
          (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))))) :=
        Nat.card_congr (LinearEquiv.congrRight e).toEquiv
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        GlobalTheory.card_dual_zmod_le_card (l ^ r) _
    _ ≤ Nat.card (TDual (ZMod (l ^ r)) M) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card M := GlobalTheory.card_dual_zmod_le_card (l ^ r) M

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FracInv

theorem tied_frac_invariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) →
      ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  intro l _ P AI T K a b hb h
  have hF : IsField P.R.BdR := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have h' : ∀ g, b * (P.PD K).actB g a = (P.PD K).actB g b * a := by
    intro g
    have := h g.1 g.2
    rw [P.PD_actB, P.PD_actB, mul_comm, this, mul_comm]
  obtain ⟨c, hc⟩ := GlobalTheory.Per.FontaineBound.frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι a)
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h' g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    refine GlobalTheory.FracAlg.mem_Kur_of_ratio l P AI T a b (c : Om l) hb ?_
    have h1 := hc
    rw [P.PD_ι, P.PD_ι] at h1
    exact h1
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

end GlobalTheory.Per.FracInv
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.SandArb

theorem map_mulLeft {O R M : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    (a : R) (z : R ⊗[O] M) :
    TensorProduct.map (LinearMap.mulLeft O a) LinearMap.id z = a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) {s : ℕ} (hs : W.s = s)
    (hp : PD.p.Prime) (hL : LevLaws W) (hI : IoLaws E)



theorem of_layers {Zl : Type} [CommRing Zl] (zl : PowerSeries Zl →+* LetA O n) (h1 : IsCrys PD W.one.ρ)
    (hP : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (w : RA) (c : RW) (hc : c = inclR w)
    (hS : GlobalTheory.HWL.Sand (latOf E hs hp hL hI zl h1 hP) T w) :
    (∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x)) ∧
      ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)} := by
  subst hc
  have hN : nOf W T = W.N T := nOf_crys W hT
  have h1' : ∀ x ∈ nOf W T, ∃ y : TW RA T, TWincl inclR T y = inclR w • E.jD T x := hS.1
  have h2' : ∀ t : ↥T.L.T, inclR w • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ (a : RA), ∃ y ∈ nOf W T, z = inclR a • E.jD T y} := hS.2
  rw [hN] at h1' h2'
  refine ⟨fun x hx => ?_, fun t => ?_⟩
  · rw [map_mulLeft]; exact h1' x hx
  · have := h2' t
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
    simp only [map_mulLeft]
    exact this

end Generic

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (hL : Laws H F h)



theorem sand_layers (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    ∃ m : ℕ, GlobalTheory.HWL.Sand (LatL H F h hL) T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) :=
  apply_layers H F h hL
    (fun _ _ _ _ Mo => ∃ m : ℕ, GlobalTheory.HWL.Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL))
    (fun Γ R I hI E Mo => GlobalTheory.HWL.SandProof.sandwich l P AI K s LL h Γ R I hI E Mo T hT)

theorem incl_pow (a : RA LL) (w : Ainf l) (ha : a = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) (m : ℕ) :
    inclR LL a ^ m = inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w ^ m)) := by
  rw [ha, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]

end


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sandwich : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∃ m : ℕ, (∀ x ∈ W.N T, ∃ y : TW (RA LL) T, TWincl (inclR LL) T y = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io W.X) ^ m)) LinearMap.id (E.jD T x)) ∧ ∀ t : ↥T.L.T, ((inclR LL (E.io W.X) ^ m) ⊗ₜ[↥(OL LL)] t : TW (RW LL) T) ∈ Submodule.span ↥(OL LL) {z : TW (RW LL) T | ∃ a : RA LL, ∃ y ∈ W.N T, z = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL a)) LinearMap.id (E.jD T y)} := by
  intro D HW F l _ K s LL h
  have hL : Laws (HW l) (F l) h := GlobalTheory.T.wach_functor_three_layer_properties_every_place D HW F l K s LL h
  have hX := (GlobalTheory.T.wachInclusion_X_Q_frobenius D HW F l K s LL h).1
  refine fun T hT => (sand_layers (HW l) (F l) h hL T hT).imp fun m hm => ?_
  exact of_layers ((F l).E K s LL h).tie ((HW l).W_s K s LL h) (p_prime (D.loc l) K) hL.lev hL.io _ hL.one
    ((HW l).W_proj K s LL h) T hT _ _ (incl_pow _ _ hX m) hm

end GlobalTheory.NL.SandArb
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem summable_absNorm_rpow_heightOneSpectrum :
    ∀ (F : Type) [Field F] [NumberField F] (σ : ℝ), 1 < σ →
      Summable (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) :=
  fun F _ _ σ hσ => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 σ hσ).2

end GlobalTheory
end
