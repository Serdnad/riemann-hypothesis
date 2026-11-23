module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsDpstFrobeniusEigenvectorOfCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle267
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem exists_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ)
    (hκ : IsOpen {σ : ↥(Ine (F := F) A) | κ (Subgroup.inclusion (Ine_le_Dec A) σ) = 1})
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) :
    ∃ (K : FinExt l) (h : Bw.Kw.1 ≤ K.1), ∀ g ∈ IK K, κ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) = 1 := by
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 hκ
  have h1 : (1 : G F Ω) ∈ U := by
    have : (1 : ↥(Ine (F := F) A)) ∈ Subtype.val ⁻¹' U := by
      rw [hUe]
      exact map_one (κ.comp (Subgroup.inclusion (Ine_le_Dec A)))
    exact this
  have hU1 : IsOpen {g : ↥(GK Bw.Kw) | ((Bw.e.symm g : ↥(Dec (F := F) A)) : G F Ω) ∈ U} :=
    hU.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U', hU', hUe'⟩ := isOpen_induced_iff.1 hU1
  have h1' : (1 : GQ l) ∈ U' := by
    have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' U' := by
      rw [hUe']
      change ((Bw.e.symm 1 : ↥(Dec (F := F) A)) : G F Ω) ∈ U
      rw [map_one]
      exact h1
    exact this
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) U').1 (hU'.mem_nhds h1')
  refine ⟨GlobalTheory.Pst.supExt Bw.Kw ⟨E, hE⟩, le_sup_left, fun g hg => ?_⟩
  set g' : ↥(GK Bw.Kw) := Subgroup.inclusion (GK_le (K' := GlobalTheory.Pst.supExt Bw.Kw ⟨E, hE⟩) le_sup_left) g with hg'
  have hgU : g' ∈ Subtype.val ⁻¹' U' :=
    hEU (GK_le (K := ⟨E, hE⟩) (K' := GlobalTheory.Pst.supExt Bw.Kw ⟨E, hE⟩) le_sup_right g.2)
  rw [hUe'] at hgU
  have hI : ((Bw.e.symm g' : ↥(Dec (F := F) A)) : G F Ω) ∈ Ine (F := F) A := by
    refine ⟨(Bw.e.symm g').2, fun x hx => ?_⟩
    rw [hj.valuation_lt_one_iff, map_sub, ← Bw.e_comm, MulEquiv.apply_symm_apply]
    exact GlobalTheory.FrobGen.norm_sub_lt ((UpperTheory.V.Loc.memIK _ g).1 hg) _
      ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
  have h2 : (⟨_, hI⟩ : ↥(Ine (F := F) A)) ∈ Subtype.val ⁻¹' U := hgU
  rw [hUe] at h2
  exact h2

theorem UpperTheory.rankOne_character_isdR_and_jumps_zero :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → IsOpen {σ : ↥(Ine (F := F) A) | κ (Subgroup.inclusion (Ine_le_Dec A) σ) = 1} → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.IsdRAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) ∧ ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), GlobalTheory.Pst.IsInduced Bw τ τ' → GlobalTheory.Pst.IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 κ) τ {0} := by
  intro F Ω _ _ _ _ _ l _ A κ hc hκ O _ _ _ Bw hj
  obtain ⟨K, h, hK⟩ := exists_ext κ hκ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  haveI : CompactSpace ↥(GK Bw.Kw) := GlobalTheory.UnramifiedCrys.compactSpace_GK _
  haveI : CompactSpace ↥(Dec (F := F) A) := Bw.e.symm.surjective.compactSpace Bw.e_symm_cont
  haveI : T2Space ↥(Dec (F := F) A) := inferInstance
  have hv : ∀ g a b, ((GlobalTheory.TripleGal.rk1 κ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) a b = κ g := by
    intro g a b
    rw [Subsingleton.elim a b]
    exact Matrix.diagonal_apply_eq _ _
  have hc0 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 κ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) :=
    continuous_pi fun a => continuous_pi fun b => by
      simp only [hv]
      exact Units.continuous_val.comp hc
  haveI := K.2
  let N : FinExt l := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
  obtain ⟨LL, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l _ 1 _ hc0 (GlobalTheory.Pst.supExt Bw.LL N)
  obtain ⟨r, hr⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem _ LL.1 hent
  have l₁ : Bw.LL.1 ≤ LL.1 := le_trans le_sup_left hL
  have l₂ : N.1 ≤ LL.1 := le_trans le_sup_right hL
  have hM : GlobalTheory.Pst.IsModel Bw (GlobalTheory.TripleGal.rk1 κ) LL r := ⟨l₁, by
    ext g a b
    exact hr g a b⟩
  let μ : ↥(GK K) →* (↥LL.1)ˣ := (Matrix.GeneralLinearGroup.det.comp r).comp
    (Bw.e.symm.toMonoidHom.comp (Subgroup.inclusion (GK_le h)))
  have hμr : ∀ g, ((μ g : (↥LL.1)ˣ) : ↥LL.1) =
      (r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 := fun g =>
    Matrix.det_fin_one _
  have hμ : ∀ g, (((μ g : (↥LL.1)ˣ) : ↥LL.1) : Om l) = κ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) := fun g => by
    rw [hμr, ← hv _ 0 0]
    exact hr _ 0 0
  have hμc : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun g : ↥(GK K) => ((κ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : (Qbar l)ˣ) : Qbar l) :=
      Units.continuous_val.comp (hc.comp (Bw.e_symm_cont.comp (continuous_inclusion (GK_le h))))
    exact this.congr fun g => (hμ g).symm
  obtain ⟨hcr, hm⟩ := GlobalTheory.UnramifiedChar.isCrys_and_multV_eq l _ _ T K LL μ hμc fun g hg => by
    apply Units.ext
    apply Subtype.ext
    rw [hμ, hK g hg]
    rfl
  let e : ↥LL.1 ≃ₗ[↥LL.1] (Fin 1 → ↥LL.1) := (LinearEquiv.funUnique (Fin 1) ↥LL.1 ↥LL.1).symm
  have he : ∀ g x, e (Formalism.WeaklyAdmissibleFiltrations.charRep μ g x) =
      ((Bw.repE LL r).comp (Subgroup.inclusion (GK_le h)) : Representation ↥LL.1 ↥(GK K) _) g (e x) := by
    intro g x
    funext a
    change ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x =
      Matrix.mulVec (r (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin 1) (Fin 1) ↥LL.1) (fun _ => x) a
    rw [hμr, Subsingleton.elim a 0]
    simp [Matrix.mulVec, dotProduct]
  have hcr' := Formalism.MainNotions.N.K.Norm.isCrys_congr _ e he hcr
  have hd : Formalism.MainNotions.N.IsDR ((UpperTheory.V.Loc.PP l).PD Bw.Kw) (Bw.repE LL r) :=
    (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l _ _ T _ K LL h _ _).2.2
      (GlobalTheory.Per.CrisDR.isDR_of_isCrys l _ _ T K LL _ _ hcr').1
  have hD : Bw.IsdRE (UpperTheory.V.Loc.PP l) LL r := by
    unfold Formalism.MainNotions.N.IsDR at hd
    rw [Module.finrank_fin_fun] at hd
    exact hd
  refine ⟨⟨_, _, hM, hD⟩, fun τ LL' τ' hτ => ?_⟩
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥Bw.Kw.1)
    (M := Om l) (E := Om l) (LL'.1.val.comp τ')
  let τ₂ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 := (σ.comp K.1.val).codRestrict LL.1.toSubalgebra fun x =>
    l₂ (AlgHom.fieldRange_le_normalClosure (σ.comp K.1.val) ⟨x, rfl⟩)
  refine ⟨LL, r, hM, hD, τ₂.comp (IntermediateField.inclusion h), fun x => ?_, fun n => ?_⟩
  · rw [hτ x]
    exact (AlgHom.congr_fun hσ _).symm
  · rw [LocBridge.multE, ← GlobalTheory.JumpRestrict.multV_restrict l _ _ T _ K LL h _ _ hd,
      ← Formalism.MainNotions.N.K.Norm.multV_congr _ e he, hm, Multiset.count_singleton]
    split_ifs <;> rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open GlobalTheory.Pst GlobalTheory.TripleGal Module
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

private theorem abs_eig {L D : Type} [Field L] [AddCommGroup D] [Module L D] (U : (End L D)ˣ) (φ g : End L D)
    (hU : (U : End L D) = φ) (hc : φ * g = g * φ) (x : D) (hx0 : x ≠ 0) (s : L) (a b : ℕ) (k : ℤ)
    (hk : k = (b : ℤ) + -(a : ℤ)) (key : g ((φ ^ b) x) = s • (φ ^ a) x) :
    ∃ x' : D, x' ≠ 0 ∧ ∀ n : ℕ, (g * ((U ^ k : (End L D)ˣ) : End L D)) ((φ ^ n) x') = s • (φ ^ n) x' := by
  subst hU hk
  have k0 : g * ((U ^ ((b : ℤ) + -(a : ℤ)) : (End L D)ˣ) : End L D) * (U : End L D) ^ a = g * (U : End L D) ^ b := by
    rw [zpow_add, zpow_neg, zpow_natCast, zpow_natCast, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      mul_assoc, ← Units.val_mul, inv_mul_cancel_right]
  refine ⟨((U : End L D) ^ a) x, fun h0 => hx0 ?_, fun n => ?_⟩
  · exact ((End.isUnit_iff _).1 (U.isUnit.pow a)).1 (h0.trans (map_zero _).symm)
  · have hc' : Commute (g * ((U ^ ((b : ℤ) + -(a : ℤ)) : (End L D)ˣ) : End L D)) ((U : End L D) ^ n) :=
      (Commute.mul_left hc.symm (Commute.units_zpow_right (Commute.refl _) _).symm).pow_right n
    rw [← End.mul_apply, hc'.eq, End.mul_apply, ← End.mul_apply _ _ x, k0, End.mul_apply, key, map_smul]

private theorem eig_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
    (ι : Qbar l ≃+* ℂ) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V)
    (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ) (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (σ : Weil h) (s : ↥L.1) {a b : ℕ}
    (hσ : ActsAs A (normV w) (σ : G F Ω) a b)
    (key : actD P ρ (weilToGK Bw h σ) ((phiD P ρ ^ (resDeg l w * b)) x) = s • (phiD P ρ ^ (resDeg l w * a)) x) :
    ι (s : Om l) ∈ (wdPst P ι Bw h hj ρ).eig σ := by
  have hfin := hV.finite
  have e1 : -alpha l σ = ((resDeg l w * b : ℕ) : ℤ) + -((resDeg l w * a : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨x', hx'0, k1⟩ := abs_eig (phiU P ρ) (phiD P ρ) (actD P ρ (weilToGK Bw h σ)) rfl (phiD_actD P ρ _) x hx0 s
    _ _ _ e1 key
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x') ≠ 0 := by
    by_contra hc
    exact hx'0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => not_not.1 fun hn => hc ⟨n, hn⟩)
  exact ParamAboveModel.mem_eig_wdPst P ι Bw h hj ρ _ h1 hV hn σ s (k1 n)

theorem UpperTheory.V.Loc.wdPotUnr :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous ψ → IsSmooth (ψ.comp (Subgroup.inclusion (Weil_le_Dec h))) → GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 ψ) → ∀ σ : Weil h, ι (ψ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 ψ)).eig σ := by
  intro F Ω _ _ _ _ _ l _ A w h O _ _ _ Bw hj ι ψ hψ hs hr σ
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨L, r', hM, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hr
  rw [e]
  let m : ↥(GK Bw.Kw) →* (↥L.1)ˣ := (Matrix.GeneralLinearGroup.det.comp r').comp Bw.e.symm.toMonoidHom
  have hm0 : ∀ g, (m g : ↥L.1) = (r' (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 := fun g => by
    simp [m, Matrix.det_unique]
  have hm : ∀ g, ((m g : ↥L.1) : Om l) = ψ (Bw.e.symm g) := fun g => by
    have := congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin 1) (Om l) =>
      (f (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) hM.2
    rw [hm0]
    simpa [Formalism.MainNotions.N.mapRep, rk1] using this
  have hρ : ∀ g v, Bw.repE L r' g v = (m g : ↥L.1) • v := fun g v => by
    ext i
    fin_cases i
    simp [LocBridge.repE, hm0, Matrix.mulVec, dotProduct]
  obtain ⟨V, hV1, hV2⟩ := isOpen_induced_iff.1 hs
  have ho2 : IsOpen {g : GK Bw.Kw | ((Bw.e.symm g : Dec (F := F) A) : G F Ω) ∈ V} :=
    hV1.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have h0 : (1 : Ine (F := F) A) ∈ Subtype.val ⁻¹' V := by rw [hV2]; simp
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simpa using h0
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  obtain ⟨x, hx0, hx⟩ := UpperTheory.exists_dpst_frobenius_eigenvector_of_character _ _ T Bw.Kw (supExt Bw.Kw ⟨K', hK1⟩) L le_sup_left m (Bw.repE L r') hρ
    (by simp only [hm]; exact Units.continuous_val.comp (hψ.comp Bw.e_symm_cont))
    (fun g hg hg' => by
      have h2 : g ∈ Subtype.val ⁻¹' U := hK2 (GK_le (K := ⟨K', hK1⟩) le_sup_right hg)
      rw [hU'] at h2
      have h3 : ((Bw.e.symm g : Dec (F := F) A) : G F Ω) ∈ Ine (F := F) A := by
        refine actsAs_zero_iff (q := 2).1 ⟨(Bw.e.symm g).2, fun y hy => ?_⟩
        rw [hj.valuation_lt_one_iff]
        simp only [pow_zero, pow_one]
        rw [map_sub, ← Bw.e_comm, MulEquiv.apply_symm_apply]
        exact GlobalTheory.FrobGen.norm_sub_lt hg' _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))
      have h4 : (⟨_, h3⟩ : Ine (F := F) A) ∈ Subtype.val ⁻¹' V := h2
      rw [hV2] at h4
      have h5 : ψ (Bw.e.symm g) = 1 := h4
      refine Units.ext (Subtype.ext ?_)
      rw [hm, h5]
      rfl)
  obtain ⟨a, b, hσ⟩ := σ.2
  have k2 := eig_of_frob (PP l) h Bw hj ι _ (by simp) hV x hx0 σ _ hσ
    (hx (weilToGK Bw h σ) _ _ (weilToGK_frobUr hj σ hσ))
  rw [hm] at k2
  simpa [weilToGK] using k2
end

section

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem cr_transport {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A G' V}
    (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : IsCr φ ρ → IsCr φ' ρ' := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  unfold IsCr
  rw [hr, hc]
  exact id

private theorem crys_of_isCr {l : ℕ} [Fact l.Prime] (K E' : FinExt l) {n : ℕ}
    (ρ : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1)) (h : IsCr (GK K).subtype ρ) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ := by
  have := E'.2
  have : IsModuleTopology ℚ_[l] (Fin n → ↥E'.1) := isModuleTopologyOfFiniteDimensional
  exact (isCrField K ρ).1.1 ((isCrIff K ρ).1.1 h)

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl, rfl⟩

theorem UpperTheory.V.Loc.potCrysOf :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1), (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) = (r (ψ h) : Matrix (Fin n) (Fin n) (Qbar l)) a b) → IsCr φ (colRep r') → UpperTheory.V.Af.PotCrysAt r (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hφψ n r hr E' r' hr' hcr
  have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := fun x => by
    change Valued.v (j x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  obtain ⟨L, Bw, hBj, hK⟩ := ex_bridge (E := F) j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw, fun x => by rw [hBj]; exact hj x, ?_⟩
  haveI : CompactSpace ↥(GK Bw.Kw) := by
    haveI := Bw.Kw.2
    exact isCompact_iff_compactSpace.1 Bw.Kw.1.fixingSubgroup_isClosed.isCompact
  haveI : CompactSpace ↥(Dec (F := F) (placeJ j)) :=
    Bw.e.symm.surjective.compactSpace Bw.e_symm_cont
  haveI : T2Space ↥(Dec (F := F) (placeJ j)) := inferInstance
  let r₀ := r.comp (Dec (F := F) (placeJ j)).subtype
  have hc0 : Continuous fun g => ((r₀ g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
    Units.continuous_val.comp (hr.comp continuous_subtype_val)
  obtain ⟨LL, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l _ n r₀ hc0 (GlobalTheory.Pst.supExt Bw.LL E')
  obtain ⟨r₁, hr₁⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem r₀ LL.1 hent
  have l₁ : Bw.LL.1 ≤ LL.1 := le_trans le_sup_left hL
  have l₂ : E'.1 ≤ LL.1 := le_trans le_sup_right hL
  refine ⟨LL, r₁, ⟨l₁, ?_⟩, ?_⟩
  · ext g a b
    exact hr₁ g a b
  obtain ⟨K, e, -, -, he, hKr, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  have hle : GK K ≤ GK Bw.Kw := by
    rw [← hKr]
    rintro _ ⟨g, rfl⟩
    rw [GlobalTheory.PlaceBridge.mem_GK_iff Bw.Kw hK]
    intro x
    rw [hφψ, AlgEquiv.commutes]
  have h : Bw.Kw.1 ≤ K.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
    exact IntermediateField.fixedField_le hle
  refine ⟨K, h, ?_⟩
  let ρK : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1) := (colRep r').comp e.symm.toMonoidHom
  have t1 : IsCr (GK K).subtype ρK := cr_transport e e.surjective he' (fun g x => by simp [ρK]) hcr
  have t2 := crys_of_isCr K E' ρK t1
  let _ : Algebra ↥E'.1 ↥LL.1 := (IntermediateField.inclusion l₂).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥E'.1 ↥LL.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := LL.2
  have : FiniteDimensional ↥E'.1 ↥LL.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  refine (GlobalTheory.Pst.isCrys_ext_iff _ (ρ := ρK) fun g => ⟨r' (e.symm g), fun _ => rfl, fun x => ?_⟩).2 t2
  have hg : ((Bw.e.symm (Subgroup.inclusion (GK_le h) g) : ↥(Dec (F := F) (placeJ j))) : G F Ω) = ψ (e.symm g) := by
    apply AlgEquiv.ext
    intro y
    apply j.injective
    have h1 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) y
    rw [hBj, MulEquiv.apply_symm_apply] at h1
    rw [← h1, ← hφψ, ← he', MulEquiv.apply_symm_apply]
    rfl
  have hM : (r₁ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin n) (Fin n) ↥LL.1) =
      (r' (e.symm g) : Matrix (Fin n) (Fin n) ↥E'.1).map (algebraMap ↥E'.1 ↥LL.1) := by
    ext a b
    rw [hr₁]
    refine Eq.trans ?_ (hr' (e.symm g) a b).symm
    rw [← hg]
    rfl
  rw [← hM]
  rfl
end
