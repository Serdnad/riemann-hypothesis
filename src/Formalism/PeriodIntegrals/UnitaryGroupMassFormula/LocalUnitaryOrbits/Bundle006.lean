module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CfCoe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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

@[expose] public section

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_basO (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    ∃ (m : ℕ) (b : Fin m → Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      (∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i) ∧
      ⊤ ≤ Submodule.span (Fv F v) (Set.range b) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E)) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (basLat_fg v L hLat.toIsLattice)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fin n → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  refine ⟨_, b0, hli, hmem, ?_⟩
  rw [← basSpan_top v L hLat, Submodule.span_le]
  intro x hx
  obtain ⟨c, rfl⟩ := (hmem x).1 hx
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem latBasO_holds
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : ℕ) (Y : TupV (E := E) v n a) : LatBasO σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, -, -⟩
  obtain ⟨L, hLat, rfl⟩ := hFull
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem lamT_open (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) (hG : GoodY σ J ψ v Λ a Y) :
    IsOpen (LamT v Λ a) := by
  obtain ⟨b, hb, hmem⟩ := hB hG
  have hCM := hG.1.1
  have hfr : Module.finrank F E = 2 := hCM.2.2.1
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hfr]; norm_num)
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hV : Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Module.finrank_baseChange, hfr, mul_comm]
  have : FiniteDimensional (Fv F v) (Fin n → Fv F v ⊗[F] E) := inferInstance
  let bb := basisOfLinearIndependentOfCardEqFinrank' b hb (by rw [Fintype.card_fin, hV])
  have hbb : ∀ i, bb i = b i := fun i => by simp [bb]
  have e : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      bb.equivFun.symm '' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      refine ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb]
    · rintro ⟨c, hc, rfl⟩
      refine (hmem _).2 ⟨fun i => ⟨c i, hc i (Set.mem_univ i)⟩, ?_⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hbb]
  have hc : Continuous bb.equivFun := IsModuleTopology.continuous_of_linearMap bb.equivFun.toLinearMap
  have hL : IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [e, LinearEquiv.image_eq_preimage_symm, LinearEquiv.symm_symm]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage hc
  have : LamT v Λ a = Set.univ.pi (fun _ => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => hL

theorem measU_of_bas (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasO σ J ψ v Λ a Y) :
    MeasU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := lamT_open σ J ψ v Λ a Y hB hG
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

theorem countU_of_bas' (a : ℕ) (Y : TupV (E := E) v n a)
    (hB : LatBasO σ J ψ v Λ a Y) (hQ : ResIdx v) (hR : RedU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y :=
  countU_of σ J ψ v Λ a Y (measU_of_bas σ J ψ v Λ a Y hB)
    (idxU_of σ J ψ v Λ a Y (idxV_of σ J ψ v Λ a Y hB hQ)) (clsU_of σ J ψ v Λ a Y hR)

end PI.OmLocU
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem phi_surj (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    Function.Surjective (phi σ J v Λ hSD he π a) := by
  intro M
  choose c hc using fun i p => hπ.1 (M i p)
  have hX : (fun i => ∑ p, (c i p : Fv F v ⊗[F] E) • e p) ∈ lamA v Λ a := fun i =>
    (he _).2 ⟨fun p => (c i p : Fv F v ⊗[F] E), fun p => (c i p).2, rfl⟩
  refine ⟨⟨_, hX⟩, ?_⟩
  funext i p
  rw [phi_apply]
  have h : cf σ J v Λ hSD he ⟨_, hX⟩ i p = c i p := by
    apply Subtype.ext
    rw [cf_coe]
    exact coord_eq σ J v e he1 (fun q => (c i q : Fv F v ⊗[F] E)) p
  rw [h, hc]

theorem phi_ker (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
    (he1 : gramR (Fv F v) σ J e = 1) {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K}
    {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π) (a : ℕ) :
    (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) = (phi σ J v Λ hSD he π a).ker := by
  ext X
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨Z, hZ, hZX⟩
    funext i p
    rw [phi_apply, Pi.zero_apply, Pi.zero_apply]
    apply (hπ.2.1 _).2
    rw [cf_coe, ← hZX]
    refine ⟨hR (Fv F v) σ J (e p) (Z i), (hSD _).1 (hZ i) _ (bas_mem v Λ he p), ?_⟩
    show hR (Fv F v) σ J (e p) (sc (E := E) v ϖ • Z i) = _
    rw [Orb.hR_smul_right]
  · intro h0
    have hP : ∀ i p, ∃ d ∈ OEv (E := E) v,
        hR (Fv F v) σ J (e p) ((X : TupV (E := E) v n a) i) = sc (E := E) v ϖ * d := by
      intro i p
      have := (hπ.2.1 (cf σ J v Λ hSD he X i p)).1 (by
        have h1 := congrFun (congrFun h0 i) p
        rw [phi_apply] at h1
        exact h1)
      exact this
    choose d hd hde using hP
    have hZ : (fun i => ∑ p, d i p • e p) ∈ lamA v Λ a := fun i => (he _).2 ⟨d i, hd i, rfl⟩
    refine ⟨_, hZ, ?_⟩
    funext i
    rw [DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, expand σ J v Λ he he1 (memA v Λ X i), Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hde, smul_smul]

theorem gram_coord (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1) {a : ℕ}
    (X : lamA v Λ a) (i j : Fin a) :
    gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j = ∑ p, sigR (Fv F v) σ (cf σ J v Λ hSD he X i p : Fv F v ⊗[F] E) *
      (cf σ J v Λ hSD he X j p : Fv F v ⊗[F] E) := by
  show hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) ((X : TupV (E := E) v n a) j) = _
  conv_lhs => rw [expand σ J v Λ he he1 (memA v Λ X j)]
  rw [Orb.hR_sum_right σ J v]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [cf_coe, cf_coe, Orb.hR_conj σ J v hcm hJ, mul_comm]

end PI.OmLocU.Red
end
end
