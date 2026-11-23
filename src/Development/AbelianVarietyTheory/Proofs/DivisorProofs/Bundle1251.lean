module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatDarbouxTransfer

theorem finrank_AE (D : D7) : Module.Free (AF D.host.F) (AE D) ∧ Module.Finite (AF D.host.F) (AE D) ∧
    Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
  exact ⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by
    rw [Module.finrank_eq_card_basis bA, Fintype.card_fin, D.sp.cm.deg2]⟩

theorem finrank_pair (K : Type) [Field K] (κ : Type) [Fintype κ] :
    Module.finrank K ((κ → K) × (κ → K)) = 2 * Fintype.card κ := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  ring

theorem finrank_mat (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (m n : ℕ) :
    Module.finrank K (Matrix (Fin m) (Fin n) L) = m * n * Module.finrank K L := by
  show Module.finrank K (Fin m → Fin n → L) = _
  simp [Module.finrank_pi_fintype, mul_assoc]

theorem card_eq (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) :
    Fintype.card κ = T.rank * S.rank := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have h := e.finrank_eq
  have ha : Module.finrank (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) = T.rank * S.rank * 2 := by
    show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AE D) = _
    simp [Module.finrank_pi_fintype, hAE, mul_assoc]
  have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  have : T.rank * S.rank * 2 = 2 * Fintype.card κ := ha.symm.trans (h.trans hb)
  omega


theorem onto (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, e.symm p ∈ ratL T S := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have hκ := card_eq D S T κ e
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
    LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
  let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) := J1.prodMap J1
  let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  let L := (e.toLinearMap.restrictScalars D.host.F).comp I
  haveI : Nontrivial (AE D) := Module.nontrivial_of_finrank_pos (R := AF D.host.F) (by rw [hAE]; norm_num)
  have hJinj : Function.Injective J := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
    simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hLinj : Function.Injective L := by
    have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
    intro x x' h
    have := e.injective h
    exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
  have hle : LinearMap.range L ≤ LinearMap.range J := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
  have heq : LinearMap.range L = LinearMap.range J := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
    refine (finrank_mat D.host.F D.host.E T.rank S.rank).trans ((finrank_pair D.host.F κ).trans ?_).symm
    rw [hκ, D.sp.cm.deg2]
    ring
  intro p hp
  obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
  have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  have hx' : e (incM D.host.F x) = J (y, z) := hx
  show incM D.host.F x = e.symm (J (y, z))
  rw [← hx']
  exact (e.symm_apply_apply _).symm

end GlobalTheory.RatDarbouxTransfer

namespace GlobalTheory.RatDarbouxTransfer

open scoped Pointwise



theorem haar_fundDomain_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro D ψ _ S T JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  haveI hMT : IsModuleTopology (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  let ce : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃L[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : Formalism.IndefR.Datum.WO S T ≃ₜ+ (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : Formalism.IndefR.Datum.WO S T ≃ᵐ (κ → AF D.host.F) × (κ → AF D.host.F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratL T S, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, co.e.symm p ∈ ratL T S :=
    onto D S T κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : Formalism.IndefR.Datum.WO S T) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratL T S := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratL T S := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratL T S => co.e (t : Formalism.IndefR.Datum.WO S T)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) (k : ratL T S),
          (k : Formalism.IndefR.Datum.WO S T) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF D.host.F) × (κ → AF D.host.F)) + co.e w = co.e ((k : Formalism.IndefR.Datum.WO S T) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl

end GlobalTheory.RatDarbouxTransfer
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.CuspMult.CutFull

open GlobalTheory.CuspMult GlobalTheory.CuspMult.EqCut

theorem mem_killed_union {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
    (I I' : Set (MonoidAlgebra ℂ H)) (v : X) : v ∈ killed ρ (I ∪ I') ↔ v ∈ killed ρ I ∧ v ∈ killed ρ I' := by
  simp only [mem_killed, Set.mem_union, or_imp, forall_and]

theorem mem_partFull_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ) (T : MMap M) :
    T ∈ partFull θ M J χ SF a ↔ T ∈ Mult θ M J χ ∧ ∀ Q d R, Hecke₂ V J χ SF Q d R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = a Q d * T v x := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
    MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_partFull_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a : Pl D.host.E → List ℤ → ℂ), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ partFull θ M (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF a = GlobalTheory.CuspMult.allMaps θ M ⊓ GlobalTheory.CuspMult.killed (GlobalTheory.CuspMult.finRep M) (GlobalTheory.CuspMult.eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim ∪ {x | ∃ (Q : Pl D.host.E) (d : List ℤ) (B : Finset (GfC V)), Hecke₂ V (levS V β (withP L (LevelP.triv L.Pg L.r ℂ))) (levChi V β (withP L (LevelP.triv L.Pg L.r ℂ))) SF Q d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ∧ x = ∑ γ ∈ B, MonoidAlgebra.single γ 1 - MonoidAlgebra.single 1 (a Q d)}) := by
  intro D V S θ M β L G _ _ eG c P SF a hs hQ hlift
  have h0 := good_hecke_eq_killed θ M β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim hs hQ hlift
  have h1 : ∀ T : MMap M, T ∈ goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ↔
      T ∈ allMaps θ M ∧ T ∈ killed (finRep M) (eqSet V β L eG c P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
    intro T
    rw [← Submodule.mem_inf, ← h0, Submodule.mem_inf, mem_hPart]
    exact ⟨fun h => ⟨h, fun p => p.elim⟩, fun h => h.1⟩
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_killed_union, ← and_assoc, ← h1, mem_partFull_iff]
  refine and_congr_right fun hg => ?_
  rw [mem_killed]
  constructor
  · rintro ⟨-, hh⟩ x ⟨Q, d, B, hB, rfl⟩
    refine (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
    have := hh Q d _ hB v x
    rw [Finset.sum_map] at this
    simp only [one_mul]
    exact this
  · intro hk
    have hm := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hg.1
    refine ⟨(GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).2 ⟨hm.aut, hm.cusp, fun v k hkk x => ?_, hm.equiv, hm.cont⟩, ?_⟩
    · exact hasType_flag1 P (F := T v) (fun k hk h => hm.lev v k hk h) k hkk x
    · intro Q d R hR v x
      classical
      have hf : ∀ γ ∈ R, γ ∈ GfC V := by
        obtain ⟨e, f, ϖ, α, -, -, -, -, -, -, -, -, -, -, h⟩ := hR
        exact fun γ hγ => (h.1 γ hγ).1
      obtain ⟨B, rfl⟩ : ∃ B : Finset (GfC V), B.map ⟨Subtype.val, Subtype.val_injective⟩ = R :=
        ⟨R.subtype (· ∈ GfC V), Finset.subtype_map_of_mem hf⟩
      have := (alg_sum M B (fun γ => γ) (fun _ => 1) _ T).1 (hk _ ⟨Q, d, B, hR, rfl⟩) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.CutFull

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

theorem IsMultIP₂ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dite_eq_right hc, mul_zero]
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

theorem schurMult_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R h i σ _ _ _ T hT T' hT'
  obtain ⟨-, hr, hip⟩ := h i σ
  have hT1 : T ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT
  have hT2 : T' ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT'
  obtain ⟨x, rfl⟩ := hT1
  obtain ⟨y, rfl⟩ := hT2
  exact IsMultIP₂ (R.HW i σ) hip x y

end GlobalTheory.LiftLower

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower

namespace GlobalTheory.Proof.ConjugateTransposeMajorant

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem csum_eq_coord (S : CSD K) (f g : S.Forms) :
    S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) = star (fun a => S.basis.repr f a) ⬝ᵥ S.H *ᵥ fun a => S.basis.repr g a := by
  have hf : ∀ c, (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr f]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hg : ∀ c, (g : S.Cl → S.V) c = ∑ a, S.basis.repr g a • (S.basis a : S.Cl → S.V) c := by
    intro c
    conv_lhs => rw [← S.basis.sum_repr g]
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have e : ∀ c, S.pair ((f : S.Cl → S.V) c) ((g : S.Cl → S.V) c) =
      ∑ a, ∑ b, star (S.basis.repr f a) * (S.pair ((S.basis a : S.Cl → S.V) c) ((S.basis b : S.Cl → S.V) c) *
        S.basis.repr g b) := by
    intro c

    rw [hf c, hg c, map_sum S.pair, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  simp only [CSD.csum, CSD.H, e, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

omit [NumberField K] in
theorem map_conjTranspose_of_mem {m n : Type} (E : Matrix m n K) (hE : ∀ a k, E a k ∈ cmMax K) (σ : K →+* ℂ) :
    Eᴴ.map σ = (E.map σ)ᴴ := by
  ext i j
  exact hE j i σ

omit [NumberField K] [StarRing K] in
theorem map_mulVec' {m n : Type} [Fintype n] (E : Matrix m n K) (x : n → K) (σ : K →+* ℂ) :
    (fun a => σ ((E *ᵥ x) a)) = E.map σ *ᵥ fun k => σ (x k) := by
  funext a

  simp [Matrix.mulVec, dotProduct, map_sum]

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms)

theorem repr_toF (x : Fin (B.dZ ℓ Z) → K) : (fun a => B.S.basis.repr (B.toF ℓ Z x) a) = B.fE ℓ Z *ᵥ x := by
  have : B.S.basis.equivFun (B.toF ℓ Z x) = B.fE ℓ Z *ᵥ x := by
    rw [BlockDat.fE, ← Matrix.mulVec_mulVec]
    exact B.S.basis.equivFun.apply_symm_apply _
  rw [← this]
  rfl

theorem HZ_eq : B.HZ ℓ Z = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.fE ℓ Z)ᴴ * B.S.H * B.fE ℓ Z) := by
  have : B.HV ℓ = ((Nat.card ℓ.P : ℕ) : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [BlockDat.HZ, this, BlockDat.fE, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem csumAt_toF (σ : K →+* ℂ) (x : Fin (B.dZ ℓ Z) → K) (u : B.S.Forms) :
    csumAt B.S σ (B.toF ℓ Z x) u = star (fun k => σ (x k)) ⬝ᵥ ((B.fE ℓ Z).map σ)ᴴ *ᵥ
      (B.S.H.map σ *ᵥ fun a => σ (B.S.basis.repr u a)) := by
  have h : (fun a => σ (B.S.basis.repr (B.toF ℓ Z x) a)) = (B.fE ℓ Z).map σ *ᵥ fun k => σ (x k) := by
    rw [← map_mulVec', ← repr_toF]
  unfold csumAt
  rw [h, Matrix.star_mulVec, Matrix.dotProduct_mulVec _ (((B.fE ℓ Z).map σ)ᴴ)]

end

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem majAt_eq_csumAt : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms), IsRatHerm (cmMax K) (B.HZ ℓ Z) (B.XQ ℓ Z) → (∀ a k, B.fE ℓ Z a k ∈ cmMax K) → (∀ (v : InfinitePlace K) x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ * csumAt B.S v.embedding (B.toF ℓ Z x) (B.toF ℓ Z y)) ∧ ∀ u : B.S.Forms, (∀ x, B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (u : B.S.Cl → B.S.V) = 0) → ∀ (σ : K →+* ℂ) x, csumAt B.S σ (B.toF ℓ Z x) u = 0 := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z hH hE
  refine ⟨fun v x y => ?_, fun u hu σ x => ?_⟩
  · have h1 : ∀ w : Fin (B.dZ ℓ Z) → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K _) v w = fun k => v.embedding (w k) := by
      intro w; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    have h2 : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y =
        star ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (x k)) ⬝ᵥ ((B.XQ ℓ Z v)⁻¹ *ᵥ fun k => v.embedding (y k)) := by
      simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1]
      rfl
    have h3 : (fun a => v.embedding (B.S.basis.repr (B.toF ℓ Z y) a)) =
        (B.fE ℓ Z).map v.embedding *ᵥ fun k => v.embedding (y k) := by
      rw [← map_mulVec', ← repr_toF]
    have h4 : (B.HZ ℓ Z).map v.embedding = ((Nat.card ℓ.P : ℕ) : ℂ)⁻¹ •
        (((B.fE ℓ Z).map v.embedding)ᴴ * B.S.H.map v.embedding * (B.fE ℓ Z).map v.embedding) := by
      rw [← map_conjTranspose_of_mem _ hE, ← Matrix.map_mul, ← Matrix.map_mul, HZ_eq]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
    rw [h2, csumAt_toF, h3, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (hH.2 v).2, h4,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  · have h0 : (B.fE ℓ Z)ᴴ *ᵥ (B.S.H *ᵥ fun a => B.S.basis.repr u a) = 0 := by
      funext k
      have := hu (Pi.single k 1)
      rw [csum_eq_coord, repr_toF, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
      have e : star (Pi.single k (1 : K) : Fin (B.dZ ℓ Z) → K) = Pi.single k 1 := by
        rw [Pi.star_single, star_one]
      rw [e, single_dotProduct, one_mul] at this
      exact this
    rw [csumAt_toF, ← map_mulVec', ← map_conjTranspose_of_mem _ hE, ← map_mulVec', h0]
    simp

end GlobalTheory.Proof.ConjugateTransposeMajorant

end
end

section

noncomputable section

namespace GlobalTheory.LowTypeRestriction

theorem determinedByLowTypes : DeterminedByLowTypes := GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes

theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end
end
