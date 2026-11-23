module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle232
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle156
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x → Reads θ V W hr X bas idx f' φ' x → (∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x) ∧ (f = f' → φ = φ') ∧ (IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → φ = φ' → f = f') := by
  first | exact @GlobalTheory.AdTh.reads_linear_injective | exact GlobalTheory.AdTh.reads_linear_injective | (intros; apply GlobalTheory.AdTh.reads_linear_injective <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.orbital_term_point_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  first | (exact @GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (exact GlobalTheory.LKMid.Pair.term_one_eq_pointSum) | (intros; apply GlobalTheory.LKMid.Pair.term_one_eq_pointSum <;> assumption)
end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.FactorDepth

theorem nuFac_eq_nuFacC_and_nuProd_eq_nuP :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
      ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
        (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
        (∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k) ∧
          ∀ cx : Lt1 Dw → ℕ, nuProd p y cx = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X
  have hc : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p) (f : Lt1 Dw) (k : ℕ),
      nuFacC Ch' X' f k = nuFacC Ch X f k := fun Ch' X' f k =>
    (GlobalTheory.T.detFactorDepthInChart_chart_independent E H Dw l Xo c p T io y Ch' Ch X' f k).trans
      (GlobalTheory.T.detFactorDepthInChart_independent_closedField E H Dw l Xo c p T io y Ch X' X f k)
  have h1 : ∀ (f : Lt1 Dw) (k : ℕ), nuFac p y f k = nuFacC Ch X f k := fun f k =>
    le_antisymm (nuFac_le Ch X f k) (le_nuFac fun Ch' X' => (hc Ch' X' f k).ge)
  refine ⟨h1, fun cx => ?_⟩
  have h2 : ∀ (Ch' : IntegralChartA3 Xo c T io y) (X' : ValExt T p), nuProdC Ch' X' cx = nuP p y cx := by
    intro Ch' X'
    rw [GlobalTheory.T.detProductDepthInChart_eq_sum_factorDepths E H Dw l Xo c p T io y Ch' X' cx, nuP]
    exact Finset.sum_congr rfl fun f _ => (hc Ch' X' f (cx f)).trans (h1 f (cx f)).symm
  exact le_antisymm (iInf_le_of_le Ch (iInf_le_of_le X (h2 Ch X).le))
    (le_iInf₂ fun Ch' X' => (h2 Ch' X').ge)

end GlobalTheory.FactorDepth
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCompU

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIrreducible_comp_of_surjective {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.ConjAtPlace.main E hU w).1
    have : Continuous fun g : GLw n w =>
        cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem isOpen_isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) := by
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [KL, Subgroup.coe_subgroupOf]
  exact ⟨hK.1.preimage continuous_subtype_val,
    (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2⟩

theorem exists_equiv (hU : Unr E) (n : ℕ) (w : Pl E) :
    ∃ e : locU n w ≃ₜ* UL n w, ∀ x : locU n w, ((e x : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  by_cases hs : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hs
    have h : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [h]; exact Subgroup.mem_top _
    refine ⟨{ toFun := fun x => ⟨e x, hm _⟩
              invFun := fun g => e.symm g.1
              left_inv := fun x => by simp
              right_inv := fun g => Subtype.ext (by simp)
              map_mul' := fun x y => Subtype.ext (by simp)
              continuous_toFun := e.continuous.subtype_mk _
              continuous_invFun := e.symm.continuous.comp continuous_subtype_val }, fun x => he x⟩
  · obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) (hns hs).1 hv
    have h : UL n w = UJ (cj w) 1 := if_neg hs
    rw [h]
    exact ⟨e, he⟩

theorem exists_unique_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E,
    (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧
      ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧
    ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ hU n _ π hπ w
  obtain ⟨e, he⟩ := exists_equiv hU n w
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_KL hU n w
  have hesurj : Function.Surjective (e.toMulEquiv.symm.toMonoidHom) := e.symm.surjective
  refine ⟨?_, ?_⟩
  · obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n ⟨π, hπ⟩ w
    let ρ : Representation ℂ (UL n w) σ₀.V := σ₀.ρ.comp e.toMulEquiv.symm.toMonoidHom
    have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
    let σ : SmIrr (UL n w) :=
      { V := σ₀.V
        ρ := ρ
        smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
        irred := isIrreducible_comp_of_surjective σ₀.ρ _ hesurj σ₀.irred }
    refine ⟨σ, ⟨e.toMulEquiv.toMonoidHom, fun x => he x, σ.irred, f, hf0, hfm, fun x v => ?_⟩, fun U hUo => ?_⟩
    · change f (σ₀.ρ (e.symm (e x)) v) = _
      rw [e.symm_apply_apply]
      exact hf x v
    · let K' : Subgroup (locU n w) := (U ⊓ KL n w).comap e.toMulEquiv.toMonoidHom
      have hK'o : IsOpen (K' : Set (locU n w)) := by
        change IsOpen (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact (hUo.inter hKo).preimage e.continuous
      have hK'c : IsCompact (K' : Set (locU n w)) := by
        change IsCompact (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact e.toHomeomorph.isCompact_preimage.2 (hKc.inter_left (U.isClosed_of_isOpen hUo))
      haveI := hadm.2 K' hK'o hK'c
      have hle : fixed σ.ρ U ≤ fixed σ₀.ρ K' := by
        intro v hv k
        have h1 := hv ⟨e k, k.2.1⟩
        simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
        change σ₀.ρ (e.symm (e k)) v = v at h1
        rwa [e.symm_apply_apply] at h1
      exact Submodule.finiteDimensional_of_le hle
  · rintro σ σ' ⟨p, hp, -, f, hf0, hfm, hf⟩ ⟨p', hp', -, f', hf0', hfm', hf'⟩
    have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
    have hpe' : ∀ x, p' x = e x := fun x => Subtype.ext ((hp' x).trans (he x).symm)
    have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
    have hps' : Function.Surjective p' := fun g => ⟨e.symm g, by rw [hpe', e.apply_symm_apply]⟩
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    let F' : Representation.IntertwiningMap (σ'.ρ.comp p') (π'.rep.comp (locU n w).subtype) :=
      ⟨f'.codRestrict π hfm', fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hF0' : F' ≠ 0 := fun h =>
      hf0' (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ'.V π'.rep (locU n w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p') π'.isIrreducible_rep
      (isIrreducible_comp_of_surjective σ.ρ p hps σ.irred)
      (isIrreducible_comp_of_surjective σ'.ρ p' hps' σ'.irred)
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0
    obtain ⟨T⟩ := h2 F' hF0'
    refine ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩
    have h1 : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have h1' : p' (e.symm g) = g := by rw [hpe', e.apply_symm_apply]
    have := T.isIntertwining' (e.symm g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h1'] at this
    exact this

end GlobalTheory.BCT.LocCompU
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.CptTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twCent_commute (hE : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) {g : GLw n w}
    (hg : g ∈ twCent (thL n w) y) : Commute g (nrmL n w y) := by
  have hinv : ∀ x, thL n w (thL n w x) = x := (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE n w).2.1
  have hg' : g * y = y * thL n w g := hg
  unfold nrmL
  split_ifs with hs
  · have ht : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    rw [ht] at hg'
    exact hg'
  · have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
    rw [ht] at hg' hinv
    show g * (y * thetaGL n (cj w) y) = (y * thetaGL n (cj w) y) * g
    calc g * (y * thetaGL n (cj w) y) = (g * y) * thetaGL n (cj w) y := by rw [mul_assoc]
      _ = y * (thetaGL n (cj w) g * thetaGL n (cj w) y) := by rw [hg', mul_assoc]
      _ = y * thetaGL n (cj w) (g * y) := by rw [map_mul]
      _ = y * thetaGL n (cj w) (y * thetaGL n (cj w) g) := by rw [hg']
      _ = (y * thetaGL n (cj w) y) * g := by rw [map_mul, hinv, mul_assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w),
    (nrmL n w y).val.charpoly.Separable →
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  intro E _ _ _ hE n w y hs
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨twCent_commute hE n w y ht, htc⟩

end GlobalTheory.CptTorus
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FinFib

section Generic

variable {G : Type} [Group G]

def twR (θ : G →* G) (x y : G) : Prop := ∃ g, y = g⁻¹ * x * θ g

theorem twR_equiv (θ : G →* G) : Equivalence (twR θ) := by
  constructor
  · intro x
    exact ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk (twR θ) x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ twR θ x y :=
  ⟨fun h => (twR_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locEl_eventually_mem (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  filter_upwards [UnitStable.eventually_mem_KGL δ, UnitStable.eventually_mem_KGL (δ * thE E n δ)] with w h1 h2
  unfold locEl
  split_ifs
  · exact h2
  · exact h1

end GlobalTheory.BCT.FinFib

namespace GlobalTheory.BCT.FinFib

end GlobalTheory.BCT.FinFib
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowPartStable

variable {D : D7}

theorem sphericalOperator_commute_levelFiniteGroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (P : Pl D.host.E) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) {d : List ℤ} {B : Finset (GA D V)}
    (hS : GlobalTheory.Hk3.SphOp V P d B) (g0 : G0 L.Pg L.r) (Φ : GA D V → ℂ) (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    actG0 V β L g0 (heckeLin V B Φ) = heckeLin V B (actG0 V β L g0 Φ) := by
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  unfold actG0
  split_ifs with hex
  · have hl := hex.choose_spec
    generalize hex.choose = κ at hl ⊢
    have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
    have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
      (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
    rw [e1, LinearMap.map_smul]
    funext h
    rw [GlobalTheory.LevOp.heckeLin_translate hP hJ' hS hΦ hk₁ s₁ s₂]
    rfl
  · rw [LinearMap.map_zero]

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) (v : M.Vec) (k : GA D V) (hk : k ∈ J) (g : GA D V) : U v (g * k) = χ k * U v g := by
  induction hU using Submodule.span_induction with
  | mem U hU => exact hU.lev v k hk g
  | zero => simp
  | add U U' _ _ h h' => simp [h, h', mul_add]
  | smul a U _ h => simp [h, mul_left_comm]

theorem map_gE_le : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ SF, IsSF R SF → ∀ c g, (EEc R SF c).map (R.gE g) ≤ EEc R SF c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hC SF hSF c g
  rintro _ ⟨x, hx, rfl⟩
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have h : R.HE.e y ∈ R.EEat R.triv := hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y
    exact goodPart_le _ _ _ _ _ h
  have hx' := ((mem_partFull R.θ (R.MY 0) _ _ SF _ _).1 hx).2
  refine (mem_partFull R.θ (R.MY 0) _ _ SF _ _).2 ⟨hmem _, fun P d B hB v => ?_⟩
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hO : OffS D SF P := by
    obtain ⟨e, f, ϖ, α, h, -⟩ := hB
    exact h
  have hG : Good R A.μ0 P := (hoff SF hSF P).1 hO
  obtain ⟨n, hn⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hN : (((D.host.g 0 * D.host.g 1) ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_pow]
    exact fun h => (hgood _ P hG).1 (P.isPrime.mem_of_pow_mem n h)
  have hPP : ∀ PP, PP ∈ (R.dat0 R.triv).Pg ∨ PP ∈ (R.dat0 R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact hG PP (Or.inl hPP)
    · exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP
  have hS := ((h2 SF d B).1 hB).2
  have hfix : ∀ y, ∀ k ∈ GlobalTheory.Hk3.hyp (Yc D 0) P, ∀ h, R.HE.e y v (h * k) = R.HE.e y v h := by
    intro y k hk h
    rw [mult_lev _ _ _ _ (hmem y) v k (h1 k hk).1 h, (h1 k hk).2, one_mul]
  have hact : R.HE.e (R.gE g x) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e x v) := by
    rw [hC.models.gE g x]; rfl
  have hcomm := sphericalOperator_commute_levelFiniteGroup (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP hS (R.eG g) (R.HE.e x v) (hfix x)
  rw [hx' P d B hB v] at hcomm
  rw [hact]
  exact hcomm.symm.trans ((actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)).map_smul _ _)

end GlobalTheory.RowPartStable

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) δ ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | exact GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum | (intros; apply GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum <;> assumption)
end
