module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle513
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle590
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle300
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle598
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle591
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle592
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.PureOm

theorem isPure_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (g : GA D S) (h : GA D T), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨U, U', hU, hU', hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hW.std S T om (GlobalTheory.Ker.isWeak_of_datum hW)
    hW.om_cont f₀ (base_theta hB)
  have hgen := GlobalTheory.T.weilRepresentation_placeByPlace_on_pureTensors D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hμ
  obtain ⟨hp0, hploc⟩ := GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hstab := GlobalTheory.T.localFactor_stable_unitaryGroupsAtPlace D ψ θ S T χS χT om sS sT ΛS ΛT hW (base_inf hB)
  have hgat := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1
  let Good : GA D S → GA D T → Prop := fun g h => ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ),
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => om (gAt S p g, gAt T p h) (x p)) (om (g, h) f)
  have om1 : ∀ u : WO S T → ℂ, om (1, 1) u = u := fun u => by
    have : om (1, 1) = 1 := map_one om
    rw [this]; rfl
  have omm : ∀ (g g' : GA D S) (h h' : GA D T) (u : WO S T → ℂ),
      om (g * g', h * h') u = om (g, h) (om (g', h') u) := fun g g' h h' u => by
    have : om (g * g', h * h') = om (g, h) * om (g', h') := map_mul om (g, h) (g', h')
    rw [this]; rfl
  have G1 : Good 1 1 := fun x f hx => by
    simpa only [gAt_one, om1] using hx
  have Gmul : ∀ g h g' h', Good g h → Good g' h' → Good (g * g') (h * h') := fun g h g' h' a b x f hx => by
    simpa only [gAt_mul, omm] using a _ _ (b x f hx)
  have Gloc : ∀ q g h, gAt S q g = g → gAt T q h = h → Good g h := fun q g h hg hh => by
    have e1 : ∀ p, p ≠ q → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact (hgat S q g).2.2 p hp
    have e2 : ∀ p, p ≠ q → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact (hgat T q h).2.2 p hp
    refine hgen g h ?_ ?_
    · refine (Set.finite_singleton q).subset fun p hp => ?_
      by_contra hpq
      exact hp (by rw [e1 p hpq, e2 p hpq, om1])
    · have := hploc q (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) (hstab q f₀ (base_isLocal hB q) _ _)
        (fun p hp => by simp only [gAt_inv, e1 p hp, e2 p hp, inv_one, om1])
      have e : om (gAt S q g⁻¹, gAt T q h⁻¹) f₀ = om (g⁻¹, h⁻¹) f₀ := by rw [gAt_inv, gAt_inv, hg, hh]
      simp only [e] at this
      exact this
  have Gfin : ∀ g h, (g ∈ U ∧ g ∈ GfC S ∧ ∀ p, gAt S p g ∈ U ∧ gAt S p g ∈ GfC S) →
      (h ∈ U' ∧ h ∈ GfC T ∧ ∀ p, gAt T p h ∈ U' ∧ gAt T p h ∈ GfC T) → Good g h := fun g h hg hh => by
    refine hgen g h ?_ ?_
    · refine Set.finite_empty.subset fun p hp => ?_
      exact hp (hfix _ (hg.2.2 p).1 (hg.2.2 p).2 _ (hh.2.2 p).1 (hh.2.2 p).2)
    · have e : (fun p => om (gAt S p g⁻¹, gAt T p h⁻¹) f₀) = fun _ => f₀ := funext fun p => by
        rw [gAt_inv, gAt_inv]
        exact hfix _ (inv_mem (hg.2.2 p).1) (inv_mem (hg.2.2 p).2) _ (inv_mem (hh.2.2 p).1) (inv_mem (hh.2.2 p).2)
      rw [e, hfix _ (inv_mem hg.1) (inv_mem hg.2.1) _ (inv_mem hh.1) (inv_mem hh.2.1)]
      exact hp0
  have GS : ∀ g, Good g 1 := fun g => by
    have hg : g ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D S U hU).2 ▸ Submonoid.mem_top g
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      rcases hg with ⟨q, hq⟩ | hg
      · exact Gloc q g 1 hq (gAt_one T q)
      · exact Gfin g 1 hg ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  have GT : ∀ h, Good 1 h := fun h => by
    have hh : h ∈ Submonoid.closure _ := (GlobalTheory.T.adelicUnitary_closure_local_components_open D T U' hU').2 ▸ Submonoid.mem_top h
    induction hh using Submonoid.closure_induction with
    | mem h hh =>
      rcases hh with ⟨q, hq⟩ | hh
      · exact Gloc q 1 h (gAt_one S q) hq
      · exact Gfin 1 h ⟨one_mem _, one_mem _, fun p => by rw [gAt_one]; exact ⟨one_mem _, one_mem _⟩⟩ hh
    | one => exact G1
    | mul a b _ _ ha hb => simpa only [mul_one] using Gmul _ _ _ _ ha hb
  intro x f hx g h
  have := Gmul _ _ _ _ (GS g) (GT h)
  rw [mul_one, one_mul] at this
  exact this x f hx

end GlobalTheory.PlaceTensor.PureOm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetIndCompare

variable {D : D7}

theorem frame_smul {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D) (Y : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • Y).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val := by
  have : (a • Y).map (toEAf D) = toEAf D a • Y.map (toEAf D) := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem frame_sub {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (Y Z : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((Y - Z).map (toEAf D))) β.val =
      HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val -
        HMul.hMul (HMul.hMul (β'⁻¹).val (Z.map (toEAf D))) β.val := by
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Matrix.mul_sub, Matrix.sub_mul]

theorem frame_incA {m n : ℕ} (y : Matrix (Fin m) (Fin n) D.host.E) :
    (y.map (incA D)).map (toEAf D) = y.map (eToEAf D) := by
  ext i j; rfl

theorem frame_mem_idS {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (EAf D)} {β' : GL (Fin m) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (I : Ideal (𝓞 D.host.E))
    {y : GlobalTheory.ChiGrid.homLat Λ Λ'} (hy : y ∈ (I • ⊤ : Submodule (𝓞 D.host.E) (GlobalTheory.ChiGrid.homLat Λ Λ'))) (i : Fin m)
    (j : Fin n) : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I,
      (t : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val ((y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D))) β.val i j := by
  have h1 : (y : Matrix (Fin m) (Fin n) D.host.E) ∈ I • GlobalTheory.ChiGrid.homLat Λ Λ' := by
    have := Submodule.mem_map_of_mem (f := (GlobalTheory.ChiGrid.homLat Λ Λ').subtype) hy
    rwa [Submodule.map_smul'', Submodule.map_subtype_top] at this
  have h2 : (y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D) ∈
      GlobalTheory.FunObj.HatFrame.genGrp D.host.F (I • GlobalTheory.ChiGrid.homLat Λ Λ') :=
    by
      unfold GlobalTheory.FunObj.HatFrame.genGrp
      apply AddSubgroup.subset_closure
      exact ⟨1, one_mem _, _, h1, by ext a b; rfl⟩
  exact GlobalTheory.FunObj.HatFrame.genGrp_le_frGrp hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) I h2 i j

theorem frame_smul_incA {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D)
    (y : Matrix (Fin m) (Fin n) D.host.E) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • y.map (incA D)).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (y.map (eToEAf D))) β.val := by
  rw [frame_smul, frame_incA]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quot_iff (I : Ideal (𝓞 E)) (y : E ⊗[F] Formalism.L2.Herm.Af F) (r : 𝓞 E) :
    (∃ h : y ∈ Formalism.L2.Herm.intAf F E, Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) ⟨y, h⟩ =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) (Formalism.L2.DIV.oToS F E r)) ↔
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - Formalism.L2.DIV.oToS F E r := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨h, _, Ideal.Quotient.eq.1 hq, rfl⟩
  · rintro ⟨h, t, ht, et⟩
    refine ⟨h, Ideal.Quotient.eq.2 ?_⟩
    have : (⟨y, h⟩ : Formalism.L2.Herm.intAf F E) - Formalism.L2.DIV.oToS F E r = t := Subtype.ext et.symm
    rw [this]; exact ht

theorem step_fwd {I : Ideal (𝓞 E)} {y N a s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hq : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a := by
  obtain ⟨t1, h1, e1⟩ := hq
  obtain ⟨t2, h2, e2⟩ := hv
  obtain ⟨t3, h3, e3⟩ := hs
  refine ⟨t1 - t2 + t3 * ⟨a, ha⟩, add_mem (sub_mem h1 h2) (Ideal.mul_mem_right _ _ h3), ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3]
  ring

theorem step_bwd {I : Ideal (𝓞 E)} {y N a a' s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hN : N ∈ Formalism.L2.Herm.intAf F E) (hsi : s ∈ Formalism.L2.Herm.intAf F E)
    (ht : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a')
    (hu : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a' - a)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N := by
  obtain ⟨t1, h1, e1⟩ := ht
  obtain ⟨t2, h2, e2⟩ := hu
  obtain ⟨t3, h3, e3⟩ := hv
  obtain ⟨t4, h4, e4⟩ := hs
  have hy : y = ((t1 + ⟨s, hsi⟩ * t2 + ⟨s, hsi⟩ * ⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [Subring.coe_add, Subring.coe_mul, e1, e2]
    ring
  refine ⟨hy ▸ Subtype.property _, t1 + ⟨s, hsi⟩ * t2 - t4 * ⟨a, ha⟩ + t3,
    add_mem (sub_mem (add_mem h1 (Ideal.mul_mem_left _ _ h2)) (Ideal.mul_mem_right _ _ h4)) h3, ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3, e4]
  ring

end Gen

theorem cmpS_mk (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.E) :
    Formalism.L2.DIV.cmpS D.host.F I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E r) := by
  unfold Formalism.L2.DIV.cmpS
  exact Ideal.quotientMap_mk



theorem mem_cosSet_iff {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)}
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) (r : Fin T.V.rank → Fin S.V.rank → 𝓞 D.host.E)
    (hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)))
    (x₀ : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (hx₀ : x₀ ∈ GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
    (hN : ∀ i j, ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) =
      HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val i j -
        (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j) : EAf D)) (x : WO S.V T.V) :
    (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ GlobalTheory.ChiGrid.cosSet e (GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩) := by
  have hAint : ∀ i j, (HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val :
      Matrix (Fin T.V.rank) (Fin S.V.rank) (EAf D)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.FunObj.HatFrame.frame_int hS hT hx₀

  have hfr : ∀ y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E,
      HMul.hMul (HMul.hMul (T.β⁻¹).val ((x - e • y.map (incA D)).map (toEAf D))) S.β.val =
        frMapO S.V T.V S.β T.β x - toEAf D e • HMul.hMul (HMul.hMul (T.β⁻¹).val (y.map (eToEAf D))) S.β.val := by
    intro y
    rw [frame_sub, frame_smul_incA]; rfl
  change _ ↔ IsHalf e x ∧ ∃ x₀' : GlobalTheory.ChiGrid.homLat S.Λ T.Λ, GlobalTheory.ChiGrid.Cos.mk I x₀' = GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩ ∧
    x - e • (x₀' : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈
      GlobalTheory.ChiGrid.hatMx (I • GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
  refine and_congr_right fun hx => ?_
  have hx' : ∀ i j, e * x i j = x i j := hx
  have hinf : ∀ (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) i j,
      infPart D ((x - e • y.map (incA D)) i j) = 0 := by
    intro y i j
    have h1 : (x - e • y.map (incA D)) i j = e * (x i j - y.map (incA D) i j) := by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, hx' i j]
    rw [h1, map_mul, he0, zero_mul]
  constructor
  · intro hc
    unfold InCosetOf at hc
    refine ⟨⟨x₀, hx₀⟩, rfl, ?_⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I]
    refine ⟨hinf x₀, fun i j => ?_⟩
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have hq := ((quot_iff I _ (r i j)).1 ((hc i j).imp fun _ h => h.trans (hcos i j))).2
    exact step_fwd (hAint i j) hq (hN i j) h1s
  · rintro ⟨y, hyc, hmem⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I] at hmem
    have hdiff := (Submodule.Quotient.eq _).1 hyc
    unfold InCosetOf
    intro i j
    have et := hmem.2 i j
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at et
    have hu := frame_mem_idS hS hT I hdiff i j
    rw [Submodule.coe_sub, Matrix.map_sub _ (map_sub (eToEAf D)), Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply] at hu
    have h := step_bwd (hAint i j) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)).2 he_int et hu (hN i j) h1s
    exact ((quot_iff I _ (r i j)).2 h).imp fun _ h => h.trans (hcos i j).symm

theorem cosetInd_eq_cosInd {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥)
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) :
    ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ I, GlobalTheory.Grid.cosetInd S T e I c = GlobalTheory.ChiGrid.cosInd e κ := by
  choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (c i j)
  obtain ⟨x₀, hx₀, hN⟩ := GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod S.Λ T.Λ S.β T.β hS hT I hI (fun i j => Formalism.L2.DIV.oToS D.host.F D.host.E (r i j))
  have hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)) := fun i j =>
    (congrArg (Formalism.L2.DIV.cmpS D.host.F I) (hr i j)).symm.trans (cmpS_mk I (r i j))
  refine ⟨GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩, funext fun x => ?_⟩
  have key := mem_cosSet_iff hS hT he0 he_int h1s c r hcos x₀ hx₀ hN x
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  classical
  rw [Set.indicator_apply]
  by_cases h : IsHalf e x ∧ InCosetOf S T I c x
  · rw [if_pos h, if_pos (key.1 h)]; rfl
  · rw [if_neg h, if_neg fun h' => h (key.2 h')]

theorem coset_eq_cos : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he c
  obtain ⟨he0, he_int, h1s⟩ := GlobalTheory.T.idempotentSum_infPart_integral_one_sub_mem e P d he
  refine cosetInd_eq_cosInd hS hT he0 ?_ he_int h1s c
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

end GlobalTheory.CosetIndCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomFieldDict

theorem det_X_isHomogeneous {σ : Type*} {a : ℕ} (f : Fin a → Fin a → σ) :
    (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)).det.IsHomogeneous a := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun e _ => ?_)
  have h1 : (∏ i, (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)) (e i) i).IsHomogeneous
      (∑ _i : Fin a, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X ℂ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  have h0 : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    have : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)) = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : ℂ) := by simp
    rw [this]; exact MvPolynomial.isHomogeneous_C _ _
  simpa using h0.mul h1

theorem minorPol_isHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    (GlobalTheory.NormSum.minorPol D T).IsHomogeneous (a * ∑ τ, n τ) := by
  unfold GlobalTheory.NormSum.minorPol
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset D.what₂.Tau)
    (fun τ => ∏ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, ((T τ j) : Fin a → Fin d) i, i') :
      MvPolynomial (GL3Theta.Idx D a d) ℂ)).det) (fun τ => ∑ _j : Fin (n τ), a) (fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => det_X_isHomogeneous _))
  convert h using 1
  simp [Finset.mul_sum, mul_comm]

theorem card_of_mem_support {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n)
    {α : TaylorLogMetric.Mono D a d} (hα : α ∈ (GlobalTheory.NormSum.minorPol D T).support) :
    Multiset.card (Finsupp.toMultiset α) = a * ∑ τ, n τ := by
  have h := minorPol_isHomogeneous T (MvPolynomial.mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem minorPol_coeff_isAlgebraic {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : GlobalTheory.NormSum.Tup D a d n)
    (α : GL3Theta.Idx D a d →₀ ℕ) : IsAlgebraic ℚ ((GlobalTheory.NormSum.minorPol D U).coeff α) := by
  have e : GlobalTheory.NormSum.minorPol D U = MvPolynomial.map (algebraMap ℚ ℂ) (∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (U τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℚ)).det) := by
    unfold GlobalTheory.NormSum.minorPol
    simp only [map_prod, RingHom.map_det]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
    congr 1
    ext1 i i'
    simp
  rw [e, MvPolynomial.coeff_map]
  exact isAlgebraic_algebraMap _

theorem apply_minorPol {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : GlobalTheory.NormSum.Tup D a d n)
    (l : MvPolynomial (GL3Theta.Idx D a d) ℂ →ₗ[ℂ] ℂ) (c p ζ : ℂ) (G : TaylorLogMetric.VC D a d → ℂ)
    (h : ∀ k : GL3Theta.Idx D a d →₀ ℕ, l (MvPolynomial.monomial k 1) =
      c * (p ^ (k.sum fun _ e => e) * (ζ * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G))) :
    l (GlobalTheory.NormSum.minorPol D U) = c * p ^ (a * ∑ τ, n τ) * (ζ * GL3Theta.applyAt0 D (GlobalTheory.NormSum.minorPol D U) G) := by
  conv_lhs => rw [(GlobalTheory.NormSum.minorPol D U).as_sum]

  rw [map_sum l, GL3Theta.applyAt0, Finset.mul_sum _ _ ζ, Finset.mul_sum _ _ (c * p ^ (a * ∑ τ, n τ))]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := card_of_mem_support U hα
  rw [Finsupp.card_toMultiset] at hk
  have e : (MvPolynomial.monomial α ((GlobalTheory.NormSum.minorPol D U).coeff α) : MvPolynomial (GL3Theta.Idx D a d) ℂ) =
      (GlobalTheory.NormSum.minorPol D U).coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hk' : (α.sum fun _ e => e) = a * ∑ τ, n τ := hk
  rw [e, map_smul, h, GlobalTheory.FockPos.applyAt0_monomial', hk', smul_eq_mul]
  ring

theorem lat_eq_colLat {D : D7} {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) :
    (r.Λ : Set (Fin V.rank → D.host.E)) = (colLat (1 : GL (Fin V.rank) D.host.E) : Set (Fin V.rank → D.host.E)) := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, h.2.1, lc_mem_colLat_one]
  simp only [Submodule.mem_one]

theorem lat_eq_inV {D : D7} {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) :
    (r.Λ : Set (Fin V.rank → D.host.E)) = GlobalTheory.MovedDict.inV 1 (StandardLatticesGL3.stdL D V.rank) := by
  ext y
  rw [SetLike.mem_coe, h.2.1]
  simp [GlobalTheory.MovedDict.inV, StandardLatticesGL3.stdL, Submodule.mem_pi, Submodule.mem_one]

end GlobalTheory.BottomFieldDict

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.integer_outside_prime_pow_dvd_maximal_ideal_pow : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w → ∀ (d : ℕ) (m : 𝓞 D.host.E),
  m ∉ w.asIdeal ^ (d + 1) → ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k], (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E)) := by
  first | exact @GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow | exact GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow | (intros; apply GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteLevelDatumVector_transforms_by_levelCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i P), ω (1, k) f = levChi (Wc D i) (R.βW i) (R.datWp i P) k • f := by
  first | exact @GlobalTheory.ZetaLaw.zeta_law | exact GlobalTheory.ZetaLaw.zeta_law | (intros; apply GlobalTheory.ZetaLaw.zeta_law <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  first | exact @GlobalTheory.EvenOnto.fock_sph_vac | exact GlobalTheory.EvenOnto.fock_sph_vac | (intros; apply GlobalTheory.EvenOnto.fock_sph_vac <;> assumption)
end
