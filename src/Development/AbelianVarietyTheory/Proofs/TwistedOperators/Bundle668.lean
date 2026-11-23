module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle661
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle366
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle563
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle473
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle442
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle636
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle590
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle608
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle657
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle663
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle345
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CosShift

variable {D : D7} {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
  {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)}

theorem isHalf_sub' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x - y) := fun i j => by
  simp only [Matrix.sub_apply, mul_sub, hx i j, hy i j]

theorem isHalf_add' {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem map_smul_sub (e : AE D) (a b : homLat Λ Λ') : e • ((a - b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  rw [Submodule.coe_sub, Matrix.map_sub _ (incA D).map_sub, smul_sub]

theorem map_smul_add (e : AE D) (a b : homLat Λ Λ') : e • ((a + b : homLat Λ Λ') : Matrix (Fin m) (Fin n) D.host.E).map (incA D) =
    e • (a : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (b : Matrix (Fin m) (Fin n) D.host.E).map (incA D) := by
  ext i j
  simp only [Submodule.coe_add, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    (incA D).map_add, smul_add]

theorem mk_sub' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a - b) = (Submodule.Quotient.mk a - Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_sub _

theorem mk_add' (a b : homLat Λ Λ') : Cos.mk 𝔪 (a + b) = (Submodule.Quotient.mk a + Submodule.Quotient.mk b :
    homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) :=
  Submodule.Quotient.mk_add _

theorem mem_cosSet_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₀ x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (t : Mx D m n) :
    t + z ∈ cosSet e (Cos.mk 𝔪 x₀) ↔ t ∈ cosSet e (Cos.mk 𝔪 (x₀ - x₁)) := by
  constructor
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨?_, y - x₁, ?_, ?_⟩
    · have := isHalf_sub' ht hz
      rwa [add_sub_cancel_right] at this
    · rw [mk_sub', mk_sub']
      exact congrArg (· - _) hy
    · rw [map_smul_sub]
      have h2 := sub_mem hm hx₁
      have e2 : t + z - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) -
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2
  · rintro ⟨ht, y, hy, hm⟩
    refine ⟨isHalf_add' ht hz, y + x₁, ?_, ?_⟩
    · rw [mk_add']
      rw [mk_sub'] at hy
      have hy' : (Submodule.Quotient.mk y : homLat Λ Λ' ⧸ (𝔪 • ⊤ : Submodule (𝓞 D.host.E) (homLat Λ Λ'))) =
          Submodule.Quotient.mk x₀ - Submodule.Quotient.mk x₁ := hy
      rw [hy', sub_add_cancel]
      rfl
    · rw [map_smul_add]
      have h2 := add_mem hm hx₁
      have e2 : t - e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) +
          (z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) =
          t + z - (e • (y : Matrix (Fin m) (Fin n) D.host.E).map (incA D) + e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D)) := by
        abel
      rwa [e2] at h2

theorem cosInd_add {e : AE D} {z : Mx D m n} (hz : IsHalf e z) (x₁ : homLat Λ Λ')
    (hx₁ : z - e • (x₁ : Matrix (Fin m) (Fin n) D.host.E).map (incA D) ∈ hatMx (𝔪 • homLat Λ Λ')) (κ : Cos Λ Λ' 𝔪) :
    ∃ κ' : Cos Λ Λ' 𝔪, (fun t => cosInd e κ (t + z)) = cosInd e κ' := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, Cos.mk 𝔪 x₀ = κ := Submodule.Quotient.mk_surjective _ κ
  refine ⟨Cos.mk 𝔪 (x₀ - x₁), funext fun t => ?_⟩
  have key := mem_cosSet_add hz x₀ x₁ hx₁ t
  rw [hx₀] at key
  show Set.indicator (cosSet e κ) 1 (t + z) = Set.indicator (cosSet e (Cos.mk 𝔪 (x₀ - x₁))) 1 t
  classical
  simp only [Set.indicator_apply, key, Pi.one_apply]

end GlobalTheory.CosShift

private theorem GlobalTheory.CosShift.selfDual_full {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem GlobalTheory.CosShift.mem_hatMx_of_latO {D : D7} (hq : OffQ D) {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}
    (hL : L.Is μ₀) (G : GridData L sc) {i : ℕ} (hi : i < D.R.m) {e : AE D} (he : IsIdemSum e G.pl.W0)
    {z : WO (G.pS (.chi i 0)) (G.pT (.chi i 0))} (hz : IsHalf e z)
    (hm : z ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) :
    z ∈ hatMx (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := by
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  obtain ⟨βS, hβS⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latS (.chi i 0)) (GlobalTheory.CosShift.selfDual_full _ _ hSD.1)
  obtain ⟨βT, hβT⟩ := Formalism.L2.DIV.frame_exists_alt D.host.F D.host.E _ (G.latT (.chi i 0)) (GlobalTheory.CosShift.selfDual_full _ _ hSD.2)
  exact GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hz fun w hw a b =>
    GlobalTheory.RowLatChi.int_of_mem_latO hSD.1 hβS hβT w (GlobalTheory.DepthFix.aa_int hL hq G hw) hm a b



open GlobalTheory.CosShift in
theorem GlobalTheory.CosShift.epart : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → (∀ κ, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e (latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd e κ) (W.cosVec i κ)) → ∀ w ∈ Ann W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (depLat G (.chi i 0)), w.map (infPart D) = 0 → ∀ κ, ∃ κ', heisO W.ψ (G.pS (.chi i 0)) (G.pT (.chi i 0)) (e • w) (W.cosVec i κ) = W.cosVec i κ' := by
  intro D hq T L μ₀ hL sc G W M hM i hi e he hθ w hw hwinf κ
  obtain ⟨⟨T₀, hT₀⟩, -⟩ := hθ κ
  have hv : ∀ κ, W.cosVec i κ = T₀ (cosInd e κ) := fun κ => (hθ κ).2 T₀ hT₀
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hz : IsHalf e (e • w) := fun a b => by
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)),
      e • w - e • (x₁ : Matrix _ _ D.host.E).map (incA D) ∈
        hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) :=
    (by
      apply GlobalTheory.T.exists_rational_hom_approx_half_mod_ideal (G.pl.modul_ne_bot sc)
      · with_unfolding_all exact selfDual_full (G.pS (.chi i 0)) (G.latS (.chi i 0)) hSD.1
      · with_unfolding_all exact selfDual_full (G.pT (.chi i 0)) (G.latT (.chi i 0)) hSD.2
      · exact he
      · exact hz
      · exact mem_hatMx_of_latO hq hL G hi he hz (GlobalTheory.T.commutantPart_chosenPlaces_mem_completedLattice hL G W.ψ W.ψ_std i hi e he w hw hwinf))
  obtain ⟨κ', hκ'⟩ := cosInd_add hz x₁ hx₁ κ
  refine ⟨κ', ?_⟩
  rw [hv κ, hv κ', ← hκ']
  exact (hT₀.trans (cosInd e κ) (GlobalTheory.GridWeil.isSBHalf_cosInd hSD.1 hSD.2 (G.pl.modul_ne_bot sc) hee
    (GlobalTheory.PlaceDatum.infPart_idemSum he) κ) (e • w) hz).symm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt resG_compl suppAt_resG isDetAt_detAt resG_one resG_mul actO_actO isHalf_actO)

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem omega_conj_vac_low: ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ Tm : (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLatO S (.top t j)) 1 (S.Z.vac (.top t j)) Tm →
      W.om (.top t j) (1, (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) (S.Z.vac (.top t j)) =
        (∏ w : locPl G t, (((locGrid G t w).mu (j + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ)) •
          Tm fun x => halfInd e (stdLatO S (.top t j)) (actO _ _ 1⁻¹ (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))⁻¹ x) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he Tm hTm
  change W.om (.top t j) (1, conjPt S j k) (S.Z.vac (.top t j)) = _ • Tm fun x => halfInd e (stdLatO S (.top t j))
    (actO _ _ 1⁻¹ (conjPt S j k)⁻¹ x)
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have he2 : e * e = e := ho.idem
  have hc : e * cA D e = 0 := he.2
  obtain ⟨ε, hε, halg⟩ := GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum he
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hsplit : (((1 : GA D (G.V (.top j))), conjPt S j k) : GA D (G.V (.top j)) × GA D (G.V (.top (j + 1)))) =
      (1, resG _ ε (conjPt S j k)) * (1, resG _ (1 - ε) (conjPt S j k)) := by
    rw [Prod.mk_mul_mk, one_mul, resG_compl _ hε]
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hS := S.N.selfDual (X := .top j) (by show j ≤ D.R.m; omega)
  have hT := S.N.selfDual (X := .top (j + 1)) (by show j + 1 ≤ D.R.m; omega)
  have hlaw := GlobalTheory.SplitLinear.law_orth hW hS hT ho hc hv.2.theta hv.2.lat one_ne_zero hTm
    (GlobalTheory.SplitLinear.suppAt_one e _) (suppAt_resG _ hε (conjPt S j k) halg.symm) (isDetAt_detAt he2 _ 1)
    (isDetAt_detAt he2 _ (resG _ ε (conjPt S j k)))
  have hvac : Tm (halfInd e (stdLatO S (.top t j))) = S.Z.vac (.top t j) := by
    have := hTm.vac; rwa [one_smul] at this
  rw [hsplit, map_mul, Module.End.mul_apply, GlobalTheory.T.truncatedConjugate_fixes_standardVacuum_topPair S hL ht j hj k hk e he ε hε halg]
  conv_lhs => rw [← hvac]
  refine (hlaw (halfInd e (stdLatO S (.top t j))) (isSBHalf_halfInd e _)).trans ?_
  congr 1
  · rw [detAt_one' he2, detAt_resG_eq he2 hc hε halg, GlobalTheory.T.detIdele_conjugatedTopPoint_eq_prod_local S ht j hj k e he]
    unfold GlobalTheory.SplitLinear.fac
    simp only [splitFacO, map_one, inv_one, one_mul]
    rw [GlobalTheory.T.topPairSourceChar_prod_localIdeles G hL j hj]
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have hm : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1
        (∏ w : locPl G t, GlobalTheory.LFun.locIdele D.host.F w.1 (gdet (kapAt S t j hj k w))) = 1 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac
      rw [GlobalTheory.T.finiteIdeleModulus_prod_localUnitIdeles _ _ (valuation_gdet_kapAt S hj hk), h1, Real.one_rpow, Real.one_rpow, mul_one]
    rw [hm, Complex.ofReal_one, mul_one]
  · congr 1
    funext x
    apply halfInd_congr
    by_cases hx : IsHalf e x
    · have hinv : (conjPt S j k)⁻¹ = resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹ := by
        rw [← resG_inv_eq hε', ← _root_.mul_inv_rev, resG_compl _ hε]
      have key : actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (conjPt S j k)⁻¹ x =
          actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x :=
        calc _ = actO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (1 * 1⁻¹)
              (resG _ (1 - ε) (conjPt S j k)⁻¹ * (resG _ ε (conjPt S j k))⁻¹) x := by rw [one_mul, ← hinv]
          _ = actO _ _ 1 (resG _ (1 - ε) (conjPt S j k)⁻¹)
              (actO _ _ 1⁻¹ (resG _ ε (conjPt S j k))⁻¹ x) := (actO_actO _ _ _ _ _).symm
          _ = _ := actO_one_resG_compl he2 hc hε halg _ _ ((isHalf_actO _ _ _).2 hx)
      rw [key]
    · constructor <;> rintro ⟨-, h⟩ <;> exact absurd ((isHalf_actO _ _ _).1 h) hx

end GlobalTheory.TopLevelInv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.unfoldingColumnArgs_movedPoint_conj_atPlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  first | exact @GlobalTheory.TopLevelInv.colAt_movedPt_conj | exact GlobalTheory.TopLevelInv.colAt_movedPt_conj | (intros; apply GlobalTheory.TopLevelInv.colAt_movedPt_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.RowEx.BottomHecke

variable {D : D7}

theorem thetaFunO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {f : WO S V → ℂ} :
    IsThetaFunO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) f ↔ IsThetaFunO ψ S V f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem weilDatumO_stdLatSp {ψ : AddChar (AF D.host.F) ℂ} {S V : HSp D} (hV : V.gram = 1) {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)} (h : IsWeilDatumO ψ S V χS χT om) :
    IsWeilDatumO ψ S (GlobalTheory.SplitVacAlg.stdLatSp V hV) χS χT om :=
  { std := h.std,
    hecS := h.hecS,
    hecT := h.hecT,
    resS := h.resS,
    resT := h.resT,
    om_pres := fun p f hf => (thetaFunO_stdLatSp hV).2 (h.om_pres p f ((thetaFunO_stdLatSp hV).1 hf)),
    om_heis := fun g h' w f hf => h.om_heis g h' w f ((thetaFunO_stdLatSp hV).1 hf),
    om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_stdLatSp hV).1 hf),
    om_cont := fun f hf => h.om_cont f ((thetaFunO_stdLatSp hV).1 hf),
    om_unit := fun μ 𝓕 hμ h𝓕 p f hf => h.om_unit μ 𝓕 hμ h𝓕 p f ((thetaFunO_stdLatSp hV).1 hf),
    om_split := fun e he g h' hg hh x y hx hy => by
      obtain ⟨r, hr, H⟩ := h.om_split e he g h' hg hh x y hx hy
      exact ⟨r, hr, fun ℓ hℓ f hf => H ℓ (fun u hu f' hf' => hℓ u hu f' ((thetaFunO_stdLatSp hV).2 hf')) f
        ((thetaFunO_stdLatSp hV).1 hf)⟩ }

theorem vacuum_hecke : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW), Formalism.L2.NTheta.IsHeckeElt (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) e (ϖ : D.host.E) k α →
      ∃ Δ : Finset (WO (GlobalTheory.Grid.neg A) WW), (∀ u ∈ Δ, u.map (infPart D) = 0) ∧
        X.ω t (1, α) X.vac =
          ((((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW α) : Circle) : ℂ) *
            ((Real.sqrt (Δ.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ Δ, heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he ϖ k α hα
  obtain ⟨hg, hlat, -⟩ := hX.stdW
  have hS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hX.is.rigA.1
  have hT : IsSelfDualC (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.rW.Λ := hX.is.rigW.1
  have hL : (X.rW.Λ : Set (Fin WW.rank → D.host.E)) = L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hg) :=
    Set.ext fun y => (hlat y).trans (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hg y).symm
  obtain ⟨Δ, hΔ⟩ := GlobalTheory.HeckeVacuum.exists_halfReps hS hT hL he hα
  refine ⟨Δ, fun x hx => GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj he) (hΔ.1 x hx).2, ?_⟩
  have hW := weilDatumO_stdLatSp hg (hX.is.weil t)
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) (GlobalTheory.SplitVacAlg.stdLatSp WW hg) X.vac :=
    (thetaFunO_stdLatSp hg).2 hX.is.isVac.2.theta
  have h := GlobalTheory.HeckeVacuum.om_elt hW hS hT hL he hα hf hX.is.isVac.2.lat hΔ
  have e1 : X.ω t (1, α) X.vac = ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm 1, α) X.vac := rfl
  rw [e1, map_one]
  exact h

end GlobalTheory.RowEx.BottomHecke
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.StabVacSplit

open GlobalTheory.Grid (neg)



theorem stab_vac_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (e : AE D) (he : IsSplitIdem D e)
    (k : GA D WW), k ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ → Formalism.L2.Theta.SuppAt e WW k →
      X.ω t (1, k) X.vac =
        (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac := by
  intro D T L sc G W i j A A' WW X hX t e he k hk hsupp
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hLW : L0c D (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) = (X.rW.Λ : Set (Fin WW.rank → D.host.E)) := by
    ext y
    exact (GlobalTheory.SplitVacAlg.mem_frameLattice_iff_integral_coords WW hX.stdW.1 y).trans (hX.stdW.2.1 y).symm
  have fwd : ∀ h : GA D WW, h ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ →
      ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) →
        actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) := by
    intro h hh u hu
    have h1 : (1 : AE D) • actO (neg A) WW 1 h u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
      GlobalTheory.HeckeVacuum.smul_actO_mem _ _ 1 h (fun y hy => by
        rw [map_one, one_smul]
        have h2 := (hh.2.1 y).1 (by rw [hLW]; exact hy)
        rw [hLW] at h2
        exact h2) u hu
    rwa [one_smul] at h1
  have hinv : k⁻¹ ∈ KsphC (GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) ∅ :=
    (GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k⁻¹).1
      (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG (V := GlobalTheory.SplitVacAlg.stdLatSp WW hX.stdW.1) k).2 hk))
  have hback : ∀ u : WO (neg A) WW, actO (neg A) WW 1 k⁻¹ (actO (neg A) WW 1 k u) = u := fun u => by
    rw [← GlobalTheory.HeckeVacuum.act_mul (S := neg A) (T := WW) k⁻¹ k u, inv_mul_cancel, GlobalTheory.HeckeVacuum.act_one]
  have hlat : ∀ u, u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) ↔
      actO (neg A) WW 1 k u ∈ (latO (neg A) WW (X.rA.Λ : Set _) (X.rW.Λ : Set _) fun _ => True) :=
    fun u => ⟨fwd k hk u, fun hu => (hback u) ▸ fwd k⁻¹ hinv _ hu⟩
  have h1 : om' (1, k) X.vac = ((splitFacO _ _ (GlobalTheory.VecInv.detAt e he.1 (neg A) 1) (GlobalTheory.VecInv.detAt e he.1 WW k) : Circle) : ℂ) • X.vac :=
    GlobalTheory.T.splitPlace_weilRep_latticeVacuum_character D W.ψ (neg A) WW X.rA.Λ X.rW.Λ _ _ om' hW hsdS hsdT e he 1 k
      (GlobalTheory.SplitLinear.suppAt_one e _) hsupp hlat _ _ (GlobalTheory.VecInv.isDetAt_detAt e he.1 (neg A) 1)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 WW k) X.vac hX.is.isVac.2.theta hX.is.isVac.2.lat
  have e1 : X.ω t (1, k) = om' (1, k) := by
    rw [hom']
    show X.ω t (1, k) = X.ω t ((GlobalTheory.Grid.ofSgn true A) 1, k)
    rw [map_one]
  rw [e1, h1, splitFacO, map_one, map_one, inv_one, one_mul]

end GlobalTheory.StabVacSplit

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (n : Fin (D.R.m + 1)),
    ((n : ℕ) = D.R.m → ∀ τ, W.onb (.top D.R.m) τ = GlobalTheory.RowReal.topFrame W τ) → ∀ τ,
    (W.onb (.top n) τ)⁻¹ * compAt W.θ τ (mt _ (GlobalTheory.RowReal.ptTop W g n)) * W.onb (.top n) τ =
      (rowComp (GlobalTheory.RowReal.rowSizes D) g n τ).1.submatrix (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2)))
        (Fin.cast (GlobalTheory.RowReal.rank_top G (Nat.lt_succ_iff.1 n.2))) := by
  first | exact @GlobalTheory.RowReal.ptTop_inOnb | exact GlobalTheory.RowReal.ptTop_inOnb | (intros; apply GlobalTheory.RowReal.ptTop_inOnb <;> assumption)
end
