module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle518
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

namespace GlobalTheory.Mem.RowsTies

theorem isQuotInt_zero {D : D7} (V : HSp D) (hV : V.SigOK) (c : ℝ) {φ : GA D V → ℂ} (h : ∀ g, φ g = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt V c φ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.Mem.VolMeasure.existsUnique_isVolMeasG D V hV
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ.1
  have e : φ = fun _ => 0 := funext h
  subst e
  exact ⟨⟨(μ, 𝓕), ⟨hμ, h𝓕⟩⟩, fun m _ => ⟨integrableOn_zero, by simp⟩⟩

theorem rows_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsChain → ∀ (xi : D.what₂.Tup → Formalism.L2.Host.HChar D.host.E) (U : Set D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n) → (∀ μ, (xi μ).TrivOn D.host.F) → (∀ μ ∈ U, R.xiH (tupT μ) = xi μ ∧ (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1)) → (∀ μ, μ ∉ U → ∀ j, j < D.R.m → D.what₂.io μ j = 0) → (∀ θ : InfF D, IsInfFam θ → ∀ ψ, IsStdChar D ψ (-1) → ∀ Wf : WeilFun D ψ, ∃ Rc : RecFun D θ ψ, Rc.ChrIs R.C xi ∧ Rc.IoTie Wf ∧ ∀ μ ∈ U, ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j)) (fun h => star ((Rc.row μ j x).1 h) * (Rc.row μ j y).1 h) (inner ℂ x y)) := by
  intro hD D G _ _ Pl0 T A Ks _ _ _ R hL hM hC xi U tupT hf ht hU hoff θ hθ ψ hψ Wf
  obtain rfl : θ = R.θ := (GlobalTheory.Mem.InfFamUnique.existsUnique_infFam D).unique hθ hM.inf
  obtain rfl : ψ = R.ψ := (GlobalTheory.StdAdelicChar.existsUnique_isStdChar D (-1) (Or.inr rfl)).unique hψ (hC.ωX A.μ0).std
  obtain ⟨Rc, hR⟩ := RecFun.exists_chrIs R.C xi hf ht R.θ R.ψ
  have hu := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1
  have he : Rc.eta = R.eta := hu _ _ _ hR.eta hL.eta
  have key : ∀ μ, ∃ (row : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] CuspS R.θ (D.sp.Y j)) (Phi : ∀ j, ThS R.ψ (D.sp.Y (j + 1)) (D.sp.Y j)),
      (∀ j, j < D.R.m → Phi j ≠ 0) ∧
      (μ ∈ U → ∀ j, j ≤ D.R.m → ∀ x y : D.what₂.Mult μ j,
        GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun h => star ((row j x).1 h) * (row j y).1 h) (inner ℂ x y)) ∧
      ∀ j, j < D.R.m → ∀ y : D.what₂.Mult μ (j + 1), ∃ L : GA D (D.sp.Y j) → ℂ,
        (∀ g, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y (j + 1)) (Rc.mY μ (j + 1) * Rc.petC (D.sp.Y (j + 1)))
          (fun h => Wf.ker _ _ (Rc.carY μ (j + 1) (j + 1)) (Rc.carY μ (j + 1) j) (Phi j) h g *
            (row (j + 1) y).1 h) (L g)) ∧
        ∀ x : D.what₂.Mult μ j, GlobalTheory.IndefiniteRowSideFullHecke.SplittingKernelQuotients.IsQuotInt (D.sp.Y j) (Rc.mY μ j * Rc.petC (D.sp.Y j))
          (fun g => star (L g) * (row j x).1 g) (inner ℂ (D.what₂.io μ j y) x) := fun μ => by
    by_cases hμ : μ ∈ U
    · obtain ⟨hx, hT⟩ := hU μ hμ
      have hc : ∀ j, j < D.R.m → Rc.chr μ (j + 1) = R.toLevCh.mu (tupT μ) (j + 1) := fun j hj =>
        hu _ _ _ (hR.chr μ ⟨j, hj⟩) (hx ▸ GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi (tupT μ)))
      obtain ⟨row, Phi, h1, h2, h3⟩ := GlobalTheory.T.oneTuple_rows_cuspForms_isometric_thetaLifts hD D G Pl0 T A Ks R hL hM hC (tupT μ) μ hT Wf
        (fun j => Rc.mY μ j * Rc.petC (D.sp.Y j)) fun j =>
          mul_pos (Rc.mY_pos _ _) (mul_pos (Rc.petF_pos _) (Finset.prod_pos fun _ _ => Rc.meas.petR_pos _ _))
      refine ⟨row, Phi, h1, fun _ => h2, fun j hj y => ?_⟩
      unfold RecFun.carY
      rw [hc j hj, he]
      exact h3 j hj y
    · refine ⟨0, Rc.Phi μ, Rc.Phi_ne hψ μ, fun h => absurd h hμ, fun j hj y => ⟨0, fun g => ?_, fun x => ?_⟩⟩
      · exact isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
      · rw [hoff μ hμ j hj]
        simpa using isQuotInt_zero _ (D.sp.Y_sig _) _ fun h => by simp
  choose row Phi h1 h2 h3 using key
  exact ⟨{ Rc with row := row, Phi := Phi, Phi_ne := fun _ => h1 }, ⟨hR.chr, hR.eta⟩, h3, h2⟩

end GlobalTheory.Mem.RowsTies
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

section EnlAux

variable {B B' : Base}

def enlEmb (hR : Set.range B.embLL ⊆ Set.range B'.embLL) : B.LL →+* B'.LL :=
  (RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))).comp B.embLL.rangeRestrict)

theorem enlEmb_spec (hR : Set.range B.embLL ⊆ Set.range B'.embLL) (x : B.LL) :
    B'.embLL (enlEmb hR x) = B.embLL x := by
  have h := congrArg Subtype.val ((RingEquiv.ofBijective B'.embLL.rangeRestrict
      ⟨fun x y h => B'.embLL.injective (congrArg Subtype.val h), B'.embLL.rangeRestrict_surjective⟩).apply_symm_apply
    ((Subring.inclusion fun x hx => RingHom.mem_range.2 (hR (RingHom.mem_range.1 hx))) (B.embLL.rangeRestrict x)))
  exact h

def ksEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.Ks ≃ₐ[ℚ] B'.Ks :=
  (B.Ks.equivMap B.embLL.toRatAlgHom).trans ((IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm).trans (B'.Ks.equivMap B'.embLL.toRatAlgHom).symm)

theorem ksEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.Ks) : B'.embLL ((ksEquiv hK x : B'.Ks) : B'.LL) = B.embLL (x : B.LL) := by
  have h3 : (B'.Ks.equivMap B'.embLL.toRatAlgHom) (ksEquiv hK x) =
      IntermediateField.equivOfEq (F := ℚ) (E := ℂ) (S := B.Ks.map B.embLL.toRatAlgHom) (T := B'.Ks.map B'.embLL.toRatAlgHom) hK.symm (B.Ks.equivMap B.embLL.toRatAlgHom x) := by
    exact (B'.Ks.equivMap B'.embLL.toRatAlgHom).apply_symm_apply _
  have h4 := congrArg Subtype.val h3
  rw [IntermediateField.coe_equivMap_apply] at h4
  rw [RingHom.toRatAlgHom_apply] at h4
  rw [h4]
  change ((B.Ks.equivMap B.embLL.toRatAlgHom x : B.Ks.map B.embLL.toRatAlgHom) : ℂ) = _
  rw [IntermediateField.coe_equivMap_apply]
  rfl

def oEquiv (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) : B.O ≃+* B'.O := RingOfIntegers.mapRingEquiv (ksEquiv hK).toRingEquiv

theorem oEquiv_spec (hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom) (x : B.O) : B'.embLL (B'.OtoLL (oEquiv hK x)) = B.embLL (B.OtoLL x) := by
  have h := RingOfIntegers.mapRingEquiv_apply (ksEquiv hK).toRingEquiv x
  change B'.embLL (((oEquiv hK x : B'.Ks)) : B'.LL) = B.embLL ((x : B.Ks) : B.LL)
  rw [show (oEquiv hK x : B'.Ks) = ksEquiv hK (x : B.Ks) from h]
  exact ksEquiv_spec hK x

end EnlAux

section EnlAux2

variable {B B' : Base}

theorem enlEmb_Ks (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hK : B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL)) {x : B'.LL} (hx : x ∈ B'.Ks) :
    ∃ x₀ ∈ B.Ks, enlEmb hR x₀ = x := by
  obtain ⟨x₀, hx₀, he⟩ : B'.embLL x ∈ B.embLL '' (B.Ks : Set B.LL) := hK ▸ ⟨x, hx, rfl⟩
  exact ⟨x₀, hx₀, B'.embLL.injective (by rw [enlEmb_spec, he])⟩

theorem coefficientFieldEnlarge_mem_larger_fixedField (hR : Set.range B.embLL ⊆ Set.range B'.embLL)
    (hL : B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL)) {x : B.LL} (hx : x ∈ B.LL0) :
    enlEmb hR x ∈ B'.LL0 := by
  obtain ⟨x', hx', he⟩ : B.embLL x ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hL ⟨x, hx, rfl⟩
  have : enlEmb hR x = x' := B'.embLL.injective (by rw [enlEmb_spec, he])
  rw [this]
  exact hx'

end EnlAux2

section CdAux

abbrev withCd (D : D7) (c₀ : CDHaar) : D7 := { D with cd := c₀ }

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {r : ℕ}

theorem finVol_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (V : HSp D) :
    Formalism.L2.Pj.FinVol (D := withCd D c₀) V ↔ Formalism.L2.Pj.FinVol (D := D) V := by
  subst h
  rfl

theorem cuspL2_withCd (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ) :
    Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu ↔ Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu := by
  subst h
  rfl

theorem peterssonDefinite_iff_of_eq_compactDualHaar (D : D7) (c₀ : CDHaar) (h : D.cd = c₀) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r)
    (σ : c.F →+* ℂ) (V : HSp D) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r) (mu : GA D V → ℂ)
    (h₁ : Formalism.L2.Pj.CuspL2 (D := withCd D c₀) U σ V dict mu) (h₂ : Formalism.L2.Pj.CuspL2 (D := D) U σ V dict mu) :
    Formalism.L2.Pj.L2DefiniteCuspForms (D := withCd D c₀) U σ V dict mu h₁ ↔ Formalism.L2.Pj.L2DefiniteCuspForms (D := D) U σ V dict mu h₂ := by
  subst h
  rfl

end CdAux

theorem exists_adelicCore_transport_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl0 B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb := by
  intro B B' f f' T T' w w' Z Z' hX Wt z hE hf hC
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  obtain ⟨h1, hKs, hLL0, hR⟩ := hE
  have hι := enlEmb_spec hR
  have hι0 := fun x (hx : x ∈ B.LL0) => coefficientFieldEnlarge_mem_larger_fixedField hR hLL0 hx
  have hιK := fun x (hx : x ∈ B'.Ks) => enlEmb_Ks hR hKs hx
  have hO := oEquiv_spec hK
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hff := eq_of_heq hf
  subst hff
  obtain ⟨hL, hCa, hDim, hpb⟩ := hC
  have hcd : (w'.st Z').toD7.cd = (w.st Z).toD7.cd := Tr.cd_eq _ _
  let g : z.core.Q.c.F →+* _ := (enlEmb hR).comp ((algebraMap (↥z.core.Q.c.F) (w.st Z).toD7.what₂.LL) : z.core.Q.c.F →+* B.LL)
  let Q' : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (z.core.Q.H), l := (z.core.Q.l), c := (z.core.Q.c), Dw := (z.core.Q.Dw), Xo := (z.core.Q.Xo),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q', U := (z.core.U), V := (z.core.V), dict := (z.core.dict), mu := (z.core.mu),
          Kf := (z.core.Kf), pb := (z.core.pb) }
      cE := (z.core.cE), chiW := (z.core.chiW), x₀ := (z.core.x₀), iota := (z.core.iota) }
  refine ⟨core', (g.toAlgebra), ?_⟩

  refine ⟨fun y => (hι _).trans (z.alg_eq y), fun y => hι0 _ (z.fieldValues_mem_fixedField y), fun x hx => ?_,
    (HEq.refl z.core.Q.H), (HEq.refl z.core.Q.l), (HEq.refl z.core.Q.c), (HEq.refl z.core.Q.Dw),
    (HEq.refl z.core.Q.Xo), (HEq.refl z.core.U), (HEq.refl z.core.V), (HEq.refl z.core.dict),
    (HEq.refl z.core.mu), (HEq.refl z.core.Kf), (HEq.refl z.core.cE), (HEq.refl z.core.chiW),
    (HEq.refl z.core.x₀), (HEq.refl z.core.iota), ?_, (hCa), (hDim), (hpb)⟩
  · obtain ⟨x₀, hx₀, he⟩ := hιK x hx
    obtain ⟨y, hy⟩ := z.Ks_le x₀ hx₀
    exact ⟨y, (congrArg (enlEmb hR) hy).trans he⟩
  · have hPF : Q'.PinField := fun x => (hO (z.core.Q.eO x)).trans (hL.pins.2.2.1 x)
    exact
      { pins := ⟨(hL.pins.left), (hL.pins.right.left), hPF, (hL.pins.right.right.right)⟩
        half := (hL.half)
        evalWD := (hL.evalWD)
        unf := (hL.unf)
        unTest := (hL.unTest)
        chiTriv := (hL.chiTriv)
        dictU := (hL.dictU)
        spaceW := (hL.spaceW)
        levelK := (hL.levelK)
        xiAbs := (hL.xiAbs)
        muUnit := (hL.muUnit)
        muCont := (hL.muCont)
        finVol := fun j hj σ hσ => (finVol_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _).1 ((hL.finVol j hj σ hσ))
        cuspFD := (hL.cuspFD)
        supDef := (hL.supDef)
        cuspidalL2Subspace := fun j hj σ hσ => (cuspL2_withCd (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _).1 ((hL.cuspidalL2Subspace j hj σ hσ))
        l2Def := fun j hj σ hσ =>
          (peterssonDefinite_iff_of_eq_compactDualHaar (w'.st Z').toD7 (w.st Z).toD7.cd hcd _ _ _ _ _ ((hL.cuspidalL2Subspace j hj σ hσ)) _).1 ((hL.l2Def j hj σ hσ))
        unitIndep := (hL.unitIndep)
        ptNe := (hL.ptNe)
        cuspMul := (hL.cuspMul)
        latZ := (hL.latZ)
        cuNe := (hL.cuNe)
        expo := (hL.expo) }

end GlobalTheory.Mem.R3.Rw
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.CuspExt


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem cusp_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {H H' : Host E} (hH : H' = H) {l : Level H} {l' : Level H'} (hl : HEq l' l)
    {c : Coeff l} {c' : Coeff l'} (hc : HEq c' c) {Dw : ℕ → Datum H} {Dw' : ℕ → Datum H'} (hDw : HEq Dw' Dw)
    {Xo : ∀ j, Moduli (Dw j) l} {Xo' : ∀ j, Moduli (Dw' j) l'} (hXo : HEq Xo' Xo)
    {U : ∀ j (σ : c.F →+* ℂ), Formalism.L2.Pj.Unf (Xo j) c σ r} {U' : ∀ j (σ : c'.F →+* ℂ), Formalism.L2.Pj.Unf (Xo' j) c' σ r}
    (hU : HEq U' U) {a a' : (E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {n n' : ℕ} (hn : n' = n) (j : ℕ) :
    Formalism.L2.Pj.Rul (Xo' j) c' = Formalism.L2.Pj.Rul (Xo j) c ∧
    (∀ (x : Formalism.L2.Pj.Rul (Xo j) c) (x' : Formalism.L2.Pj.Rul (Xo' j) c'), HEq x' x →
      (x' ∈ Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n' ↔ x ∈ Formalism.L2.Pj.cusp (Xo j) c (U j) a n)) ∧
    (∀ (x : Formalism.L2.Pj.Rul (Xo j) c) (x' : Formalism.L2.Pj.Rul (Xo' j) c') (h : x ∈ Formalism.L2.Pj.cusp (Xo j) c (U j) a n)
      (h' : x' ∈ Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n'), HEq x' x →
      HEq (⟨x', h'⟩ : Formalism.L2.Pj.cusp (Xo' j) c' (U' j) a' n') (⟨x, h⟩ : Formalism.L2.Pj.cusp (Xo j) c (U j) a n)) := by
  subst hH ha hn
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hDw
  obtain rfl := eq_of_heq hXo
  obtain rfl := eq_of_heq hU
  refine ⟨rfl, fun x x' hx => ?_, fun x x' h h' hx => ?_⟩
  · obtain rfl := eq_of_heq hx; exact Iff.rfl
  · obtain rfl := eq_of_heq hx; exact HEq.rfl



theorem cusp_ext : StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        z'.core.R ((j' : ℕ) + 1) = z.core.R ((j : ℕ) + 1) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)), HEq r' r → (r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n ↔ r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) ∧
        (∀ (r : z.core.R ((j : ℕ) + 1)) (r' : z'.core.R ((j' : ℕ) + 1)) (h : r ∈ z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n) (h' : r' ∈ z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n), HEq r' r →
          HEq (⟨r', h'⟩ : z'.core.cuspA ((j' : ℕ) + 1) (Formalism.L2.Pj.wtA (z'.geo.κ j')) (z'.geo.κ j').n) (⟨r, h⟩ : z.core.cuspA ((j : ℕ) + 1) (Formalism.L2.Pj.wtA (z.geo.κ j)) (z.geo.κ j).n)) := by
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj => ?_
  have hB := hE.1
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have e : j' = j := Fin.ext hj.symm
  subst e

  obtain ⟨h1, h2, h3⟩ := hx.κ j' j' rfl
  have e1 : (z'.geo.κ j').aP = (z.geo.κ j').aP := eq_of_heq h1
  have e2 : (z'.geo.κ j').aM = (z.geo.κ j').aM := eq_of_heq h2
  have hw : Formalism.L2.Pj.wtA (z'.geo.κ j') = Formalism.L2.Pj.wtA (z.geo.κ j') := by
    funext x
    unfold Formalism.L2.Pj.wtA
    rw [e1, e2]
    rfl
  obtain ⟨hR, hm, hs⟩ := cusp_heq (r := (w.st Z).toD7.R.r) (eq_of_heq hx.H) hx.l hx.c hx.Dw hx.Xo hx.U hw h3 ((j' : ℕ) + 1)
  exact ⟨hR, hm, hs⟩

end GlobalTheory.Mem.R3.CuspExt

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LevBC

theorem exists_intCast_of_card_prime {R : Type} [Ring R] (h : (Nat.card R).Prime) (x : R) : ∃ n : ℤ, (n : R) = x := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero h.ne_zero
  have htop : AddSubgroup.zmultiples (1 : R) = ⊤ := by
    rcases h.eq_one_or_self_of_dvd _ (AddSubgroup.card_addSubgroup_dvd_card (AddSubgroup.zmultiples (1 : R))) with h1 | h1
    · exfalso
      have hb := AddSubgroup.eq_bot_of_card_eq _ h1
      have h10 : (1 : R) = 0 := by
        have : (1 : R) ∈ AddSubgroup.zmultiples (1 : R) := AddSubgroup.mem_zmultiples 1
        rw [hb] at this
        exact (AddSubgroup.mem_bot).1 this
      have : Subsingleton R := subsingleton_of_zero_eq_one h10.symm
      rw [Nat.card_unique] at h
      exact Nat.not_prime_one h
    · exact AddSubgroup.eq_top_of_card_eq _ h1
  have hx : x ∈ AddSubgroup.zmultiples (1 : R) := by rw [htop]; exact AddSubgroup.mem_top x
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  exact ⟨n, by rw [← hn, zsmul_one]⟩

theorem exists_intCast_vGs (B : Base) (px : PreX B.toPre) (PP : Pl B.host.E) (hPP : PP ∈ (B.primes px).vGs)
    (c : 𝓞 B.host.E ⧸ PP.asIdeal) : ∃ n : ℤ, (n : 𝓞 B.host.E ⧸ PP.asIdeal) = c := by
  classical
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B px
  have hi : ∃ i, PP ∈ (B.primes px).vG i := by
    rcases Finset.mem_union.1 hPP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hi
  have hn := hPr.vG_norm i PP hi
  have hp := hPr.g_prime i
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
  rw [← hn] at hp
  exact exists_intCast_of_card_prime hp c

theorem baseLevelCharacter_map_coefficientRingHom {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {LL LL' : Type} [CommRing LL] [CommRing LL']
    (ψ : ∀ PP : Pl E, AddChar (kP PP) LL) (ψ' : ∀ PP : Pl E, AddChar (kP PP) LL') (φ : LL →+* LL')
    (h : ∀ PP ∈ Pg, ∀ c, ψ' PP c = φ (ψ PP c)) (x : (P0 Pg r ψ).H) (x' : (P0 Pg r ψ').H) (hx : (x : G0 Pg r) = x') :
    (((P0 Pg r ψ').chi x' : LL'ˣ) : LL') = φ (((P0 Pg r ψ).chi x : LLˣ) : LL) := by
  obtain ⟨x, hxm⟩ := x
  obtain ⟨x', hxm'⟩ := x'
  simp only at hx
  subst hx
  show ((((∏ PP : ↥Pg, (addCharHom (ψ' PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm'⟩ : LL'ˣ)) : LL') =
    φ (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hxm⟩ : LLˣ) : LL)
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LLˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LLˣ) := ⟨fun _ _ _ => rfl⟩
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LL'ˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* LL'ˣ) := ⟨fun _ _ _ => rfl⟩
  rw [prod_apply, prod_apply, Units.coe_prod, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact h PP.1 PP.2 _

theorem lev_bc (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (I : ColIn B px) (I' : ColIn B' px') (hI : I.Ok) (hI' : I'.Ok) (φ : B.LL →+* B'.LL) (hφ : ∀ x, B'.embLL (φ x) = B.embLL x)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    (g' ∈ lev0 I' ↔ g ∈ lev0 I) ∧ ∀ (h0 : g ∈ lev0 I) (h0' : g' ∈ lev0 I'),
      ((chr0 I' ⟨g', h0'⟩ : B'.LLˣ) : B'.LL) = φ (chr0 I ⟨g, h0⟩ : B.LLˣ) := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp I I' hI hI' φ hφ g g' hg
  subst h
  cases hp
  cases hg
  refine ⟨Iff.rfl, fun h0 h0' => ?_⟩
  refine baseLevelCharacter_map_coefficientRingHom _ _ _ _ φ (fun PP hPP c => ?_) ⟨_, h0⟩ ⟨_, h0'⟩ rfl
  rw [psiC_of_mem _ hPP, psiC_of_mem I' hPP]
  obtain ⟨n, hn⟩ := exists_intCast_vGs _ _ PP hPP (Formalism.L2.Col.redP PP P'.host.xi0 * c)
  have e1 := hI'.weil ⟨PP, hPP⟩ c n hn.symm
  have e2 := hI.weil ⟨PP, hPP⟩ c n hn.symm
  have e3 := hφ (I.Ch.psi0 ⟨PP, hPP⟩ c)
  exact RingHom.injective _ (e1.trans (e2.symm.trans e3.symm))

end GlobalTheory.Mem.R3.LevBC

namespace GlobalTheory.Mem.R3.Rw

theorem extN_baseLevel_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (g' ∈ (z'.F.lv2.lvl false).P ↔ g ∈ (z.F.lv2.lvl false).P) ∧ ∀ (hg : g ∈ (z.F.lv2.lvl false).P) (hg' : g' ∈ (z'.F.lv2.lvl false).P), (((z'.F.lv2.lvl false).ψ ⟨g', hg'⟩ : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.F.lv2.lvl false).ψ ⟨g, hg⟩ : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w hE _ _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' _ φ hφ g g' hg
  exact GlobalTheory.Mem.R3.LevBC.lev_bc B B' hE.1 w.px w'.px hpx w.I w'.I w.ok w'.ok φ hφ g g' hg

end GlobalTheory.Mem.R3.Rw
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∃ (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ), ∀ f, IsThetaFunO ψ V W f → IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f → GlobalTheory.ChainFr.LieFockWith ψ θ A B ω f τ κS κT := by
  first | exact @GlobalTheory.LieFock.lieFockUpTo_at | exact GlobalTheory.LieFock.lieFockUpTo_at | (intros; apply GlobalTheory.LieFock.lieFockUpTo_at <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weil_maximalCompact_fock_substitution_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (p q : D.what₂.Tau → ℕ), (∀ τ, p τ + q τ = T.rank) → (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℚ) = -(((p τ : ℚ) - q τ) / 2 + b τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ P : PolF D T.rank S.rank, om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fact M.ε x₁ x₂ x₃ (fun τ => M.fr τ * compAt θ τ (Formalism.L2.Theta.mt T h) * (M.fr τ)⁻¹) (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ) P) := by
  first | exact @GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact | exact GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact | (intros; apply GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_adelicCore_transport_enlargedCoefficientBase_alt : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt),
    Enl0 B B' → HEq f' f → CoreP z →
    ∃ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) ∧
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) ∧
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) ∧
      HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota ∧
      Formalism.L2.Pj.LawsCore core'.toCore ∧ core'.Q.Canon ∧ (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) ∧ core'.pb = f'.P.pb := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_adelicCore_transport_enlargedCoefficientBase | exact GlobalTheory.Mem.R3.Rw.exists_adelicCore_transport_enlargedCoefficientBase | (intros; apply GlobalTheory.Mem.R3.Rw.exists_adelicCore_transport_enlargedCoefficientBase <;> assumption)

end
end
