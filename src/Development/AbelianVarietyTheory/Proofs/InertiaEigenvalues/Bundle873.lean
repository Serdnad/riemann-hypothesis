module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle842
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle856
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle071
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle859
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle861
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle864
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.ExportSeries.TupleChars

variable {D : D7}

open GlobalTheory.StepLaw (ResAt UnrOff)

theorem idemSum_mul_idemAt {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) : (idem Q + cA D (idem Q)) * idemAt PP = 0 := by

  rw [idem, map_sum, add_mul, Finset.sum_mul, Finset.sum_mul,
  Finset.sum_eq_zero fun i hi => h.mul_eq_zero (hQ hi) hPP (by rintro rfl; exact hn hi),
  Finset.sum_eq_zero fun i hi => by rw [mul_comm]; exact h.mul_conj hPP (hQ hi), add_zero]

theorem idemSum_mul_of_off {P Q : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : Q ⊆ P) {PP : Pl D.host.E}
    (hPP : PP ∈ P) (hn : PP ∉ Q) {e : AE D} (he : IsIdemAt e PP) {x : AE D} (hx : e * (x - 1) = x - 1) :
    (idem Q + cA D (idem Q)) * x = idem Q + cA D (idem Q) := by
  have k := idemSum_mul_idemAt h hQ hPP hn
  rw [idemAt_eq he] at k
  linear_combination (-(idem Q + cA D (idem Q))) * hx + (x - 1) * k

theorem resAt_of_isResAt {χ : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {c : (kP PP)ˣ →* Circle} (h : IsResAt χ PP c) :
    ResAt χ PP (Circle.toUnits.comp c) := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  rw [h x (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm]
  rfl

theorem resAt_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet P)
    (hQ : Q ⊆ P) {PP : Pl D.host.E} (hPP : PP ∈ P) (hn : PP ∉ Q) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2 (idemSum_mul_of_off h hQ hPP hn he hx)]
  simp

theorem resAt_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (PP : Pl D.host.E) : ResAt χ PP 1 := by
  intro e he x hx hi u hu
  have he' := idemAt_eq he
  have hfu := SpecGood.finUnit_of_res PP (by rw [he']; exact he) x
    (by rw [he']; linear_combination (-1 : AE D) * hx) hi u hu.symm
  rw [hχ x hfu.1 hfu.2.1 hfu.2.2]
  simp

theorem resAt_twist {t : Twist D Circle} (ht : t.Good) {P : Finset (Pl D.host.E)} (h : SplitSet P) (hQ : t.Q ⊆ P)
    {PP : Pl D.host.E} (hPP : PP ∈ P) : ResAt t.chi PP (t.locC PP) := by
  by_cases hq : PP ∈ t.Q
  · have e : t.locC PP = t.resC PP := by simp only [Twist.locC, if_pos hq]
    rw [e]
    exact resAt_of_isResAt (ht.res PP hq)
  · have e : t.locC PP = 1 := by simp only [Twist.locC, if_neg hq]
    rw [e]
    exact resAt_of_unram ht.unram h hQ hPP hq

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  simp [infPart, Algebra.TensorProduct.algebraMap_apply]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
  exact TensorProduct.zero_tmul _ _

theorem infPart_eq_one {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x : AE D}
    (h : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  have k := congrArg (infPart D) h
  rw [map_mul, map_sub, map_one, infPart_placeIdem hε, zero_mul] at k
  linear_combination -k

theorem unrOff_of_unram {χ : (AE D)ˣ →* Circle} {P Q : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (h : SplitSet Q)
    (hQ : Q ⊆ P) : UnrOff χ P := by
  intro v ε hε hv x h1 h2 h3
  refine hχ x (infPart_eq_one hε h1) h2 h3 ?_
  have k : (idem Q + cA D (idem Q)) * algebraMap (AF D.host.F) (AE D) ε = 0 := by

    rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v', ε', hε', he⟩ := (h.isIdemAt hPP).1
    have hu := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v' ε' (h.isIdemAt hPP) hε' he
    rw [he, ← map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε fun e => hv PP (hQ hPP) (hu.trans e), map_zero]
  linear_combination (-(idem Q + cA D (idem Q))) * h1 + ((x : AE D) - 1) * k

theorem unrOff_of_unramEverywhere {χ : (AE D)ˣ →* Circle} (hχ : UnramEverywhere D χ) (P : Finset (Pl D.host.E)) :
    UnrOff χ P := fun _ _ hε _ x h1 h2 h3 => hχ x (infPart_eq_one hε h1) h2 h3

theorem tuple_chars : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ (ν : Twist D Circle), ν.Good → B.admitted ν.Q →
    (∀ PP ∈ allP B ν.Q, GlobalTheory.StepLaw.ResAt (B.mu * ν.chi) PP (resP B ν PP) ∧
      GlobalTheory.StepLaw.ResAt (B.mu * ν.chi * B.eta⁻¹) PP (resP B ν PP)) ∧
    GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi) (allP B ν.Q) ∧ GlobalTheory.StepLaw.UnrOff (B.mu * ν.chi * B.eta⁻¹) (allP B ν.Q) := by
  intro D S T B hB ν hν hA
  classical
  obtain ⟨P, hPg, hQP, hP⟩ := hA.1.split
  have hsub : allP B ν.Q ⊆ P := Finset.union_subset hPg hQP
  have hdeP : B.de.Q ⊆ P := fun x hx => hQP (Finset.mem_union_left _ hx)
  have hνP : ν.Q ⊆ P := fun x hx => hQP (Finset.mem_union_right _ hx)
  have hη : UnramEverywhere D B.eta := hB.eta.2.1
  have key : ∀ PP ∈ allP B ν.Q, ResAt (B.mu * ν.chi) PP (resP B ν PP) := by
    intro PP hPP
    have hPPP := hsub hPP
    have hνr := resAt_twist hν hP hνP hPPP
    by_cases hg : PP ∈ B.G.Pg
    · have hde : PP ∉ B.de.Q := fun h => Finset.disjoint_left.1 hA.1.disj hg (Finset.mem_union_left _ h)
      have hdl : B.de.locC PP = 1 := by simp only [Twist.locC, if_neg hde]
      rw [resP, if_pos hg, hdl, mul_one]
      exact ResAt.mul (resAt_of_isResAt (hB.tame PP hg)) hνr
    · rw [resP, if_neg hg]
      exact ResAt.mul (ResAt.mul (resAt_of_unram hB.unram hP hPg hPPP hg) (resAt_twist hB.de hP hdeP hPPP)) hνr
  have u1 : UnrOff (B.mu * ν.chi) (allP B ν.Q) :=
    UnrOff.mul (UnrOff.mul (unrOff_of_unram hB.unram (hP.mono hPg) (by intro x hx; simp [allP, hx]))
      (unrOff_of_unram hB.de.unram hB.de.split (by intro x hx; simp [allP, hx])))
      (unrOff_of_unram hν.unram hν.split (by intro x hx; simp [allP, hx]))
  refine ⟨fun PP hPP => ⟨key PP hPP, ?_⟩, u1, u1.mul (unrOff_of_unramEverywhere hη _).inv⟩
  have := (key PP hPP).mul (resAt_of_unramEverywhere hη PP).inv
  rwa [inv_one, mul_one] at this

end GlobalTheory.ExportSeries.TupleChars

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.VacTransOrth

theorem vacuumTranslates_conjHalf_sq_norm_eq_card_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y hY hYd μ 𝓕 hμ
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hψ, hf⟩ := hP
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hSV hSW
  have hc0 : infPart D (cA D eT) = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hT
  have hfin : ∀ y ∈ Y, y.map (infPart D) = 0 := fun y hy => by
    ext i j
    show infPart D (y i j) = 0
    rw [← hY y hy i j, RingHom.map_mul, hc0, zero_mul]
  have h := GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ V W hψ.1 μ 𝓕 hμ f₀ hf.theta (hf.norm.2 (μ, 𝓕) hμ) (WO V W) Y id
    (fun _ => 1) (fun _ _ => norm_one) ?_
  · simpa only [one_smul, id] using h
  intro y hy y' hy' hne
  have hnot : y - y' ∉ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) :=
    fun hm => hne (hYd y hy y' hy' hm)
  have hm0 : (y - y').map (infPart D) = 0 := by
    ext i j
    have h1 : infPart D (y i j) = 0 := congrFun (congrFun (hfin y hy) i) j
    have h2 : infPart D (y' i j) = 0 := congrFun (congrFun (hfin y' hy') i) j
    show infPart D (y i j - y' i j) = 0
    rw [RingHom.map_sub, h1, h2, sub_zero]
  rw [hd _ hm0] at hnot
  push_neg at hnot
  obtain ⟨l, hl, hne'⟩ := hnot
  obtain ⟨ε, hε, hεf⟩ := hsign f₀ hf.lat l hl
  exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f₀ hf.lat, hne'⟩

end GlobalTheory.VacTransOrth
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.RealVacPow

open scoped ComplexOrder

theorem vacuum_det_power : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∃ k : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f →
      (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
      om (a, 1) f = (∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) • f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP p BW hB
  have hP1 := hP.1
  obtain ⟨η, hη⟩ := hP1.eta
  choose b hb using hP1.expW
  have hsW : ∀ τ, IsCartanInv (gramAt D W τ) (sW τ) := hP.2.2.2.2.2.2.2.1
  choose q hq1 hq using fun τ => GlobalTheory.OneMapRef.RealMove.detPlus_one (n := V.rank) (sW τ) (hsW τ).1
  refine ⟨fun τ => -(b τ) - (q τ : ℤ), fun a ha f hf hv => ?_⟩
  have hθ : IsInfFam θ := hP1.inf
  have hψ := hP1.weil.std
  have hgV : ∀ τ, gramAt D V τ = 1 := fun τ => by
    unfold gramAt; rw [hP1.std]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun τ => by
    rw [hgV]; exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hdetV : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => by rw [hgV]; simp
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ V hdetV a ha
  have mt1 : Formalism.L2.Theta.mt W 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have hy : IsDetRoot W 1 1 := by
    unfold IsDetRoot
    have : ((matHom W 1).1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) = 1 := mt1
    rw [this, Matrix.det_one, one_mul, Units.val_one, map_one]
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := fun τ => by
    rw [mt1]; exact Matrix.map_one _ (by simp) (by simp)
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hψ V W θ hθ χV χW om η hη hP1.weil (fun _ => 1) sW hS hsW a ha 1 (one_mem _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (χW * (η ^ W.rank)⁻¹) τ ((b τ : ℤ) : ℚ) := fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hb τ) (hη.2.2.2 τ) W.rank
    rwa [add_sub_cancel_right] at this
  have hνx := hxv _ b hexp
  have hinv : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)).det * (compAt θ τ (Formalism.L2.Theta.mt V a)).det = 1 := fun τ => by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, GlobalTheory.OneMapRef.RealMove.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    have : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
      unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one]; rfl
    rw [this, Matrix.det_one, map_one, map_one]
  have hd0 : ∀ τ, (compAt θ τ (Formalism.L2.Theta.mt V a)).det ≠ 0 := fun τ h => by
    have := hinv τ; rw [h, mul_zero] at this; exact zero_ne_one this
  have hdp : ∀ τ, GlobalTheory.WeilParts.detPlus 1 (sW τ) (compAt θ τ (Formalism.L2.Theta.mt V a⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt W 1)) =
      ((compAt θ τ (Formalism.L2.Theta.mt V a)).det)⁻¹ ^ q τ := fun τ => by
    rw [one, (hq τ _ 1 (by rw [Matrix.one_mul, Matrix.mul_one])).1]
    have e : (1 / 2 : ℂ) • (1 + sW τ) * 1 + (1 / 2 : ℂ) • (1 - sW τ) = 1 := by rw [Matrix.mul_one]; module
    rw [e, Matrix.det_one, one_pow, one_mul, eq_inv_of_mul_eq_one_left (hinv τ)]
  rw [map_one, mul_one, Circle.coe_inv, hνx, Finset.prod_congr rfl fun τ _ => hdp τ, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [zpow_sub₀ (hd0 τ), _root_.zpow_neg, zpow_natCast, inv_pow, div_eq_mul_inv]

end GlobalTheory.RealVacPow

end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)




end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}
variable (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q)

theorem isLetters_letterEquiv : IsLetters Dw (letterEquiv (n := n) Dw hΨ hm) := by
  rintro ⟨τ, i, b⟩
  rcases GlobalTheory.Harm.half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate _)
    (GlobalTheory.Harm.not_mem_hostType_iff H) τ with h | ⟨τ', h, rfl⟩
  · have e : letterEquiv Dw hΨ hm ⟨τ, i, b⟩ = ((tauPsi hΨ).symm ⟨τ, h⟩,
        Fin.cast hm.symm (Fin.castAdd Dw.q (i.cast (GlobalTheory.Harm.mult_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_of_mem Dw h]
      rfl
    rw [e]
    exact ⟨rfl, Or.inl ⟨(congrArg Subtype.val ((tauPsi hΨ).apply_symm_apply ⟨τ, h⟩)).symm, rfl⟩⟩
  · have e : letterEquiv Dw hΨ hm ⟨ComplexEmbedding.conjugate τ', i, b⟩ = ((tauPsi hΨ).symm ⟨τ', h⟩,
        Fin.cast hm.symm (Fin.natAdd Dw.p (i.cast (GlobalTheory.Harm.mult_conjEmb_of_mem Dw h))), b) := by
      simp only [letterEquiv, Equiv.trans_apply, GlobalTheory.Harm.thetaLetterEquiv_conjugate Dw h]
      rfl
    rw [e]
    refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
    change conjEmb τ' = conjEmb (tauE D ((tauPsi hΨ).symm ⟨τ', h⟩))
    rw [← tauPsi_apply hΨ, Equiv.apply_symm_apply]

end GlobalTheory.FockLetters

noncomputable section
namespace GlobalTheory.FockLetters

end GlobalTheory.FockLetters
end
end
end
end

section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.MSpanDecay

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Growth (F : GA E a → ℂ) : Prop :=
  ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N

def Good (F : GA E a → ℂ) : Prop :=
  ∃ h : F ∈ Sm E a, ∀ l : List (Lie E a),
    GlobalTheory.ShortVecDecay.Decays (GlobalTheory.GLFin.word l ⟨F, h⟩).1 ∧ Growth (GlobalTheory.GLFin.word l ⟨F, h⟩).1


theorem Growth.zero : Growth (0 : GA E a → ℂ) := fun _ => ⟨0, 0, fun _ => by simp⟩

theorem Growth.add {F G : GA E a → ℂ} (hF : Growth F) (hG : Growth G) : Growth (F + G) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  obtain ⟨C', N', h'⟩ := hG g
  refine ⟨|C| + |C'|, max N N', fun y => ?_⟩
  have h1 := one_le_height y
  have p1 : height y ^ N ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_left _ _)
  have p2 : height y ^ N' ≤ height y ^ max N N' := pow_le_pow_right₀ h1 (le_max_right _ _)
  have q : 0 ≤ height y ^ N := by positivity
  have q' : 0 ≤ height y ^ N' := by positivity
  calc ‖(F + G) (g * infGL E a y)‖ ≤ ‖F (g * infGL E a y)‖ + ‖G (g * infGL E a y)‖ := norm_add_le _ _
    _ ≤ C * height y ^ N + C' * height y ^ N' := add_le_add (h y) (h' y)
    _ ≤ |C| * height y ^ max N N' + |C'| * height y ^ max N N' := by
        exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C) q).trans
            (mul_le_mul_of_nonneg_left p1 (abs_nonneg C))) ((mul_le_mul_of_nonneg_right (le_abs_self C') q').trans
            (mul_le_mul_of_nonneg_left p2 (abs_nonneg C')))
    _ = (|C| + |C'|) * height y ^ max N N' := by ring

theorem Growth.smul {F : GA E a → ℂ} (hF : Growth F) (z : ℂ) : Growth (z • F) := fun g => by
  obtain ⟨C, N, h⟩ := hF g
  refine ⟨‖z‖ * C, N, fun y => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h y) (norm_nonneg _)

theorem Good.mem_Sm {F : GA E a → ℂ} (h : Good F) : F ∈ Sm E a := h.1

theorem Good.decays {F : GA E a → ℂ} (h : Good F) : GlobalTheory.ShortVecDecay.Decays F := (h.2 []).1

theorem Good.growth {F : GA E a → ℂ} (h : Good F) : Growth F := (h.2 []).2

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by
  simp [GlobalTheory.GLFin.word, Module.End.mul_apply]

theorem word_append_single (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.prod_append, Module.End.mul_apply]

theorem Good.derivative {F : GA E a → ℂ} (h : Good F) (X : Lie E a) : Good (lieD X F) := by
  obtain ⟨hF, hl⟩ := h
  refine ⟨lieD_mem_Sm X hF, fun l => ?_⟩
  have e : (⟨lieD X F, lieD_mem_Sm X hF⟩ : Sm E a) = lie E a X ⟨F, hF⟩ := rfl
  rw [e, ← word_append_single]
  exact hl _

theorem good_zero : Good (0 : GA E a → ℂ) := by
  refine ⟨zero_mem _, fun l => ?_⟩
  have e : (⟨0, zero_mem _⟩ : Sm E a) = 0 := rfl
  rw [e, map_zero]
  exact ⟨GlobalTheory.ShortVecDecay.Decays.zero, Growth.zero⟩

theorem Good.add {F G : GA E a → ℂ} (hF : Good F) (hG : Good G) : Good (F + G) := by
  obtain ⟨hF1, hF2⟩ := hF
  obtain ⟨hG1, hG2⟩ := hG
  refine ⟨add_mem hF1 hG1, fun l => ?_⟩
  have e : (⟨F + G, add_mem hF1 hG1⟩ : Sm E a) = ⟨F, hF1⟩ + ⟨G, hG1⟩ := rfl
  rw [e, map_add (f := _), Submodule.coe_add]
  exact ⟨(hF2 l).1.add (hG2 l).1, (hF2 l).2.add (hG2 l).2⟩

theorem Good.smul {F : GA E a → ℂ} (hF : Good F) (z : ℂ) : Good (z • F) := by
  obtain ⟨hF1, hF2⟩ := hF
  refine ⟨Submodule.smul_mem _ z hF1, fun l => ?_⟩
  have e : (⟨z • F, Submodule.smul_mem _ z hF1⟩ : Sm E a) = z • ⟨F, hF1⟩ := rfl
  rw [e, map_smul, Submodule.coe_smul]
  exact ⟨(hF2 l).1.smul z, (hF2 l).2.smul z⟩

theorem good_of_mem {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a} (hφ : φ ∈ π.V) : Good φ.1 :=
  ⟨φ.2, fun l => ⟨GlobalTheory.ShortVecDecay.decays_of_mem hπ (GlobalTheory.ShortVecDecay.word_mem l hφ),
    (π.cusp _ (GlobalTheory.ShortVecDecay.word_mem l hφ)).1.growth⟩⟩

end GlobalTheory.MSpanDecay
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.localLifting_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, 160 ≤ C → ElementDenominator.Conclusion1 D C := by
  first | exact @GlobalTheory.theoremA_closing | exact GlobalTheory.theoremA_closing | (intros; apply GlobalTheory.theoremA_closing <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localLifting_theoremB_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  first | exact @GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.prv_twenty_five_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), RamifiedCoefficientChains.aux₃ D HW F 25 := by
  first | exact @GlobalTheory.ramifiedCoefficientChains_prv_twenty_five | exact GlobalTheory.ramifiedCoefficientChains_prv_twenty_five | (intros; apply GlobalTheory.ramifiedCoefficientChains_prv_twenty_five <;> assumption)
end
