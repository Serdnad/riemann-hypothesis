module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle126
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle011
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetter
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle144
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle145
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle147
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem xiOver_eq_XiTopG {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl

theorem xiOver_eq_XiTop : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (n : ℕ) (h : n + 1 + 1 = R.m) (p : ChPt (R := R) sel mu u (n + 1)) (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u (n + 1 + 1)), xiOver Ch sel mu cst n h p Y p' = Formalism.L2.Col.XiTop Ch sel mu cst (n + 1) p Y p' := by
  intro X Pr R Ch sel S mu cst u n h p Y p'
  exact xiOver_eq_XiTopG Ch sel mu cst n h p Y p'

end GlobalTheory.Mem.Col2
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

set_option autoImplicit false
noncomputable section
open TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.AlgSard

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {d : ℕ}

theorem countable_charts [SmoothOfRelativeDimension d p] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ C : Set (AlgChart p (RingHom.id ℂ) d), C.Countable ∧
      ∀ z ∈ ptsIn p (RingHom.id ℂ) U, ∃ ch ∈ C, z ∈ ch.e.source := by
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  have h1 := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  obtain ⟨k, G, ⟨hom⟩⟩ := GlobalTheory.AffCxPts.homeomorph_zeroSet X p U hU hft
  haveI : SecondCountableTopology (ptsIn p (RingHom.id ℂ) U) := hom.secondCountableTopology
  choose ch hch using fun y : ptsIn p (RingHom.id ℂ) U =>
    AlgChart.exists_mem_source (p := p) (D := d) (σ := RingHom.id ℂ) y.1
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : ptsIn p (RingHom.id ℂ) U =>
      (Subtype.val ⁻¹' (ch y).e.source : Set (ptsIn p (RingHom.id ℂ) U)))
    (fun y => (ch y).e.open_source.preimage continuous_subtype_val)
  refine ⟨ch '' T, hT.image _, fun z hz => ?_⟩
  have hm : (⟨z, hz⟩ : ptsIn p (RingHom.id ℂ) U) ∈ ⋃ i ∈ T, Subtype.val ⁻¹' (ch i).e.source := by
    rw [hTU]; exact mem_iUnion.2 ⟨⟨z, hz⟩, hch _⟩
  obtain ⟨y, hyT, hy⟩ := mem_iUnion₂.1 hm
  exact ⟨ch y, mem_image_of_mem _ hyT, hy⟩

end GlobalTheory.AlgSard


open GlobalTheory.AlgSard in
theorem GlobalTheory.AlgSard.main : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] (U : X.Opens), IsAffineOpen U →
    ∀ φ : Fin d → Γ(X, U), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ c ∉ E, ∀ (z : CxPts p (RingHom.id ℂ)) (hz : z ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
        (∀ j, CxPts.evHom hz (φ j) + c j = 0) →
        RingHom.ker (CxPts.evHom hz) ≤
          Ideal.span (Set.range fun j => φ j + ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (c j)) ⊔ RingHom.ker (CxPts.evHom hz) ^ 2 := by
  intro X p d _ U hU φ
  obtain ⟨C, hC, hcov⟩ := countable_charts (p := p) (d := d) hU
  choose E hE0 hE using fun ch : AlgChart p (RingHom.id ℂ) d => GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero X p d U ch φ
  refine ⟨⋃ ch ∈ C, E ch, (measure_biUnion_null_iff hC).2 fun ch _ => hE0 ch, ?_⟩
  intro c hc z hz hzero
  obtain ⟨ch, hchC, hzc⟩ := hcov z hz
  have hcz : c = fun j => -evHom hz (φ j) := funext fun j => by linear_combination hzero j
  have hdet : (ch.jacMat φ z).det ≠ 0 := fun h0 =>
    hc (mem_biUnion hchC (hcz ▸ hE ch z hzc hz h0))
  have key := GlobalTheory.T.ker_evalComplexPoint_le_span_jacobian X p d U hU ch φ z hzc hz hdet
  have e : (fun j => φ j + algX p U (c j)) = fun j => φ j - algX p U (evHom hz (φ j)) := by
    funext j; rw [hcz, map_neg, sub_eq_add_neg]
  rw [e]; exact key
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.exponentShape_of_integralClass_oneLetter : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  first | exact @GlobalTheory.KerStd.expShape_of_integralClass | exact GlobalTheory.KerStd.expShape_of_integralClass | (intros; apply GlobalTheory.KerStd.expShape_of_integralClass <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d → ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  first | exact @GlobalTheory.KerStd.BeData.exists_of_curveData | exact GlobalTheory.KerStd.BeData.exists_of_curveData | (intros; apply GlobalTheory.KerStd.BeData.exists_of_curveData <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.jumpIn_of_reads | exact GlobalTheory.HTW.Rec.jumpIn_of_reads | (intros; apply GlobalTheory.HTW.Rec.jumpIn_of_reads <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.wachFunctor_letters_inverseFrobenius_orbit : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  first | exact @GlobalTheory.HTW.Rec.reads_orbit_invFrob | exact GlobalTheory.HTW.Rec.reads_orbit_invFrob | (intros; apply GlobalTheory.HTW.Rec.reads_orbit_invFrob <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.lattice_in_sum_twisted_duals_fits_word : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.fits_of_isSubOfSums | exact GlobalTheory.HTW.Rec.fits_of_isSubOfSums | (intros; apply GlobalTheory.HTW.Rec.fits_of_isSubOfSums <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.lattice_twisted_dual_fits_word_few_small_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  first | exact @GlobalTheory.HTW.Rec.fits_lowCount_of_matRep | exact GlobalTheory.HTW.Rec.fits_lowCount_of_matRep | (intros; apply GlobalTheory.HTW.Rec.fits_lowCount_of_matRep <;> assumption)
end

section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.weylLattice_exists_cofactorTwist_dual : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν, ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  first | exact @GlobalTheory.ValCmp.weyl_exists_cofRel | exact GlobalTheory.ValCmp.weyl_exists_cofRel | (intros; apply GlobalTheory.ValCmp.weyl_exists_cofRel <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dualFrame_hermitian_form_trace_real_places : ∀ (D : D7) (X : Fields) (s : Seam D X) (L : PeriodPair) (Λ : AddSubgroup ℂ), L.lattice.toAddSubgroup = Λ → Function.Bijective (tauPl D) → ∀ (N N' : ℕ) (A B : Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area Λ)⁻¹) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k)) := by
  first | exact @GlobalTheory.DFrame.hOK_vecF | exact GlobalTheory.DFrame.hOK_vecF | (intros; apply GlobalTheory.DFrame.hOK_vecF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.card_cosets_eq_subspaces_kernel_residue : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  first | exact @GlobalTheory.SplitHecke.Cosets.card_cosets | exact GlobalTheory.SplitHecke.Cosets.card_cosets | (intros; apply GlobalTheory.SplitHecke.Cosets.card_cosets <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedProductCommutes_familyProduct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  first | exact @GlobalTheory.ProdReorder.commutes_multiProd | exact GlobalTheory.ProdReorder.commutes_multiProd | (intros; apply GlobalTheory.ProdReorder.commutes_multiProd <;> assumption)
end
