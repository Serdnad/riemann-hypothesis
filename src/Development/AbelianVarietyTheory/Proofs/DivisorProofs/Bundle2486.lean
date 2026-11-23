module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsBigSmallFactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedPrimeLogSumOscillationBoundLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  first | exact @GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep | exact GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep | (intros; apply GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

theorem _root_.GlobalTheory.T.exists_primeDivisor_over_source_of_birational : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_complex | exact GlobalTheory.Discrepancy.DivOver.exists_over_complex | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_complex <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

theorem _root_.GlobalTheory.T.exists_primeDivisor_over_target_of_birational : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex | exact GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem _root_.GlobalTheory.T.thetaExponents_bigSmallFactorBounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H), ∀ (F k m n B : ℕ) (Sg : ℝ) (u : GlobalTheory.AllWt.Weight Dw), Shape Dw F k m → k ≤ Dw.p + 1 → WtBd Dw k n u B Sg → ExpBd Dw k (gap Dw (thA Dw u n)) (B + 1) (F * (Sg + 2 * Dw.q * B)) (2 * B + 1) := by
  first | exact @GlobalTheory.RefSum.ThetaExp.expBd_thA | exact GlobalTheory.RefSum.ThetaExp.expBd_thA | (intros; apply GlobalTheory.RefSum.ThetaExp.expBd_thA <;> assumption)
end

section

open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.weightedPrimeLogSum_oscillationBound_le : ∀ (F N k m M : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (large₂ ll : ℝ) (S₀ R : Finset ℕ), 0 ≤ Mb → 0 ≤ Sm → (∀ q, 0 ≤ vd q) → N + 1 = k + m → m ≤ k → 1 ≤ m → 1 ≤ large₂ → 1 ≤ ll → Real.log M ≤ large₂ → Real.log N ≤ large₂ → ∑ q ∈ S₀, (1 + vd q / 2) * Real.log q ≤ 3 / 2 * large₂ → Real.log (Real.log k) ≤ ll → R.card ≤ 2 → (∀ q ∈ R, N * Real.log q / ((q : ℝ) - 1) ≤ m * large₂) → PrimeSum ((Finset.range (M + 1)).filter Nat.Prime) (fun p => if p.Prime then eOf F N k m Mb Sm vd M S₀ R p else 0) (40 * ((F * m * Mb + Sm) * large₂ * ll + F * (N : ℝ) ^ 3 * large₂ + M)) := by
  first | exact @GlobalTheory.SumBound.primeSum_eOf | exact GlobalTheory.SumBound.primeSum_eOf | (intros; apply GlobalTheory.SumBound.primeSum_eOf <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

theorem _root_.GlobalTheory.T.siegel_set_witt_frame_schwartz_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  first | exact @GlobalTheory.TorusTheta.theta_torus_le | exact GlobalTheory.TorusTheta.theta_torus_le | (intros; apply GlobalTheory.TorusTheta.theta_torus_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem _root_.GlobalTheory.T.effective_generation_canonical_nef_numberField : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.EffGen.effective_generation | exact GlobalTheory.EffGen.effective_generation | (intros; apply GlobalTheory.EffGen.effective_generation <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | exact GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | (intros; apply GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : Q.P →+* G) (n : ℕ), Q.IsStd δ η → IsLev δ (n + 1) → SemiHom (RingHom.id R) q → IsDPMorphism η δ' q → Function.Surjective q → J' = (Q.ext J).map q → (∀ b, q b = 0 ↔ b ∈ fil η (n + 1)) → ∀ (α : B →+* G) (h : SemiHom (RingHom.id R) α) (hd : IsDPMorphism δ δ' α), (∀ b, α b = q (algebraMap B Q.P b)) → RQ h hd := by
  first | exact @GlobalTheory.PDForm.rq_truncPoly | exact GlobalTheory.PDForm.rq_truncPoly | (intros; apply GlobalTheory.PDForm.rq_truncPoly <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_quasiInverse_isogeny' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → ∃ (n : ℕ) (g : B ⟶ A), 0 < n ∧ IsIsogeny g ∧ f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 B := by
  first | exact @GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny | exact GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny | (intros; apply GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.hom_torsionFree | exact GlobalTheory.AV.AbVar.hom_torsionFree | (intros; apply GlobalTheory.AV.AbVar.hom_torsionFree <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) → ¬ l ∣ deg h := by
  first | (exact @GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (exact GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (intros; apply GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel  <;> assumption)
end
