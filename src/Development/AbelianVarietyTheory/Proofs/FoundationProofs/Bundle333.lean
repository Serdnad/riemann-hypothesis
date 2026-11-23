module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle011
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle332
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle330
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle318
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle331
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle320
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle259
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
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
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

theorem _root_.GlobalTheory.T.isLieEigenbasis_baseChange_localAlgebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (l : Level H) (c : Coeff l) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (j : c.F →+* R) (g : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R')) (n : SABMap t' t (spMap g)) (τ : E →+* ℂ) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR R' ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act (FramedFlatCoordinates.chr c τ j) v → (∀ i, IsVecOver g n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act (FramedFlatCoordinates.chr c τ (g.comp j)) v' := by
  first | exact @GlobalTheory.EigBasisLocal.isEigBasis_baseChange | exact GlobalTheory.EigBasisLocal.isEigBasis_baseChange | (intros; apply GlobalTheory.EigBasisLocal.isEigBasis_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

theorem _root_.GlobalTheory.T.isLieEigenbasis_localization_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] (t : SAB H (Sp R)) (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), EigenvectorLieDegree.IsEigBasis t.act χ v → (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) → EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v' := by
  first | exact @GlobalTheory.EigBasisPrime.isEigBasis_atPrime | exact GlobalTheory.EigBasisPrime.isEigBasis_atPrime | (intros; apply GlobalTheory.EigBasisPrime.isEigBasis_atPrime <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

theorem _root_.GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)), (∀ (p : Ideal R) [p.IsPrime], ∃ (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) ∧ EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v') → EigenvectorLieDegree.IsEigBasis t.act χ v := by
  first | exact @GlobalTheory.FlatRow.isEigBasis_of_local | exact GlobalTheory.FlatRow.isEigBasis_of_local | (intros; apply GlobalTheory.FlatRow.isEigBasis_of_local <;> assumption)
end

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.siegelUnit_edgeClass_kummer_dlog_congruence : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits →
  ∀ (L n N c d : ℕ) (A₁ a₂ g B₁ b₂ h : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → b₂ ≡ N * h [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → (N : ℤ) ∣ b₂ → 1 ≤ n → n ≤ L → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → 1 < d → Nat.Coprime d (6 * N * p) →
    ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ B₁) →
  ∀ (F K Ω' : Type) [Field F] [Field K] [Field Ω'] [Algebra F K] [Algebra F Ω'] [Algebra K Ω'] [IsScalarTower F K Ω'] [IsAlgClosure K Ω'] [Normal F K]
    (e : K →+* X.K), (∀ y, e y ∈ KT X (p ^ L)) →
  ∀ (z a b : K) (ζ α β : Ω'), e z = algebraMap Ω X.K (zt ε p n) → ζ = algebraMap K Ω' z →
    e a = sgN X c N (N * p ^ L) (A₁, a₂) → e b = sgN X d N (N * p ^ L) (B₁, b₂) →
    α ^ (p ^ n) = algebraMap K Ω' a → β ^ (p ^ n) = algebraMap K Ω' b →
  ∀ (x y : (Ω' ≃ₐ[F] Ω') →* Multiplicative (ZMod (p ^ n))), (∀ t, (x t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ α t) → (∀ t, (y t).toAdd = GlobalTheory.NeedB.kum (K := F) (N := p ^ n) ζ β t) →
  ∀ η : (Ω' ≃ₐ[F] Ω') → ZMod (p ^ n), GlobalTheory.KEdge.CobOn (GlobalTheory.K4.geo F K Ω') x y η → IsLocallyConstant (fun t : GlobalTheory.K4.geo F K Ω' => η t) →
  ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s : Ω ≃ₐ[ℚ] Ω, Stab A s → s (zt ε p L) = zt ε p L → (∀ f : F, X.gal s (e (algebraMap F K f)) = e (algebraMap F K f)) →
    ∀ σ : Ω' ≃ₐ[F] Ω', (∀ k k' : K, e k' = X.gal s (e k) → σ (algebraMap K Ω' k) = algebraMap K Ω' k') →
    ∀ (w : K) (φ : HahnSeries ℚ Ω) (t : ZMod (p ^ n)), GlobalTheory.K4.IsTopW ζ x y η σ w → IsDl X A p n ((p : ℚ) ^ L) (e w) φ →
      s (zt ε p (L + n)) = zt ε p n ^ t.val * zt ε p (L + n) →
      ∀ r : ℚ, CgA A p n ((p : Ω) ^ cc * φ.coeff r)
        (s.symm (ξ r) - ξ r - (p : Ω) ^ cc * ((A₁ * h - g * B₁ : ℤ) : Ω) * (t.val : Ω) *
          coefQ (p ^ L) (cmul (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂) (smF d 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) B₁ b₂)) r) := by
  first | exact @GlobalTheory.pair_edge_dlog | exact GlobalTheory.pair_edge_dlog | (intros; apply GlobalTheory.pair_edge_dlog <;> assumption)
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.Comp

theorem lift_mem_lam {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (P : FreeAlgebra E Letter) :
    ∀ p ∈ H3.abelian₂ X l E,
      (FreeAlgebra.lift E (X.opV N l E) P p.1, FreeAlgebra.lift E (opL E N l) P p.2) ∈ H3.abelian₂ X l E := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro p hp
    convert (H3.abelian₂ X l E).smul_mem r hp using 1
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  | grade1 T =>
    intro p hp
    simpa using GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T p hp
  | mul a b ha hb =>
    intro p hp
    simpa using ha _ (hb p hp)
  | add a b ha hb =>
    intro p hp
    simpa using (H3.abelian₂ X l E).add_mem (ha p hp) (hb p hp)

theorem ssbb_of_ssPotB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ ι lam hSS
  haveI : CharZero E := RingHom.charZero ι.toRingHom
  obtain ⟨P, hPA, hP1, hP⟩ := GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv N l w ι lam hSS
  refine ⟨P, hPA, hP1, fun x hx T hT => ?_⟩
  obtain ⟨G, hG, hxG⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB ε X N l w (GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer ε X hε hj N l w hl2 hN hNl hw) x hx
  have h1 := lift_mem_lam ε X N l P (x, G) hxG
  have h2 := GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T _ h1
  have h3 := (H3.abelian₂ X l E).sub_mem h2 ((H3.abelian₂ X l E).smul_mem (lam T) h1)
  have h4 : ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        (FreeAlgebra.lift E (X.opV N l E) P x),
      (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
        (FreeAlgebra.lift E (opL E N l) P G)) ∈ H3.abelian₂ X l E := by
    simpa using h3
  exact GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial ε X hε hj N l w (by omega) inferInstance _ _ h4 (hP G hG T hT)

end GlobalTheory.KZ.Comp
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

theorem _root_.GlobalTheory.T.substUpperTriangularHahn_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  first | exact @GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | exact GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | (intros; apply GlobalTheory.CyclotomicQExpansion.sub_mul_and_one <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.kernelAtPrime_eq_sum_torsionTranslates : ∀ (D : D7), Inp D → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → 0 < Q → ∀ (P : Pair D ⊤ δ t0 Q) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (g : GA D P.a) (g' k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ∃ (b : Fin (fF D * P.a * P.d) → Matrix (Fin P.d) (Fin P.a) D.host.E) (k M : ℕ) (r : Fin k → Qbar) (s : Fin k → VC D P.a P.d), OnB D b ∧ LocBasis D p (YYl D (stdL D P.a) (stdL D P.d)) b ∧ 0 < M ∧ Nat.Coprime M p ∧ (∀ i, (M * Q) • s i ∈ LaB D (tor0 D ⊤ δ) b) ∧ (∀ i, ‖lam (r i)‖ ≤ (‖(Q : ℂ_[p])‖⁻¹) ^ (P.a * P.d)) ∧ P.W.Om g g' P.F = fun z => ∑ i, (r i : ℂ) * U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z := by
  first | exact @GlobalTheory.NormSum.kernel_eq_sum_translates | exact GlobalTheory.NormSum.kernel_eq_sum_translates | (intros; apply GlobalTheory.NormSum.kernel_eq_sum_translates <;> assumption)
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.theta_lattice_diamond_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧ IsLat 1 (thN X A N l n d b) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_isThB | exact GlobalTheory.CyclotomicQExpansion.thN_isThB | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_isThB <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslateSeries_eq_const_mul_integral_one_series : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  first | exact @GlobalTheory.ThetaUnit.tau_eq_C_mul | exact GlobalTheory.ThetaUnit.tau_eq_C_mul | (intros; apply GlobalTheory.ThetaUnit.tau_eq_C_mul <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl.KernLaws

theorem exists_finite_lift {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ κ ∈ GfC V, fin V κ = q := by
  obtain ⟨_, g, rfl⟩ := q
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  exact ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩⟩, k1, Subtype.ext k2⟩

theorem fin_mul {D : D7} (V : HSp D) (a b : GA D V) : fin V a * fin V b = fin V (a * b) :=
  (map_mul (finHom V).rangeRestrict a b).symm

theorem ratF_eq {D : D7} (V : HSp D) (γ : GQ V) : Bridge.ratF V γ = fin V γ := rfl

theorem lift_of_mem_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {κ : GA D V}
    (hκ : κ ∈ GfC V) (hk : fin V κ ∈ (levEnv V β L).J) :
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ ⟨_, hk⟩)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine ⟨⟨hκ, hk.1, Subgroup.mem_bot.1 hk.2⟩, ?_⟩
  unfold levChi
  rw [← levFn_flag1, Units.val_inv_eq_inv_val]
  rfl

theorem exists_lift_J {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L 1 κ ∧ ((((levEnv V β L).χ k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨κ, hκ, rfl⟩ := exists_finite_lift V k
  exact ⟨κ, rfl, lift_of_mem_J V β L hκ hk⟩

theorem finE_of_fin {D : D7} (V : HSp D) {κ : GA D V} {x : Bridge.Gf V} (e : fin V κ = x) :
    finE V κ = Formalism.UG.bc (swapAE D) (x : GL _ _) := by
  have : finHom V κ = x.1 := congrArg Subtype.val e
  rw [finE_eq, this]

theorem exists_lift_Q {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).Q) : ∃ κ, fin V κ = k ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) ((k : Bridge.Gf V) : GL _ _))) κ ∧
      ((((levEnv V β L).ch k)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  obtain ⟨κ, hκ, e⟩ := exists_finite_lift V k.1
  have e' := finE_of_fin V e
  refine ⟨κ, e, ⟨hκ, ?_, congrArg (rTup β L) e'⟩, ?_⟩
  · rw [e']
    exact k.2.1
  · have e2 : (levEnv V β L).ch k = levFn β (flagL L) (finE V κ) := (congrArg (levFn β (flagL L)) e').symm
    rw [Units.val_inv_eq_inv_val, e2, levChi]

theorem lift_one {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsLevelLift V β L 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem exists_actL {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (g0 : G0 L.Pg L.r) (hex : ∃ κ, IsLevelLift V β L g0 κ) : ∃ κ, IsLevelLift V β L g0 κ ∧
      ∀ F h, actL V β L g0 F h = (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  refine ⟨hex.choose, hex.choose_spec, fun F h => ?_⟩
  change actG0 V β L g0 F h = _
  unfold actG0
  rw [dite_eq_left hex]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

theorem kernA_apply (h : GA D (Vc D i)) (w : (R.cV i).W) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t h w v g =
      Datum.thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w))) := rfl

theorem kernA_mul_real (hio : R.thP_ioP) (h : GA D (Vc D i)) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) :
    kernA R i t (h * u) = kernA R i t h := by
  ext w v g
  rw [kernA_apply, kernA_apply]
  unfold Datum.thetaKO
  rw [show ((h * u, g) : GA D (Vc D i) × GA D (Wc D i)) = (h, g) * (u, 1) from Prod.ext rfl (mul_one g).symm,
    map_mul, Module.End.mul_apply, (hio i t).1 u hu, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem kern_fin (hio : R.thP_ioP) (h : GA D (Vc D i)) : kern R i t (fin (Vc D i) h) = kernA R i t h := by
  unfold kern
  have e := (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose_spec
  generalize (MonoidHom.mem_range.1 (fin (Vc D i) h).2).choose = h' at e
  have hu : h⁻¹ * h' ∈ GinfC (Vc D i) := by
    change finHom (Vc D i) (h⁻¹ * h') = 1
    rw [map_mul, map_inv, e]
    exact inv_mul_cancel _
  rw [← kernA_mul_real R i t hio h hu, mul_inv_cancel_left]

theorem kernA_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (γ : GQ (Vc D i)) (h : GA D (Vc D i)) (w : (R.cV i).W) :
    kernA R i t (γ * h) ((R.cV i).ρ γ w) = kernA R i t h w := by
  funext v g
  rw [kernA_apply, kernA_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _
    (hpt i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ρ h⁻¹ w)))).1 γ γ.2 1 (one_mem _) h g
  rwa [one_mul] at this

theorem kernA_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kernA R i t (h * κ) w v (g * κ') = c * kernA R i t h w v g := by
  rw [kernA_apply, kernA_apply, mul_inv_rev, map_mul, (hc i).1 _ (inv_mem hκ), one_mul]
  exact (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ (hω i t) _ (hpt i t _)).2 κ κ' c
    (GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ _ hθ (hω i t) _ _ _ _ _ (hpt i t) κ hκ κ' hκ' c e _) h g

theorem levChi_flag_datWp (κ' : GA D (Wc D i)) : levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ' = 1 := by
  have h2 : ext1 (flagL (R.datWp i R.triv)).P.H (flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (flagL (R.datWp i R.triv)) (finE (Wc D i) κ')) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2, show (flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem kern_rat (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP) (γ : GQ (Vc D i)) (h : Bridge.Gf (Vc D i))
    (w : (R.cV i).W) : kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = kern R i t h w := by
  obtain ⟨h', -, e⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (Bridge.ratF (Vc D i) γ * h) = kernA R i t (γ * h') := by
    rw [← e, ratF_eq, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_rat R i t hω hpt γ h' w

theorem kern_eigen (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i)) {κ' : GA D (Wc D i)} (hκ' : κ' ∈ GfC (Wc D i)) {c : ℂ}
    (e : R.ωP i t (κ, κ') (R.vP i t) = c • R.vP i t) (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    kern R i t (h * fin (Vc D i) κ) w v (g * κ') = c * kern R i t h w v g := by
  obtain ⟨h', -, e0⟩ := exists_finite_lift (Vc D i) h
  have e1 : kern R i t (h * fin (Vc D i) κ) = kernA R i t (h' * κ) := by
    rw [← e0, fin_mul, kern_fin R i t hio]
  have e2 : kern R i t h = kernA R i t h' := by rw [← e0, kern_fin R i t hio]
  rw [e1, e2]
  exact kernA_eigen R i t hθ hc hω hpt hκ hκ' e h' w v g

theorem eq_smul_of_mul_one {X Y : Type} [Monoid Y] (F F' : X → Y → ℂ) (c : ℂ) (h : ∀ v g, F v (g * 1) = c * F' v g) :
    F = c • F' := by
  funext v g
  rw [← mul_one g, h, mul_one]
  rfl

theorem eq_smul_of_mul {Y : Type} [Monoid Y] (B F F' : Y → ℂ) (a c : ℂ) (y : Y) (ha : a = 1) (h1 : ∀ g, B g = a⁻¹ * F (g * y))
    (h : ∀ g, F (g * y) = c * F' g) : B = c • F' := by
  funext g
  rw [h1, ha, inv_one, one_mul, h]
  rfl

theorem kern_level (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (h : Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) (w : (R.cV i).W) :
    kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • kern R i t h w := by
  obtain ⟨κ, e1, l1, e2⟩ := exists_lift_J (Vc D i) (R.βV i) (R.datVt i t) k
  rw [e2, ← e1]
  exact eq_smul_of_mul_one _ _ _ (kern_eigen R i t hθ hc hω hpt hio l1.1 (GfC (Wc D i)).one_mem
    (hD 1 κ 1 l1 (lift_one _ (R.βW i) (R.datWp i R.triv))) h w)

theorem kern_act (hθ : R.models_inf) (hc : R.models_cV) (hω : R.thP_ωP) (hpt : R.thP_pt_theta) (hio : R.thP_ioP)
    (hD : DatumType R i t) (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q)
    (hg : g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)))
    (hex : ∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (h : Bridge.Gf (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (kern R i t (h * q) w v) =
      ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • kern R i t h w v := by
  refine (exists_lift_Q (Vc D i) (R.βV i) (R.datVt i t) q).elim fun κ H => ?_
  refine (exists_actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 hex).elim fun κ' H' => ?_
  have l1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ := ⟨H.2.1.1, H.2.1.2.1, H.2.1.2.2.trans hg.symm⟩
  have := kern_eigen R i t hθ hc hω hpt hio l1.1 H'.1.1 (hD g0 κ κ' l1 H'.1) h w v
  rw [H.2.2, ← H.1]
  exact eq_smul_of_mul _ _ _ _ _ κ' (levChi_flag_datWp R i κ') (H'.2 _) this

end GlobalTheory.TraceIncl.KernLaws

namespace GlobalTheory.TraceIncl

open KernLaws

theorem kern_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0), R.models_inf → R.models_cV → R.thP_ωP → R.thP_pt_theta → R.thP_ioP → GlobalTheory.TraceIncl.DatumType R i t → (∀ h, GlobalTheory.TraceIncl.kern R i t (fin (Vc D i) h) = GlobalTheory.TraceIncl.kernA R i t h) ∧ (∀ (γ : GQ (Vc D i)) h w, GlobalTheory.TraceIncl.kern R i t (Bridge.ratF (Vc D i) γ * h) ((R.cV i).coef.ρ γ w) = GlobalTheory.TraceIncl.kern R i t h w) ∧ (∀ h (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) w, GlobalTheory.TraceIncl.kern R i t (h * k) w = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w) ∧ ∀ (g0 : G0 R.Pg D.R.r) (q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q), g0 = rTup (R.βV i) (R.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _)) → (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') → ∀ h w v, actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 (GlobalTheory.TraceIncl.kern R i t (h * q) w v) = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q)⁻¹ : ℂˣ) : ℂ) • GlobalTheory.TraceIncl.kern R i t h w v := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i t hθ hc hω hpt hio hD
  exact ⟨kern_fin R i t hio, kern_rat R i t hω hpt hio, kern_level R i t hθ hc hω hpt hio hD,
    kern_act R i t hθ hc hω hpt hio hD⟩

end GlobalTheory.TraceIncl
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.WeilTheta

theorem sd_of_moves (D : D7) {N : ℕ} (g : GA D N) (L : Lat D N) (h : Moves D (g : GL (Fin N) (AE D)) L) :
    SD D L := by
  obtain ⟨Lt, hLt, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x
    rw [h x, (hLt g).1 x]
  rw [this]
  exact (hLt g).2

theorem om_mem_Th_moved : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h : GA D N) (g' h' : GA D N') (L₁ L₂ : Lat D N) (L₁' L₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' F ∈ Th D (tor0 D cc δ) L₂ L₂' := by
  intro D cc δ hC N N' e0 W g h g' h' L₁ L₂ L₁' L₂' h1 h1' h2 h2' F hF
  have hD := (GlobalTheory.InducedType.induced_type D).1
  have s1 := sd_of_moves D h L₁ h1
  have s1' := sd_of_moves D h' L₁' h1'
  have s2 := sd_of_moves D _ L₂ h2
  have s2' := sd_of_moves D _ L₂' h2'
  obtain ⟨hnice, -⟩ := GlobalTheory.ThetaTriple.klat_triples D cc δ hC N N'
  have n1 := hnice _ (Or.inr ⟨L₁, L₁', s1, s1', rfl⟩)
  have n2 := hnice _ (Or.inr ⟨L₂, L₂', s2, s2', rfl⟩)
  obtain ⟨hT, hW, -⟩ := GlobalTheory.T.thetaFunctions_all_levels_closure D cc δ hC N N'
  have hFT := hT L₁ L₁' s1 s1' F hF
  have hGT := W.maps g g' F hFT
  have hfix := ((n1.mem_ThSp F).1 hF).2
  refine (n2.mem_ThSp _).2 ⟨hGT.1, fun y hy => ?_⟩
  obtain ⟨z, hz, -⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hD cc δ hC.1.1 N N' _ _ L₂ L₂' h2 h2' y hy
  have hWT : Wd D (tor0 D cc δ) y (W.Om g g' F) ∈ TT D (tor0 D cc δ) N N' := by
    rw [hz]; exact hW z _ hGT
  obtain ⟨x, hx, he⟩ := GlobalTheory.WeilEquiv.om_wd_moved D hD cc δ hC.1.1 N N' e0 W g⁻¹ (g * h) g'⁻¹ (g' * h')
    L₂ L₁ L₂' L₁' h2 h2' (by rwa [inv_mul_cancel_left]) (by rwa [inv_mul_cancel_left]) y hy _ hGT
  rw [← W.mul _ _ _ _ F hFT, inv_mul_cancel, inv_mul_cancel, W.one F hFT, hfix x hx] at he
  have h3 := congrArg (W.Om g g') he
  rwa [← W.mul _ _ _ _ _ hWT, mul_inv_cancel, mul_inv_cancel, W.one _ hWT] at h3

end GlobalTheory.WeilTheta
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.character_at_detRoot_cong_one_odd_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  first | exact @GlobalTheory.DetRootCong.char_root_eq_one | exact GlobalTheory.DetRootCong.char_root_eq_one | (intros; apply GlobalTheory.DetRootCong.char_root_eq_one <;> assumption)
end
