module

import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle008
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle239
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle252
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle178
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle164
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle154
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle187
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle176
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle258
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle175
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle240
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

namespace GlobalTheory.CompanionTheory.MatInv

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chart (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiffOn_chartInv (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chart n).symm (Ring.inverse (chart n M)))
      {M | IsUnit (chart n M)} := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ Ring.inverse (GlobalTheory.CompanionTheory.MatInv.chart n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact ((GlobalTheory.CompanionTheory.MatInv.chart n).symm.contDiff.contDiffAt.comp M
    (h1.comp M (GlobalTheory.CompanionTheory.MatInv.chart n).contDiff.contDiffAt)).contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiffOn_inv : ∀ {n : ℕ}, ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  apply PositivityTheory.RgBcC.LfSt.Kchain.KcInv.inv_contDiffOn <;> assumption

end GlobalTheory.CompanionTheory.MatInv
end
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.local_binary_gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice | exact GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice <;> assumption)
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.local_binary_gram_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses | exact GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses | (intros; apply GlobalTheory.CompanionTheory.SW.FibreCpt.fibre_masses <;> assumption)
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.ContAutForm

open GlobalTheory.CuspRep

theorem continuous_of_isAutForm_totallyComplex (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ)
    (φ : Sm E N) (h : IsAutForm φ) : Continuous φ.1 :=
  h.continuous

end GlobalTheory.CompanionTheory.ContAutForm
end

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliGelfand

theorem etr_eq_gelfVal_of_capelli :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
      (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E →
      (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) →
      ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  intro V _ _ m E χ v hE hq
  have hcap : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∏ s, (Y + χ s) := by
    intro Y
    rfl
  have hP : ∀ u : ℂ, Formalism.REAL.qdet E u v =
      (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).eval u • v := by
    intro u
    have h := hq (u - (m : ℂ) / 2)
    have h1 : u - (m : ℂ) / 2 + (((m + 1 : ℕ) : ℂ) - 1) / 2 = u := by
      push_cast
      ring
    rw [h1, hcap] at h
    rw [h, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  intro k
  induction k using Nat.strong_induction_on with
  | _ N ih =>
    rw [GlobalTheory.T.trace_element_capelli_recursion V m E hE _ v hP N (fun k => GlobalTheory.Dec.gelfVal χ k) (fun k hk => ih k hk)]
    rw [GlobalTheory.T.trace_element_gelfand_polynomial_formula m χ N]

end GlobalTheory.CompanionTheory.CapelliGelfand
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.parabolicInd_equiv_levi_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | exact GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | (intros; apply GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles.Assembly

theorem arith {a s p1 b h1 lam p2 h2 h0' q0 h0 m arch : ℕ}
    (h4 : a * s * p1 = b * h1 * lam) (h5 : s * p2 = h2 * h0') (h6 : p1 = q0 * p2 * m)
    (h7 : h0 * h2 * m = h1 * arch) (hh1 : 0 < h1) :
    a * h0' * q0 * arch = b * h0 * lam := by
  apply Nat.eq_of_mul_eq_mul_right hh1
  calc a * h0' * q0 * arch * h1 = a * h0' * q0 * (h1 * arch) := by ring
    _ = a * h0' * q0 * (h0 * h2 * m) := by rw [h7]
    _ = h0 * (a * (h2 * h0') * q0 * m) := by ring
    _ = h0 * (a * (s * p2) * q0 * m) := by rw [h5]
    _ = h0 * (a * s * (q0 * p2 * m)) := by ring
    _ = h0 * (a * s * p1) := by rw [h6]
    _ = h0 * (b * h1 * lam) := by rw [h4]
    _ = b * h0 * lam * h1 := by ring

theorem card_pi_submodule {R ι : Type} [Semiring R] [Fintype ι] {X : ι → Type}
    [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)] (L : ∀ i, Submodule R (X i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
      invFun := fun y => ⟨fun i => (y i).1, fun i _ => (y i).2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem greenbergWiles_of_poitouTate : PoitouTateNormalised → GlobalEulerChar → LocalTateDuality →
    LocalEulerChar → LocalFiniteness → GreenbergWiles := by
  intro hPT hGEC hLTD hLEC hLF
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hl hS hρ μ hμ Av hAv c hc L
  classical
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfinD : Finite (TDual (ZMod (l ^ r)) M) := GlobalTheory.CompanionTheory.DualFin.finite_dual_all (ZMod (l ^ r)) M
  obtain ⟨inv, hinv, hnine, hsha⟩ :=
    GlobalTheory.CompanionTheory.GreenbergWiles.poitouTate_instance F Ω l r M S Av μ ρ hρ hμ hPT hl hr hS hAv
  have hρ' : ContAction (twDual μ ρ) := GlobalTheory.T.selmer_group_dual_exact F Ω l r M S Av μ ρ hρ hμ
  have hj : ∀ v, Function.Injective (invAt S Av μ hμ inv v) := fun v =>
    ((hinv _ _ (hAv v)).comp (toMuLoc_bijective S Av μ hμ v)).injective
  have hlf := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hLF hr hAv
  have hlf' := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r (TDual (ZMod (l ^ r)) M)
    S Av μ (twDual μ ρ) hρ' hLF hr hAv
  haveI : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v => (hlf v).2.1
  haveI : ∀ v : S, Finite (H2 (ρ.comp (locFam S Av v))) := fun v => (hlf v).2.2
  haveI : ∀ v : S, Finite (H1 ((twDual μ ρ).comp (locFam S Av v))) := fun v => (hlf' v).2.1
  obtain ⟨hH0, hH1, hH2, hH0', hH1'⟩ := GlobalTheory.T.greenberg_wiles_formula F Ω l r M S Av μ ρ hρ
    (invAt S Av μ hμ inv) hμ hfinD hLF hr hAv hnine hsha
  have hloc := GlobalTheory.T.galois_cohomology_localization_exact F Ω l r M S Av μ ρ hρ hμ hLTD hr inv hinv hAv
  have hB := GlobalTheory.CompanionTheory.Pairing.sum_perfect (ZMod (l ^ r)) S (fun v => H1 (ρ.comp (locFam S Av v)))
    (fun v => H1 ((twDual μ ρ).comp (locFam S Av v)))
    (fun v => (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂
      (invAt S Av μ hμ inv v)) (fun v => (hloc v).1) (fun v => (hloc v).2)
  have hBi : Function.Injective (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ) := by
    unfold sumPair; rw [LinearMap.coe_sum]; exact hB.1
  have hBf : Function.Injective (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ).flip := by
    unfold sumPair; exact hB.2
  have hrange := GlobalTheory.T.tate_shafarevich_duality_h1 F Ω l r M S Av μ ρ hρ (invAt S Av μ hμ inv) hnine
  have count := GlobalTheory.CompanionTheory.Counting.card_comap_mul_card_ker_mul_card_eq (l ^ r) (H1 ρ)
    (H1 (twDual μ ρ)) (∀ v : S, H1 (ρ.comp (locFam S Av v)))
    (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v)))
    (sumPair S Av μ (invAt S Av μ hμ inv) ρ hρ) hBi hBf (loc1 S Av ρ) (loc1 S Av (twDual μ ρ))
    hrange (Submodule.pi Set.univ L)
  have hsel := GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ
  have hsel' := GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker F Ω l r (TDual (ZMod (l ^ r)) M) S Av μ
    (twDual μ ρ) hρ'
  rw [← GlobalTheory.CompanionTheory.Duality.pi_perpCond_eq_annihilator_sumPair F Ω l r M S Av μ ρ hρ _ hj L,
    ← hsel.1 L, ← hsel'.1, ← hsel'.2.1, card_pi_submodule L, hsha.1.2.2.2] at count
  have h5 := GlobalTheory.T.poitou_tate_nine_term_exact F Ω l r M S Av μ ρ hρ (invAt S Av μ hμ inv) hLF hr hAv hnine hH2 hH0'
  have h7 := hGEC F Ω l r M S ρ hr hS hρ c hc
  have hdeg : ∑ v : S, (if ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then locDeg v.1 else 0) =
      Module.finrank ℚ F := by
    rw [← GlobalTheory.T.sum_local_degrees_over_l F l (S.filter fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)
      (fun v => by rw [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hS v h, h⟩⟩),
      Finset.sum_filter]
    exact Finset.sum_coe_sort S (fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0)
  have hle := GlobalTheory.CompanionTheory.Gal.localEuler_places F Ω l r M S Av μ ρ hρ hLEC hr hAv
  have h6 : Nat.card (∀ v : S, H1 (ρ.comp (locFam S Av v))) =
      (∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v)))) *
        Nat.card (∀ v : S, H2 (ρ.comp (locFam S Av v))) * Nat.card M ^ Module.finrank ℚ F := by
    have hv : ∀ v : S, Nat.card (H1 (ρ.comp (locFam S Av v))) =
        Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v))) *
          Nat.card M ^ (if ((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal then locDeg v.1 else 0) := by
      intro v
      split_ifs with h
      · exact (hle v).1 h
      · rw [pow_zero, mul_one]; exact (hle v).2 h
    rw [Nat.card_pi, Nat.card_pi, Finset.prod_congr rfl (fun v _ => hv v),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  exact arith count h5 h6 h7 Nat.card_pos

end GlobalTheory.CompanionTheory.GreenbergWiles.Assembly
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.levi_intersection_conjugate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), Nonempty (Representation.Equiv ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.GeomCell.cell_iso | exact GlobalTheory.CompanionTheory.GeomCell.cell_iso | (intros; apply GlobalTheory.CompanionTheory.GeomCell.cell_iso <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing


theorem _root_.GlobalTheory.T.compact_span_finite_dim_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | exact GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span | (intros; apply GlobalTheory.CompanionTheory.HCRep.liB_skew_mem_span <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem sk_skew {n : ℕ} (p : Ix n) : (sk p)ᴴ = -sk p := by
  obtain ⟨b, i, j⟩ := p
  have hc : ∀ (a b : Fin n) (c : ℂ), (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
    intro a b c
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]
  cases b
  · simp [sk, Matrix.conjTranspose_add, hc, Matrix.single_neg, add_comm]
  · simp [sk, Matrix.conjTranspose_sub, hc]

theorem Rd_Rd_of_act {n : ℕ} (E : KMod n) (Y : Mat n) (B : E.V →L[ℂ] E.V)
    (hB : ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) (f : Mat n → E.V) (hf : f ∈ CE E)
    (g : Mat n) (hg : g ∈ GLs n) : Rd Y (Rd Y f) g = B (B (f g)) := by
  have hnhds : GLs n ∈ nhds g := isOpen_GLs.mem_nhds hg
  have hev : Rd Y f =ᶠ[nhds g] (B.restrictScalars ℝ) ∘ f := by
    filter_upwards [hnhds] with y hy
    simpa using hB f hf y hy
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt hnhds).differentiableAt (by simp)
  have hfd : fderiv ℝ (Rd Y f) g = (B.restrictScalars ℝ).comp (fderiv ℝ f g) := by
    rw [hev.fderiv_eq]
    exact ((B.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  have h1 : Rd Y (Rd Y f) g = B (Rd Y f g) := by
    change fderiv ℝ (Rd Y f) g (g * Y) = B (fderiv ℝ f g (g * Y))
    rw [hfd]
    rfl
  rw [h1, hB f hf g hg]

theorem om_section {n : ℕ} (E : KMod n) : ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  choose B hB using fun p : Ix n => rd_skew_eq_const E (sk p) (sk_skew p)
  refine ⟨-(1 / 4 : ℂ) • ∑ p, B p * B p, fun f hf g hg => ?_⟩
  rw [OmDec.Om_eq_squares f hf.1 g hg, sub_eq_add_neg]
  congr 1
  have h : ∀ p, Rd (sk p) (Rd (sk p) f) g = B p (B p (f g)) := fun p =>
    Rd_Rd_of_act E (sk p) (B p) (hB p) f hf g hg
  simp only [h, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.neg_apply, neg_smul]
  rfl

end GlobalTheory.CompanionTheory.WaveSpd
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.energy_density_smooth : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v → Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | exact GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_dens_inner <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTHodge

theorem exists_lubinTateChar : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 :=
  fun K => GlobalTheory.CompanionTheory.LTHodge.CharEx.exists_ltChar K

end GlobalTheory.CompanionTheory.LTHodge
end
end
