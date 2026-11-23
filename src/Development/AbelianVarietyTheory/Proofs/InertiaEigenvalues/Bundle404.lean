module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle384
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle202
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → (∃ g, IsGen χ K j g) ∧ ∀ g, IsGen χ K j g → ((∀ b : ℕ, IsGen χ K (j + b) (g ^ (l ^ b))) ∧ (∀ σ ∈ Gj K j, ∀ n : ℕ, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gj K n) ∧ (Gj K j : Set (GQ l)) ⊆ closure {x | ∃ h ∈ Hinf K, ∃ a : ℕ, x = h * g ^ a}) := by
  first | exact @GlobalTheory.Cyc.gen_dense | exact GlobalTheory.Cyc.gen_dense | (intros; apply GlobalTheory.Cyc.gen_dense <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation : WeilEt → RankOne → GammaOne → ∀ r, FourierMatch r := by
  first | exact @GlobalTheory.JR.fourierMatch_of_weil | exact GlobalTheory.JR.fourierMatch_of_weil | (intros; apply GlobalTheory.JR.fourierMatch_of_weil <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcrisRadius_pos_definite : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → 0 < gC l ρ x := by
  first | exact @GlobalTheory.PMon.Gauss.gC_pos_target | exact GlobalTheory.PMon.Gauss.gC_pos_target | (intros; apply GlobalTheory.PMon.Gauss.gC_pos_target <;> assumption)
end

section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.inertia_compatible_conjugation_representation : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  first | exact @GlobalTheory.ConjPoly.conj_inertia | exact GlobalTheory.ConjPoly.conj_inertia | (intros; apply GlobalTheory.ConjPoly.conj_inertia <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i), PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  first | exact @GlobalTheory.Pass.CutEq.main | exact GlobalTheory.Pass.CutEq.main | (intros; apply GlobalTheory.Pass.CutEq.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.CrisPlus

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem plus_phi {b : P.R.B} (h : Plus T b) : Plus T (P.φB b) := by
  obtain ⟨N, x, hx⟩ := h
  refine ⟨N, GlobalTheory.MemLoc.phiA l x, ?_⟩
  have e : (l : P.R.B) ^ N * P.φB b = P.φB ((l : P.R.B) ^ N * b) := by
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.frob, hx]
  exact GlobalTheory.CrisMaps.φB_phiA l x

theorem plus_iterate {b : P.R.B} (h : Plus T b) (j : ℕ) : Plus T (P.φB^[j] b) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact plus_phi T ih

theorem plus_add_mul {a b : P.R.B} (ha : Plus T a) (hb : Plus T b) : Plus T (a + b) ∧ Plus T (a * b) := by
  obtain ⟨N, x, hx⟩ := ha
  obtain ⟨M, y, hy⟩ := hb
  refine ⟨⟨N + M, (l : Formalism.Per.Acris l) ^ M * x + (l : Formalism.Per.Acris l) ^ N * y, ?_⟩, ⟨N + M, x * y, ?_⟩⟩
  · have e : (l : P.R.B) ^ (N + M) * (a + b) = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * a) + (l : P.R.B) ^ N * ((l : P.R.B) ^ M * b) := by
      ring
    rw [e, map_add (f := _), map_mul T.eB ((l : P.R.B) ^ M) ((l : P.R.B) ^ N * a),
      map_mul T.eB ((l : P.R.B) ^ N) ((l : P.R.B) ^ M * b), hx, hy]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  · have e : (l : P.R.B) ^ (N + M) * (a * b) = ((l : P.R.B) ^ N * a) * ((l : P.R.B) ^ M * b) := by ring
    rw [e, map_mul, hx, hy, map_mul]

theorem plus_alg (q : ℚ_[l]) : Plus T (algebraMap ℚ_[l] P.R.B q) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖q‖ hl
  have hz : ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
    rw [norm_mul, Padic.norm_p_pow]
    have hp : (0 : ℝ) < (l : ℝ) ^ N := by positivity
    rw [zpow_neg, zpow_natCast]
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact hN.le
  let z : ℤ_[l] := ⟨(l : ℚ_[l]) ^ N * q, hz⟩
  refine ⟨N, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z), ?_⟩
  have e : (l : P.R.B) ^ N * algebraMap ℚ_[l] P.R.B q = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
    change _ = algebraMap ℚ_[l] P.R.B ((l : ℚ_[l]) ^ N * q)
    rw [map_mul, map_pow, map_natCast]
  rw [e, T.zB, GlobalTheory.RingIface.zB_eq_aB_zA l z, GlobalTheory.RingIface.aB_eq_alg l]

theorem plus_ainf (x : Formalism.Per.Ainf l) : Plus T (T.eB.symm (Formalism.Per.aB l x)) :=
  ⟨0, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) x, by rw [pow_zero, one_mul, RingEquiv.apply_symm_apply]; exact GlobalTheory.RingIface.aB_eq_alg l x⟩

theorem plus_alt : Plus T P.tB := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  exact ⟨0, C.t, by rw [pow_zero, one_mul, hC.t]; rfl⟩

theorem plus_fil {b : P.R.B} (h : Plus T b) : P.ιB b ∈ Fil P 0 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨N, x, hx⟩ := h
  obtain ⟨u, hu⟩ := (GlobalTheory.MemLoc.isUnit_l_BdRp l).exists_left_inv
  have e1 : T.eD (P.ιB ((l : P.R.B) ^ N * b)) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (C.j x) := by
    rw [hC.ι, hx, C.ι_j]
  simp only [map_mul, map_pow, map_natCast] at e1
  have e2 : T.eD (P.ιB b) = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N * C.j x) := by
    calc T.eD (P.ιB b)
        = (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) u * (l : Formalism.Per.BdR l)) ^ N * T.eD (P.ιB b) := by
          rw [← map_natCast (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)) l, ← map_mul, hu, map_one, one_pow, one_mul]
      _ = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (u ^ N) * ((l : Formalism.Per.BdR l) ^ N * T.eD (P.ιB b)) := by
          rw [map_pow]; ring
      _ = _ := by rw [e1, ← map_mul]
  show P.ιB b ∈ (P.PD (botExt l)).Fil 0
  refine (T.fil (botExt l) 0 _).2 ?_
  rw [e2]
  exact GlobalTheory.RingIface.alg_mem_FilD_zero l _

theorem plus_props : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    (∀ b, Plus T b → Plus T (P.φB b)) ∧ (∀ b, Plus T b → ∀ j, ev P j b ∈ Fil P 0) ∧
    (∀ a b, Plus T a → Plus T b → Plus T (a + b) ∧ Plus T (a * b)) ∧
    (∀ q : ℚ_[l], Plus T (algebraMap ℚ_[l] P.R.B q)) ∧
    (∀ x : Formalism.Per.Ainf l, Plus T (T.eB.symm (Formalism.Per.aB l x))) ∧ Plus T P.tB := by
  intro l _ P AI T
  exact ⟨fun b h => plus_phi T h, fun b h j => plus_fil T (plus_iterate T h j), fun a b ha hb => plus_add_mul T ha hb,
    plus_alg T, plus_ainf T, plus_alt T⟩

end GlobalTheory.PMon.CrisPlus
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) → ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  first | exact @GlobalTheory.PMon.unr_of_iterate_fixed | exact GlobalTheory.PMon.unr_of_iterate_fixed | (intros; apply GlobalTheory.PMon.unr_of_iterate_fixed <;> assumption)
end

section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleFrobDual

theorem charpoly_smul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • M).charpoly = (m.map fun β => X - C (c * β)).prod := by
  have h1 := GlobalTheory.ConjPoly.charpoly_smul_inv M N h m 1 hM
  have h2 := GlobalTheory.ConjPoly.charpoly_smul_inv N M (mul_eq_one_comm.1 h) (m.map (·⁻¹)) c
    (by rw [one_smul] at h1; rw [h1, Multiset.map_map]; simp)
  rw [h2, Multiset.map_map]
  simp

theorem cyclotomicChar_frobenius_eq_normPlace {D : D7} (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∉ placesOver D.host.E (D.ntw.l i)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A v)
    {σ : Gen.GE D.nd} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  have h := cycZ_of_isFrob hv hA hσ
  change algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : _) = _
  rw [h, map_natCast]

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TripleFrobDual
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates : WeilRes := by
  first | exact @GlobalTheory.PMon.weilRes | exact GlobalTheory.PMon.weilRes | (intros; apply GlobalTheory.PMon.weilRes <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.CupAbove

theorem cup_mem_of_span {R Γ M M' P : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (π : Representation R Γ M) (π' : Representation R Γ M') (μ : Representation R Γ P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (π g x) (π' g y) = μ g (b x y)) (hc : ContAction π')
    (W : Submodule R (Z2 μ)) (hW : (B2 μ).comap (Z2 μ).subtype ≤ W) (S : Set (H1 π)) (S' : Set (H1 π'))
    (h : ∀ s ∈ S, ∀ s' ∈ S', ∃ z z', s = Submodule.Quotient.mk z ∧ s' = Submodule.Quotient.mk z' ∧
      cupCocycleZ1Z1 π π' μ b hb hbe hc z z' ∈ W)
    (x : Z1 π) (y : Z1 π') (hx : Submodule.Quotient.mk x ∈ Submodule.span R S)
    (hy : Submodule.Quotient.mk y ∈ Submodule.span R S') : cupCocycleZ1Z1 π π' μ b hb hbe hc x y ∈ W := by
  have e : ∀ z z', cupProductH1H1 π π' μ b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.mkQ _ (cupCocycleZ1Z1 π π' μ b hb hbe hc z z') := fun _ _ => rfl
  have h1 : Submodule.map₂ (cupProductH1H1 π π' μ b hb hbe hc) (Submodule.span R S) (Submodule.span R S') ≤
      W.map (Submodule.mkQ _) := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨s, hs, s', hs', rfl⟩
    obtain ⟨z, z', rfl, rfl, hz⟩ := h s hs s' hs'
    exact ⟨_, hz, (e z z').symm⟩
  have h2 := h1 (Submodule.apply_mem_map₂ _ hx hy)
  rw [e, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hW] at h2
  exact h2

def addCob {K Γ A : Type} [CommRing K] [Group Γ] [TopologicalSpace Γ] [TopologicalSpace K] [DiscreteTopology K]
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (μ : Representation K Γ K) (χ : Γ → A) : Submodule K (Z2 μ) where
  carrier := {z | ∀ lam : K →+ A, ∃ a : Γ → A, Continuous a ∧ ∀ g h, lam (z.1 (g, h)) = χ g * a h - a (g * h) + a g}
  zero_mem' := fun lam => ⟨0, continuous_const, fun g h => by simp⟩
  add_mem' := fun {z z'} hz hz' lam => by
    obtain ⟨a, ha, h1⟩ := hz lam
    obtain ⟨a', ha', h2⟩ := hz' lam
    refine ⟨a + a', ha.add ha', fun g h => ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), h1, h2]
    ring
  smul_mem' := fun k z hz lam => hz (lam.comp (AddMonoidHom.mulLeft k))

theorem map_padic_mul {l : ℕ} [Fact l.Prime] {K : Type} [CommRing K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
    (lam : K →+ ZMod (l ^ 1)) (u : ℤ_[l]) (k : K) : lam (φ u * k) = PadicInt.toZModPow 1 u * lam k := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 u)
  have h1 : φ u = (u.appr 1 : ℕ) := by
    have := congrArg φ hc
    rw [map_mul, map_pow, map_natCast, hl, map_sub, map_natCast, pow_one, mul_zero] at this
    exact sub_eq_zero.1 this.symm
  have h2 : PadicInt.toZModPow 1 u = (u.appr 1 : ℕ) := rfl
  rw [h1, h2, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

section Galois

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}

theorem mk_eq_zero_iff (w : Z2 (muLoc F l 1 A)) : (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 ↔
    ∃ a : Dec (F := F) A → ZMod (l ^ 1), Continuous a ∧ ∀ g h : Dec (F := F) A, w.1 (g, h) =
      PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * a h - a (g * h) + a g := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem]
  refine exists_congr fun a => and_congr_right fun _ => ⟨fun e g h => (congrFun e (g, h)).symm, fun e => ?_⟩
  funext ⟨g, h⟩
  exact (e g h).symm

variable {K : Type} [CommRing K] [TopologicalSpace K] [DiscreteTopology K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
  (μ : Representation K (Dec (F := F) A) K) (hμ : ∀ g k, μ g k = φ ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * k)

include hl hμ

theorem exists_push (z : Z2 μ) (lam : K →+ ZMod (l ^ 1)) : ∃ w : Z2 (muLoc F l 1 A), ∀ g h, w.1 (g, h) = lam (z.1 (g, h)) := by
  refine ⟨⟨fun p => lam (z.1 p), continuous_of_discreteTopology.comp z.2.1, fun g h k => ?_⟩, fun _ _ => rfl⟩
  have e := congrArg lam (z.2.2 g h k)
  rw [map_sub, map_add (f := _), map_sub, hμ, map_padic_mul φ hl, map_zero] at e
  exact e

theorem coboundaries_le_cyclotomic_additive : (B2 μ).comap (Z2 μ).subtype ≤
    addCob μ (fun g => PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) := by
  rintro z ⟨c, hc, e⟩ lam
  refine ⟨fun g => lam (c g), continuous_of_discreteTopology.comp hc, fun g h => ?_⟩
  have e' : z.1 (g, h) = μ g (c h) - c (g * h) + c g := (congrFun e (g, h)).symm
  rw [e', map_add (f := _), map_sub, hμ, map_padic_mul φ hl]

end Galois

theorem mk_eq_zero_of_rational (hT : LocalTateDuality) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (β : O →+ ZMod (l ^ 1)) (z : Dec (F := F) A → Dec (F := F) A → O) (f : Dec (F := F) A → ↥Bw.LL.1) (hf : Continuous f)
    (hz : ∀ g h, Bw.toLL (z g h) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g)
    (w : Z2 (muLoc F l 1 A)) (hw : ∀ g h, w.1 (g, h) = β (z g h)) :
    (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  have : IsGalois F Ω := {}
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have : IsTopologicalRing ↥Bw.LL.1 := inferInstanceAs (IsTopologicalRing ↥Bw.LL.1.toSubfield.toSubring)
  have hr : Set.range Bw.toLL = Set.range (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1) :=
    Bw.eO.surjective.range_comp (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1)
  obtain ⟨n, a, ha, e⟩ := GlobalTheory.T.exists_zmod_pow_coboundary_of_rational_coboundary' (Dec (F := F) A) l (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) O ↥Bw.LL.1 Bw.toLL
    (GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw) (hr ▸ GlobalTheory.LocalIntegers.isOpen_integers l Bw.LL)
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    (fun x => by
      obtain ⟨n, hn⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL (fun (_ : Unit) (_ : Fin 1) => x)
        continuous_const
      exact ⟨n, hr ▸ ⟨⟨_, hn () 0⟩, rfl⟩⟩) β z f hf hz
  refine GlobalTheory.T.mu_cocycle_coboundary_lift hT F Ω l A v hA n w a ha fun g h => ?_
  rw [hw]
  exact e g h

section Matrices

variable {Γ O K : Type} [Group Γ] [CommRing O] [CommRing K] [Algebra O K] {r : ℕ}

theorem repOn_one_apply (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    repOn ρ (1 : Γ →* Kˣ) K g m = (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem dot_equivariant (T T' : Matrix (Fin r) (Fin r) O) (hT : IsUnit T.det) (u : O) (h : T' = u • T⁻¹.transpose)
    (x y : Fin r → K) :
    (T.map (algebraMap O K)).mulVec x ⬝ᵥ (T'.map (algebraMap O K)).mulVec y = algebraMap O K u * (x ⬝ᵥ y) := by
  have e : (T.map (algebraMap O K)).transpose * T'.map (algebraMap O K) = algebraMap O K u • 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.mul_smul, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hT, Matrix.transpose_one]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_generators (T : Matrix (Fin r) (Fin r) O) (y y' : Fin r → O) (b b' : K) :
    (fun a => algebraMap O K (y a) • b) ⬝ᵥ (T.map (algebraMap O K)).mulVec (fun a => algebraMap O K (y' a) • b') =
      (b * b') * algebraMap O K (y ⬝ᵥ T.mulVec y') := by

  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

end Matrices

theorem cup_eq_zero_above : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  intro hT D N X bkP i s _ K _ _ _ _ hK ρ hρ v hv x y hx hy lam w hw
  let φ : ℤ_[X.l i] →+* K := (algebraMap (X.O0 i) K).comp (algebraMap ℤ_[X.l i] (X.O0 i))
  have hl : ((X.l i : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap (X.O0 i) K)]
    exact hK _ (GlobalTheory.PrimeToInertia.l_mem i)
  let μ : Representation K (DecV N v) K :=
    charRep (((Units.map (algebraMap (X.O0 i) K).toMonoidHom).comp (eps0 X i)).comp (DecV N v).subtype)
  have hμ : ∀ (g : DecV N v) k, μ g k = φ ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) * k := fun _ _ => rfl
  have hbe : ∀ (g : DecV N v) (m m' : Fin D.R.r → K),
      dotProductBilin K K (((red i K (Tgl i s)).comp (DecV N v).subtype) g m) (((red i K ρ).comp (DecV N v).subtype) g m') =
        μ g (dotProductBilin K K m m') := by
    intro g m m'
    change red i K (Tgl i s) g m ⬝ᵥ red i K ρ g m' = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (m ⬝ᵥ m')
    rw [repOn_one_apply, repOn_one_apply]
    refine dot_equivariant _ _ (Matrix.isUnits_det_units _) _ ?_ m m'
    rw [hρ, Tgl_coe]
    rfl
  have hc : ContAction ((red i K ρ).comp (DecV N v).subtype) := by
    have : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
      by_contra hn
      exact ha.ne_zero (hK a hn)⟩
    have h1 : ContAction (red i K ρ) := by
      refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun c hc => ?_⟩
      · simp_rw [show ∀ g, _ from hρ]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
      · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hc
        rw [hc, zero_smul]
    exact h1.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop)
  rw [bkOn, dite_eq_left hv] at hx hy
  have key := cup_mem_of_span _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc _
    (coboundaries_le_cyclotomic_additive φ hl μ hμ) _ _ (by
      rintro _ ⟨z, c, t, b, h1, h2, h3, rfl⟩ _ ⟨z', c', t', b', h1', h2', h3', rfl⟩
      refine ⟨z, z', rfl, rfl, fun lam => ?_⟩
      obtain ⟨f, hf, e⟩ := GlobalTheory.T.cup_coboundary_alt D N X bkP i s ‹_› ρ hρ v hv c c' t t' h1 h1' h2 h2'
      obtain ⟨w, hw⟩ := exists_push φ hl μ hμ
        (cupCocycleZ1Z1 _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc z z') lam
      simp_rw [← hw]
      refine (mk_eq_zero_iff w).1 (mk_eq_zero_of_rational hT (N.plOm.2 v) (bkP.br i v hv)
        ((lam.comp (AddMonoidHom.mulLeft (b * b'))).comp (algebraMap (X.O0 i) K).toAddMonoidHom) _ f hf e w fun g h => ?_)
      rw [hw]
      change lam (z.1 g ⬝ᵥ red i K ρ g (z'.1 h)) = lam (b * b' * algebraMap (X.O0 i) K _)
      rw [repOn_one_apply, show z.1 g = _ from funext (h3 g), show z'.1 h = _ from funext (h3' h), dot_generators])
    x y hx hy
  obtain ⟨a, ha, e⟩ := key lam
  exact (mk_eq_zero_iff w).2 ⟨a, ha, fun g h => (hw g h).trans (e g h)⟩

end GlobalTheory.CupAbove
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

theorem _root_.GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  first | exact @GlobalTheory.PendOf.EigSpanProof.main | exact GlobalTheory.PendOf.EigSpanProof.main | (intros; apply GlobalTheory.PendOf.EigSpanProof.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

theorem _root_.GlobalTheory.T.chebotarevInductionGrowBound_of_presentation : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmS bkP → ∀ (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → Grow bkP i s := by
  first | exact @GlobalTheory.Growth.grow | exact GlobalTheory.Growth.grow | (intros; apply GlobalTheory.Growth.grow <;> assumption)
end
