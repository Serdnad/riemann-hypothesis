module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle123
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle066
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle275
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HtOrth

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped NNReal

variable {D : D7}


open Classical in
def vInf (w : InfinitePlace D.host.F) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun p : EmbOver D.host.E w × Fin n =>
    ‖infEmb p.1 (compInf D.host.F D.host.E w (x p.2))‖₊

def vFin (v : HeightOneSpectrum (𝓞 D.host.F)) {n : ℕ} (x : Fin n → AE D) : ℝ≥0 :=
  Finset.univ.sup fun i => absFin D.host.F v (compFin D.host.F D.host.E v (x i))

def vsize {n : ℕ} (x : Fin n → AE D) : ℝ :=
  (((∏ w, vInf w x) * ∏ᶠ v, vFin v x : ℝ≥0) : ℝ)

def seen (V : HSp D) (g : GA D V) (ξ : Fin V.rank → D.host.E) : Fin V.rank → AE D :=
  mt V g⁻¹ *ᵥ fun i => incA D (ξ i)

theorem vsize_nonneg {n : ℕ} (x : Fin n → AE D) : 0 ≤ vsize x := NNReal.coe_nonneg _

end GlobalTheory.HtOrth

end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.volM_blocks_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (A D : Type) [Fintype A] [Fintype D] (S₁₁ : Set (Matrix A A k)) (S₁₂ : Set (Matrix A D k))
    (S₂₁ : Set (Matrix D A k)) (S₂₂ : Set (Matrix D D k)),
    volM ν (A ⊕ D) (A ⊕ D)
        {x | x.toBlocks₁₁ ∈ S₁₁ ∧ x.toBlocks₁₂ ∈ S₁₂ ∧ x.toBlocks₂₁ ∈ S₂₁ ∧ x.toBlocks₂₂ ∈ S₂₂} =
      volM ν A A S₁₁ * volM ν A D S₁₂ * volM ν D A S₂₁ * volM ν D D S₂₂ := by
  first | exact @GlobalTheory.blockVolume_prod | exact GlobalTheory.blockVolume_prod | (intros; apply GlobalTheory.blockVolume_prod <;> assumption)
end

section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.parameters_spacing_and_gap : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {H : ℝ}, 2 ≤ H → H ≤ G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 → (∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a c, a < c → 2 ≤ lam a - lam c) ∧ (∀ a c, a < c → 2 ≤ mu a - mu c) ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam H ∧ Formalism.QuantumDeterminants.GapAtLeast ε' mu H := by
  first | exact @GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing | exact GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing | (intros; apply GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_normalizedBorelJacquet_unramified : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  first | exact @GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | exact GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult | (intros; apply GlobalTheory.SmGL.UnramFixed.jhMult_jacB_eq_expMult <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.parabolicInduction_detCharacters_rank_one_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α] (c : α → Type) [∀ i, Fintype (c i)] [∀ i, DecidableEq (c i)] (g : (Σ i, c i) ≃ Unit) (ψ : α → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Nonempty ((multiProd g fun i => detRep (c i) (ψ i)).Equiv (detRep Unit (ψ (g.symm ()).1))) := by
  first | exact @GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | exact GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit | (intros; apply GlobalTheory.SmGL.RankOneProduct.nonempty_equiv_multiProd_unit <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.exists_exponent_of_iwahori_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → fixed π (iwahori k (Fin n)) ≠ ⊥ → ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  first | exact @GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | exact GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | (intros; apply GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.jacquetModule_map_injective_of_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W) (f : π₁.IntertwiningMap π), IsSmooth π → Function.Injective f → Function.Injective (jacMap e f) := by
  first | exact @GlobalTheory.JacInj.jacMap_injective | exact GlobalTheory.JacInj.jacMap_injective | (intros; apply GlobalTheory.JacInj.jacMap_injective <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.exists_equiv_detCharacter_of_irreducible_rank_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Type) [Fintype c] [DecidableEq c] [Subsingleton c] (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL c k) V), IsSmooth σ → σ.IsIrreducible → ∃ ψ : kˣ →* ℂˣ, IsSmoothChar ψ ∧ Nonempty (σ.Equiv (detRep c ψ)) := by
  first | exact @GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | exact GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep | (intros; apply GlobalTheory.SmGL.RankLeOne.exists_equiv_detRep <;> assumption)
end

section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.interlaced_signed_parameters : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  first | exact @GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 | exact GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 | (intros; apply GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 <;> assumption)
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL.CuspSegment

def intervals (l d : ℕ) : (Σ _ : Fin l, Fin d) ≃ Fin (l * d) :=
  (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv

theorem intervals_lt {l d : ℕ} {a b : Fin l} {i j : Fin d}
    (h : intervals l d ⟨a, i⟩ < intervals l d ⟨b, j⟩) : a < b ∨ (a = b ∧ i < j) := by
  have key : (i : ℕ) + d * a < j + d * b := by
    simpa [intervals, finProdFinEquiv, Fin.lt_def] using h
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact Or.inl hab
  · exact Or.inr ⟨rfl, Fin.lt_def.2 (by omega)⟩
  · exfalso
    have h1 : (b : ℕ) + 1 ≤ a := hab
    have h2 : d * ((b : ℕ) + 1) ≤ d * a := Nat.mul_le_mul_left d h1
    have hj := j.isLt
    rw [Nat.mul_succ] at h2
    omega

variable {R : Type} [CommRing R]

theorem unipRad_intervals_le (l d : ℕ) : unipRad R (intervals l d) ≤ unipB R (Fin (l * d)) := by
  intro g hg
  obtain ⟨hpar, hdiag⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hpar
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact hpar _ _ (by simpa using hba)
    · rw [hdiag]
      exact Matrix.one_apply_ne hji.ne'
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [hdiag]
    exact Matrix.one_apply_eq i

theorem leviEmb_intervals_mem {l d : ℕ} (g : Levi R fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB R (Fin d)) : leviEmb R (intervals l d) g ∈ unipB R (Fin (l * d)) := by
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact leviEmb_apply_ne _ _ _ hba.ne' _ _
    · rw [leviEmb_apply_same]
      exact ((mem_unipB (R := R)).1 (hg b)).1 i j hji
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [leviEmb_apply_same]
    exact ((mem_unipB (R := R)).1 (hg a)).2 i

theorem twKer_unipB_eq_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 1 < d) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin d) k) W} (hσ : IsCuspidal σ) :
    twKer σ (unipB k (Fin d)) 1 = ⊤ := by
  classical
  obtain ⟨-, hcusp⟩ := hσ

  let e : (Σ _ : Fin d, Fin 1) ≃ Fin d := Equiv.sigmaUnique (Fin d) fun _ => Fin 1
  have hblk : ∀ i, blk e i = i := fun i => rfl
  have hne : unipRad k e ≠ ⊥ := by
    rw [CuspMax.unipRad_ne_bot_iff]
    refine ⟨⟨0, by omega⟩, ⟨1, hd⟩, ?_⟩
    rw [hblk, hblk]
    exact Fin.mk_lt_mk.2 Nat.zero_lt_one
  have hsub : Subsingleton (Jacquet σ (unipRad k e)) := hcusp d (fun _ => 1) e hne
  have hB : Subsingleton (Jacquet σ (unipRad k (points (Fin d)))) :=
    CuspMax.subsingleton_jacquet_of_perm σ (e := e) (e' := points (Fin d)) (Equiv.refl _)
      (fun i j h => h) hsub
  exact Submodule.Quotient.subsingleton_iff.1 hB

private theorem deltaHalf_eq_one_of_unipB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l d : ℕ} (g : Levi k fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB k (Fin d)) : deltaHalf k (fun _ : Fin l => Fin d) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad (hu := (show g a ∈ unipRad k (points (Fin d)) from hg a)), map_one]

theorem subsingleton_jacquet_unipB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (l d : ℕ) (hl : 0 < l) (hd : 1 < d) (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W)
    (π : Representation ℂ (GL (Fin (l * d)) k) V) (hσ : IsCuspidal σ)
    (h : ∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d),
      Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) :
    Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  classical
  obtain ⟨φ⟩ := h (intervals l d)
  obtain ⟨a₀⟩ : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  set K := twKer π (unipB k (Fin (l * d))) 1 with hK

  have hgen : ∀ u ∈ unipB k (Fin (l * d)), ∀ v : V, π u v - v ∈ K := by
    intro u hu v
    exact Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩

  have hUK : twKer π (unipRad k (intervals l d)) 1 ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, v, rfl⟩
    simpa using hgen n (unipRad_intervals_le l d n.2) v
  let P := Submodule.factor hUK
  have hP : ∀ v : V, P (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun v =>
    Submodule.factor_mk hUK v

  have hlevi : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ q, P (jac (intervals l d) π g q) = P q := by
    intro g hg q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [jac_mk, deltaHalf_eq_one_of_unipB g hg, inv_one, Units.val_one, one_smul, hP, hP]
    exact (Submodule.Quotient.eq _).2 (hgen _ (leviEmb_intervals_mem g hg) v)

  have hfwd : ∀ g z, φ (jac (intervals l d) π g z) = piTensor (segTerm σ l) g (φ z) := by
    intro g z
    have := LinearMap.congr_fun (φ.isIntertwining' g) z
    simpa using this
  have hint : ∀ g y, φ.symm (piTensor (segTerm σ l) g y) = jac (intervals l d) π g (φ.symm y) := by
    intro g y
    apply EquivLike.injective φ
    rw [hfwd, Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
  let F : (⨂[ℂ] _ : Fin l, W) →ₗ[ℂ] V ⧸ K := P ∘ₗ φ.symm.toLinearMap
  have hFapp : ∀ y, F y = P (φ.symm y) := fun y => rfl
  have hF : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ y, F (piTensor (segTerm σ l) g y) = F y := by
    intro g hg y
    rw [hFapp, hFapp, hint]
    exact hlevi g hg _

  have htop : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 = ⊤ :=
    twKer_unipB_eq_top hd (LocGL.isCuspidal_twist hσ (LocGL.isSmoothChar_absPow _))
  have htens : ∀ x : Fin l → W, F (PiTensorProduct.tprod ℂ x) = 0 := by
    intro x
    let Lx := (PiTensorProduct.tprod ℂ).toLinearMap x a₀
    have hker : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 ≤ LinearMap.ker (F ∘ₗ Lx) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      have hg : ∀ a, (Pi.mulSingle a₀ (u : GL (Fin d) k) : Levi k fun _ : Fin l => Fin d) a ∈
          unipB k (Fin d) := by
        intro a
        by_cases ha : a = a₀
        · rw [ha, Pi.mulSingle_eq_same]
          exact u.2
        · rw [Pi.mulSingle_eq_of_ne ha]
          exact one_mem _
      have hact : Lx (segTerm σ l a₀ u v) =
          piTensor (segTerm σ l) (Pi.mulSingle a₀ (u : GL (Fin d) k)) (Lx v) := by
        simp only [Lx, MultilinearMap.toLinearMap_apply, piTensor_tprod]
        congr 1
        funext a
        by_cases ha : a = a₀
        · rw [ha]
          simp
        · simp [ha]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, MonoidHom.one_apply,
        Units.val_one, one_smul, map_sub, hact, hF _ hg, sub_self]
    have hx : Lx (x a₀) = PiTensorProduct.tprod ℂ x := by
      simp [Lx]
    rw [← hx]
    exact LinearMap.mem_ker.1 (hker (by rw [htop]; exact Submodule.mem_top))
  have hF0 : F = 0 := PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using htens x)

  have hv : ∀ v : V, (Submodule.Quotient.mk v : V ⧸ K) = 0 := by
    intro v
    rw [← hP v]
    have hPF : P (Submodule.Quotient.mk v) = F (φ (Submodule.Quotient.mk v)) := by
      rw [hFapp, Representation.Equiv.symm_apply_apply]
    rw [hPF, hF0, LinearMap.zero_apply]
  refine ⟨fun a b => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact (hv v).trans (hv w).symm

end GlobalTheory.SmGL.CuspSegment
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.DetSqrtCover

theorem nonempty_grpData : ∀ p q : ℕ, Nonempty (GrpData p q) :=
  fun p q => ⟨grpOf p q MeasureTheory.Measure.haar⟩

end GlobalTheory.DetSqrtCover
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

theorem _root_.GlobalTheory.T.isCompact_detSqrtCover_maxCompact : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  first | exact @GlobalTheory.PolarU.isCompact_Kset | exact GlobalTheory.PolarU.isCompact_Kset | (intros; apply GlobalTheory.PolarU.isCompact_Kset <;> assumption)
end
