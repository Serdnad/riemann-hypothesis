module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Formalism.LocalRingCardinality.DataHost
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle704
public import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SUVol.Degenerate

theorem realSU_subsingleton {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1) :
    Subsingleton (realSU Ψ G) := by
  refine ⟨fun g g' => ?_⟩
  have key : ∀ g : realSU Ψ G, g = 1 := by
    intro g
    apply Subtype.ext
    funext τ
    rcases h with h | h
    · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
    · subst h
      apply Units.ext
      have hd := (g.2 τ).1
      rw [Matrix.det_unique] at hd
      ext a b
      rw [Subsingleton.elim a default, Subsingleton.elim b default]
      simpa using hd
  rw [key g, key g']

theorem realLie_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1)
    (X : Ψ → Fin r → Fin r → ℂ) (hX : X ∈ realLie Ψ G) : X = 0 := by
  funext τ
  rcases h with h | h
  · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
  · subst h
    have ht := (hX τ).1
    rw [Matrix.trace_fin_one] at ht
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simpa using ht

theorem fromFrame_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (hdet : ∀ τ, (mat x τ).det ≠ 0)
    (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (hY : fromFrame x Y = 0) : Y = 0 := by
  ext ⟨τ, a, b⟩
  have h1 := congrFun hY τ
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (hdet τ)
  have h2 : Matrix.of (fun a b => Y (τ, a, b)) = 0 := by
    have e : (mat x τ)⁻¹ * (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹) * mat x τ =
        Matrix.of (fun a b => Y (τ, a, b)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [← e]
    have h1' : (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := h1
    rw [h1', Matrix.mul_zero, Matrix.zero_mul]
  have := congrFun (congrFun h2 a) b
  simpa using this

end GlobalTheory.SUVol.Degenerate


open GlobalTheory.SUVol.Degenerate in
theorem GlobalTheory.SUVol.Degenerate.riemHaar_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  intro E _ _ _ r Ψ G x hr hdet hc S
  have h : Ψ.card = 0 ∨ r = 1 := by
    rcases Nat.mul_eq_zero.1 hc with h | h
    · exact Or.inl h
    · right
      have : r ^ 2 ≤ 1 := by omega
      nlinarith
  haveI := realSU_subsingleton Ψ G h
  haveI : CompactSpace (realSU Ψ G) := Finite.compactSpace
  set K := (realLie Ψ G).comap (fromFrame x) with hK
  haveI hKs : Subsingleton K := by
    refine ⟨fun Y Y' => ?_⟩
    have hz : ∀ Y : K, Y = 0 := fun Y => by
      apply Subtype.ext
      exact fromFrame_eq_zero x hdet Y.1 (realLie_eq_zero Ψ G h _ Y.2)
    rw [hz Y, hz Y']

  have hν : ∀ s, riemLie Ψ G x s ≤ 1 := by
    intro s
    set b := (stdOrthonormalBasis ℝ K).toBasis
    have hb : b.addHaar Set.univ = 1 := by
      rw [← Set.Nonempty.eq_univ (b.parallelepiped).nonempty]
      exact b.addHaar_self
    calc riemLie Ψ G x s ≤ riemLie Ψ G x Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := by
        unfold riemLie
        by_cases hm : AEMeasurable (fun Y : K => fromFrame x Y.1) b.addHaar
        · rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ, Set.preimage_univ, hb]
        · have hne : b.addHaar ≠ 0 := by
            intro he
            simp [he] at hb
          rw [Measure.map_of_not_aemeasurable_of_ne_zero hm hne]
          simp
  set μ := (Measure.haar : Measure (realSU Ψ G))
  have hu0 : μ Set.univ ≠ 0 := (isOpen_univ.measure_ne_zero μ Set.univ_nonempty)
  have hut : μ Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  have hball : ∀ ε : ℝ, 0 < ε → grpBall (realSU Ψ G) ε = Set.univ := by
    intro ε hε
    ext g
    simp only [Set.mem_univ, iff_true]
    rw [Subsingleton.elim g 1]
    intro τ a b
    simpa using hε
  have hlim : Filter.limsup (fun ε : ℝ => riemLie Ψ G x (tanBall Ψ r ε) / μ (grpBall (realSU Ψ G) ε))
      (nhdsWithin 0 (Set.Ioi 0)) ≤ 1 / μ Set.univ := by
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hball ε hε]
    exact ENNReal.div_le_div_right (hν _) _
  show riemHaar Ψ G x S ≤ 1
  unfold riemHaar tangentHaar
  rw [Measure.smul_apply, smul_eq_mul]
  calc _ ≤ (1 / μ Set.univ) * μ Set.univ :=
        mul_le_mul' hlim (measure_mono (Set.subset_univ S))
    _ = 1 := ENNReal.div_mul_cancel hu0 hut
end

section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil


theorem _root_.GlobalTheory.T.latticeIntertwinerRep_splitPlace_positive_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h →
          ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
            (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
              ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
            ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, h) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.FinLatF.isLatRepF_split | exact GlobalTheory.FinLatF.isLatRepF_split | (intros; apply GlobalTheory.FinLatF.isLatRepF_split <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := by
  first | exact @GlobalTheory.RealLift.PolRangePf.polRange_of | exact GlobalTheory.RealLift.PolRangePf.polRange_of | (intros; apply GlobalTheory.RealLift.PolRangePf.polRange_of <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  first | exact @GlobalTheory.CCRFock.fock_map_of_ccr_dep | exact GlobalTheory.CCRFock.fock_map_of_ccr_dep | (intros; apply GlobalTheory.CCRFock.fock_map_of_ccr_dep <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.archimedeanTrace_symplecticForm_orthonormalFrames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFrames.symp_frames | exact GlobalTheory.SympFrames.symp_frames | (intros; apply GlobalTheory.SympFrames.symp_frames <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ)
    (cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd → HasExp τ χ m →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x)) →
    (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 →
    0 < R + S → ∀ w, cd w = m w / 2 := by
  first | exact @GlobalTheory.RealLift.DConst.cd_eq_half_exp | exact GlobalTheory.RealLift.DConst.cd_eq_half_exp | (intros; apply GlobalTheory.RealLift.DConst.cd_eq_half_exp <;> assumption)
end

section

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.VacLn
theorem vac_ne_zero {ι : Type} [Fintype ι] {P Q R S : ℕ} :
    (PiTensorProduct.tprod ℂ fun _ : ι => (1 : Pol P Q R S)) ≠ 0 := by
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    fun _ => (MvPolynomial.aeval (R := ℂ) (S₁ := ℂ) (σ := Ln P Q R S) fun _ => 0).toLinearMap)) h
  simp at this

theorem vacLine_of_derEx (hD : DerEx) : VacLine := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hStd hFr hΦ f₀ ε hyp
  obtain ⟨D, hDu⟩ := hD F E σ α β κ ψ JA JB d hStd
  obtain ⟨J, e, e', hJ, he, hJe, he1, he2, hy⟩ := GlobalTheory.T.fockVacuumEquations_in_archimedeanDarbouxCoordinates F E σ α β κ P Q R S τ JA JB d a b A C ε hCM hFr
  have hDx : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x = fderiv ℝ f x (coord d u).1 -
      2 * Real.pi * Complex.I * (trPair F κ x (coord d u).2 : ℝ) * f x := fun u hu f x => (hDu u hu f).2 x
  have hf : ∀ y x, fderiv ℝ f₀ x (J (y - (2 : ℝ) • e y)).1 - 2 * Real.pi * Complex.I *
      (trPair F κ x (J (y - (2 : ℝ) • e y)).2 : ℝ) * f₀ x =
      Complex.I * (fderiv ℝ f₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * f₀ x) := by
    intro y x
    obtain ⟨u, u', u₁, c, hu, hu', -, hc, hc', -, h0, h', -⟩ := hy y
    have key := hyp u u' hu hu' c hc hc' (D u f₀) (D u' f₀) (hDu u hu f₀).1 (hDu u' hu' f₀).1
    have := congrArg (fun g : SInf F κ => g x) key
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u' hu'] at this
    rw [← h', ← h0]
    exact this
  set g₀ := Φ (PiTensorProduct.tprod ℂ fun _ => 1) with hg₀
  have hg0 : g₀ ≠ 0 := fun h => vac_ne_zero (hΦ.1 (h.trans (map_zero Φ).symm))
  have hg : ∀ y x, fderiv ℝ g₀ x (J y).1 - 2 * Real.pi * Complex.I * (trPair F κ x (J y).2 : ℝ) * g₀ x =
      Complex.I * (fderiv ℝ g₀ x y.1 - 2 * Real.pi * Complex.I * (trPair F κ x y.2 : ℝ) * g₀ x) := by
    intro y x
    obtain ⟨u, -, u₁, c, hu, -, hu₁, hc, -, hc₁, h0, -, h1⟩ := hy y
    have e0 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u hu g₀).1 (hΦ.2 u hu c hc _)
    have e1 := GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators (hDu u₁ hu₁ g₀).1 (hΦ.2 u₁ hu₁ _ hc₁ _)
    rw [GlobalTheory.T.piTensorSumFockHeisenberg_I_smul_signConj_vacuum, map_smul, ← e0] at e1
    have := congrArg (fun g : SInf F κ => g x) e1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at this
    rw [hDx u hu, hDx u₁ hu₁] at this
    rw [← h1, ← h0]
    exact this
  obtain ⟨z, hz⟩ := GlobalTheory.T.schwartz_complexStructure_vacuum_solution_eq_smul (trPair F κ) (fun y h => GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate y h) J e e' hJ he hJe he1 he2 f₀ g₀ hg0 hg hf
  exact ⟨z, hz⟩

end GlobalTheory.VacLn
end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaSmoothF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def iotaHom {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : (IxF F nS nT → ℂ) →+ WOF F E nS nT where
  toFun := iotaVF ι
  map_zero' := iotaVF_zero ι
  map_add' := iotaVF_add ι

theorem contDiff_heis_iota (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) (x : WOF F E nS nT) :
    ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)
  let φ : (IxF F nS nT → ℂ) →+ ℂ :=
    { toFun := fun v => lam (symplOHF σ JS JT ξ₀ x (iotaVF ι v))
      map_zero' := by rw [iotaVF_zero, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun u v => by rw [iotaVF_add, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ x (continuous_iotaVF hι))
  let eqv := (Module.finBasis ℝ (IxF F nS nT → ℂ)).equivFunL
  let L' : (Fin (Module.finrank ℝ (IxF F nS nT → ℂ)) → ℝ) →+ WOF F E nS nT :=
    (iotaHom ι).comp eqv.symm.toLinearEquiv.toAddMonoidHom
  have hL' : Continuous L' := (continuous_iotaVF hι).comp eqv.symm.continuous
  have hsm := hf.smooth _ L' hL' (fun t => real_iotaVF hι _) x
  have hg : ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => f (x + iotaVF ι v) := by
    have h1 := hsm.comp eqv.contDiff
    convert h1 using 1
    funext v
    simp [L', iotaHom]
  have e : (fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x) =
      fun v => Complex.exp (φ.toRealLinearMap hφ v) * f (x + iotaVF ι v) := by
    funext v
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ x _ (real_iotaVF hι v))]
    rfl
  rw [e]
  exact ((φ.toRealLinearMap hφ).contDiff.cexp).mul hg

end GlobalTheory.ThetaSmoothF


open GlobalTheory.ThetaSmoothF in
theorem GlobalTheory.ThetaSmoothF.sm_of_thetaF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι hψ f hf
  have hstd := GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB
  let H := HMF (nS := nS) (nT := nT) JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)
  let B₀ : (IxF F nS nT → ℂ) →ₗ[ℝ] (IxF F nS nT → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
      (fun x x' y => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
      (fun x y y' => by simp [add_dotProduct])
      (fun c x y => by simp [star_smul, smul_dotProduct])
  let om : (IxF F nS nT → ℂ) →L[ℝ] (IxF F nS nT → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ H *ᵥ x).im := rfl
  have hH : IsHeis (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ H *ᵥ x).im) (rhoVF σ JS JT ξ₀ B.ψ hψ ι) := by
    refine ⟨fun g => ?_, fun u v g => ?_, fun u g => norm_rhoBF hψ _ g, fun g => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι 0) g = g
      rw [iotaVF_zero]
      exact rhoBF_zero hψ g
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι v) g) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (u + v)) g
      rw [rhoBF_rhoBF, iotaVF_add, GlobalTheory.T.stdChar_half_symplecticForm_real_coordinates F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι u v]
    · exact (GlobalTheory.T.continuous_heisenbergOperatorBoundedThetaFunctions F E σ nS nT JS JT ξ₀ B.ψ hψ g).comp (continuous_iotaVF hι)
  refine GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set (IxF F nS nT → ℂ) (BBF σ JS JT ξ₀ B.ψ) om (rhoVF σ JS JT ξ₀ B.ψ hψ ι) (e ▸ hH)
    (WOF F E nS nT) (ev _ _) norm_ev_le (fun b C => norm_QB_le b)
    (fun x v => ⟨B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)), x + iotaVF ι v, fun b => rfl⟩)
    {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g.1} ?_ ?_ f hf
  · intro g hg x
    exact (contDiff_heis_iota σ B hB JS JT ξ₀ hι hg x).differentiable (by simp)
  · intro g hg z
    let L : ℝ →+ WOF F E nS nT :=
      { toFun := fun t => iotaVF ι (t • z)
        map_zero' := by rw [zero_smul, iotaVF_zero]
        map_add' := fun s t => by rw [add_smul, iotaVF_add] }
    have hL : Continuous L := (continuous_iotaVF hι).comp (continuous_id.smul continuous_const)
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => real_iotaVF hι _
    let d : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g.1 w) 0
    have hlev : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u d = d := by
      obtain ⟨U, hU, hUf⟩ := hg.level
      exact ⟨U, hU, fun u hu hu0 =>
        GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 L hL hL0 u hu0 (hUf u hu hu0)⟩
    have hsm : ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L' →
        (∀ t, (L' t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ∞ fun t => d (w + L' t) :=
      fun k L' hL' hL'0 w => GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 k L' hL' hL'0 w
    have hd : IsThetaFunOF σ JS JT ξ₀ B.ψ d :=
      ⟨fun γ w => GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 γ w, hlev,
        GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd d hlev hsm, hsm⟩
    have hb := GlobalTheory.T.orientedModelThetaFunction_bounded F E σ nS nT JS JT ξ₀ B.ψ hψ d hd
    refine ⟨toBF d hd.cont hb hd.quasi, hd, fun x => ?_⟩
    exact (GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 x).hasDerivAt
end
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.isThetaFun_of_smooth_real_heisenberg_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  first | exact @GlobalTheory.ThetaOfSmF.theta_of_smF | exact GlobalTheory.ThetaOfSmF.theta_of_smF | (intros; apply GlobalTheory.ThetaOfSmF.theta_of_smF <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

namespace GlobalTheory.ThetaSmoothCM

theorem contDiff_thetaTr_real_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  intro F E _ _ _ _ _ σ B hgood nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ hψ JA JB ξ hJA hJB κ _ co hrat φ hφ k L hLc hLf w
  exact GlobalTheory.T.contDiff_thetaTransform_archimedean_cm F E σ B hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ hJA hJB κ co hrat φ hφ k L hLc hLf w

end GlobalTheory.ThetaSmoothCM
end
