module

public import Formalism.GaussJetBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Formalism.LocalRingCardinality.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle083
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
public import Formalism.LocalToGlobal.Columns.Adelic
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle087
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AddCoordExponentIntegralJetsUnramified
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnitConjugateNormTwoPowerTwoAdic
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle058
public import Formalism.SharpRestriction.ParConsts
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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Formalism.LocalRingCardinality.Bundle007
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames

open MvPowerSeries GlobalTheory.Proof.DirectionalDerivative

section Formal

variable {p : ℕ} [Fact p.Prime] {σ κ : Type}

theorem jetsIntegral_iff (G : MvPowerSeries κ ℂ_[p]) :
    JetsIntegral G ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral G := by
  unfold JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt Formalism.DworkPowerSeriesWeights.mfact
  simp [Finsupp.prod, Nat.cast_prod]

theorem jetAt_linAt_list [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (l : List κ) (G : MvPowerSeries σ ℂ_[p]) :
    GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt (linAt c G) (l.map fun x => Finsupp.single x 1).sum =
      constantCoeff (l.foldl (fun H x => dirDer (fun k => c k x) H) G) := by
  induction l generalizing G with
  | nil => simp [jetAt_zero, constantCoeff_linAt]
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, add_comm, jetAt_add_single, pderiv_linAt, ih, List.foldl_cons]

end Formal

theorem jetsInt_frames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  intro D N N' p _ lm Yl F
  refine ⟨⟨fun hF n y hy => ?_, fun h n y hy => ?_⟩, fun hF ν _ M hM => ?_⟩
  · change JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F)
    rw [jetsIntegral_iff]
    exact jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG)
      (fun x G hG => keeps_vecY D lm Yl (hy x) G hG) F hF
  · have hJ := (jetsIntegral_iff _).1 (h n y hy)
    change GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F) at hJ
    have := hJ (((List.finRange n).reverse.map fun x => Finsupp.single x 1).sum)
    rw [jetAt_linAt_list, List.foldl_reverse] at this
    show ‖constantCoeff ((List.ofFn y).foldr (fun y' G => der D lm y' G) F)‖ ≤ 1
    rw [List.ofFn_eq_map, List.foldr_map]
    have hfun : (fun x G => der D lm (y x) G) = fun x G => dirDer (fun k => vecY D lm (y x) k) G := by
      funext x G
      exact der_eq D lm (y x) G
    rw [hfun]
    exact this
  · change JetsIntegral (linAt M F)
    rw [jetsIntegral_iff]
    refine jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x => ?_) F hF
    obtain ⟨n, r, y, hr, hy, hMx⟩ := hM x
    have e : (fun k => M k x) = ∑ j, r j • vecY D lm (y j) := by
      funext k
      rw [hMx k, Finset.sum_apply]
      rfl
    rw [e]
    exact Finset.sum_induction _ (Keeps D lm Yl) (fun _ _ ha hb => keeps_add D lm Yl ha hb) (keeps_zero D lm Yl)
      fun j _ => keeps_smul D lm Yl (hr j) (keeps_vecY D lm Yl (hy j))

end GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.formalGroup_nu_cast_eq_ite_lt_N : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  first | exact @GlobalTheory.fock_rows_of_fills | exact GlobalTheory.fock_rows_of_fills | (intros; apply GlobalTheory.fock_rows_of_fills <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField MvPolynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

section Generic

open Formalism.GradedWeylDivisibility

variable {a b : ℕ} (hab : a ≤ b)

def subGen : MvPolynomial (Fin a × Fin a) ℤ →ₐ[ℤ] MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ) :=
  aeval fun v => ∑ β : Fin b, C (X (β, Fin.castLE hab v.2)) * X (β, v.1)

theorem aeval_subGen {A : Type} [CommRing A] (d : Fin b × Fin a → A) (y : Fin b × Fin b → A)
    (f : MvPolynomial (Fin a × Fin a) ℤ) :
    aeval (fun v : Fin a × Fin a => ∑ β : Fin b, y (β, Fin.castLE hab v.2) * d (β, v.1)) f =
      ∑ α ∈ (subGen hab f).support, aeval y ((subGen hab f).coeff α) * ∏ v ∈ α.support, d v ^ α v := by
  have h := eval₂_eq (aeval (R := ℤ) y).toRingHom d (subGen hab f)
  refine Eq.trans ?_ h
  have : (aeval (R := ℤ) (fun v : Fin a × Fin a => ∑ β : Fin b, y (β, Fin.castLE hab v.2) * d (β, v.1))).toRingHom =
      (eval₂Hom (aeval (R := ℤ) y).toRingHom d).comp (subGen hab).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
    simp [subGen]
  exact RingHom.congr_fun this f

theorem isHomogeneous_of_mem_weyl {ν : Fin a → ℕ} (hν : Antitone ν) {f : MvPolynomial (Fin a × Fin a) ℤ}
    (hf : f ∈ weyl ℤ a a le_rfl ν) : f.IsHomogeneous (∑ r, ν r) := by
  have h : IsWeightedHomogeneous (colW a a) f ν := (weylLeDual ℤ a a le_rfl ν hν hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

theorem subGen_isHomogeneous {n : ℕ} {f : MvPolynomial (Fin a × Fin a) ℤ} (hf : f.IsHomogeneous n) :
    (subGen hab f).IsHomogeneous n := by
  have := hf.aeval (fun v : Fin a × Fin a => ∑ β : Fin b,
    (C (X (β, Fin.castLE hab v.2)) * X (β, v.1) : MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ)))
    (n := 1) (fun v => IsHomogeneous.sum _ _ _ fun β _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at this
  exact this

theorem coeff_subGen_mem {ν : Fin a → ℕ} {ν' : Fin b → ℕ} (hν : Antitone ν')
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) {f : MvPolynomial (Fin a × Fin a) ℤ}
    (hf : f ∈ weyl ℤ a a le_rfl ν) (α : Fin b × Fin a →₀ ℕ) : (subGen hab f).coeff α ∈ weyl ℤ b b le_rfl ν' := by
  let S := MvPolynomial (Fin b × Fin a) ℤ
  let M : Matrix (Fin b) (Fin b) S := fun i β => if h : (i : ℕ) < a then X (β, ⟨i, h⟩) else 0
  have h1 := GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice ℤ a b hab ν ν' h f hf
  have hmap : ∀ g ∈ weyl ℤ b b le_rfl ν', map (algebraMap ℤ S) g ∈ weyl S b b le_rfl ν' := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, by
        beta_reduce
        rw [← lclosedeq_hw_map (algebraMap ℤ S), lclosedeq_applyWord_map]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := map (algebraMap ℤ S))]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have h2 := GlobalTheory.T.weylRowAction_mem_weylLattice_square S b ν' hν M _ (hmap _ h1)
  let ψ : MvPolynomial (Fin b × Fin b) S →+* MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ) :=
    eval₂Hom (map (algebraMap ℤ _)) fun v => C (X v)
  have hψ : ∀ g : MvPolynomial (Fin b × Fin b) ℤ, ψ (map (algebraMap ℤ S) g) = C g := fun g => by
    have : ψ.comp (map (algebraMap ℤ S)) = C :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => by simp [ψ]
    exact RingHom.congr_fun this g
  have e : subGen hab f = ψ (rowAct S M (map (algebraMap ℤ S) (rename (fun v : Fin a × Fin a =>
      ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f))) := by
    have : (subGen hab).toRingHom = ψ.comp ((rowAct S M).toRingHom.comp ((map (algebraMap ℤ S)).comp
        (rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b))).toRingHom)) := by
      refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
      simp [subGen, rowAct, ψ, M, mul_comm]
      exact Finset.sum_congr rfl fun x _ => congrArg (· * _) (map_X _ _).symm
    exact RingHom.congr_fun this f
  rw [e]
  generalize rowAct S M _ = F at h2
  induction h2 using Submodule.span_induction generalizing α with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have : applyWord S w (hw S le_rfl ν') = map (algebraMap ℤ S) (applyWord ℤ w (hw ℤ le_rfl ν')) := by
      rw [← lclosedeq_hw_map (algebraMap ℤ S), lclosedeq_applyWord_map]
    simp only [this, hψ, coeff_C]
    split_ifs
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), AddMonoidAlgebra.coeff_add]; exact add_mem (hx α) (hy α)
  | smul c x _ hx =>
    classical
    rw [smul_eq_C_mul, map_mul, coeff_mul]
    refine Submodule.sum_mem _ fun p _ => ?_
    have : ψ (C c) = map (algebraMap ℤ _) c := by simp [ψ]
    rw [this, coeff_map, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hx _)

end Generic

section Integral

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

variable {D : D7} {N : ℕ} {wt : D.what₂.Tau → DomWeight N}

variable {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {O : LiftObj D (D.chTw u μ)} {i : ℕ}

end Integral

section Subst

variable {D : D7} {N N' : ℕ}

end Subst

section Lift

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem natW_anti {n : ℕ} (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

end Lift

end GlobalTheory.LiftTypePrime

end
end

section

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
open Matrix

namespace GlobalTheory.RatInt

theorem mem_range_of_iA_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a : E) (ha : iA F E a ∈ Formalism.L2.Herm.intAf F E) : a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hmem : (fun _ => a : Fin 1 → E) ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    have h2 : (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := Submodule.smul_mem _ (⟨_, ha⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)
    rw [map_one, mul_one]
  rw [Formalism.UG.P.global_lattice_one_holds F E (Fin 1) Λ hfin hspan] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem intAt_of_intAtA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  intro F E _ _ _ _ _ P x ⟨s, hs, hm⟩
  rw [← map_mul] at hm
  obtain ⟨r, hr⟩ := mem_range_of_iA_mem (F := F) _ hm
  exact ⟨r, s, hs, hr.symm⟩

end GlobalTheory.RatInt
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.pointLocalEigen_galoisPolynomial_split : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → Formalism.L2.HeckeRational D M → Formalism.L2.AVTied D M → Formalism.L2.NormalizedLocalCompatibility D M → ∀ i : D.nd.Loc, (∀ (P : D.naut.AV i) (w : PlE D.host), SplitOut D.nd i w → ∃ lam : ℕ → ℂ, galPol D.naut (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) = X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV, C ((-1) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (D.R.nV - k) ∧ ∀ (k : ℕ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host w s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i P, Formalism.L2.NG.tN (M.loc i).J s ϖ k ((M.loc i).real y) = lam k • (M.loc i).real y) → GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  first | exact @GlobalTheory.PtLocalEig.main | exact GlobalTheory.PtLocalEig.main | (intros; apply GlobalTheory.PtLocalEig.main <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.addCoord_exponent_integral_jets_unramified : ∀ (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F → F1 F be0 → F2 l σ be0 → ∀ n : Fin 2 →₀ ℕ, ‖(((n 0).factorial * (n 1).factorial : ℕ) : MaximalUnramifiedExtension l) * MvPowerSeries.coeff n (addC l be0)‖ ≤ 1 := by
  first | exact @GlobalTheory.AddJet.addC_integral_jets | exact GlobalTheory.AddJet.addC_integral_jets | (intros; apply GlobalTheory.AddJet.addC_integral_jets <;> assumption)
end

section

namespace GlobalTheory.ThLoc

theorem goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight : Formalism.L2.Th1.Top.GoodModelTwo :=
  GlobalTheory.ThLoc.GoodTwo.goodModelTwo

end GlobalTheory.ThLoc
end

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem tateDual_matRep_crys : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  intro l _ P K LL k M hT hM hC
  haveI : IsTopologicalRing ↥LL.1 := by
    first
      | infer_instance
      | exact Subring.instIsTopologicalRing LL.1.toSubring
      | exact inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  have hχ := GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum P K LL
  have hinv : Continuous fun g : ↥(GK K) => M g⁻¹ := hM.comp continuous_inv
  have hc : Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) := by
    change Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose
    exact hχ.smul hinv.matrix_transpose
  refine ⟨hc, ?_⟩
  exact hT (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) M hM)
    (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) _ hc) (dotProductBilin ↥LL.1 ↥LL.1)
    (TwistDualLoc.isDual1_dot (P.PD K) M) hC

end GlobalTheory.HTW.Rec
end
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem nonempty_places_of_record (D : D7) : Nonempty D.what₂.places.Pl := by
  have h : Nonempty (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.what₂.LL)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.what₂.LL)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
      (NumberField.RingOfIntegers.not_isField _)⟩⟩
  exact h.map D.plEq.symm

theorem fill_eq_wPl : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
    ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)),
      fill (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z = wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  refine ⟨0, fun x _ hx i j hj z => ?_⟩
  obtain ⟨w⟩ := nonempty_places_of_record (Fm.D x i)
  refine (Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_
  · simp only [SizeData₂.lifts, Finset.mem_Icc]; omega
  · simp [tauPl]

end GlobalTheory
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem rank_two_logb_five_sq_le {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
      2 * Real.logb 5 ((Fm.L x i).sc.a ^ 2) + 2 ≤ ((Fm.D x i).R.k : ℝ) - 1 := by
  refine ⟨3, fun x hx hx1 i => ?_⟩
  have hK := (Fm.sizes x hx1 i).2.2.1.1
  have hsx := Fm.L_x x i hx1
  have he := (Fm.L x i).sc.eps_pos
  have he' := (Fm.L x i).sc.eps_lt
  have hx3 : (3 : ℝ) ≤ x := hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [hsx] at hK
  have h4 : x ^ (4 : ℕ) ≤ ((Fm.D x i).R.k : ℝ) := by
    refine le_trans ?_ hK
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold szTh
    push_cast
    linarith
  have hL : (Fm.L x i).sc.L ≤ x := by
    unfold Scale.L
    rw [hsx]
    calc x ^ (Fm.L x i).sc.eps ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    rw [hsx]
    positivity
  have hla : Real.log (Fm.L x i).sc.a = Real.log x + (Fm.L x i).sc.L := by
    unfold Scale.a Scale.b
    rw [hsx, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h5 : 1 ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hb : Real.logb 5 ((Fm.L x i).sc.a ^ 2) ≤ 4 * x := by
    rw [Real.logb, Real.log_pow, hla]
    push_cast
    refine (div_le_self (by linarith) h5).trans (by linarith)
  have h27 : 27 ≤ x ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
  have : 27 * x ≤ x ^ 4 := by
    calc 27 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h27 hx0.le
      _ = x ^ 4 := by ring
  linarith

end GlobalTheory
end
