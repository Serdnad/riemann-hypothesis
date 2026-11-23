module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle488
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle453
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle857
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle711
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

theorem isConn_of_chart {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k) {d : ℕ}
    (c : Katz.Chart G d) : G.IsConn := by
  intro n a ha
  obtain ⟨f, rfl⟩ := c.presents.1 n a
  have h0 : Coalgebra.counit (R := k) (Katz.evA k (c.x n) (c.nil n) f) = 0 := by
    have := RingHom.mem_ker.1 ha
    simpa using this
  have hf : MvPowerSeries.constantCoeff f = 0 := by
    rw [← (Katz.counit_dUnit_evA k d (G.A n) (c.x n) (c.nil n) (c.aug n) f).1]; exact h0
  exact mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero k (Fin d) (G.A n)
    (Katz.evA k (c.x n) (c.nil n)) (fun i => by rw [Katz.evA_X]; exact c.nil n i) f hf

end GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem katz_etDual_of_iso : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))
    (C : Base p (fun _ _ G => G.IsEt)) (D : Base p (fun _ _ _ => True)), B.Katz → C.EtDual B →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn),
      D.M G trivial ≃ₗ[WittVector p k] B.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsConn) (h : G.IsConn) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = B.smap h' h s (e G h m)) →
    (∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt),
      D.M G trivial ≃ₗ[WittVector p k] C.M G h, ∀ (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
      [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k)
      (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (m : D.M G trivial),
      e G' h' (D.smap trivial trivial s m) = C.smap h' h s (e G h m)) →
    D.Katz ∧ D.EtDual D := by
  intro p _ B C D hB hC ⟨eB, neB⟩ ⟨eC, neC⟩
  obtain ⟨κ, hκ⟩ := hB
  obtain ⟨δ, hδ⟩ := hC

  have FB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsConn)
      (t : True) (m : D.M G trivial), eB G h (D.F G t m) = B.F G h (eB G h m) := fun G h _ m =>
    neB _ _ _ G G h h _ m
  have FC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt)
      (t : True) (m : D.M G trivial), eC G h (D.F G t m) = C.F G h (eC G h m) := fun G h _ m =>
    neC _ _ _ G G h h _ m
  have MB : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsConn)
      (h' : H.IsConn) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eB G h (D.map t t' f m) = B.map h h' f (eB H h' m) := fun G H h h' f _ _ m =>
    neB _ _ _ G H h h' _ m
  have MC : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (h : G.IsEt)
      (h' : H.IsEt) (f : G ⟶ H) (t t' : True) (m : D.M H trivial),
      eC G h (D.map t t' f m) = C.map h h' f (eC H h' m) := fun G H h h' f _ _ m =>
    neC _ _ _ G H h h' _ m
  refine ⟨⟨fun {_} _ _ _ G _ {_} c {_} hμ hc => (eB G (isConn_of_chart G c)).trans (κ G _ c hμ hc), ?_⟩,
    ⟨fun G _ _ hG => (eC G hG).trans ((δ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG).trans
      (eB G.dual (PDivGroup.dual_isConn_of_isEt p _ G hG)).dualMap), ?_⟩⟩
  · intro k _ _ _ G _ d c μ hμ hc
    obtain ⟨h1, h2⟩ := hκ G (isConn_of_chart G c) c hμ hc
    refine ⟨?_, ?_⟩
    · convert h1 using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, FB, LinearEquiv.apply_symm_apply]
    · intro H _ d' c' ν hν hc' f φ hφ hm
      convert h2 H (isConn_of_chart H c') c' hν hc' f φ hφ hm using 1
      funext x
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
        MB G H (isConn_of_chart G c) (isConn_of_chart H c'), LinearEquiv.apply_symm_apply]
  · intro k _ _ _ G _ _ hG
    obtain ⟨h1, h2⟩ := hδ G hG (PDivGroup.dual_isConn_of_isEt p _ G hG) hG
    refine ⟨fun x y => ?_, fun H _ _ hH f x y => ?_⟩
    · simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, FB, FC]
      exact h1 _ _
    · obtain ⟨-, h3⟩ := hδ H hH (PDivGroup.dual_isConn_of_isEt p _ H hH) hH
      simp only [LinearEquiv.trans_apply, LinearEquiv.dualMap_apply]
      rw [MC G H hG hH f, MB H.dual G.dual (PDivGroup.dual_isConn_of_isEt p _ H hH)
        (PDivGroup.dual_isConn_of_isEt p _ G hG) (G.dualHom H f)]
      exact h2 H hH _ hH f _ _

end GlobalTheory.Dieu
end
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

theorem _root_.GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ) (x : Fin 2 → FR E), 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E)) → ∀ j, IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  first | exact @GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | exact GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | (intros; apply GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.CMTypeEmb

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) : Fintype.card I = Module.finrank ℚ (FR E) := by
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)
  have hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E)) :=
    Fintype.card_congr (IsCMField.equivInfinitePlace E)
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (FR E)
  have hr : InfinitePlace.nrComplexPlaces (FR E) = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (FR E)
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)
  omega

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  intro E _ _ _ I _ φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := card_eq_finrank hφ
  let e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀
  refine ⟨e₀.symm.trans e, fun i x ↦ ?_⟩
  have := he (e₀.symm i) x
  simp only [Equiv.apply_symm_apply] at this
  simp only [Equiv.trans_apply]
  exact this.symm

end GlobalTheory.CMTypeEmb
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.schur_mul_vandermonde_det_eq_det : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → GlobalTheory.JSW.schur n l * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  first | exact @GlobalTheory.JSW.schur_mul_det_eq_det | exact GlobalTheory.JSW.schur_mul_det_eq_det | (intros; apply GlobalTheory.JSW.schur_mul_det_eq_det <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def locSpan (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) : Submodule ℂ (GA E a → ℂ) :=
  sInf {V | F₀ ∈ V ∧ (∀ F ∈ V, ∀ h ∈ supS (E := E) (a := a) S, (fun g => F (g * h)) ∈ V) ∧
    ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V}

variable {S : Finset (HeightOneSpectrum (𝓞 E))} {F₀ : GA E a → ℂ}

theorem self_mem_locSpan : F₀ ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun _ hV => hV.1

theorem rt_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {h : GA E a} (hh : h ∈ supS (E := E) (a := a) S) :
    (fun g => F (g * h)) ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.1 F (Submodule.mem_sInf.1 hF V hV) h hh

theorem kerInf_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.2 F (Submodule.mem_sInf.1 hF V hV) X ν k γ hk

theorem locSpan_le {V : Submodule ℂ (GA E a → ℂ)} (h₁ : F₀ ∈ V)
    (h₂ : ∀ F ∈ V, ∀ h ∈ supS (E := E) (a := a) S, (fun g => F (g * h)) ∈ V)
    (h₃ : ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V) : locSpan S F₀ ≤ V :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem locSpan_le_rspan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ rspan π :=
  locSpan_le (mem_rspan hφ) (fun _ hF h _ => rt_mem_rspan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_rspan hF ν hk

theorem locSpan_le_mspanR {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ mspanR π := by
  rw [← rspan_eq_mspanR]; exact locSpan_le_rspan hφ

end GlobalTheory.JSW.MirSemi
end
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

abbrev compGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)

theorem compGL_apply (w : InfinitePlace E) (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = (g : Matrix (Fin n) (Fin n) (Cinf E)) i j w := rfl

abbrev matInf (g : GL (Fin n) (Cinf E)) : Fin n → Fin n → Cinf E :=
  fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j

def IsWhitInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), ∀ g,
    W (u * g) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * W g

def IsModGrowthInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  Continuous W ∧ ∃ (C : ℝ) (N : ℕ), ∀ g, ‖W g‖ ≤ C * htInf g ^ N

def IsRapidFInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : X → Z →L[ℝ] ℝ) : Prop :=
  Measurable k ∧ (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
    (∀ z, Measurable fun x => η x z) ∧
    ∀ N : ℕ, Integrable (fun x => ‖k x‖ * (htInf (γ x) * (1 + ‖η x‖)) ^ N) ν

def IsKerOpInf {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin n) (Cinf E))
    (η : X → Z →L[ℝ] ℝ), IsRapidFInf ν k γ η ∧
      ∀ W, IsModGrowthInf W → ∀ z g, T W z g = ∫ x, k x * (𝐞 (η x z) : ℂ) * W (g * γ x) ∂ν


variable (E) in
def levSetInf (n r : ℕ) : Set (GL (Fin n) (Cinf E)) := {g | ∀ w, compGL w g ∈ levSet n r}

def rowCutInf (ρ : Fin n) (x : Matrix (Fin n) (Fin n) (Cinf E)) : Fin n → Cinf E := fun j => if j ≤ ρ then x ρ j else 0

def secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) : Fin n → Fin n → Cinf E :=
  fun i l w => secMat ρ (j w) (fun l => v l w) i l


open Classical in
def onMatInf (W : GL (Fin n) (Cinf E) → ℂ) (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℂ :=
  if h : IsUnit x then W h.unit else 0

def smoothMatInf (α : (Fin n → Fin n → Cinf E) → ℂ) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) : ℂ :=
  ∫ a : Fin n → Fin n → Cinf E, α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)


open Classical in
def toGLInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : GL (Fin n) (Cinf E) := if h : IsUnit x then h.unit else 1

theorem val_toGLInf {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    (toGLInf x : Matrix (Fin n) (Fin n) (Cinf E)) = x := by
  simp [toGLInf, h]

theorem onMatInf_val (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) :
    onMatInf W (g : Matrix (Fin n) (Fin n) (Cinf E)) = W g := by
  simp [onMatInf]

theorem onMatInf_of_isUnit (W : GL (Fin n) (Cinf E) → ℂ) {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    onMatInf W x = W (toGLInf x) := by
  simp [onMatInf, toGLInf, h]

theorem mem_levSetInf {r : ℕ} {g : GL (Fin n) (Cinf E)} : g ∈ levSetInf E n r ↔
    ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
      (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1 := by
  constructor
  · intro h i hi
    refine ⟨fun j hj => funext fun w => ?_, funext fun w => ?_⟩
    · exact (h w i hi).1 j hj
    · exact (h w i hi).2
  · intro h w i hi
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [compGL_apply, (h i hi).1 j hj]; rfl
    · rw [compGL_apply, (h i hi).2]; rfl

theorem isKerOpInf_dirac (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (h : GL (Fin n) (Cinf E)) :
    IsKerOpInf (fun W (_ : Z) g => W (g * h)) := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => h, fun _ => 0,
    ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_const _⟩,
    fun W _ z g => ?_⟩
  simp

def LevRepInf (E : Type) [Field E] [NumberField E] (n r : ℕ) (lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ) : Prop :=
  ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (B : Y × (Fin n → Fin n → Cinf E) → ℂ),
    ContDiffOn ℝ ∞ B {p | IsUnit (Matrix.of p.2)} → (∀ y, IsWhitInf fun g => B (y, matInf g)) →
    (∃ (D : Set Y) (C : Set (GL (Fin n) (Cinf E))), IsCompact D ∧ IsCompact C ∧ ∀ y, ∀ g ∈ levSetInf E n r,
      B (y, matInf g) ≠ 0 → y ∈ D ∧ ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u⁻¹ * g ∈ C) →
    ∃ T : (GL (Fin n) (Cinf E) → ℂ) → Y → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T ∧
      ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ y, ∀ g ∈ levSetInf E n r, T W y g = B (y, matInf g) * lam W

end GlobalTheory.JSW.MirCinf
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer.FrameFn

theorem analyticAt_lin {g : ℕ} (w : Fin g → ℂ) (p : Tot Empty g) :
    AnalyticAt ℂ (fun q : Tot Empty g ↦ (Real.pi : ℂ) * (q.2 ⬝ᵥ w)) p := by
  refine analyticAt_const.mul ?_
  unfold dotProduct
  refine Finset.analyticAt_fun_sum _ fun i _ ↦ AnalyticAt.mul ?_ analyticAt_const
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g ↦ ℂ) i).analyticAt p.2).comp analyticAt_snd

theorem isUnit_of_fn_ne {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} (f : Hol W)
    (h : ∀ p ∈ W, f.fn p ≠ 0) : IsUnit f := by
  have ha : AnalyticOnNhd ℂ (fun q ↦ (f.fn q)⁻¹) (W : Set E) := fun q hq ↦ (f.analytic q hq).inv (h q hq)
  refine IsUnit.of_mul_eq_one (b := Hol.mk (fun q ↦ (f.fn q)⁻¹) ha) (Hol.ext_fn fun p hp ↦ ?_)
  rw [Hol.fn_mul _ _ hp, Hol.fn_mk _ ha hp, mul_inv_cancel₀ (h p hp), ← Hol.ev_apply p hp, map_one]

theorem exists_frame_factor_log : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k) := by
  intro A _ g L u M u' _ hex H χ hAH K r hr j hj
  obtain ⟨-, -, hχ, hfac⟩ := hAH
  have hE : ∀ k (p : Tot Empty g) (hp : p ∈ K.W k),
      spMap (Hol.ev p hp).toRingHom ≫ r.x k = (u'.ex p.2).left := fun k p hp ↦ by
    rw [hex]; exact hr k p hp
  have hmem : ∀ k (U : A.left.Opens), ⊤ ≤ r.x k ⁻¹ᵁ U → ∀ p ∈ K.W k, ⊤ ≤ (u'.ex p.2).left ⁻¹ᵁ U :=
    fun k U hU p hp ↦ by
      rw [← hE k p hp]; exact (evalAt_fn_eq_valAt' (K.W k) (r.x k) U hU 0 p hp).1
  have hΛ : ∀ l : u.Λ, (l : Fin g → ℂ) ∈ u'.Λ := fun l ↦ (u'.ker _).1 (by rw [hex]; exact (u.ker _).2 l.2)
  have hper : ∀ (z : Fin g → ℂ) (l : u.Λ), u'.ex (z + l) = u'.ex z := fun z l ↦ by
    rw [u'.ex_add, (u'.ker _).2 (hΛ l), _root_.mul_one]
  have hfr : ∀ k, AnalyticOnNhd ℂ (fun p : Tot Empty g ↦ u'.fr (j k) p.2) (K.W k) := fun k p hp ↦
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (u'.hol (M.U (j k)) 0).1 (u'.fr_hol (j k)) p.2
      (hmem k _ (hj k) p hp)).comp analyticAt_snd
  let G : u.Λ → Tot Empty g → ℂ := fun l q ↦ (Real.pi : ℂ) * (q.2 ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))
  let e : u.Λ → Tot Empty g → ℂ := fun l q ↦ χ ⟨l, hΛ l⟩ * Complex.exp (G l q +
    Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))))
  have hG : ∀ l p, AnalyticAt ℂ (G l) p := fun l p ↦ analyticAt_lin _ p
  have he : ∀ l p, AnalyticAt ℂ (e l) p := fun l p ↦ analyticAt_const.mul ((hG l p).add analyticAt_const).cexp
  have hlaw : ∀ (l : u.Λ) i (p : Tot Empty g), ⊤ ≤ (u'.ex p.2).left ⁻¹ᵁ M.U i →
      u'.fr i p.2 = e l p * u'.fr i (p.2 + l) := fun l i p h ↦ hfac ⟨l, hΛ l⟩ i p.2 h
  obtain ⟨fr, vfr⟩ : ∃ fr : ∀ k, Hol (K.W k), ∀ k, ∀ p ∈ K.W k, (fr k).fn p = u'.fr (j k) p.2 :=
    ⟨fun k ↦ Hol.mk _ (hfr k), fun k p hp ↦ Hol.fn_mk _ _ hp⟩
  obtain ⟨a, va⟩ : ∃ a : u.Λ → ∀ k, Hol (K.W k), ∀ l k, ∀ p ∈ K.W k, (a l k).fn p = e l p :=
    ⟨fun l k ↦ Hol.mk (e l) fun p _ ↦ he l p, fun l k p hp ↦ Hol.fn_mk _ _ hp⟩
  obtain ⟨lg, vl⟩ : ∃ lg : u.Λ → ∀ k, Hol (K.W k), ∀ l k, ∀ p ∈ K.W k, (lg l k).fn p = G l p :=
    ⟨fun l k ↦ Hol.mk (G l) fun p _ ↦ hG l p, fun l k p hp ↦ Hol.fn_mk _ _ hp⟩
  refine ⟨fr, a, lg, fun k ↦ ?_, fun l k' k h hh ↦ ?_, fun l k ↦ ?_, fun l k c ↦ ?_,
    fun l m k'' k' h ↦ ?_, fun l m k'' k' h ↦ ?_, fun l m k ↦ ?_⟩
  · refine isUnit_of_fn_ne _ fun p hp ↦ ?_
    rw [vfr _ p hp]
    exact u'.fr_ne _ _ (hmem k _ (hj k) p hp)
  · refine Hol.ext_fn fun p hp ↦ ?_
    have h1 := hmem k' _ hh p hp
    rw [Hol.fn_mul _ _ hp, Hol.fn_mul _ _ hp, Charts.fn_sh h _ hp, vfr _ p hp, va _ _ p hp,
      vfr _ _ (K.maps h p hp), (evalAt_fn_eq_valAt' (K.W k') (r.x k') _ hh _ p hp).2, hE k' p hp,
      u'.fr_compat _ _ _ h1, hlaw l (j k) p (fun q hq ↦ (h1 hq).2)]
    exact (_root_.mul_assoc _ _ _).symm
  · refine isUnit_of_fn_ne _ fun p hp ↦ ?_
    rw [va _ _ p hp]
    refine mul_ne_zero (fun h0 ↦ ?_) (Complex.exp_ne_zero _)
    have := hχ ⟨l, hΛ l⟩
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · refine Hol.ext_fn fun p hp ↦ ?_
    have hd : HasFDerivAt (e l) _ p :=
      (((hG l p).differentiableAt.hasFDerivAt.add_const _).cexp).const_mul (χ ⟨l, hΛ l⟩)
    rw [Hol.fn_mul _ _ hp, dw, Hol.fn_der _ _ hp, Hol.fn_der _ _ hp, va _ _ p hp,
      Hol.fderiv_fn_congr _ (va l k) hp, Hol.fderiv_fn_congr _ (vl l k) hp, hd.fderiv]
    simp only [smul_apply, smul_eq_mul, e]
    ring
  · refine Hol.ext_fn fun p hp ↦ ?_
    rw [Hol.fn_mul _ _ hp, Charts.fn_sh h _ hp, va _ _ p hp, va _ _ p hp, va _ _ _ (K.maps h p hp)]
    have h0 := hmem k'' _ (hj k'') p hp
    have h1 := hlaw (l + m) _ p h0
    have h2 := hlaw m _ p h0
    have h3 := hlaw l (j k'') ((fibFam u).shift m p) (by
      change ⊤ ≤ (u'.ex (p.2 + m)).left ⁻¹ᵁ _
      rw [hper]; exact h0)
    have h4 : u'.fr (j k'') (p.2 + (l + m : u.Λ)) ≠ 0 := u'.fr_ne _ _ (by rw [hper]; exact h0)
    have h5 : ((fibFam u).shift m p).2 + (l : Fin g → ℂ) = p.2 + (l + m : u.Λ) := by
      change p.2 + (m : Fin g → ℂ) + l = p.2 + ((l : Fin g → ℂ) + m)
      abel
    rw [h5] at h3
    refine mul_right_cancel₀ h4 ?_
    rw [← h1, h2, mul_comm (e l _), _root_.mul_assoc (e m p), ← h3]
    rfl
  · refine Hol.ext_fn fun p hp ↦ ?_
    rw [Hol.fn_add _ _ hp, Charts.fn_sh h _ hp, vl _ _ p hp, vl _ _ _ (K.maps h p hp), K.fn_cst _ _ hp,
      Hol.fn_algebraMap _ (K.base _ p hp)]
    change (Real.pi : ℂ) * ((p.2 + (m : Fin g → ℂ)) ⬝ᵥ _) = (Real.pi : ℂ) * (p.2 ⬝ᵥ _) + _
    rw [add_dotProduct, mul_add]
  · refine Hol.ext_fn fun p hp ↦ ?_
    rw [Hol.fn_add _ _ hp, vl _ _ p hp, vl _ _ p hp, vl _ _ p hp]
    simp only [G, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add, mul_add]

end GlobalTheory.AnPer.FrameFn
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.TotTwoBaseChange.main | exact GlobalTheory.TotTwoBaseChange.main | (intros; apply GlobalTheory.TotTwoBaseChange.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bijective_liftSemi_tot0_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  first | exact @GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | exact GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective | (intros; apply GlobalTheory.totalZeroCochains_finiteCategory_baseChange_bijective <;> assumption)
end
