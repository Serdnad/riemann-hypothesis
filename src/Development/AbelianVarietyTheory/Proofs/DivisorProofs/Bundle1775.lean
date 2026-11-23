module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Mathlib.Algebra.CharP.Pi
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.KirArchTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_here : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_map_pInf_here :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_here)

theorem ent {R : Type} [CommRing R] (p : Ad E →+* R) (g : GA E a) (i j : Fin a) :
    ((GeneralLinearGroup.map p g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j = p ((g : Matrix (Fin a) (Fin a) (Ad E)) i j) :=
  rfl

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem eq_finGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E a (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem comm_infGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin a) (Cinf E)) :
    q * infGL E a y = infGL E a y * q := by
  rw [eq_finGL hq]
  exact (infGL_comm y _).symm

theorem infGL_apply_of_ne (y : GL (Fin a) (Cinf E)) {i j : Fin a} (h : i ≠ j) :
    (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) := by
  refine ad_ext ?_ ?_
  · rw [← ent, pInf_infGL, pInf_sInf]
  · rw [← ent, pFin_infGL, pFin_sInf]
    simp [Matrix.one_apply, h]

theorem infGL_mem_NA {u : GL (Fin a) (Cinf E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a)) :
    infGL E a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · refine ad_ext ?_ ?_
    · rw [map_zero, ← ent, pInf_infGL]; exact h1 i j hji
    · rw [map_zero, ← ent, pFin_infGL]; simp [Matrix.one_apply, hji.ne']
  · refine ad_ext ?_ ?_
    · rw [map_one, ← ent, pInf_infGL]; exact h2 i
    · rw [map_one, ← ent, pFin_infGL]; simp

theorem psiN_infGL (u : GL (Fin a) (Cinf E)) :
    GlobalTheory.JSW.psiN (infGL E a u) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) := by
  have hs : GlobalTheory.Whittaker.superDiag (infGL E a u) = sInf E (GlobalTheory.Whittaker.superDiag u) := by

    simp only [GlobalTheory.Whittaker.superDiag, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      intro e; subst e; simp at hj
    exact infGL_apply_of_ne u hij
  have h := GlobalTheory.ThetaPoisson.adelicChar_sInf_sum (E := E) (n := 1) (fun _ => GlobalTheory.Whittaker.superDiag u) (fun _ => 1)
  simp only [Fin.sum_univ_one, mul_one, Pi.one_apply] at h
  rw [GlobalTheory.JSW.psiN, hs, h]

theorem map_pInf_mem_unipB {u : GA E a} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := a)) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a) := by
  refine (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [ent, hu.1 i j hji, map_zero]
  · rw [ent, hu.2 i, map_one]

theorem ad_eq_ite_iff (x : Ad E) (c : Prop) [Decidable c] :
    x = (if c then 1 else 0) ↔ pInf E x = (if c then 1 else 0) ∧ pFin E x = (if c then 1 else 0) := by
  refine ⟨fun h => ?_, fun h => ad_ext ?_ ?_⟩
  · subst h; split_ifs <;> simp
  · rw [h.1]; split_ifs <;> simp
  · rw [h.2]; split_ifs <;> simp

theorem mem_mirS_iff {m : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) {q : GA E (m + 1)}
    (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin (m + 1)) (Cinf E)) :
    q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ↔
      (q ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ ∀ j, ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧
      y ∈ GlobalTheory.JSW.mirSet (Cinf E) m := by
  have hsup : ∀ w : HeightOneSpectrum (𝓞 E),
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E (m + 1) y) = 1 :=
    fun w => map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
  have hI : GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y := by
    rw [map_mul, hq, one_mul, pInf_infGL]
  have hF : GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q := by
    rw [map_mul, pFin_infGL, mul_one]
  have hrow : ∀ j, ((q * infGL E (m + 1) y : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (if j = Fin.last m then 1 else 0) ↔
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = (if j = Fin.last m then 1 else 0) ∧
      ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E))
        (Fin.last m) j = (if j = Fin.last m then 1 else 0) := by
    intro j
    rw [ad_eq_ite_iff, ← ent, ← ent, hI, hF]
  have hS : q * infGL E (m + 1) y ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ↔ q ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    rw [map_mul, hsup, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hS.1 h1, fun j => ((hrow j).1 (h2 j)).2⟩, fun j => ((hrow j).1 (h2 j)).1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨hS.2 h1, fun j => (hrow j).2 ⟨h3 j, h2 j⟩⟩

end GlobalTheory.JSW.KirArchTransfer

namespace GlobalTheory.JSW.KirArchTransfer

theorem kirillov_arch : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (q : GA E (m + 1)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b q) (invSet E (m + 1)) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (q * infGL E (m + 1) y)) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (q * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → GeneralLinearGroup.map (pInf E) q = 1 → W q ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GlobalTheory.JSW.kerInf ν k γ W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y) := by
  intro E _ _ _ m S b W q hbe hbC hbs hWe hWc hWg hq hWq
  classical
  by_cases hne : ∃ y₀ : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y₀ ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m)
  · obtain ⟨y₀, hy₀⟩ := hne
    have hP := ((mem_mirS_iff S hq y₀).1 hy₀).1
    have hiff : ∀ y, q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ↔ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m :=
      fun y => (mem_mirS_iff S hq y).trans ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
    have heq : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
        ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y,
          F (q * infGL E (m + 1) (u * y)) =
            (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * F (q * infGL E (m + 1) y) := by
      intro F hF u hu y
      rw [map_mul, ← mul_assoc, comm_infGL hq u, mul_assoc, hF _ (infGL_mem_NA hu), psiN_infGL]
    obtain ⟨C, hC, hCp⟩ := hbC
    obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ := GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic E m (fun y => b (q * infGL E (m + 1) y))
      (fun y => W (q * infGL E (m + 1) y)) (heq b hbe) ⟨chart b q, hbs, fun y => chart_val b q y⟩
      ⟨GeneralLinearGroup.map (pInf E) '' C, hC.image continuous_map_pInf_here, fun y hy hb0 => by
        obtain ⟨u, hu, hu'⟩ := hCp _ ((hiff y).2 hy) hb0
        refine ⟨GeneralLinearGroup.map (pInf E) u, map_pInf_mem_unipB hu, _, hu', ?_⟩
        rw [map_mul, map_inv, map_mul, hq, one_mul, pInf_infGL]⟩
      (heq W hWe) hWc hWg (by simpa using hWq)
    refine ⟨X, inferInstance, ν, inferInstance, k, γ, hk, fun y hy => ?_⟩
    rw [← hK y ((hiff y).1 hy)]
    simp only [GlobalTheory.JSW.kerInf]
    congr 1
    funext x
    rw [map_mul, mul_assoc]
  · exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => 1, GlobalTheory.JSW.isRapidInf_dirac 1,
      fun y hy => (hne ⟨y, hy⟩).elim⟩

end GlobalTheory.JSW.KirArchTransfer
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

variable {D : D7}

def IsHalfIdem (D : D7) (ε : AE D) : Prop :=
  ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧
    (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧
    ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0

theorem exists_isHalfIdem (D : D7) : ∃ ε, IsHalfIdem D ε := GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D

theorem finRat_eq (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T x = (1 - realIdem D) • (ratW T S x : WO S T) := by
  funext i j
  refine adele_ext ?_ ?_
  · exact (congrFun (congrFun (finRat_inf S T x) i) j).trans (congrFun (congrFun (fin_smul_fin (ratW T S x)) i) j).symm
  · show finPart D (ratW T S x i j) = finPart D ((1 - realIdem D) * ratW T S x i j)
    rw [RingHom.map_mul, RingHom.map_sub, finPart_realIdem, RingHom.map_one, sub_zero, one_mul]

theorem finRat_smul (S T : HSp D) (c : D.host.E) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T (c • x) = incA D c • finRat S T x := by
  rw [finRat_eq, finRat_eq, smul_comm]
  congr 1
  funext i j
  exact (incA D).map_mul c (x i j)

def latQ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | finRat S T x ∈ latO S T LS LT fun _ => True}
  add_mem' {x y} hx hy := by
    show finRat S T (x + y) ∈ latO S T LS LT fun _ => True
    rw [map_add (f := _)]
    exact add_mem hx hy
  zero_mem' := by
    show finRat S T 0 ∈ latO S T LS LT fun _ => True
    rw [map_zero]
    exact zero_mem _
  smul_mem' r x hx := by
    show finRat S T ((r : D.host.E) • x) ∈ latO S T LS LT fun _ => True
    rw [finRat_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ _ (finPart_intA r) _ hx

theorem mem_latQ {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} :
    x ∈ latQ S T LS LT ↔ finRat S T x ∈ latO S T LS LT fun _ => True := Iff.rfl

def gamQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  ψ (symplO S T (finRat S T x) (finRat S T y))


open Classical in
def chiLat (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) : ℂ :=
  if (1 - realIdem D) • x ∈ latO S T LS LT (fun _ => True) then
    ψ (symplOH S T (intA D w • (1 - realIdem D) • x) ((1 - realIdem D) • x)) else 0

def serO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) : WO S T → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WO S T) (piW θ T S) (iotaW σ T S) (fun x y => ψ (symplOH S T x y))
    (omO S T) (jO S T sS sT) (ratL T S) (chiLat ψ S T LS LT w) a

def actR (S T : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : RW T S :=
  fun τ => (b τ * Matrix.of (v τ) * a τ : Matrix (Fin T.rank) (Fin S.rank) ℂ)

def gaussR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omO S T (actR S T a b v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (actR S T a b v - v) (jO S T sS sT (actR S T a b v - v)) : ℝ))

def sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    Module.End K (Matrix (Fin m) (Fin n) K) where
  toFun x := b * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem sandw_apply {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K)
    (x : Matrix (Fin m) (Fin n) K) : sandw b a x = b * x * a := rfl

theorem toMatrix_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) (sandw b a) = b ⊗ₖ aᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, sandw_apply]
  have : ∀ x : Matrix (Fin m) (Fin n) K, (Matrix.stdBasis K (Fin m) (Fin n)).repr x (i, j) = x i j := fun x => by
    simp [Matrix.stdBasis]
  rw [this]
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem det_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a) = (b ⊗ₖ aᵀ).det := by
  rw [← toMatrix_sandw, LinearMap.det_toMatrix]

theorem det_sandw_sub_one {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a - 1) = (b ⊗ₖ aᵀ - 1).det := by
  rw [← toMatrix_sandw, ← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), map_sub, LinearMap.toMatrix_one]

end GlobalTheory.RatAut

end
end

section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.SumSlope

variable {K : Type} [Field K] [NumberField K] {O : Type} [Fintype O] [DecidableEq O] {ι : O → Type}
  [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)]

def sumNorm (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (σ : K →+* ℂ) (x : ∀ o, ι o → K) : ℝ :=
  Real.sqrt (∑ o, matNorm (Y o) σ (x o) ^ 2)

abbrev inc (o : O) : (ι o → K) →ₗ[K] (∀ o, ι o → K) := LinearMap.single K (fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem inc_injective (o : O) : Function.Injective (inc (K := K) (ι := ι) o) :=
  Pi.single_injective (M := fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem iSupIndep_range_inc : iSupIndep fun o => LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
  have h : (⨆ p, ⨆ (_ : p ≠ o), LinearMap.range (inc (K := K) (ι := ι) p)) ≤
      LinearMap.ker (LinearMap.proj (R := K) (φ := fun o => ι o → K) o) := by
    refine iSup₂_le fun p hp => ?_
    rintro _ ⟨x, rfl⟩
    simp [Pi.single_eq_of_ne hp.symm]
  refine Submodule.disjoint_def.2 ?_
  rintro _ ⟨x, rfl⟩ hx
  have h1 : x = 0 := by simpa using h hx
  rw [h1, map_zero]

variable (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ)

omit [NumberField K] [Fintype O] [DecidableEq O] [∀ o, DecidableEq (ι o)] in
theorem matNorm_zero (o : O) (σ : K →+* ℂ) : matNorm (Y o) σ 0 = 0 := by
  have h : (fun j : ι o => σ ((0 : ι o → K) j)) = 0 := by funext j; simp
  simp only [matNorm, h, Matrix.mulVec_zero]
  simp

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_inc (o : O) (σ : K →+* ℂ) (x : ι o → K) : sumNorm Y σ (inc o x) = matNorm (Y o) σ x := by
  unfold sumNorm
  rw [Finset.sum_eq_single o]
  · simp only [LinearMap.coe_single, Pi.single_eq_same]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  · intro p _ hp
    simp only [LinearMap.coe_single, Pi.single_eq_of_ne hp, matNorm_zero]
    simp
  · intro h; exact absurd (Finset.mem_univ o) h

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_sum (σ : K →+* ℂ) (f : O → ∀ o, ι o → K) (hf : ∀ o, f o ∈ LinearMap.range (inc (K := K) (ι := ι) o)) :
    sumNorm Y σ (∑ o, f o) ^ 2 = ∑ o, sumNorm Y σ (f o) ^ 2 := by
  choose g hg using hf
  have h : ∑ o, f o = g := by
    rw [← Finset.univ_sum_single g]
    exact Finset.sum_congr rfl fun o _ => (hg o).symm
  rw [h, sumNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun o _ => by rw [← hg o, sumNorm_inc]

theorem hasGram_sumNorm (hY : ∀ o σ, (Y o σ).det ≠ 0) : HasGram (sumNorm Y) := by
  refine GlobalTheory.OrthSumGram.orth_sum_hasGram K _ O (sumNorm Y) (fun o => LinearMap.range (inc (K := K) (ι := ι) o))
    (fun _ _ => Real.sqrt_nonneg _) iSupIndep_range_inc (LinearMap.iSup_range_single K _) (fun o => ?_)
    (fun σ f => sumNorm_sum Y σ (fun o => f o) fun o => (f o).2)
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := (isGram_matNorm K (ι o) (Y o) (hY o)).2
  let e := LinearEquiv.ofInjective (inc (K := K) (ι := ι) o) (inc_injective o)
  have h := GlobalTheory.RestrictNorm.hasGram_comp (matNorm (Y o)) e.symm.toLinearMap e.symm.injective b X hG
  convert h using 3 with σ x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact sumNorm_inc Y o σ y

theorem le_slope_sq_of_sum : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (O : Type) [Fintype O] [Nonempty O] (ι : O → Type) [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] [∀ o, Nonempty (ι o)] (Nv : (K →+* ℂ) → V → ℝ) (M : Submodule (𝓞 K) V) (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (L : ∀ o, Submodule (𝓞 K) (ι o → K)) (Φ : (∀ o, ι o → K) →ₗ[K] V) (s : ℝ), HasGram Nv → M.FG → (∀ o σ, (Y o σ).det ≠ 0) → (∀ o, Submodule.IsFullLattice K (L o)) → Function.Injective Φ → (∀ x, (∀ o, x o ∈ L o) → Φ x ∈ M) → (∀ v ∈ M, v ∈ LinearMap.range Φ) → (∀ σ x, Nv σ (Φ x) ^ 2 ≤ ∑ o, matNorm (Y o) σ (x o) ^ 2) → (∀ o, s ≤ slope_sq (matNorm (Y o)) (L o)) → s ≤ slope_sq Nv M := by
  intro K _ _ _ V _ _ _ _ O _ _ ι _ _ _ Nv M Y L Φ s hNv hM hY hL hΦ hin hrg hle hs
  classical
  have hG := hasGram_sumNorm Y hY
  let P : O → Submodule (𝓞 K) (∀ o, ι o → K) := fun o => (L o).map ((inc o).restrictScalars (𝓞 K))
  have hsp : ∀ o, Submodule.span K (P o : Set (∀ o, ι o → K)) = LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
    letI := hL o
    have hspan : Submodule.span K (L o : Set (ι o → K)) = ⊤ := Submodule.IsFullLattice.span_eq_top
    rw [LinearMap.range_eq_map, ← hspan, ← Submodule.span_image]
    rfl
  have hP : ∀ o, (P o).FG := fun o => (hL o).fg.map _
  obtain ⟨hrk, hdeg⟩ := GlobalTheory.OrthRankDeg.rkK_deg_iSup K _ O (sumNorm Y) P hG hP
    fun σ f hf => sumNorm_sum Y σ f fun o => hsp o ▸ hf o
  have hd : ∀ o, (Formalism.HN.rkK (P o) : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (P o) := fun o => by
    obtain ⟨h1, h2⟩ := (GlobalTheory.RestrictNorm.restrict_deg K _ _ (sumNorm Y) (inc o) (inc_injective o) hG).2
      (L o) (hL o).fg
    have h3 : (fun σ x => sumNorm Y σ (inc o x)) = matNorm (Y o) := by
      funext σ x; exact sumNorm_inc Y o σ x
    rw [h3] at h2
    show (Formalism.HN.rkK ((L o).map _) : ℝ) * _ ≤ GlobalTheory.AllWt.deg _ ((L o).map _)
    rw [h1, h2, GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope]
    exact mul_le_mul_of_nonneg_left (by linarith [hs o]) (Nat.cast_nonneg _)
  have htop : Submodule.span K ((⨆ o, P o : Submodule (𝓞 K) _) : Set (∀ o, ι o → K)) = ⊤ := by
    apply top_unique
    rw [← LinearMap.iSup_range_single K (fun o => ι o → K)]
    refine iSup_le fun o => ?_
    rw [← hsp o]
    exact Submodule.span_mono (le_iSup P o)
  have hmap : (⨆ o, P o).map (Φ.restrictScalars (𝓞 K)) ≤ M := by
    rw [Submodule.map_iSup]
    refine iSup_le fun o => ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine hin _ fun p => ?_
    by_cases hp : p = o
    · subst hp; simpa using hx
    · simp [Pi.single_eq_of_ne hp]
  have hspM : Submodule.span K (M : Set V) = LinearMap.range Φ := by
    refine le_antisymm (Submodule.span_le.2 hrg) ?_
    rw [LinearMap.range_eq_map, ← htop, ← Submodule.span_image]
    exact Submodule.span_mono hmap
  have hrkS : Formalism.HN.rkK (⨆ o, P o) = finrank K (∀ o, ι o → K) := by
    rw [Formalism.HN.rkK, htop, finrank_top]
  have hrkM : Formalism.HN.rkK M = Formalism.HN.rkK (⨆ o, P o) := by
    rw [hrkS, Formalism.HN.rkK, hspM, LinearMap.finrank_range_of_inj hΦ]
  have key := GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le K _ V (sumNorm Y) Nv Φ (fun _ => 1) (⨆ o, P o) M ⊤ hG hNv hΦ
    (fun _ => one_pos) (fun _ => rfl)
    (fun σ x => by rw [one_mul]; exact (le_abs_self _).trans (Real.abs_le_sqrt (hle σ x)))
    (Submodule.fg_iSup _ hP) hM top_ne_bot (by rwa [Submodule.top_smul]) hrkM
  have hpos : (0 : ℝ) < Formalism.HN.rkK M := by
    rw [hrkM, hrkS]
    exact_mod_cast Module.finrank_pos
  have h1 : (Formalism.HN.rkK M : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (⨆ o, P o) := by
    rw [hdeg, hrkM, hrk, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun o _ => hd o
  simp only [Real.log_one, Finset.sum_const_zero, Ideal.absNorm_top, Nat.cast_one, zero_div, neg_zero, sub_zero,
    mul_zero, add_zero] at key
  have h2 := h1.trans key
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope] at h2
  have h3 := le_of_mul_le_mul_left h2 hpos
  linarith

end GlobalTheory.SumSlope

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermLineBundlePair_sectionBall_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  first | exact @GlobalTheory.HSNef.bl_finite | exact GlobalTheory.HSNef.bl_finite | (intros; apply GlobalTheory.HSNef.bl_finite <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quotientHeight_lower_bound_short_isotropic_vector : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → ∀ a ∈ GfC V, ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ z ∈ ZI V ξ, ∀ u ∈ GinfC V, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ τ i, ‖((archM V (θ τ) u)⁻¹.mulVec (fun j => tauE D τ (ξ j))) i‖ ≤ δ) → c ≤ δ * (GlobalTheory.CuspDecay.quotHeight θ V (z * a * u) : ℝ) ^ N := by
  first | exact @GlobalTheory.HolDict.quotHeight_lower_bound | exact GlobalTheory.HolDict.quotHeight_lower_bound | (intros; apply GlobalTheory.HolDict.quotHeight_lower_bound <;> assumption)
end
