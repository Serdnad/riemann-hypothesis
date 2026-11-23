module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.JointApproxOfMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle689
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle603
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle279
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

def IsOp2 {l : ℕ} [Fact l.Prime] {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (n₁ n₂ : ℕ) (s : Per.Bcris l)
    (V : Matrix (Fin d) (Fin d) (Per.Bcris l)) : Prop :=
  ∃ U, IsPerU ρ U ∧ V * U.map ⇑(Per.φB l ^ n₂) = s • U.map ⇑(Per.φB l ^ n₁)

def LinkOp2 : Prop :=
  ∀ (R : Type) [CommRing R] (π s : R) (d d' : ℕ) (W Z Zs : Matrix (Fin d) (Fin d) R)
    (W₁ Z₁ Zs₁ : Matrix (Fin d') (Fin d') R) (Pm R₀ : Matrix (Fin d) (Fin d') R),
    Zs * Z = s • (1 : Matrix (Fin d) (Fin d) R) → Z₁ * Zs₁ = s • (1 : Matrix (Fin d') (Fin d') R) →
    (∀ i j, π ∣ (Pm * Z₁ - Z * R₀) i j) → (∀ i j, π ∣ (Pm * W₁ - W * R₀) i j) →
    ∀ i j, π ∣ ((s • (W * Zs)) * Pm - Pm * (s • (W₁ * Zs₁))) i j

def OpOne2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (τ₁ : Per.Acris l), IsUnit (iB l τ₁) → ∀ (K : FinExt l) (N k n₁ n₂ d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l])
    (y y' Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)),
    y * y' = τ₁ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    Q * Q' = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) →
    IsPerU ρ U → iB l τ₁ ^ N • U = (y * Q).map (iB l) →
    (y * Q) * (Q' * y') = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    (Q' * y') * (y * Q) = (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧
    IsUnit (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N)) ∧
    IsOp2 ρ n₁ n₂ (iB l ((phiA l ^ n₂) τ₁ ^ (3 * N) * (l : Per.Acris l) ^ (4 * k) * (phiA l ^ n₁) τ₁ ^ N))
      (((phiA l ^ n₂) (τ₁ ^ (2 * N) * (l : Per.Acris l) ^ (2 * k)) •
        ((y * Q).map ⇑(phiA l ^ n₁) * (Q' * y').map ⇑(phiA l ^ n₂))).map (iB l))

def LinkZ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N M : ℕ), ∃ n : ℕ, ∀ (k d d' : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (F : Frame bk N d ρ) (F' : Frame bk N d' ρ')
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y₁ : Matrix (Fin d') (Fin d') (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T →
    Y₁.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (Q Q' : Matrix (Fin d) (Fin d) (Per.Acris l)) (Q₁ Q₁' : Matrix (Fin d') (Fin d') (Per.Acris l)),
    IsSecQ bk N k F.A Q Q' → IsSecQ bk N k F'.A Q₁ Q₁' → ∀ (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (R : Matrix (Fin d) (Fin d') bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) →
    ∀ i j, (l : Per.Acris l) ^ M ∣ (Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk)) i j

def OpEx2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n₁ n₂ : ℕ), FixUr K n₁ → FixUr K n₂ →
    ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ m, Frame bk N (tw.d' m) fun g => (tw.ρ' m g).val)
      (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ m, (F m).IsCr) → F₀.IsCr →
      (∀ n', ∃ m, n' ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n' r) →
    ∃ (s : Per.Acris l) (V : Matrix (Fin d) (Fin d) (Per.Acris l)) (V' : ∀ m, Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Per.Acris l)),
      IsUnit (iB l s) ∧ IsOp2 ρ n₁ n₂ (iB l s) (V.map (iB l)) ∧ (∀ m, IsOp2 (tw.ρ' m) n₁ n₂ (iB l s) ((V' m).map (iB l))) ∧
      ∀ M, ∃ m, M ≤ m ∧ ∀ i j, (l : Per.Acris l) ^ M ∣ (V * (tw.Pi m).map (zC l) - (tw.Pi m).map (zC l) * V' m) i j

def FixOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Induces Bw → ∀ (g : ↥(Weil h)), FixUr Bw.Kw (alpha l g).natAbs

def WeilPhi2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)]
      (m : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P), m ∈ Dst P R → ∃ x : ↥(Dpst P R),
      (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₂) m ∧
      ((weilD Bw h P R g x : ↥(Dpst P R)) : (Fin a → ↥L.1) ⊗[ℚ_[l]] Bst P) = (phiV P ↥L.1 (Fin a → ↥L.1) ^ n₁) m

def TieRep2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (L : FinExt l) (a d : ℕ) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P R)],
    Module.finrank ℂ (WDSpace P ι R) = a → ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) ↥L.1)
      (e : Fin d → ℤ_[l]), (∀ g j (k : Fin a), R g (fun i => b j i k) = ∑ i, ((ρ g).val i j : ℚ_[l]) • fun i' => b i i' k) →
      ∑ i, (e i : ℚ_[l]) • b i = 1 → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (((b i).trace : ↥L.1) : Om l))
        (ι.symm (LinearMap.trace ℂ (WDSpace P ι R) (wdRho P ι Bw h hj R g)))

def Tie2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (g : ↥(Weil h)) (n₁ n₂ : ℕ), alpha l g = (n₂ : ℤ) - n₁ →
    ∀ (a d : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), IsCrysAt P Bw r →
    ∀ (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]),
      Reads ρ (r.comp Bw.e.symm.toMonoidHom) b e → ∀ (s : Per.Bcris l) (V : Matrix (Fin d) (Fin d) (Per.Bcris l)), IsOp2 ρ n₁ n₂ s V →
      IsTr (uB T) s (V *ᵥ fun i => Per.zB l (e i)) (fun i => (b i).trace) (wdTr P ι Bw h hj r g)

def ClosedTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ)
    (a : ℕ), 1 ≤ a → ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw)
      (J : (E →+* Om l) → Multiset ℤ) (r : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l)), Continuous r → IsSSRep r →
    ∀ (C : Set (Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Om l))) (g : ↥(Weil h)) (θ : Om l),
      JointApprox r C (fun ρ => wdTr P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype) g) θ →
      (∀ ρ ∈ C, Continuous ρ ∧ GlobalTheory.GalOfCusp.IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Om l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      wdTr P ι Bw h hj (r.comp (Dec (F := E) A).subtype) g = θ

def PowTr : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (x : WD h) (σ : ↥(Weil h)) (n : ℕ),
    GlobalTheory.CongPhi.phiSum x σ n = -(x.charPol (σ ^ n)).nextCoeff

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix GlobalTheory.TraceConjugationCover
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem coverJ_holds : CoverJ := by
  intro l _ Γ _ _ _ _ a L₀ r hr hss Cl hCl p θ hap
  classical
  obtain ⟨d, ρ, b, e, hρ, hreads, hind, hbr⟩ := GlobalTheory.T.exists_padicInt_span_image_lattice_regular l Γ a r hr
  obtain ⟨c, hc⟩ := GlobalTheory.T.small_traces_dvd_span_image l Γ a r hr hss
  obtain ⟨K, hK⟩ := traceL l a d b
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hch : ∀ ρ' : Γ →* GL (Fin a) (Om l), ∃ (L : FinExt l) (t : Finset (Matrix (Fin a) (Fin a) (Om l))), Continuous ρ' →
      (L₀.1 ≤ L.1 ∧ (∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) ∧ (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧
        (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧
        (∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c' y) • y = 1) ∧
        ∀ g, ∀ x ∈ t, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t, zOm l (c' y) • y) := by
    intro ρ'
    by_cases h : Continuous ρ'
    · obtain ⟨L, hLf, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a ρ' h
      haveI := hLf
      haveI := L₀.2
      let L' : FinExt l := ⟨L ⊔ L₀.1, inferInstance⟩
      have hL' : ∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L'.1 := fun g i j =>
        (le_sup_left : L ≤ L ⊔ L₀.1) (hL g i j)
      obtain ⟨t, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_stable_spanning_finset_matrices l Γ a ρ' L' h hL'
      exact ⟨L', t, fun _ => ⟨le_sup_right, hL', h1, h2, h3, h4⟩⟩
    · exact ⟨L₀, ∅, fun h' => absurd h' h⟩
  choose Lf tf htf using hch

  have hap' : ∀ n : ℕ, ∃ (s : Finset (Γ →* GL (Fin a) (Om l))) (cc : (Γ →* GL (Fin a) (Om l)) → Om l),
      (s : Set (Γ →* GL (Fin a) (Om l))) ⊆ Cl ∧ (∀ g, ‖trc r g - ∑ ρ' ∈ s, cc ρ' * trc ρ' g‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c)) ∧
        ‖θ - ∑ ρ' ∈ s, cc ρ' * p ρ'‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c) :=
    fun n => hap _ (by positivity)
  choose s cc hsCl hscc hth using hap'
  let U : ℕ → Finset (Γ →* GL (Fin a) (Om l)) := fun n => (Finset.range (n + 1)).biUnion s
  have hUmono : ∀ n, U n ⊆ U (n + 1) := fun n =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  have hsU : ∀ n, s n ⊆ U n := fun n => Finset.subset_biUnion_of_mem s (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hUCl : ∀ n, ∀ ρ' ∈ U n, ρ' ∈ Cl := by
    intro n ρ' h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
    exact hsCl j hj
  let m : ℕ → ℕ := fun n => (U n).card
  let ρs : ∀ n, Fin (m n) → (Γ →* GL (Fin a) (Om l)) := fun n k => ((U n).equivFin.symm k).1
  have hρsU : ∀ n k, ρs n k ∈ U n := fun n k => ((U n).equivFin.symm k).2
  have hρsC : ∀ n k, Continuous (ρs n k) := fun n k => hCl _ (hUCl n _ (hρsU n k))
  let cs : ∀ n, Fin (m n) → Om l := fun n k => if ρs n k ∈ s n then cc n (ρs n k) else 0
  have hcs : ∀ n (q : (Γ →* GL (Fin a) (Om l)) → Om l), ∑ k, cs n k * q (ρs n k) = ∑ ρ' ∈ s n, cc n ρ' * q ρ' := by
    intro n q
    have e1 : ∑ k, cs n k * q (ρs n k) = ∑ x : (U n), (if x.1 ∈ s n then cc n x.1 else 0) * q x.1 :=
      Fintype.sum_equiv (U n).equivFin.symm _ _ (fun k => rfl)
    rw [e1, Finset.sum_coe_sort (U n) (fun x => (if x ∈ s n then cc n x else 0) * q x)]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsU n)]
  have hK' : ∀ n, ∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ (n + K) • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n w
    rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
    calc ((l : ℝ)⁻¹) ^ (n + K) * ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul_of_nonneg_left (hK w) (by positivity)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hlay : ∀ n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin (m n) → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (Lf (ρs n k)).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin (m n) → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (Lf (ρs n k)).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs n k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ latT (ρs n) (fun k => tf (ρs n k)) M) ∧ (∀ x ∈ latT (ρs n) (fun k => tf (ρs n k)) M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ Carries r b (ρs n) (fun k => tf (ρs n k)) M bb P (n + K) ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs n k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n
    exact GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow l Γ a r d ρ b e hreads hind hbr c hc n (n + K) (by omega) (hK' n) (m n) (ρs n)
      (fun k => Lf (ρs n k)) (fun k => tf (ρs n k)) (hρsC n) (fun k => (htf _ (hρsC n k)).2.1)
      (fun k => (htf _ (hρsC n k)).2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.1)
      (fun k => (htf _ (hρsC n k)).2.2.2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.2.2) (cs n)
      (fun g => by rw [hcs n (fun ρ' => trc ρ' g)]; exact hscc n g)
  choose M₀ hM₀ using hlay
  let M : ℕ → ℕ := fun n => ∑ j ∈ Finset.range (n + 1), M₀ j
  have hMle : ∀ n, M₀ n ≤ M n := fun n =>
    Finset.single_le_sum (f := M₀) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hMmono : ∀ n, M n ≤ M (n + 1) := fun n => by
    simp only [M]
    rw [Finset.sum_range_succ _ (n + 1)]
    exact Nat.le_add_right _ _
  have hL := fun n => hM₀ n (M n) (hMle n)
  choose d' ρ' bb e' P hcont hbbL hind' hspan' hreads' hmem hcoord hcar honto hunit htr using hL
  let ι : ∀ n, Fin (m n) → Fin (m (n + 1)) := fun n k =>
    (U (n + 1)).equivFin ⟨((U n).equivFin.symm k).1, hUmono n ((U n).equivFin.symm k).2⟩
  have hι : ∀ n k, ρs (n + 1) (ι n k) = ρs n k := by
    intro n k
    simp [ρs, ι]
  have htrans : ∀ n, ∃ f : Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l], (∀ g, f * ((ρ' (n + 1) g : GL (Fin (d' (n + 1))) ℤ_[l]) : Matrix (Fin (d' (n + 1))) (Fin (d' (n + 1))) ℤ_[l]) = ((ρ' n g : GL (Fin (d' n)) ℤ_[l]) : Matrix (Fin (d' n)) (Fin (d' n)) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P n * f - P (n + 1)) i j := by
    intro n
    exact GlobalTheory.T.exists_equivariant_transition_matrix_cover l Γ a r d b hind (m n) (m (n + 1)) (ρs n) (ρs (n + 1)) (ι n) (hι n)
      (fun k => tf (ρs n k)) (fun k => tf (ρs (n + 1) k)) (fun k => by rw [hι n k]) (M n) (M (n + 1)) (hMmono n)
      (d' n) (d' (n + 1)) (ρ' n) (ρ' (n + 1)) (bb n) (bb (n + 1)) (e' n) (e' (n + 1)) (hind' n) (hreads' n)
      (hreads' (n + 1)) (hmem (n + 1)) (hcoord n) (P n) (P (n + 1)) n (n + K) (n + 1 + K) (by omega) (by omega)
      (hcar n) (hcar (n + 1))
  choose f hfe hfP using htrans
  let tw : Tower ρ :=
    { d' := d', ρ' := ρ', Pi := P, onto := honto, f := f, f_equi := hfe, f_Pi := hfP }
  let lay : ∀ n, Layer L₀ Cl (tw.ρ' n) := fun n =>
    { m := m n, rep := ρs n, mem := fun k => hUCl n _ (hρsU n k), L := fun k => Lf (ρs n k),
      le := fun k => (htf _ (hρsC n k)).1, rep_mem := fun k => (htf _ (hρsC n k)).2.1, b := bb n,
      b_mem := hbbL n, indep := hind' n, span := hspan' n, e := e' n, reads := hreads' n, c := cs n }
  refine ⟨{ d := d, ρ := ρ, cont := hρ, b := b, e := e, reads := hreads, tw := tw, cont' := hcont, lay := lay,
            unit := hunit, trace := htr }, fun n => ?_⟩
  show ‖θ - ∑ k, cs n k * p (ρs n k)‖ ≤ _
  rw [hcs n p]
  refine (hth n).trans ?_
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (by omega)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end
