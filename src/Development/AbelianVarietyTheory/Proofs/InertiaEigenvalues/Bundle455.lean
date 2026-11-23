module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle377
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle441
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLSaturatedOfSelmerSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountOfSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle322
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_io_smul_of {O RA RW M : Type} [CommRing O] [TopologicalSpace O] [CommRing RA]
    [Algebra O RA] [CommRing RW] [Algebra O RW] [AddCommGroup M] [Module RW M] [Module O M]
    [IsScalarTower O RW M] [TopologicalSpace M] [IsTopologicalAddGroup M] {n : ℕ}
    (io : LetA O n →ₐ[O] RA) (inc : RA →ₐ[O] RW) (y : M) (πA : RA) (hπ : io letπ = πA)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ z : RA, inc (πA ^ k * z) • y ∈ U)
    (hlin : ∀ f : (ZMod n → O) →ₗ[O] M, Continuous f) :
    Continuous fun a : LetA O n => inc (io a) • y := by
  let Φ : LetA O n →+ M :=
    { toFun := fun a => inc (io a) • y
      map_zero' := by simp only [map_zero, zero_smul]
      map_add' := fun a c => by simp only [map_add, add_smul] }
  refine GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous Φ ?_ ?_
  · intro U hU
    obtain ⟨k, hk⟩ := hsmall U hU
    refine ⟨k, fun r => ?_⟩
    have hΦ : Φ (letπ ^ k * r) = inc (πA ^ k * io r) • y := by
      show inc (io (letπ ^ k * r)) • y = _
      rw [map_mul, map_pow, hπ]
    rw [hΦ]
    exact hk _
  · intro j
    let f : (ZMod n → O) →ₗ[O] M :=
      { toFun := fun c => inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y)
        map_add' := fun c c' => by
          have : (fun i => PowerSeries.C ((c + c') i)) =
              (fun i => PowerSeries.C (c i)) + fun i => PowerSeries.C (c' i) := by
            funext i; exact map_add PowerSeries.C (c i) (c' i)
          simp only [this, map_add (f := _), add_smul]
        map_smul' := fun o c => by
          have : (fun i => PowerSeries.C ((o • c) i)) = o • (fun i => PowerSeries.C (c i)) := by
            funext i
            simp only [Pi.smul_apply, smul_eq_mul, PowerSeries.smul_eq_C_mul, map_mul]
          simp only [this, map_smul, smul_assoc, RingHom.id_apply] }
    refine (hlin f).congr fun c => ?_
    have hc : (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j : LetA O n) =
        (fun i => PowerSeries.C (c i)) * letπ ^ j := by
      funext i; rw [Pi.mul_apply, Pi.pow_apply]; rfl
    show inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y) =
      inc (io (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) • y
    rw [hc, map_mul, map_mul, mul_smul, map_pow, map_pow]

end GlobalTheory.WeakClosed

namespace GlobalTheory.WeakClosed

theorem isTopologicalAddGroup_twTop {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d) : letI := twTop T b; IsTopologicalAddGroup (TW (RW LL) T) := by
  let := cbValued l
  let := zlMod T
  have := zlTower T
  let : TopologicalSpace (WCb l) := wTop l
  let : TopologicalSpace (TW (RW LL) T) := twTop T b
  have : IsTopologicalRing (Cb l) := inferInstance
  have : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  exact Topology.IsInducing.isTopologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩

theorem finrank_maxUnramifiedSubfield_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) : 0 < Module.finrank ℚ_[l] ↥(K0 K) := by
  have hle : K0 K ≤ K.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] (K0 K) :=
    let := K.2
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  exact Module.finrank_pos

-- Resolve the tensor-product actions while the scalar rings are still abstract.
private theorem tensorProduct_left_scalarTower {O R N : Type} [CommRing O] [CommRing R]
    [Algebra O R] [AddCommGroup N] [Module O N] : IsScalarTower O R (R ⊗[O] N) :=
  TensorProduct.isScalarTower_left

theorem continuous_inclR_io_smul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  intro l hl P AI K s LL h W E T d e b bO y
  let algA : Algebra ↥(OL LL) (RA LL) :=
    Algebra.TensorProduct.leftAlgebra (R := ℤ_[l]) (A := ↥(OL LL)) (B := Ainf l)
  let algW : Algebra ↥(OL LL) (RW LL) :=
    Algebra.TensorProduct.leftAlgebra (R := ℤ_[l]) (A := ↥(OL LL)) (B := WCb l)
  let modW : Module ↥(OL LL) (RW LL) := Algebra.toModule
  let modSelf : Module (RW LL) (RW LL) := Semiring.toModule
  let modO : Module ↥(OL LL) (TW (RW LL) T) :=
    TensorProduct.instModule (R := ↥(OL LL)) (M := RW LL) (N := ↥T.L.T)
  let modRW : Module (RW LL) (TW (RW LL) T) :=
    TensorProduct.leftModule (R := ↥(OL LL)) (R'' := RW LL) (M := RW LL) (N := ↥T.L.T)
  let tT := twTop T b
  let tO := oTop bO
  have ht := isTopologicalAddGroup_twTop T b
  have hn : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨(finrank_maxUnramifiedSubfield_pos K).ne'⟩
  have hTower := @tensorProduct_left_scalarTower ↥(OL LL) (RW LL) ↥T.L.T _ _ algW _ _
  have hlin := @GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord l hl
    ↥(OL LL) (TW (RW LL) T) (ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    _ _ (ZMod.fintype _) _ modO tT ht e bO (GlobalTheory.T.continuous_padicInt_smul_latB T b)
  exact @continuous_io_smul_of ↥(OL LL) (RA LL) (RW LL) (TW (RW LL) T)
    _ tO _ algA _ algW _ modRW modO hTower tT ht _
    E.tie.io (inclR LL) y _ E.tie.io_π (GlobalTheory.T.exists_pow_inclR_smul_mem' AI s T b y) hlin

end GlobalTheory.WeakClosed
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.SelOrder

theorem cupB_sub_cob {Γ A M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
    {n : ℕ} (χ : Γ → ZMod n) (π : Representation A Γ M) (π' : Representation A Γ M') (P : M →+ M' →+ ZMod n)
    (hP : ∀ g x y, P (π g x) (π' g y) = χ g * P x y) (x : Γ → M) (y y' : Γ → M') (m : M')
    (hx : Continuous x) (hx' : ∀ g h, x (g * h) = x g + π g (x h)) (hm : Continuous fun g => π' g m)
    (hy : ∀ g, y' g = y g - (π' g m - m))
    (h : CupB χ (fun g m => π' g m) P x y) : CupB χ (fun g m => π' g m) P x y' := by
  obtain ⟨F, hF, h⟩ := h
  refine ⟨F + fun g => P (x g) (π' g m), hF.add (((IsLocallyConstant.iff_continuous _).2 (hx.prodMk hm)).comp
    fun p : M × M' => P p.1 p.2), fun g k => ?_⟩
  have h1 := h g k
  have h2 := hP g (x k) (π' k m)
  simp only [hy, map_add (f := _), map_sub, AddMonoidHom.add_apply, Pi.add_apply, hx', map_mul, Module.End.mul_apply] at h1 ⊢
  linear_combination h1 + h2

theorem tors_all (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (B : Type) [AddCommGroup B] [Module A B] :
    Tors A B := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine fun b => ⟨n, fun x hx => ?_⟩
  rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

section General

open Formalism.GaloisCohomology

variable {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] (n : ℕ) {Λ W W' : Type} [CommRing Λ]
  [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W]
  [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W']

theorem order_formula (hPT : PoitouTateTotallyComplex) (hLF : LocalFiniteness) (hLD : LocalTateDuality)
    (hLE : LocalEulerChar) (hGF : GlobalFiniteness) (hGE : GlobalEulerChar)
    (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)) (hn : 0 < n)
    (hc : ContAction ρ) (hc' : ContAction ρ') (hl : ∀ x, (∀ y, P x y = 0) → x = 0) (hr : ∀ y, (∀ x, P x y = 0) → y = 0)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y)
    (A : Places F Ω) (T : Set (HeightOneSpectrum (𝓞 F))) (hT : T.Finite) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (hTl : ∀ v ∈ T, v ∉ placesOver F l) (hQl : ∀ v ∈ Q, v ∉ placesOver F l)
    (hur : ∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ B : ValuationSubring Ω, IsPlaceOver B v →
      ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1)
    (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (C : Set (H1 ρ'))
    (hC : ∀ c, c ∈ C ↔ ∃ y : Z1 ρ',
      ((∀ v, v ∉ placesOver F l → v ∉ T → v ∉ Q → ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧
        (∀ v, v ∈ T ∨ v ∈ Q → ∃ m, ∀ g ∈ Dec (F := F) (A.1 v), y.1 g = ρ' g m - m) ∧
        ∀ v ∈ placesOver F l, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v →
          CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
            (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) ∧ c = Submodule.Quotient.mk y)
    (h0 : H0 ρ = ⊥) (h0' : H0 ρ' = ⊥) (hT0 : ∀ v ∈ T, H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype) = ⊥)
    (hcount : ∏ᶠ v ∈ placesOver F l, Nat.card (L v) =
      (∏ᶠ v ∈ placesOver F l, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        Nat.card W ^ InfinitePlace.nrComplexPlaces F) :
    Finite C ∧ Nat.card (SelAll ρ A (bkCond ρ A l (T ∪ ↑Q) L)) =
      Nat.card C * ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
  classical
  have hfin := GlobalTheory.SelObstruction.finite_above (F := F) l
  have hsub : ∀ {M : Type} [AddCommGroup M] [Module Λ M] [TopologicalSpace M] [DiscreteTopology M]
      (π : Representation Λ (G F Ω) M), ContAction π → ∀ U : Subgroup (G F Ω), ContAction (π.comp U.subtype) :=
    fun π h U => h.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hloc := fun v => GlobalTheory.T.localDuality_perfect_pair_finite_modules hLF hLD hLE F Ω l n (A.1 v) v (A.2 v) Λ W W'
    (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P hn (hsub ρ hc _) (hsub ρ' hc' _)
    hl hr (fun g x y => hP g.1 x y)
  have hS : ∀ v, v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∈ placesOver F l ∨ v ∈ T ∨ v ∈ Q := by simp
  have hS' : ∀ v, v ∉ hfin.toFinset ∪ (hT.toFinset ∪ Q) ↔ v ∉ placesOver F l ∧ v ∉ T ∧ v ∉ Q := fun v => by
    rw [hS, not_or, not_or]
  have hnl : ∀ v, v ∈ T ∨ v ∈ Q → v ∉ placesOver F l := fun v h => h.elim (hTl v) (hQl v)
  have b1 : ∀ v ∈ placesOver F l, bkCond ρ A l (T ∪ ↑Q) L v = L v := fun v hv => if_pos hv
  have b2 : ∀ v, v ∈ T ∨ v ∈ Q → bkCond ρ A l (T ∪ ↑Q) L v = ⊤ := fun v hv => (if_neg (hnl v hv)).trans (if_pos hv)
  obtain ⟨fC, e⟩ := GlobalTheory.T.greenbergWiles_pair_alt hPT hLF hGF hGE F Ω l n Λ W W' ρ ρ' P hn hc hc' hl hr hP
    (hfin.toFinset ∪ (hT.toFinset ∪ Q)) A (fun v hv => (hS v).2 (.inl hv))
    (fun v hv => hur v ((hS' v).1 hv).1 ((hS' v).1 hv).2.1 ((hS' v).1 hv).2.2) (bkCond ρ A l (T ∪ ↑Q) L)
    (fun v hv => (if_neg ((hS' v).1 hv).1).trans (if_neg (not_or.2 ((hS' v).1 hv).2))) C (fun y => by
      rw [hC]
      constructor
      · rintro ⟨y', ⟨k1, k2, k3⟩, e⟩
        have e' : (y' - y).1 ∈ B1 ρ' := (Submodule.Quotient.eq ((B1 ρ').comap (Z1 ρ').subtype)).1 e.symm
        obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 e'
        have hm' : ∀ g, y.1 g = y'.1 g - (ρ' g m - m) := fun g => by
          rw [← hm g]
          exact (sub_sub_cancel _ _).symm
        refine ⟨fun v hv τ hτ => ?_, fun v hv x hx => ?_⟩
        · obtain ⟨a, b, c⟩ := (hS' v).1 hv
          rw [hm', k1 v a b c τ hτ, (hur v a b c _ (A.2 v) τ hτ).2]
          simp
        · rcases (hS v).1 hv with hv | hv
          · rw [b1 v hv] at hx
            exact cupB_sub_cob _ (ρ.comp (Dec (F := F) (A.1 v)).subtype) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P
              (fun g x y => hP g.1 x y) x.1 _ _ m x.2.1 x.2.2
              ((hsub ρ' hc' _).comp (continuous_id.prodMk continuous_const)) (fun g => hm' g.1) (k3 v hv x hx)
          · obtain ⟨m', hm''⟩ := k2 v hv
            refine ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).2 ⟨m' - m, fun g => ?_⟩ x
            change y.1 g.1 = ρ' g.1 (m' - m) - (m' - m)
            rw [hm', hm'' g.1 g.2, map_sub]
            abel
      · rintro ⟨k1, k2⟩
        refine ⟨y, ⟨fun v a b c => k1 v ((hS' v).2 ⟨a, b, c⟩), fun v hv => ?_, fun v hv x hx => ?_⟩, rfl⟩
        · obtain ⟨m, hm⟩ := ((hloc v).1 (restrictCocycles1 ρ' _ continuous_subtype_val y)).1 fun x =>
            k2 v ((hS v).2 (.inr hv)) x (by rw [b2 v hv]; trivial)
          exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩
        · exact k2 v ((hS v).2 (.inl hv)) x (by rw [b1 v hv]; exact hx))
  refine ⟨fC, ?_⟩
  have hd : Disjoint hfin.toFinset (hT.toFinset ∪ Q) := Finset.disjoint_right.2 fun v hv h =>
    hnl v (by simpa using hv) (by simpa using h)
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin] at hcount
  have e1 : ∏ v ∈ hfin.toFinset, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) = ∏ v ∈ hfin.toFinset, Nat.card (L v) :=
    Finset.prod_congr rfl fun v hv => by rw [b1 v (by simpa using hv)]
  have e2 : ∏ v ∈ hT.toFinset ∪ Q, Nat.card (bkCond ρ A l (T ∪ ↑Q) L v) =
      (∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
        ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ∈ T ∨ v ∈ Q := by simpa using hv
    rw [b2 v hv', Nat.card_congr Submodule.topEquiv.toEquiv]
    exact (hloc v).2 (hnl v hv')
  have e3 : ∏ v ∈ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) =
      ∏ v ∈ hT.toFinset ∪ Q, Nat.card (H0 (ρ'.comp (Dec (F := F) (A.1 v)).subtype)) :=
    Finset.prod_subset Finset.subset_union_right fun v hv hv' => by
      have : v ∈ T ∨ v ∈ Q := by simpa using hv
      rw [hT0 v (this.resolve_right hv')]
      exact Nat.card_unique
  have hpos : 0 < (∏ v ∈ hfin.toFinset ∪ (hT.toFinset ∪ Q), Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) *
      Nat.card W ^ InfinitePlace.nrComplexPlaces F :=
    mul_pos (Finset.prod_pos fun v _ => Nat.card_pos) (pow_pos Nat.card_pos _)
  rw [h0, h0', Nat.card_unique (α := (⊥ : Submodule Λ W)), Nat.card_unique (α := (⊥ : Submodule Λ W')), mul_one, mul_one,
    Finset.prod_union hd (f := fun v => Nat.card (bkCond ρ A l (T ∪ ↑Q) L v)), e1, e2, hcount, ← e3, mul_assoc] at e
  refine Nat.eq_of_mul_eq_mul_right hpos (e.trans ?_)
  rw [Finset.prod_union hd]
  ring

end General

theorem orderFormula : PoitouTateTotallyComplex → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q := by
  intro hPT hLF hLD hLE hGF hGE h4 D N X bkP i s A _ _ _ _ κ Q ρ hS hK hD hNI Y Y' _ _ _ _ _ _ _ _ _ _ β hβ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := hS.2.1
  have hcx : InfinitePlace.nrComplexPlaces D.host.E = D.R.f := by
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
      rw [D.host.finrank_cmField]
      unfold Ranks.f Ranks.n
      ring
    omega
  obtain ⟨hc, hc', hP, hU⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hS hK hD Y Y' β hβ.1
  have hcount := GlobalTheory.T.localConditionOrder_aboveL_finiteModules D N X bkP i s A κ Q hS hK
    (GlobalTheory.LocalSaturation.main hLF hLD hLE h4 D N X bkP i s A κ Q hS)
    (GlobalTheory.LocalConditionCount.locCount hLF hLD hLE h4 D N X bkP i s A κ Q hS) Y
  have hko : IsOpen ((κ⁻¹).ker : Set (GE N)) := by
    convert hS.2.2.2.1 using 2
    ext g
    simp
  refine order_formula (X.l i) (nu X i + 1) hPT hLF hLD hLE hGF hGE (repOn (Tgl i s) κ Y) (repOn ρ κ⁻¹ Y') (vecPair D.R.r β)
    (show 0 < nu X i + 1 by omega) hc hc' (fun x hx => funext fun c => hβ.2.1 _ fun y' => ?_) (fun y hy => funext fun c => hβ.2.2 _ fun x => ?_) hP
    N.plOm (Spl i) (GlobalTheory.SelObstruction.finite_Spl i) Q (fun v hv => hv.2) hS.2.2.2.2.2.2.1 hU
    (bkOn bkP i (Tgl i s) κ Y) (DualCl bkP i s κ ρ β Q) (fun c => Iff.rfl)
    (GlobalTheory.NoGlobalInv.noInv D N X bkP i s A κ Q hS Y (tors_all A Y)) (eq_bot_iff.2 fun m hm => hNI Y' m hm)
    (fun v hv => (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hS.1 v hv A κ⁻¹ hko (fun g => ?_) Y'
      (tors_all A Y') ρ (.inr hD)).1) ?_
  · have := hx (Pi.single c y')
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · have := hy (Pi.single c x)
    rw [vecPair_apply, Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  · obtain ⟨n, hn⟩ := hS.2.2.2.2.1 g
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  · rw [hcount, hcx, Nat.card_pi, Finset.prod_const, Finset.card_fin, ← pow_mul, mul_comm D.R.r]

end GlobalTheory.SelOrder
end
end

section

open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

theorem Stable.scale_mem {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) {c : k} (hc : c ≠ 0)
    (α β γ : ℂ) (a r b s : k)
    (h : α • (fun _ => (1 : ℂ)) + β • ballFn a r + γ • ballFn b s ∈ S) :
    α • (fun _ => (1 : ℂ)) + β • ballFn (c * a) (c * r) + γ • ballFn (c * b) (c * s) ∈ S := by
  have hv : 0 < valuation k c := zero_lt_iff.2 (by simpa using hc)
  have key : ∀ a r x : k, ballFn (c * a) (c * r) x = ballFn a r ((c⁻¹ * x + 0 : k) : OnePoint k) := by
    intro a r x
    have h1 : x - c * a = c * (c⁻¹ * x + 0 - a) := by field_simp; ring
    rw [ballFn_coe, ballFn_coe, h1, map_mul, map_mul]
    congr 1
    rw [mul_le_mul_iff_right₀ hv]
  refine hS.1 _ h c⁻¹ 0 (inv_ne_zero hc) _ (by simp [ballFn]) fun x => ?_
  simp only [Pi.add_apply, Pi.smul_apply, key]

theorem ballFn_eq_ballFn_zero {a r : k} (h : valuation k a ≤ valuation k r) : ballFn a r = ballFn 0 r := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x =>
    rw [ballFn_coe, ballFn_coe, sub_zero]
    congr 1
    refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_sub_le hx h⟩
    have := (valuation k).map_add_le hx h
    rwa [sub_add_cancel] at this

theorem ballFn_congr_radius (a : k) {r s : k} (h : valuation k r = valuation k s) : ballFn a r = ballFn a s := by
  funext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe x => rw [ballFn_coe, ballFn_coe, h]

theorem Stable.ballFn_mem_and_one_mem_of_sub_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (ϖ : k)
    (hϖ : valuation k ϖ = uniformizer k) (h : ballFn 0 ϖ - ballFn 1 ϖ ∈ S) :
    ballFn (0 : k) 1 ∈ S ∧ (fun _ => (1 : ℂ)) ∈ S := by
  classical
  have hlt : valuation k ϖ < 1 := hϖ ▸ uniformizer_lt_one
  have hle : ∀ x : k, valuation k x ≤ valuation k ϖ ↔ valuation k x < 1 := fun x => by
    rw [hϖ]; exact le_uniformizer_iff
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (hϖ.symm.trans (map_zero _))
  have hdiff : ∀ a : k, valuation k a ≤ 1 → ballFn 0 ϖ - ballFn a ϖ ∈ S := by
    intro a ha
    rcases ha.lt_or_eq with ha | ha
    · rw [ballFn_eq_ballFn_zero ((hle a).2 ha), sub_self]
      exact S.zero_mem
    · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
      have h1 := hS.scale_mem ha0 0 1 (-1) 0 ϖ 1 ϖ (by simpa [sub_eq_add_neg] using h)
      have h2 : valuation k (a * ϖ) = valuation k ϖ := by rw [map_mul, ha, one_mul]
      rw [ballFn_congr_radius _ h2, ballFn_congr_radius _ h2] at h1
      simpa [sub_eq_add_neg] using h1
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_eq_sum_ballFn (r := ϖ) (R := 1) h0 (by simpa using hlt.le)
  simp only [map_one] at hT1 hT2 hT3
  set q : ℂ := (T.card : ℂ) with hqdef
  have hsum : ballFn (0 : k) 1 = ∑ a ∈ T, ballFn a ϖ := by
    rw [hT3 (ballFn 0 1) rfl (fun x hx => by rw [ballFn_coe, if_neg (by simpa using hx)]) (fun x b hb => ?_)]
    · refine Finset.sum_congr rfl fun a ha => ?_
      rw [ballFn_coe, if_pos (by simpa using hT1 a ha), one_smul]
    · have hb1 : valuation k b ≤ 1 := hb.trans hlt.le
      rw [ballFn_coe, ballFn_coe, sub_zero, sub_zero, map_one]
      congr 1
      refine propext ⟨fun hx => ?_, fun hx => (valuation k).map_add_le hx hb1⟩
      have := (valuation k).map_sub_le hx hb1
      rwa [add_sub_cancel_right] at this
  set e : OnePoint k → ℂ := fun _ => 1 with he
  have R1 : (0 : ℂ) • e + (1 : ℂ) • ballFn (0 : k) 1 + (-q) • ballFn (0 : k) ϖ ∈ S := by
    have h1 := S.neg_mem (S.sum_mem fun a (ha : a ∈ T) => hdiff a (hT1 a ha))
    rw [Finset.sum_sub_distrib, ← hsum, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, ← hqdef] at h1
    convert h1 using 1
    module
  have R2 := hS.scale_mem h0 _ _ _ _ _ _ _ R1
  have R3 : (1 - q) • e + q • ballFn (0 : k) 1 + (-1 : ℂ) • ballFn (0 : k) ϖ ∈ S := by
    refine hS.2 _ R1 _ ?_ ?_ fun x hx => ?_
    · simp [ballFn_coe, ballFn, he]; ring
    · simp [ballFn_coe, ballFn, he]
    · have hx0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
      simp only [Pi.add_apply, Pi.smul_apply, ballFn_coe, sub_zero, map_one, hϖ, le_uniformizer_iff, map_inv₀, he, smul_eq_mul,
        inv_le_one₀ hx0, inv_lt_one₀ hx0]
      rcases lt_trichotomy (valuation k x) 1 with h1 | h1 | h1
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]
      · simp [h1]
      · simp [h1, h1.le, h1.not_ge, h1.not_gt]; ring
  have R4 := hS.scale_mem h0 _ _ _ _ _ _ _ R3
  simp only [mul_zero, mul_one] at R2 R4
  rw [← he] at R2 R4
  have hq1 : (1 - q) ≠ 0 := by
    rw [sub_ne_zero, hqdef]
    exact_mod_cast (hT2 hlt).ne
  have hq2 : (1 + q) ≠ 0 := by
    rw [hqdef]
    exact_mod_cast (by omega : 1 + T.card ≠ 0)
  have h2 : ballFn (0 : k) (ϖ * ϖ) ∈ S := by
    have h3 := S.sub_mem (S.add_mem (S.sub_mem R4 R3) (S.smul_mem q R1)) (S.smul_mem (q + 1 - q ^ 2) R2)
    have h4 : -((1 - q) * (1 - q) * (1 + q)) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hq1 hq1) hq2)
    refine (S.smul_mem_iff h4).1 ?_
    convert h3 using 1
    module
  have hu0 : ballFn (0 : k) 1 ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 one_ne_zero
  have hu1 : ballFn (0 : k) ϖ ∈ S := hS.ballFn_mem (mul_ne_zero h0 h0) h2 0 h0
  refine ⟨hu0, (S.smul_mem_iff hq1).1 ?_⟩
  convert S.add_mem (S.sub_mem R3 (S.smul_mem q hu0)) hu1 using 1
  module

end GlobalTheory.LocGL.ProjLine
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.tate_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  first | exact @GlobalTheory.LocalFieldIso.isTateEps_transport | exact GlobalTheory.LocalFieldIso.isTateEps_transport | (intros; apply GlobalTheory.LocalFieldIso.isTateEps_transport <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; IoLaws E := by
  first | exact @GlobalTheory.NL.ioLaws | exact GlobalTheory.NL.ioLaws | (intros; apply GlobalTheory.NL.ioLaws <;> assumption)
end
