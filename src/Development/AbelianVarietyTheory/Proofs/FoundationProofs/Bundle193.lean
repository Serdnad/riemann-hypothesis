module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle255
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle002

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def IsClassTerm {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

theorem isToricSum_iff {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (T : ℂ) :
    IsToricSum φ s κ c χ T ↔ Finite (PicO c) ∧ ∃ t : PicO c → ℂ, (∀ q, IsClassTerm φ s κ c χ q.out (t q)) ∧ T = ∑ᶠ q, t q := by
  refine and_congr_right fun _ => ⟨fun ⟨S, hS, hT⟩ => ⟨_, fun q => ⟨S q, hS q, rfl⟩, hT⟩, fun ⟨t, ht, hT⟩ => ?_⟩
  choose S hS hS' using ht
  exact ⟨S, hS, by rw [hT]; exact finsum_congr hS'⟩

def IsHostDatum {R : Ranks} (H : Host R) {I : Type} [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E))
    (χ : HChar H.E) : Prop :=
  IsCMType φ ∧ (∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) ∧ 1 ≤ s ∧ (∀ τ, 1 ≤ κ τ) ∧ IsBaseCond 𝔣 ∧ IsValChar φ s κ 𝔣 ∅ χ

def below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (OF E) :=
  P.under (OF E)

theorem over_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Over P (below P) := rfl


open Classical in
def belowSet {E : Type} [Field E] [NumberField E] (Q : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (OF E)) :=
  Q.image below

theorem splits_below {R : Ranks} (H : Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : Splits (below P) := by
  obtain ⟨x, hx, hx'⟩ := h
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  have hc : ∀ a : 𝓞 H.E, ((c a : 𝓞 H.E) : H.E) = H.conj (a : H.E) := fun a => rfl
  refine ⟨P, P.comap c.toRingHom c.surjective, fun e => ?_, rfl, ?_⟩
  · have : x ∈ (P.comap c.toRingHom c.surjective).asIdeal := e ▸ hx
    exact hx' (c x) (hc x) this
  · ext a
    have : c (algebraMap (OF H.E) (𝓞 H.E) a) = algebraMap (OF H.E) (𝓞 H.E) a := by
      apply RingOfIntegers.ext
      apply H.φ₀.injective
      show H.φ₀ (H.conj ((a : maximalRealSubfield H.E) : H.E)) = H.φ₀ ((a : maximalRealSubfield H.E) : H.E)
      rw [H.toHostAx.conjE_apply]
      exact (a : maximalRealSubfield H.E).2 H.φ₀
    show c (algebraMap (OF H.E) (𝓞 H.E) a) ∈ P.asIdeal ↔ algebraMap (OF H.E) (𝓞 H.E) a ∈ P.asIdeal
    rw [this]

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev Kbar (i : X.Tw) : Type := AlgebraicClosure (FractionRing (X.O i))

def toBar (i : X.Tw) : FractionRing (X.O0 i) →+* Kbar X i :=
  (algebraMap (FractionRing (X.O i)) (Kbar X i)).comp
    (IsFractionRing.lift (g := (algebraMap (X.O i) (FractionRing (X.O i))).comp (algebraMap (X.O0 i) (X.O i)))
      ((IsFractionRing.injective (X.O i) (FractionRing (X.O i))).comp (X.O_inj i)))

def IsRecMap (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) {c : Ideal (OF D.host.E)} (π : PicO c →* X.RCG i Q) : Prop :=
  ∀ P, P ∉ X.S0 i → P ∉ Q → ∀ σ : G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ →
    π (QuotientGroup.mk (unifAt P)) = (X.art i Q σ)⁻¹

def IsToricEltAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
    (u : Kbar X i),
    IsHostDatum D.host φ s κ 𝔣 χ ∧
    (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    (∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1) ∧
    u ≠ 0 ∧
    ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def atSide {i : X.Tw} (b : Bool) (ι : ℂ →+* Kbar X i) : ℂ →+* Kbar X i := if b then ι else ι.comp (starRingEnd ℂ)

def IsToricElt : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsToricEltAt X i (atSide X (X.sideL i lam) ι) lam s

variable {X}

theorem placesBelow_splitCoprimeConductor_of_admissible {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (hQ : BlochKatoReduction.Gen.QOk X i Q) {𝔣 : Ideal (OF D.host.E)}
    (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) :
    IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q) ∧ ∀ q ∈ belowSet Q, ((X.l i : ℕ) : OF D.host.E) ∉ q.asIdeal := by
  classical
  constructor
  · intro q hq
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨splits_below D.host (hQ.1 P hP), fun h => Finset.disjoint_left.1 hQ.2.1 hP (h𝔣 P h)⟩
  · intro q hq h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine Finset.disjoint_left.1 hQ.2.1 hP (X.twistExcludedPlaces_contains_residueChar i ?_)
    have : algebraMap (OF D.host.E) (𝓞 D.host.E) ((X.l i : ℕ) : OF D.host.E) ∈ P.asIdeal := h
    rwa [map_natCast] at this

end Record

end GlobalTheory.ToricDenom
end
end

section

namespace GlobalTheory.TraceConjugacy

open Matrix

theorem exists_conj_of_surjective {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    {a : ℕ} (φ φ' : A →ₐ[O] Matrix (Fin a) (Fin a) O) (hφ : Function.Surjective φ)
    (htr : ∀ x, (φ x).trace = (φ' x).trace) :
    ∃ U : GL (Fin a) O, ∀ x, φ' x * (U : Matrix (Fin a) (Fin a) O) = U * φ x := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨1, fun x => Subsingleton.elim _ _⟩
  obtain ⟨s, hs⟩ := φ.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hφ)
  have hs' : ∀ X, φ (s X) = X := fun X => LinearMap.congr_fun hs X
  let θ : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O := φ'.toLinearMap ∘ₗ s
  have hθ : ∀ X, θ X = φ' (s X) := fun X => rfl
  let T : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O :=
    { toFun := fun X => Matrix.of fun i j => (X * θ (Matrix.single j i 1)).trace
      map_add' := fun X Y => by ext i j; simp [add_mul]
      map_smul' := fun c X => by ext i j; simp }
  have hT : ∀ x, T (φ' x) = φ x := by
    intro x
    ext i j
    change (φ' x * θ (Matrix.single j i 1)).trace = _
    rw [hθ, ← map_mul, ← htr, map_mul, hs', Matrix.trace_mul_single]
    simp
  have hTinj : Function.Injective T :=
    OrzechProperty.injective_of_surjective_endomorphism T fun X =>
      ⟨φ' (s X), by rw [hT, hs']⟩
  have hfac : ∀ x, θ (φ x) = φ' x := fun x => hTinj (by rw [hθ, hT, hT, hs'])
  have hmul : ∀ X Y, θ X * θ Y = θ (X * Y) := by
    intro X Y
    rw [hθ, hθ, ← map_mul, ← hfac, map_mul, hs', hs']
  let o : Fin a := ⟨0, ha⟩
  have h1 : ∑ y, θ (Matrix.single o o 1) y y = 1 := by
    have := htr (s (Matrix.single o o 1))
    rw [hs', Matrix.trace_single_eq_same] at this
    exact this.symm
  obtain ⟨y, -, hy⟩ := IsLocalRing.exists_of_isUnit_sum (show IsUnit (∑ y, θ (Matrix.single o o 1) y y) by
    rw [h1]; exact isUnit_one)
  let U : Matrix (Fin a) (Fin a) O := Matrix.of fun x i => θ (Matrix.single i o 1) x y
  let V : Matrix (Fin a) (Fin a) O := Matrix.of fun j x => θ (Matrix.single o j 1) y x
  have hVU : V * U = θ (Matrix.single o o 1) y y • (1 : Matrix (Fin a) (Fin a) O) := by
    ext j i
    have : (V * U) j i = (θ (Matrix.single o j 1) * θ (Matrix.single i o 1)) y y := by
      simp [Matrix.mul_apply, U, V]
    rw [this, hmul]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hij]
      simp [hij]
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := congrArg Matrix.det hVU
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact isUnit_of_mul_isUnit_right (this ▸ hy.pow _)
  refine ⟨hU.unit, fun z => ?_⟩
  rw [IsUnit.unit_spec, ← hfac]
  ext x i
  have h2 : (θ (φ z) * U) x i = (θ (φ z) * θ (Matrix.single i o 1)) x y := by
    simp [Matrix.mul_apply, U]
  have h3 : φ z * Matrix.single i o (1 : O) = ∑ k, φ z k i • Matrix.single k o (1 : O) := by
    ext p q
    by_cases hq : q = o
    · subst hq
      simp [Matrix.sum_apply, Matrix.single_apply]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq]
      simp [Matrix.sum_apply, Matrix.single_apply, Ne.symm hq]

  rw [h2, hmul, h3, map_sum, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem span_eq_top_of_residue {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (M g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | (apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top ..)

theorem exists_conj_of_trace_eq_local {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {a : ℕ} (ρ ρ' : Γ →* GL (Fin a) O)
    (h : Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤)
    (htr : ∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace =
      ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) :
    ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  have hspan : Submodule.span O
      (Set.range fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) = ⊤ :=
    by
    refine span_eq_top_of_residue _ ?_
    have h0 := GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ h
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) = fun g =>
        ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (IsLocalRing.residue O) := by
      funext g
      rfl
    rwa [h1] at h0
  let φ : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ)
  let φ' : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ')
  have hφ : ∀ g c, φ (MonoidAlgebra.single g c) = c • (ρ g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ]
  have hφ' : ∀ g c, φ' (MonoidAlgebra.single g c) = c • (ρ' g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ']
  have hsurj : Function.Surjective φ := by
    have : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simpa using hφ g 1⟩
    exact LinearMap.range_eq_top.1 this
  have htr' : ∀ x, (φ x).trace = (φ' x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single g c => rw [hφ, hφ', Matrix.trace_smul, Matrix.trace_smul, htr]
  obtain ⟨U, hU⟩ := exists_conj_of_surjective φ φ' hsurj htr'
  refine ⟨U, fun g => Units.ext ?_⟩
  have := hU (MonoidAlgebra.single g 1)
  rwa [hφ, hφ', one_smul, one_smul] at this

theorem exists_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g :=
  fun _ _ _ _ _ _ _ ρ ρ' h htr => exists_conj_of_trace_eq_local ρ ρ' h htr

end GlobalTheory.TraceConjugacy
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

theorem _root_.GlobalTheory.T.isSSRep_of_trace_nondegenerate' : ∀ (Γ K : Type) [Group Γ] [Field K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) → IsSSRep ρ := by
  first | exact @GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate | exact GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate | (intros; apply GlobalTheory.TraceSemisimple.isSSRep_of_trace_nondegenerate <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

theorem _root_.GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff : ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | exact GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | (intros; apply GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep : ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.isSSRep_trace_nondegenerate | exact GlobalTheory.isSSRep_trace_nondegenerate | (intros; apply GlobalTheory.isSSRep_trace_nondegenerate <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TateTopCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.TateLocalDualityDegreeTwo

section Transport

variable {O O' G M M' : Type} [CommRing O] [CommRing O'] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O' M'] [TopologicalSpace M']
  [DiscreteTopology M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O' M']
  {σ : O →+* O'} {σ' : O' →+* O} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (π : Representation O G M) (ρ : Representation O' G M') (e : M ≃ₛₗ[σ] M')

variable (he : ∀ g x, e (π g x) = ρ g (e x))
include he


end Transport

section Integers

variable {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [CommRing O] [Algebra O LL]

theorem mem_range_of_norm_le (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) (hx : ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1) :
    x ∈ Set.range (algebraMap O LL) := by
  obtain ⟨⟨hO, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := h
  obtain ⟨-, -, hmt', -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l L').1
  have hcont : Continuous φ.symm :=
    IsModuleTopology.continuous_of_linearMap φ.symm.toLinearEquiv.toLinearMap
  have hU : IsOpen (φ.symm ⁻¹' Set.range (algebraMap O LL)) := hop.preimage hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 ⟨0, by simp⟩
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] hε
  have hc0' : c ≠ 0 := norm_pos_iff.1 hc0
  have hk : ∀ k : ℕ, ∃ b : O, algebraMap O LL b = algebraMap ℚ_[l] LL c * x ^ k := by
    intro k
    have : φ (algebraMap ℚ_[l] LL c * x ^ k) ∈ Metric.ball (0 : ↥L'.1) ε := by
      rw [mem_ball_zero_iff]
      change ‖((φ (algebraMap ℚ_[l] LL c * x ^ k) : ↥L'.1) : Om l)‖ < ε
      rw [map_mul, map_pow, AlgEquiv.commutes]
      push_cast
      rw [norm_mul, norm_pow]
      have h1 : ‖((algebraMap ℚ_[l] ↥L'.1 c : ↥L'.1) : Om l)‖ = ‖c‖ := PadicAlgCl.norm_extends l c
      calc _ ≤ ‖c‖ * 1 := by
            gcongr
            · exact h1.le
            · exact pow_le_one₀ (norm_nonneg _) hx
        _ < ε := by simpa using hc
    simpa using hball this
  rcases ValuationRing.isInteger_or_isInteger O x with h | ⟨y, hy⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  by_cases hu : IsUnit y
  · obtain ⟨z, hz⟩ := hu.exists_right_inv
    refine ⟨z, ?_⟩
    have := congrArg (algebraMap O LL) hz
    rw [map_mul, hy, map_one] at this
    field_simp at this
    exact this
  · exfalso
    obtain ⟨a, ha⟩ := hk 0
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hc0' (by simpa using ha.symm)
    obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hu ha0
    obtain ⟨b, hb⟩ := hk (n + 1)
    refine hn ⟨b, IsFractionRing.injective O LL ?_⟩
    rw [map_mul, map_pow, hy, hb, ha, inv_pow]
    field_simp

theorem mem_range_iff (h : GoodO (Qp := ℚ_[l]) LL O) (L' : FinExt l)
    (φ : LL ≃ₐ[ℚ_[l]] ↥L'.1) (x : LL) :
    x ∈ Set.range (algebraMap O LL) ↔ φ x ∈ OL L' := by
  have hO : φ x ∈ OL L' ↔ ‖((φ x : ↥L'.1) : Om l)‖ ≤ 1 := mem_integralClosure_padicInt_iff L'.1 _
  rw [hO]
  refine ⟨?_, mem_range_of_norm_le h L' φ x⟩
  rintro ⟨a, rfl⟩
  by_contra hlt
  rw [not_le] at hlt
  have hsurj : Function.Surjective (algebraMap O LL) := by
    intro w
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖((φ w : ↥L'.1) : Om l)‖ hlt
    have hpos : 0 < ‖((φ (algebraMap O LL a) : ↥L'.1) : Om l)‖ ^ k := by positivity
    have ha : algebraMap O LL a ≠ 0 := by
      intro h0
      rw [h0] at hlt
      norm_num at hlt
    obtain ⟨b, hb⟩ := mem_range_of_norm_le h L' φ (w / algebraMap O LL a ^ k) (by
      rw [map_div₀, map_pow]
      push_cast
      rw [norm_div, norm_pow, div_le_one hpos]
      exact hk.le)
    exact ⟨b * a ^ k, by rw [map_mul, map_pow, hb]; field_simp⟩
  obtain ⟨⟨hO, hdvr, hfr⟩, -⟩ := h
  exact IsDiscreteValuationRing.not_isField O
    ((RingEquiv.ofBijective (algebraMap O LL)
      ⟨IsFractionRing.injective O LL, hsurj⟩).toMulEquiv.isField (Field.toIsField LL))

theorem exists_finExt (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] :
    ∃ L' : FinExt l, Nonempty (LL ≃ₐ[ℚ_[l]] ↥L'.1) := by
  let ψ : LL →ₐ[ℚ_[l]] Om l := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨⟨ψ.fieldRange, (AlgEquiv.ofInjectiveField ψ).toLinearEquiv.finiteDimensional⟩,
    ⟨AlgEquiv.ofInjectiveField ψ⟩⟩

end Integers

section Quotients

variable {G LL O LL' O' M' : Type} [Group G] [TopologicalSpace G] [Field LL] [CommRing O]
  [Algebra O LL] [Field LL'] [CommRing O'] [Algebra O' LL'] [AddCommGroup M'] [Module O' M']
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalAddGroup M']
  [ContinuousConstSMul O' M']


omit [TopologicalSpace G] in
def rangeLattice (hinj : Function.Injective (algebraMap O LL)) (χ : G →* LLˣ)
    (hχ : ∀ g, ((χ g : LLˣ) : LL) ∈ Set.range (algebraMap O LL)) :
    Lattice (O := O) (charRep χ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hχ g
    exact ⟨a * y, by simp [charRep, ha]⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) :
        Submodule O LL) : Set LL) := Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x this

end Quotients

section Compare

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

end Compare

end GlobalTheory.TateTopCompare
end
end
