module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle546
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
import Formalism.LocalToGlobal.UnitaryNorms.UnramT
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle845
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle844
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def trSp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (e : AE D) (M : ℕ) (O : Subring ℂ) :
    Submodule O (WO V W → ℂ) :=
  Submodule.span O {f | ∃ y : WO V W, IsHalf e y ∧ M • y ∈ latO V W ΛV ΛW (fun _ => True) ∧ f = heisO ψ V W y f₀}

abbrev stdF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (sW BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) :
    MvPolynomial (FVar D W.rank V.rank) ℂ →ₗ[ℂ] (WO V W → ℂ) :=
  pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f

def OneAt (V : HSp D) (l : ℕ) (h : GA D V) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V h - 1) a b = 0

def ChiData (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) : Prop :=
  ChrEq χW χ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def ValRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ) : Prop :=
  ∀ x : k, la.valuation k x ≤ 1 → σ x ∈ O

def locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) : Subring ℂ :=
  (la.valuation k).integer.map σ

theorem valRing_locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la (locRing σ la) := fun x hx => ⟨x, hx, rfl⟩

theorem valRing_range {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la σ.range := fun x _ => ⟨x, rfl⟩

def ConjIn (D : D7) {k : Type} [Field k] (σ : k →+* ℂ) : Prop := ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), ∃ x, σ x = τ a

def DenomAt {E : Type} [Field E] {n : ℕ} (l c : ℕ) (γ : GL (Fin n) E) : Prop :=
  ∃ m : ℕ, Nat.Coprime m l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ.val a b) ∧
    IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ⁻¹.val a b)

theorem oneAt_one (V : HSp D) (l : ℕ) : OneAt V l 1 := fun _ _ _ _ a b => by
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  rw [h1, sub_self]
  simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)

def BaseCc (ph : ℂ) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * T.cE ((i : ℕ) + 1) T.σ₀ k

def CovCc (ph : ℂ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂)
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * C.cc₂ k

end GlobalTheory.LevelSeries

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar



open Classical
namespace GlobalTheory.ExportSeries
open GlobalTheory.PlaceModel

variable {D : D7}

theorem isPlaceModel_restrictHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := GlobalTheory.T.isPlaceModel_comp_restrictToHalfLatticeIndicator ha hb hab hΛ hT

theorem toEAf_mem_intAf_of_idem {e : AE D} (he : e * e = e) : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.T.finiteAdeleCM_mem_integral_of_idempotent he

theorem isIntM_of_mem_lat_half {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    {x : WO S T} (hx : IsHalf (idem R) x) (hl : x ∈ F.lat) :
    IsIntM (frMapO S T F.βS F.βT x) ∧ IsIntM (frMapAdj S T F.βS F.βT x) :=
  GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hR hx hl

theorem mem_lat_of_isIntM_half {S T : HSp D} {F : Frame S T} (hF : F.Good) {R : Finset (Pl D.host.E)} (hR : PlacesOK ∅ R)
    {x : WO S T} (hx : IsHalf (idem R) x) (hi : IsIntM (frMapO S T F.βS F.βT x)) : x ∈ F.lat := GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hR hx hi

theorem redM_halfIdem_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Qa Qb : Finset (Pl D.host.E)} (hP : PlacesOK Pg Qa) (hQ : Qb ⊆ Qa) {x : WO S T}
    (hx : IsHalf (halfIdem Pg Qa) x) (h1 : IsIntM (frMapAdj S T βS βT x)) (h2 : IsIntM (frMapO S T βS βT x)) :
    (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧
    (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) :=
  GlobalTheory.T.frameMatrixReduction_eq_of_halfIdempotent_subset βS βT hP hQ hx h1 h2

end GlobalTheory.ExportSeries



open Classical
namespace GlobalTheory.ExportSeries
open GlobalTheory.PlaceModel GlobalTheory.AdelicLatMove

variable {D : D7}

theorem halfIdem_eq_add {Pg Qa Qb : Finset (Pl D.host.E)} (hQ : Qb ⊆ Qa) :
    halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
  unfold halfIdem idem
  rw [← Finset.sum_sdiff hQ]
  ring

theorem PlacesOK.empty_sdiff {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa) : PlacesOK ∅ (Qa \ Qb) :=
  ⟨h.split.imp fun _ hP => ⟨Finset.empty_subset _, Finset.sdiff_subset.trans hP.2.1, hP.2.2⟩, Finset.disjoint_empty_left _,
    fun PP hPP => h.prime PP (Or.inr (Finset.sdiff_subset (hPP.resolve_left (Finset.notMem_empty PP))))⟩

theorem idem_mul_self_of {R : Finset (Pl D.host.E)} (h : PlacesOK ∅ R) : idem R * idem R = idem R := by
  have := h.isOrthSum.1.idem
  rwa [halfIdem, idem_empty, map_zero, zero_add] at this

theorem halfIdem_mul_idem {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa) (hQ : Qb ⊆ Qa) :
    halfIdem Pg Qb * idem (Qa \ Qb) = 0 := by
  have h1 := h.isOrthSum.1.idem
  have h2 := (h.mono hQ).isOrthSum.1.idem
  have h3 := idem_mul_self_of (h.empty_sdiff (Qb := Qb))
  rw [halfIdem_eq_add hQ] at h1
  refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
  push_cast
  linear_combination h1 - h2 - h3

theorem frMapO_add' {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((e • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D e) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem isIntM_smul {b a : ℕ} {e : AE D} (he : e * e = e) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    IsIntM (toEAf D e • N) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem (toEAf_mem_intAf_of_idem he) (hN i j)

theorem isIntM_smul_cA {b a : ℕ} {e : AE D} (he : e * e = e) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    IsIntM (toEAf D (cA D e) • N) := isIntM_smul (by rw [← map_mul, he]) hN

theorem isHalf_smul {m n : ℕ} {e : AE D} (he : e * e = e) (x : Mx D m n) : IsHalf e (e • x) := fun i j => by
  show e * (e * x i j) = e * x i j
  rw [← mul_assoc, he]

theorem isInt_iff {S T : HSp D} {F : Frame S T} (hF : F.Good) {Pg Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK Pg Qa)
    (hQ : Qb ⊆ Qa) {x : WO S T} (hx : IsHalf (halfIdem Pg Qa) x) :
    (IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) ↔
      (IsIntM (frMapAdj S T F.βS F.βT (halfIdem Pg Qb • x)) ∧ IsIntM (frMapO S T F.βS F.βT (halfIdem Pg Qb • x)) ∧
        idem (Qa \ Qb) • x ∈ F.lat) := by
  have hR := h.empty_sdiff (Qb := Qb)
  have ha' := (h.mono hQ).isOrthSum.1.idem
  have hb := idem_mul_self_of hR
  have hxe : x = halfIdem Pg Qb • x + idem (Qa \ Qb) • x := by
    rw [← add_smul, ← halfIdem_eq_add hQ]
    exact (Matrix.ext fun i j => hx i j).symm
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, mem_lat_of_isIntM_half hF hR (isHalf_smul hb x) ?_⟩
    · rw [frMapAdj_smul]; exact isIntM_smul_cA ha' h1
    · rw [frMapO_smul]; exact isIntM_smul ha' h2
    · rw [frMapO_smul]; exact isIntM_smul hb h2
  · rintro ⟨k1, k2, k3⟩
    obtain ⟨o, d⟩ := isIntM_of_mem_lat_half hF hR (isHalf_smul hb x) k3
    rw [hxe, GlobalTheory.PlaceVec.frMapAdj_add, frMapO_add']
    exact ⟨fun i j => add_mem (k1 i j) (d i j), fun i j => add_mem (k2 i j) (o i j)⟩

theorem datumFn_eq_restrict {S T : HSp D} {F : Frame S T} (hF : F.Good) {G : TypeDat D T.rank}
    {Qa Qb : Finset (Pl D.host.E)} (h : PlacesOK G.Pg Qa) (hQ : Qb ⊆ Qa) {ω : Reds D T.rank S.rank → ℂ}
    (hω : ∀ y y', (∀ PP ∈ Qb, y PP = y' PP) → ω y = ω y') :
    F.datumFn G Qa ω = restrictHalf (halfIdem G.Pg Qb) (idem (Qa \ Qb)) F.lat (F.datumFn G Qb ω) := by
  funext x
  have ha' := (h.mono hQ).isOrthSum.1.idem
  have hb := idem_mul_self_of (h.empty_sdiff (Qb := Qb))
  rw [restrictHalf_apply, ← halfIdem_eq_add hQ]
  by_cases hx : IsHalf (halfIdem G.Pg Qa) x
  swap
  · rw [if_neg hx, mul_zero]
    simp only [Frame.datumFn]
    rw [if_neg fun h => hx h.1, zero_mul]
  rw [if_pos hx, mul_one]
  have ha'x := isHalf_smul ha' x
  have hbx := isHalf_smul hb x
  by_cases hint : IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)
  · obtain ⟨k1, k2, k3⟩ := (isInt_iff hF h hQ hx).1 hint
    obtain ⟨r1, r2⟩ := redM_halfIdem_smul F.βS F.βT h hQ hx hint.1 hint.2
    simp only [Frame.datumFn, halfInd]
    rw [if_pos ⟨hx, hint.1⟩, if_pos ⟨hx, hint.2⟩, if_pos ⟨ha'x, k1⟩, if_pos ⟨ha'x, k2⟩, if_pos ⟨k3, hbx⟩, mul_one]
    congr 1
    · exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP => r1 PP hPP
    · exact hω _ _ fun PP hPP => r2 PP hPP
  · have hL : F.datumFn G Qa ω x = 0 := by
      rcases not_and_or.1 hint with h1 | h1
      · simp [Frame.datumFn, h1]
      · simp [Frame.datumFn, h1]
    rw [hL]
    have hr := mt (isInt_iff hF h hQ hx).2 hint
    rcases not_and_or.1 hr with h1 | h1
    · simp [Frame.datumFn, h1]
    rcases not_and_or.1 h1 with h1 | h1
    · simp [Frame.datumFn, h1]
    · simp [halfInd, h1]

theorem vecAt_drop : ∀ (D : D7) (S T : HSp D) (B : Base S T) (Q Q' : Finset (Pl D.host.E)) [DecidablePred (· ∈ Q')]
    (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ), B.Good → B.admitted Q → Q' ⊆ Q →
    B.vecAt Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.vecAt Q' fun PP => φ PP.1 := by
  intro D S T B Q Q' _ φ hB hQ hQ'
  classical
  have hL : B.locFn Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.locFn Q' (fun PP => φ PP.1) := by
    funext y
    unfold Base.locFn
    congr 1
    beta_reduce
    rw [Finset.prod_coe_sort Q (fun P => if P ∈ Q' then φ P (y P) else 1),
      ← Finset.prod_subset hQ' (fun P _ hn => if_neg hn), Finset.prod_coe_sort Q' (fun P => φ P (y P))]
    exact Finset.prod_congr rfl fun P hP => if_pos hP
  have hQb : B.de.Q ∪ Q' ⊆ B.de.Q ∪ Q := Finset.union_subset_union (subset_refl _) hQ'
  have hω : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q', y PP = y' PP) →
      B.locFn Q' (fun PP => φ PP.1) y = B.locFn Q' (fun PP => φ PP.1) y' := fun y y' hy => by
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)],
      Finset.prod_congr (s₁ := Finset.univ) rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]]
  have hP := hQ.1
  have hPb := hP.mono hQb
  unfold Base.vecAt Frame.vec
  rw [hL, datumFn_eq_restrict hB.frame hP hQb hω]
  have hmodel := Frame.isPlaceModel_placeMap hB.frame hP
  rw [halfIdem_eq_add hQb] at hmodel ⊢
  have hm' := isPlaceModel_restrictHalf hPb.isOrthSum.1.idem (idem_mul_self_of (hP.empty_sdiff (Qb := B.de.Q ∪ Q')))
    (halfIdem_mul_idem hP hQb) (fun e he u hu => GlobalTheory.PlaceModelSum.idem_smul_latO he hu) hmodel
  exact GlobalTheory.PlaceVec.placeModel_unique hB.frame.vac.1 hB.frame.sdS hB.frame.sdT hPb.isOrthSum.1.idem
    hPb.isOrthSum.1.infPart_eq hm' (Frame.isPlaceModel_placeMap hB.frame hPb) (Frame.isSBHalf_datumFn hB.frame hPb hω)

end GlobalTheory.ExportSeries
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open scoped TensorProduct




namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


open Classical in
def specXi (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • ρ.xi i j b Y Q M h P a

theorem exists_mem_thPsi_of_mem_span {ρ : Setup X} {hρ : ρ.Good} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b} (T : CellTie hρ Y rd) (hR : RatTwist hρ rd) {k : ℕ}
    {Q : Finset (Pl D.host.E)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q)
    (d : Y.Dat i ((j : ℕ) + 1) b) {f : GA D (Wc D j) → ℂ}
    (hf : f ∈ Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q ψ (T.cls d) (T.coef d))) :
    ∃ z ∈ Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i ((j : ℕ) + 1) b k Q ψ {d}, rdK rd hρ k z = f := by
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨z, hz⟩ := hR k Q ψ hψ hQ _ _ _ (T.dat d) hs
    refine ⟨z, Submodule.subset_span ?_, hz⟩
    exact Set.mem_biUnion (Set.mem_singleton d) ((T.thPsi_iff k Q ψ hψ d z).2 (hz ▸ hs))
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add f g _ _ hf hg =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨z', hz', rfl⟩ := hg
    exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
  | smul c f _ hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨c', hc'⟩ := c.2
    refine ⟨c' • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [map_smulₛₗ]
    change ρ.eOk i b k c' • rdK rd hρ k z = (c : ℂ) • rdK rd hρ k z
    rw [hc']

end Ser

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpecLoc

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


open Classical in
def specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (y : Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1)) : ℂ :=
  ∑ c : ZMod (X.l i ^ M), ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP c))) : X.Ok i k) *
    ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 c y : ℚ) : ℂ)

def specSer (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
    (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ)) h P)

end SpecLoc

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser2

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
theorem rdK_specU_grpSum {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (x : (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i ((j : ℕ) + 1) b) :
    rdK rd hρ k (Formalism.MainNotions.IntegralHeckeForms.specU Y i ((j : ℕ) + 1) b Q M k χ (grpSum Y (ρ.ch i) Q M x)) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • rd (x a) := by

  rw [grpSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Formalism.MainNotions.IntegralHeckeForms.specU, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply, AddMonoidAlgebra.lift_single, one_smul,
    MonoidHom.coe_comp, Units.coeHom_apply]
  rw [rdK_tmul]

end Ser2

end GlobalTheory.SeriesTie
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



noncomputable section

namespace GlobalTheory.SplitOffS0

theorem main : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  intro D N X ρ hρ i Q hQ P hsplit hP
  have hinv : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := fun z => Formalism.L2.Host.conj_conj (D := D) D.host z
  let c : 𝓞 D.host.E → 𝓞 D.host.E := fun x => RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := fun x => rfl
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      (x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ↔ y ∈ P.asIdeal) :=
    fun x y h => GlobalTheory.Mem.Col2.HAt.mem_conjIdeal_Pv P.asIdeal x y h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hy⟩ := hsplit
    intro heq
    have h1 : c x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal :=
      (key (c x) x (by rw [hc, hinv])).2 hx
    exact hy (c x) (hc x) (heq ▸ h1)
  · intro hPQ
    exact hP (hQ P (by simpa using hPQ))
  · intro Q' hQ' heq
    apply hP
    refine hρ.goodSetup_badPlaces_conj i Q' (hQ Q' (by simpa using hQ')) P ?_
    intro x y hxy
    rw [heq]
    exact key x y hxy

end GlobalTheory.SplitOffS0
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heckeChar_unramified_outside_of_lPower_galois_char : ∀ (D : D7) (N : NData D.R D.host D.what₂) (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E N.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (r : G D.host.E N.Om →* ℂˣ) (l n : ℕ), l.Prime → (∀ σ, r σ ^ (l ^ n) = 1) → ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → GlobalTheory.ToricDistribution.Corr art r χ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, r σ = 1) → GlobalTheory.ExportSeries.UnramOutside c Q := by
  first | exact @GlobalTheory.UnramPull.unramOutside_of_corr | exact GlobalTheory.UnramPull.unramOutside_of_corr | (intros; apply GlobalTheory.UnramPull.unramOutside_of_corr <;> assumption)
end
