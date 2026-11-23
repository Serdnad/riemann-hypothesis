module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2002
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.SumSize.OppConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {ι : Type} [Fintype ι] {n : ℕ}

def mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (lam : ι → DomWeight n) (x : VV K lam) : VV L lam :=
  ⟨MvPolynomial.map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩

theorem mapVV_mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (ψ : L →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (mapF φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (ψ : ℂ →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (GlobalTheory.CoefModel.mapVV φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_id (lam : ι → DomWeight n) (v : VV ℂ lam) : GlobalTheory.CoefModel.mapVV (RingHom.id ℂ) lam v = v :=
  Subtype.ext (by
    change MvPolynomial.map (RingHom.id ℂ) v.1 = v.1
    rw [MvPolynomial.map_id])

theorem conj_comp_conj : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ :=
  RingHom.ext fun z => Complex.conj_conj z

theorem mapVV_conj_conj (lam : ι → DomWeight n) (v : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = v := by
  rw [mapVV_mapVV, conj_comp_conj, mapVV_id]

def conjMap {n' : ℕ} {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (v : VV ℂ lam) : VV ℂ lam' :=
  GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam' (K (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v))

end Coef

section Places

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjPl (q : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (q.embedding.comp (starRingEnd K))

variable {K}

theorem conjugate_comp (φ : K →+* ℂ) (f : K →+* K) :
    (ComplexEmbedding.conjugate φ).comp f = ComplexEmbedding.conjugate (φ.comp f) :=
  RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]

theorem conjPl_mk (φ : K →+* ℂ) : conjPl K (InfinitePlace.mk φ) = InfinitePlace.mk (φ.comp (starRingEnd K)) := by
  unfold conjPl
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, conjugate_comp, InfinitePlace.mk_conjugate_eq]

theorem star_comp_star : (starRingEnd K).comp (starRingEnd K) = RingHom.id K :=
  RingHom.ext fun x => by simp

theorem conjPl_conjPl (q : InfinitePlace K) : conjPl K (conjPl K q) = q := by
  change conjPl K (InfinitePlace.mk (q.embedding.comp (starRingEnd K))) = q
  rw [conjPl_mk, RingHom.comp_assoc, star_comp_star, RingHom.comp_id, InfinitePlace.mk_embedding]

theorem conjPl_involutive : Function.Involutive (conjPl K) := conjPl_conjPl

theorem meanInf_conjPl (g : InfinitePlace K → ℝ) : Formalism.PairingDivisionLocalBalance.meanInf K (fun q => g (conjPl K q)) = Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  congr 1
  exact Equiv.sum_comp (conjPl_involutive.toPerm _) g

end Places

section Nrm

variable {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

theorem nrm_conj (v : VV ℂ lam) :
    nrm lam (fun _ => 1) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = nrm lam (fun _ => 1) v := by
  have h := GlobalTheory.CoefModel.pairK_mapVV (starRingEnd ℂ) lam (fun _ => rfl) (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) v v
  simp only [Matrix.map_one _ (map_zero _) (map_one _)] at h
  simp only [nrm, h, Complex.conj_re]

theorem nrmLe_conj_iff (σ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam ((starRingEnd ℂ).comp σ) v B ↔ NrmLe lam σ v B := by
  constructor
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj] at hB
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj]

theorem nrmLe_mk_iff (φ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam (InfinitePlace.mk φ).embedding v B ↔ NrmLe lam φ v B := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · have e : ComplexEmbedding.conjugate φ = (starRingEnd ℂ).comp φ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [h, e, nrmLe_conj_iff]

end Nrm

section Transfer

variable {D : D7} {n n' : ℕ} {lam : D.what₂.Tau → DomWeight n} {lam' : D.what₂.Tau → DomWeight n'}

theorem embLL_comp_star : D.what₂.embLL.comp (starRingEnd D.what₂.LL) = (starRingEnd ℂ).comp D.what₂.embLL :=
  RingHom.ext fun x => D.starLL_cx x

theorem nrmLe_of_conjMap (σ : D.what₂.LL →+* ℂ) (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ)
    (h : ∀ B v, NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) v B →
      NrmLe lam' (σ.comp (starRingEnd D.what₂.LL)) (conjMap K v) (c * B))
    (B : ℝ) (v : VV ℂ lam) (hv : NrmLe lam σ v B) : NrmLe lam' σ (K v) (c * B) := by
  obtain ⟨u, hu, hB⟩ := hv
  have h1 : NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) B := by
    refine ⟨mapF (starRingEnd D.what₂.LL) lam u, ?_, ?_⟩
    · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu]
    · rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
  obtain ⟨u', hu', hB'⟩ := h B _ h1
  refine ⟨mapF (starRingEnd D.what₂.LL) lam' u', ?_, ?_⟩
  · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu', conjMap, mapVV_conj_conj, mapVV_conj_conj]
  · rwa [mapVV_mapF]

end Transfer

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairStdAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β),
    (∀ (j : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B)) ∧
    ∀ (i : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (conjMap (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1))) v) (Real.exp (g p) * B)

theorem infRowAt_of (h : PairStdAt ch C b) : InfRowAt ch C b := by
  obtain ⟨g, hg, h⟩ := h
  refine ⟨fun p => g (conjPl _ p), by rwa [meanInf_conjPl], ?_⟩
  intro p Φ β d hO c i B v hv
  have key := (h (conjPl _ p) Φ β d hO c).2 i
  refine nrmLe_of_conjMap p.embedding _ _ (fun B' v' hv' => ?_) B v hv
  exact (nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).1
    (key B' v' ((nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).2 hv'))

end Std

def PairStdK : Prop := BigC fun _ ch C b => PairStdAt ch C b

theorem bigC_mono {Q Q' : ChQ} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ),
    Q F ch C b → Q' F ch C b) : BigC Q → BigC Q' := by
  rintro ⟨CF0, h0⟩
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h1⟩ := h0 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h2⟩ := h1 ε C hC
  exact ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h3 h4 h5 =>
    h F ch C large₂.sc.b (h2 D large₂ he hx Γ Pl0 T A Ks R F hS ch h3 h4 h5)⟩

theorem infRowK_of (h : PairStdK) : InfRowK := bigC_mono (fun _ ch C b => infRowAt_of ch C b) h

end GlobalTheory.SumSize.OppConj

end
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.KerConjMean

variable (D : D7) (δ t0 : ℂ)

abbrev lat : AddSubgroup ℂ := lamOf D D.host.ccK δ

def fld : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.embLL ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})

theorem embLL_mem (x : D.what₂.LL) : D.what₂.embLL x ∈ fld D δ t0 :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨x, rfl⟩)

def ext (σ : D.what₂.LL →+* ℂ) : Set (fld D δ t0 →ₐ[ℚ] ℂ) :=
  {ρ | ∀ x, ρ ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩ = σ x}


open Classical in
def tc (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℂ :=
  if h : ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) t then h.choose else 0

def hArea (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ := Real.posLog (area (lamConj (fld D δ t0) ρ (lat D δ)))⁻¹

def hTh (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ :=
  Real.posLog (nrm1Sq (lamConj (fld D δ t0) ρ (lat D δ)) (GL3Theta.th0 (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ)))

def avg (σ : D.what₂.LL →+* ℂ) (h : (fld D δ t0 →ₐ[ℚ] ℂ) → ℝ) : ℝ :=
  (∑ᶠ ρ ∈ ext D δ t0 σ, h ρ) / Nat.card (ext D δ t0 σ)

end GlobalTheory.KerConjMean

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.KerConjMean

open GlobalTheory.SumSize GlobalTheory.RowTest GlobalTheory.FunObj GlobalTheory.ChiGrid Formalism.IndefR.Links Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  (ch : _root_.GlobalTheory.RowTest.Choice R) (C b C1 : ℝ)

def RatTopAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1))), ∀ u,
    ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjTopAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ), nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.SumCount

section

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def DataNum : Prop := (Nat.card ch.G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def CosNum : Prop := ∀ Φ, ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def PureNum : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ τ,
  IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ →
    (τ.support.card : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

end

def DataK : Prop := BigC fun _ ch C b => DataNum ch C b

def CosK : Prop := BigC fun _ ch C b => CosNum ch C b

def PureK : Prop := BigC fun _ ch C b => PureNum ch C b


open IsDedekindDomain NumberField Matrix in
theorem _root_.GlobalTheory.SumCount.infCountK_of (h1 : _root_.GlobalTheory.SumCount.DataK)
    (h2 : _root_.GlobalTheory.SumCount.CosK) (h3 : _root_.GlobalTheory.SumCount.PureK) :
    _root_.GlobalTheory.SumSize.InfCountK := by
  unfold _root_.GlobalTheory.SumSize.InfCountK
  obtain ⟨s₁, h1⟩ := h1
  obtain ⟨s₂, h2⟩ := h2
  obtain ⟨s₃, h3⟩ := h3
  refine ⟨max s₁ (max s₂ s₃), fun CF hCF ↦ ?_⟩
  obtain ⟨C1, h1⟩ := h1 CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, h2⟩ := h2 CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C3, h3⟩ := h3 CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C1 (max C2 C3), fun ε C hC ↦ ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, h2⟩ := h2 ε C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC)
  obtain ⟨x3, h3⟩ := h3 ε C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC)
  refine ⟨max x1 (max x2 x3), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hR ch hch hs hf ↦ ?_⟩
  have a1 := h1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hR ch hch hs hf
  have a2 := h2 D large₂ he (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
    Γ Pl0 T A Ks R F hR ch hch hs hf
  have a3 := h3 D large₂ he (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
    Γ Pl0 T A Ks R F hR ch hch hs hf
  exact ⟨a1, fun Φ ↦ ⟨a2 Φ, a3 Φ⟩⟩

end GlobalTheory.SumCount

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.ArchTens

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeSz {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) : ℝ :=
  (cosExp G w : ℝ) * Real.log (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)

theorem placeSz_nonneg {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (w : Pl D.host.E) :
    0 ≤ placeSz G w :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C : ℝ)

def DatAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ (w : locPl ch.G A.μ0) x y,
  AbsLe σ ((ch.S.term A.μ0 Φ β w).datum (ch.S.colAt A.μ0 w x) (ch.S.rowAt A.μ0 w y))
    (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def FlipAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ (w : locPl ch.G A.μ0) z,
  AbsLe σ (Tflip ch.W ch.S.B A.μ0 Φ w z) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

def CoefAt : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ w : locPl ch.G A.μ0,
  |((ch.S.term A.μ0 Φ β w).coef : ℝ)| ≤ Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz ch.G w)

end Claims

section Abs

variable {D : D7}

theorem absLe_mono {σ : D.what₂.LL →+* ℂ} {z : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (hB : B ≤ B') : AbsLe σ z B' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.trans (Real.exp_le_exp.2 hB)⟩

theorem absLe_mul {σ : D.what₂.LL →+* ℂ} {z z' : ℂ} {B B' : ℝ} (h : AbsLe σ z B) (h' : AbsLe σ z' B') :
    AbsLe σ (z * z') (B + B') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  refine ⟨y * y', by rw [map_mul, e, e'], ?_⟩
  rw [map_mul, norm_mul, Real.exp_add]
  exact mul_le_mul hy hy' (norm_nonneg _) (Real.exp_pos _).le

theorem absLe_prod {ι : Type} (s : Finset ι) {σ : D.what₂.LL →+* ℂ} (z : ι → ℂ) (B : ι → ℝ) (h : ∀ i ∈ s, AbsLe σ (z i) (B i)) :
    AbsLe σ (∏ i ∈ s, z i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, map_one _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact absLe_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem absLe_rat (σ : D.what₂.LL →+* ℂ) (q : ℚ) {B : ℝ} (h : |(q : ℝ)| ≤ Real.exp B) : AbsLe σ (q : ℂ) B := by
  refine ⟨(q : D.what₂.LL), map_ratCast _ _, ?_⟩
  rw [map_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Abs

theorem sum_placeSz_le {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) :
    ∑ w : locPl G t, placeSz G w ≤ sig G := by
  classical
  rw [Finset.sum_coe_sort (locPl G t) (placeSz G)]
  have h1 : ∑ w ∈ locPl G t, placeSz G w = ∑ w ∈ G.pl.W0, placeSz G w := by
    refine (Finset.sum_subset (Finset.subset_union_left) fun w _ hw => ?_).symm
    simp [placeSz, (depthAt_of_notMem G hw).1]
  rw [h1, sig]
  unfold Places.W0
  refine (Finset.sum_image_le_of_nonneg fun w _ => placeSz_nonneg G w).trans (le_of_eq (Finset.sum_congr rfl fun v hv => ?_))
  rw [placeSz, (depthAt_w G hv).1, G.pl.under_w hv]

end GlobalTheory.ArchTens

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqCompare

theorem gBig_three {Q₁ Q₂ Q₃ Q : GP} (h₁ : GBig Q₁) (h₂ : GBig Q₂) (h₃ : GBig Q₃)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  obtain ⟨F₃, h₃⟩ := h₃
  refine ⟨max F₁ (max F₂ F₃), fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C₂, x₂, k₂⟩ := h₂ ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C₃, x₃, k₃⟩ := h₃ ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C₁ (max C₂ C₃), max x₁ (max x₂ x₃), fun C hC D large₂ he hx hR T Lc μ₀ hL G => H G μ₀ C _ _ ?_ ?_ ?_⟩
  · exact k₁ C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  · exact k₂ C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G
  · exact k₃ C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hR T Lc μ₀ hL G

end GlobalTheory.SqCompare
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

theorem _root_.GlobalTheory.T.const_one_mem_cuspForms_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ cA : CptF (GlobalTheory.Grid.neg A), HidaSetting W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s A'.rank cA → (fun _ => (1 : ℂ)) ∈ A0 W.θ (GlobalTheory.Grid.neg A) cA := by
  first | exact @GlobalTheory.BottomCusp.one_mem_A0_of_isBottomTri | exact GlobalTheory.BottomCusp.one_mem_A0_of_isBottomTri | (intros; apply GlobalTheory.BottomCusp.one_mem_A0_of_isBottomTri <;> assumption)
end
