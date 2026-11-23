module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.TripleCplxAt

variable {m n : Type} [Fintype m] [Fintype n]

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map conj).map conj = M := by
  ext; simp

theorem smul_map_conj {m n : Type} (c : ℂ) (M : Matrix m n ℂ) : (c • M).map conj = conj c • M.map conj := by
  ext; simp

theorem transpose_map_conj {k : Type} (M : Matrix k k ℂ) : (M.map conj)ᵀ = Mᴴ := by
  ext; simp [Matrix.conjTranspose_apply]

theorem cartan_comm {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  obtain ⟨h1, h2, -⟩ := h
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h2]

theorem mul_cols {a b d k : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (X : Matrix (Fin b) (Fin d) ℂ) (f : Fin k → Fin d) :
    (A * X).submatrix id f = A * X.submatrix id f := by
  ext; simp [Matrix.mul_apply]

theorem smul_cols {a d k : ℕ} (c : ℂ) (X : Matrix (Fin a) (Fin d) ℂ) (f : Fin k → Fin d) :
    (c • X).submatrix id f = c • X.submatrix id f := by
  ext; simp

theorem conj_hyp {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ)) :
    X' = (-Complex.I) • (sW.map conj * X * (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁)ᵀ) := by
  have h := congrArg (fun M => M.map (starRingEnd ℂ)) hX
  simp only [map_conj_conj, smul_map_conj, Matrix.map_mul, Complex.conj_I] at h
  rw [h, ← Matrix.transpose_map, map_conj_conj]

theorem algV {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW G : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : sWᴴ * G = G * sW) :
    (X'.submatrix id fun k => e (.inl k))ᵀ * (-G) =
      Complex.I • (cV * ((X.submatrix id fun k => e (.inl k))ᵀ * (-G)) * (-sW)) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inl, mul_cols, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, transpose_map_conj]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_smul, neg_neg, hs]

theorem algW {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ G₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : cV₁ᴴ * G₁ = G₁ * cV₁) :
    -((X'.submatrix id fun k => e (.inr k)).map conj * G₁) =
      Complex.I • (sW * (-((X.submatrix id fun k => e (.inr k)).map conj * G₁)) * cV₁) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inr, mul_cols, smul_map_conj, Matrix.map_mul, Matrix.map_mul, map_conj_conj,
    Matrix.transpose_map, transpose_map_conj]
  simp only [map_neg, Complex.conj_I, neg_neg, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul,
    Matrix.mul_neg, smul_neg, neg_smul, hs]

end GlobalTheory.TripleCplxAt

namespace GlobalTheory.TripleCplxAt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

section Adelic

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {a b c : ℕ} (A : Mx D a b) (B : Mx D b c) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_neg' (θ : InfFam D) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (-A) = -compAt θ τ A :=
  Matrix.map_neg _ (fun a => map_neg ((θ τ).comp (infPart D)) a) A

theorem compAt_inc (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) :
    compAt θ τ (A.map (incA D)) = A.map (tauE D τ) := by
  ext x y; exact (hθ τ).1 (A x y)

theorem compAt_conj (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (A.map (cA D)) = (compAt θ τ A).map conj := by
  ext x y; exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_mapV (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapV e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * (-gramAt D (spW G i j) τ) := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((negSp (spW G i j)).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ, negSp_gram, Matrix.map_neg _ (map_neg _)]
  rfl

theorem compAt_mapW (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapW e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl

end Adelic

theorem cplx_pair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ u u' : Pt G i j, (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) → ∀ τ,
      compAt W.θ τ (mapV e u') = cplxO (-W.cart (.grid (i + 1) (j + 1)) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapV e u)) ∧
      compAt W.θ τ (mapW e u') = cplxO (W.cart (.grid (i + 1) j) τ) (W.cart (.grid (i + 1) (j + 1)) τ) (compAt W.θ τ (mapW e u)) := by
  intro D T L sc G W M t i j e Bs Γ X h u u' hu τ
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V.θ w = W.cart (.grid (i + 1) (j + 1)) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, hV, -, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : Pt G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW := W.cart_is (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · rw [compAt_mapV W.θ W.θ_is, compAt_mapV W.θ W.θ_is]
    exact algV e _ _ _ _ _ _ hX (cartan_comm cW)
  · rw [compAt_mapW W.θ W.θ_is, compAt_mapW W.θ W.θ_is]
    exact algW e _ _ _ _ _ _ hX (cartan_comm cV₁)

end GlobalTheory.TripleCplxAt

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilCont

theorem adeleJoin_zero_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  simp only [adeleJoin, Pi.zero_apply, map_zero, Prod.mk_zero_zero]

theorem sum_mul_zero_prod {κ : Type} [Fintype κ] {A B : Type} [CommRing A] [CommRing B] (z : κ → A × B)
    (y : κ → B) : (∑ i, z i * ((0 : A), y i)) = ((0 : A), ∑ i, (z i).2 * y i) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem dotProduct_adeleJoin_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (z : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    z ⬝ᵥ adeleJoin F 0 y = pairA F 0 ((fun i => (z i).2) ⬝ᵥ y) := by
  simp only [dotProduct, adeleJoin, pairA, Pi.zero_apply, map_zero]
  exact sum_mul_zero_prod (A := InfiniteAdeleRing F) (B := FiniteAdeleRing (𝓞 F) F) z y

theorem exists_local_finite_parts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
        om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f i) (g i) := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ _ co hco ω hω om hom Φ hΦ p0
  obtain ⟨pres, impl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ co hco ω hω om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := GlobalTheory.T.exists_openSubgroups_schroedinger_fix_standardChar D ψ hψ κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := GlobalTheory.T.exists_nhds_transportedAction_finite_openSubgroups D T.rank S.rank JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := GlobalTheory.T.isCompact_finiteAdeleAnnihilator_stdChar D ψ hψ κ L₂' hL₂'
  have hA := GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition D.host.F κ L₁' hL₁' hL₁c _ hK
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := hA
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', GlobalTheory.WeilM.schr ψ (adeleJoin D.host.F 0 x,
      adeleJoin D.host.F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    have hxy := hNL p hp x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hxy
    have := impl p (co.e.symm (adeleJoin D.host.F 0 x', adeleJoin D.host.F 0 y')) Φ hΦ
    simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy', he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [GlobalTheory.WeilM.schr, adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [GlobalTheory.WeilM.schr, adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this

end GlobalTheory.WeilCont

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

noncomputable section

namespace GlobalTheory.LocArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

@[reducible] def arcRestrict (b : O →+* O') (hb : β'.comp b = β) {O'' : Type} [CommRing O''] [IsDomain O'']
    {b' : O' →+* O''} (a : ArcIn D l β' O'' b') : ArcIn D l β O'' (b'.comp b) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom := fun F _ _ _ r z hr hz => a.geom F (b r) (b z) (by rw [← hb] at hr; exact hr) (by rw [← hb] at hz; exact hz)

variable (Y : Model Xo c β) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)]

theorem mono_locMap : Mono (locMap Y b).φ :=
  (MorphismProperty.monomorphisms Scheme.{0}).of_isPullback (locMap Y b).cart.1.flip
    (show Mono (pullback.fst Y.s (spMap b)) from inferInstance)

theorem hasArcData_iff {O'' R : Type} [CommRing O''] [IsDomain O''] [CommRing R] [IsDomain R] {b' : O' →+* O''}
    (a : ArcIn D l β' O'' b') (I : Ideal R) (f : O'' →+* R) (u : R) (χ : Sp R ⟶ (locModel Y b hb).X) :
    (locModel Y b hb).HasArcData a I f u χ ↔
      Y.HasArcData (arcRestrict b hb a) I f u (χ ≫ pullback.fst Y.s (spMap b)) := by
  have ej := locModel_j Y b hb
  have em := locModel_m Y b hb
  constructor
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, ej, hy]
      simp only [Category.assoc]
    · have := mono_locMap Y b
      rw [← cancel_mono (locMap Y b).φ]
      rw [hn, ← em] at k₄
      simp only [Category.assoc]
      exact k₄
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_cancel (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← ej, ← Category.assoc, hy]
      simp only [Category.assoc]
    · have := congrArg (· ≫ (locMap Y b).φ) k₄
      simp only [Category.assoc] at this
      rw [hn, ← em]
      exact this

theorem mem_range_j_iff (x : (locModel Y b hb).X) :
    x ∈ Set.range (locModel Y b hb).j ↔ pullback.fst Y.s (spMap b) x ∈ Set.range Y.j := by
  rw [← locModel_j Y b hb]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, (pullback.fst Y.s (spMap b)).isEmbedding.injective ?_⟩
    rw [← hu, Scheme.Hom.comp_apply]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem locModel_arc (h : Y.N4) : (locModel Y b hb).N4 := by
  intro O'' _ _ _ b' ϖ a hO
  obtain ⟨χ₀, hu, hs⟩ := h O'' (b'.comp b) ϖ (arcRestrict b hb a) hO
  obtain ⟨c₁, c₂, c₃, c₄⟩ := (hu χ₀).1 rfl
  have hw : χ₀ ≫ Y.s = (spMap (PowerSeries.C (R := O'')) ≫ spMap b') ≫ spMap b := by
    rw [c₁, spMap_comp', Category.assoc]
  have hχ : pullback.lift χ₀ _ hw ≫ pullback.fst Y.s (spMap b) = χ₀ := pullback.lift_fst _ _ _
  refine ⟨pullback.lift χ₀ _ hw, fun χ' => ⟨?_, ?_⟩, fun hi y' ev d₁ d₂ d₃ d₄ d₅ => ?_⟩
  · rintro rfl
    refine ⟨pullback.lift_snd _ _ _, fun x => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_abLocus_locModel, ← Scheme.Hom.comp_apply, hχ]
      exact c₂ x
    · rw [mem_range_j_iff, ← Scheme.Hom.comp_apply, hχ]
      exact c₃ x hx
    · rw [hasArcData_iff, hχ]
      exact c₄
  · rintro ⟨d₁, d₂, d₃, d₄⟩
    rw [← cancel_mono (pullback.fst Y.s (spMap b)), hχ]
    refine (hu _).2 ⟨?_, fun x => ?_, fun x hx => ?_, (hasArcData_iff Y b hb a _ _ _ _).1 d₄⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp', ← Category.assoc]
      exact congrArg (· ≫ spMap b) d₁
    · rw [Scheme.Hom.comp_apply, ← mem_abLocus_locModel Y b hb]
      exact d₂ x
    · rw [Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₃ x hx
  · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, hχ]
    refine hs hi _ ev ?_ ?_ ((hasArcData_iff Y b hb a _ _ _ _).1 d₃) d₄ d₅
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp']
      exact congrArg (· ≫ spMap b) d₁
    · rintro _ ⟨q, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₂ ⟨q, rfl⟩

end GlobalTheory.LocArc

theorem GlobalTheory.LocArc.arc_localise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ b hb _ _ h => GlobalTheory.LocArc.locModel_arc Y b hb h
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

namespace GlobalTheory.BoxNonzeroClosed

theorem flat_powObj {S : Scheme.{0}} (G : Over S) [Flat G.hom] : ∀ n : ℕ, Flat (Out.powObj G n).hom
  | 0 => inferInstanceAs (Flat (𝟙 S))
  | n + 1 => by
    have := flat_powObj G n
    exact inferInstanceAs (Flat (pullback.fst G.hom (Out.powObj G n).hom ≫ G.hom))

theorem flat_pow {S : Scheme.{0}} (G : Over S) [Flat G.hom] (N : ℕ) : Flat (pow G N).hom := by
  have := flat_powObj G N
  let e : pow G N ≅ Out.powObj G N :=
    (productIsProduct (fun _ : Fin N => G)).conePointUniqueUpToIso (Out.powIsLimit G N)
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← Over.w e.hom]
  infer_instance

theorem main : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec),
    NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  rintro V _ _ G _ L θ ⟨g, hg, hθ⟩ N
  refine ⟨flat_pow G N, ?_⟩
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.BoxSection.exists_point (fun k => Pi.π (fun _ : Fin N => G) k)
    (productIsProduct (fun _ : Fin N => G)) _ (fun _ => g) (fun _ => hg)
  exact ⟨y, hy, GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec L (pr G N) (fun _ => θ) y
    fun i => (hy' i).symm ▸ hθ⟩

end GlobalTheory.BoxNonzeroClosed
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_nsmul_symplecticPairing_character_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
    ∀ (S T : HSp D) (A0 : WO S T), ∃ N : ℕ, 0 < N ∧ ∀ v : WO S T, (∀ i j, infPart D (v i j) = 0) →
      (∀ i j, GlobalTheory.BotClassDict.finQ D (v i j) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) → ψ (symplOH S T A0 (N • v)) = 1 := by
  first | exact @GlobalTheory.FinCharInt.char_sympl_nsmul_int | exact GlobalTheory.FinCharInt.char_sympl_nsmul_int | (intros; apply GlobalTheory.FinCharInt.char_sympl_nsmul_int <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  first | exact @GlobalTheory.pull_two_nsmul_eq_zero_of_triples | exact GlobalTheory.pull_two_nsmul_eq_zero_of_triples | (intros; apply GlobalTheory.pull_two_nsmul_eq_zero_of_triples <;> assumption)
end
