module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle250
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle249
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle252
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.BaseFrame

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_x0Mat {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {r : ℕ} (hr : V.rank = r) (ρ : D.what₂.Tau)
    {p q : ℕ} (hpq : r = p + q) (hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p)) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
      (Matrix.reindex (finCongr hr) (finCongr hr) (x0Mat M ρ)) =
      Matrix.diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ) := by
  subst hr
  have hp : p ≤ V.rank := by omega
  have hq : nNeg (M.ε ρ) = q := (nNeg_shape hp hε).trans (by omega)
  have h0 : ∀ x : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := fun x => by
    ext a b
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply,
      conjTranspose_apply, gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring
  have hinv : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ))
  have h1 : ((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
    rw [← M.fr_gram ρ]
    calc _ = (M.fr ρ * (M.fr ρ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε ρ) * (M.fr ρ * (M.fr ρ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hinv]; simp
  have h2 : (x0Mat M ρ)ᴴ * gramAt D V ρ * x0Mat M ρ =
      (((M.fr ρ)⁻¹)ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (arr (nNeg (M.ε ρ))) (arr (nNeg (M.ε ρ))) := rfl
  show ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) (x0Mat M ρ) = _
  rw [h0, h2, h1, hq]
  ext a c
  have ha := a.2
  have hc := c.2
  simp only [transpose_apply, Matrix.neg_apply, submatrix_apply, Formalism.REAL.Jm, diagonal_apply, hε, sgn, arr, Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

theorem exists_baseFrame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → AlgTie T → FrameKs T.Q.c.F R.MW → ∃ (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k, IsOrthogonalFrame ((T.U j σ).X k) (x₀ j σ) := by
  intro D G _ _ Pl0 T0 A T _ R hL hA hF
  classical
  let x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ := fun j s τ =>
    if h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau, j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2 then
      Matrix.reindex (finCongr (rank_Wc h.choose.1)) (finCongr (rank_Wc h.choose.1))
        (x0Mat (R.MW h.choose.1 h.choose.2.1) h.choose.2.2)
    else T.x₀ j s τ
  have key : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (x₀ ((i : ℕ) + 1) (res T σ)) := by
    intro i σ ρ
    have h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        (i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2 := ⟨(i, σ, ρ), rfl, rfl, rfl⟩
    have aux : ∀ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
        ((i : ℕ) + 1 = (p.1 : ℕ) + 1 ∧ res T σ = res T p.2.1 ∧ tauE D ρ = tauE D p.2.2) →
        Matrix.reindex (finCongr (rank_Wc p.1)) (finCongr (rank_Wc p.1)) (x0Mat (R.MW p.1 p.2.1) p.2.2) =
          Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (x0Mat (R.MW i σ) ρ) := by
      rintro ⟨i', σ', ρ'⟩ ⟨h1, h2, h3⟩
      obtain rfl : i = i' := Fin.ext (Nat.add_right_cancel h1)
      obtain rfl : ρ = ρ' := tauE_injective h3
      rw [hF.1 i σ σ' h2 ρ]
    exact (dif_pos h).trans (aux _ h.choose_spec)
  refine ⟨x₀, fun i σ _ => key i σ, fun j hj s hs k τ hτ => ?_⟩
  by_cases h : ∃ p : Fin D.R.m × (D.what₂.LL →+* ℂ) × D.what₂.Tau,
      j = (p.1 : ℕ) + 1 ∧ s = res T p.2.1 ∧ τ = tauE D p.2.2
  · obtain ⟨⟨i, σ, ρ⟩, rfl, rfl, rfl⟩ := h
    dsimp only at hj hs k hτ ⊢
    have hU := hL.unf _ hj _ hs
    have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hL.pins.2.2.2 _ hj).1
    have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) (res T σ)).X k) := by
      obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hs
      have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := hL.spaceW _ hj _ hs
      have h1 := hm k
      revert hr
      rw [hV]
      exact fun _ _ h => h
    have hε : ∀ a, (R.MW i σ).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun a => by
      rw [hF.2 i σ (fun ρ' => (GlobalTheory.HolRead.good_iff_labE_and_lab_conj D T hL hA σ ρ').1.1 hs) ρ a, hdp,
        show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    rw [key i σ ρ, hM.1, (hU.2.1 k).1]
    exact gram_x0Mat _ _ ρ hU.1 hε
  · have e : x₀ j s τ = T.x₀ j s τ := dif_neg h
    rw [e]
    exact hL.familyUniformisationBasePointOrthogonal j hj s hs k τ hτ

end GlobalTheory.RealGeo.BaseFrame
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseEx

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

end ext

section host

variable {R : Ranks} (H : Host R)

theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩


end host

end GlobalTheory.Mem.BaseEx

end
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem CoBear₂ : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ g hg hco K _
  have hcomp : ∀ p : Sp K ⟶ Y₁.X, p ≫ f₁ = (p ≫ g) ≫ f₂ := by
    intro p; rw [Category.assoc, hg]
  constructor
  · intro p p' hpp'
    simp only at hpp'
    have h1 := hco K p
    have h2 := hco K p'
    rw [← hpp'] at h2
    exact GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p p' (p ≫ g) (hcomp p)
      (by rw [hcomp p', hpp']) h1 h2
  · intro w
    obtain ⟨A, hA, h, hh, hw⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ hR₂ K w
    obtain ⟨p, ⟨hpx, hpA⟩, -⟩ := hR₁.2.2 K (w ≫ f₂) A hA h hh
    obtain ⟨B, hB, h', -, hpB, hqB⟩ := hco K p
    have hA' : A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)) := by rw [hpx]; exact hA
    have hqA : Bears S₂ φ₂ A h (p ≫ g) :=
      GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p (p ≫ g) (hcomp p) A hA' B hB h h'
        hpA hpB hqB
    obtain ⟨q, -, hq⟩ := hR₂.2.2 K (w ≫ f₂) A hA h hh
    refine ⟨p, ?_⟩
    simp only
    rw [hq (p ≫ g) ⟨by rw [← hcomp p, hpx], hqA⟩, hq w ⟨rfl, hw⟩]

end GlobalTheory.FlagBundle
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gelfandInvariantAction_commute_unitaryRep_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (k : ℕ), ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ w ∈ smSub G (trRep σ P), gelfH G (trRep σ P) k ((trRep σ P) g w) = (trRep σ P) g (gelfH G (trRep σ P) k w) := by
  first | exact @GlobalTheory.SmVecGelfComm.gelfH_rep | exact GlobalTheory.SmVecGelfComm.gelfH_rep | (intros; apply GlobalTheory.SmVecGelfComm.gelfH_rep <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.admitted

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isKFin_of_mem_closure (hσ : IsURepOn (UJset ε) σ) {U : Set H} {M : ℕ}
    (hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S)
    {u : H} (hu : u ∈ closure U) : IsKFin ε σ u := by
  let t : Set H := Set.range fun k : KG ε => σ (toMK k) u
  obtain ⟨b, hbt, hsp, hli⟩ := exists_linearIndependent ℂ t
  have hfin : b.Finite := by
    by_contra hinf
    haveI : Infinite b := Set.infinite_coe_iff.2 hinf
    let e : Fin (M + 1) ↪ b := Fin.valEmbedding.trans (Infinite.natEmbedding b)
    choose k hk using fun i => hbt (e i).2
    have hc : Continuous fun w : H => fun i : Fin (M + 1) => σ (toMK (k i)) w :=
      continuous_pi fun i => (σ _).continuous
    have ho := (isOpen_setOf_linearIndependent (𝕜 := ℂ) (E := H) (ι := Fin (M + 1))).preimage hc
    have hu' : LinearIndependent ℂ fun i : Fin (M + 1) => σ (toMK (k i)) u := by
      have := hli.comp e e.injective
      rwa [show (Subtype.val ∘ e : Fin (M + 1) → H) = _ from funext fun i => (hk i).symm] at this
    obtain ⟨w, hw, hwU⟩ := mem_closure_iff.1 hu _ ho hu'
    obtain ⟨S, hS, hM, hwS, hK⟩ := hU w hwU
    have h1 : LinearIndependent ℂ fun i : Fin (M + 1) =>
        (⟨σ (toMK (k i)) w, hK _ (toMK_mem_K _) w hwS⟩ : S) :=
      LinearIndependent.of_comp S.subtype hw
    have h2 := h1.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨Submodule.span ℂ t, hsp ▸ FiniteDimensional.span_of_finite ℂ hfin, Submodule.subset_span ⟨1, ?_⟩,
    fun g hg v hv => ?_⟩
  · exact sigma_one hσ u
  · refine (Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
    exact Submodule.subset_span ⟨g' * k, sigma_mul hσ (K_le_UJ hg) (K_le_UJ (toMK_mem_K k)) u⟩

variable [CompleteSpace H]

theorem exists_word_clm (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W] (hW : ∀ w ∈ W, Sm ε σ w)
    {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) : ∃ A : W →L[ℂ] H, ∀ w : W, A w = Dw σ l w := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) h.1 l hl
  let A : W →ₗ[ℂ] H := (smooth (Jm ε) σ).subtype ∘ₗ L ∘ₗ Submodule.inclusion hW
  have hA : ∀ x : W, A x = Dw σ l x := fun x => hL _
  refine ⟨⟨A, A.continuous_of_seq_closed_graph fun s x z hs hz =>
    h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_⟩, hA⟩
  have h1 : Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) atTop (𝓝 ⟪y, z⟫_ℂ) := tendsto_const_nhds.inner hz
  simp only [hA, fun x : W => inner_Dw h.1 hl hy (hW _ x.2)] at h1 ⊢
  exact tendsto_nhds_unique h1
    (tendsto_const_nhds.mul (tendsto_const_nhds.inner ((continuous_subtype_val.tendsto x).comp hs)))

theorem finiteDimensional_of_smooth (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W]
    (hW : ∀ w ∈ W, Sm ε σ w) : FiniteDimensional ℂ W := by
  obtain ⟨S, C, hS, hC, hts⟩ := GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt n ε H σ h
  choose A hA using fun l : {l // l ∈ S} => exists_word_clm h W hW (hS l.1 l.2)
  haveI : Finite {l // l ∈ S} := (List.finite_toSet S).to_subtype
  obtain ⟨B, hB⟩ := (Set.finite_range fun l => ‖A l‖ ^ 2).bddAbove
  have hB' : ∀ l, ‖A l‖ ^ 2 ≤ |B| := fun l => (hB ⟨l, rfl⟩).trans (le_abs_self B)
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ W
  have hfin : Finite w := by
    by_contra hinf
    haveI : Infinite w := not_finite_iff_infinite.1 hinf
    obtain ⟨m, hm⟩ := exists_nat_gt (C * |B|)
    let e : Fin m ↪ w := Fin.valEmbedding.trans (Infinite.natEmbedding w)
    have ho : Orthonormal ℂ fun j => b (e j) := b.orthonormal.comp e e.injective
    have key := hts (Fin m) (fun j => b (e j)) (fun j => b (e j)) |B| (abs_nonneg B) (fun j => hW _ (b (e j)).2)
      (fun l hl z => by
        have e1 : ∑ j, z j • Dw σ l (b (e j) : H) = A ⟨l, hl⟩ (∑ j, z j • b (e j)) := by

          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hA]
        have e2 : ‖∑ j, z j • b (e j)‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
          have := ho.inner_sum z z Finset.univ
          rw [inner_self_eq_norm_sq_to_K] at this
          simp only [RCLike.conj_mul] at this
          exact_mod_cast this
        rw [e1, ← e2]
        calc _ ≤ (‖A ⟨l, hl⟩‖ * ‖∑ j, z j • b (e j)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((A _).le_opNorm _) 2
          _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hB' _) (sq_nonneg _))
    have hn : ∀ j, ‖(b (e j) : H)‖ = 1 := fun j => ho.1 j
    simp only [inner_self_eq_norm_sq_to_K, hn] at key
    simp at key
    have h0 : 0 ≤ C * |B| := mul_nonneg hC (abs_nonneg B)
    nlinarith
  haveI := Fintype.ofFinite w
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

end GlobalTheory.TypeSum.admitted

namespace GlobalTheory.TypeSum

theorem finiteDimensional_of_bounded_orbits : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ),
    (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) →
      FiniteDimensional ℂ U := by
  intro n ε H _ _ _ σ h U M hU
  haveI : CompleteSpace U.topologicalClosure := U.isClosed_topologicalClosure.completeSpace_coe
  haveI := admitted.finiteDimensional_of_smooth h U.topologicalClosure fun w hw =>
    h.2.2.1 w (admitted.isKFin_of_mem_closure h.1 (U := U) hU hw)
  exact Submodule.finiteDimensional_of_le U.le_topologicalClosure

end GlobalTheory.TypeSum
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_polyRep_combination_pure_power_trace : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (i : ℕ), 1 ≤ i → ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n → ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  first | exact @GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | exact GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace | (intros; apply GlobalTheory.GoodMetric.PureVirt.exists_pure_power_trace <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.exists_finite_measure_reduction_domain_infinity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Λ : Submodule (𝓞 E) (Fin a → E)), Submodule.IsFullLattice E Λ → ∀ [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))] (ν : Measure (GL (Fin a) (Cinf E))) [ν.IsHaarMeasure], ∃ Ω : Set (GL (Fin a) (Cinf E)), ν Ω < ⊤ ∧ ∀ y, ∃ γ : GL (Fin a) E, (∀ x, (γ : Matrix (Fin a) (Fin a) E) *ᵥ x ∈ Λ ↔ x ∈ Λ) ∧ ∃ n : ℤ, GeneralLinearGroup.map (pInf E) (ratGL E a γ * splitCentre E a 1 ^ n) * y ∈ Ω := by
  first | exact @GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | exact GlobalTheory.GLInfReduction.exists_cover_of_finite_measure | (intros; apply GlobalTheory.GLInfReduction.exists_cover_of_finite_measure <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

theorem eq_of_psiInf_eq {F : Type} [Field F] [NumberField F] {ψ ψ' : AddChar (AF F) ℂ}
    (h : IsCharAF F ψ) (h' : IsCharAF F ψ') (e : ∀ x, psiInf F ψ x = psiInf F ψ' x) : ψ = ψ' := by
  have hrat : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = ψ' (pairA F 0 (algebraMap F (Af F) x)) := fun x => by
    rw [GlobalTheory.StdRat.char_fin_rat ψ h, GlobalTheory.StdRat.char_fin_rat ψ' h', e]
  have hp : Continuous fun y : Af F => pairA F 0 y := Continuous.prodMk continuous_const continuous_id
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = ψ' (pairA F 0 α) :=
    fun α hα => GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 y) = ψ' (pairA F 0 y)})
      (isClosed_eq (h.1.comp hp) (h'.1.comp hp)) (fun a => hrat a) α hα
  have hfin : ∀ y : Af F, ψ (pairA F 0 y) = ψ' (pairA F 0 y) := fun y => by
    obtain ⟨a, s, hs, hy⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos y
    have e1 : pairA F 0 y = pairA F 0 (algebraMap F (Af F) a) + pairA F 0 s := by
      refine Prod.ext (add_zero _).symm ?_
      show y = algebraMap F (Af F) a + s
      simpa only [one_smul] using hy
    rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hrat, hint s hs]
  refine AddChar.ext _ _ fun a => ?_
  have e2 : a = pairA F a.1 0 + pairA F 0 a.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hfin]
  exact congrArg (· * _) (e a.1)

theorem isCharAF_inv {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) :
    IsCharAF F ψ⁻¹ := by
  refine ⟨?_, fun x => ?_, fun a => ?_, ?_⟩
  · exact h.1.comp continuous_neg
  · exact h.2.1 (-x)
  · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
  · obtain ⟨x, hx⟩ := h.2.2.2
    exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩

theorem isStdChar_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) :
    IsStdChar D ψ⁻¹ (-s) := by
  refine ⟨isCharAF_inv h.1, h.2.1, fun θ hθ x => ?_⟩
  have e : psiInf D.host.F ψ⁻¹ x = psiInf D.host.F ψ (-x) := by
    rw [psiInf, psiInf, AddChar.inv_apply]
    exact congrArg ψ (Prod.ext rfl neg_zero)
  rw [e, h.2.2 θ hθ]
  simp only [TensorProduct.neg_tmul, map_neg, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s)
    (h' : IsStdChar D ψ' s) : ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem existsUnique_isStdChar :
    ∀ (D : D7) (s : ℤ), s = 1 ∨ s = -1 → ∃! ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ s := by
  intro D s hs
  obtain ⟨ψ, hψ⟩ := exists_isStdChar D
  rcases hs with rfl | rfl
  · have h1 : IsStdChar D ψ⁻¹ 1 := by simpa using isStdChar_inv hψ
    exact ⟨ψ⁻¹, h1, fun ψ' h' => isStdChar_unique h' h1⟩
  · exact ⟨ψ, hψ, fun ψ' h' => isStdChar_unique h' hψ⟩

end GlobalTheory.StdAdelicChar

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coeffExt_rationalForms_values_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL → ∃ c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, (∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i jL σ' (c0L i) c0') ∧ ∀ t (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)), PlaceEx R i t h c0' := by
  first | exact @GlobalTheory.Mem.PlaceVal.exists_coef_placeEx | exact GlobalTheory.Mem.PlaceVal.exists_coef_placeEx | (intros; apply GlobalTheory.Mem.PlaceVal.exists_coef_placeEx <;> assumption)
end

section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  first | exact @GlobalTheory.HighestPolynomial.exists_intertwiner | exact GlobalTheory.HighestPolynomial.exists_intertwiner | (intros; apply GlobalTheory.HighestPolynomial.exists_intertwiner <;> assumption)
end
