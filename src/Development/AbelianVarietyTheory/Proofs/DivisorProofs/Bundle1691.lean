module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle003
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.LocalRingCardinality.Bundle007
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SymmetricPowerMatrix
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef.DFormPos

theorem sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) (y : G.Cˣ) (s : ℚ),
    (y : G.C) * B.β * sh G y = algebraMap ℚ G.C s * B.β → 0 < s := by
  intro p _ G B y s hsim0
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  set h := G.gram v
  set A := G.psi v (y : G.C)
  set Ai := G.psi v ((y⁻¹ : G.Cˣ) : G.C)
  set Pb := G.psi v (B.β : G.C)
  set Bm := G.psi v ((B.β⁻¹ : G.Cˣ) : G.C)
  set c : ℂ := ((s : ℚ) : ℂ)
  have hsim := congrArg (G.psi v) hsim0
  have hc : G.psi v (algebraMap ℚ G.C s) = c • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F]
    ext i j; simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, c]
  rw [map_mul, map_mul, map_mul, hc] at hsim
  change A * Pb * G.psi v (G.star (y : G.C)).unop = _ at hsim
  rw [G.psi_star, Matrix.smul_mul, Matrix.one_mul] at hsim
  have hBβ : Bm * Pb = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hβB : Pb * Bm = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hAiA : Ai * A = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hdet : IsUnit h.det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hhi : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h hdet
  have e1 : Aᴴ * h = c • (h * Bm * Ai * Pb) := by
    have := congrArg (fun M => h * Bm * Ai * M) hsim
    calc Aᴴ * h = h * Bm * Ai * (A * Pb * (h⁻¹ * Aᴴ * h)) := by
          simp only [← Matrix.mul_assoc]
          rw [Matrix.mul_assoc (h * Bm) Ai A, hAiA, Matrix.mul_one, Matrix.mul_assoc h Bm Pb, hBβ, Matrix.mul_one, hhi,
            Matrix.one_mul]
      _ = _ := by rw [this, Matrix.mul_smul]
  have key : Aᴴ * (h * Bm) * A = c • (h * Bm) := by
    rw [← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pb Bm A, hβB, Matrix.one_mul, hAiA, Matrix.mul_one]
  obtain ⟨x, hx⟩ : ∃ x : Fin G.n → ℂ, x ≠ 0 := ⟨Pi.single ⟨0, G.n_pos⟩ 1, by simp⟩
  have hAx : A *ᵥ x ≠ 0 := fun h0 => hx (by
    have := congrArg (Ai *ᵥ ·) h0
    simpa [Matrix.mulVec_mulVec, hAiA] using this)
  have e2 : star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x)) = c * (star x ⬝ᵥ ((h * Bm) *ᵥ x)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc] at key ⊢
    rw [key, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcr : c = ((s : ℝ) : ℂ) := by simp [c]
  have h1 := B.posR v x hx
  have h2 := B.posR v _ hAx
  change (_ → 0 < (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re) ∧ (_ → (star x ⬝ᵥ ((h * Bm) *ᵥ x)).re < 0) at h1
  change (_ → 0 < (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re) ∧
    (_ → (star (A *ᵥ x) ⬝ᵥ ((h * Bm) *ᵥ (A *ᵥ x))).re < 0) at h2
  rw [e2, hcr, Complex.re_ofReal_mul] at h2
  have hs : (0 : ℝ) < s := by
    by_cases hv : sigPosH (G.gram_herm v) = 1
    · have a1 := h1.1 hv
      have a2 := h2.1 hv
      by_contra hn
      push_neg at hn
      nlinarith
    · have a1 := h1.2 hv
      have a2 := h2.2 hv
      by_contra hn
      push_neg at hn
      nlinarith
  exact_mod_cast hs

end GlobalTheory.LKDef.DFormPos
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.Per

namespace GlobalTheory.CrysSubRep

variable {l : ℕ} [Fact l.Prime]

def entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) : FinExt l :=
  ⟨L.1 ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2),
    haveI := L.2
    haveI : FiniteDimensional ℚ_[l]
        (IntermediateField.adjoin ℚ_[l] (Set.range fun p : Fin d × Fin a => M p.1 p.2)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    IntermediateField.finiteDimensional_sup _ _⟩

theorem le_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) :
    L.1 ≤ (entExt L M).1 := le_sup_left

theorem mem_entExt (L : FinExt l) {d a : ℕ} (M : Matrix (Fin d) (Fin a) (Om l)) (i : Fin d) (j : Fin a) :
    M i j ∈ (entExt L M).1 :=
  (le_sup_right : IntermediateField.adjoin ℚ_[l] _ ≤ (entExt L M).1)
    (IntermediateField.subset_adjoin _ _ ⟨(i, j), rfl⟩)

theorem exists_leftInv {K : Type} [Field K] {d a : ℕ} (M : Matrix (Fin d) (Fin a) K)
    (h : Function.Injective M.mulVec) : ∃ N : Matrix (Fin a) (Fin d) K, N * M = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' M)
    (LinearMap.ker_eq_bot.2 (by rw [Matrix.toLin'_apply', Matrix.coe_mulVecLin]; exact h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem exists_model_of_mem {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (hL : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : Γ →* GL (Fin a) ↥L.1, Formalism.MainNotions.N.mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : Γ → Matrix (Fin a) (Fin a) ↥L.1 :=
    fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : Γ →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, MonoidHom.ext fun g => Units.ext (hM g)⟩

end GlobalTheory.CrysSubRep

namespace GlobalTheory.CrysSubRep

theorem isCrysAt_of_sub : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (d a : ℕ) (ρ : ↥(GK Bw.Kw) →* GL (Fin d) ℚ_[l])
    (r : ↥Gw →* GL (Fin a) (Om l)),
    IsCrys (P.PD Bw.Kw) (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp ((Units.coeHom _).comp ρ) : Representation ℚ_[l] ↥(GK Bw.Kw) (Fin d → ℚ_[l])) →
    ∀ M : Matrix (Fin d) (Fin a) (Om l), Function.Injective M.mulVec →
    (∀ g : ↥Gw, ((ρ (Bw.e g) : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) * M =
      M * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
    GlobalTheory.Pst.IsCrysAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw d a ρ r hρ M hM hint
  obtain ⟨T⟩ := hT
  let L : FinExt l := entExt Bw.LL M
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M' : Matrix (Fin d) (Fin a) ↥L.1 := Matrix.of fun i j => ⟨M i j, mem_entExt Bw.LL M i j⟩
  have hM' : M'.map f = M := Matrix.ext fun i j => rfl
  have hinjM' : Function.Injective M'.mulVec := by
    intro x y hxy
    have h1 : ∀ v : Fin a → ↥L.1, M.mulVec (fun i => f (v i)) = fun i => f (M'.mulVec v i) :=
      fun v => funext fun i => by rw [← hM']; exact (RingHom.map_mulVec f M' v i).symm
    have h2 := hM (show M.mulVec (fun i => f (x i)) = M.mulVec (fun i => f (y i)) by rw [h1, h1, hxy])
    exact funext fun i => f.injective (congrFun h2 i)
  obtain ⟨N, hN⟩ := exists_leftInv M' hinjM'
  let ρL : ↥(GK Bw.Kw) →* Matrix (Fin d) (Fin d) ↥L.1 :=
    (RingHom.mapMatrix (algebraMap ℚ_[l] ↥L.1)).toMonoidHom.comp ((Units.coeHom _).comp ρ)
  have hmapρ : ∀ g, ((ρ g : GL (Fin d) ℚ_[l]) : Matrix (Fin d) (Fin d) ℚ_[l]).map (algebraMap ℚ_[l] (Om l)) =
      (ρL g).map f := fun g => by
    simp only [ρL, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Units.coeHom_apply, Matrix.map_map]
    congr 1
  have hint' : ∀ g, (ρL (Bw.e g)).map f * M'.map f = M'.map f * (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hmapρ, hM']; exact hint g
  have hr : ∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)) = (N * ρL (Bw.e g) * M').map f := fun g => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, hint', ← Matrix.mul_assoc, ← Matrix.map_mul, hN,
      Matrix.map_one f (map_zero f) (map_one f), Matrix.one_mul]
  have hmem : ∀ g i j, (r g : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1 := fun g i j => by
    rw [hr g]; exact ((N * ρL (Bw.e g) * M') i j).2
  obtain ⟨r', hr'⟩ := exists_model_of_mem r L hmem
  have hmod : GlobalTheory.Pst.IsModel Bw r L r' := ⟨le_entExt Bw.LL M, hr'⟩
  have hr'g : ∀ g, ((r' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).map f =
      (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => by
    rw [← hr']; rfl
  have hinjMap : ∀ {m n : ℕ}, Function.Injective (fun X : Matrix (Fin m) (Fin n) ↥L.1 => X.map f) :=
    fun {m n} X Y h => Matrix.ext fun i j => f.injective (congrFun (congrFun h i) j)
  have hintL : ∀ g, ρL (Bw.e g) * M' = M' * (r' g : Matrix (Fin a) (Fin a) ↥L.1) := fun g =>
    hinjMap (by simp only [Matrix.map_mul]; rw [hr'g]; exact hint' g)
  haveI := L.2
  have hcL : IsCrys (P.PD Bw.Kw) (Formalism.MainNotions.N.matRep ρL) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD Bw.Kw) (fun g => ⟨(ρ g : Matrix (Fin d) (Fin d) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).2 hρ
  refine ⟨L, r', hmod, ?_⟩
  refine GlobalTheory.TateDualCrys.isCrys_of_isSubOfSums T Bw.Kw L (ι := Unit) (fun _ => ρL) (fun _ => hcL) (Fin a → ↥L.1)
    (Bw.repE L r') ⟨1, fun _ => (), LinearMap.pi (fun _ => Matrix.toLin' M'), fun x y h => hinjM' (congrFun h 0), ?_⟩
  intro g v
  funext i
  have e1 := hintL (Bw.e.symm g)
  rw [MulEquiv.apply_symm_apply] at e1
  show M'.mulVec ((r' (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥L.1).mulVec v) = (ρL g).mulVec (M'.mulVec v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]

end GlobalTheory.CrysSubRep
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelLoss

variable {D : D7} {L : SizeData₂ D}

theorem u_bound_off_top (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) (hl0 : ¬ (l.1 = 0 ∧ τ ∈ topsOf D.host D.eTau)) :
    |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 3 * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hb1 := GlobalTheory.HCEntries.b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hS : L.Sc ≤ L.sc.b := by linarith [GlobalTheory.HCEntries.b'_Sc_le hS, GlobalTheory.HCEntries.b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    have ha : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := fun ha =>
      hl0 ⟨rfl, by unfold topsOf; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
    have h1 := P.cloud_place_bound τ (by omega) ha
    push_cast at h1
    linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem N_le_b (h : SizesAt L) (P : ParameterChoice' D L) : 5 * (D.R.N D.R.m : ℝ) ≤ L.sc.b := by
  have h1 := (GlobalTheory.FockDegreeGap.errors_le h P).2.2
  have hk : (5 : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega : 5 ≤ D.R.k)
  have h0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  nlinarith

theorem true_entry_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (i : ℕ) (hi : i ≤ D.R.m) (a : Fin (D.R.N i)) (ha : ¬ (a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau)) :
    |((((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 5 * L.sc.b := by
  have hN := N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by positivity
  have s0 : (0 : ℝ) ≤ ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have s1 : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by
    have : i * (D.R.t + 1) / 2 ≤ D.R.m * (D.R.t + 1) :=
      (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ hi)
    exact_mod_cast this
  have e0 : ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = (((((D.fm u).lam i τ).w a : ℤ) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast]
  rw [Int.cast_sub, Int.cast_natCast, e0, (D.fm u).lam_eq i hi τ a]
  split_ifs with hk
  · have b := abs_le.1 (u_bound_off_top h P hx u τ ⟨a.1, hk⟩ ha)
    have a1 : (a.1 : ℝ) ≤ D.R.k := by exact_mod_cast hk.le
    have a0 : (0 : ℝ) ≤ a.1 := Nat.cast_nonneg _
    unfold hcToWeightQ rhoVec
    push_cast
    rw [abs_le]
    constructor <;> linarith [b.1, b.2, GlobalTheory.HCEntries.one_le_b L]
  · have hq := D.R.blk_lt hi a hk
    generalize_proofs
    obtain ⟨w0, w1⟩ := GlobalTheory.HCEntries.wj_bounds h hx ((a.1 - D.R.k) / (D.R.t + 1) + 1) (Nat.le_add_left _ _) hq τ
    rw [GlobalTheory.FockDegreeGap.wj_succ D _ hq] at w0 w1
    rw [D.hcW_e]
    have q1 : (((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast hq
    have q0 : (1 : ℝ) ≤ (((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    unfold wG
    generalize ((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) = q at q0 q1 ⊢
    have q2 : (q : ℝ) * (D.R.t + 1) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by gcongr
    have q3 : (1 : ℝ) * (D.R.t + 1) ≤ (q : ℝ) * (D.R.t + 1) := by gcongr
    push_cast
    rw [abs_le]
    constructor <;> linarith

theorem Wtau_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (Wtau D u τ : ℝ) ≤ 5 * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  rw [← Nat.le_floor_iff (by linarith)]
  unfold Wtau
  refine Finset.sup_le fun i hi => Finset.sup_le fun a _ => ?_
  split_ifs with ha
  · exact Nat.zero_le _
  · rw [Nat.le_floor_iff (by linarith), Nat.cast_natAbs, Int.cast_abs]
    exact true_entry_le h P hx u τ i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) a ha

end GlobalTheory.LevelLoss
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct


theorem _root_.GlobalTheory.T.cmTrace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := by
  first | exact @GlobalTheory.TraceAddStar.trace_eq_add_star | exact GlobalTheory.TraceAddStar.trace_eq_add_star | (intros; apply GlobalTheory.TraceAddStar.trace_eq_add_star <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct


theorem _root_.GlobalTheory.T.stdChar_finiteAdele_rational_eq_exp_trace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ q : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := by
  first | exact @GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap | exact GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap | (intros; apply GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetChar

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

section Alg

variable {R : Type} [CommRing R]

def cut (a : R) (ha : a * a = a) : Rˣ →* Rˣ where
  toFun u := ⟨a * u + (1 - a), a * (u⁻¹ : Rˣ) + (1 - a),
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv,
    by linear_combination ((u : R) * (u⁻¹ : Rˣ) - u - (u⁻¹ : Rˣ) + 1) * ha + a * u.mul_inv⟩
  map_one' := Units.ext (by simp)
  map_mul' u w := Units.ext (by
    show a * ((u : R) * w) + (1 - a) = (a * u + (1 - a)) * (a * w + (1 - a))
    linear_combination (-((u : R) * w) + u + w - 1) * ha)

theorem cut_val (a : R) (ha : a * a = a) (u : Rˣ) : (cut a ha u : R) = a * u + (1 - a) := rfl

theorem continuous_cut [TopologicalSpace R] [IsTopologicalRing R] (a : R) (ha : a * a = a) :
    Continuous (cut a ha) :=
  Units.continuous_iff.2 ⟨(continuous_const.mul Units.continuous_val).add continuous_const,
    (continuous_const.mul Units.continuous_coe_inv).add continuous_const⟩

theorem mul_det {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, a * (M - 1) i j = 0) :
    a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R a)
  have hI : ∀ x, x ∈ I ↔ x * a = 0 := fun x => Iff.rfl
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 ((hI _).2 ((mul_comm _ _).trans (h i j)))
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, det_one, map_one]
  have h3 := (hI _).1 (Ideal.Quotient.eq.1 h2)
  linear_combination h3

end Alg


theorem char_norm {D : D7} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n)
    (x y : (Formalism.L2.Theta.AE D)ˣ) (hy : (y : Formalism.L2.Theta.AE D) = x * cA D x) : χ y = 1 := by
  obtain ⟨⟨η, hη⟩, h⟩ := h
  have := D.host.isCMField_hostE
  have e : y = idF D (Units.map (Algebra.norm (AF D.host.F) : Formalism.L2.Theta.AE D →* AF D.host.F) x) :=
    Units.ext (hy.trans (GlobalTheory.Published.algebraMap_norm_tensor (E := D.host.E) (AF D.host.F)
      (x : Formalism.L2.Theta.AE D)).symm)
  rw [e, h η hη, hη.2.2.1, one_pow]


end GlobalTheory.SplitDetChar

end
end

section

open Matrix
open Formalism.REAL (inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin)
open scoped InnerProductSpace

namespace GlobalTheory.HdSmooth

theorem kFinite_smoothVec : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  intro n ε H _ _ _ _ σ hU hI v hv
  have hAnalytic :=
    CompanionTheory.D.gk.HC.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hU hI v hv
  have h := hAnalytic.smoothVec (P := 1) (G := Formalism.REAL.Jm ε) isUnit_one (by simp)
  simpa [inG] using h

end GlobalTheory.HdSmooth
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff : ∀ (D : D7) {n : ℕ} (γ B : GL (Fin n) D.host.E), ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (γ * B)) ↔
      (γ⁻¹).1.map (eToEAf D) *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) := by
  first | exact @GlobalTheory.LatMulAd.mem_hatL_colLat_mul | exact GlobalTheory.LatMulAd.mem_hatL_colLat_mul | (intros; apply GlobalTheory.LatMulAd.mem_hatL_colLat_mul <;> assumption)
end
