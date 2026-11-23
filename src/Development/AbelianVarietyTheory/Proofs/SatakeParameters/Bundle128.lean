module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle120
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImage
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Mathlib.Algebra.Module.Submodule.Union
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle122
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle121
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehomA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets

def SplitSet {X : Fields} (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AA ≠ ⊥ ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧ IsCoprime ϖ (X.conjO ϖ) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P ∈ S

def TranslateInt {X : Fields} (A : Amb X) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (π : X.E) (κ : ℂ) (e : DVar X.Tau a b →₀ ℕ) : Prop :=
  ∀ (s : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * π) • s ∈ per A N N' →
    GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (κ * jetC A.cD (Wx A s (A.e a b N N')) e)

def PlaceAbove : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)),
    (p : 𝓞 K) ∈ w.asIdeal →
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k : K, GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt lam (σ k) ↔ w.valuation K k ≤ 1

def TypePrimeBadPrimesLevelsHypotheses : Prop :=
  ∀ (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ)
    (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), HostTie EX → IsSel (recFields D) sel →
    ∀ (i : Fin 2) (u : (recPrimes EX).Word) (mu : Tup (recFields D).F (recFields D).E (recFields D).K (badS D))
      (cst : LocCst (recFields D) (rowSG (recPrimes EX) sel mu)), cst.Ok →
    ∀ a b : ℕ, (ambOf (recSeam D) B χ cD).LaHyp a b ∅ → (ambOf (recSeam D) B χ cD).ESmooth a b →
      SplitSet (ambOf (recSeam D) B χ cD) a b (Sall sel mu u) ((recFields D).conjO ((recPrimes EX).piG i))
        ((recPrimes EX).g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ (recPrimes EX).g i ∣ cBof sel mu cst u

end GlobalTheory.DatumJets
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory NumberField IsDedekindDomain

namespace GlobalTheory.DetFields

open GlobalTheory.Mem.Col2.JetEx.VacEqPf

theorem iE_det {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (γ : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    s.iE ((LinearEquiv.det γ : X.Eˣ) : X.E) = (matOf s γ).det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix']
  rw [show s.iE (LinearMap.toMatrix' (γ : Sp X.E n →ₗ[X.E] Sp X.E n)).det = _ from
    RingHom.map_det (s.iE : X.E →+* D.host.E) _]
  congr 1

theorem det_of_stab : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ), s.Ok → TaylorLogMetric.IsChi D χ → ∀ (n : ℕ) (N' : Submodule (𝓞 X.E) (Sp X.E n)), IsSDLat D.host.E n (s.lat N') → ∀ γ : UF X.E n, gmap γ.1 N' = N' → ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) * star ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 ∧ IsIntegral ℤ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ∧ ∏ τ, TaylorLogMetric.embT D τ (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) = 1 := by
  intro D X s χ hok hχ n N' hL γ hγ
  have hd := iE_det s γ.1
  have hSD : Formalism.MainNotions.StandardLatticesGL3.SD D (s.lat N') := hL
  have hfg : (s.lat N').FG := hL.1
  have hsp : Submodule.span D.host.E ((s.lat N' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = ⊤ := hL.2.1
  have hU := matOf_unitary s hok γ
  set M := matOf s γ.1 with hM

  have hMM : GlobalTheory.RatEqui.adj D M * M = 1 ∧ M * GlobalTheory.RatEqui.adj D M = 1 := by
    letI := D.host.cmStar
    have e : star M = GlobalTheory.RatEqui.adj D M := by
      ext i j
      simp [GlobalTheory.RatEqui.adj, Matrix.star_apply, star_conj]
    rw [← e]
    exact ⟨Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU⟩
  have hadj : M * GlobalTheory.RatEqui.adj D M = 1 := hMM.2

  have hs : ∀ v, v ∈ s.lat N' ↔ M.mulVec v ∈ s.lat N' := by
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := (mem_lat s N' v).1 hv
      refine (mem_lat s N' _).2 ⟨γ.1 x, ?_, (matOf_mulVec s γ.1 x).symm⟩
      rw [← hγ]
      exact ⟨x, hx, rfl⟩
    · intro hv
      obtain ⟨y, hy, hyv⟩ := (mem_lat s N' _).1 hv
      rw [← hγ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      have hx' : M.mulVec (vec s x) = M.mulVec v := by
        rw [← hyv]
        exact matOf_mulVec s γ.1 x
      have hinj : vec s x = v := by
        have := congrArg (fun w => (GlobalTheory.RatEqui.adj D M).mulVec w) hx'
        simpa only [Matrix.mulVec_mulVec, hMM.1, Matrix.one_mulVec] using this
      rw [← hinj]
      exact (mem_lat s N' _).2 ⟨x, hx, rfl⟩

  have hdet : M.det * D.host.conj M.det = 1 := by
    have h1 : (GlobalTheory.RatEqui.adj D M).det = D.host.conj M.det := by
      unfold GlobalTheory.RatEqui.adj
      rw [Matrix.det_transpose]
      exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm
    rw [← h1, ← Matrix.det_mul, hMM.2, Matrix.det_one]
  refine ⟨?_, ?_, ?_⟩
  · apply s.iE.injective
    rw [map_mul, hok.2, hd, map_one]
    exact hdet
  · have i1 := GlobalTheory.DetStab.isIntegral_det_of_stable (s.lat N') hfg hsp M fun v hv => (hs v).1 hv
    have i2 : IsIntegral ℤ M.det := isIntegral_trans (R := ℤ) _ i1
    have i3 := map_isIntegral_int s.iE.symm.toRingHom i2
    rw [← hd] at i3
    simpa using i3
  · rw [hd]
    exact GlobalTheory.DetStab.prod_emb_det_eq_one D χ hχ n (s.lat N') hSD M hadj hs

end GlobalTheory.DetFields
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TameIwahori.JacquetNonzero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_mk_ne_zero (hp : GlobalTheory.Published.DepthZeroJacquetInjective)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (π : Irr k n) (v : π.V) (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : IsIwVec θ π.π v) :
    (Submodule.Quotient.mk v : Jacquet π.π (unipB k (Fin n))) ≠ 0 := by
  first
  | exact @_root_.GlobalTheory.PointStabilizer.mk_ne_zero
  | exact _root_.GlobalTheory.PointStabilizer.mk_ne_zero
  | (apply _root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PointStabilizer.mk_ne_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PointStabilizer.mk_ne_zero ..)

end GlobalTheory.TameIwahori.JacquetNonzero
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  first | exact @GlobalTheory.TwU.map_mem_homLat_of_mem_YYl | exact GlobalTheory.TwU.map_mem_homLat_of_mem_YYl | (intros; apply GlobalTheory.TwU.map_mem_homLat_of_mem_YYl <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.matrixHomLattice_le_span_ideal_hom_image : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (hN : N.FG) (hN' : N'.FG) (hsN : Submodule.span D.host.E (N : Set (Fin k → D.host.E)) = ⊤) (hsN' : Submodule.span D.host.E (N' : Set (Fin k' → D.host.E)) = ⊤) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) D.host.E => A.map ρ) '' (TaylorLogMetric.YYl D N N' : Set (Matrix (Fin k') (Fin k) D.host.E))) := by
  first | exact @GlobalTheory.VolOnto.homLat_le_span_YYl | exact GlobalTheory.VolOnto.homLat_le_span_YYl | (intros; apply GlobalTheory.VolOnto.homLat_le_span_YYl <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

theorem exists_linear_mod_sq {A : Type} [CommRing A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → A) (hr : Algebra.adjoin ℂ (Set.range r) = ⊤) (e : A →+* ℂ)
    (he : ∀ c : ℂ, e (algebraMap ℂ A c) = c) (a : A) (ha : e a = 0) :
    ∃ c : ι → ℂ, a - ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) ∈ RingHom.ker e ^ 2 := by
  have hK : ∀ x : A, x - algebraMap ℂ A (e x) ∈ RingHom.ker e := fun x => by
    rw [RingHom.mem_ker, map_sub, he, sub_self]
  have hP : ∀ x, ∃ c : ι → ℂ,
      x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) ∈ RingHom.ker e ^ 2 := by
    intro x
    have hx : x ∈ Algebra.adjoin ℂ (Set.range r) := hr ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      refine ⟨Pi.single l 1, ?_⟩
      have hs : ∑ l', (Pi.single l 1 : ι → ℂ) l' • (r l' - algebraMap ℂ A (e (r l'))) =
          r l - algebraMap ℂ A (e (r l)) := by
        rw [Finset.sum_eq_single l]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      rw [hs, sub_self]
      exact zero_mem _
    | algebraMap c =>
      refine ⟨0, ?_⟩
      simp [he]
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨c + d, ?_⟩
      have h : x + y - algebraMap ℂ A (e (x + y)) - ∑ l, (c + d) l • (r l - algebraMap ℂ A (e (r l))) =
          (x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l)))) +
          (y - algebraMap ℂ A (e y) - ∑ l, d l • (r l - algebraMap ℂ A (e (r l)))) := by
        simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
        ring
      rw [h]
      exact add_mem hc hd
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨e x • d + e y • c, ?_⟩
      have h : x * y - algebraMap ℂ A (e (x * y)) -
            ∑ l, (e x • d + e y • c) l • (r l - algebraMap ℂ A (e (r l))) =
          algebraMap ℂ A (e x) * (y - algebraMap ℂ A (e y) - ∑ l, d l • (r l - algebraMap ℂ A (e (r l)))) +
          algebraMap ℂ A (e y) * (x - algebraMap ℂ A (e x) - ∑ l, c l • (r l - algebraMap ℂ A (e (r l)))) +
          (x - algebraMap ℂ A (e x)) * (y - algebraMap ℂ A (e y)) := by
        have hsum : ∑ l, (e x • d + e y • c) l • (r l - algebraMap ℂ A (e (r l))) =
            e x • ∑ l, d l • (r l - algebraMap ℂ A (e (r l))) +
              e y • ∑ l, c l • (r l - algebraMap ℂ A (e (r l))) := by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, add_smul, smul_eq_mul, smul_eq_mul, mul_smul,
            mul_smul]
        rw [hsum, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
        ring
      have hxy : (x - algebraMap ℂ A (e x)) * (y - algebraMap ℂ A (e y)) ∈ RingHom.ker e ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hK x) (hK y)
      rw [h]
      exact add_mem (add_mem (Ideal.mul_mem_left _ _ hd) (Ideal.mul_mem_left _ _ hc)) hxy
  obtain ⟨c, hc⟩ := hP a
  rw [ha, map_zero, sub_zero] at hc
  exact ⟨c, hc⟩

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem algebraMap_basicOpen {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) (c : ℂ) :
    algebraMap ℂ Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g) c =
      (Proj.awayToSection (grading ℂ N) g).hom
        (HomogeneousLocalization.fromZeroRingHom (grading ℂ N) _ (algebraMap ℂ (grading ℂ N 0) c)) := by
  have h := GlobalTheory.QCoh.Qcqs.baseRingHom_comp_SpecMap (Proj.toSpecZero (grading ℂ N))
    (CommRingCat.ofHom (algebraMap ℂ (grading ℂ N 0))) (Proj.basicOpen (grading ℂ N) g)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading ℂ N) hg one_pos
  rw [GlobalTheory.QCoh.Qcqs.baseRingHom.eq_1 (Proj.toSpecZero _), h'] at h
  exact congrArg (fun φ => φ.hom c) h

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem frac_eq_aeval {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) ℂ) (hf : f ∈ grading ℂ N (n • 1)) :
    frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) f (g ^ n) hf (SetLike.pow_mem_graded n hg)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) =
      MvPolynomial.aeval (fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) (MvPolynomial.X l) g
        (X_mem ℂ N l) hg le_rfl) f := by
  refine ext fun x hx => ?_
  let t : Localization.AtPrime x.asHomogeneousIdeal.toIdeal := Localization.mk 1 ⟨g, hx⟩
  have hC : (ev (grading ℂ N) _ x hx).comp (algebraMap ℂ Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g)) =
      (algebraMap (MvPolynomial (Fin (N + 1)) ℂ) _).comp MvPolynomial.C := by
    ext c
    simp only [RingHom.comp_apply]
    rw [algebraMap_basicOpen hg, awayToSection_fromZero, ev_frac, ← Localization.mk_one_eq_algebraMap]
    rfl
  have hX : ∀ l, ev (grading ℂ N) _ x hx (frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g) (MvPolynomial.X l) g
        (X_mem ℂ N l) hg le_rfl) = algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l) * t := by
    intro l
    rw [ev_frac, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    congr 1
    · simp
    · ext1; simp
  have hf' : f.IsHomogeneous n := by simpa using hf
  erw [ev_frac]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, hC]
  have hfun : (ev (grading ℂ N) _ x hx ∘ fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl) =
      fun l => algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l) * t := funext hX
  rw [hfun, ReciprocityTheory.AnForm.R.eval₂_mul_const_of_isHomogeneous _ _ _ hf']
  have h3 : MvPolynomial.eval₂ ((algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)).comp MvPolynomial.C)
      (fun l => algebraMap (MvPolynomial (Fin (N + 1)) ℂ) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (MvPolynomial.X l)) f = algebraMap _ _ f := by
    have := MvPolynomial.eval₂_comp_left (algebraMap (MvPolynomial (Fin (N + 1)) ℂ)
      (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)) MvPolynomial.C MvPolynomial.X f
    rw [MvPolynomial.eval₂_eta] at this
    exact this.symm
  rw [h3, Localization.mk_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  · simp
  · ext1; simp

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

open GlobalTheory.ProjSpace GlobalTheory.ProjFrac

variable {N : ℕ}

theorem mem_adjoin_frac {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1)
    (s : Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g)) :
    s ∈ Algebra.adjoin ℂ (Set.range fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl) := by
  obtain ⟨y, rfl⟩ := (Proj.basicOpenIsoAway (grading ℂ N) g hg one_pos).commRingCatIsoToRingEquiv.surjective s
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hg y
  change (Proj.awayToSection (grading ℂ N) g).hom _ ∈ _
  rw [awayToSection_mk, frac_eq_aeval hg n f hf, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨f, rfl⟩

theorem adjoin_fRatio_eq_top {S : Scheme.{0}} (p : S ⟶ Sp ℂ) (ι : S ⟶ PSpace ℂ N) [IsClosedImmersion ι]
    (hp : ι ≫ PSpace.str ℂ N = p) {g : MvPolynomial (Fin (N + 1)) ℂ} (hg : g ∈ grading ℂ N 1) :
    Algebra.adjoin (A := Sec p (fOpen ι g)) ℂ
      (Set.range fun l => fRatio ι (MvPolynomial.X l) g (X_mem ℂ N l) hg) = ⊤ := by
  subst hp
  let ψ : Γ(PSpace ℂ N, Proj.basicOpen (grading ℂ N) g) →ₐ[ℂ] Sec (ι ≫ PSpace.str ℂ N) (fOpen ι g) :=
    { (ι.app (Proj.basicOpen (grading ℂ N) g)).hom with
      commutes' := fun c => GlobalTheory.QCoh.Qcqs.app_baseRingHom ι (PSpace.str ℂ N) _ c }
  have hsurj : Function.Surjective ψ :=
    ι.app_surjective _ (Proj.isAffineOpen_basicOpen (grading ℂ N) g hg one_pos)
  rw [eq_top_iff]
  intro a _
  obtain ⟨s, rfl⟩ := hsurj a
  have h1 : ψ s ∈ (Algebra.adjoin ℂ (Set.range fun l => frac (grading ℂ N) (Proj.basicOpen (grading ℂ N) g)
      (MvPolynomial.X l) g (X_mem ℂ N l) hg le_rfl)).map ψ := Subalgebra.mem_map.2 ⟨s, mem_adjoin_frac hg s, rfl⟩
  rw [AlgHom.map_adjoin, ← Set.range_comp] at h1
  exact h1

end GlobalTheory.EtProj.RatSpan

namespace GlobalTheory.EtProj.RatSpan

theorem ratio_span_cotangent : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N), IsClosedImmersion ι → ι ≫ PSpace.str ℂ N = p → ∀ (g : MvPolynomial (Fin (N + 1)) ℂ) (hg : g ∈ GlobalTheory.ProjSpace.grading ℂ N 1) (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι g)), let U := GlobalTheory.EtProj.fOpen ι g; let r : Fin (N + 1) → Sec p U := fun l => GlobalTheory.EtProj.fRatio ι (MvPolynomial.X l) g (GlobalTheory.ProjSpace.X_mem ℂ N l) hg; let e : Sec p U →+* ℂ := CxPts.evHom hy; ∀ a : Sec p U, e a = 0 → ∃ c : Fin (N + 1) → ℂ, a - ∑ l, c l • (r l - algebraMap ℂ (Sec p U) (e (r l))) ∈ RingHom.ker e ^ 2 := by
  intro X p N ι hι hp g hg y hy U r e a ha
  have hr : Algebra.adjoin ℂ (Set.range r) = ⊤ := adjoin_fRatio_eq_top p ι hp hg
  have he : ∀ c : ℂ, e (algebraMap ℂ (Sec p U) c) = c := fun c =>
    (CxPts.ev_eq hy _).symm.trans (CxPts.ev_algX hy c)
  exact exists_linear_mod_sq r hr e he a ha

end GlobalTheory.EtProj.RatSpan
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem exists_form_forall_notMem (N n : ℕ) (T : Finset (PSpace ℂ N)) :
    ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n, ∀ x ∈ T, f ∉ x.asHomogeneousIdeal := by
  classical
  let V : T → Submodule ℂ (GlobalTheory.ProjSpace.grading ℂ N 1) := fun x =>
    ((x.1.asHomogeneousIdeal.toIdeal).restrictScalars ℂ).comap (GlobalTheory.ProjSpace.grading ℂ N 1).subtype
  have hV : ∀ x, V x ≠ ⊤ := by
    intro x h
    obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℂ N x.1
    have hX : (⟨MvPolynomial.X i, GlobalTheory.ProjSpace.X_mem ℂ N i⟩ : GlobalTheory.ProjSpace.grading ℂ N 1) ∈ V x :=
      h ▸ Submodule.mem_top
    exact (Proj.mem_basicOpen _ _ _).1 hi hX
  obtain ⟨ℓ, hℓ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top V hV
  have hpow : ℓ.1 ^ n ∈ GlobalTheory.ProjSpace.grading ℂ N n := by
    simpa using SetLike.pow_mem_graded n ℓ.2
  refine ⟨ℓ.1 ^ n, hpow, fun x hx hmem => hℓ ⟨x, hx⟩ ?_⟩
  exact x.isPrime.mem_of_pow_mem n hmem

theorem exists_form_genericPoint_cxPts : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (N : ℕ)
    (ι : X ⟶ PSpace ℂ N) (n : ℕ) (F : Finset (CxPts p (RingHom.id ℂ))), ∃ f ∈ GlobalTheory.ProjSpace.grading ℂ N n,
      genericPoint X ∈ GlobalTheory.EtProj.fOpen ι f ∧ ∀ z ∈ F, z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι f) := by
  intro X _ p N ι n F
  classical
  obtain ⟨f, hf, hT⟩ := exists_form_forall_notMem N n
    (insert (ι.base (genericPoint X)) (F.image fun z => ι.base (z.1 (IsLocalRing.closedPoint ℂ))))
  refine ⟨f, hf, hT _ (Finset.mem_insert_self _ _), fun z hz => ?_⟩
  exact CxPts.mem_ptsIn.2 (hT _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.EtProj
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dual_local_bases_pair_dual_mod_root_minus_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  first | exact @GlobalTheory.DFrame.dual_local_bases_pair | exact GlobalTheory.DFrame.dual_local_bases_pair | (intros; apply GlobalTheory.DFrame.dual_local_bases_pair <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.dualFrame_paired_blocks_diagonal_mod_root : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (X : Fields) (s : Seam D X) (L : PeriodPair) (sc : ℝ) (n : Bool × HH D → ℕ) (N N' : ℕ) (a : ∀ z, Fin (n z) → D.host.E) (cκ : Bool × HH D → ℂ_[p]) (r : ∀ z, Fin (n z) → ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (σ σ' : Bool × HH D → 𝓞 D.host.E) (th : ℂ_[p]), ‖th‖ ≤ 1 → (∀ A B : Matrix (Fin N') (Fin N) D.host.E, ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s A) (GlobalTheory.DFrame.vecF D s B)) = ∑ z : Bool × HH D, GlobalTheory.DFrame.rho D ι z (∑ i, ∑ k, A i k * D.host.conj (B i k))) → (∀ τ ρ : Bool × HH D, ρ ≠ τ → ∀ α' : (Σ z : Bool × HH D, Fin (n z)), ∑ α, GlobalTheory.DFrame.gc D cκ r τ α * GlobalTheory.DFrame.rho D ι ρ (a α.1 α.2 * D.host.conj (a α'.1 α'.2)) = 0) → (∀ t, ‖GlobalTheory.DFrame.uu D ι cκ r a t‖ ≤ 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) → (∀ (t : HH D) (b₁ b₂ : Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ' (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P' σ' r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P' σ' r₂ i)) * GlobalTheory.DFrame.pc D ι σ' (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) → ∀ (t : HH D) (ab ab' : Fin N × Fin N'), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ j, ∑ k, GlobalTheory.DFrame.coef D ι cκ r σ σ' j ((false, t), ab) * ι (Formalism.L2.Th1.GD.hOK L (Formalism.L2.AlgTh.hSc X.Tau N N' sc) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' j)) (GlobalTheory.DFrame.vecF D s (GlobalTheory.DFrame.mat D a P P' σ σ' k))) * GlobalTheory.DFrame.coef D ι cκ r σ σ' k ((true, t), ab') = (if ab = ab' then GlobalTheory.DFrame.uu D ι cκ r a t else 0) + th * e := by
  first | exact @GlobalTheory.DFrame.pairedBlock_diag | exact GlobalTheory.DFrame.pairedBlock_diag | (intros; apply GlobalTheory.DFrame.pairedBlock_diag <;> assumption)
end
