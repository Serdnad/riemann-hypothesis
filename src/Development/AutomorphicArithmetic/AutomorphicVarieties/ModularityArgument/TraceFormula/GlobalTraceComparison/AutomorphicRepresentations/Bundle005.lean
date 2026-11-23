module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle020
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory

private theorem twist_general {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (fd : IsFundamentalDomain Γ F μ) (θ : G →* G) (hc : Continuous θ) (hi : ∀ x, θ (θ x) = x)
    (hΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) (hf : ∀ (γ : Γ) x, f ((γ : G) * x) = f x)
    (hI : Integrable f (μ.restrict F)) :
    Integrable (fun x => f (θ x)) (μ.restrict F) ∧
      ∫ x, f (θ x) ∂(μ.restrict F) = ∫ x, f x ∂(μ.restrict F) :=
  _root_.UpperTheory.Reformulated.B.Qh1.twist_general μ Γ fd θ hc hi hΓ f hf hI

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.thetaInt_pf :
    Basic → ThetaInt := by
  intro _ E _ _ _ n D f hf hI
  have hb := PositivityTheory.Rg.BcB.E1.thetaBasic_holds E
  let θ : PositivityTheory.Rg.BcB.E.H E n 0 →* PositivityTheory.Rg.BcB.E.H E n 0 :=
    (PositivityTheory.Rg.BcB.thetaA E n).prodMap (PositivityTheory.Rg.BcB.thetaA E 0)
  have hc : Continuous θ :=
    ((hb n).1.comp continuous_fst).prodMk ((hb 0).1.comp continuous_snd)
  have hi : ∀ x, θ (θ x) = x := fun x => Prod.ext ((hb n).2.1 x.1) ((hb 0).2.1 x.2)
  have hΓ : ∀ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0, θ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0 := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(PositivityTheory.Rg.BcB.thetaE E n g.1, PositivityTheory.Rg.BcB.thetaE E 0 g.2),
      Prod.ext ((hb n).2.2 g.1).symm ((hb 0).2.2 g.2).symm⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E 0
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E n).2.1
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E 0).2.1
  letI := PositivityTheory.Rg.BcB.E.borelH E n 0
  haveI : BorelSpace (PositivityTheory.Rg.BcB.E.H E n 0) := ⟨rfl⟩
  haveI : D.μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2
      toIsMulLeftInvariant := D.haar.1
      toIsOpenPosMeasure := D.haar.2.2.1 }
  haveI : Countable (PositivityTheory.Rg.BcB.E.ratH E n 0) :=
    (((GlobalTheory.CuspRep.ratGL E n).prodMap (GlobalTheory.CuspRep.ratGL E 0)).rangeRestrict_surjective).countable
  exact twist_general D.μ _ D.fd θ hc hi hΓ f hf hI
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem row_int (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) (w : Lp ℂ 2 D.ν) (x : H E n 0) :
    Integrable (fun y => kerH φ x y * (w : H E n 0 → ℂ) y) D.ν :=
  by
    let X : Ctx := by
      haveI := CuspidalL2GL.t2Space_GA E n
      haveI := CuspidalL2GL.t2Space_GA E 0
      haveI := CuspidalL2GL.locallyCompactSpace_GA E n
      haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
      haveI := CuspidalL2GL.secondCountableTopology_GA E n
      haveI := CuspidalL2GL.secondCountableTopology_GA E 0
      haveI := (ratProper_holds E n).2.1
      haveI := (ratProper_holds E 0).2.1
      refine { G := H E n 0
               ms := borelH E n 0
               bs := ⟨rfl⟩
               μ := D.μ
               haar := { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2, toIsMulLeftInvariant := D.haar.1, toIsOpenPosMeasure := D.haar.2.2.1 }
               Γ := ratH E n 0
               cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
               proper := ?_
               F := D.F
               fd := D.fd }
      intro C hC
      have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
      have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
      refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
      rintro ⟨_, γ, rfl⟩ hγ
      exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
    exact MemLp.integrable_mul ((kernel_rows_columns_square_integrable X φ hφ).2 x) (Lp.memLp w)

private theorem ker_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ)
    (x y : H E n 0) : kerH (trM Φ M) x y = ∑ i, ∑ j, kerH (Φ i j) x y * M j i := by
  let X : Ctx := by
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (ratProper_holds E n).2.1
    haveI := (ratProper_holds E 0).2.1
    refine { G := H E n 0
             ms := borelH E n 0
             bs := ⟨rfl⟩
             μ := D.μ
             haar := { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2, toIsMulLeftInvariant := D.haar.1, toIsOpenPosMeasure := D.haar.2.2.1 }
             Γ := ratH E n 0
             cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
             proper := ?_
             F := D.F
             fd := D.fd }
    intro C hC
    have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
    have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
    refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
    rintro ⟨_, γ, rfl⟩ hγ
    exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
  have h := (kerLin X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).2 x y
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  refine Eq.trans h ?_
  exact Fintype.sum_prod_type _

private theorem part_eq {D : Dom E n 0} {π : CuspSub E n} {U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsPiPart D π U Uπ) (f : Hs (ι := ι) D) : Uπ f = U ((piSp D π ι).starProjection f) := by
  have h1 : Uπ ((piSp D π ι).starProjection f) = U ((piSp D π ι).starProjection f) :=
    h.1 _ (Submodule.starProjection_apply_mem _ _)
  have h2 : Uπ (f - (piSp D π ι).starProjection f) = 0 :=
    h.2 _ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [map_sub, sub_eq_zero] at h2
  rw [h2, h1]

private theorem vec_int {D : Dom E n 0} (w : Lp ℂ 2 D.ν) (c : ι → ℂ) (j : ι) {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    (x : H E n 0) :
    ∫ y, kerH φ x y * ((vecM w c) j : H E n 0 → ℂ) y ∂D.ν = c j * ∫ y, kerH φ x y * (w : H E n 0 → ℂ) y ∂D.ν := by
  have e : ((vecM w c) j : H E n 0 → ℂ) =ᵐ[D.ν] fun y => c j * (w : H E n 0 → ℂ) y := by
    have : (vecM w c) j = c j • w := rfl
    rw [this]
    filter_upwards [Lp.coeFn_smul (c j) w] with y hy
    simpa using hy
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [e] with y hy
  rw [hy]; ring

end SlopeTestRemainingChoices

theorem ker_pf :
    Weak → PointRep → PComm → PDiag → Ker := by
  intro hW hPR hPC hPD E _ _ _ n ι _ s m v x
  set w := P0 s.D s.π v with hw
  let u : ι → Hs (ι := ι) s.D := fun i => ContinuousLinearMap.adjoint m.Uπ (s.k₁ x i)
  have hG : ∀ y, (v : H E n 0 → ℂ) y * m.G x (th y) =
      ∑ i, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) := by
    intro y
    simp only [Mid.G, Gk, Finset.mul_sum, u, ContinuousLinearMap.adjoint_inner_left]
  have hI : ∀ i, Integrable (fun y => (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i)) s.D.ν :=
    fun i => (hW E n ι s v (u i) i).1
  have hterm : ∀ i, ∫ y, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) ∂s.D.ν =
      ∑ j, s.M j i * ∫ y, kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y ∂s.D.ν := by
    intro i
    rw [(hW E n ι s v (u i) i).2]
    have e1 : inner ℂ (u i) (s.T₂ (vecM v fun l => s.M l i)) =
        inner ℂ (s.k₁ x i) (m.U (s.T₂ (vecM w fun l => s.M l i))) := by
      simp only [u, ContinuousLinearMap.adjoint_inner_left]
      rw [part_eq m.pp, hPC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂, hPD E n s.D s.π ι]
    rw [e1, hPR E n ι s m.Φ (s.T₁ * m.U * s.T₂) m.t m.o (m.U (s.T₂ (vecM w fun l => s.M l i)))
      (vecM w fun l => s.M l i) rfl x i]
    exact Finset.sum_congr rfl fun j _ => vec_int w _ j (m.t i j) x
  refine ⟨?_, ?_⟩
  · simp only [hG]
    exact integrable_finsetSum _ fun i _ => hI i
  · simp only [hG]
    rw [integral_finsetSum _ fun i _ => hI i]
    simp only [hterm]
    have e2 : ∀ y, kerH m.φ x y * (w : H E n 0 → ℂ) y =
        ∑ i, ∑ j, s.M j i * (kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) := by
      intro y
      rw [Mid.φ, ker_trM s.D m.t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    have hr : ∀ i j, Integrable (fun y => kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) s.D.ν :=
      fun i j => row_int s.D (m.t i j) w x
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hr i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hr i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open NumberField PositivityTheory.Rg.BcB.E MeasureTheory

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ker_left (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ (γ * x) y = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).1

private theorem ker_right (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ x (γ * y) = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).2

private theorem th_mul' (x y : H E n 0) :
    PositivityTheory.Rg.BcB.E1.th (x * y) = PositivityTheory.Rg.BcB.E1.th x * PositivityTheory.Rg.BcB.E1.th y :=
  Prod.ext (map_mul (PositivityTheory.Rg.BcB.thetaA E n) x.1 y.1) (map_mul (PositivityTheory.Rg.BcB.thetaA E 0) x.2 y.2)

private theorem th_rat {δ : H E n 0} (hδ : δ ∈ ratH E n 0) : PositivityTheory.Rg.BcB.E1.th δ ∈ ratH E n 0 := by
  obtain ⟨γ, rfl⟩ := hδ
  refine ⟨(PositivityTheory.Rg.BcB.thetaE E n γ.1, PositivityTheory.Rg.BcB.thetaE E 0 γ.2), ?_⟩
  exact Prod.ext ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).2.2 γ.1).symm
    ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E 0).2.2 γ.2).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.kInv_pf :
    KInv := by
  intro E _ _ _ n ι _ s
  refine ⟨fun γ x => ?_, fun γ x => ?_⟩
  · funext i
    refine ext_inner_right ℂ fun u => ?_
    rw [s.vecs.rep₁, s.vecs.rep₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ker_left s.D (s.t₁ i j) γ.2]
  · funext i
    refine ext_inner_left ℂ fun u => ?_
    rw [s.vecs.rep₂, s.vecs.rep₂]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [th_mul', ker_right s.D (s.t₂ j l) (th_rat γ.2)]
end
