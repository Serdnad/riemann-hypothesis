module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle004
import Formalism.LocalRingCardinality.DataHost
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

variable {F : Type} [Field F] [NumberField F]

theorem fst_eq (x : AF F) : fstA F x = x.1 := rfl
theorem snd_eq (x : AF F) : sndA F x = x.2 := rfl

theorem idF_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε.1 = 1 := hε.1

open Classical in
theorem idF_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) (v : HeightOneSpectrum (𝓞 F)) :
    ε.2 v = if v ∈ S then 1 else 0 := hε.2 v

theorem idF_mul {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε * ε = ε := by
  classical
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · change ε.1 * ε.1 = ε.1
    rw [idF_fst hε, one_mul]
  · change ε.2 v * ε.2 v = ε.2 v
    rw [idF_snd hε v]
    split_ifs <;> simp

theorem ker_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0) :
    y.1 = 0 := by
  have h : (ε * y).1 = 0 := by rw [hy]; rfl
  change ε.1 * y.1 = 0 at h
  rwa [idF_fst hε, one_mul] at h

theorem ker_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : y.2 v = 0 := by
  classical
  have h : (ε * y).2 v = 0 := by rw [hy]; rfl
  change ε.2 v * y.2 v = 0 at h
  rwa [idF_snd hε v, if_pos hv, one_mul] at h

theorem fix_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {h : AF F} (hh : ε * h = h)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : h.2 v = 0 := by
  classical
  have h' : (ε * h).2 v = h.2 v := by rw [hh]
  change ε.2 v * h.2 v = h.2 v at h'
  rw [idF_snd hε v, if_neg hv, zero_mul] at h'
  exact h'.symm

theorem fix_mul_ker {ε h y : AF F} (hε : ε * ε = ε) (hh : ε * h = h) (hy : ε * y = 0) : h * y = 0 := by
  calc h * y = (ε * h) * y := by rw [hh]
    _ = h * (ε * y) := by ring
    _ = 0 := by rw [hy, mul_zero]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMuId

variable {D : D7} {a b r t n : ℕ}

scoped instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩
scoped instance scMx (m n : ℕ) : SecondCountableTopology (Mx D m n) := (GlobalTheory.MixModel.lattice_Mx D m n).2.2.1

theorem fromCols_smul_apply (e : AE D) (x : Mx D a r) (v : Mx D a t) (i : Fin a) :
    ∀ k, Matrix.fromCols (e • x) (e • v) i k = e • Matrix.fromCols x v i k := by
  rintro (k | k) <;> rfl

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) : jn hn (e • x) (e • v) = e • jn hn x v := by
  ext i j
  exact fromCols_smul_apply e x v i _

theorem jn_inl (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (k : Fin r) :
    jn hn x v i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl k)) = x i k := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromCols_apply_inl]

theorem jn_inr (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (k : Fin t) :
    jn hn x v i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr k)) = v i k := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply, Matrix.fromCols_apply_inr]

theorem intOff_jn (S : Finset (Pl D)) (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i k => ?_, fun w hw i k => ?_⟩
    · simpa only [jn_inl] using h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl k))
    · simpa only [jn_inr] using h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr k))
  · rintro ⟨hx, hv⟩ w hw i j
    obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
    rcases k with k | k
    · rw [jn_inl]; exact hx w hw i k
    · rw [jn_inr]; exact hv w hw i k

theorem good_pos {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (h : Good S e Φ) {x : Mx D a b} (hx : IntOff S x) :
    Φ x = Φ (e • x) := by
  rw [h x, if_pos hx]

theorem good_neg {S : Finset (Pl D)} {e : AE D} {Φ : Mx D a b → ℂ} (h : Good S e Φ) {x : Mx D a b} (hx : ¬ IntOff S x) :
    Φ x = 0 := by
  rw [h x, if_neg hx]

theorem continuous_jn (hn : r + t = n) : Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  have h : Continuous fun z : Mx D a r × Mx D a t => Matrix.fromCols z.1 z.2 := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    rcases k with k | k
    · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
    · exact (continuous_apply k).comp ((continuous_apply i).comp continuous_snd)
  exact h.matrix_submatrix _ _

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) : Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z :=
  continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd))

theorem measurable_sm (e : AE D) : Measurable fun z : Mx D a r × Mx D a t => (e • z.1, e • z.2) :=
  ((continuous_const_smul e).measurable.comp measurable_fst).prodMk ((continuous_const_smul e).measurable.comp measurable_snd)

theorem map_ne_zero (ν : Measure (Mx D a r × Mx D a t)) (s : Set (Mx D a r × Mx D a t)) (e : AE D) (hs : ν s ≠ 0) :
    (ν.restrict s).map (fun z => (e • z.1, e • z.2)) ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure _ => μ Set.univ) h
  simp only [Measure.map_apply (measurable_sm e) MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.coe_zero, Pi.zero_apply] at this
  exact hs this

theorem transfer (hn : r + t = n) {V : HSp D} {b₀ : HermE D r} {S : Finset (Pl D)} {e : AE D}
    (ν : Measure (Mx D V.rank r × Mx D V.rank t))
    (hyv : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 →
      IntOff S (yv V b₀ z) ∧ yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z)
    (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ)
    (hη : Good S e η) :
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) ∂((ν.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map
      fun z => (e • z.1, e • z.2)) = ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) ∂ν := by
  set F : Mx D V.rank r × Mx D V.rank t → ℂ := fun z => Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z)) with hF
  set s : Set (Mx D V.rank r × Mx D V.rank t) := {z | IntOff S z.1 ∧ IntOff S z.2} with hs
  have hFc : Continuous F := (hΦc.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hηc.comp (continuous_yv V b₀)))
  have hfc : Continuous fun z : Mx D V.rank r × Mx D V.rank t => (e • z.1, e • z.2) :=
    ((continuous_const_smul e).comp continuous_fst).prodMk ((continuous_const_smul e).comp continuous_snd)
  have key : ∀ z ∈ s, F (e • z.1, e • z.2) = F z := by
    rintro z ⟨h1, h2⟩
    obtain ⟨hy, hye⟩ := hyv z h1 h2
    have hj : IntOff S (jn hn z.1 z.2) := (intOff_jn S hn z.1 z.2).2 ⟨h1, h2⟩
    simp only [hF, hye, jn_smul]
    rw [← good_pos hΦ hj, ← good_pos hη hy]
  have off : ∀ z ∉ s, F z = 0 := by
    intro z hz
    have hj : ¬ IntOff S (jn hn z.1 z.2) := fun h => hz ((intOff_jn S hn z.1 z.2).1 h)
    simp only [hF, good_neg hΦ hj, zero_mul]
  rw [integral_map (measurable_sm e).aemeasurable hFc.aestronglyMeasurable]
  have hae : ∀ᵐ z ∂(ν.restrict s), F (e • z.1, e • z.2) = F z := by
    have hm : MeasurableSet {a : Mx D V.rank r × Mx D V.rank t | ¬F (e • a.1, e • a.2) = F a} :=
      (isOpen_ne_fun (hFc.comp hfc) hFc).measurableSet
    rw [ae_iff, Measure.restrict_apply hm]
    convert measure_empty (μ := ν)
    exact Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.1 (key z hz.2)
  rw [integral_congr_ae hae, setIntegral_eq_integral_of_forall_compl_eq_zero off]

theorem orb_null {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (hν : IsOrb V b₀ e ν) (hfree : ν {z | ¬ Free e z} = 0)
    (hno : ∀ z : Mx D V.rank r × Mx D V.rank t, Free e z →
      ¬ (ip V z.1 z.1 = e • rat b₀.1 ∧ e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ qv V b₀ z = 0)) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  refine le_antisymm ?_ bot_le
  calc ν Set.univ ≤ ν ({z | ¬ (e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ ip V z.1 z.1 = e • rat b₀.1 ∧ qv V b₀ z = 0)} ∪
        {z | ¬ Free e z}) := by
        refine measure_mono fun z _ => ?_
        by_cases hz : Free e z
        · left
          rintro ⟨h1, h2, h3, h4⟩
          exact hno z hz ⟨h3, h1, h2, h4⟩
        · right; exact hz
    _ ≤ _ := measure_union_le _ _
    _ = 0 := by rw [hν.supp, hfree, add_zero]

end PositivityTheory.Rg.Rsw.L.LMuId

open PositivityTheory.Rg.Rsw.L.LMuId in
theorem PositivityTheory.Rg.Rsw.L.muId : IdemEx → GoodEv → BumpEx → ThProd → EisMeas → NullSing → Uniq → NoFrame → ThetaSideMeasure → ToS →
    MuId := by
  classical
  intro hI hG _ _ hE hN hU hF hT hS D n t B W d hn ψ χ θ μB μW ωB ωW hst mu hmu M m b₀ hb₀ hRho I
  have hdet : b₀.1.det ≠ 0 := hb₀.2
  have hθ : IsInfFam θ := hst.hθ
  obtain ⟨S₁, hS₁⟩ := hE D n t B W d hn ψ χ θ μB μW ωB ωW hst mu hmu M m b₀ hb₀ hRho
  have hΩc : ∀ Ω, IsTh ψ χ θ b₀ m.μ Ω → Continuous (Ω 1) := fun Ω hΩ =>
    hΩ.cont.comp (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_⟩
  · intro hno Φ Ω hΩ hcs
    obtain ⟨S₂, hS₂⟩ := hF D t B W ⟨d⟩ b₀ hdet hno
    obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
    obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
    set S := S₁ ∪ S₂ ∪ S₃ ∪ S₄ with hSdef
    obtain ⟨e, he⟩ := (hI D S).1
    obtain ⟨ν, hν, hint⟩ := hS₁ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
    have h0 : ν = 0 := orb_null hν (hN D W.rank t B b₀ hdet S e he ν hν)
      (hS₂ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
    rw [hint Φ (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) Ω hΩ
      (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) hcs, h0, integral_zero_measure]
  · intro x₀ hx₀
    have : m.μ.IsAddHaarMeasure := m.hμ.1
    obtain ⟨ν₂, hν₂, ⟨S₅, hS₅⟩, hT2⟩ := hT D n t B W d hn I θ hθ m.μ inferInstance b₀ hdet x₀ hx₀
    obtain ⟨S₆, hS₆⟩ := hS D W.rank t B b₀ hdet
    have core : ∀ S, S₁ ⊆ S → S₅ ⊆ S → S₆ ⊆ S → ∀ e, IsIdem S e → ∃ c : ℂ, ∀ (Φ : schwartzA θ B.rank n) Ω,
        IsTh ψ χ θ b₀ m.μ Ω → HasCompactSupport (Ω 1) → Good S e Φ.1 → Good S e (Ω 1) →
        mu (Rsec M m ψ b₀ (fun g => (ωB g Φ).1 0) 1 Ω) =
          c * ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv B b₀ z)) ∂ν₂ := by
      intro S h1 h5 h6 e he
      obtain ⟨ν, hν, hint⟩ := hS₁ S h1 e he
      obtain ⟨hOrb, hyv⟩ := hS₆ S h6 e he ν₂ hν₂
      obtain ⟨κ, hκ⟩ := hU D W.rank t B b₀ hdet S e he ν _ hν hOrb (map_ne_zero ν₂ _ e (hS₅ S h5))
      refine ⟨((κ : ℝ) : ℂ), fun Φ Ω hΩ hcs hΦg hΩg => ?_⟩
      rw [hint Φ hΦg Ω hΩ hΩg hcs, hκ, integral_smul_nnreal_measure,
        transfer hn ν₂ hyv Φ.1 (Ω 1) (GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ _ _ Φ.1 Φ.2).1 (hΩc Ω hΩ) hΦg hΩg,
        NNReal.smul_def, Complex.real_smul]
    by_cases hex : ∃ (Φ₀ : schwartzA θ B.rank n) (Ω₀ : G D t → Mx D W.rank t → ℂ), IsTh ψ χ θ b₀ m.μ Ω₀ ∧
        HasCompactSupport (Ω₀ 1) ∧ ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂ ≠ 0
    · obtain ⟨Φ₀, Ω₀, hΩ₀, hcs₀, hI₀⟩ := hex
      refine ⟨mu (Rsec M m ψ b₀ (fun g => (ωB g Φ₀).1 0) 1 Ω₀) /
        ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂, fun Φ Ω hΩ hcs => ?_⟩
      obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
      obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
      obtain ⟨S₇, hS₇⟩ := hG D θ hθ B.rank n Φ₀.1 Φ₀.2
      obtain ⟨S₈, hS₈⟩ := hG D θ hθ W.rank t (Ω₀ 1) (hΩ₀.mem 1)
      set S := S₁ ∪ S₅ ∪ S₆ ∪ S₃ ∪ S₄ ∪ S₇ ∪ S₈ with hSdef
      obtain ⟨e, he⟩ := (hI D S).1
      obtain ⟨c, hc⟩ := core S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
      have h₀ := hc Φ₀ Ω₀ hΩ₀ hcs₀ (hS₇ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₈ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
      have h := hc Φ Ω hΩ hcs (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he)
      have hcv : c = mu (Rsec M m ψ b₀ (fun g => (ωB g Φ₀).1 0) 1 Ω₀) /
          ∫ z, Φ₀.1 (jn hn z.1 z.2) * conj (Ω₀ 1 (yv B b₀ z)) ∂ν₂ := (eq_div_iff hI₀).mpr h₀.symm
      rw [h, ← hcv, (hT2 Φ.1 Φ.2 (Ω 1) (hΩ.mem 1)).2.2]
    · push Not at hex
      refine ⟨0, fun Φ Ω hΩ hcs => ?_⟩
      obtain ⟨S₃, hS₃⟩ := hG D θ hθ B.rank n Φ.1 Φ.2
      obtain ⟨S₄, hS₄⟩ := hG D θ hθ W.rank t (Ω 1) (hΩ.mem 1)
      set S := S₁ ∪ S₅ ∪ S₆ ∪ S₃ ∪ S₄ with hSdef
      obtain ⟨e, he⟩ := (hI D S).1
      obtain ⟨c, hc⟩ := core S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he
      rw [hc Φ Ω hΩ hcs (hS₃ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he) (hS₄ S (by intro x hx; simp only [hSdef, Finset.mem_union]; tauto) e he), hex Φ Ω hΩ hcs, mul_zero,
        zero_mul]

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LThCoef

theorem rinv_of_rank {K : Type*} [Field K] {m n : ℕ} (x : Matrix (Fin m) (Fin n) K) (h : x.rank = m) :
    ∃ x' : Matrix (Fin n) (Fin m) K, x * x' = 1 := by
  have hr : LinearMap.range x.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.finrank_range_mulVecLin, h]
    simp
  obtain ⟨g, hg⟩ := x.mulVecLin.exists_rightInverse_of_surjective hr
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (x.mulVecLin ∘ₗ g) = x * LinearMap.toMatrix' g := by
    show LinearMap.toMatrix' (Matrix.toLin' x ∘ₗ g) = _
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

theorem orbit_mat {K : Type*} [Field K] [StarRing K] {m n : ℕ} (J : Matrix (Fin m) (Fin m) K) (hJ : IsUnit J.det)
    (x y : Matrix (Fin m) (Fin n) K) (x' y' : Matrix (Fin n) (Fin m) K) (hx : x * x' = 1) (hy : y * y' = 1)
    (h : xᴴ * (J * x) = yᴴ * (J * y)) : ∃ g : Matrix (Fin m) (Fin m) K, g * x = y ∧ gᴴ * (J * g) = J := by
  have hL : y'ᴴ * yᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hy, Matrix.conjTranspose_one]
  have h0 : J * (y * (1 - x' * x)) = 0 := by
    calc J * (y * (1 - x' * x)) = (y'ᴴ * yᴴ) * (J * y) * (1 - x' * x) := by
          rw [hL, Matrix.one_mul, Matrix.mul_assoc]
      _ = y'ᴴ * (yᴴ * (J * y)) * (1 - x' * x) := by rw [Matrix.mul_assoc y'ᴴ]
      _ = y'ᴴ * (xᴴ * (J * x)) * (1 - x' * x) := by rw [h]
      _ = y'ᴴ * xᴴ * J * (x - x * x' * x) := by
          simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hx, Matrix.one_mul, sub_self, Matrix.mul_zero]
  have h1 : y * (1 - x' * x) = 0 := by
    have := congrArg (fun M => J⁻¹ * M) h0
    simp only [Matrix.mul_zero] at this
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul] at this
  refine ⟨y * x', ?_, ?_⟩
  · have : y - y * (x' * x) = 0 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one]
    rw [Matrix.mul_assoc]
    exact (sub_eq_zero.1 this).symm
  · calc (y * x')ᴴ * (J * (y * x')) = x'ᴴ * (yᴴ * (J * y)) * x' := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = x'ᴴ * (xᴴ * (J * x)) * x' := by rw [h]
      _ = (x * x')ᴴ * (J * (x * x')) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [hx, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

variable {D : D7}

theorem gramQ_eq' (W : HSp D) {n : ℕ} (x : Matrix (Fin W.rank) (Fin n) D.host.E) : gramQ W x = xᴴ * (HSpace.gram W * x) := rfl

theorem exists_rat (W : HSp D) (γ : GQ W) : ∃ δ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, rat δ = mt W γ := by
  obtain ⟨δ, hδ⟩ := (mem_GQ_iff W γ.1).1 γ.2
  exact ⟨δ, hδ⟩

def dl (W : HSp D) (γ : GQ W) : Matrix (Fin W.rank) (Fin W.rank) D.host.E := Classical.choose (exists_rat W γ)

theorem rat_dl (W : HSp D) (γ : GQ W) : rat (dl W γ) = mt W γ := Classical.choose_spec (exists_rat W γ)

theorem dl_unitary (W : HSp D) (γ : GQ W) : (dl W γ)ᴴ * (HSpace.gram W * dl W γ) = HSpace.gram W := by
  apply rat_injective
  rw [rat_mul, rat_mul, rat_conjTranspose, rat_dl]
  exact mt_unitary W γ.1

theorem dl_inv_mul (W : HSp D) (γ : GQ W) : dl W γ⁻¹ * dl W γ = 1 := by
  apply rat_injective
  rw [rat_mul, rat_dl, rat_dl, rat_one]
  exact mt_inv_mul W γ.1

theorem orbit_equiv (W : HSp D) {n : ℕ} (x₀ : Matrix (Fin W.rank) (Fin n) D.host.E) (hx₀ : x₀.rank = W.rank) :
    ∃ e : GQ W ≃ {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀},
      ∀ γ, rat (e γ).1 = mm (mt W γ) (rat x₀) := by
  obtain ⟨x', hx'⟩ := rinv_of_rank x₀ hx₀
  have hrk : ∀ γ : GQ W, (dl W γ * x₀).rank = W.rank := fun γ => by
    refine le_antisymm (Matrix.rank_le_height _) ?_
    calc W.rank = x₀.rank := hx₀.symm
      _ = (dl W γ⁻¹ * (dl W γ * x₀)).rank := by rw [← Matrix.mul_assoc, dl_inv_mul, Matrix.one_mul]
      _ ≤ _ := Matrix.rank_mul_le_right _ _
  have hgr : ∀ γ : GQ W, gramQ W (dl W γ * x₀) = gramQ W x₀ := fun γ => by
    rw [gramQ_eq', gramQ_eq', Matrix.conjTranspose_mul]
    calc x₀ᴴ * (dl W γ)ᴴ * (HSpace.gram W * (dl W γ * x₀))
        = x₀ᴴ * ((dl W γ)ᴴ * (HSpace.gram W * dl W γ) * x₀) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [dl_unitary]
  let f : GQ W → {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank ∧ gramQ W y = gramQ W x₀} :=
    fun γ => ⟨dl W γ * x₀, hrk γ, hgr γ⟩
  have hinj : Function.Injective f := by
    intro γ γ' hγ
    have h1 : dl W γ * x₀ = dl W γ' * x₀ := congrArg Subtype.val hγ
    have h2 : dl W γ = dl W γ' := by
      have := congrArg (· * x') h1
      simpa only [Matrix.mul_assoc, hx', Matrix.mul_one] using this
    have h3 : mt W γ = mt W γ' := by rw [← rat_dl, ← rat_dl, h2]
    exact Subtype.ext (mt_injective W h3)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hyr, hyg⟩
    obtain ⟨y', hy'⟩ := rinv_of_rank y hyr
    obtain ⟨g, hgx, hgu⟩ := orbit_mat (HSpace.gram W) (gram_isUnit_det W) x₀ y x' y' hx' hy'
      (by rw [← gramQ_eq', ← gramQ_eq', hyg])
    have hM : adj (rat g) * (gA W * rat g) = gA W := by
      rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, hgu]
    let γ : GA D W := ofMat W (rat g) hM
    have hγ : γ ∈ GQ W := (mem_GQ_iff W γ).2 (by rw [mt_ofMat]; exact ⟨g, rfl⟩)
    refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
    have : dl W ⟨γ, hγ⟩ = g := rat_injective (by rw [rat_dl]; exact mt_ofMat W _ hM)
    show dl W ⟨γ, hγ⟩ * x₀ = y
    rw [this, hgx]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun γ => ?_⟩
  show rat (dl W γ * x₀) = _
  rw [rat_mul, rat_dl]

end PositivityTheory.Rg.Rsw.L.LThCoef

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem tsum_GQ (V : HSp D) (n : ℕ) (γ : GA D V) (hγ : γ ∈ GQ V) (F : Mx D V.rank n → ℝ≥0∞) :
    ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (mm (mt V γ) (rat x.1)) =
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (rat x.1) := by
  obtain ⟨g, hg⟩ := mem_ratMx.1 ((mem_GQ_iff V γ).1 hγ)
  obtain ⟨g', hg'⟩ := mem_ratMx.1 ((mem_GQ_iff V γ⁻¹).1 (inv_mem hγ))
  have h1 : g' * g = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_inv_mul V γ)
  have h2 : g * g' = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_mul_inv V γ)
  have hu : IsUnit g.det := isUnit_iff_exists_inv.2 ⟨g'.det, by rw [← Matrix.det_mul, h2, Matrix.det_one]⟩
  have hu' : IsUnit g'.det := isUnit_iff_exists_inv.2 ⟨g.det, by rw [← Matrix.det_mul, h1, Matrix.det_one]⟩
  let e : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} ≃
      {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} :=
    { toFun := fun x => ⟨g * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g x.1 hu]; exact x.2⟩
      invFun := fun x => ⟨g' * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g' x.1 hu']; exact x.2⟩
      left_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h1, Matrix.one_mul])
      right_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]) }
  rw [← e.tsum_eq (fun x => F (rat x.1))]
  refine tsum_congr fun x => ?_
  show F _ = F (rat (g * x.1))
  rw [rat_mul, hg]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end
