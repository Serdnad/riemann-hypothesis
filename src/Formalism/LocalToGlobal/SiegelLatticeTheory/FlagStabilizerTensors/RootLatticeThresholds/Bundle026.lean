module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Aesop.Main
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Formalism.PeriodIntegrals.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SubMemOfIndQ

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.NGLeaves

open Formalism.BasicNotions Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

theorem nondegenerate_gram_tuple : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 = PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

end Formalism.L2.SG.NGLeaves
end
end

section

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsConv

open Formalism.MainNotions.S Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.unitaryCongruence

variable (I : AutInst)

def coset (m : ℕ) (q : KSub I ⧸ KgN I m) : Set I.Gf := {y | ((q.out : KSub I) : I.Gf)⁻¹ * y ∈ I.Kg m}

theorem coset_sub (m : ℕ) (q : KSub I ⧸ KgN I m) : coset I m q ⊆ I.Kset := by
  intro y hy
  have h1 : ((q.out : KSub I) : I.Gf) * (((q.out : KSub I) : I.Gf)⁻¹ * y) ∈ I.Kset :=
    K_mul I (q.out : KSub I).2 hy.1
  simpa using h1

theorem mem_coset_iff (m : ℕ) {y : I.Gf} (hy : y ∈ I.Kset) (q : KSub I ⧸ KgN I m) :
    y ∈ coset I m q ↔ q = (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m) := by
  constructor
  · intro h
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 h
  · intro h
    subst h
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m))
    exact this

theorem isOpen_coset (m : ℕ) (hm : 1 ≤ m) (q : KSub I ⧸ KgN I m) : IsOpen (coset I m q) :=
  (I.topf_open m hm).preimage (continuous_const.mul continuous_id)

theorem measure_coset (μf : Measure I.Gf) [μf.IsMulLeftInvariant] (m : ℕ) (q : KSub I ⧸ KgN I m) :
    μf (coset I m q) = μf (I.Kg m) :=
  measure_preimage_mul μf _ (I.Kg m)

theorem term_eq {m : ℕ} {f₁ f₂ : I.Gf → ℂ} (h1N : ∀ y, ∀ n ∈ I.Kg m, f₁ (y * n) = f₁ y)
    (h2N : ∀ z, ∀ n ∈ I.Kg m, f₂ (n * z) = f₂ z) (x : I.Gf) (q : KSub I ⧸ KgN I m) {y : I.Gf}
    (hyq : y ∈ coset I m q) :
    f₁ y * f₂ (y⁻¹ * x) = f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x) := by
  have hn : ((q.out : KSub I) : I.Gf)⁻¹ * y ∈ I.Kg m := hyq
  generalize ((q.out : KSub I) : I.Gf) = c at hn ⊢
  have e1 : f₁ y = f₁ c := by
    have := h1N c (c⁻¹ * y) hn
    rwa [mul_inv_cancel_left] at this
  have e2 : f₂ (y⁻¹ * x) = f₂ (c⁻¹ * x) := by
    have := h2N (y⁻¹ * x) (c⁻¹ * y) hn
    rw [← this]
    congr 1
    group
  rw [e1, e2]

theorem convF_fin (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {m : ℕ} (hm : 1 ≤ m) (hfin : μf (I.Kg m) < ⊤)
    [Fintype (KSub I ⧸ KgN I m)] {f₁ f₂ : I.Gf → ℂ} (h1K : ∀ y, f₁ y ≠ 0 → y ∈ I.Kset)
    (h1N : ∀ y, ∀ n ∈ I.Kg m, f₁ (y * n) = f₁ y) (h2N : ∀ z, ∀ n ∈ I.Kg m, f₂ (n * z) = f₂ z) (x : I.Gf) :
    I.convF μf f₁ f₂ x = (μf (I.Kg m)).toReal *
      ∑ q : KSub I ⧸ KgN I m, f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x) := by
  classical
  have key : (fun y => f₁ y * f₂ (y⁻¹ * x)) = fun y => ∑ q : KSub I ⧸ KgN I m,
      Set.indicator (coset I m q)
        (fun _ => f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x)) y := by
    funext y
    by_cases hy : y ∈ I.Kset
    · rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m)]
      · have hmem := (mem_coset_iff I m hy (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m)).2 rfl
        rw [Set.indicator_of_mem hmem]
        exact term_eq I h1N h2N x _ hmem
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hmem
        exact hq ((mem_coset_iff I m hy q).1 hmem)
      · intro h; exact absurd (Finset.mem_univ _) h
    · have h0 : f₁ y = 0 := by by_contra h; exact hy (h1K y h)
      rw [h0, zero_mul]
      symm
      refine Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hy (coset_sub I m q hmem)) _
  unfold AutInst.convF
  rw [key, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (isOpen_coset I m hm q).measurableSet, measureReal_def, measure_coset,
      Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (isOpen_coset I m hm q).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_coset]
    exact hfin.ne

end Formalism.L2.SG.Pf.AllRowsConv
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRedKer

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.MainNotions.BridgeLemma

variable {D : D7}

def sigH (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

theorem sigH_coe (a : 𝓞 D.host.E) : ((sigH D a : 𝓞 D.host.E) : D.host.E) = D.host.conj (a : D.host.E) := rfl

def conjH (w : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (sigH D)
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (sigH D).surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem conj_conj (X : HidaSetting D) (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  obtain ⟨x, rfl⟩ := X.ιE.surjective y
  rw [← X.ιE_conj, ← X.ιE_conj, star_star]

theorem sigH_sigH (X : HidaSetting D) (a : 𝓞 D.host.E) : sigH D (sigH D a) = a := by
  apply RingOfIntegers.ext
  rw [sigH_coe, sigH_coe]
  exact conj_conj X _

theorem conjH_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : conjH (conjH w) = w := by
  apply HeightOneSpectrum.ext
  show (w.asIdeal.comap (sigH D)).comap (sigH D) = w.asIdeal
  ext a
  simp only [Ideal.mem_comap]
  rw [sigH_sigH X]

theorem isConjPl_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : IsConjPl D.host w (conjH w) := by
  intro x y hxy
  have hs : sigH D y = x := by
    apply RingOfIntegers.ext
    rw [sigH_coe, hxy, conj_conj X]
  show x ∈ w.asIdeal ↔ sigH D y ∈ w.asIdeal
  rw [hs]

theorem natCast_mem_conjH {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ} (h : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    (p : 𝓞 D.host.E) ∈ (conjH w).asIdeal := by
  show sigH D (p : 𝓞 D.host.E) ∈ w.asIdeal
  rw [map_natCast]
  exact h

theorem wB_conjH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : wB X (conjH w) = wc X.B.I (wB X w) := by
  apply HeightOneSpectrum.ext
  ext a
  rw [mem_wc]
  simp only [wB, conjH, Ideal.mem_comap]
  have hc : sigH D (RingOfIntegers.mapRingEquiv X.ιE a) =
      RingOfIntegers.mapRingEquiv X.ιE (sigO X.B.I a) := by
    apply RingOfIntegers.ext
    rw [sigH_coe]
    simp [RingOfIntegers.mapRingEquiv, sigO_coe, X.ιE_conj]
  rw [hc]

theorem finrank_cmField (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  haveI := D.host.galois
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr D.host.gal.toEquiv, Formalism.HC.Frame.natCard_GG]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  ring

theorem cover (X : HidaSetting D) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = conjH (D.naut.plGw k v) := by
  have hp := D.host.g_prime k
  set A : Set (HeightOneSpectrum (𝓞 D.host.E)) :=
    Set.range (D.naut.plGw k) ∪ Set.range (fun v => conjH (D.naut.plGw k v)) with hA
  set T : Set (HeightOneSpectrum (𝓞 D.host.E)) := placesOver D.host.E (D.host.g k) with hT
  have hAT : A ⊆ T := by
    rintro _ (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · exact D.naut.plGw_over k v
    · exact natCast_mem_conjH (D.naut.plGw_over k v)
  have hTfin : T.Finite := finite_plOver D.host.E hp
  have hinj2 : Function.Injective (fun v => conjH (D.naut.plGw k v)) := by
    intro v v' h
    apply D.naut.plGw_inj k
    have := congrArg conjH h
    simpa only [conjH_conjH X] using this
  have hdisj : Disjoint (Set.range (D.naut.plGw k)) (Set.range (fun v => conjH (D.naut.plGw k v))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, rfl⟩ ⟨v', hv'⟩
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    have hv'' : conjH (D.naut.plGw k v') = D.naut.plGw k v := hv'
    rw [hv''] at this
    exact this
  have hcA : A.ncard = 2 * D.R.f := by
    rw [hA, Set.ncard_union_eq hdisj (Set.finite_range _) (Set.finite_range _),
      Set.ncard_range_of_injective (D.naut.plGw_inj k), Set.ncard_range_of_injective hinj2,
      Nat.card_eq_fintype_card, D.nd.card_PlG k]
    ring
  have hcT : T.ncard = 2 * D.R.f := by rw [hT, D.nd.g_split k, finrank_cmField]
  have hEq : A = T := Set.eq_of_subset_of_ncard_le hAT (by rw [hcA, hcT]) hTfin
  have : w ∈ A := by rw [hEq]; exact hw
  rcases this with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨v, Or.inl rfl⟩
  · exact ⟨v, Or.inr rfl⟩

theorem unram (X : HidaSetting D) (k : Fin 2) (P : Ideal (𝓞 X.B.I.E)) (hPm : P.IsMaximal)
    (hgP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∉ P ^ 2 := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE
  have hQm : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  have hgQ : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.map e := by
    have := Ideal.mem_map_of_mem e hgP
    rwa [map_natCast] at this
  obtain ⟨-, hsq⟩ := hspl _ hQm hgQ
  intro h
  apply hsq
  have := Ideal.mem_map_of_mem e h
  rwa [map_natCast, Ideal.map_pow] at this

def toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv X.ιE).symm
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv X.ιE).symm.surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

theorem wB_toH (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 X.B.I.E)) : wB X (toH X w) = w := by
  apply HeightOneSpectrum.ext
  ext a
  simp [wB, toH, Ideal.mem_comap]

theorem redKerP_holds (X : HidaSetting D) (k : Fin 2) : Formalism.L2.SG.AllRowsOf.RedKerP X k := by
  intro x hx hred
  have hp := D.host.g_prime k
  have hA : ∀ v, ∀ y ∈ X.B.I.Lf, (X.B.I.fmat x - 1) *ᵥ y ∈ Lq X.B.I (wB X (D.naut.plGw k v)) := by
    intro v
    have h0 := (redMat_iff X _ _ x _).1 (hred v)
    exact stepA X.B.I hp (by rw [card_wB, card_res_host]) hx h0
  refine glue X.B.I hp (unram X k) hx fun w hw => ?_
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X w).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [map_natCast]; exact hw
  obtain ⟨v, hv | hv⟩ := cover X k (toH X w) hwH
  · rw [← wB_toH X w, hv]
    exact hA v
  · rw [← wB_toH X w, hv, wB_conjH X]
    exact stepB X.B.I hx (hA v)

end Formalism.L2.SG.Pf.AllRowsRedKer
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

namespace Formalism.L2.SG.LoopsFinal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section admitted

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)

variable (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)

end admitted

section AtOne

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))
  (H : TieHyp W hI) (A : AmpDat X) (hV : PvalForm W hI A)

theorem jtPin_of (hA : AmpFibreConst Y) : JtPin hF hI (termTieOf W hI H A hV) := by
  intro u u' t s hs
  have h : ∃ s' : TT Y u u', s'.toTerm = tc hI t := ⟨s, hs⟩
  show hsNormSq (JtOf hI t) = ampL s ^ 2
  unfold JtOf
  rw [dite_eq_left h, ← Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  have e := hA u u' (tc hI t) ⟨h.choose, h.choose_spec⟩ ⟨s, hs⟩
  unfold ampL at e ⊢
  rw [e]

def FrameChangeAt : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)),
    (∀ a b, b < a → ξ a b = 0) → (∀ a, ξ a a = 1) →
      ∃ m ∈ NLam (lamOf W hI t) (fl'Of W hI t), ∀ b, m (frame (fl'Of W hI t) b) = frameAct (frame (fl'Of W hI t)) ξ b

theorem frameEqvInj_of (hFC : FrameChangeAt W hI) (u u' : D.what₂.Word) :
    FrameEqvInj (termTieOf W hI H A hV) (u' := u') (FlagOfWord W u) := by
  intro t t' hL hE
  obtain ⟨n, hn, ξ, hl, hd, hfr⟩ := hE
  obtain ⟨m, hm, hmf⟩ := hFC u u' t ξ hl hd
  refine term_injC W hI t t' hL ⟨n, hn, m, hm, fun b => ?_⟩
  have e1 : frame (fl'Of W hI t') b = frameAct (fun a => n (frame (fl'Of W hI t) a)) ξ b := congrFun hfr b
  rw [e1, hmf b]

  simp only [frameAct, map_sum, map_smul]

end AtOne

section Ev

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
  (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt (Fm.D x i) (At x hx i))

end Ev

section Summ

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} {hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)}


end Summ

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (_root_.Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

def AtF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i) :=
  fun x hx i => termTieOf (W x hx i) (hI x hx i) (H x hx i) (A x hx i) (hV x hx i)

variable (hFC : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FrameChangeAt (W x hx i) (hI x hx i))
  (B : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopLocDat (Fm.D x i) (Fm.L x i) u u' C1)
  (M : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTermDat (Fm.D x i) (Fm.L x i) (AtF Fm X Y hF hI W H A hV x hx i) u u' C1 (B x hx i u u'))

variable (hAF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpFibreConst (Y x hx i))
  (hRF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.L2.SG.Pf.FibreCounting.RowFree (Y x hx i))
  (gam : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), GamPin (Y x hx i))

end Fam

section Closed

def NormTieC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairNormRelation (termTieOf W hI H A hV) u u'

def GramDeterminantCount : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    @Formalism.MainNotions.BridgeLemma.LatticeDeterminantFactorization D (termTieOf W hI H A hV) u u'

def EntryLatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X) (H : TieHyp W hI)
    (A : AmpDat X) (hV : PvalForm W hI A) (u u' : D.what₂.Word),
    BridgeLemma₂.wordPairEntriesInLattice (termTieOf W hI H A hV) u u'

def FrameChangeC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF)) (W : WittDat X), FrameChangeAt W hI

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (_root_.Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (W : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), WittDat (X x hx i))
  (H : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieHyp (W x hx i) (hI x hx i))
  (A : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmpDat (X x hx i))
  (hV : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PvalForm (W x hx i) (hI x hx i) (A x hx i))

end Closed

end Formalism.L2.SG.LoopsFinal
end
end
