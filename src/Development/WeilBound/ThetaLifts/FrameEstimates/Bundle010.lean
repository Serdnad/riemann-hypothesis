module

public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle002
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle002
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.Bundle001
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle009
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_clm (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕)
    (hsb : φ ∈ SB _) (h : UA σ W.J) :
    ∃ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), L f = M.I om (pureA F f φ) h := by
  obtain ⟨h1, h2⟩ := dom_facts hB hp hD hφ hsb
  refine ⟨⟨⟨⟨fun f => M.I om (pureA F f φ) h, fun f f' => ?_⟩, fun c f => ?_⟩, h2 h⟩, fun _ => rfl⟩
  · have e : pureA F (f + f' : SInf F _) φ = pureA F f φ + pureA F f' φ := by
      funext x; simp [pureA, add_mul]
    unfold Model.I
    rw [e, ← integral_add ((h1 f).1 h) ((h1 f').1 h)]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_add hp (pureA_mem f hsb) (pureA_mem f' hsb) g h)
  · have e : pureA F (c • f : SInf F _) φ = c • pureA F f φ := by
      funext x; simp [pureA, mul_assoc]
    change M.I om (pureA F (c • f : SInf F _) φ) h = c * M.I om (pureA F f φ) h
    unfold Model.I
    rw [e, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun g => theta_smul hp c (pureA_mem f hsb) g h)

theorem one_mem_UAt : (1 : UA σ X.J) ∈ UAt σ X (evI F) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem one_mem_Lines : (1 : Multiplicative ℝ →* UA σ X.J) ∈ Lines σ X := ⟨continuous_const, fun _ => one_mem_UAt⟩

end

theorem iDer_of (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) (hI : IInv) : IDer := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hD φ hφ hsb f hf
  obtain ⟨-, i2, i3⟩ := hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_UAt _ (hγ.2 (Multiplicative.ofAdd t))
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_mem_Lines γ hγ T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have := hd L
    rw [hLf] at this
    convert this using 2 with t
    rw [hLf, ← (hT t).1.1 f φ hsb, i3]
  · choose T hT using fun t : ℝ => hO F E σ B n d X W M χX χW om r s r' s' hp _ (hγ.2 (Multiplicative.ofAdd t)) 1 one_mem_UAt
    obtain ⟨f₁, hf₁, ha, hd⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ 1 one_mem_Lines T (fun t => (hT t).1) f hf
    refine ⟨f₁, hf₁, ha, funext fun h => ?_⟩
    obtain ⟨L, hLf⟩ := exists_clm hB hp hD hφ hsb h
    have h1 := hd L
    have h2 : (fun t => L (T t f)) = fun _ => M.I om (pureA F f φ) h := funext fun t => by
      rw [hLf, ← (hT t).1.1 f φ hsb, i2]
    rw [h2] at h1
    rw [← hLf]
    exact h1.unique (hasDerivAt_const _ _)

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_soFin (hF : SoFin) (hp : IsPair B M χX χW om r s r' s') {m : ℕ} (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) : ∃ ψ : Fin m → (Fin n × Fin d → Af F) → ℂ, (∀ j, ψ j ∈ soFin B M) ∧
      ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
        ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (soCoeff (B := B) M φ)
  let P := Submodule.linearProjOfIsCompl _ _ hQ
  let ψ : Fin m → (Fin n × Fin d → Af F) → ℂ := fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i
  have hψ : ∀ j, ψ j ∈ soFin B M := fun j =>
    ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i), (P (Pi.single j 1)).2⟩
  have key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := fun w hw => by
    obtain ⟨m', f', χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw
    have hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B := B) M φ := fun x f₀ => by
      have e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i := by
        funext y
        obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F,
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y :=
          ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
            funext fun i => RingEquiv.apply_symm_apply _ _, rfl⟩
        have := congrFun e z
        simp only [Finset.sum_apply, pureA, hz1, hz2] at this
        simpa [Finset.sum_apply] using this
      have e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i) := by
        funext z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)
    funext z
    set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
    have e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ) := by
      have a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x :=
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)
      have a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [← a1, a2]
      simp
    have e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i := fun i => by
      simpa [Finset.sum_apply] using congrFun e4 i
    simp only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  exact ⟨ψ, hψ, key⟩

theorem polData_sum (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb) ∧ (∀ i, φ i ∈ SB _) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, x, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f hf χ h1 h2 h3 using fun i => (x i).2
  refine ⟨m, fun i => c i • f i, fun i => FiniteAdelicSupportCompactness.pf (χ i), fun i => Submodule.smul_mem _ _ (hf i),
    fun i => FiniteAdelicSupportCompactness.pf_mem ⟨h1 i, ((h2 i).and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩,
    Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h3 i, FiniteAdelicSupportCompactness.pure_eq]
  funext z
  simp [pureA, mul_assoc]


variable (B W) in
def Nice (f : UA σ W.J → ℂ) : Prop := LeftInv f ∧ UMG W f ∧ SmoothFin W B.emb f

theorem nice_zero : Nice B W (0 : UA σ W.J → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨0, {0}, rfl, by
    rintro _ rfl
    exact ⟨continuous_const, ⟨0, fun h => by simp⟩, fun γ _ => ⟨0, rfl, fun h => hasDerivAt_const _ _⟩⟩⟩,
    Set.univ, univ_mem, fun _ _ _ _ => rfl⟩

theorem Nice.lin (hU : UMGLin) (hc : IsCMExt F E σ) (hJ : EpsHerm σ W.J) {f f' : UA σ W.J → ℂ} (h : Nice B W f)
    (h' : Nice B W f') (a b : ℂ) : Nice B W (a • f + b • f') := by
  refine ⟨fun γ hγ x => ?_, hU F E σ hc B.emb d W hJ f f' h.2.1 h'.2.1 a b, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, h.1 γ hγ x, h'.1 γ hγ x]
  · obtain ⟨U, hU1, hu⟩ := h.2.2
    obtain ⟨U', hU1', hu'⟩ := h'.2.2
    refine ⟨U ∩ U', inter_mem hU1 hU1', fun u hm h1 x => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, hu u hm.1 h1 x, hu' u hm.2 h1 x]

theorem nice_sum (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hp : IsPair B M χX χW om r s r' s')
    {𝓕} (hD : Dom M om 𝓕) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hf : ∀ i, f i ∈ M.Pol B.ψ B.emb) (hφ : ∀ i, φ i ∈ 𝓕) (hsb : ∀ i, φ i ∈ SB _) :
    Nice B W (M.I om (∑ i, pureA F (f i) (φ i))) := by
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  have e : M.I om (∑ i, pureA F (f i) (φ i)) = ∑ i, M.I om (pureA F (f i) (φ i)) :=
    funext fun h => ((dom_sum hB hp hD f φ hφ hsb).2.2 h).trans (Finset.sum_apply _ _ _).symm
  rw [e]
  refine Finset.sum_induction _ _ (fun a b ha hb => by simpa using ha.lin hU hp.base.cm hJ hb 1 1) nice_zero fun i _ => ?_
  exact ⟨(hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem _ (hsb i))).1,
    hG F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hD _ (hφ i) (hsb i) _ (hf i)⟩

end

theorem sig_nice (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (ht' : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ PositivityTheory.ThKEnd.Sig B G om om') :
    Nice B G.W f := by
  obtain ⟨h1, h2, h3⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  obtain ⟨m, f, φ, c1, c2, rfl⟩ := polData_sum h1 hΦ
  obtain ⟨m', f', φ', c1', c2', rfl⟩ := polData_sum h2 hΦ'.1
  obtain ⟨ψ, hψ, hk⟩ := exists_soFin hF h2 φ' c2'
  rw [hk f' hΦ'.2]
  have n1 := nice_sum hB hU hE hG hI h1 (hW F E σ B _ _ _ _ _ _ _ om _ _ _ _ h1 (Or.inl h3)) f φ c1 c2 c2
  have n2 := nice_sum hB hU hE hG hI h2 (dom_of_domSoU hS h2) f' ψ c1' hψ fun i => (hψ i).1
  simpa [sub_eq_add_neg] using n1.lin hU h1.base.cm hJ n2 1 (-1)

theorem sigRapid_of (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) (hC : CuspRapid) : PositivityTheory.ThKEnd.Orth.SigRapid := by
  intro F E _ _ _ _ _ σ B a a' G X om om' ht' f hf hc
  obtain ⟨n1, n2, n3⟩ := sig_nice hB hU hE hG hI hT hW hS hF ht' hf
  obtain ⟨h1, -, -⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  refine ⟨?_, n1, hC F E σ h1.base.cm B.emb _ G.W hJ f n1 n2 n3 hc⟩
  obtain ⟨k, S, hS1, hS2⟩ := n2
  exact (hS2 f hS1).1

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem dom_continuous (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hp : IsPair B M χX χW om r s r' s') {𝓕}
    (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) (hsb : φ ∈ SB _) (f : SInf F (Fin n × Fin d)) :
    Continuous (M.I om (pureA F f φ)) := by
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨i1, i2, -, -, -, -, -, hb⟩ := hT F E σ hp.base.cm d W.J hJ'
  obtain ⟨p, k, G, -, hG, hfin, hbd⟩ := hD φ hφ
  have hc := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 _ (pureA_mem f hsb)).1
  haveI : FirstCountableTopology (UA σ W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i2
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds h₀
  obtain ⟨C, hC⟩ := hb K hK
  have hpf : 0 ≤ p f := apply_nonneg p f
  refine continuousAt_of_dominated (bound := fun g => p f * (C : ℝ) ^ k * (G g).toReal)
    (Eventually.of_forall fun h => (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable) ?_
    ((integrable_toReal_of_lintegral_ne_top hG.aemeasurable hfin.ne).const_mul _)
    (Eventually.of_forall fun g => (hc.comp (continuous_const.prodMk continuous_id)).continuousAt)
  filter_upwards [hK0] with h hh
  filter_upwards [ae_lt_top hG hfin.ne] with g hg
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne) (hbd f g h)
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at e
  refine e.trans ?_
  have : (ht h : ℝ) ≤ C := hC h hh
  gcongr

theorem dom_bound (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) :
    ∃ k : ℕ, ∀ f : SInf F (Fin n × Fin d), ∃ C : ℝ, ∀ h, ‖M.I om (pureA F f φ) h‖ ≤ C * (ht h : ℝ) ^ k := by
  obtain ⟨p, k, G, -, hG, hfin, hb⟩ := hD φ hφ
  refine ⟨k, fun f => ⟨p f * (∫⁻ g in M.dom, G g ∂M.μ).toReal, fun h => ?_⟩⟩
  have h1 : ‖M.I om (pureA F f φ) h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * ∫⁻ g in M.dom, G g ∂M.μ := by
    rw [← lintegral_const_mul _ hG]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun g => hb f g h)
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h1
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (apply_nonneg p f) (by positivity))] at e
  exact e.trans (le_of_eq (by ring))

end

theorem iUMG_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hD : IDer) (hL : Level) (hI : IInv) : IUMG := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f hf
  obtain ⟨k, hk⟩ := dom_bound hp hdom hφ
  refine ⟨⟨k, {u | ∃ f₁ ∈ M.Pol B.ψ B.emb, u = M.I om (pureA F f₁ φ)}, ⟨f, hf, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩
    refine ⟨dom_continuous hB hT hE hp hdom hφ hsb f₁, hk f₁, fun γ hγ => ?_⟩
    obtain ⟨f₂, hf₂, -, hd⟩ := (hD F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f₁ hf₁).1 γ hγ
    exact ⟨_, ⟨f₂, hf₂, rfl⟩, hd⟩
  · obtain ⟨U, hU, hu⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp φ hsb
    refine ⟨U, hU, fun u huU h1 h => ?_⟩
    rw [← (hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)).2.2 h u, hu u huU h1]

end PositivityTheory.ThKEst

end
end

section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem latFull_of : LatTor → Minor → LatFull := by
  intro hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m
  obtain ⟨N, hN⟩ := hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  refine ⟨N + m * (n + 1), fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hN C hC
  obtain ⟨c, hc, h⟩ := hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  refine ⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩
  let i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E)) := fun x => ⟨x.1, trivial⟩
  have hi : Function.Injective i := fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
  let g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))
  calc _ ≤ ∑' x, ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := h s hs t ht x.1 x.2
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        unfold maj
        split_ifs with hx
        · have h2 := pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp] at h2
          rw [pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)
        · simp
    _ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) *
          (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.coe_mul]
        change _ = ENNReal.ofReal _ * _ * _
        ring

end PositivityTheory.ThKEst

end
end
