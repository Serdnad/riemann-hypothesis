module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRelationsReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviStabilityReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarActionFifthReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationReal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle553
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle537
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle555
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BWGal

theorem gal_wn {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) (x : (Wc.bs l r.k n).R) :
    galBase σ n (Mid.wn r n x) = Mid.wn r n x := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Mid.wn_mk, galBase_cris, hσ]

abbrev bWM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Wc.L l (B.schFn M.p) r.ρ n) (Mid.Lm r M n) (Mid.wn r n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl

abbrev gM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) :
    Mor (Mid.Lm r M n) (Mid.Lm r M n) (galBase σ n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl

theorem bW_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  intro l _ K r M σ hσ n j y
  haveI : RingHomCompTriple r.w (ACris.galCris σ) r.w := ⟨RingHom.ext hσ⟩
  refine (pull_pull r.w (bWMor r M n) (galT' r M σ hσ n) j y).trans ?_
  exact cr_pull_eq _ _ (fun T => crHom (T := (bWM r M n).obj ((gM r M σ hσ n).obj T)) (T' := (bWM r M n).obj T)
    (RingHom.id T.B) (fun x => congrArg T.i (gal_wn r σ hσ n x)) (DPMorphism.id T.δ).isDPMorphism
    fun h => (pt_id _ h _).trans rfl) (fun _ _ => rfl) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.BWGal
end
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.invariant_pick_real : PositivityTheory.RgBcC.RealD.InvPick := by
  first | exact @GlobalTheory.CompanionTheory.InvPickKP.invPick | exact GlobalTheory.CompanionTheory.InvPickKP.invPick | (intros; apply GlobalTheory.CompanionTheory.InvPickKP.invPick <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.levi_relations_real : PositivityTheory.RgBcC.RealD.LevRel := by
  first | exact @GlobalTheory.CompanionTheory.LevChainRel.levRel | exact GlobalTheory.CompanionTheory.LevChainRel.levRel | (intros; apply GlobalTheory.CompanionTheory.LevChainRel.levRel <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.levi_stability_real : PositivityTheory.RgBcC.RealD.LevStab := by
  first | exact @GlobalTheory.CompanionTheory.LevBd.levStab | exact GlobalTheory.CompanionTheory.LevBd.levStab | (intros; apply GlobalTheory.CompanionTheory.LevBd.levStab <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.scalar_action_fifth_real : PositivityTheory.RgBcC.RealD.CapelliProductsScalar := by
  first | exact @GlobalTheory.CompanionTheory.CapScal.capScal | exact GlobalTheory.CompanionTheory.CapScal.capScal | (intros; apply GlobalTheory.CompanionTheory.CapScal.capScal <;> assumption)
end

section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

theorem _root_.GlobalTheory.T.semisimple_classification_real : PositivityTheory.RgBcC.RealD.SemiCls := by
  first | exact @GlobalTheory.CompanionTheory.SemiClass.semiCls | exact GlobalTheory.CompanionTheory.SemiClass.semiCls | (intros; apply GlobalTheory.CompanionTheory.SemiClass.semiCls <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagAvg

theorem avg_conj {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') (f : G → ℂ) (hl : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g)
    (g : G) :
    avg (fun k : K => f ((k : G)⁻¹ * g * k)) = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * g * x) := by
  set S : Subgroup K := K'.subgroupOf K with hSdef
  set u : K → ℂ := fun k => f ((k : G)⁻¹ * g * k) with hu
  have hS : S ≤ rStab u := by
    intro s hs k
    have hs' : (s : G) ∈ K' := Subgroup.mem_subgroupOf.1 hs
    show f (((k * s : K) : G)⁻¹ * g * ((k * s : K) : G)) = f ((k : G)⁻¹ * g * k)
    have e : ((k * s : K) : G)⁻¹ * g * ((k * s : K) : G) = (s : G)⁻¹ * ((k : G)⁻¹ * g * k) * s := by
      simp only [Subgroup.coe_mul]; group
    rw [e, (hl _ hs' _).2, (hl _ (K'.inv_mem hs') _).1]
  let φ : {x // x ∈ X} → K ⧸ S := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ S)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := by
        have h2 := QuotientGroup.eq.1 hxy
        exact Subgroup.mem_subgroupOf.1 h2
      have hy := hX y.1 (hXK _ y.2)
      exact Subtype.ext (hy.unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  let e := Equiv.ofBijective φ hφ
  have hindex : S.index = X.card := by
    show Nat.card (K ⧸ S) = _
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : S.index ≠ 0 := by
    rw [hindex]
    obtain ⟨x, ⟨hxX, -⟩, -⟩ := hX 1 K.one_mem
    exact (Finset.card_pos.2 ⟨x, hxX⟩).ne'
  rw [GlobalTheory.CompanionTheory.AvgLevel.avg_eq_level S u hS hne, hindex]
  congr 1
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort X]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (⟨x.1, hXK _ x.2⟩ : K)
  show u (φ x).out = u ⟨x.1, hXK _ x.2⟩
  have hφx : (φ x).out = (⟨x.1, hXK _ x.2⟩ : K) * s := hs
  rw [hφx]
  exact hS s.2 _

theorem hint_const_mul_sum {H ι : Type} [Group H] (A L : Subgroup H) (hLA : L ≤ A) (hfin : L.relIndex A ≠ 0)
    (s : Finset ι) (v : ι → H → ℂ) (c : ℂ) (hst : ∀ i ∈ s, L ≤ rStab (v i))
    (hsupp : ∀ i ∈ s, (Function.support fun q : H ⧸ L => v i q.out).Finite) :
    hint A (fun z => c * ∑ i ∈ s, v i z) = c * ∑ i ∈ s, hint A (v i) := by
  have hL : L ≤ rStab (fun z => c * ∑ i ∈ s, v i z) := by
    intro l hl z
    show c * ∑ i ∈ s, v i (z * l) = c * ∑ i ∈ s, v i z
    congr 1
    exact Finset.sum_congr rfl fun i hi => hst i hi hl z
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L _ hLA hL hfin,
    Finset.sum_congr rfl fun i hi => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L (v i) hLA (hst i hi) hfin,
    ← Finset.mul_sum]
  have h1 : ∑ᶠ q : H ⧸ L, c * ∑ i ∈ s, v i q.out = c * ∑ i ∈ s, ∑ᶠ q : H ⧸ L, v i q.out := by
    simp only [Finset.mul_sum]
    rw [finsum_sum_comm s (fun (q : H ⧸ L) i => c * v i q.out) fun i hi =>
      (hsupp i hi).subset fun q hq => right_ne_zero_of_mul hq]
    exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  rw [h1]
  ring

theorem support_finite {G H : Type} [Group G] [Group H] (L : Subgroup H) (K' : Subgroup G) (θ : H → G)
    (hθ : ∀ z z', (θ z)⁻¹ * θ z' ∈ K' → z⁻¹ * z' ∈ L) (f : G → ℂ) (hr : ∀ u ∈ K', ∀ g, f (g * u) = f g)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    (Function.support fun q : H ⧸ L => f (θ q.out)).Finite := by
  refine Set.Finite.of_finite_image (f := fun q : H ⧸ L => ((θ q.out : G) : G ⧸ K')) (hfin.subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (θ q.out)
    show f ((θ q.out : G) : G ⧸ K').out ≠ 0
    rw [hs, hr _ s.2]
    exact hq
  · intro q _ q' _ hqq
    have h2 : ((q.out : H) : H ⧸ L) = q'.out := QuotientGroup.eq.2 (hθ _ _ (QuotientGroup.eq.1 hqq))
    simpa using h2

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (ho : IsOpen (K' : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) : {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun i : G ⧸ K' => {g : G | i.out⁻¹ * g ∈ K'})
    (fun i => ho.preimage (continuous_const.mul continuous_id)) fun g _ =>
      Set.mem_iUnion.2 ⟨(g : G ⧸ K'), QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ K'))⟩
  refine t.finite_toSet.subset fun q hq => ?_
  obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have h1 : ((i.out : G) : G ⧸ K') = q.out := QuotientGroup.eq.2 hqi
  have h2 : i = q := by simpa using h1
  exact h2 ▸ hi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_toAdd_mul {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (Z l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd (Z * l)) =
      blk h w m (Multiplicative.toAdd Z) * blk h w 1 (Multiplicative.toAdd l) := by
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simp [add_comm]

theorem ct_eq_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ m, ct h w f m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, phi3 h w f x x m := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX f hf m
  have hbi : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g := fun u hu g =>
    ⟨by simpa using hf.2.2.2 u hu 1 K'.one_mem g, by simpa using hf.2.2.2 1 K'.one_mem u hu g⟩
  have hcos := finite_cosets K' hopen f hf.2.2.1
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hopen hle
  set L := (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) with hLdef
  have hmem : ∀ Y, Y ∈ L ↔ blk h w 1 (Multiplicative.toAdd Y) ∈ K' := fun Y => Iff.rfl
  have hstep : (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      avg fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Z) * k)) =
      fun Z => ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) :=
    funext fun Z => avg_conj _ K' X hXK hX f hbi _
  have hst : ∀ x ∈ X, L ≤ rStab (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) := by
    intro x hx l hl Z
    show f (x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x) = f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)
    have hU : x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x ∈ K' := by
      simpa using hnorm x⁻¹ ((GlobalTheory.LFun.KGL w (n := n)).inv_mem (hXK x hx)) _ ((hmem l).1 hl)
    have e : x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x =
        (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) * (x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x) := by
      rw [blk_toAdd_mul]; group
    rw [e]
    exact (hbi _ hU _).2
  have hsupp : ∀ x ∈ X, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd q.out) * x)).Finite := by
    intro x hx
    refine support_finite L K' (fun Z => x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) ?_ f
      (fun u hu g => (hbi u hu g).2) hcos
    intro z z' hz
    rw [hmem]
    have hb : blk h w m (Multiplicative.toAdd z') =
        blk h w m (Multiplicative.toAdd z) * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by
      rw [← blk_toAdd_mul, mul_inv_cancel_left]
    have e : (x⁻¹ * blk h w m (Multiplicative.toAdd z) * x)⁻¹ * (x⁻¹ * blk h w m (Multiplicative.toAdd z') * x) =
        x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x := by
      rw [hb]; group
    have hz' : x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x ∈ K' := e ▸ hz
    have := hnorm x (hXK x hx) _ hz'
    have e2 : x * (x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x) * x⁻¹ =
        blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by group
    rwa [e2] at this
  simp only [ct, phi3]
  rw [hstep, hint_const_mul_sum (intMat a b w) L hLA hfin X
    (fun x Z => f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) _ hst hsupp, ← Finset.mul_sum]
  ring

end GlobalTheory.CompanionTheory.DiagAvg
end
end

section


theorem _root_.GlobalTheory.T.finite_level_facts : PositivityTheory.Rg.BcB.G8.FinLevel := by
  first | exact @GlobalTheory.CompanionTheory.FinLevelTw.finLevel | exact GlobalTheory.CompanionTheory.FinLevelTw.finLevel | (intros; apply GlobalTheory.CompanionTheory.FinLevelTw.finLevel <;> assumption)
end

section


theorem _root_.GlobalTheory.T.finite_kernel_compact_open : PositivityTheory.Rg.BcB.G8.KfOC := by
  first | exact @GlobalTheory.CompanionTheory.IntegralPoints.kfOC | exact GlobalTheory.CompanionTheory.IntegralPoints.kfOC | (intros; apply GlobalTheory.CompanionTheory.IntegralPoints.kfOC <;> assumption)
end

section

noncomputable section

open GlobalTheory.BCT

namespace GlobalTheory.CompanionTheory.MassProd

section Cards

variable {A B C : Type} [Group A] [Group B] [Group C]

theorem card_doubleCoset (e : C ≃* A × B) (H K : Subgroup A) (H' K' : Subgroup B) (H'' K'' : Subgroup C)
    (hH : ∀ c, c ∈ H'' ↔ (e c).1 ∈ H ∧ (e c).2 ∈ H') (hK : ∀ c, c ∈ K'' ↔ (e c).1 ∈ K ∧ (e c).2 ∈ K') :
    Nat.card (DoubleCoset.Quotient (H'' : Set C) (K'' : Set C)) =
      Nat.card (DoubleCoset.Quotient (H : Set A) (K : Set A)) *
        Nat.card (DoubleCoset.Quotient (H' : Set B) (K' : Set B)) := by
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let F : C → DoubleCoset.Quotient (H : Set A) (K : Set A) × DoubleCoset.Quotient (H' : Set B) (K' : Set B) :=
    fun c => (DoubleCoset.mk H K (e c).1, DoubleCoset.mk H' K' (e c).2)
  have hF : ∀ x y : C, F x = F y ↔ DoubleCoset.mk H'' K'' x = DoubleCoset.mk H'' K'' y := by
    intro x y
    simp only [F, Prod.mk.injEq, DoubleCoset.eq]
    constructor
    · rintro ⟨⟨h, hh, k, hk, h1⟩, h', hh', k', hk', h2⟩
      refine ⟨e.symm (h, h'), ?_, e.symm (k, k'), ?_, ?_⟩
      · rw [hH]; simpa using ⟨hh, hh'⟩
      · rw [hK]; simpa using ⟨hk, hk'⟩
      · apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact Prod.ext (by simpa using h1) (by simpa using h2)
    · rintro ⟨h, hh, k, hk, rfl⟩
      rw [hH] at hh
      rw [hK] at hk
      exact ⟨⟨_, hh.1, _, hk.1, by simp⟩, _, hh.2, _, hk.2, by simp⟩
  refine Equiv.ofBijective (Quotient.lift F fun x y h => (hF x y).2 (Quotient.sound h)) ⟨?_, ?_⟩
  · intro p q
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    intro h
    exact (hF x y).1 h
  · rintro ⟨p, q⟩
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    refine ⟨DoubleCoset.mk H'' K'' (e.symm (x, y)), ?_⟩
    show F (e.symm (x, y)) = _
    simp [F]

end Cards

section Top

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

theorem twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ : G) (δ' : G') :
    twCent (θ.prodMap θ') (δ, δ') = (twCent θ δ).prod (twCent θ' δ') := by
  ext ⟨a, b⟩
  show (a, b) * (δ, δ') = (δ, δ') * (θ a, θ' b) ↔ a * δ = δ * θ a ∧ b * δ' = δ' * θ' b
  simp [Prod.ext_iff]

theorem compactPowers_prod (a : G) (b : G') :
    IsCompact (closure (Subgroup.zpowers ((a, b) : G × G') : Set (G × G'))) ↔
      IsCompact (closure (Subgroup.zpowers a : Set G)) ∧ IsCompact (closure (Subgroup.zpowers b : Set G')) := by
  constructor
  · intro h
    constructor
    · refine (h.image continuous_fst).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
    · refine (h.image continuous_snd).closure_of_subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨(a, b) ^ n, subset_closure ⟨n, rfl⟩, by simp⟩
  · rintro ⟨h, h'⟩
    refine (h.prod h').closure_of_subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨subset_closure ⟨n, by simp⟩, subset_closure ⟨n, by simp⟩⟩

theorem cptPart_prod (T : Subgroup G) (T' : Subgroup G') :
    cptPart (T.prod T') = (cptPart T).prod (cptPart T') := by
  have h1 : ∀ {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X],
      IsCompact (closure (Subgroup.zpowers (1 : X) : Set X)) := by
    intro X _ _ _
    simpa using (isCompact_singleton (x := (1 : X))).closure
  unfold cptPart
  have hs : (1 : G) ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := ⟨T.one_mem, h1⟩
  have hs' : (1 : G') ∈ {t | t ∈ T' ∧ IsCompact (closure (Subgroup.zpowers t : Set G'))} := ⟨T'.one_mem, h1⟩
  rw [← Subgroup.closure_prod hs hs']
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_prod, compactPowers_prod, Subgroup.mem_prod]
  tauto

theorem card_inf_prod (Γ C : Subgroup G) (Γ' C' : Subgroup G') :
    Nat.card (Γ.prod Γ' ⊓ C.prod C' : Subgroup (G × G')) =
      Nat.card (Γ ⊓ C : Subgroup G) * Nat.card (Γ' ⊓ C' : Subgroup G') := by
  have h : Γ.prod Γ' ⊓ C.prod C' = (Γ ⊓ C).prod (Γ' ⊓ C') := by
    ext ⟨a, b⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_prod]
    tauto
  rw [h, ← Nat.card_prod]
  exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv

end Top

theorem massProd : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  intro G G' _ _ _ _ _ _ θ θ' Γ Γ' δ δ'
  unfold mass
  rw [twCent_prodMap, cptPart_prod, card_inf_prod]
  rw [card_doubleCoset (Subgroup.prodEquiv (twCent θ δ) (twCent θ' δ'))
    (Γ.subgroupOf (twCent θ δ)) ((cptPart (twCent θ δ)).subgroupOf (twCent θ δ))
    (Γ'.subgroupOf (twCent θ' δ')) ((cptPart (twCent θ' δ')).subgroupOf (twCent θ' δ'))
    _ _ (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)
    (fun c => by simp only [Subgroup.mem_subgroupOf, Subgroup.mem_prod]; exact Iff.rfl)]
  push_cast
  rw [mul_div_mul_comm]

end GlobalTheory.CompanionTheory.MassProd

end
end

section


theorem _root_.GlobalTheory.T.archimedean_local_global_dictionary : PositivityTheory.RgEis.DictInf := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.dictInf | exact GlobalTheory.CompanionTheory.RgEis.dictInf | (intros; apply GlobalTheory.CompanionTheory.RgEis.dictInf <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.isotropic_hyperbolic_complement : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ), Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 → ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool), Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧ C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | exact GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | (intros; apply GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame <;> assumption)
end
