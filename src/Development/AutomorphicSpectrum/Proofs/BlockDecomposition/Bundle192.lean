module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle182
public import GroundTheory.GlobalFields.TateThesis.AdeleIdealMeasure
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.AutomorphicForms.LocallyProfinite
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

open GlobalTheory.CompanionTheory.CupRep

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) :
    Ideal.Quotient.mk T.J (liftV T h g) = ev T h g :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T h g))

theorem liftV_sub_map_mem {V : X.Opens} {T T' : Thick (smFun X q)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T')
    (g : Γ(X, V)) : liftV T' h' g - φ.φ (liftV T h g) ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [mk_liftV]
  have e : Ideal.Quotient.mk T'.J (φ.φ (liftV T h g)) =
      Ideal.quotientMap T'.J φ.φ φ.hle (Ideal.Quotient.mk T.J (liftV T h g)) := (Ideal.quotientMap_mk).symm
  rw [e, mk_liftV]
  exact GlobalTheory.CompanionTheory.GrForm.ev_nat φ h h' g

theorem liftV_add_mem {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (x y : Γ(X, V)) :
    liftV T h x + liftV T h y - liftV T h (x + y) ∈ T.J := by
  refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [map_sub, map_add (f := _), mk_liftV, mk_liftV, mk_liftV, map_add (f := _), sub_self]

variable (s : ℕ) (V : X.Opens)

theorem addC_mem (g : Γ(X, V)) :
    addC (KS q s {V}) (fun T => liftV T.obj (ks_in q s V T.obj T.property) g) ∈
      FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
  refine mem_FC.2 fun u => ?_
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  rw [Nat.cast_one, hF.one]
  exact liftV_sub_map_mem (u.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom _ _ g

theorem cupList_mem {d : ℕ} (l : Fin d → CH.Cn (CH.modF (sP (KS q s {V})).A) 1)
    (hl : ∀ k, l k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1) :
    cupListC (sP (KS q s {V})).A l ∈ FC (sFil (KS q s {V}) ((d : ℕ) : ℤ)) d := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  induction d with
  | zero =>
    refine mem_FC.2 fun u => ?_
    rw [hF.top _ (by simp)]
    trivial
  | succ n ih =>
    exact cup_mem hF (by omega) (ih _ fun i => hl _) (hl (Fin.last n))

theorem xdtC_val {d : ℕ} (t : Fin d → Γ(X, V)) (x : Γ(X, V)) (u : ComposableArrows (KS q s {V}).FullSubcategory d) :
    vl (xdtC (q := q) s V t x) u =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) *
      vl (cupListC (sP (KS q s {V})).A fun k =>
        addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)) u :=
  congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last d)) =>
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) * b)
    (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))

end GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

namespace GlobalTheory.CompanionTheory.ConeLocal

open GlobalTheory.CompanionTheory.CupRep XdtAdd

theorem rep_xdtC_add {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (s : ℕ) (V : X.Opens)
    {d : ℕ} (t : Fin d → Γ(X, V)) (x y : Γ(X, V)) (a b : HQ (KS q s {V}) d ((d : ℤ) + 1) d)
    (ha : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t x) a)
    (hb : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t y) b) :
    Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t (x + y)) (a + b) := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  refine rep_congr (rep_add ha hb) fun u => ?_
  have hc := mem_FC.1 (cupList_mem s V (fun k => addC (KS q s {V}) fun T =>
    liftV T.obj (ks_in q s V T.obj T.property) (t k)) fun k => addC_mem s V (t k)) u
  let T0 := u.obj (CH.front (Nat.zero_add d) (Fin.last 0))
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0))))
  have h1 : ((sP (KS q s {V})).A.map ψ).hom
      (liftV T0.obj (ks_in q s V _ T0.property) x + liftV T0.obj (ks_in q s V _ T0.property) y -
        liftV T0.obj (ks_in q s V _ T0.property) (x + y)) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact (sP (KS q s {V})).J.map_mem ψ (liftV_add_mem T0.obj _ x y)
  have h2 := hF.mul 1 d _ h1 hc
  have e : ((1 + d : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
  rw [e] at h2
  change vl (xdtC (q := q) s V t x) u + vl (xdtC (q := q) s V t y) u - vl (xdtC (q := q) s V t (x + y)) u ∈ _
  rw [xdtC_val, xdtC_val, xdtC_val]
  convert h2 using 1
  rw [map_sub, map_add (f := _)]
  ring

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeFinite

universe u v u' v'

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem pull_sqC_comb (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} {c c₁ c₂ e e' : R'}
    (hc : c = e * c₁ + e' * c₂) (ha : m.LeC c a a') (hb : m.LeC c b b') (ha₁ : m.LeC c₁ a a') (hb₁ : m.LeC c₁ b b')
    (ha₂ : m.LeC c₂ a a') (hb₂ : m.LeC c₂ b b') (j : ℕ) (x : CH.H (sq a b) j) :
    (m.sqC c ha hb).pull j x =
      e • (m.sqC c₁ ha₁ hb₁).pull j x + e' • (m.sqC c₂ ha₂ hb₂).pull j x := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = e • Submodule.Quotient.mk _ + e' • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  refine congrArg _ (Subtype.ext (funext fun s => ?_))
  change (m.sqC c ha hb).τ _ (f (s ⋙ m.G)) =
    e • (m.sqC c₁ ha₁ hb₁).τ _ (f (s ⋙ m.G)) + e' • (m.sqC c₂ ha₂ hb₂).τ _ (f (s ⋙ m.G))
  generalize f (s ⋙ m.G) = w
  obtain ⟨z, hz⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine Subtype.ext ?_
  have key : algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c * m.ρ (s.obj (Fin.last j)) y =
      e • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₁ * m.ρ (s.obj (Fin.last j)) y) +
      e' • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₂ * m.ρ (s.obj (Fin.last j)) y) := by
    rw [hc, map_add (f := _), map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  exact congrArg (Ideal.Quotient.mk (b'.S (s.obj (Fin.last j)))) key

theorem exists_fg_pull_sqC (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (P : Ideal R') (hP : P.FG)
    (h₁ : ∀ c ∈ P, m.LeC c a a') (h₂ : ∀ c ∈ P, m.LeC c b b') (j : ℕ) (hfin : Module.Finite R (CH.H (sq a b) j)) :
    ∃ N : Submodule R' (CH.H (sq a' b') j), N.FG ∧ ∀ (c : R') (ha : m.LeC c a a') (hb : m.LeC c b b'), c ∈ P →
      ∀ x, (m.sqC c ha hb).pull j x ∈ N := by
  classical
  obtain ⟨G, rfl⟩ := hP
  obtain ⟨X, hX⟩ := (Module.Finite.fg_top : (⊤ : Submodule R (CH.H (sq a b) j)).FG)
  let φ : G × X → CH.H (sq a' b') j := fun p =>
    (m.sqC p.1.1 (h₁ _ (Ideal.subset_span p.1.2)) (h₂ _ (Ideal.subset_span p.1.2))).pull j p.2.1
  refine ⟨Submodule.span R' (Set.range φ), Submodule.fg_span (Set.finite_range φ), ?_⟩
  have hgen : ∀ (g : R') (hg : g ∈ G) (ha : m.LeC g a a') (hb : m.LeC g b b') (x : CH.H (sq a b) j),
      (m.sqC g ha hb).pull j x ∈ Submodule.span R' (Set.range φ) := by
    intro g hg ha hb x
    have hx : x ∈ Submodule.span R (X : Set (CH.H (sq a b) j)) := hX ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨(⟨g, hg⟩, ⟨x, hx⟩), rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  intro c ha hb hc x
  refine Submodule.span_induction
    (p := fun c _ => ∀ (ha : m.LeC c a a') (hb : m.LeC c b b'), (m.sqC c ha hb).pull j x ∈ Submodule.span R' (Set.range φ))
    ?_ ?_ ?_ ?_ hc ha hb
  · intro g hg ha hb
    exact hgen g hg ha hb x
  · intro ha hb
    rw [pull_sqC_comb m (c₁ := 0) (c₂ := 0) (e := 0) (e' := 0) (by simp) ha hb ha hb ha hb j x]
    simp
  · intro c₁ c₂ m₁ m₂ i₁ i₂ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₂) (e := 1) (e' := 1) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₂) (h₂ _ m₂) j x]
    simpa using add_mem (i₁ (h₁ _ m₁) (h₂ _ m₁)) (i₂ (h₁ _ m₂) (h₂ _ m₂))
  · intro e c₁ m₁ i₁ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₁) (e := e) (e' := 0) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₁) (h₂ _ m₁) j x]
    simpa using Submodule.smul_mem _ e (i₁ (h₁ _ m₁) (h₂ _ m₁))

end General

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') :
    pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, h₁, h₂, h₃⟩ => ⟨l, h₁, h.trans h₂, h₃⟩

theorem tfBase_mono {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {l m s : ℕ} (h : TFBase δ l m)
    (hms : m ≤ s) : TFBase δ l s :=
  ⟨le_bot_iff.1 (h.nil ▸ dividedPowerFiltration_anti δ hms), h.tf, h.dv⟩

theorem afgA_of_bcOn_finO : BcOn False → FinO → AfgA := by
  intro hB hF O A _ _ _ _ _ I γ l s m hl hO hL hms X q _ U 𝒱 h𝒱 r r' hr hr' j
  obtain ⟨S⟩ := GlobalTheory.T.graded_splitting_over_lattice_base γ l m hl hL
  have hA : TFBase γ l s := tfBase_mono hL.tf hms
  have hC : ∀ (i : Fin m) (t : ℤ) (c : A), c ∈ pdP γ i →
      (smO γ q l s 𝒱).LeC c (sFil _ (t - i)) (sFil _ t) :=
    fun i t c hc => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s 𝒱 i c hc t
  have ha : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
    fun i n => hC i r _ (S.mem i n)
  have hb : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r' - i)) (sFil _ r') :=
    fun i n => hC i r' _ (S.mem i n)
  obtain ⟨g, hg⟩ := hB γ l s m hO hA S q 𝒱 (Or.inr ⟨not_false, ⟨U⟩, h𝒱⟩) r r' hr hr' ha hb j
  have hN : ∀ i : Fin m, ∃ N : Submodule A (HQ (TS γ q l s 𝒱) r r' j), N.FG ∧
      ∀ n x, ((smO γ q l s 𝒱).sqC (S.ν i n) (ha i n) (hb i n)).pull j x ∈ N := by
    intro i
    have hi : (0 : ℤ) ≤ (i : ℕ) := Int.natCast_nonneg _
    obtain ⟨N, h₁, h₂⟩ := exists_fg_pull_sqC (smO γ q l s 𝒱) (pdP γ i) (hL.fg i) (fun c hc => hC i r c hc)
      (fun c hc => hC i r' c hc) j (hF l s hO q U 𝒱 h𝒱 (r - i) (r' - i) (by omega) (by omega) j)
    exact ⟨N, h₁, fun n x => h₂ _ _ _ (S.mem i n) x⟩
  choose N hNfg hNmem using hN
  refine ⟨0, ⨆ i, N i, Submodule.fg_iSup _ hNfg, fun y => ?_⟩
  rw [pow_zero, one_smul]
  have hsingle : ∀ (i : Fin m) (t : S.N i ⊗[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j),
      g (Pi.single i t) ∈ ⨆ i, N i := by
    intro i t
    induction t using TensorProduct.inductionOn with
    | tmul n x => rw [hg]; exact Submodule.mem_iSup_of_mem i (hNmem i n x)
    | add t t' ht ht' => rw [Pi.single_add, map_add (f := _)]; exact add_mem ht ht'
  have hy : y = ∑ i, g (Pi.single i (g.symm y i)) := by

    rw [← map_sum, Finset.univ_sum_single, g.apply_symm_apply]
  rw [hy]
  exact sum_mem fun i _ => hsingle i _

end GlobalTheory.CompanionTheory.LatticeFinite
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EpConvB

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors
open GroundTheory.Global GroundTheory.Automorphic

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) : ℝ :=
  if y.2 ∈ idealFiniteAdeles L then ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ else 0

theorem adeleWeight_nonneg (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    0 ≤ adeleWeight L A y := by
  unfold adeleWeight
  split_ifs <;> positivity

theorem adeleWeight_le_one (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ 1 := by
  unfold adeleWeight
  split_ifs
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (homeomorphMixedSpace K y.1)]))
  · exact zero_le_one

theorem adeleWeight_mono {L L' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : (L : FractionalIdeal (𝓞 K)⁰ K) ≤ L') (A : ℕ) (y : 𝔸[K]) :
    adeleWeight L A y ≤ adeleWeight L' A y := by
  unfold adeleWeight
  by_cases h1 : y.2 ∈ idealFiniteAdeles L
  · have h2 : y.2 ∈ idealFiniteAdeles L' := idealFiniteAdeles_subset h h1
    simp only [if_pos h1, if_pos h2, le_refl]
  · rw [if_neg h1]
    split_ifs
    · positivity
    · exact le_rfl

@[simp] theorem adeleWeight_zero (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    adeleWeight L A (0 : 𝔸[K]) = 1 := by
  have h0 : (0 : 𝔸[K]).2 ∈ idealFiniteAdeles L := zero_mem _
  have h1 : homeomorphMixedSpace K (0 : 𝔸[K]).1 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  unfold adeleWeight
  rw [if_pos h0, h1]
  simp

theorem continuous_adeleWeight (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (A : ℕ) :
    Continuous (adeleWeight (K := K) L A) := by
  have hc : IsClopen ((idealFiniteAdeles L : AddSubgroup 𝔸ᶠ[K]) : Set 𝔸ᶠ[K]) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_idealFiniteAdeles L), isOpen_idealFiniteAdeles L⟩
  have hc' : IsClopen {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L} := hc.preimage continuous_snd
  have hf : Continuous fun y : 𝔸[K] ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun y ↦ ?_
    have := norm_nonneg (homeomorphMixedSpace K y.1)
    positivity
  have : adeleWeight (K := K) L A = Set.indicator {y : 𝔸[K] | y.2 ∈ idealFiniteAdeles L}
      (fun y ↦ ((1 + ‖homeomorphMixedSpace K y.1‖) ^ A)⁻¹) := by
    funext y
    simp only [adeleWeight, Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact hf.indicator (by rw [hc'.frontier_eq]; simp)
end

end GlobalTheory.CompanionTheory.EpConvB
end

section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.DimChart

theorem isIso_residueFieldMap {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    IsIso (j.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
  refine ⟨Y.residue _ c, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
  rfl

noncomputable def residueFieldEquiv {Y : Scheme.{0}} {B : Type} [CommRing B] (j : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] (q : PrimeSpectrum B) :
    Y.residueField (j q) ≃+* q.asIdeal.ResidueField :=
  haveI := isIso_residueFieldMap j q
  (asIso (j.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso (.of B) q).commRingCatIsoToRingEquiv

theorem trdeg_int_eq_of_isFractionRing (A : Type) [CommRing A] [IsDomain A] [Algebra ℤ A] (L : Type)
    [Field L] [Algebra ℤ L] [Algebra A L] [IsFractionRing A L]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ L := by
  obtain rfl : ‹Algebra ℤ A› = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A L)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hA
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  rw [← trdeg_add_eq ℤ A (A := L), trdeg_eq_zero (R := A) (A := L), add_zero]

theorem trdeg_int_eq_of_ringEquiv {L L' : Type} [CommRing L] [CommRing L'] [Algebra ℤ L]
    [Algebra ℤ L'] (e : L ≃+* L') : Algebra.trdeg ℤ L = Algebra.trdeg ℤ L' := by
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L'› = Ring.toIntAlgebra L' := Subsingleton.elim _ _
  exact e.toIntAlgEquiv.trdeg_eq

theorem ringKrullDim_quotient_eq (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (h0 : CharZero (Y.residueField (j q))) :
    ringKrullDim (B ⧸ q.asIdeal) =
      (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  have e := residueFieldEquiv j q
  have : CharZero q.asIdeal.ResidueField := charZero_of_injective_ringHom (f := e.toRingHom) e.injective
  have hinj : Function.Injective (algebraMap ℤ (B ⧸ q.asIdeal)) := by
    have hK : Function.Injective
        ((algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp (algebraMap ℤ (B ⧸ q.asIdeal))) := by
      rw [show (algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp
        (algebraMap ℤ (B ⧸ q.asIdeal)) = Int.castRingHom _ from Subsingleton.elim _ _]
      exact Int.cast_injective
    rw [RingHom.coe_comp] at hK
    exact Function.Injective.of_comp hK
  have : Algebra.FiniteType ℤ (B ⧸ q.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q.asIdeal) (Ideal.Quotient.mkₐ_surjective _ _)
  rw [GroundTheory.Heights₂.Heights.IntDomainDim.proof (B ⧸ q.asIdeal) hinj,
    trdeg_int_eq_of_isFractionRing (B ⧸ q.asIdeal) q.asIdeal.ResidueField hinj,
    trdeg_int_eq_of_ringEquiv e.symm]

end GlobalTheory.CompanionTheory.DimChart
end

section

noncomputable section

open PositivityTheory.jumpWindows
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothVectors

theorem contDiffOn_of_fderiv_family {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ} {U : Set E} (hU : IsOpen U)
    (o : P → E → F) (S : Set P) (A : Fin n → E → E →L[ℝ] ℝ)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) U)
    (h : ∀ v ∈ S, ∃ w : Fin n → P, (∀ i, w i ∈ S) ∧
      ∀ M ∈ U, HasFDerivAt (o v) (∑ i, (A i M).smulRight (o (w i) M)) M) :
    ∀ v ∈ S, ContDiffOn ℝ ∞ (o v) U := by
  have key : ∀ m : ℕ, ∀ v ∈ S, ContDiffOn ℝ m (o v) U := by
    intro m
    induction m with
    | zero =>
      intro v hv
      obtain ⟨w, -, hw⟩ := h v hv
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun M hM => (hw M hM).continuousAt.continuousWithinAt
    | succ m ih =>
      intro v hv
      obtain ⟨w, hwS, hw⟩ := h v hv
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun M hM => (hw M hM).differentiableAt.differentiableWithinAt, fun hm => ?_, ?_⟩
      · exact absurd hm (by simp)
      · refine ContDiffOn.congr (f := fun M => ∑ i, (A i M).smulRight (o (w i) M)) ?_
          fun M hM => (hw M hM).fderiv
        exact ContDiffOn.sum fun i _ =>
          (contDiffOn_infty.1 (hA i) m).smulRight (ih (w i) (hwS i))
  intro v hv
  exact contDiffOn_infty.2 fun m => key m v hv

section Chart

variable {ι : Type} [Fintype ι] {a : ℕ}

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

end Norm

end Chart

section Orbit

variable {ι : Type} [Fintype ι] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

end Orbit

end GlobalTheory.CompanionTheory.SmoothVectors

end
end
