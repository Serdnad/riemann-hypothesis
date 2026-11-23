module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscrMulHermitianIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.cuspFlow_eq_torusAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  first | exact @GlobalTheory.CuspFlow.flow_eq_zAct | exact GlobalTheory.CuspFlow.flow_eq_zAct | (intros; apply GlobalTheory.CuspFlow.flow_eq_zAct <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters

theorem scale_tangent_pow (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ) (hn : 0 < n) (hv : IsTangent v) :
    spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  have h : GrpTangent.epsScale ((n : ℂ)⁻¹) ≫ (v ^ n) = v := by
    rw [GrpTangent.pow_eq_epsScale_comp hv, GrpTangent.epsScale_mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'),
      GrpTangent.epsScale_one, Category.id_comp]
  exact congrArg (fun φ => φ.left) h

end GlobalTheory.AbelianLetters
end
end

section

namespace GlobalTheory

theorem exists_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] :
    ∃ q : Y → ℕ, (∀ x y, q (x - y) ≤ q x + q y) ∧ (∀ (m : ℕ) y, q (m • y) = m * q y) ∧
      ∀ y, q y = 0 → y = 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ Y
  refine ⟨fun y => ∑ i, (b.repr y i).natAbs, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub, Finsupp.sub_apply]
    exact Int.natAbs_sub_le _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    apply b.repr.injective
    ext i
    simpa using hy i (Finset.mem_univ i)

theorem exists_invariant_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) :
    ∃ p : Y → ℕ, (∀ x y, p (x - y) ≤ p x + p y) ∧ (∀ (m : ℕ) y, p (m • y) = m * p y) ∧
      (∀ y, p y = 0 → y = 0) ∧ ∀ y, p (σ y) = p y := by
  obtain ⟨q, h1, h2, h3⟩ := exists_nat_length_lattice Y
  refine ⟨fun y => ∑ j ∈ Finset.range n, q ((σ ^ j) y), ?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_sub]
    exact h1 _ _
  · intro m y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, h2]
  · intro y hy
    rw [Finset.sum_eq_zero_iff] at hy
    have := hy 0 (Finset.mem_range.mpr hn)
    exact h3 y (by simpa using this)
  · intro y
    have e1 := Finset.sum_range_succ (fun j => q ((σ ^ j) y)) n
    have e2 := Finset.sum_range_succ' (fun j => q ((σ ^ j) y)) n
    have e3 : ∑ j ∈ Finset.range n, q ((σ ^ j) (σ y)) =
        ∑ j ∈ Finset.range n, q ((σ ^ (j + 1)) y) :=
      Finset.sum_congr rfl fun j _ => by rw [pow_succ, Module.End.mul_apply]
    rw [hσ] at e1
    rw [pow_zero] at e2
    simp only [e3]
    omega

theorem end_eq_one_of_pow_eq_one_of_congr (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n M : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) (hM : 3 ≤ M)
    (h : ∀ y, ∃ z, σ y = y + M • z) : σ = 1 := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_invariant_nat_length_lattice Y σ n hn hσ
  have key : ∀ (k : ℕ) (y : Y), p y = k → σ y = y := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro y hy
      obtain ⟨z, hz⟩ := h y
      rcases Nat.eq_zero_or_pos k with hk | hk
      · have : y = 0 := h3 y (hy.trans hk)
        rw [this, map_zero]
      have hle : M * p z ≤ k + k := by
        have := h1 (σ y) y
        rw [h4, hy, hz, add_sub_cancel_left, h2] at this
        exact this
      have hlt : p z < k := by nlinarith
      have hzz : σ z = z := ih _ hlt z rfl
      have hj : ∀ j : ℕ, (σ ^ j) y = y + (j * M) • z := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          rw [pow_succ', Module.End.mul_apply, ihj, map_add (f := _), map_nsmul, hzz, hz, add_mul, one_mul,
            add_smul]
          abel
      have h0 : (n * M) • z = 0 := by
        have := hj n
        rw [hσ, Module.End.one_apply] at this
        exact left_eq_add.mp this
      have h00 : p z = 0 := by
        have e := h2 (n * M) z
        have e0 := h2 0 z
        rw [zero_smul, zero_mul] at e0
        rw [h0, e0] at e
        have : 0 < n * M := Nat.mul_pos hn (by omega)
        rcases Nat.mul_eq_zero.mp e.symm with h' | h'
        · omega
        · exact h'
      rw [hz, h3 z h00, smul_zero, add_zero]
  ext y
  exact key _ y rfl

theorem latMinkowski : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatMinkowskiSt := by
  intro Y _ _ _ σ n M hn hσ hM h
  have hp : (σ : Module.End ℤ Y) ^ n = 1 := by
    ext y
    have : (σ ^ n) y = y := by rw [hσ]; rfl
    rw [LinearEquiv.pow_apply] at this
    rw [Module.End.pow_apply]
    exact this
  have := end_eq_one_of_pow_eq_one_of_congr Y (σ : Module.End ℤ Y) n M hn hp hM h
  ext y
  exact LinearMap.congr_fun this y

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_pow_eq_one_of_posDef_form (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (b : LinearMap.BilinForm ℤ Y) (hs : ∀ y z, b y z = b z y) (hp : ∀ y, y ≠ 0 → 0 < b y y)
    (σ : Y ≃ₗ[ℤ] Y) (hσ : ∀ y z, b (σ y) (σ z) = b y z) : ∃ n : ℕ, 0 < n ∧ σ ^ n = 1 := by
  classical
  rw [← isOfFinOrder_iff_pow_eq_one]
  by_contra hfin
  have hinj := injective_pow_iff_not_isOfFinOrder.mpr hfin
  let e := Module.Free.chooseBasis ℤ Y
  have h0 : ∀ y, 0 ≤ b y y := fun y => by
    by_cases h : y = 0
    · simp [h]
    · exact (hp y h).le
  have hpow : ∀ (n : ℕ) y, b ((σ ^ n) y) ((σ ^ n) y) = b y y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ', LinearEquiv.mul_apply, hσ, ih]
  have hnd : ∀ y, (∀ j, b y (e j) = 0) → y = 0 := by
    intro y hy
    by_contra h
    have : b y = 0 := e.ext fun j => by simpa using hy j
    have h2 := hp y h
    simp [this] at h2
  let f : ℕ → (_ → _ → ℤ) := fun n i j => b ((σ ^ n) (e i)) (e j)
  have hf : Function.Injective f := by
    intro m n h
    apply hinj
    apply LinearEquiv.toLinearMap_injective
    refine e.ext fun i => ?_
    rw [← sub_eq_zero]
    apply hnd
    intro j
    have := congrFun (congrFun h i) j
    simp only [f] at this
    simp [this]
  let C : _ → _ → ℤ := fun i j => b (e i) (e i) * b (e j) (e j)
  have hS : (Set.univ.pi fun i => Set.univ.pi fun j => Set.Icc (-C i j) (C i j)).Finite :=
    Set.Finite.pi fun i => Set.Finite.pi fun j => Set.finite_Icc _ _
  refine Set.infinite_of_injective_forall_mem hf (fun n => ?_) hS
  intro i _ j _
  have h1 := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le b h0 ((σ ^ n) (e i)) (e j)
  rw [hpow, hs (e j), hs (e j)] at h1
  have h2 : f n i j ^ 2 ≤ C i j := by
    simp only [f, C]; nlinarith [h1]
  constructor <;> nlinarith [h2, sq_nonneg (f n i j - 1), sq_nonneg (f n i j + 1), Int.le_self_sq (f n i j), Int.le_self_sq (-f n i j)]

theorem latFinOrdSt : ReciprocityTheory.ChartRestriction.G.Geo.Tor.LatFinOrdSt :=
  fun Y _ _ _ b hs hp σ hσ => exists_pow_eq_one_of_posDef_form Y b hs hp σ hσ

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_iso_pull_cancel {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} (hL : L.IsLB)
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {φ₁ : X'' ⟶ X} {φ₂ : X' ⟶ X} {θ : X'' ⟶ X'} (h : θ ≫ φ₂ = φ₁)
    (w₁ : LB.Iso L'' (L.pull φ₁)) (w₂ : LB.Iso L' (L.pull φ₂)) (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ (wθ : LB.Iso L'' (L'.pull θ)) (w₁' : LB.Iso L'' (L.pull (θ ≫ φ₂))),
      wθ.IsGen ∧ HEq w₁' w₁ ∧ Tri w₂ wθ w₁' := by
  subst h
  obtain ⟨wθ, T⟩ := exists_cancel hL w₂ w₁ ((isGen_iff _).1 g₂) ((isGen_iff _).1 g₁) hL' hL''
  exact ⟨wθ, w₁, (isGen_iff _).2 (T.pgen_cancel hL ((isGen_iff _).1 g₂) ((isGen_iff _).1 g₁)), HEq.rfl, T⟩

end GlobalTheory
end
end

section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace GlobalTheory

theorem exists_point_over_dominant_geometric_point {U S : Scheme.{u}} (g : U ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] [Nonempty U] {F : Type u} [Field F]
    [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t] :
    ∃ j : Spec (.of F) ⟶ U, j ≫ g = t := by
  obtain ⟨z, u, hu⟩ := t.denseRange.exists_mem_open g.isOpenMap.isOpen_range
    (Set.range_nonempty _)
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := t) u z hu
  have : JacobsonSpace ↥(pullback g t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g t)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback g t)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd g t) c hc ≫ pullback.fst g t, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem eq_of_dominant_geometric_points_of_unramified {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] (g : T ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] {a b : T ⟶ X} (ha : a ≫ f = g) (hb : b ≫ f = g)
    {F : Type u} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (h : ∀ j : Spec (.of F) ⟶ T, j ≫ g = t → j ≫ a = j ≫ b) : a = b := by
  have hab : a ≫ f = b ≫ f := ha.trans hb.symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  by_contra hne
  let U : T.Opens := ⟨(Set.range (equalizer.ι a b))ᶜ,
    (equalizer.ι a b).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hne
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨j, hj⟩ := exists_point_over_dominant_geometric_point (U.ι ≫ g) t
  have h1 := range_subset_range_equalizer_ι (j ≫ U.ι) (h _ (by simpa using hj))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have h2 : (j ≫ U.ι) p ∈ U := by
    rw [Scheme.Hom.comp_apply]
    exact (j p).2
  exact h2 (h1 ⟨_, rfl⟩)

theorem fix_torsion_of_fix_geometric_of_etale {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : ℕ)
    [Etale (mulA A M).left] [IsSeparated (mulA A M).left]
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : A ⟶ A) [IsMonHom s]
    (hs : ∀ x : Over.mk t ⟶ A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ A) (hx : x ^ M = 1) : x ≫ s = x := by
  have hmul : ∀ {Z : Over S} (y : Z ⟶ A), y ≫ mulA A M = y ^ M := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let K : Over S := Over.mk (pullback.snd (mulA A M).left η[A].left)
  have hη : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  let i : K ⟶ A := Over.homMk (pullback.fst (mulA A M).left η[A].left) (by
    change pullback.fst (mulA A M).left η[A].left ≫ A.hom = pullback.snd (mulA A M).left η[A].left
    rw [← Over.w (mulA A M), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hi : i ^ M = 1 := by
    rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    exact pullback.condition
  have hlift : ∀ {Z : Over S} (y : Z ⟶ A), y ^ M = 1 → ∃ l : Z ⟶ K, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA A M).left = Z.hom ≫ η[A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over S} (l l' : Z ⟶ K), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  obtain ⟨σ, hσ⟩ := hlift (i ≫ s) (by rw [← MonObj.pow_comp, hi, MonObj.one_comp])
  have hEt : Etale K.hom := inferInstanceAs (Etale (pullback.snd (mulA A M).left η[A].left))
  have hSep : IsSeparated K.hom :=
    inferInstanceAs (IsSeparated (pullback.snd (mulA A M).left η[A].left))
  have key : σ = 𝟙 K := by
    apply Over.OverMorphism.ext
    refine eq_of_dominant_geometric_points_of_unramified K.hom K.hom (Over.w σ) (Over.w (𝟙 K)) t ?_
    intro j hj
    let j' : Over.mk t ⟶ K := Over.homMk j hj
    have : j' ≫ σ = j' ≫ 𝟙 K := by
      apply hmono
      rw [Category.assoc, hσ, Category.comp_id, ← Category.assoc]
      exact hs _ (by rw [← MonObj.comp_pow, hi, MonObj.comp_one])
    exact congr(($this).left)
  obtain ⟨l, rfl⟩ := hlift x hx
  rw [Category.assoc, ← hσ, key, Category.id_comp]

theorem fix_torsion_of_fix_geometric_of_isDominant (hmul : MulNSt) {S : Scheme.{0}}
    [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (hM : 1 ≤ M) (hMu : IsUnit (M : Γ(S, ⊤)))
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : P.A ⟶ P.A) (hsm : IsMonHom s)
    (hs : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ s = x := by
  obtain ⟨hfin, -, -, het, -⟩ := hmul S P M hM
  have := het hMu
  exact fix_torsion_of_fix_geometric_of_etale P.A M t s hs T x hx

end GlobalTheory
end

section

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.TorusFourier
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsotropicSub (G : Matrix (Fin r) (Fin r) E) (V : Submodule E (Fin r → E)) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, herm G v w = 0

theorem isIsotropicSub_span {G : Matrix (Fin r) (Fin r) E} {s : Set (Fin r → E)}
    (h : ∀ v ∈ s, ∀ w ∈ s, herm G v w = 0) : IsIsotropicSub G (Submodule.span E s) := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [herm, cc]
    | add y z _ _ hy hz =>
      have : herm G x (y + z) = herm G x y + herm G x z := by
        simp [herm, cc, mul_add, Finset.sum_add_distrib]
      rw [this, hy, hz, add_zero]
    | smul c y _ hy =>
      have : herm G x (c • y) = cc c * herm G x y := by
        simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [this, hy, mul_zero]
  | zero => simp [herm]
  | add x y _ _ hx hy =>
    have : herm G (x + y) w = herm G x w + herm G y w := by
      simp [herm, add_mul, Finset.sum_add_distrib]
    rw [this, hx, hy, add_zero]
  | smul c x _ hx => rw [herm_smul_left', hx, mul_zero]

theorem exists_smul_mem (X : Data E r) (v : Fin r → E) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ X.Λ := by
  first
  | exact @_root_.GlobalTheory.SubmoduleScalarClosure.main
  | exact _root_.GlobalTheory.SubmoduleScalarClosure.main
  | (apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubmoduleScalarClosure.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubmoduleScalarClosure.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubmoduleScalarClosure.main ..)

section Torus

variable (X : Data E r)

end Torus

section Main

variable (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
  (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
    Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)

include hP hχ

end Main

end

end GlobalTheory.MaxCusp
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.fourierJacobi_coeff_linear_bounded_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℕ) (a : Fin m → ℂ) (Q : Fin m → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (Q i)) → (∀ x ∈ X.dom, f x = ∑ i, a i * Q i x) → ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν f x = ∑ i, a i * X.fj la ξ ν (Q i) x := by
  first | exact @GlobalTheory.fj_eq_sum_of_eqOn_dom | exact GlobalTheory.fj_eq_sum_of_eqOn_dom | (intros; apply GlobalTheory.fj_eq_sum_of_eqOn_dom <;> assumption)
end
