module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle043
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubicalQuasiFinite

theorem triv_translDiff_of_fixes {S : Scheme.{0}} {B Z : Over S} [GrpObj B] (φ : B ⟶ Z) {M : LB B.left}
    {H : LB Z.left} (hM : M.IsLB) (hH : H.IsLB) (hw : LBIso M (H.pull φ.left)) (x : 𝟙_ (Over S) ⟶ B)
    (hx : ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ) : Triv (translDiff B M x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  have e : translPt B x ≫ φ = snd _ B ≫ φ := by
    have e₀ : translPt B x = snd _ B ≫ ((toUnit B ≫ x) * 𝟙 B) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (snd _ B ≫ toUnit B) (fst _ B)]
      rfl
    rw [e₀, Category.assoc, hx]
  have e' : (translPt B x).left ≫ φ.left = (snd _ B).left ≫ φ.left := congrArg CommaMorphism.left e
  obtain ⟨c, hc, -⟩ := exists_gen hH
    (φ' := fun k : Fin 2 => (![(translPt B x).left, (snd _ B).left] : Fin 2 → _) k ≫ φ.left) (ε' := ![1, -1])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e', zpow_one, zpow_neg,
        mul_inv_cancel])) (LB.oneGen H (Y := (𝟙_ (Over S) ⊗ B).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  exact exists_down hw hH hM c hc

theorem locallyQuasiFinite_of_pow_iso_pull : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (_ : CubicalStr B L) (r n : ℕ), n.Prime → (n : K) ≠ 0 → ¬ n ∣ r → (∀ x : baseOver _ ⟶ B, x ^ n = 1 → Triv (translDiff B L.L x) → x = 1) → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z) (H : LB Z.left), H.IsLB → LBIso (pw L.L r) (H.pull φ.left) → LocallyQuasiFinite φ.left := by
  intro hcount K _ _ B _ _ hB L c r n hn hnK hnr hK Z _ _ φ H hH hw
  obtain ⟨C, W, hW, hC, hCW⟩ := GlobalTheory.Stabiliser.exists_closed_stabiliser K B hB Z φ
  have hfin : Finite C := by
    refine GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion hcount K B n hB hn hnK C W hW hCW fun x hx hxn => ?_
    have h₁ : Triv (translDiff B L.L (x ^ r)) :=
      ((GlobalTheory.Square.square_of_cubical _ B L c K (𝟙 _)).2 r x).1
        (triv_translDiff_of_fixes φ (isLB_pw L.isLB r) hH hw x ((hC x).1 hx))
    have h₂ : x ^ r = 1 := hK (x ^ r) (by
      change (x ^ r) ^ n = 1
      rw [← pow_mul, _root_.mul_comm, pow_mul, hxn, one_pow]) h₁
    have h₃ := pow_gcd_eq_one.2 ⟨hxn, h₂⟩
    rwa [(Nat.Prime.coprime_iff_not_dvd hn).2 hnr, pow_one] at h₃
  refine GlobalTheory.FiniteStabiliser.locallyQuasiFinite_of_finite_stabiliser K B hB Z φ ?_
  have e : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ} = (C : Set _) := Set.ext fun x => (hC x).symm
  rw [e]
  exact Set.toFinite _

end GlobalTheory.CubicalQuasiFinite
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAffineOpen_nonzeroLocus_of_universallyClosed {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y]
    [UniversallyClosed f] {H : LB X} {κ : Type} [Finite κ] (s : κ → H.Sec) (hcov : ⨆ j, nonzeroLocus (s j) = ⊤)
    (haff : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (t : H.Sec) : IsAffineOpen (nonzeroLocus t) := by
  classical
  have := Fintype.ofFinite κ
  choose r hr using fun j => AmpleSpan.exists_isRatio (s j) t
  choose σ hσ using fun j => AmpleSpan.exists_isRatio t (s j)
  have top := AmpleSpan.ker_sup_span_eq_top f s s hcov (fun j l => if l = j then 1 else 0)
    (fun j k => by simp [apply_ite]) t (AmpleSpan.isCompact_nonzeroLocus s hcov haff t) r hr
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range r) ?_ ?_
  · have e := congrArg (Ideal.map (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t) le_top).hom r)) top
    rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
      (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq] at e
    convert e using 3
    funext j
    simp [apply_ite]
  · rintro _ ⟨j, rfl⟩
    rw [(hr j).basicOpen, inf_comm, ← (hσ j).basicOpen]
    exact (haff j).basicOpen _

theorem IsAmpleLB.isAffineOpen_nonzeroLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f]
    {L : LB X} (h : IsAmpleLB L) {n : ℕ} (hn : 1 ≤ n) (s : (lbPow L n).Sec) : IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨N, hN, H⟩ := h.exists_cover_mul
  obtain ⟨M, u, hu, ha⟩ := H n hn
  have := isAffineOpen_nonzeroLocus_of_universallyClosed f u hu ha (secCast (Nat.mul_comm n N) (secPow s N))
  rwa [nonzeroLocus_secCast, nonzeroLocus_secPow s hN] at this

theorem isAffineOpen_nonzeroLocus_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ (n : ℕ), 1 ≤ n → (∀ s : H0 L n, IsAffineOpen (nonzeroLocus s)) ∧ ∃ (m : ℕ) (_ : 1 ≤ m) (M : ℕ) (t : Fin M → H0 L (n * m)), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro R _ X _ L hL hA n hn
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨s', hs, -⟩ : ∃ s' : (lbPow L n).Sec, nonzeroLocus s' = nonzeroLocus s ∧ _ :=
      exists_sec_oneTerm L (K' := PUnit) rfl s
    exact hs ▸ h.isAffineOpen_nonzeroLocus X.hom hn s'
  · obtain ⟨N, hN, H⟩ := h.exists_cover_mul
    obtain ⟨M, u, hu, -⟩ := H n hn
    choose t ht using fun i => exists_sec_oneTerm L (K' := Fin 1) (e' := ((n * N : ℕ) : ℤ))
      (by rw [Nat.mul_comm]) (u i)
    exact ⟨N, hN, M + 1, t, (iSup_congr fun i => (ht i).1).trans hu⟩

end GlobalTheory
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PullPair

open LBGerm GlobalTheory.AbLaw

def chartPullTw {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t) (𝟙 X) where
  idx J := (fun _ => J 0, fun _ => J 1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1⟩
  g y J J' hJ hJ' := by
    have a₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 1
    have b₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J' 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 1
    refine (gm_linComb L _ _ (𝟙 X) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t y
      (fun _ => J 0, fun _ => J 1) (fun _ => J' 0, fun _ => J' 1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb L _ _ (𝟙 X) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp]

theorem exists_sec_twist {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (f : X ⟶ X) (e : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (y : X) : ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have hLB := h.isLB
  obtain ⟨n, hn, hc⟩ := h.exists_cover_mul
  obtain ⟨N, s, hs, ha⟩ := hc k hk
  have : CompactSpace X := h.compactSpace
  have : QuasiSeparatedSpace X := h.quasiSeparatedSpace
  obtain ⟨i, hi⟩ : ∃ i, y ∈ nonzeroLocus (s i) := by
    have hy : y ∈ (⨆ i, nonzeroLocus (s i)) := hs ▸ trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  have hM := LB.isLB_linComb hLB (fun _ : PUnit => f) (fun _ => e)
  have hH := isLB_lbPow hLB (n * k)
  obtain ⟨V, N', hyV, hV⟩ := GlobalTheory.TwistGen.exists_nhds hM hH (s i) (ha i) y hi
  obtain ⟨u, hu⟩ := hV 1
  have hmul : n * k * (N' + 1) = k * (n * (N' + 1)) := by ring
  refine ⟨n * (N' + 1), Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  rw [← hmul]
  refine ⟨chartSec (chartPullTw L f e (n * k) (N' + 1)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id]
  · exact hu hyV
  · intro z j hj
    refine ⟨![j.1 PUnit.unit, j.2 PUnit.unit], Set.mem_iInter.2 fun m => ?_⟩
    fin_cases m
    · exact Set.mem_iInter.1 hj.1 PUnit.unit
    · exact Set.mem_iInter.1 hj.2 PUnit.unit

theorem exists_cross : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A F j, ∃ t₁' t₂' : SecA A F (k * n), Cross a t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A.L z J → sA t₂ (ptSecT A.A 1).left z J ≠ 0) → (∀ z J, Good A.L z J → sA t₂' (ptSecT A.A 1).left z J ≠ 0)) := by
  intro _ R _ _ A F _ _ a ha j k hk
  have hamp : IsAmpleLB A.L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample
  have hUq : Unique (TFK (R := R) F).left := by
    unfold TFK
    exact inferInstanceAs (Unique (Spec (CommRingCat.of F)))
  obtain ⟨n, hn, u, hu⟩ := PullPair.exists_sec_twist hamp a.left (-(j : ℤ)) k hk
    ((1 : TFK (R := R) F ⟶ A.A).left default)
  have hασ : ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) A.A).left ≫ a.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have hF : FormEq (Sum.elim (fun m => (snd (TFK (R := R) F) A.A).left ≫ (![a.left, 𝟙 A.A.left] : Fin 2 → _) m)
      (fun _ : Fin 1 => ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left))
      (Sum.elim (![-(j : ℤ), ((k * n : ℕ) : ℤ)] : Fin 2 → ℤ) (fun _ : Fin 1 => (j : ℤ)))
      (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => ((k * n : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, hασ]
    rw [mul_right_comm, ← zpow_add, neg_add_cancel, zpow_zero, _root_.one_mul]
  refine ⟨n, hn, fun (t₁ t₂ : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (fun _ => (j : ℤ)))) => ?_⟩
  obtain ⟨s₁, hs₁⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₁ ((TFK (R := R) F) ◁ a).left))
  obtain ⟨s₂, hs₂⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₂ ((TFK (R := R) F) ◁ a).left))
  refine ⟨s₁, s₂, ?_, ?_⟩
  · intro z J hJ
    unfold sA
    rw [hs₁ _ _ z J hJ, hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
    simp only [Category.id_comp]
    ring
  · intro hne z J hJ
    have hr : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ ((TFK (R := R) F) ◁ a).left =
        (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_whiskerLeft, MonObj.one_comp]
    have hs : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
        (1 : TFK (R := R) F ⟶ A.A).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_snd]
    have hne' := hne z J hJ
    unfold sA at hne' ⊢
    rw [hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, hr]
    have hmem : ((ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left) z ∈
        nonzeroLocus u := by
      rw [hs, Subsingleton.elim z default]
      exact hu
    unfold nonzeroLocus at hmem
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hmem
    have hunit := ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval u _ z hJ i hi
    exact fun h0 => hne' ((hunit.mul_right_eq_zero).1 h0)

end GlobalTheory.PullPair
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteTorsionExt

theorem eq_of_isPullF {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {x : Spec (CommRingCat.of F) ⟶ T.left} {g : GtPt D T}
    {g₁ g₂ : GtPtF D F} (h₁ : GtPt.IsPullF F x g g₁) (h₂ : GtPt.IsPullF F x g g₂) : g₁ = g₂ := by
  obtain ⟨b₁, s₁, i₁, z₁, m₁⟩ := g₁
  obtain ⟨b₂, s₂, i₂, z₂, m₂⟩ := g₂
  obtain rfl : b₁ = b₂ := Over.OverMorphism.ext (h₁.1.trans h₂.1.symm)
  obtain rfl : s₁ = s₂ := funext fun χ => GlobalTheory.TorusCoord.gen_eq_of_corr D.P.isLB (i₁ χ) (i₂ χ)
    (DVR.corr_trans D.P.isLB (h₁.2 χ) (DVR.corr_symm (h₂.2 χ)))
  rfl

theorem main : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → I' ≠ ⊤ → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (x₁ : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ G') (gp : GtPt D'.toPre (𝟙_ (Over (Spec (CommRingCat.of R'))))), x₁ ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R' I' e) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G'), xe ≫ fstG I' e G' = toUnit _ ≫ x₁ ∧ xe ≫ (U'.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (LB.pullGen D'.toPre.P.L _ _ ((U'.gt e).t χ) xe.left) (LB.pullGen D'.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R' I' e))).left)) → ∀ (p : QkPt D.toPre F k) (g' : GtPtF D'.toPre F) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → IsPullGtF φ hD F p.g g' → GtPt.IsPullF F (toUnit (TF (R := R') F)).left gp g' → x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R') F) ≫ x₁).left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) → QkToAkU U.toUnifPre F k p x := by
  intro hL R R' _ _ _ _ _ I I' hR hR' φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU hI' F _ _ _ hF k hk x₁ gp hx₁ hxe
    p g' x hp hg hg' hx
  obtain ⟨p', hp', hpg'⟩ := (GlobalTheory.T.torsionPoint_qk_alt hL.globalFns R' I' hR' hI' D' A' G' U'.toUnifPre k x₁ gp hx₁ hxe).2 F
  have e : p'.g = g' := eq_of_isPullF hpg' hg'
  let y : TFK (R := R') F ⟶ (Over.pullback (jK R')).obj G' :=
    Over.homMk (pullback.lift (toUnit (TF (R := R') F) ≫ x₁).left (jFK (R := R') F)
      (Over.w (toUnit (TF (R := R') F) ≫ x₁))) (pullback.lift_snd _ _ _)
  have hy : (y ≫ U'.gen.hom).left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') =
      (toUnit (TF (R := R') F) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine GlobalTheory.T.qkToAk_descends_along_baseChange hL.globalFns hL.secBaseChange R R' I I' hR hR' φ D A G U G' bc hbc A' D' hD U' hU F hF k hk
    p x p' (y ≫ U'.gen.hom) (by rw [hp, hp', map_zero]) (e ▸ hg) ?_
    (GlobalTheory.T.qkToAkU_of_integral_torsion_point hL R' I' hR' hI' D' A' G' U' k hk x₁ gp hx₁ hxe F p' _ hp' hpg' hy)
  rw [hx, ← hy]
  simp only [Category.assoc]

end GlobalTheory.FiniteTorsionExt
end
