module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

theorem lbIso_of_refines {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem refines_npw {X : Scheme.{0}} (L : LB X) (N : ℕ) :
    Refines (npw L N) L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ)) := by
  refine ⟨fun i _ => i, fun i y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z i j _ _ => ?_⟩
  refine (map_pow _ _ _).trans (Eq.symm ((Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)))
  rw [Category.comp_id]
  rfl

theorem npw_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (N : ℕ) :
    LBIso (npw L N) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ))) :=
  lbIso_of_refines hL (refines_npw L N) (refines_self _ _) _ isGen_one fun U _ f => by
    rw [Fintype.prod_empty, _root_.one_mul]

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a b : Sp k ⟶ X)
    (u v : Y ⟶ X) (φ : Fin 4 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) (h₂ : φ 2 = v) (h₃ : φ 3 = p ≫ b) :
    LBIso (LB.LinComb L φ Oε) (LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := Fin 2) ![a, b] ![1, -1]
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ (DVR.pullGen_isGen _ _ _ e he p) fun U _ f => ?_
  rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, h₀, h₁, h₂, h₃]
  change f (p ≫ a) ^ (1 : ℤ) * f (p ≫ b) ^ (-1 : ℤ) *
    (f u ^ (1 : ℤ) * f (p ≫ a) ^ (-1 : ℤ) * f v ^ (-1 : ℤ) * f (p ≫ b) ^ (1 : ℤ)) = f u ^ (1 : ℤ) * f v ^ (-1 : ℤ)
  simp only [zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_pol : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  rintro hB k _ Φ R _ _ D s π hπ xe hO N ⟨cp⟩
  obtain ⟨P', g, hg, hdim, hm, t, ht⟩ := hB _ _ s D.P
  have gp : IsGrpPullback P'.A D.P.A s g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨β, hβ, hβπ⟩ := grpPullback_iso hπ gp
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  have hL := D.P.isLB
  have hL' := P'.isLB
  have key : ∀ {K : Type} [Fintype K] (φ' : K → (Φ.E.B.left ⟶ P'.A.left)) (φ : K → (Φ.E.B.left ⟶ D.P.A.left))
      (ε : K → ℤ), (∀ a, φ a = φ' a ≫ g) → LBIso (LB.LinComb D.P.L φ ε) (LB.LinComb P'.L φ' ε) := by
    intro K _ φ' φ ε h
    obtain rfl : φ = fun a => φ' a ≫ g := funext h
    exact (iso_linComb ((isGen_iff w).1 hw) φ' ε).symm
  have hc : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, (s ≫ x.left) ≫ D.P.A.hom = 𝟙 _ ≫ s := fun x => by
    rw [Category.assoc, Over.w x, Category.id_comp]
    exact Category.comp_id _
  let c : Φ.E.X → (baseOver (Sp k) ⟶ P'.A) := fun χ =>
    Over.homMk (hg.lift (s ≫ (D.c (xe χ)).left) (𝟙 _) (hc _)) (hg.lift_snd _ _ _)
  have hcg : ∀ χ, (c χ).left ≫ g = s ≫ (D.c (xe χ)).left := fun χ => hg.lift_fst _ _ _
  have hu : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, π ≫ (toUnit D.P.A ≫ x).left = Φ.E.B.hom ≫ s ≫ x.left := fun x => by
    rw [← Category.assoc, ← hπ.1.w, Category.assoc]
    rfl
  refine ⟨⟨P', β, hβ, c, ?_, fun χ => ?_⟩, hdim⟩
  · have h₁ : LBIso Φ.N₀ (LB.LinComb D.P.L (K := PUnit) (fun _ => π) (fun _ => (N : ℤ))) :=
      LBIso.chartPull cp (chartPullSame _ _ _ _ π fun _ => (Category.comp_id _).symm) (npw_iso hL N)
    have h₂ := key (K := PUnit) (fun _ => β.hom.left) (fun _ => π) (fun _ => (N : ℤ)) fun _ => hβπ.symm
    have h₃ : LBIso (LB.LinComb P'.L (K := PUnit) (fun _ => β.hom.left) (fun _ => (N : ℤ)))
        ((lbPow P'.L N).pull β.hom.left) :=
      LBIso.chartPull (chartPullId _) (chartPullOut P'.L _ _ β.hom.left _ fun _ => (Category.comp_id _).symm)
        (exists_iso hL' rfl _)
    exact LBIso.trans Φ.isLB (DVR.linComb_isLB _ hL _ _) (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₁
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
        (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₂ h₃)
  · let q : Φ.E.B ⟶ baseOver (Sp k) := Over.homMk Φ.E.B.hom (Category.comp_id _)
    have e₀ : π ≫ D.Oφ (𝟙 D.P.A) (xe χ) 0 = (β.hom * (q ≫ c χ)).left ≫ g := by
      let ρ : Over.mk (Φ.E.B.hom ≫ s) ⟶ D.P.A := Over.homMk π hπ.1.w
      refine Eq.trans ?_ (gp.2 Φ.E.B β.hom (q ≫ c χ) (ρ ≫ 𝟙 _) (ρ ≫ toUnit _ ≫ D.c (xe χ))
        ((Category.comp_id _).trans hβπ.symm) ?_)
      · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (𝟙 _) (toUnit _ ≫ D.c (xe χ)))
      · refine (hu _).trans ?_
        rw [← hcg]
        exact (Category.assoc _ _ _).symm
    have h₁ := lbIso_drop hL Φ.E.B.hom (s ≫ (D.c (xe χ)).left) (s ≫ (η[D.P.A]).left) _ π
      (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) e₀ (hu _) (Category.comp_id _) (hu _)
    have h₂ := key (K := Fin 2) ![(β.hom * (q ≫ c χ)).left, β.hom.left] ![(β.hom * (q ≫ c χ)).left ≫ g, π] ![1, -1]
      (fun a => by
        fin_cases a
        · rfl
        · exact hβπ.symm)
    exact LBIso.trans (Φ.E.O χ).isLB (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) (hO χ)
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) h₁ h₂)

end GlobalTheory.ZH.UFib
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.Scalar


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ModelData.Scalar.tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : _root_.GlobalTheory.Ex.NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p = N.tx m p' := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at h
  obtain ⟨z, hz1, hz2⟩ := h
  unfold _root_.GlobalTheory.Ex.NumD.tx
  have ht : ∀ χ, N.txT m p' χ = N.txT m p (χ + m • z) := fun χ =>
    (_root_.GlobalTheory.Ex.txT_shift O N m hm p p' χ).1 z hz1 hz2
  rw [tsum_congr ht]
  exact ((Equiv.addRight (m • z)).tsum_eq (fun χ => N.txT m p χ)).symm

variable {O : Type} [CommRing O] {N : NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k}

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
private theorem qEq_mul' (N : _root_.GlobalTheory.Ex.NumD O) {k : ℕ}
    {p p' q q' : N.QT k} (h : N.QEq p p')
    (h' : N.QEq q q') :
    N.QEq (p * q) (p' * q') := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at *
  obtain ⟨z, hz1, hz2⟩ := h
  obtain ⟨z', hz1', hz2'⟩ := h'
  refine ⟨z + z', ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Prod.fst_mul, toAdd_mul, hz1, hz1', smul_add]
    abel
  · simp only [Subgroup.coe_mul, Prod.snd_mul, hz2, hz2', N.io_add]
    ac_rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
private theorem qEq_label_pow_nsmul
    (hL : _root_.GlobalTheory.ModelData.Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x : La) :
    ∀ d : ℕ, 1 ≤ d → N.QEq ((lab k x) ^ d) (lab k (d • x)) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => simpa using (N.qEq_equivalence k).refl (lab k x)
  | succ d hd ih =>
    rw [pow_succ, succ_nsmul]
    unfold _root_.GlobalTheory.ModelData.Labels at hL
    exact (N.qEq_equivalence k).trans
      (qEq_mul' N ih ((N.qEq_equivalence k).refl _)) (hL.1 k hk _ _)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
private theorem tx_label_nsmul_eq_of_odd [TopologicalSpace O]
    (hL : _root_.GlobalTheory.ModelData.Labels N EF ζ lab) {d m : ℕ} (hd : Odd d) (hm : Odd m)
    (K : ℕ) (hK : K = d * m) (x : La) :
    N.tx K (lab (K ^ 2) (d • x)) = N.tx m (lab (m ^ 2) x) := by
  subst hK
  have hdm : Odd (d * m) := hd.mul hm
  set q := lab ((d * m) ^ 2) x with hq
  have hmem : ((q : Multiplicative N.X × N.Gt).1, (q : Multiplicative N.X × N.Gt).2 ^ (d ^ 2)) ∈
      N.QT (m ^ 2) := by
    rw [N.mem_QT]
    have hqm := (N.mem_QT).1 q.2
    rw [← pow_mul, show d ^ 2 * m ^ 2 = (d * m) ^ 2 by ring]
    exact hqm
  set p : N.QT (m ^ 2) := ⟨_, hmem⟩ with hp
  have h1 : N.tx (d * m) (lab ((d * m) ^ 2) (d • x)) =
      N.tx (d * m) (q ^ d) :=
    (_root_.GlobalTheory.ModelData.Scalar.tx_congr N hdm
      (qEq_label_pow_nsmul hL (pow_pos hdm.pos 2) x d hd.pos)).symm
  have h2 : N.tx (d * m) (q ^ d) = N.tx m p := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr (fun χ => ?_)
    refine _root_.GlobalTheory.Ex.Nest.txT_nest O N d m hd hm (q ^ d) p ?_ ?_ χ
    · rw [SubgroupClass.coe_pow, Prod.pow_fst]
    · rw [SubgroupClass.coe_pow, Prod.pow_snd, ← pow_mul, ← sq]
  have h3 : N.QEq p (lab (m ^ 2) x) := by
    have c4 : ∀ K, m ^ 2 * d ^ 2 = K → ∀ p' : N.QT (m ^ 2),
        (p' : Multiplicative N.X × N.Gt).1 = (lab K x : Multiplicative N.X × N.Gt).1 →
        (p' : Multiplicative N.X × N.Gt).2 = (lab K x : Multiplicative N.X × N.Gt).2 ^ (d ^ 2) →
        N.QEq p' (lab (m ^ 2) x) := by
      intro K hK
      subst hK
      unfold _root_.GlobalTheory.ModelData.Labels at hL
      exact hL.2.2.2.1 (m ^ 2) (d ^ 2) (pow_pos hm.pos 2) (pow_pos hd.pos 2) x
    exact c4 ((d * m) ^ 2) (by ring) p rfl rfl
  rw [h1, h2]
  exact _root_.GlobalTheory.ModelData.Scalar.tx_congr N hm h3


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {O : Type} [CommRing O] {N : _root_.GlobalTheory.Ex.NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k} in
theorem _root_.GlobalTheory.ModelData.Scalar.scalar_const : ∀ (C : Type) [NormedField C] (N N' : _root_.GlobalTheory.Ex.NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → _root_.GlobalTheory.ModelData.Labels N EF ζ lab → _root_.GlobalTheory.ModelData.Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n hn hL hL' hc hx
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨c₁, hc₁⟩ := hc 1
  have hn1 : Odd (n ^ 1) := by simpa using hn
  refine ⟨c₁, c₁.ne_zero, fun j x => ?_⟩
  cases j with
  | zero =>
    have e1 := tx_label_nsmul_eq_of_odd hL hn (Odd.pow hn : Odd (n ^ 0)) (n ^ 1) (by ring) x
    have e2 := tx_label_nsmul_eq_of_odd hL' hn (Odd.pow hn : Odd (n ^ 0)) (n ^ 1) (by ring) x
    rw [← e1, ← e2, hc₁]
  | succ i =>
    obtain ⟨c, hc'⟩ := hc (i + 1)
    have e1 := tx_label_nsmul_eq_of_odd hL (Odd.pow hn : Odd (n ^ i)) hn1 (n ^ (i + 1))
      (by ring) x₀
    have e2 := tx_label_nsmul_eq_of_odd hL' (Odd.pow hn : Odd (n ^ i)) hn1 (n ^ (i + 1))
      (by ring) x₀
    have hcc : (c : C) = c₁ := by
      have h := hc' (n ^ i • x₀)
      rw [e1, e2, hc₁] at h
      exact (mul_right_cancel₀ hx₀ h).symm
    rw [hc' x, hcc]

end GlobalTheory.ModelData.Scalar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal
open GlobalTheory.ThetaPtMove

theorem exists_good_translate : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  intro hL S P K _ _ x n hn hK th hth a
  let β : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := hth (Over.mk x) β
  have h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0 := fun e => c.ne_zero 0 ((hc 0).trans e)
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a
  refine ⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.isLB p
  have q := hu p J hJ
  have e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hz]
    congr 1
    ext1 <;> simp [ptSecT, β]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e, sv_of_isValueAt hv _ p hJ, h0,
    GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul] at q
  exact not_isUnit_zero q

end GlobalTheory.ThetaReal
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.GlueTheta

theorem res_res {X : Scheme.{0}} {U V T : X.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem glue_secOn {X : Scheme.{0}} (L : LB X) {I : Type} (V : I → X.Opens) (W : X.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : ∀ x ∈ W, ∃ i, x ∈ V i) (σ : ∀ i j, Γ(X, V i ⊓ L.U j)) (hσ : ∀ i, σ i ∈ secOn L (V i))
    (hc : ∀ i i' j (O : X.Opens) (h : O ≤ V i ⊓ L.U j) (h' : O ≤ V i' ⊓ L.U j),
      resG X h (σ i j) = resG X h' (σ i' j)) :
    ∃ s ∈ secOn L W, ∀ i j, resG X (inf_le_inf_right _ (hle i)) (s j) = σ i j := by
  have key : ∀ j, ∃ s : Γ(X, W ⊓ L.U j), ∀ i, resG X (inf_le_inf_right _ (hle i)) s = σ i j := by
    intro j
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V i ⊓ L.U j) (W ⊓ L.U j)
      (fun i => homOfLE (inf_le_inf_right _ (hle i)))
      (fun x hx => by
        obtain ⟨i, hi⟩ := hcov x hx.1
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi, hx.2⟩)
      (fun i => σ i j) (fun i i' => hc i i' j _ inf_le_left inf_le_right)
    exact ⟨s, hs⟩
  choose s hs using key
  refine ⟨s, fun j k => ?_, fun i j => hs j i⟩
  refine X.sheaf.eq_of_locally_eq' (fun i => V i ⊓ L.U j ⊓ L.U k) (W ⊓ L.U j ⊓ L.U k)
    (fun i => homOfLE (inf_le_inf_right _ (inf_le_inf_right _ (hle i))))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcov x hx.1.1
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, ⟨hi, hx.1.2⟩, hx.2⟩) _ _ fun i => ?_
  have h := hσ i j k
  rw [← hs j i, ← hs k i, res_res, res_res] at h
  change resG X _ _ = resG X _ _
  rw [map_mul, res_res, res_res, res_res]
  exact h

theorem exists_glue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (c : Ω), (∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N'), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j)) → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ N ≤ W ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.ThMul c N σ ∧ Q.FibNe N σ) → ∃ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ W), Q.ThMul c W σ ∧ Q.FibNe W σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q c huniq W hloc
  choose N σ hz hNW hsec hth hne using fun z : W => hloc z.1 z.2
  obtain ⟨s, hs, hres⟩ := glue_secOn Q.LOne (fun z : W => Q.G.hom ⁻¹ᵁ N z) (Q.G.hom ⁻¹ᵁ W)
    (fun z x hx => hNW z hx) (fun x hx => ⟨⟨Q.G.hom x, hx⟩, hz _⟩) σ hsec
    (fun z z' => huniq _ _ _ _ (hth z) (hth z'))
  have hval : ∀ (K : Type) [Field K] (g : Sp K ⟶ Q.G.left) (z : W) (j : Q.LOne.ι),
      ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) → valF g _ (σ z j) = valF g _ (s j) := by
    intro K _ g z j h
    rw [← hres z j]
    exact GlobalTheory.Points.valR_res g _ h _
  refine ⟨s, hs, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    let z : W := ⟨Q.G.hom ((g ≫ Q.φ) (IsLocalRing.closedPoint K)), h5 ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z) := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    have hU : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U fun _ => jL) := fun t ht =>
      ⟨hN ht, Set.mem_iInter.2 fun _ => h4 ⟨t, rfl⟩⟩
    rw [← hval K _ z _ hU]
    exact hth z K β g r jP jL h1 h2 h3 h4 (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
  · intro K _ _ x hx
    let z : W := ⟨x (IsLocalRing.closedPoint K), hx ⟨_, rfl⟩⟩
    have hN : ⊤ ≤ x ⁻¹ᵁ N z := (GlobalTheory.Points.le_preimage_iff _ _).2 (hz z)
    obtain ⟨g, j, hg, hv⟩ := hne z K x (by rintro _ ⟨t, rfl⟩; exact hN (x := t) trivial)
    refine ⟨g, j, hg, ?_⟩
    have hU : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N z ⊓ Q.LOne.U j) := by
      by_contra hU
      exact hv (dif_neg hU)
    rwa [← hval K g z j hU]

end GlobalTheory.ZH.GlueTheta
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem resG_trans_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem scale_mem_secOn {X : Scheme.{0}} (L : LB X) {V V' : X.Opens} (h : V' ≤ V) (a : Γ(X, V'))
    {σ : ∀ j, Γ(X, V ⊓ L.U j)} (hσ : σ ∈ secOn L V) :
    (fun j => resG X inf_le_left a * resG X (inf_le_inf_right _ h) (σ j)) ∈ secOn L V' := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    V' ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hσ i j)
  simp only [map_mul, resG_trans_apply] at e ⊢
  rw [e, mul_left_comm]

theorem valF_scale {X Z : Scheme.{0}} (p : X ⟶ Z) {N N' : Z.Opens} (h : p ⁻¹ᵁ N' ≤ p ⁻¹ᵁ N) (F : Γ(Z, N'))
    (U : X.Opens) (s : Γ(X, p ⁻¹ᵁ N ⊓ U)) {K : Type} [Field K] (g : Sp K ⟶ X)
    (hg : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ N' ⊓ U)) :
    valF g (p ⁻¹ᵁ N' ⊓ U) (resG X inf_le_left ((p.app N').hom F) * resG X (inf_le_inf_right _ h) s) =
      valF (g ≫ p) N' F * valF g _ s := by
  rw [valF_eq_valR, valR_mul g _ hg, valR_res g _ hg, valR_res g _ hg, ← valR_comp]
  rfl

theorem RatModel.exists_unit_fn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (N' : M.Z.Opens) (f : Ω) (hf : ∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) :
    ∃ F : Γ(M.Z, N'), (∀ z ∈ N', z ∈ M.Z.basicOpen F) ∧ ((N' : Set M.Z).Nonempty → valF M.pt N' F = f) := by
  by_cases hN : (N' : Set M.Z).Nonempty
  · obtain ⟨F, hF⟩ := (RatModel.mem_ringOn_iff_exists hN).1 (RatModel.mem_ringOn.2 fun z hz => (hf z hz).2.1)
    subst hF
    exact ⟨F, fun z hz => (RatModel.isUnit_valF_iff hz F).1
      ((RatModel.isUnit_O_iff _).2 ⟨(hf z hz).1, (hf z hz).2.2⟩), fun _ => rfl⟩
  · exact ⟨1, fun z hz => (hN ⟨z, hz⟩).elim, fun h => (hN h).elim⟩

theorem ZHPre.exists_scale_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  intro o Ω _ _ _ _ S ρ M U₀ Q N N' σ c f hN hf hσ hT hF
  obtain ⟨F, hFu, hFv⟩ := M.exists_unit_fn N' f hf
  have h : Q.G.hom ⁻¹ᵁ N' ≤ Q.G.hom ⁻¹ᵁ N := fun _ hz => hN hz
  refine ⟨_, scale_mem_secOn Q.LOne h ((Q.G.hom.app N').hom F) hσ, ?_, ?_⟩
  · intro K _ β g r jP jL h1 h2 h3 h4 h5
    have e := hT K β g r jP jL h1 h2 h3 h4 (h5.trans h)
    have hg : ⊤ ≤ (g ≫ Q.φ) ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U (fun _ => jL)) := fun w _ =>
      ⟨h5 ⟨w, rfl⟩, Set.mem_iInter.2 fun _ => h4 ⟨w, rfl⟩⟩
    have hp : (g ≫ Q.φ) ≫ Q.G.hom = spMap β ≫ M.pt := by
      rw [Category.assoc, Q.cart.1.w, ← h1]
      rfl
    have hne : (N' : Set M.Z).Nonempty := ⟨_, h5 ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have hv := valF_scale Q.G.hom h F _ (σ fun _ => jL) _ hg
    rw [hp, valF_eq_valR (spMap β ≫ M.pt), valR_spMap_comp β M.pt N' (M.top_le_preimage_pt hne),
      ← valF_eq_valR, hFv hne] at hv
    refine Eq.trans ?_ (congrArg (_ * ·) hv.symm)
    refine Eq.trans ?_ ((congrArg (β f * ·) e).trans (mul_left_comm _ _ _))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by rw [map_mul, _root_.mul_assoc]
  · intro K _ _ x hx
    obtain ⟨g, j, hg, hne⟩ := hF K x (hx.trans hN)
    have h1 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) := by
      by_contra hc
      exact hne (dif_neg hc)
    have hx' : ⊤ ≤ x ⁻¹ᵁ N' := (top_le_preimage_iff x N').2 hx
    have h2 : ⊤ ≤ g ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j) := fun w hw =>
      ⟨(show ⊤ ≤ (g ≫ Q.G.hom) ⁻¹ᵁ N' from hg ▸ hx') hw, (h1 hw).2⟩
    refine ⟨g, j, hg, ?_⟩
    rw [valF_scale Q.G.hom h F _ (σ j) g h2, hg]
    exact mul_ne_zero ((le_preimage_basicOpen_iff x hx' F).1 fun w hw => hFu _ (hx' hw)).ne_zero hne

end GlobalTheory.ZH
end
end
