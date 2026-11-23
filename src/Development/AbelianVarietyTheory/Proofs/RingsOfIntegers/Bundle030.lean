module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WchartCompLePull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BoxSymIsSymmetry
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle029
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle025
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle026
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle013
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowDegPre

section General

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J] (F : J → (X' ⟶ X)) (q : Y ⟶ X')
  (n : ℤ)

def genOfPullBoxPow
    (a : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n))) :
    LB.Gen (LB.LinComb L (fun i => q ≫ F i) (fun _ => n)) where
  s := fun jN => res (wchart_comp_le_pull L F q jN) (a.s (fun _ => jN))

private lemma res_res_eq_pullU_pow_mul_res_of_res_eq {Y Z : Scheme.{0}} (q : Y ⟶ Z) {O : Z.Opens} (g : Γ(Z, O)ˣ) (n : ℤ)
    {U1 U2 D V : Y.Opens} (s1 : Γ(Y, U1)ˣ) (s2 : Γ(Y, U2)ˣ)
    (hD1 : D ≤ U1) (hE : D ≤ q ⁻¹ᵁ O) (hD2 : D ≤ U2)
    (h : res hD1 s1 = (∏ _x : PUnit, res hE (pullU q O g) ^ n) * res hD2 s2)
    (hB : V ≤ U1) (hA : q ⁻¹ᵁ O ≤ V) (hC : q ⁻¹ᵁ O ≤ U2) (hDO : q ⁻¹ᵁ O ≤ D) :
    res hA (res hB s1) = pullU q O g ^ n * res hC s2 := by
  have h2 := congrArg (res hDO) h
  simp only [map_mul, map_zpow, Fintype.prod_unique, res_res'] at h2
  have hid : ∀ (k : q ⁻¹ᵁ O ≤ q ⁻¹ᵁ O) (x : Γ(Y, q ⁻¹ᵁ O)ˣ), res k x = x :=
    fun k x => (res_res' k k x).symm.trans (res_of_le_of_le k k x)
  rw [res_res', h2, hid]

theorem mapsAt_idIso_pow
    (a : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n)))
    (ha : a.IsGen) :
    GeneratorPullback.MapsAt L (LB.LinComb L F (fun _ => 1)) F (CubePf.idIsoL _) q n a
      (genOfPullBoxPow L F q n a) := by
  intro jN jL
  have h := ha (fun _ => jN) (fun _ => jL)
  simp only [CubePf.idIsoL, genOfPullBoxPow]
  refine res_res_eq_pullU_pow_mul_res_of_res_eq q ((L.LinComb F fun _ => 1).g jN jL) n (a.s fun _ => jN) (a.s fun _ => jL) _ _ _ h _ _ _ ?_
  intro y hy
  have hy' := TopologicalSpace.Opens.mem_inf.1 (show q.base y ∈ _ from hy)
  exact TopologicalSpace.Opens.mem_inf.2
    ⟨Set.mem_iInter.2 fun _ => hy'.1, Set.mem_iInter.2 fun _ => hy'.2⟩

variable (r : J → (Y ⟶ X)) (he : ∀ i, q ≫ F i = r i)
  (t : ∀ i, LB.Gen (LB.LinComb L (K := PUnit) (fun _ => r i) (fun _ => n)))

def boxAt : LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) (K := PUnit) (fun _ => q) (fun _ => n)) :=
  GeneratorPullback.boxGen L F (fun _ => q) (fun _ => n) fun i =>
    GeneratorPullback.pullAlong L (F i) (𝟙 Y) (fun _ => r i) (fun _ => n) (fun _ => q)
      (fun _ => (he i).trans (Category.id_comp _).symm) (t i)

theorem isGen_boxAt (ht : ∀ i, (t i).IsGen) : (boxAt L F q n r he t).IsGen := by
  unfold boxAt
  exact isGen_boxGen L F _ _ _ fun i =>
    LBxP.isGen_pullAlong L (F i) (𝟙 Y) _ _ _ _ (t i) (ht i)

private lemma res_pullU_id_eq_res_of_le {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (h' : V ≤ U)
    (x : Γ(Y, U)ˣ) : res h (pullU (𝟙 Y) U x) = res h' x := by
  ext
  simp [res, pullU]
  rfl

private lemma res_res_prod_res_pullU_id_eq_res_prod {Y : Scheme.{0}} {J : Type} [Fintype J] {O T : J → Y.Opens}
    {W V Z W' : Y.Opens} (x : ∀ i, Γ(Y, O i)ˣ) (hD : ∀ i, T i ≤ (𝟙 Y) ⁻¹ᵁ O i) (hC : ∀ i, W ≤ T i)
    (hB : V ≤ W) (hA : Z ≤ V) (hG : ∀ i, W' ≤ O i) (hE : Z ≤ W') :
    res hA (res hB (∏ i, res (hC i) (res (hD i) (pullU (𝟙 Y) (O i) (x i))))) =
      res hE (∏ i, res (hG i) (x i)) := by
  simp only [map_prod, res_res']
  exact Finset.prod_congr rfl fun i _ => res_pullU_id_eq_res_of_le _ _ (x i)

theorem corr_boxAt :
    LB.Gen.Corr L _ _ _ _ (genOfPullBoxPow L F q n (boxAt L F q n r he t))
      (GeneratorPullback.finProdGen L (J := J) (fun i _ => r i) (fun _ _ => n) t) := by
  intro j j' hj hj' hjj
  have hj'' : j' = fun p => j p.1 := funext fun p => (hjj p.1 p (he p.1)).symm
  subst hj''
  simp only [genOfPullBoxPow, boxAt, GeneratorPullback.boxGen, GeneratorPullback.pullAlong, GeneratorPullback.finProdGen]
  exact res_res_prod_res_pullU_id_eq_res_prod (fun i => (t i).s fun _ => j i) _ _ _ _ _ _

end General

section Points

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)

def tuple {T : Over S} (x : Fin j → (T ⟶ G)) : T ⟶ G' := p.lim.lift (Fan.mk T x)

theorem tuple_pr {T : Over S} (x : Fin j → (T ⟶ G)) (i : Fin j) : tuple p x ≫ p.pr i = x i := by
  simpa [tuple] using p.lim.fac (Fan.mk T x) ⟨i⟩

theorem pt_ext {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  refine p.lim.hom_ext fun k => ?_
  obtain ⟨k⟩ := k
  simpa using h k

theorem lift_mul_pr {T : Over S} (a b : T ⟶ G') (i : Fin j) :
    (lift a b ≫ μ[G']) ≫ p.pr i = lift (a ≫ p.pr i) (b ≫ p.pr i) ≫ μ[G] := by
  have := p.hom i
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem eSec_pr (i : Fin j) : η[G'].left ≫ (p.pr i).left = η[G].left := by
  have := p.hom i
  rw [← Over.comp_left, IsMonHom.one_hom]

end Points

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (j : ℕ)

abbrev pw : IsPowGrp (powPol D.P j).A D.P.A j := (isPowPolAV_powPol D.P j).toIsPowGrp

theorem ptK_tuple_pr (x : Fin j → D.X) (i : Fin j) :
    ptK (tuple (pw D j) fun i => D.c (x i)) ≫ ((pw D j).pr i).left = ptK (D.c (x i)) := by
  unfold ptK
  rw [← Over.comp_left, Category.assoc, tuple_pr]

def pow : DegPre R where
  P := powPol D.P j
  rig := boxRig (pw D j) D.P.L D.rig
  rig_gen := boxRigIsGen _ _ _ j (pw D j) D.P.L D.rig D.P.isLB D.rig_gen
  cub := Classical.choose (boxCubical _ _ _ j (pw D j) ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub
    (powPol D.P j).isLB (boxRigIsGen _ _ _ j (pw D j) D.P.L D.rig D.P.isLB D.rig_gen))
  sym := boxSym (pw D j) D.P.L D.sym
  sym_gen := (boxSym_isSymmetry _ _ _ j (pw D j) D.P.L D.sym D.P.isLB D.sym_gen D.sym_rig).1
  sym_rig := (boxSym_isSymmetry _ _ _ j (pw D j) D.P.L D.sym D.P.isLB D.sym_gen D.sym_rig).2
  X := Fin j → D.X
  c := fun x => tuple (pw D j) fun i => D.c (x i)
  c_add := fun a b => pt_ext (pw D j) fun i => by
    refine (tuple_pr _ _ i).trans (Eq.trans ?_ (lift_mul_pr (pw D j) _ _ i).symm)
    rw [tuple_pr, tuple_pr]
    exact D.c_add _ _
  psi := fun x => boxAt D.P.L (fun i => ((pw D j).pr i).left) _ (-1) (fun i => ptK (D.c (x i)))
    (ptK_tuple_pr D j x) (fun i => D.psi (x i))
  psi_gen := fun x => isGen_boxAt _ _ _ _ _ _ _ fun i => D.psi_gen (x i)

def isPowDeg_pow : IsPowDeg (pow D j) D j where
  pw := pw D j
  w := CubePf.idIsoL (boxLB D.P.L (pw D j).pr)
  w_gen := CubePf.idIsoL_isGen (LB.isLB_linComb D.P.isLB _ _)
  w_rig := ⟨_, mapsAt_idIso_pow D.P.L _ _ 1 _ (pow D j).rig_gen,
    corr_boxAt D.P.L _ _ 1 (fun _ => eSec D.P.A) (eSec_pr (pw D j)) (fun _ => D.rig)⟩
  xe := AddEquiv.refl _
  c_pr := fun x i => tuple_pr (pw D j) _ i
  w_psi := fun x => ⟨_, mapsAt_idIso_pow D.P.L _ _ (-1) _ ((pow D j).psi_gen x),
    corr_boxAt D.P.L _ _ (-1) (fun i => ptK (D.c (x i))) (ptK_tuple_pr D j x) (fun i => D.psi (x i))⟩

theorem exists_pow : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (j : ℕ),
    ∃ D' : DegPre R, Nonempty (IsPowDeg D' D j) := by
  intro R _ _ D j
  exact ⟨pow D j, ⟨isPowDeg_pow D j⟩⟩

end GlobalTheory.PowDegPre
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory


open Geo.Tor in
theorem isSymmetric_of_symmetry_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm

theorem exists_pelUnif_pow : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of R))) (P : Geo.Tor.PELUnif I t) (j : ℕ), UnifPowSt3 (I := I) → (∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre P.D.toPre j)) → (∃ A' : PolAV (Spec (CommRingCat.of (FractionRing R))), Nonempty (IsPowPolAV A' P.A j)) → ∃ (t' : Geo.Tor.SAB H (Spec (CommRingCat.of R))) (P' : Geo.Tor.PELUnif I t') (pG : IsPowGrp t'.G t.G j) (pD : IsPowDeg P'.D.toPre P.D.toPre j) (pA : IsPowPolAV P'.A P.A j), Nonempty (UnifPowOf3 pD pA pG P'.U P.U) ∧ (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧ ∀ (a : NumberField.RingOfIntegers E) (x : P'.D.toPre.X), pD.xe (a • x) = a • pD.xe x := by
  intro hG R _ _ I E _ _ _ H t P j hU ⟨D', ⟨pD⟩⟩ ⟨A', ⟨pA⟩⟩
  letI := H.starRing
  let pG : IsPowGrp (powObj t.G j) t.G j := powIsPowGrp t.G j
  obtain ⟨U', ⟨Q⟩⟩ := hU P.D P.A t.G P.U j D' A' (powObj t.G j) pD pA pG
  obtain ⟨act', hact⟩ := (GlobalTheory.exists_powAct _ _ _ j pG).2 _ t.act
  have iso : Geo.Tor.LBIso U'.LG.L (boxLB t.PP.L pG.pr) := by
    rw [← P.bundle]; exact ⟨Q.wL, Q.wL_gen⟩
  let t' : Geo.Tor.SAB H (Spec (CommRingCat.of R)) :=
    { G := powObj t.G j
      semi := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ j pG t.semi
      act := act'
      PP := U'.LG
      cub := U'.cubG
      sym := isSymmetric_of_symmetry_generator U'.LG U'.symG U'.symG_gen U'.symG_rig
      adj := fun a => GlobalTheory.PowAdj.lbIso_cube_pow _ _ _ j pG _ _ t.PP.isLB U'.LG.isLB iso _ _ _ _ (hact a) (hact (H.bar a)) (t.adj a)
      prim := GlobalTheory.PowPrimitive.lbIso_cube_pow _ _ _ j pG _ _ t.PP.isLB U'.LG.isLB iso _ _ (hact H.w0) t.prim }
  letI md : Module (NumberField.RingOfIntegers E) D'.toPre.X := pD.xe.module _
  have hx : ∀ (a : NumberField.RingOfIntegers E) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x := fun a x =>
    pD.xe.apply_symm_apply _
  obtain ⟨oD', hoD⟩ := GlobalTheory.powDeg_diagonal_action hG R j _ _ pD _ hx P.oD
  obtain ⟨rA, hrA⟩ := (GlobalTheory.exists_powAct _ _ _ j pA.toIsPowGrp).1 _ P.oA.toRingAct
  let oA' : A'.OAct (NumberField.RingOfIntegers E) :=
    { toRingAct := rA
      rosati := fun a => GlobalTheory.rosatiAdj_pow _ _ _ j pA.toIsPowGrp _ _ P.A.isLB A'.isLB ⟨pA.w, pA.w_gen⟩ _ _ _ _ (hrA a)
        (hrA (star a)) (P.oA.rosati a) }
  let P' : Geo.Tor.PELUnif I t' :=
    { D := D'
      oD := oD'
      A := A'
      oA := oA'
      U := U'
      bundle := rfl
      lin := GlobalTheory.oLinear_of_unifPow R I j _ _ _ _ _ _ pD pA pG U' P.U Q _ hx P.oD oD' P.oA oA' t.act.toRingAct act'.toRingAct
        hoD hrA hact P.lin
      w0 := GlobalTheory.PsiWZeroProd.main R j _ _ pD _ hx P.oD oD' hoD H.w0 P.w0 }
  exact ⟨t', P', pG, pD, pA, ⟨Q⟩, hact, hx⟩

end GlobalTheory
end
