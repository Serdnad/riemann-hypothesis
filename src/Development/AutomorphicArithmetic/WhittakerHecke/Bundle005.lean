module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.OneMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveRes

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem exists_local_lift {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {U : Scheme.{0}}
    (p : P.PA.obj (op U)) (x : U) :
    ∃ O : U.Opens, x ∈ O ∧ ∃ t : Sx (cech P.e) 0 (O : Scheme.{0}),
      ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0})) t =
        Quotient.mk (P.relS (O : Scheme.{0})) (P.PA.map O.ι.op p) := by
  obtain ⟨O, a, h, u, hx, hv⟩ := P.onto p.1 p.2 x
  refine ⟨O, hx, cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl), ?_⟩
  have key : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0}))
      (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl)) =
      Quotient.mk (P.relS (O : Scheme.{0})) (a ≫ P.ρ, P.v a) := by
    change Quotient.mk _ (P.sv (Sx.map P.bunF (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl))) 0) = _
    rw [P.sv_bunF, pts_cechPt]
  rw [key]
  exact Quotient.sound ⟨h, u, hv⟩

theorem UpperTheory.projBundleData_bundle_isLocallySurjective_etale :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d),
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} ((P.bunF ≫ P.pS).app (op ⦋0⦌)) := by
  intro T W r d P
  constructor
  intro U s
  obtain ⟨p, rfl⟩ := Quotient.exists_rep s
  choose O hO t ht using fun x => exists_local_lift P p x
  have hc : TopologicalSpace.IsOpenCover O := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hO x⟩
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hc))
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  exact ⟨t x, ht x⟩
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem comp_hom_eq_of_coords {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (U : Scheme.{0})
    (a b : Sx (cech P.e) 0 U)
    (hab : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) a = ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) b) :
    pts P.e a 0 ≫ P.e = pts P.e b 0 ≫ P.e := by
  have hq : (⟦P.sv (Sx.map P.bunF a) 0⟧ : Quotient (P.relS U)) = ⟦P.sv (Sx.map P.bunF b) 0⟧ := hab
  have hr := Quotient.exact hq
  change P.rel U _ _ at hr
  rw [PBData.sv_bunF, PBData.sv_bunF] at hr
  obtain ⟨h, u, hu⟩ := hr
  exact P.inj _ _ h u hu

theorem UpperTheory.projBundleData_cech_existsUnique_simplex_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx (cech P.e) 0 U),
        (∀ i j, ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) (t i) = ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) (t j)) →
        ∃! z : Sx (cech P.e) n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i := by
  intro T W r d P n U t ht
  let y : Fin (n + 1) → (U ⟶ P.T') := fun i => pts P.e (t i) 0
  have hy : ∀ i, y i ≫ P.e = y 0 ≫ P.e := fun i => comp_hom_eq_of_coords P U (t i) (t 0) (ht i 0)
  have key : ∀ (z : Sx (cech P.e) n U) (i : Fin (n + 1)),
      Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i ↔ pts P.e z i = y i := by
    intro z i
    constructor
    · intro h
      have := congrFun (congrArg (pts P.e) h) 0
      rw [pts_along] at this
      simpa using this
    · intro h
      apply pts_inj
      funext j
      rw [pts_along]
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      simpa using h
  refine ⟨cechPt P.e n (y 0 ≫ P.e) y hy, fun i => (key _ i).2 (by rw [pts_cechPt]), ?_⟩
  intro z hz
  apply pts_inj
  rw [pts_cechPt]
  funext i
  exact (key z i).1 (hz i)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

theorem UpperTheory.projBundleData_exists_simplex_of_rel :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → P.PA.obj (op U)),
        (∀ i j, P.rel U (t i) (t j)) → ∃ z : Sx P.S n U, ∀ i, P.sv z i = t i := by
  intro T W r d P n U t ht
  choose h u hu using ht
  let F : ComposableArrows (Um d Γ(U, ⊤)) n :=
    { obj := fun i => (t i).2
      map := fun {i j} _ => ⟨(P.g (t i).1 (t j).1 (h i j), u i j), hu i j⟩
      map_id := by
        intro i
        apply Subtype.ext
        apply Prod.ext
        · exact P.g_self _ _
        · show u i i = 1
          apply Um.unit_unique (t i).2
          have e := hu i i
          rw [P.g_self] at e
          rw [Units.val_one, one_smul, ← e]
          simp
      map_comp := by
        intro i j k _ _
        apply Subtype.ext
        apply Prod.ext
        · show P.g (t i).1 (t k).1 (h i k) = P.g (t j).1 (t k).1 (h j k) * P.g (t i).1 (t j).1 (h i j)
          exact (P.g_coc _ _ _ (h i j) (h j k)).symm
        · show u i k = u j k * u i j
          apply Um.unit_unique (t k).2
          rw [← hu i k, ← P.g_coc _ _ _ (h i j) (h j k), Units.val_mul, ← Matrix.mulVec_mulVec,
            hu i j, Matrix.mulVec_smul, hu j k, smul_smul, Units.val_mul, mul_comm] }
  let x : Sx (cech P.c) n U := cechPt P.c n ((t 0).1 ≫ P.c) (fun i => (t i).1) (fun i => h i 0)
  have hx : pts P.c x = fun i => (t i).1 := pts_cechPt _ _ _ _
  have key : Sx.map P.bunV x = Sx.map (PGL.pr d) F := by
    show (P.gFun (pts P.c x) (pts_eq P.c x) : ComposableArrows (SingleObj (GL (Fin d) Γ(U, ⊤))) n) =
      F ⋙ Um.toGL d Γ(U, ⊤)
    fapply CategoryTheory.Functor.ext
    · intro i
      rfl
    · intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      show P.g (pts P.c x i) (pts P.c x j) _ = P.g (t i).1 (t j).1 (h i j)
      exact P.g_congr (congrFun hx i) (congrFun hx j) _ _
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U x F key
  refine ⟨z, fun i => ?_⟩
  show (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i,
    (Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i) = t i
  rw [hz1, hz2, hx]
  rfl
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem arrow_heq {A : Type} [CommRing A] {N : ℕ} {v v' w w' : Um N A} (hv : v = v') (hw : w = w')
    (p : v ⟶ w) (p' : v' ⟶ w') (h : p.1.1 = p'.1.1) : HEq p p' := by
  subst hv hw
  refine heq_of_eq (Subtype.ext (Prod.ext h (Um.unit_unique w ?_)))
  rw [← p.2, ← p'.2, h]

private theorem arrow_mat {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {n : ℕ} {U : Scheme.{0}}
    (z : Sx P.S n U) {i j : Fin (n + 1)} (hij : i ≤ j) :
    ((show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z).map (homOfLE hij)).1.1 =
      P.g (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i)
        (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) j) (pts_eq P.c _ i j) :=
  (congrArg (fun F : Fin (n + 1) ⥤ SingleObj (GL (Fin d) Γ(U, ⊤)) =>
    (show GL (Fin d) Γ(U, ⊤) from F.map (homOfLE hij))) (P.S_comm z)).symm

theorem UpperTheory.projBundleData_simplex_ext_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {n : ℕ} {U : Scheme.{0}} (z z' : Sx P.S n U),
        (∀ i, P.sv z i = P.sv z' i) → z = z' := by
  intro T W r d P n U z z' h
  have hp : ∀ i, pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i =
      pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z') i := fun i => congrArg Prod.fst (h i)
  have hf : Sx.map (pullback.fst P.bunV (PGL.pr d)) z = Sx.map (pullback.fst P.bunV (PGL.pr d)) z' :=
    pts_inj P.c (funext hp)
  have hobj : ∀ i, (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i =
      (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z').obj i :=
    fun i => congrArg Prod.snd (h i)
  have hg : (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z) =
      (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z') := by
    refine CategoryTheory.Functor.hext hobj (fun i j a => ?_)
    have hij : i ≤ j := leOfHom a
    obtain rfl : a = homOfLE hij := Subsingleton.elim _ _
    refine arrow_heq (hobj i) (hobj j) _ _ ?_
    rw [arrow_mat P z, arrow_mat P z']
    exact P.g_congr (hp i) (hp j) _ _
  exact (UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U _ _ (P.S_comm z)).unique ⟨rfl, rfl⟩ ⟨hf.symm, hg.symm⟩
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem inv_along {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E := by
  intro U hU
  obtain ⟨x⟩ := hU
  exact h U ⟨Sx.map f x⟩

private theorem pull_castHt {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q E n i) := by
  subst hn hi
  rfl

private theorem pull_cpow (hA : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E')
    (y : Ht q E' 2 1) (j : ℕ) : pull _ f _ _ (cpow q y j) = cpow q (pull _ f _ _ y) j := by
  obtain ⟨hcup, hone, -, -⟩ := hA q
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pull_castHt]
    congr 1
    exact hone f hE
  | succ k ih =>
    rw [cpow_succ, cpow_succ, pull_castHt]
    congr 1
    rw [hcup, ih]

private theorem inv_sch_of_is_unit (q : ℕ) (W : Scheme.{0}) (hq : IsUnit (q : Γ(W, ⊤))) : Inv q (sch.obj W) := by
  intro U hU
  obtain ⟨g⟩ := hU
  have g' : U ⟶ W := g
  have := hq.map (CommRingCat.Hom.hom (Scheme.Hom.appTop g'))
  simpa using this

theorem UpperTheory.firstChernClass_projBundle_line_of_twist_equiv :
    In → ∀ (q : ℕ) [NeZero q] {T W : Scheme.{0}} (r : T ⟶ W) (d : ℕ) {Ec Ee : Spc} (ac : Ec ⟶ sch.obj W) (ae : Ee ⟶ sch.obj T)
        (V : Ec ⟶ ofCat (glCat d)) (F : Ee ⟶ pullback V (PGL.pr d)),
        (∀ i : ℤ, Eqv _ ac (tw q i)) → (∀ i : ℤ, Eqv _ ae (tw q i)) → (∀ i : ℤ, Eqv _ F (tw q i)) →
        F ≫ pullback.fst V (PGL.pr d) ≫ ac = ae ≫ sch.map r → IsUnit (q : Γ(W, ⊤)) →
        ∀ (L : Ee ⟶ ofCat (glCat 1)) (ε : ℤˣ),
        (∀ (U : Scheme.{0}) (y : Sx Ee 1 U), lineUnit L y = lineUnit (F ≫ pullback.snd V (PGL.pr d) ≫ PGL.line d) y ^ (ε : ℤ)) →
        ∀ x : Ht q (sch.obj T) 2 1, pull _ ae _ 2 x = c1 q L → PBT q d r x := by
  intro hIn q _ T W r d Ec Ee ac ae V F hac hae hF hcomm hq L ε hL x hx
  obtain ⟨hcup, hone, hc1, -⟩ := hIn.a6nat q
  have iW := inv_sch_of_is_unit q W hq
  have iT : Inv q (sch.obj T) := inv_sch_of_is_unit q T (by
    simpa using hq.map (CommRingCat.Hom.hom (Scheme.Hom.appTop r)))
  have iEc : Inv q Ec := inv_along ac iW
  have iP : Inv q (pullback V (PGL.pr d)) := inv_along (pullback.fst V (PGL.pr d)) iEc
  have iEe : Inv q Ee := inv_along F iP
  have hxe : pull _ ae _ 2 x =
      (ε : ℤ) • pull _ F _ 2 (c1 q (pullback.snd V (PGL.pr d) ≫ PGL.line d)) := by
    rw [hx, UpperTheory.firstChernClass_eq_zsmul_of_lineUnit_eq_zpow hIn.a6add q L _ ε iEe hL, hc1 F _ iP]
  have hee : ∀ k : ℕ, ((ε : ℤ) ^ k) * ((ε : ℤ) ^ k) = 1 := by
    intro k
    rw [← mul_pow, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_pow]
  intro n i
  have hD := hIn.d1 q V iEc n i
  let G : (∀ j : Fin d, Ht q (sch.obj W) (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))) →
      (∀ j : Fin d, Ht q Ec (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))) :=
    fun a j => ((ε : ℤ) ^ (j : ℕ)) • pull _ ac _ _ (a j)
  have hG : Function.Bijective G := by
    constructor
    · intro a b hab
      funext j
      have e := congrFun hab j
      have e2 := congrArg (fun y => ((ε : ℤ) ^ (j : ℕ)) • y) e
      simp only [G, smul_smul, hee, one_smul] at e2
      exact (hac _ _).1 e2
    · intro b
      refine ⟨fun j => Function.surjInv (hac _ _).2 (((ε : ℤ) ^ (j : ℕ)) • b j), ?_⟩
      funext j
      simp only [G, Function.surjInv_eq, smul_smul, hee, one_smul]
  have key : ∀ a, pull _ ae _ n (∑ j : Fin d, Ht.cast (by omega) (by omega)
      ((cup q) (pull _ (sch.map r) (tw q (i - ((j : ℕ) : ℤ))) (n - 2 * ((j : ℕ) : ℤ)) (a j))
        (cpow q x (j : ℕ))) : Ht q (sch.obj T) n i) =
      pull _ F _ n (∑ j : Fin d, Ht.cast (by omega) (by omega)
      ((cup q) (pull _ (pullback.fst V (PGL.pr d)) (tw q (i - ((j : ℕ) : ℤ))) (n - 2 * ((j : ℕ) : ℤ)) (G a j))
        (cpow q (c1 q (pullback.snd V (PGL.pr d) ≫ PGL.line d)) (j : ℕ))) : Ht q _ n i) := by
    intro a

    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pull_castHt, pull_castHt]
    congr 1
    rw [hcup, hcup, pull_cpow hIn.a6nat q ae iT, hxe, UpperTheory.chernPower_zsmul_eq_pow_smul, pull_cpow hIn.a6nat q F iP,
      ← pull_comp, ← hcomm, pull_comp, pull_comp]
    simp only [G, map_zsmul, AddMonoidHom.smul_apply]
  rw [← Function.Bijective.of_comp_iff' (hae i n)]
  convert (hF i n).comp (hD.comp hG) using 1
  funext a
  exact key a
end
