module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

section Transport

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {P B : LB Y}

def isoSec (w : LB.Iso P B) (hw : w.IsGen) : (LB.div B P).Sec := ⟨fun i => (w.s i : _), fun i j => by
  have := congrArg Units.val (hw i j)
  rw [Units.val_mul] at this
  exact this⟩

theorem val_congr_pt {O : Y.Opens} {R : Type} [CommRing R] {x x' : Sp R ⟶ Y} (h : x = x') (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hO' : ⊤ ≤ x' ⁻¹ᵁ O) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst h; rfl

theorem val_restr_eq {O O' : Y.Opens} (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ Y) (i : B.ι)
    (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

end Transport



theorem exists_rule_of_cls_pull : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)) (L : LB (X₀ TF.Y Z)) (hL : L.IsLB), CechPic.pull (π₀ TF.X Z) (cls L hL) = cls (L₀ TF.X Z la) (isLB_L₀ TF.X Z _) → ∃ Φ : H0 (s₀ TF.Y Z) L ⊤ → Rul Y.d.Xo₂ Y.d.c₂, (∀ t, nonzeroLocus (toSec t) ≤ (j₀ TF.Y Z).opensRange → Φ t ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) ∧ ∀ (y : FrPt Y.d.Xo₂ Y.d.c₂ ℂ) (v : Sp ℂ ⟶ V₀ TF.Y Z), v ≫ i₀ TF.Y Z = ptF y → ∀ (k : L.ι) (hk : ⊤ ≤ (v ≫ j₀ TF.Y Z) ⁻¹ᵁ L.U k), ∃ lam : ℂˣ, ∀ t, evR Y.d.Xo₂ Y.d.c₂ (Φ t) y = lam * H0.val (v ≫ j₀ TF.Y Z) k le_top hk t := by
  intro D T j Y e o hG hE Z TF la L hL hc
  have hP : (L.pull (π₀ TF.X Z)).IsLB := LB.isLB_pull hL _
  have hB := isLB_L₀ TF.X Z la
  obtain ⟨w, hw⟩ := (cls_eq_iff hP hB).1 ((cls_pull hL _ hP).trans hc)
  let C := divChart hB hP
  let G : H0 (str₀ TF.X Z) (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))) ⊤ := H0.ofSec _ ⊤ (isoSec w hw)
  let sOf : H0 (s₀ TF.Y Z) L ⊤ → H0 (str₀ TF.X Z) (L₀ TF.X Z la) ⊤ := fun t =>
    C.mul (H0.pull (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) G
  choose f hf hf' using fun t => exists_suppOn_sec₀_eq _ _ _ _ _ _ _ _ _ (AllWt.exOf _ la 0) (H0.restr le_top (sOf t))
  refine ⟨fun t => (f t).1, fun t ht => ?_, fun yy v hv k hk => ?_⟩
  · have hs : sOf t ∈ vanBd TF.X Z la := (mem_vanBd _ _).2 fun y hy hn => by
      obtain ⟨τ, ha, hb, hcc⟩ := C.cover y
      have u1 : IsUnit (H0.germ (C.c τ) y (memTop y) hcc (sOf t)) := by
        rw [← ger_toSec]; exact (isUnit_ger_iff _ hcc).2 hn
      have e3 := C.germ_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G τ y (memTop y) ha hb hcc
      have u1' : IsUnit (H0.germ (C.a τ) y (memTop y) ha
          (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t : H0 (str₀ TF.X Z) (L.pull (π₀ TF.X Z)) ⊤) *
          H0.germ (C.b τ) y (memTop y) hb G) := (congrArg IsUnit e3).mp u1
      have u2 := (congrArg IsUnit (H0.germ_pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top (C.a τ) y (memTop y) ha t)).mp
        (isUnit_of_mul_isUnit_left u1')
      have u3 := (isUnit_map_iff (Scheme.Hom.stalkMap (π₀ TF.X Z) y).hom _).1 u2
      rw [← ger_toSec] at u3
      obtain ⟨v', hv'⟩ := ht ((isUnit_ger_iff _ _).1 u3)
      refine hy (show TF.X.π (inc₀ TF.X Z y) ∈ LogKS.interior TF.Y from ⟨i₀ TF.Y Z v', ?_⟩)
      rw [← Scheme.Hom.comp_apply, ← j₀_ι, Scheme.Hom.comp_apply, hv', ← Scheme.Hom.comp_apply, morphismRestrict_ι,
        Scheme.Hom.comp_apply]
    obtain ⟨g, hg⟩ := vanBd_le_space D T j Y e o hG hE Z TF la hs
    have e0 : f t = Submodule.inclusion (cusp_le_secZ Z Y.U la) g := by
      refine sub_eq_zero.1 (eq_zero_of_sec₀ TF.X Z (Submodule.sub_mem _ (hf t) g.2.2) ?_)
      rw [map_sub, hf' t, ← hg]
      exact sub_self _
    show (f t).1 ∈ _
    rw [e0]
    exact g.2
  · have e1 : TF.X.ptY yy ≫ TF.X.π = v ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
      rw [(TF.X.lies_ptY yy).1, j₀_ι, ← Category.assoc, hv]
      rfl
    have hr : Set.range (TF.X.ptY yy) ⊆ Set.range (inc₀ TF.X Z) := by
      rintro _ ⟨s, rfl⟩
      refine ⟨⟨_, show TF.X.π (TF.X.ptY yy s) ∈ barComp TF.Y Z from ?_⟩, rfl⟩
      rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
      exact ((v ≫ j₀ TF.Y Z) s).2
    let zz := IsOpenImmersion.lift (inc₀ TF.X Z) (TF.X.ptY yy) hr
    have hzz : zz ≫ inc₀ TF.X Z = TF.X.ptY yy := IsOpenImmersion.lift_fac _ _ _
    have e2 : zz ≫ π₀ TF.X Z = v ≫ j₀ TF.Y Z := by
      have h1 : (zz ≫ π₀ TF.X Z) ≫ (barComp TF.Y Z).ι = (v ≫ j₀ TF.Y Z) ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, Category.assoc, ← e1, ← hzz, Category.assoc]
        exact congrArg (zz ≫ ·) (morphismRestrict_ι TF.X.π (barComp TF.Y Z))
      exact (cancel_mono _).1 h1
    obtain ⟨k', hk'⟩ := exists_chart_of_field (TF.X.F.isLB_LL (AllWt.exOf (T.Q.Dw j) la 0)) (TF.X.pt yy ≫ TF.X.inc)
    obtain ⟨Q, tt, hQ, htt⟩ := FlagCover.exists_chartFr_frBor TF.X yy k' hk'
    have hO : ⊤ ≤ (TF.X.pt yy ≫ TF.X.inc) ⁻¹ᵁ flagOpen TF.X :=
      FlagMod.le_preimage_map TF.X.inc (top_le_inc TF.X) le_top
    have hzO : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ flagOpen TF.X := by rw [hzz, ← FlagCover.pt_inc]; exact hO
    have hzk : ⊤ ≤ (zz ≫ inc₀ TF.X Z) ⁻¹ᵁ (TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0)).U k' := by
      rw [hzz, ← FlagCover.pt_inc]; exact hk'
    have hTop : ⊤ ≤ zz ⁻¹ᵁ (⊤ : (Y₀ TF.X Z).Opens) := fun _ _ => trivial
    have hz1 : ⊤ ≤ zz ⁻¹ᵁ U₀ TF.X Z := hzO
    have hz2 : ⊤ ≤ zz ⁻¹ᵁ (L₀ TF.X Z la).U (pIdx _ (inc₀ TF.X Z) k') := fun s hs => mem_pIdx.2 (hzk hs)
    have hπ1 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ (⊤ : (X₀ TF.Y Z).Opens) := fun _ _ => trivial
    have hπ2 : ⊤ ≤ (zz ≫ π₀ TF.X Z) ⁻¹ᵁ L.U k := by rw [e2]; exact hk
    have hz3 : ⊤ ≤ zz ⁻¹ᵁ (L.pull (π₀ TF.X Z)).U (pIdx L (π₀ TF.X Z) k) := fun s hs => mem_pIdx.2 (hπ2 hs)
    have hz4 : ⊤ ≤ zz ⁻¹ᵁ (LB.div (L₀ TF.X Z la) (L.pull (π₀ TF.X Z))).U
        (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) := fun s hs => ⟨hz2 hs, hz3 hs⟩
    have hu : IsUnit (H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G) := by
      rw [H0.val_ofSec]
      exact (w.s (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)).isUnit.map (GlobalTheory.TangentOrigin.evalPt zz _ hz4)
    obtain ⟨c0, hc0⟩ : ∃ c0 : ℂˣ, ∀ g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0),
        evR _ _ g.1 yy = c0.val * H0.val (TF.X.pt yy ≫ TF.X.inc) k' hO hk' (secOf TF.X _ g) :=
      ⟨_, fun g => evR_eq_val_secOf g hO hQ htt⟩
    refine ⟨c0 * hu.unit, fun t => ?_⟩
    show evR _ _ (f t).1 yy = _
    rw [hc0 (f t)]
    rw [val_congr_pt (p := flagStr TF.X) (B := TF.X.LL (AllWt.exOf (T.Q.Dw j) la 0))
      ((FlagCover.pt_inc TF.X yy).trans hzz.symm) k' hO hk' hzO hzk]
    rw [show H0.val (zz ≫ inc₀ TF.X Z) k' hzO hzk (secOf TF.X _ (f t)) =
        H0.val zz (pIdx _ (inc₀ TF.X Z) k') hz1 hz2 (sec₀ TF.X Z _ (f t)) from
      (H0.val_pull (inc₀ TF.X Z) le_rfl zz (pIdx _ _ k') hz1 hz2 hzO hzk _).symm]
    rw [hf' t, val_restr_eq le_top zz _ hTop hz1 hz2]
    have e4 : H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) =
        H0.val (v ≫ j₀ TF.Y Z) k le_top hk t :=
      (H0.val_pull (π₀ TF.X Z) le_top zz (pIdx _ _ k) hTop hz3 hπ1 hπ2 t).trans (val_congr_pt e2 k hπ1 hπ2 le_top hk t)
    have e5 : H0.val zz (pIdx _ (inc₀ TF.X Z) k') hTop hz2 (sOf t) =
        H0.val zz (pIdx L (π₀ TF.X Z) k) hTop hz3 (H0.pull (p := s₀ TF.Y Z) (π₀ TF.X Z) le_top t) *
          H0.val zz (C.b (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k)) hTop hz4 G :=
      C.val_mul (p := str₀ TF.X Z) (H0.pull (π₀ TF.X Z) le_top t) G (pIdx _ (inc₀ TF.X Z) k', pIdx L (π₀ TF.X Z) k) zz
        hTop hz3 hz4 hz2
    rw [e5, e4, Units.val_mul, IsUnit.unit_spec]
    ring

end GlobalTheory.OrbitSep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelChangePairing

open GlobalTheory.CechPic

section Lift

variable {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B]

theorem lift_mul_lift' (x x' : T ⟶ A) (y y' : T ⟶ B) : lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

theorem lift_pow_eq (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) : lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

theorem lift_one_one : (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

end Lift

theorem isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (m : ℕ) :
    IsMonHom ((𝟙 A) ^ m : A ⟶ A) := by
  induction m with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem pc_mul_right {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {P : LB (G2 A).left} (hP : P.IsLB)
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (T : Over S) (x y y' : T ⟶ A) :
    DiagPairing.pc hP x (y * y') = DiagPairing.pc hP x y + DiagPairing.pc hP x y' := by
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have z₁ : ∀ z : T ⟶ A, DiagPairing.pc hP 1 z = 0 := fun z => by
    obtain ⟨t, ht⟩ := h₁
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e
    have q : lift (1 : T ⟶ A) z = z ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [q, Over.comp_left, pull_comp, e, map_zero]
  have z₂ : ∀ z : T ⟶ A, DiagPairing.pc hP z 1 = 0 := fun z => by
    obtain ⟨t, ht⟩ := h₂
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e
    have q : lift z (1 : T ⟶ A) = z ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [q, Over.comp_left, pull_comp, e, map_zero]
  have h := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hAA P hP T (lift 1 y) (lift 1 y') (lift x 1)
  have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![lift 1 y * lift 1 y' * lift x 1, lift 1 y * lift 1 y',
    lift 1 y * lift x 1, lift 1 y' * lift x 1, lift 1 y, lift 1 y', lift x 1, 1] k).left) ![1, -1, -1, -1, 1, 1, 1, -1]
  have e := (cls_eq_zero_iff hl).2 h
  rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
  simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  simp only [lift_mul_lift', _root_.mul_one, _root_.one_mul, ← lift_one_one] at e
  have o : (1 : T ⟶ G2 A) = lift (1 : T ⟶ A) 1 := lift_one_one
  rw [o] at e
  have a1 := z₁ (y * y')
  have a2 := z₁ y
  have a3 := z₁ y'
  have a4 := z₂ x
  have a5 := z₁ 1
  unfold DiagPairing.pc at a1 a2 a3 a4 a5 ⊢
  rw [a1, a2, a3, a4, a5] at e
  rw [← sub_eq_zero, ← e]
  abel

theorem weilIs_pow_pos {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hG : Out.GlobalFnsSt)
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L k x y c) {j : ℕ} (hj : 0 < j) :
    Out.WeilIs A L k (x ^ j) y (c ^ j) := by
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simpa using h
    · rw [pow_succ x j, pow_succ c j]
      exact DiagPairing.weilIs_mul_left hG hA hL (ih hj') h

theorem weilIs_levelChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N m : ℕ), 0 < N → 0 < m → ((N * m : ℕ) : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ (N * m) = 1 → b ^ (N * m) = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P ((N * m : ℕ) : ℤ) (lift a 1) (lift 1 b) c → Out.WeilIs (G2 A) P N (lift (a ^ m) 1) (lift 1 (b ^ m)) (c ^ m) := by
  intro S A _ _ hA P hP h₁ h₂ κ _ _ y N m hN hm hNm a b ha hb c hc
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hB' := pc_mul_right A hA hP h₁ h₂
  haveI := isMonHom_id_pow A m
  let ψ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ (𝟙 A) ^ m)
  have e : ∀ {T : Over S} (u v : T ⟶ A), lift u v ≫ ψ = lift u (v ^ m) := fun u v => by
    simp only [ψ, comp_lift, ← Category.assoc, MonObj.comp_pow, Category.comp_id, lift_fst, lift_snd]
  have hψ' : ψ = lift (fst A A) (snd A A ^ m) := by
    rw [← e (fst A A) (snd A A), lift_fst_snd, Category.id_comp]
  have hL : (lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have hiso : LBIso (lbPow P m) (P.pull ψ.left) := by
    refine (cls_eq_iff hL (pull_isLB hP _)).1 ?_
    rw [cls_lbPow hP, cls_pull hP, hψ']
    have e' := DiagPairing.pc_pow_right hP hB' (fst A A) (snd A A) m
    unfold DiagPairing.pc at e'
    rw [e', lift_fst_snd]
    exact congrArg (m • ·) (pull_id _).symm
  have hNκ : (N : κ) ≠ 0 := by
    rw [Nat.cast_mul] at hNm
    exact left_ne_zero_of_mul hNm
  have hx : (lift (a ^ m) 1 : Over.mk y ⟶ G2 A) ^ N = 1 := by
    rw [lift_pow_eq, ← pow_mul, mul_comm m N, ha, one_pow, lift_one_one]
  have hy : (lift 1 (b ^ m) : Over.mk y ⟶ G2 A) ^ N = 1 := by
    rw [lift_pow_eq, ← pow_mul, mul_comm m N, hb, one_pow, lift_one_one]
  obtain ⟨c₀, h₀⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ y N hN hNκ _ _ hx hy
  have h₀' : Out.WeilIs (G2 A) P (N : ℤ) (lift (a ^ m) 1 ≫ ψ) (lift 1 b ≫ ψ) c₀ := by
    rw [e, e, one_pow]; exact h₀
  have h₁' : Out.WeilIs (G2 A) P ((N : ℤ) * (m : ℕ)) (lift (a ^ m) 1) (lift 1 b) c₀ :=
    GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP ψ hiso h₀'
  have h₂' : Out.WeilIs (G2 A) P ((N * m : ℕ) : ℤ) (lift (a ^ m) 1) (lift 1 b) (c ^ m) := by
    have := weilIs_pow_pos hG hAA hP hc hm
    rwa [lift_pow_eq, one_pow] at this
  have hc₀ : c₀ = c ^ m :=
    GlobalTheory.CommutatorPairing.weilIs_unique hG hAA hP (by rw [Nat.cast_mul]; exact h₁') h₂'
  rw [← hc₀]
  exact h₀

end GlobalTheory.LevelChangePairing
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

theorem range_sub_iff {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (W : Set X) (p₀ : Sp k) :
    Set.range x.base ⊆ W ↔ x.base p₀ ∈ W := by
  refine ⟨fun H => H ⟨p₀, rfl⟩, ?_⟩
  rintro H _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p p₀]


open GlobalTheory.SiegelPull in
theorem exists_open_sympLev : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  intro h M S' _ t G _ _ P lev hab hP hr₁ hr₂ hsy hM hodd hadd htor
  let Good : S'.Opens → Prop := fun W => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S')
    (β : cycAway M →+* k) (z : kˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      SympAt P h M lev k x z
  have hsup : ∀ (k : Type) [Field k] (x : Sp k ⟶ S'), Set.range x.base ⊆ (sSup {W | Good W} : S'.Opens) →
      ∃ W, Good W ∧ Set.range x.base ⊆ W := by
    intro k _ x hx
    let p₀ : Sp k := (⊥ : PrimeSpectrum k)
    rw [range_sub_iff x _ p₀] at hx
    obtain ⟨W, hW, hpW⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨W, hW, (range_sub_iff x _ p₀).2 hpW⟩
  refine ⟨sSup {W | Good W}, fun V hV => ?_, ?_⟩
  · have pb := Pdiv.PullbackComparison.isGrpPullback V.ι G
    refine (isSympLev_iff _ _ _ _ _ _).2 ⟨fun a b => push_injective pb _ ?_, fun a => push_injective pb _ ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · rw [map_mul, push_secPull', push_secPull', push_secPull', hadd, MonObj.comp_mul]
    · rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, htor, MonObj.comp_one]
    · rw [sympAt_pullback_iff V.ι hP (pull_isLB hP _) pb (Pdiv.PullbackComparison.isSquare V.ι G)
        (Pdiv.PullbackComparison.gen_refl _ (pull_isLB hP _)) (fun a => secPull_left pb _)]
      obtain ⟨W, hW, hxW⟩ := hsup k (x ≫ V.ι) (by
        rintro _ ⟨p, rfl⟩
        exact hV (by first | exact (x.base p).2 | simp | (rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩)))
      exact hW k (x ≫ V.ι) β z hxW (by rw [Category.assoc]; exact hx) hz
  · intro T g c' φ φ₂ pb sq iso hl
    rintro _ ⟨τ, rfl⟩
    obtain ⟨K, _, _, x₀, ⟨q, hq⟩⟩ := GlobalTheory.SiegelTypings.exists_geomPt τ
    obtain ⟨β, hβ⟩ := (⟨(Spec.preimage (x₀ ≫ g ≫ t)).hom, by simp [spMap]⟩ : ∃ β : cycAway M →+* K, spMap β = x₀ ≫ g ≫ t)
    let z : Kˣ := ((GlobalTheory.LowChart.isUnit_zetaAway M hM).map β).unit
    have hc : SympAt c'.P h M c'.lev K x₀ z := c'.geom K x₀ β z hβ.symm rfl
    obtain ⟨hS₁, hS₂, hS₃⟩ := (sympAt_pullback_iff g hP c'.isLB pb sq iso hl K x₀ z).1 hc
    have e₁ := GlobalTheory.T.level_sections_exact_kernel_locus_open S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₂ := GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₃ := GlobalTheory.T.symmetric_bundle_level_odd S' M t G P h lev hab hP hr₁ hr₂ hsy hM hodd hadd htor K (x₀ ≫ g) β z (by rw [Category.assoc, hβ]) rfl
    obtain ⟨W₁, hW₁, H₁⟩ := e₁ hS₁
    obtain ⟨W₂, hW₂, H₂⟩ := e₂ hS₂
    obtain ⟨W₃, hW₃, H₃⟩ := e₃ hS₃
    have hgood : Good (W₁ ⊓ W₂ ⊓ W₃) := fun k _ _ x β' z' hx hxt hz' =>
      ⟨H₁ k x (hx.trans (le_trans inf_le_left inf_le_left)), H₂ k x (hx.trans (le_trans inf_le_left inf_le_right)),
        H₃ k x β' z' (hx.trans inf_le_right) hxt hz'⟩
    have hmem : g.base τ ∈ (W₁ ⊓ W₂ ⊓ W₃ : S'.Opens) := by
      have e : (x₀ ≫ g).base q = g.base τ := by first | simp [← hq] | (rw [Scheme.Hom.comp_apply, hq]) | (rw [Scheme.comp_base_apply, hq])
      rw [← e]
      exact ⟨⟨hW₁ ⟨q, rfl⟩, hW₂ ⟨q, rfl⟩⟩, hW₃ ⟨q, rfl⟩⟩
    exact (le_sSup (show W₁ ⊓ W₂ ⊓ W₃ ∈ {W | Good W} from hgood)) hmem

end GlobalTheory.SympLevLocus
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_localFormOfTensorSection_in_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    δ.IsLB → ⊤ ≤ ξ ⁻¹ᵁ δ.U i → ∃ t : (KeyVals.bL L ξ).L.Sec, KeyVals.IsLocSec σ i ξ t := by
  first | exact @GlobalTheory.KeyValsSec.exists_locSec | exact GlobalTheory.KeyValsSec.exists_locSec | (intros; apply GlobalTheory.KeyValsSec.exists_locSec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric := by
  first | exact @GlobalTheory.KeyVals.isSymmetric_bL | exact GlobalTheory.KeyVals.isSymmetric_bL | (intros; apply GlobalTheory.KeyVals.isSymmetric_bL <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.localFormsTensorSection_genericFibre_transitionGerm : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  first | exact @GlobalTheory.KeySecRel.locSec_eq_germ_mul | exact GlobalTheory.KeySecRel.locSec_eq_germ_mul | (intros; apply GlobalTheory.KeySecRel.locSec_eq_germ_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.principalPolarisationOnAbLocus_genericFibre : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsOpen (abLocus G) →
    genericPoint S ∈ abLocus G → PolOnAb G L.L → PolOnAb (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)).L := by
  first | exact @GlobalTheory.KeyValsPol.polOnAb_genPt | exact GlobalTheory.KeyValsPol.polOnAb_genPt | (intros; apply GlobalTheory.KeyValsPol.polOnAb_genPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  first | exact @GlobalTheory.KeyVals.nzFib_of_isLocSec | exact GlobalTheory.KeyVals.nzFib_of_isLocSec | (intros; apply GlobalTheory.KeyVals.nzFib_of_isLocSec <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.dualTangentBasis_pulledFrame_compatible_pointChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (c : VB.Chart (LieVB.omega G) g) (R R' : Type)
    [CommRing R] [CommRing R'] (ξ : Sp R ⟶ S) (r : R →+* R') (ξ' : Sp R' ⟶ S) (y : Fin g → (epsR R ⟶ KeyVals.bG G ξ))
    (y' : Fin g → (epsR R' ⟶ KeyVals.bG G ξ')), spMap r ≫ ξ = ξ' → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    KeyVals.IsDual c ξ y → KeyVals.IsDual c ξ' y' →
    ∀ F : DualNumber R →+* DualNumber R', (∀ a, F (algebraMap R _ a) = algebraMap R' _ (r a)) →
      F DualNumber.eps = DualNumber.eps → ∀ j, (y' j).left ≫ pullback.fst G.hom ξ' = spMap F ≫ (y j).left ≫ pullback.fst G.hom ξ := by
  first | exact @GlobalTheory.KeyVals.Vec.dual_vec | exact GlobalTheory.KeyVals.Vec.dual_vec | (intros; apply GlobalTheory.KeyVals.Vec.dual_vec <;> assumption)
end
