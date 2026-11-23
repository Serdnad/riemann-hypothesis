module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.IsoSat

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isotropic_vector (D : Datum H) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) :
    ∃ x : D.La, x ≠ 0 ∧ ∀ a : 𝓞 E, D.EF (a • x) x = 0 := by
  by_cases h3 : 3 ≤ D.p + D.q
  · have hξ := GlobalTheory.OneSpace.cc_rt H
    have hξ0 := GlobalTheory.OneSpace.rt_ne H
    obtain ⟨G, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H D (H.rt : E) hξ hξ0 (D.p + D.q) rfl
    have hind := GlobalTheory.SplitGenus.indefinite D hp hq G φ hM
    obtain ⟨inj, span, hG, hdet, hEF⟩ := hM
    have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
      refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
      have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
      linear_combination (1 / 2 : E) * h2
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind
    have hz' : FD.herm G z z = 0 := hz
    obtain ⟨N, g, hN, hg⟩ := GlobalTheory.SplitGenus.exists_scaled_map (LinearMap.toSpanSingleton (𝓞 E) _ z) φ inj span
    have h1 : φ (g 1) = (N : E) • z := by rw [hg, LinearMap.toSpanSingleton_apply, one_smul]
    refine ⟨g 1, fun h => ?_, fun a => ?_⟩
    · rw [h, map_zero, eq_comm, smul_eq_zero] at h1
      exact h1.elim (Nat.cast_ne_zero.2 hN.ne') hz0
    · have h2 := hEF (a • g 1) (g 1)
      rw [map_smul φ, h1, show a • (N : E) • z = (a : E) • (N : E) • z from rfl, GlobalTheory.HermModel.herm_smul_left,
        GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right, hz'] at h2
      simp only [zero_mul, mul_zero, map_zero] at h2
      exact_mod_cast h2
  · obtain ⟨k, f, hk, hf⟩ := GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry E H (GlobalTheory.HostModel.hypDatum H) D
      (by change D.p = 1; omega) (by change D.q = 1; omega) 2 two_pos
    have hk0 : (k : ℤ) ^ 2 ≠ 0 := by
      have : k ≠ 0 := by
        rintro rfl
        simp at hk
      positivity
    refine ⟨f (1, 0), fun h => ?_, fun a => ?_⟩
    · have : ((1, 0) : (GlobalTheory.HostModel.hypDatum H).La) = 0 := (GlobalTheory.HostModel.hypDatum H).unimod.1 (LinearMap.ext fun y => by
        have := hf (1, 0) y
        rw [h, map_zero, LinearMap.zero_apply] at this
        rw [map_zero, LinearMap.zero_apply]
        exact (mul_eq_zero.1 this.symm).resolve_left hk0)
      exact one_ne_zero (congrArg Prod.fst this)
    · rw [← map_smul, hf, GlobalTheory.HostModel.hypDatum_smul, smul_zero, GlobalTheory.HostModel.hypDatum_EF_inl_inl, mul_zero]

theorem exists_saturation (D : Datum H) (W : Submodule (𝓞 E) D.La) (hW : W ≤ perp D W) :
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) W := by
  have := D.fin
  let Z : Submodule (𝓞 E) D.La :=
    { carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ W}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact nsmul_mem hx m
        · rw [mul_smul]; exact nsmul_mem hy n
      smul_mem' := by
        rintro a x ⟨n, hn, hx⟩
        exact ⟨n, hn, by rw [smul_comm]; exact W.smul_mem a hx⟩ }
  have hle : W ≤ Z := fun x hx => ⟨1, one_ne_zero, by rwa [one_smul]⟩
  refine ⟨Z, ⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨n, hn, hx⟩ y ⟨m, hm, hy⟩
    have := hW hx _ hy
    simpa [hn, hm] using this
  · rintro n x hn ⟨m, hm, hx⟩
    exact ⟨m * n, mul_ne_zero hm hn, by rwa [mul_smul]⟩
  · have h1 := Submodule.finrank_quotient_add_finrank (W.comap Z.subtype)
    have h2 : Module.finrank (𝓞 E) (Z ⧸ W.comap Z.subtype) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro x
      obtain ⟨⟨x, n, hn, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
      refine ⟨(n : 𝓞 E), Nat.cast_ne_zero.2 hn, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Nat.cast_smul_eq_nsmul]
      exact hx
    rw [← h1, h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]

theorem exists_succ (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z)
    (hr : Module.finrank (𝓞 E) Z + 1 ≤ min D.p D.q) :
    ∃ Z' : Submodule (𝓞 E) D.La, IsIsoSat D Z' ∧ Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) Z + 1 := by
  have := D.fin
  obtain ⟨D', f, ⟨hs, hk, hE⟩, hp, hq⟩ := exists_lowerDatum D Z hZ
  obtain ⟨x', hx0, hx⟩ := exists_isotropic_vector D' (by omega) (by omega)
  obtain ⟨x, rfl⟩ := hs x'
  have := D'.proj
  have hnot : ∀ a : 𝓞 E, a • (x : D.La) ∈ Z → a = 0 := fun a ha => by
    have h := (hk (a • x)).2 ha
    rw [map_smul, smul_eq_zero] at h
    exact h.resolve_right hx0
  let g : (Z × 𝓞 E) →ₗ[𝓞 E] D.La := Z.subtype.coprod (LinearMap.toSpanSingleton (𝓞 E) _ (x : D.La))
  have hg : ∀ u, g u = u.1 + u.2 • (x : D.La) := fun u => rfl
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun u hu => by
    rw [hg] at hu
    have h2 : u.2 = 0 := hnot _ (by rw [eq_neg_of_add_eq_zero_right hu]; exact neg_mem u.1.2)
    rw [h2, zero_smul, add_zero] at hu
    exact Prod.ext (Subtype.ext hu) h2
  obtain ⟨Z', h1, h2⟩ := exists_saturation D (LinearMap.range g) (by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have e1 : D.EF u.1 v.1 = 0 := hZ.1 u.1.2 _ v.1.2
    have e2 : ∀ (a : 𝓞 E) (z : Z), D.EF (a • (x : D.La)) z = 0 := fun a z => (a • x).2 _ z.2
    have e3 : D.EF (u.2 • (x : D.La)) (v.2 • (x : D.La)) = 0 := by
      have h := hx (H.bar v.2 * u.2)
      rw [← map_smul, hE, Submodule.coe_smul, mul_smul, D.adj, bar_bar] at h
      exact h
    rw [hg, hg]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [e1, e2, e3, ef_swap, e2]
    simp)
  refine ⟨Z', h1, ?_⟩
  rw [h2, ← (LinearEquiv.ofInjective g hinj).finrank_eq]
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.snd (𝓞 E) Z (𝓞 E)))
  rw [((LinearMap.snd (𝓞 E) Z (𝓞 E)).quotKerEquivOfSurjective LinearMap.snd_surjective).finrank_eq,
    Module.finrank_self, ← LinearMap.range_inl,
    ← (LinearEquiv.ofInjective _ LinearMap.inl_injective).finrank_eq] at h3
  omega

end GlobalTheory.LowFilt.IsoSat

namespace GlobalTheory.LowFilt

theorem exists_isIsoSat_finrank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ),
    r ≤ min D.p D.q → ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  intro E _ _ _ H D r
  induction r with
  | zero => exact fun _ => ⟨⊥, (isOpp_bot D).isIsoSat, finrank_bot _ _⟩
  | succ r ih =>
    intro hr
    obtain ⟨Z, hZ, rfl⟩ := ih (by omega)
    exact IsoSat.exists_succ D Z hZ hr

end GlobalTheory.LowFilt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  first | exact @GlobalTheory.TensPsiCoord.main | exact GlobalTheory.TensPsiCoord.main | (intros; apply GlobalTheory.TensPsiCoord.main <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.FactorAdj

open AdjComp

def chartPullTwo {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y'' ⟶ X)) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y'' ⟶ Y') (n : Y' ⟶ Y) (hc : ∀ k, φ' k = (h ≫ n) ≫ φ k) :
    ChartPull (LB.LinComb L φ' ε) ((LB.LinComb L φ ε).pull n) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ ((LB.LinComb L φ ε).pull n).U (fun _ => j) := fun j _ hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 ((chartPullSame L φ' φ ε (h ≫ n) hc).le j hy)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L φ' φ ε (h ≫ n) hc).g y j j' hj hj').trans
      (gm_pull_g (LB.LinComb L φ ε) n h y (fun _ => j) (fun _ => j') (le j hj) (le j' hj')).symm }

theorem exists_pull_lam {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} {n : G2 G ⟶ G2 G'} (w : LB.Iso (abelian₂ G L) ((abelian₂ G' L').pull n.left))
    (hw : w.IsGen) (m : T ⟶ G2 G) (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T ⟶ G')) (hx : ∀ i, x i = m ≫ x2 G i)
    (hx' : ∀ i, x' i = (m ≫ n) ≫ x2 G' i) :
    ∃ w' : LB.Iso (cubeLB G x L) (cubeLB G' x' L'), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ T.left) (z : Z) J' J,
      Good L' z J' → Good L z J → adjVal w' p z J' J = lamVal w (p ≫ m.left) z J' J := by
  let a : ChartPull (cubeLB G x L) (abelian₂ G L) m.left := cubePull L m _ _ hx
  let b : ChartPull (cubeLB G' x' L') ((abelian₂ G' L').pull n.left) m.left :=
    chartPullTwo L' _ _ _ m.left n.left (psum_left_pull (m ≫ n) _ _ hx')
  refine ⟨pullIso a b w, pullIso_isGen a b hw, fun Z p z J' J hJ' hJ => ?_⟩
  have mA := Good.mem hJ (fun I : ULift (Finset (Fin 2)) => (psum G x I.down).left) p
  have mB := Good.mem hJ' (fun I : ULift (Finset (Fin 2)) => (psum G' x' I.down).left) p
  refine ((adjVal_of (pullIso a b w) p z J' J _ _ (fun _ => rfl) (fun _ => rfl)).trans
    (gm_pullIso a b w p z (_, _) ⟨mB, mA⟩)).trans ?_
  have e₁ : (fun I : ULift (Finset (Fin 2)) => J (p ≫ (psum G x I.down).left)) =
      fun I => J ((p ≫ m.left) ≫ (psum G (x2 G) I.down).left) := funext fun I => by
    rw [psum_left_pull m _ _ hx I, Category.assoc]
  have e₂ : (fun I : ULift (Finset (Fin 2)) => J' (p ≫ (psum G' x' I.down).left)) =
      fun I => J' ((p ≫ m.left) ≫ n.left ≫ (psum G' (x2 G') I.down).left) := funext fun I => by
    rw [psum_left_pull (m ≫ n) _ _ hx' I, Over.comp_left, Category.assoc, Category.assoc]
  rw [e₁, e₂]
  rfl

theorem exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribSMul.toAddMonoidHom D'.toPre.X F.e) y) (((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D' F
  let m : (pol D').B ⊗ (pol D).B ⟶ G2 (pol D).B := lift (fst _ _ ≫ F.pr) (snd _ _)
  let n : G2 (pol D).B ⟶ G2 (pol D').B := lift (fst _ _ ≫ F.inc) (snd _ _ ≫ F.inc ≫ F.o.onB.act F.f)
  let w₀ : LB.Iso (abelian₂ (pol D).B (pol D).M.L) ((abelian₂ (pol D').B (pol D').M.L).pull n.left) := F.w
  obtain ⟨w, gw, hw⟩ := exists_pull_lam w₀ F.w_gen m ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B]
    ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f]
    (fun i => by
      fin_cases i
      · exact (lift_fst _ _).symm
      · exact (lift_snd _ _).symm)
    (fun i => by
      fin_cases i
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_fst _ _)).trans ?_))
        refine (lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
        exact congrArg (fst (pol D').B (pol D).B ≫ ·) F.pr_inc
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_snd _ _)).trans ?_))
        exact lift_snd_assoc _ _ _)
  refine ⟨w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hP : (lift (toUnit (TK R) ≫ D.toPre.c (F.xp y)) (toUnit (TK R) ≫ D.toPre.c y')).left =
      (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left ≫ m.left := by
    refine congrArg (fun q : TK R ⟶ G2 (pol D).B => q.left) (Eq.symm ((comp_lift _ _ _).trans ?_))
    refine congrArg₂ lift ((lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)) (lift_snd _ _)
    exact congrArg (toUnit (TK R) ≫ ·) (c_xp F y).symm
  have e := F.tau (F.xp y) y' z J₁ J₂ hJ₁ hJ₂
  rw [F.xi_xp, hP] at e
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre _ _).choose_spec.2 _ _ z J₂ hJ₂).trans (e.trans ?_)
  exact congrArg₂ (· * ·) (hw _ _ z J₁ J₂ hJ₁ hJ₂).symm
    ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre (F.e • y) (F.f • F.xi y')).choose_spec.2 _ _ z J₁ hJ₁).symm

end GlobalTheory.MumFam.FactorAdj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_unique_point : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' vs → v' = u' := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_unique | exact GlobalTheory.Mum.TensTor.gtRelV_unique | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumFam.lbIso_lam_retract_adj | exact GlobalTheory.MumFam.lbIso_lam_retract_adj | (intros; apply GlobalTheory.MumFam.lbIso_lam_retract_adj <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs := by
  first | exact @GlobalTheory.Mum.TensTor.VExist.gtRelV_exists | exact GlobalTheory.Mum.TensTor.VExist.gtRelV_exists | (intros; apply GlobalTheory.Mum.TensTor.VExist.gtRelV_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) (DistribSMul.toAddMonoidHom D.toPre.X (Star.star a)) := by
  first | exact @GlobalTheory.MumFam.adj_act | exact GlobalTheory.MumFam.adj_act | (intros; apply GlobalTheory.MumFam.adj_act <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorData_psi_values_through_bundleIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), ∀ χ', (N'.ψ χ' : F) * wv T ν ν' 1 = wv T ν ν' (N'.c χ') * ((∏ i, ∏ j, N.τ (chi T ν ν' χ' i) (chi T ν ν' χ' j) ^ W i j : Fˣ) : F) := by
  first | exact @GlobalTheory.Mum.TensTor.tensFacts_psi | exact GlobalTheory.Mum.TensTor.tensFacts_psi | (intros; apply GlobalTheory.Mum.TensTor.tensFacts_psi <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorTorsionPairing_eq_prod_factor_pairings : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  first | exact @GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod | exact GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod | (intros; apply GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_unique_components : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → IsUnit (W + W.transpose).det → ∀ (v' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv v' us → vs = us := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_components_unique | exact GlobalTheory.Mum.TensTor.gtRelV_components_unique | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_components_unique <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_mul : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us → GtRelV W φ e wv (v' * u') (vs * us) := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_mul | exact GlobalTheory.Mum.TensTor.gtRelV_mul | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_onto (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) (hT : TensFacts W φ e wv)
    (hdet : IsUnit (W + W.transpose).det) (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs :=
  Vonto.of_exist_mul hT hdet (VExist.gtRelV_exists F N N' W φ e wv hT)
    (gtRelV_mul F N N' W φ e wv hT) v'

end GlobalTheory.Mum.TensTor
end
