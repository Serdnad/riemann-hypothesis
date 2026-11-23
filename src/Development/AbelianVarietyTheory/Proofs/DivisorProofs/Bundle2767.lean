module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle068
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilRootLocal

theorem exists_weilIs_root_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (PP : RigLB A), CubicalStr A PP → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (t : Sp R ⟶ S) (n : ℕ) (g h : Over.mk t ⟶ A), g ^ n = 1 → h ^ n = 1 →
    ∃ u : Rˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) := by
  intro S A _ _ hA PP cub R _ _ t n g h hg hh
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have loc : ∀ z : Over.mk t ⟶ A, z ^ n = 1 → ∀ p : (Over.mk t).left, ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A PP.L (n : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := TorsionThetaLocal.exists_theta_of_pow_eq_one S A PP cub R t n z hz
    obtain ⟨θ', hθ'⟩ := CommutatorPairing.exists_pull PP.isLB θ (Out.overResι ⊤)
    exact ⟨⊤, trivial, θ', by rw [hθ', hθ]⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG hA PP.isLB (loc g hg) (loc h hh)
  have pw : ∀ m : ℕ, Out.WeilIs A PP.L (n : ℤ) (g ^ (m + 1)) h (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih =>
      rw [pow_succ g (m + 1), pow_succ c (m + 1)]
      exact DiagPairing.weilIs_mul_left hG hA PP.isLB ih hc
  have e := pw n
  rw [pow_succ g, hg, _root_.one_mul] at e
  have hcn := CommutatorPairing.weilIs_unique hG hA PP.isLB e hc
  rw [pow_succ, mul_eq_right] at hcn
  obtain ⟨u, rfl⟩ : ∃ u : Rˣ, unitOn u = c :=
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).surjective c
  refine ⟨u, unitOn_injective_of_commRing ?_, hc⟩
  show unitOn (u ^ n) = unitOn 1
  rw [unitOn, unitOn, map_pow, map_one]
  exact hcn

end GlobalTheory.WeilRootLocal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.normW_origin : ∀ (V : Type) [CommRing V] [IsDomain V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (A : Over (Sp (FractionRing V))) [GrpObj A] [IsCommMonObj A] (θ : (Over.pullback (jK V)).obj G ⟶ A) [IsMonHom θ]
    (φ : A.left ⟶ G.left), θ.left ≫ φ = pullback.fst G.hom (jK V) →
    ∀ (he : eSec A ≫ φ = spMap (algebraMap V (FractionRing V)) ≫ eSec G)
    (LP : LB A.left) (LL LM : LB G.left), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (rA : LB.Gen (LP.pull (eSec A))) (rL : LB.Gen (LL.pull (eSec G))) (rM : LB.Gen (LM.pull (eSec G)))
      (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ.left) (LM.pull (pullback.fst G.hom (jK V)))),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK V)).obj G).left) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        pullback.fst G.hom (jK V) (r z) ∈ LL.U i → pullback.fst G.hom (jK V) (r z) ∈ LM.U j → θ.left (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) =
          (gm (r ≫ pullback.fst G.hom (jK V)) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ.left) z i k) →
      LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec A) (fun _ => 1)) rA
        (rigPullOf φ (spMap (algebraMap V (FractionRing V))) he LL rL) →
      LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)) rM rL →
      ∀ (z : Sp (FractionRing V)) (JA : (Sp (FractionRing V) ⟶ A.left) → LP.ι) (JG : (Sp (FractionRing V) ⟶ G.left) → LM.ι),
        Good LP z JA → Good LM z JG →
        gw w₀ (eSec ((Over.pullback (jK V)).obj G)) z (JG (jK V ≫ eSec G)) (fun _ => JA (eSec A)) *
            val (L := LP) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rA (𝟙 _) z JA =
          val (L := LM) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) rM (jK V) z JG := by
  intro V _ _ G _ _ A _ _ θ _ φ hφ he LP LL LM hP hL hM rA rL rM ψ e w₀ hpt hψ hε z JA JG gA gG
  have h1 : eSec ((Over.pullback (jK V)).obj G) ≫ θ.left = eSec A := by
    show η[(Over.pullback (jK V)).obj G].left ≫ θ.left = η[A].left
    rw [← Over.comp_left, IsMonHom.one_hom]
  have h2 : eSec ((Over.pullback (jK V)).obj G) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
    rw [← hφ, ← Category.assoc, h1, he]
  have p1 : θ.left (eSec ((Over.pullback (jK V)).obj G) z) = eSec A z := congrArg (fun f => f z) h1
  have p2 : pullback.fst G.hom (jK V) (eSec ((Over.pullback (jK V)).obj G) z) = eSec G (jK V z) :=
    congrArg (fun f => f z) h2
  have p3 : φ (eSec A z) = eSec G (jK V z) := congrArg (fun f => f z) he
  have hA : eSec A z ∈ LP.U (JA (eSec A)) := gA (eSec A)
  have hG : eSec G (jK V z) ∈ LM.U (JG (jK V ≫ eSec G)) := gG (jK V ≫ eSec G)
  obtain ⟨i, hi⟩ := exists_chart hL (eSec G (jK V z))

  have s2 := hpt _ (eSec ((Over.pullback (jK V)).obj G)) z i (JG (jK V ≫ eSec G)) (JA (eSec A))
    (by rw [p2]; exact hi) (by rw [p2]; exact hG) (by rw [p1]; exact hA)
  rw [h2, h1] at s2

  have s3 := (maps_iff ψ (fun _ : PUnit => eSec A) (fun _ => eSec G) (fun _ => 1) rA rL
    (spMap (algebraMap V (FractionRing V))) _ (rigPull_le φ _ he LL) (fun _ => rfl)).1 hψ
    _ (𝟙 _) z (fun _ => i) (fun _ => JA (eSec A))
    (fun _ => by show φ (eSec A z) ∈ _; rw [p3]; exact hi) (fun _ => hA)
  simp only [Category.id_comp, Fintype.prod_unique, zpow_one] at s3

  have hm : jK V z ∈ (LB.wchart LL (fun _ : PUnit => eSec G) (fun _ => i) ⊓
      LB.wchart LM (fun _ : PUnit => eSec G) (fun _ => JG (jK V ≫ eSec G)) : (Sp V).Opens) := by
    exact ⟨Set.mem_iInter.2 fun _ => hi, Set.mem_iInter.2 fun _ => hG⟩
  have s4 := congrArg (gm (jK V) z _) (hε (fun _ => i, fun _ => JG (jK V ≫ eSec G)))
  have eU : gm (jK V) z _ ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s
      (fun _ => i, fun _ => JG (jK V ≫ eSec G))) =
      gm (jK V ≫ eSec G) z (LL.U i ⊓ LM.U (JG (jK V ≫ eSec G))) (e.s (i, JG (jK V ≫ eSec G))) := by
    show gm _ z _ (∏ _k : PUnit, (res _ (pullU (eSec G) _ (e.s (i, JG (jK V ≫ eSec G))))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z _ hm _).trans (gm_pull _ _ z _ (show eSec G (jK V z) ∈ LL.U i ⊓ LM.U (JG (jK V ≫ eSec G)) from ⟨hi, hG⟩) _)
  have s4' := (gm_res _ z _ hm _).symm.trans (s4.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) eU (gm_res _ z _ hm _))))
  rw [val_of rA (𝟙 _) z JA (fun _ => JA (eSec A)) (fun _ => by rw [Category.id_comp]),
    val_of rM (jK V) z JG (fun _ => JG (jK V ≫ eSec G)) (fun _ => rfl), s2, _root_.mul_assoc, ← s3]
  exact inv_mul_eq_of_eq_mul s4'
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unit_value_translated_bundleSection : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (α ν : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k))), (¬ ∀ j, s.f j = 0) → ∃ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J ∧ IsUnit (sval s (DegPre.trF Q (FractionRing R) ν).left z J) := by
  first | exact @GlobalTheory.UnitPt.exists_unit_sval | exact GlobalTheory.UnitPt.exists_unit_sval | (intros; apply GlobalTheory.UnitPt.exists_unit_sval <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBGenericAgree

variable {R : Type} [CommRing R] [IsDomain R]

theorem isUnit_jK_app (c : R) (hc : c ≠ 0) :
    IsUnit ((jK R).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have h := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hu : IsUnit (algebraMap R (FractionRing R) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  rw [h] at this
  exact this

theorem isUnit_gs (Q : DegPre R) (c : R) (hc : c ≠ 0) (z : (DegPre.BF Q (FractionRing R)).left) :
    IsUnit (gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e1 : (DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom =
      ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Over.w (DegPre.prB Q (FractionRing R)), Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)).symm
  rw [e1, ← gs_pull ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) (jK R) z ⊤ trivial,
    gs_eq _ z (jK R ⁻¹ᵁ ⊤) trivial]
  exact ((isUnit_jK_app c hc).map _).map _

theorem f_eq (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R) (hc : c ≠ 0)
    (H : ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J →
      gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s (DegPre.prB Q (FractionRing R)).left z J =
        gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s' (DegPre.prB Q (FractionRing R)).left z J)
    (j : Fin 4 → Q.P.L.ι) : s.f j = s'.f j := by
  set p := (DegPre.prB Q (FractionRing R)).left
  have H' : ∀ z J, Good Q.P.L z J → sval s p z J = sval s' p z J := fun z J hJ =>
    (isUnit_gs Q c hc z).mul_left_cancel (H z J hJ)
  refine GlobalTheory.IntegralExpansion.prB_app_injective Q _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ y)
  have hI' : Good Q.P.L y I := hI
  have m := hI'.mem (DegPre.famφB Q β) p
  rw [gs_pull (𝟙 _) p y _ hy, gs_pull (𝟙 _) p y _ hy, Category.id_comp]
  exact (sec_trans s p y hy m).trans ((congrArg _ (H' y I hI')).trans (sec_trans s' p y hy m).symm)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  intro R _ _ Q k β s s' c hc H Z x z J _
  have hf : s.f = s'.f := funext (f_eq Q k β s s' c hc H)
  show gs x z _ (s.f _) = gs x z _ (s'.f _)
  rw [hf]

end GlobalTheory.SecBGenericAgree
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_clear_denominator_bundleSection_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s : LB.Sec (LB.LinComb Q.P.L (DegPre.famφ Q (FractionRing R) β) (DegPre.famε k))), ∃ r : R, r ≠ 0 ∧ ∃ σ : Q.SecB k β, ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF Q (FractionRing R)).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval σ (x ≫ (DegPre.prB Q (FractionRing R)).left) z J = gs (x ≫ (DegPre.BF Q (FractionRing R)).hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * sval s x z J := by
  first | exact @GlobalTheory.ClearSecB.exists_clear | exact GlobalTheory.ClearSecB.exists_clear | (intros; apply GlobalTheory.ClearSecB.exists_clear <;> assumption)
end
