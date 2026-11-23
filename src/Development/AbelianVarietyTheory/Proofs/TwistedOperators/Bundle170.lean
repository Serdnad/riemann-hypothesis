module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle160
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle150
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

variable {D : D7}

def Stab (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (g : GA D V) : Prop :=
  g ∈ GfC V ∧ finE V g ∈ St β

def UnrOff (b : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → b * (x : AE D) = b → χ x = 1


open Classical in
def adjDatum (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (Pg Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO S T) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj S T βS βT x) then
    omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
      omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
  else 0

theorem finE_val (V : HSp D) (g : GA D V) :
    (finE V g).val = (Formalism.L2.Theta.mt V g).map (toEAf D) := rfl

theorem Stab.one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Stab V β 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩

theorem Stab.inv {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (h : Stab V β g) : Stab V β g⁻¹ :=
  ⟨Subgroup.inv_mem _ h.1, by rw [map_inv]; exact Subgroup.inv_mem _ h.2⟩

theorem isFrame_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) : IsFrame (x * β) Λ := by
  obtain ⟨y, rfl⟩ := hx
  have e : frGL β y * β = β * intGL F E n y := by simp [frGL]
  have key : ∀ (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      (∀ i, w i ∈ Formalism.L2.Herm.intAf F E) →
      ∀ i, (intGL F E n z).val.mulVec w i ∈ Formalism.L2.Herm.intAf F E := fun z w hw i => by
    show ∑ j, ((z.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) * w j ∈ _
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (z.val i j).2 (hw j)
  intro w
  rw [hβ w, e, mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv]
  refine ⟨fun h => key _ _ h, fun h => ?_⟩
  have := key y _ h
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at this

theorem mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)}
    {βT : GL (Fin T.rank) (Lev.EAf D)} (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) {g : GA D S} {h : GA D T}
    (hg : finE S g ∈ St βS) (hh : finE T h ∈ St βT) (u : WO S T) :
    u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ u,
      u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) →
      actO S T g h u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
    fun g h hg hh u hu => GlobalTheory.AdelicLatMove.actO_mem_latO S T g h ΛS ΛS ΛT ΛT βS _ βT _ hS (isFrame_mul hS hg) hT
      (isFrame_mul hT hh) rfl rfl u hu
  refine ⟨key g h hg hh u, fun hu => ?_⟩
  have := key g⁻¹ h⁻¹ (by rw [map_inv]; exact inv_mem hg) (by rw [map_inv]; exact inv_mem hh) _ hu
  have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at e
  rwa [e] at this

theorem exists_det_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β) :
    ∃ a : Formalism.L2.Herm.intAf D.host.F D.host.E, (a : Lev.EAf D) = toEAf D (Formalism.L2.Theta.mt V g).det ∧
      ∀ PP : Pl D.host.E, ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP a := by
  obtain ⟨y, hy⟩ := hg
  refine ⟨y.val.det, ?_, fun PP => ?_⟩
  · have h1 : toEAf D (Formalism.L2.Theta.mt V g).det = (finE V g).val.det := by
      rw [finE_val, RingHom.map_det]; rfl
    have h2 : (Matrix.GeneralLinearGroup.det (frGL β y)) = Matrix.GeneralLinearGroup.det (intGL _ _ _ y) := by
      simp [frGL]
    have h3 := congrArg Units.val h2
    rw [h1, ← hy]
    refine Eq.trans ?_ h3.symm
    exact (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.map_det y.val
  · rw [← hy, redFn_frGL]
    exact ((resS D.host.F PP).map_det y.val).symm

def detAt (e : AE D) (he : e * e = e) (V : HSp D) : GA D V →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => e * (Formalism.L2.Theta.mt V g).det + (1 - e)
      map_one' := by rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]; ring
      map_mul' := fun g g' => by
        rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.det_mul]
        linear_combination (-(Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g').det + (Formalism.L2.Theta.mt V g).det
          + (Formalism.L2.Theta.mt V g').det - 1) * he }

theorem isDetAt_detAt (e : AE D) (he : e * e = e) (V : HSp D) (g : GA D V) : IsDetAt e V g (detAt e he V g) := rfl

end GlobalTheory.VecInv

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ProjComm

theorem coeff_conj_of_central {H : Type} [Group H] (z : MonoidAlgebra ℂ H) (hz : ∀ a, z * a = a * z) (g h : H) :
    z.coeff (g * h * g⁻¹) = z.coeff h := by
  have key := congrArg (fun w => w.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at key
  exact key

theorem goodProjector_coeff_classFunction (D : D7) (g h : G0g D.nd) : D.ntypes.e0.coeff (g * h * g⁻¹) = D.ntypes.e0.coeff h := by
  unfold NTypes.e0
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · exact Finset.prod_congr rfl fun kv _ =>
      coeff_conj_of_central _ (D.ntypes.eSer_central kv.1 _) (g kv) (h kv)
  · rfl

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  unfold IsLevelLift at hκ hκ' ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  obtain ⟨h1', h2', h3'⟩ := hκ'
  refine ⟨mul_mem h1 h1', ?_, ?_⟩
  · rw [map_mul]
    exact mul_mem h2 h2'
  · rw [map_mul, Formalism.L2.DIV.rTup_mul h2 h2', h3, h3']

theorem isLift_inv {g : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g κ) :
    IsLevelLift V β L g⁻¹ κ⁻¹ := by
  unfold IsLevelLift at hκ ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  refine ⟨inv_mem h1, ?_, ?_⟩
  · rw [map_inv]
    exact inv_mem h2
  · rw [map_inv, Formalism.L2.DIV.rTup_inv h2, h3]

private theorem actG0_apply_eq_levChi_inv_mul_choose {g : G0 L.Pg L.r} (hex : ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) (x : GA D V) :
    actG0 V β L g F x = (levChi V β (flagL L) hex.choose)⁻¹ * F (x * hex.choose) := by
  unfold actG0
  rw [dite_eq_left hex]

private theorem levChi_flagL_mul_of_mem_parLev {κ κ' : GA D V} (hκ : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hκ' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ hκ', Units.val_mul]

theorem levelGroupAction_mul_of_lifts {g g' : G0 L.Pg L.r} (hg : ∃ κ, IsLevelLift V β L g κ) (hg' : ∃ κ, IsLevelLift V β L g' κ)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actG0 V β L g (actG0 V β L g' F) = actG0 V β L (g * g') F := by
  have hex := hg
  obtain ⟨κ', hκ'⟩ := hg'
  funext x
  have hc : IsLevelLift V β L g hex.choose := hex.choose_spec
  have hm : IsLevelLift V β L (g * g') (hex.choose * κ') := isLift_mul hc hκ'
  have hpar : finE V hex.choose ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hc
    exact hc.2.1
  have hpar' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hκ'
    exact hκ'.2.1
  rw [actG0_apply_eq_levChi_inv_mul_choose hex, level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (x * hex.choose),
    level_action_spec hF ⟨_, hm⟩ _ hm x, levChi_flagL_mul_of_mem_parLev hpar hpar', mul_assoc x]
  ring

theorem levelGroupAction_eq_zero_of_no_lift {g : G0 L.Pg L.r} (hg : ¬ ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) :
    actG0 V β L g F = 0 := by
  unfold actG0
  exact dif_neg hg

theorem actL_conj (g h : G0 L.Pg L.r) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actL V β L (g * h * g⁻¹) (actL V β L g F) = actL V β L g (actL V β L h F) := by
  show actG0 V β L (g * h * g⁻¹) (actG0 V β L g F) = actG0 V β L g (actG0 V β L h F)
  by_cases hg : ∃ κ, IsLevelLift V β L g κ
  · obtain ⟨κ, hκ⟩ := hg
    by_cases hh : ∃ κ, IsLevelLift V β L h κ
    · obtain ⟨μ, hμ⟩ := hh
      have hc : ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ :=
        ⟨κ * μ * κ⁻¹, isLift_mul (isLift_mul hκ hμ) (isLift_inv hκ)⟩
      rw [levelGroupAction_mul_of_lifts hc ⟨κ, hκ⟩ hF, levelGroupAction_mul_of_lifts ⟨κ, hκ⟩ ⟨μ, hμ⟩ hF, inv_mul_cancel_right]
    · have hc : ¬ ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ := by
        rintro ⟨ν, hν⟩
        apply hh
        have hl := isLift_mul (isLift_mul (isLift_inv hκ) hν) hκ
        rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hl
        exact ⟨_, hl⟩
      rw [levelGroupAction_eq_zero_of_no_lift hc, levelGroupAction_eq_zero_of_no_lift hh]
      exact (map_zero (actL V β L g)).symm
  · rw [levelGroupAction_eq_zero_of_no_lift hg F, levelGroupAction_eq_zero_of_no_lift hg (actG0 V β L h F)]
    exact map_zero (actL V β L (g * h * g⁻¹))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : G) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  unfold gaL

  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun y => ?_).symm
  show c y • actL V β L (eG g) (actL V β L (eG y) F) =
    c (g * y * g⁻¹) • actL V β L (eG (g * y * g⁻¹)) (actL V β L (eG g) F)
  rw [hc, map_mul, map_mul, map_inv, actL_conj _ _ hF]

theorem proj_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → (∀ g F, HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) F → R.e0 (actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) F) = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.e0 F)) ∧ ∀ i σ g F, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) F → R.eWf i σ (actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) F) = actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) (R.eWf i σ F) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hrec
  obtain ⟨eR, plg, iso, he, -, -⟩ := hrec
  have hcls : ∀ a b : G, (idemOf A.X).coeff (a * b * a⁻¹) = (idemOf A.X).coeff b := fun a b =>
    D.what₂.embLL.injective (by rw [he, he, map_mul eR, map_mul eR, map_inv eR, goodProjector_coeff_classFunction])
  have hcl : ∀ (σ : D.what₂.LL →+* ℂ) (a b : G),
      RealDat.eC (A := A) σ (a * b * a⁻¹) = RealDat.eC (A := A) σ b := fun σ a b => by
    unfold RealDat.eC
    rw [hcls]
  refine ⟨fun g F hF => ?_, fun i σ g F hF => ?_⟩
  · exact gaL_comm (L := R.dat0 R.triv) R.eG _ (hcl _) g hF
  · exact gaL_comm (L := R.datWp i R.triv) R.eG _ (hcl σ) g hF

end GlobalTheory.ProjComm

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace ClassSumTranslate

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

theorem card_stab (γ : Γ) (y : G) (k : J) :
    Nat.card (Bridge.stab ι J (ι γ * y * k)) = Nat.card (Bridge.stab ι J y) := by
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ => ?_)
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (ι γ * y * k)⁻¹ * ι δ * (ι γ * y * k) =
      (k : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * k := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInnerIndep : Bridge.AdInnerIndep ι ρ J χ := by
  intro hρ hχ I I' _ _ y y' hy hy' F hF F' hF'
  choose σ hσ using fun i => (hy' (y i)).exists
  have hinj : Function.Injective σ := by
    intro i j hij
    obtain ⟨γ, k, h1⟩ := hσ i
    obtain ⟨γ', k', h2⟩ := hσ j
    refine (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨γ * γ'⁻¹, k'⁻¹ * k, ?_⟩
    rw [h1, h2, hij]; simp [mul_assoc]
  have hsurj : Function.Surjective σ := by
    intro j
    obtain ⟨i, γ, k, h1⟩ := (hy (y' j)).exists
    obtain ⟨γ', k', h2⟩ := hσ i
    refine ⟨i, (hy' (y' j)).unique ⟨γ * γ', k' * k, ?_⟩ ⟨1, 1, by simp⟩⟩
    rw [h1, h2]; simp [mul_assoc]
  unfold Bridge.adInner
  refine Fintype.sum_bijective σ ⟨hinj, hsurj⟩ _ _ fun i => ?_
  obtain ⟨γ, k, h⟩ := hσ i
  rw [h, card_stab, hF γ _ k, hF' γ _ k, inner_smul_left, inner_smul_right, hρ, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ]
  simp

variable {J} in
theorem stab_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) (y : G) :
    Bridge.stab ι J (y * κ) = Bridge.stab ι J y := by
  ext δ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← hκ (y⁻¹ * ι δ * y)]
  simp [mul_assoc]

variable {J} in
theorem isReps_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) {I : Type} {y : I → G}
    (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * κ := by
  intro h
  refine (existsUnique_congr fun i => ?_).1 (hy (h * κ⁻¹))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨_, (hκ k).2 k.2⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at e
    rw [e]; simp [mul_assoc]
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨κ * k * κ⁻¹, (hκ _).1 (by simpa [mul_assoc] using k.2)⟩, ?_⟩
    rw [e]; simp [mul_assoc]

theorem translate (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (κ : l.Q) {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) :
    (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) ∈ Bridge.AdForms ι ρ l.J l.χ ∧
      Bridge.adInner ι l.J y (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ))
        (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) = Bridge.adInner ι l.J y F F := by
  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := fun k =>
    ⟨fun h => by simpa [mul_assoc] using hn _ (l.Q.inv_mem κ.2) _ h, hn _ κ.2 _⟩
  constructor
  · intro γ h k
    have e := hF γ (h * κ) ⟨_, (hκ k).2 k.2⟩
    have e2 : l.χ ⟨_, (hκ k).2 k.2⟩ = l.χ k := by
      rw [← l.ch_J, ← l.ch_J]
      have : (⟨(κ : G)⁻¹ * k * κ, l.J_le ((hκ k).2 k.2)⟩ : l.Q) = κ⁻¹ * ⟨k, l.J_le k.2⟩ * κ := rfl
      simp only
      rw [this, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    rw [e2] at e
    simp only
    rw [map_smul, smul_comm, ← e]
    simp [mul_assoc]
  · rw [adInnerIndep ι ρ l.J l.χ hρ (fun k => by rw [← l.ch_J]; exact hch _) I I y _ hy
      (isReps_mul ι hκ hy) F hF F hF]
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stab_mul ι hκ, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
      Complex.conj_mul', norm_inv, hch]
    simp

theorem translate_model (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (M : Links.HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ l.J l.χ) (Bridge.adInner ι l.J y)) (κ : l.Q) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖ := by
  have hx : M.e x ∈ Bridge.AdForms ι ρ l.J l.χ := by
    rw [← hM.2.1]; exact ⟨x, rfl⟩
  obtain ⟨h1, h2⟩ := translate ι ρ l hρ hn hch hy κ hx
  rw [← hM.2.1] at h1
  obtain ⟨x', hx'⟩ := h1
  refine ⟨x', fun h => congrFun hx' h, ?_⟩
  have h3 : inner ℂ x' x' = inner ℂ x x := by
    rw [hM.2.2, hM.2.2, hx']; exact h2
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h3]

end Generic

theorem norm_char {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) (x : M) : ‖(c x : ℂ)‖ = 1 := by
  have h : IsOfFinOrder (((Units.coeHom ℂ).comp c) x) := MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite x)
  exact h.norm_eq_one

variable {D : D7}

theorem norm_levFn (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) x) = 1 := subgroupCharExtension_one_apply _ _
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => by
    first | infer_instance | exact Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  unfold levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_char _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_char _ _

theorem lev_conj (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {q k : GL (Fin V.rank) (Lev.EAf D)} (hq : q ∈ lev D.sp.cm V.gram β (flagL L))
    (hk : k ∈ lev D.sp.cm V.gram β (flag1L L)) : q⁻¹ * k * q ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have hq' : q ∈ parLev D.sp.cm V.gram β L := hq.1
  have hk' : k ∈ parLev D.sp.cm V.gram β L := hk.1
  have hk2 : rTup β L k ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2
  have h1 : q⁻¹ * k * q ∈ parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq'
  have h2 : rTup β L (q⁻¹ * k * q) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := by
    rw [Subgroup.mem_bot] at hk2 ⊢
    rw [rTup_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq', rTup_mul (Subgroup.inv_mem _ hq') hk',
      rTup_inv hq', hk2, mul_one, inv_mul_cancel]
  exact ⟨h1, h2⟩

theorem comap_conj {G H : Type} [Group G] [Group H] (f : G →* H) {Q J : Subgroup H}
    (h : ∀ q ∈ Q, ∀ k ∈ J, q⁻¹ * k * q ∈ J) : ∀ q ∈ Q.comap f, ∀ k ∈ J.comap f, q⁻¹ * k * q ∈ J.comap f := by
  intro q hq k hk
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact h _ hq _ hk

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ q ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, q⁻¹ * k * q ∈ (levEnv V β L).J :=
  comap_conj (finHom V).range.subtype (comap_conj (Formalism.UG.bc (swapAE D)) fun _ hq _ hk => lev_conj V β L hq hk)

theorem model (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (levEnv_normal V β L) (fun q => norm_levFn V β L _) hy M hM ⟨_, hq⟩ x

end ClassSumTranslate

theorem translate_unitary_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HV → R.models_cV → ∀ i t g0 κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∀ y : (R.HV i t).H, ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) ∧ ‖y'‖ = ‖y‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hH hc i t g0 κ hκ y
  exact ClassSumTranslate.model _ _ _ _ (hc i) _ _ (R.B.L i t).pres.reps (hH i t) g0 κ hκ y

end GlobalTheory
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_completedHomLattice_iff_frameStabiliser_action : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT → ∀ (g : GA D S) (h : GA D T), finE S g ∈ St βS → finE T h ∈ St βT → ∀ (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT Pv ↔ actO S T g h u ∈ latO S T ΛS ΛT Pv := by
  first | exact @GlobalTheory.LatStab.mem_latO_iff_actO_mem | exact GlobalTheory.LatStab.mem_latO_iff_actO_mem | (intros; apply GlobalTheory.LatStab.mem_latO_iff_actO_mem <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.place_over_typePrime_divides_or_conjugate : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  first | exact @GlobalTheory.StepLaw.div_or_isConjPl_div | exact GlobalTheory.StepLaw.div_or_isConjPl_div | (intros; apply GlobalTheory.StepLaw.div_or_isConjPl_div <;> assumption)
end
