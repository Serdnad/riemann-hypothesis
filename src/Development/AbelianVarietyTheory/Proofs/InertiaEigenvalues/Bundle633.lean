module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle511
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle605
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

noncomputable section

namespace GlobalTheory.BaseCoefIner

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {W : Type} [AddCommGroup W] [Module K W]

theorem extS_mono {S T : Submodule K W} (h : S ≤ T) : CJ.extS L S ≤ CJ.extS L T := by
  have := CJ.extS_inf (L := L) S T
  rw [inf_eq_left.2 h] at this
  rw [this]
  exact inf_le_right

theorem extS_iSup_le {J : Sort*} (S : J → Submodule K W) :
    CJ.extS L (⨆ j, S j) ≤ ⨆ j, CJ.extS L (S j) := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | tmul c s =>
    obtain ⟨s, hs⟩ := s
    rw [LinearMap.baseChange_tmul]
    change c ⊗ₜ[K] s ∈ _
    induction hs using Submodule.iSup_induction' with
    | mem j x hx =>
      exact Submodule.mem_iSup_of_mem j ⟨c ⊗ₜ[K] (⟨x, hx⟩ : S j), by simp [LinearMap.baseChange_tmul]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [tmul_add]; exact Submodule.add_mem _ hx hy

end Ext

section Main

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']

section Tower

variable [Algebra LL LL'] [IsScalarTower Qp LL LL'] {k : ℕ}

theorem comm_act_smul (A : Matrix (Fin k) (Fin k) LL) (β : B →ₗ[Qp] B) (r : LL)
    (x : LL' ⊗[LL] ((Fin k → LL) ⊗[Qp] B)) :
    CJ.EE (Qp := Qp) (LL' := LL') B ((PI.CoefExt.actT A β - r • LinearMap.id).baseChange LL' x)
      = (PI.CoefExt.actT (A.map (algebraMap LL LL')) β - (algebraMap LL LL' r) • LinearMap.id :
        (Fin k → LL') ⊗[Qp] B →ₗ[LL'] (Fin k → LL') ⊗[Qp] B) (CJ.EE B x) := by
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.sub_apply, map_sub,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.id_apply, ← algebraMap_smul LL' r x, map_smul]
  congr 1
  exact PI.CoefExt.coefEquiv_comm A β x

theorem dpcris_ext (M : G →* Matrix (Fin k) (Fin k) LL) :
    (CJ.extS LL' (PC.Dpcris (CJ.rep M))).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Dpcris (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) := by
  unfold PotCrysData.Dpcris Dcris
  rw [CJ.extS_iInf]
  simp only [CJ.extS_ker]
  exact CJ.map_iInf_ker _ _ _ (fun g x => CJ.comm_act (BdR := B) (M g) _ x)

theorem eig_ext (M : G →* Matrix (Fin k) (Fin k) LL) (I : Subgroup G) (a : I →* LLˣ) :
    (CJ.extS LL' (PC.Eig (CJ.rep M) I a)).map ((CJ.EE (Qp := Qp) (LL := LL) (LL' := LL') (k := k) B :
        _ ≃ₗ[LL'] _) : _ →ₗ[LL'] _)
      = PC.Eig (CJ.rep (((IsScalarTower.toAlgHom Qp LL LL').mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M)) I
          ((Units.map (algebraMap LL LL' : LL →* LL')).comp a) := by
  unfold PotCrysData.Eig
  rw [CJ.extS_inf, CJ.map_inf_equiv, dpcris_ext, CJ.extS_iInf]
  simp only [CJ.extS_ker]
  congr 1
  exact CJ.map_iInf_ker _ _ _ (fun g x => comm_act_smul (M g) _ _ x)

end Tower

theorem orderOf_comp {I : Type} [Group I] (f : LL →+* LL') (a : I →* LLˣ) :
    orderOf ((Units.map (f : LL →* LL')).comp a) = orderOf a := by
  refine orderOf_eq_orderOf_iff.2 fun n => ?_
  simp only [MonoidHom.ext_iff, MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.one_apply]
  refine forall_congr' fun g => ?_
  rw [← map_pow]
  exact map_eq_one_iff _ (Units.map_injective f.injective)

theorem inertiaThrough_mat (f : LL →ₐ[Qp] LL') {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough (CJ.rep M) Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp M))
      (mapSig f.toRingHom Sig) := by
  classical
  let _ : Algebra LL LL' := f.toRingHom.toAlgebra
  have _ : IsScalarTower Qp LL LL' := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have hf : IsScalarTower.toAlgHom Qp LL LL' = f := AlgHom.ext fun _ => rfl
  have hm : ∀ c, c ∈ mapSig f.toRingHom Sig ↔
      ∃ a ∈ Sig, (Units.map (f.toRingHom : LL →* LL')).comp a = c := fun c => by
    unfold mapSig
    convert Finset.mem_image
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨fun c hc g hg => ?_, fun c hc => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [MonoidHom.comp_apply, h1 a ha g hg, map_one]
  · obtain ⟨a, ha, rfl⟩ := (hm c).1 hc
    rw [orderOf_comp]
    exact h2 a ha
  · have hD := dpcris_ext (LL' := LL') PC M
    rw [hf] at hD
    refine hD.symm.le.trans (Submodule.map_le_iff_le_comap.2 ?_)
    refine (extS_mono h3.le).trans ?_
    refine (extS_iSup_le _).trans (iSup_le fun a => (extS_iSup_le _).trans (iSup_le fun ha => ?_))
    refine Submodule.map_le_iff_le_comap.1 ?_
    have hE := eig_ext (LL' := LL') PC M PC.Iner a
    rw [hf] at hE
    refine hE.le.trans ?_
    exact le_iSup₂_of_le ((Units.map (f.toRingHom : LL →* LL')).comp a) ((hm _).2 ⟨a, ha, rfl⟩) le_rfl
  · exact iSup₂_le fun _ _ => inf_le_left

theorem inertiaThrough_basis (f : LL →ₐ[Qp] LL') {k : ℕ}
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (b : Module.Basis (Fin k) LL V)
    (Sig : Finset (PC.Iner →* LLˣ)) (hS : PC.InertiaThrough ρ Sig) :
    PC.InertiaThrough (CJ.rep ((f.mapMatrix :
          Matrix (Fin k) (Fin k) LL →ₐ[Qp] Matrix (Fin k) (Fin k) LL').toRingHom.toMonoidHom.comp
          ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ)))
      (mapSig f.toRingHom Sig) := by
  refine inertiaThrough_mat _ f _ Sig ?_
  refine (GlobalTheory.HTW.Rec.potCrys_inertiaThrough_of_equiv _ b.equivFun.symm ?_).2 Sig hS
  intro g v
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change (LinearMap.toMatrix b b (ρ g)).mulVec v = _
  have := LinearMap.toMatrix_mulVec_repr b b (ρ g) (b.equivFun.symm v)
  rw [← Module.Basis.equivFun_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] at this
  exact this

end Main



theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)), (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → (pc Pl h hN hF hS).InertiaThrough (extLat hL T b hb).ρ (mapSig (incl hL).toRingHom Sig) := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb Sig hI
  exact inertiaThrough_basis (pc Pl h hN hF hS) (incl hL) T.ρ b Sig hI

end GlobalTheory.BaseCoefIner
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal



theorem cmp_semilinear_pair : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (μ : OA l O), IsUnit (toB l O μ) → (∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O μ • v) = TWincl (inclO l O) T z) → ∀ (σA : OA l O →ₐ[O] OA l O) (σW : OW l O →ₐ[O] OW l O) (σB : OB l O →ₐ[O] OB l O) (h : ↥T.L.T →ₗ[O] ↥T.L.T) (F : (ι → OW l O) →ₗ[O] (ι → OW l O)) (lam : OA l O) (Γ : Matrix ι ι (OA l O)), (∀ x, inclO l O (σA x) = σW (inclO l O x)) → (∀ x, toB l O (σA x) = σB (toB l O x)) → (∀ v, I.j (F v) = TensorProduct.map σW.toLinearMap h (I.j v)) → (∀ (r : OW l O) v, F (r • v) = σW r • F v) → (∀ c, inclO l O lam • F (inclL t ϖ P c) = inclL t ϖ P (Γ *ᵥ fun i => σA (c i))) → ∀ v : ι → OB l O, jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hC μ hμ hL σA σW σB h F lam Γ h1 h2 h3 h4 h5

  have hmapB : ∀ (r : OB l O) (z : TW (OB l O) T),
      TensorProduct.map σB.toLinearMap h (r • z) = σB r • TensorProduct.map σB.toLinearMap h z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
    | tmul b x => simp [TensorProduct.smul_tmul', TensorProduct.map_tmul]
  have hmapW : ∀ z : TW (OA l O) T, TensorProduct.map σW.toLinearMap h (TWincl (inclO l O) T z) =
      TWincl (inclO l O) T (TensorProduct.map σA.toLinearMap h z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b x => simp [TWincl, TensorProduct.map_tmul, h1]
  have hmapBA : ∀ z : TW (OA l O) T, TensorProduct.map σB.toLinearMap h (TWincl (toB l O) T z) =
      TWincl (toB l O) T (TensorProduct.map σA.toLinearMap h z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b x => simp [TWincl, TensorProduct.map_tmul, h2]
  have hsmulL : ∀ (m : OA l O) (c : ι → OA l O), inclO l O m • inclL t ϖ P c = inclL t ϖ P (m • c) := by
    intro m c
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext k
    simp [map_mul]
  have htoB : ∀ (m : OA l O) (c : ι → OA l O), (fun k => toB l O ((m • c) k)) = toB l O m • fun k => toB l O (c k) := by
    intro m c; funext k; simp [map_mul]

  have key : ∀ i : ι, jB (fun k => toB l O (Γ k i)) =
      toB l O lam • TensorProduct.map σB.toLinearMap h (jB (Pi.single i 1)) := by
    intro i
    set c : ι → OA l O := Pi.single i 1 with hc
    have hcB : (fun k => toB l O (c k)) = (Pi.single i 1 : ι → OB l O) := by
      funext k; by_cases hk : k = i
      · subst hk; simp [hc]
      · simp [hc, Pi.single_apply, hk]
    obtain ⟨z, hz⟩ := hL (inclL t ϖ P c) ⟨c, rfl⟩
    rw [hsmulL] at hz
    have hz1 : toB l O μ • jB (Pi.single i 1) = TWincl (toB l O) T z := by
      rw [← hC _ _ hz, htoB, hcB, map_smul]
    have hσc : (fun k => σA ((μ • c) k)) = σA μ • c := by
      funext k; by_cases hk : k = i
      · subst hk; simp [hc]
      · simp [hc, Pi.single_apply, hk]
    have hF : I.j (inclL t ϖ P (σA μ • (Γ *ᵥ c))) =
        TWincl (inclO l O) T (lam • TensorProduct.map σA.toLinearMap h z) := by
      rw [← Matrix.mulVec_smul, ← hσc, ← h5, map_smul, h3, hz, hmapW, GlobalTheory.Cyc.Decomp.TWincl_smul]
    have h6 := hC _ _ hF
    rw [htoB, GlobalTheory.Cyc.Decomp.TWincl_smul, ← hmapBA, ← hz1, hmapB, h2, map_smul] at h6
    have hΓ : (fun k => toB l O ((Γ *ᵥ c) k)) = fun k => toB l O (Γ k i) := by
      funext k; simp [hc, Matrix.mulVec_single]
    rw [hΓ, smul_comm (toB l O lam)] at h6
    exact ((hμ.map σB).smul_left_cancel).1 h6
  intro v
  let Pr : (ι → OB l O) → Prop := fun v =>
    jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v)
  have h0 : Pr 0 := by
    have h00 : (fun i => σB ((0 : ι → OB l O) i)) = 0 := by funext i; simp
    simp only [Pr]
    rw [h00, Matrix.mulVec_zero, map_zero, map_zero, smul_zero]
  have hadd : ∀ v w, Pr v → Pr w → Pr (v + w) := by
    intro v w hv hw
    simp only [Pr] at hv hw ⊢
    have : (fun i => σB ((v + w) i)) = (fun i => σB (v i)) + fun i => σB (w i) := by
      funext i; simp
    rw [this, Matrix.mulVec_add, map_add (f := _), hv, hw, map_add (f := _), map_add (f := _), smul_add]
  have hsm : ∀ (r : OB l O) v, Pr v → Pr (r • v) := by
    intro r v hv
    simp only [Pr] at hv ⊢
    have : (fun i => σB ((r • v) i)) = σB r • fun i => σB (v i) := by
      funext i; simp [map_mul]
    rw [this]
    rw [Matrix.mulVec_smul]
    rw [map_smul, hv, map_smul, hmapB]
    rw [smul_smul, smul_smul, mul_comm]
  have hbas : ∀ i, Pr (Pi.single i 1) := by
    intro i
    simp only [Pr]
    have : (fun k => σB ((Pi.single i 1 : ι → OB l O) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [this, Matrix.mulVec_single]
    convert key i using 2
    funext k; simp
  have hv : v = ∑ i, v i • (Pi.single i 1 : ι → OB l O) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  have := Finset.sum_induction (s := Finset.univ) (fun i => v i • (Pi.single i 1 : ι → OB l O)) Pr hadd h0
    (fun i _ => hsm _ _ (hbas i))
  rw [← hv] at this
  exact this

end GlobalTheory.BKGal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtLatCrys

theorem isCrys_comp_extRep {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (K : FinExt l) (Pl : LocPrime l)
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL (Gl l) V)
    (hT : IsCrys (Pl.PD K) (ρ.comp (inclG K) : Representation LL ↥(GK K) V)) (z : ↥(continuousCocycles ρ))
    (hz : (z : Gl l → V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep ρ z).comp (inclG K) : Representation LL ↥(GK K) (V × LL)) := by
  let ρ' : Representation LL ↥(GK K) V := ρ.comp (inclG K)
  have hρ' : ∀ g, ρ' g = ρ (inclG K g) := fun _ => rfl
  have hc : (fun g => (z : Gl l → V) (inclG K g)) ∈ continuousCocycles ρ' :=
    ⟨z.2.1.comp (continuous_subtype_val.subtype_mk _), fun g k => by
      have := z.2.2 (inclG K g) (inclG K k)
      rw [← map_mul] at this
      exact this⟩
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt ρ' ⟨_, hc⟩
  have h2 : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Pl.R.B), actVB (Pl.PD K) ρ' g y =
      actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ (inclG K g) y := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, Pl.PD_actB, hρ']; rfl
    | add u w hu hw => rw [map_add (f := _), map_add (f := _), hu, hw]
  have h1 := (GlobalTheory.CrysExt.isCrystalline_iff_mem_H1f (Pl.PD K) (ρ := ρ') hT h0.1 ⟨_, hc⟩ h0.2).mpr
    ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.mk_mem_H1fSub (Pl.PD K) ρ' ⟨_, hc⟩).mpr (by
      obtain ⟨-, x, hx⟩ := hz
      refine ⟨hc, x, fun g => ?_⟩
      rw [h2]
      exact hx (inclG K g)))
  exact h1

theorem isCrys_comp_extRep_lat {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (K : FinExt l) (Pl : LocPrime l)
    (T : LocLat (Gl l) ℚ_[l] LL O)
    (hT : IsCrys (Pl.PD K) (T.ρ.comp (inclG K) : Representation LL ↥(GK K) T.V)) (z : ↥(continuousCocycles T.ρ))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep T.ρ z).comp (inclG K) : Representation LL ↥(GK K) (T.V × LL)) :=
  isCrys_comp_extRep K Pl T.ρ hT z hz

theorem isCrys_resF_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  intro l _ a e _ _ ϖ LL _ _ Pl T hT z hz
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact isCrys_comp_extRep_lat (ϖ.field a) Pl T hT ⟨z, z.2.1⟩ hz

end GlobalTheory.ExtLatCrys
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.BKGal

theorem card_le_finrank_of_mem_span {K U W : Type} [Field K] [Field U] [AddCommGroup W] [Module K W]
    [Module U W] (hKU : ∀ c : K, ∃ c' : U, ∀ w : W, c • w = c' • w) (D : Submodule K W) [Module.Finite K D]
    {d : ℕ} (e : Fin d → W) (he : LinearIndependent U e) (hsp : ∀ i, e i ∈ Submodule.span U (D : Set W)) :
    d ≤ Module.finrank K D := by
  classical
  let u := Module.finBasis K D
  let u' := fun i => (u i : W)
  have hle : (D : Set W) ⊆ Submodule.span U (Set.range u') := by
    intro x hx
    have h4 := congrArg Subtype.val (u.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h4
    rw [← h4]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hKU (u.repr ⟨x, hx⟩ i)
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h6 := linearIndependent_le_span_aux' _ he (Set.range u') (by
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le.2 hle (hsp i))
  have h7 := Fintype.card_range_le u'
  simp only [Fintype.card_fin] at h6 h7
  exact h6.trans h7

theorem isCrys_of_span_generic {G G' : Type} [Group G] [Group G'] {Qp K₀ K K₀' K' U : Type} [Field Qp] [Field K₀]
    [Field K] [Field K₀'] [Field K'] [Field U]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [IsDomain B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra U B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR] [SMulCommClass Qp U B]
    (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (hf : FracInv PD) (hf' : FracInv PD') (hU : ∀ c : K₀, ∃ c' : U, algebraMap K₀ B c = algebraMap U B c')
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (ρ' : Representation LL G' V) (hc : IsCrys PD' ρ')
    (hsp : ∀ m ∈ DcrisK₀ PD' ρ', m ∈ Submodule.span U (DcrisK₀ PD ρ : Set (B ⊗[Qp] V))) : IsCrys PD ρ := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_le₀ PD hf ρ
  obtain ⟨h3, -⟩ := finite_le₀ PD' hf' ρ'
  rw [isCrys_iff_finrank] at hc ⊢
  refine le_antisymm h2 ?_
  let e := Module.finBasisOfFinrankEq K₀' _ hc
  have hB := (indepB PD' hf' ρ' e e.linearIndependent).restrict_scalars' U
  refine card_le_finrank_of_mem_span (U := U) (fun c => ?_) _ _ hB fun i => hsp _ (e i).2
  obtain ⟨c', h⟩ := hU c
  exact ⟨c', fun w => by rw [← algebraMap_smul B c w, h, algebraMap_smul]⟩

theorem isCrys_of_dcris_le_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (LL : FinExt l) (T : QLat LL) (F K'' : FinExt l), IsCrys (P.PD K'') (T.ρ.comp (inclG K'')) → (∀ m ∈ DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')), m ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (↑(DcrisK₀ (P.PD F) (T.ρ.comp (inclG F))) : Set (P.R.B ⊗[ℚ_[l]] T.V))) → IsCrys (P.PD F) (T.ρ.comp (inclG F)) := by
  intro l _ P AI hs LL T F K'' hc hsp
  obtain ⟨Ti⟩ := hs
  haveI := LL.2
  haveI : IsDomain P.R.B := isDomain_of_tied Ti F
  exact isCrys_of_span_generic (U := ↥(MaximalUnramifiedExtension l)) (P.PD F) (P.PD K'') (GlobalTheory.Per.TiedRestrict.fracInv_of_tied Ti F)
    (GlobalTheory.Per.TiedRestrict.fracInv_of_tied Ti K'') (fun c => ⟨⟨c.1, c.2.2⟩, rfl⟩) _ _ hc hsp

end GlobalTheory.BKGal
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.disc_restrict_injective | exact GlobalTheory.BSP.disc_restrict_injective | (intros; apply GlobalTheory.BSP.disc_restrict_injective <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_eq_span {A : Type} [CommRing A] {I : Ideal A} {t : A}
    (hI : Module.Invertible A ↥I) (h : I = Ideal.span {t}) : t ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply (Module.Invertible.toModuleEnd_bijective A ↥I).1
  rw [map_zero]
  ext ⟨y, hy⟩
  rw [h] at hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  change x * (z * t) = 0
  linear_combination z * hx

theorem hf_E_span_and_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  intro l _ K bk B g
  have h : B.I = Ideal.span {BK.hf g bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ _ _ g]
    change Ideal.map (BK.hf g) (Ideal.span {bk.E}) = _
    rw [Ideal.map_span, Set.image_singleton]
  exact ⟨h, mem_nonZeroDivisors_of_invertible_eq_span B.inv h⟩

end GlobalTheory.BSP
end
