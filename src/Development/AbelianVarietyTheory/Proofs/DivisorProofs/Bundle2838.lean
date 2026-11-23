module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle614
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle643
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn.Vert
open GlobalTheory.KS

theorem transport {k : Type} [Field k] {R : Type} [CommRing R] (A : Over (Sp R)) (L : LB A.left)
    (A₀ B₀ : Over (Sp k)) (m₀ : A₀.left ⟶ A.left) (e : B₀.left ⟶ A₀.left) (he : e ≫ A₀.hom = B₀.hom)
    (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (v : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK A L A₀ m₀ D' V jj v q) :
    GlobalTheory.HeatConn.IsConnK A L B₀ (e ≫ m₀) D' V jj (fun W f => pbT e (v W f) ((e ≫ m₀) ⁻¹ᵁ W))
      (fun i => pbT e (q i) ((e ≫ m₀) ⁻¹ᵁ V i)) := by
  obtain ⟨hd, hcov, hle, htr⟩ := hc
  have le : ∀ W : A.left.Opens, (e ≫ m₀) ⁻¹ᵁ W ≤ e ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun W => le_rfl
  have app : ∀ W (f : Γ(A.left, W)), pbT e ((m₀.app W).hom f) ((e ≫ m₀) ⁻¹ᵁ W) = ((e ≫ m₀).app W).hom f := by
    intro W f
    rw [AdjDlog.app_eq_pbT m₀, AdjDlog.app_eq_pbT (e ≫ m₀), AdjDlog.pbT_pbT e m₀ le_rfl (le W)]
  refine ⟨⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, hcov, hle, fun i i' => ?_⟩
  · simp only [hd.add W le_top, pbT_add]
  · rw [hd.mul W le_top, pbT_add, pbT_mul, pbT_mul, app, app]
  · show pbT e (v W' (resG A.left h f)) _ = rsT (pbT e (v W f) _) _
    rw [hd.res W W' h le_top, pbT_rsT e (m₀.preimage_mono h) (le W'), rsT_pbT e (le W) ((e ≫ m₀).preimage_mono h)]
  · show pbT e (v W (constFn A.hom W r)) _ = _
    rw [hd.base W le_top, pbT_constFn A₀.hom e (le W), he]
  · show pbT e (v (V i ⊓ V i') _) _ = _
    rw [htr i i', pbT_mul, pbT_sub, AdjDlog.pbT_pbT e m₀ (m₀.preimage_mono (le_inf (inf_le_left.trans (hle i)) (inf_le_right.trans (hle i')))) (le _),
      pbT_rsT e (m₀.preimage_mono inf_le_left) (le _), pbT_rsT e (m₀.preimage_mono inf_le_right) (le _),
      rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_left), rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_right)]

theorem coeff_const (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W))
    (hv : LocDerK P₀.A.hom P.A.hom θ (fun _ => (0 : k)) ⊤ v) :
    ∃ c : Fin n → k, ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f) := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  have hU : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top _
  obtain ⟨c0, hc0, -⟩ := GlobalTheory.KSUniq.coeff_id hs hu hdd (spMap x₀) P.A.hom θ hθ hU ⊤ (fun _ _ => trivial) v
    (fun W _ => hv.add W le_top) (fun W _ => hv.mul W le_top) (fun W W' h _ => hv.res W W' h le_top) (fun W _ r => by
      have e1 : pbT P.A.hom r W = constFn P.A.hom W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
        rw [pbT_of_le _ (by simp)]
        simp [constFn]
      rw [e1, hv.base W le_top]
      simp [constFn])
  have hGF := GlobalTheory.allSixLaws.1.globalFns
  choose s hs' using fun a => (hGF _ P₀.A P₀.isAb).2 (rsT (c0 a) ⊤)
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (s a), fun W f => ?_⟩
  rw [hc0 W le_top f]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← rsT_rsT (O₁ := ⊤) (by simp) le_top, ← hs' a, rsT_of_le le_top]
  simp [constFn]
  rfl

theorem cob_of_conn (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R))
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left)
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => θ ⁻¹ᵁ P.L.U i)) (hφ : IsDlog θ P.L dd φ) (hcoc : ∀ a, IsCoc _ (φ a))
    {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (c : Fin n → k)
    (hcv : ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f)) :
    IsCob _ (lc P₀.A.hom c φ) := by
  obtain ⟨-, hcov, hle, htr⟩ := hc
  have hres : ∀ a, ∀ W W' (f : Γ(P₀.A.left, W)), W' ≤ W → dd a W' (rsT f W') = rsT (dd a W f) W' :=
    fun a => ((GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).2 (dd a) (hdd a)).2.2.1
  have hcovθ : ⨆ p, θ ⁻¹ᵁ V p = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : θ z ∈ ⨆ i, V i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine GlobalTheory.T.isCechOneCoboundary_of_refinement (fun i => θ ⁻¹ᵁ P.L.U i) (lc P₀.A.hom c φ) (GlobalTheory.KSUniq.isCoc_lc _ _ _ hcoc)
    (fun p => θ ⁻¹ᵁ V p) jj (fun p => θ.preimage_mono (hle p)) hcovθ q (fun p p' => ?_)
  have hWU : V p ⊓ V p' ≤ P.L.U (jj p) ⊓ P.L.U (jj p') := le_inf (inf_le_left.trans (hle p)) (inf_le_right.trans (hle p'))
  have hOU : θ ⁻¹ᵁ (V p ⊓ V p') ≤ θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p') := θ.preimage_mono hWU
  change rsT (lc P₀.A.hom c φ (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) =
    rsT (q p') (θ ⁻¹ᵁ (V p ⊓ V p')) - rsT (q p) (θ ⁻¹ᵁ (V p ⊓ V p'))
  have E := htr p p'
  rw [hcv] at E
  set g := (P.L.g (jj p) (jj p')).val with hg
  have r1 : rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) = pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) :=
    rsT_pbT θ (O₀ := P.L.U (jj p) ⊓ P.L.U (jj p')) (O₁ := θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p')) le_rfl hOU _
  have e1 : (θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p')) =
      rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) := by
    rw [AdjDlog.app_eq_pbT, pbT_rsT θ hWU le_rfl, r1]
  have e2 : ∀ a, dd a (θ ⁻¹ᵁ (V p ⊓ V p')) ((θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p'))) =
      pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) * rsT (φ a (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) := fun a => by
    rw [e1, hres a _ _ _ hOU, ← hφ a (jj p) (jj p'), rsT_mul, r1]
  simp only [e2] at E
  have hunit : IsUnit (pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p'))) := AdjDlog.isUnit_pbT θ (θ.preimage_mono hWU) _
  refine (hunit.mul_left_cancel ?_).symm
  rw [← E, lc, rsT_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_mul, rsT_constFn _ hOU]
  ring

theorem vert_polAV (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    (hiso : LBIso P₀.L (P.L.pull θ)) {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (W : P.A.left.Opens) (f : Γ(P.A.left, W)) :
    v W f = 0 := by
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis P₀.A P₀.smoothDim
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent k P₀ P₀.g u dd hu hdd _ θ P.L P.isLB hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  obtain ⟨c, hcv⟩ := coeff_const k R P x₀ P₀ θ hθ u hu dd hdd v hc.1
  have c0 := hcob c (cob_of_conn k R P P₀ θ u hu dd hdd φ hφ hcoc V jj v q hc c hcv)
  rw [hcv]
  simp [c0, constFn]

theorem vert_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  intro k _ R _ P x₀ A₀ _ m₀ hm J V jj v q hc W f
  obtain ⟨P₀, θ, hθ, hiso⟩ := GlobalTheory.UniformisedModel.exists_polBaseChange GlobalTheory.allSixLaws.1.polBaseChange (spMap x₀) P
  obtain ⟨e, -, he⟩ := grpPullback_iso hθ hm
  subst he
  have hw : e.hom.left ≫ A₀.hom = P₀.A.hom := Over.w e.hom
  have hc' := transport P.A P.L A₀ P₀.A m₀ e.hom.left hw (fun _ => 0) V jj v q hc
  have h0 := vert_polAV k R P x₀ P₀ _ hθ.1 hiso V jj _ _ hc' W f
  haveI : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  have hle : m₀ ⁻¹ᵁ W ≤ (inv e.hom.left) ⁻¹ᵁ ((e.hom.left ≫ m₀) ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id_assoc]
  have key := congrArg (fun s => pbT (inv e.hom.left) s (m₀ ⁻¹ᵁ W)) h0
  rw [AdjDlog.pbT_pbT (inv e.hom.left) e.hom.left (U := m₀ ⁻¹ᵁ W) (V := (e.hom.left ≫ m₀) ⁻¹ᵁ W) le_rfl hle, IsIso.inv_hom_id, LinDir.pbT_id, pbT_zero] at key
  exact key

end GlobalTheory.HeatConn.Vert
end
end

section

open Matrix

namespace GlobalTheory.ZarhinFam

theorem zW_symm_blocks (d : ℕ) (i j : Fin 4 ⊕ Fin 4) :
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 i j +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 j i =
    2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1 i j := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.zero_apply, smul_eq_mul]
  all_goals (try simp only [@eq_comm _ b a])
  all_goals (try split_ifs)
  all_goals ring

theorem zarhin_block_posDef {d : ℕ} (hd : 0 < d) :
    (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
      (Int.cast : ℤ → ℝ) |>.PosDef := by
  set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx
  have hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢
    rw [h0]
    split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]
  set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC
  set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'
  have hCC : C' * C = 1 := by
    rw [hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg (C'.mulVec) hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C =
      (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
        (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
    congr 1
    · rw [Matrix.transpose_one, Matrix.one_mul, hxx]; ext i j
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    · simp [hx, Matrix.transpose_map]
    · simp [hx]
    · simp
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

theorem zW_symm_posDef : ∀ (d : ℕ), 0 < d →
    ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  intro d hd
  have hsig : Function.Injective sig := by
    intro a b h; revert a b h; decide
  have h := ((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e := zW_symm_blocks d (sig k) (sig l)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

end GlobalTheory.ZarhinFam
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_comp_idPow {S : Scheme.{0}} {B Y : Over S} [GrpObj B] (b : Y ⟶ B) (n : ℕ) :
    b ≫ (𝟙 B) ^ n = b ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem zClsDiag_nsmul_evc {S : Scheme.{0}} {A B Y : Over S} [GrpObj A] [GrpObj B]
    {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (hs : IsDual B A (swap Q)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) :
    n • evc hQ a b = evc hQ a (b ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ← evc_swap hQ hs.isLB, hs.additive.evc_one hs.isLB]
  | succ n ih =>
    rw [succ_nsmul, ih, pow_succ, ← evc_swap hQ hs.isLB (b ^ n * b), (isAdditive_iff hs.isLB).1 hs.additive,
      evc_swap hQ hs.isLB, evc_swap hQ hs.isLB]

theorem zClsDiag_key {h M d : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
    {B : Over S} [GrpObj B] [IsCommMonObj B] {Q : LB (c.A ⊗ B).left} {la : c.A ⟶ B} {mu : B ⟶ c.A}
    (hZ : ZData c d B Q la mu) {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B) :
    d • pull (lift a b).left (cls Q hZ.2.1.isLB) = pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := by
  have hQ := hZ.2.1.isLB
  have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  show d • evc hQ a b = _
  rw [e, pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hZ.2.2.2.2.2.2.1, zClsDiag_comp_idPow,
    zClsDiag_nsmul_evc hQ hZ.2.2.1]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zClsDiag_sum_sig {M : Type*} [AddCommMonoid M] (F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → M) :
    ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) = ∑ s, ∑ t, F s t := by
  let e : Fin 8 ≃ Fin 4 ⊕ Fin 4 := Equiv.ofBijective sig (by decide)
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_congr rfl fun k _ => Equiv.sum_comp e (F (sig k))).trans (Equiv.sum_comp e fun s => ∑ t, F s t)

theorem nsmul_pull_diag_zCls : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → d • GlobalTheory.CechPic.pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left (GlobalTheory.ZarhinFam.zCls c.A B c.isLB hZ.2.1.isLB d mu) = ∑ kl : Fin 8 × Fin 8, GlobalTheory.ZarhinFam.zW d kl.1 kl.2 • GlobalTheory.CechPic.pull (lift (GlobalTheory.ZarhinFam.zpr c.A B mu kl.1) (GlobalTheory.ZarhinFam.zpr c.A B mu kl.2)).left (GlobalTheory.CechPic.cls c.P c.isLB) := by
  intro h M d S t c B _ _ Q la mu hZ _
  let F : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Pic (Zob c.A B).left := fun s u =>
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 s u •
      pull (lift (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) s)
        (Sum.elim (pa c.A B) (fun j => pb c.A B j ≫ mu) u)).left (cls c.P c.isLB)
  rw [show (∑ kl : Fin 8 × Fin 8, zW d kl.1 kl.2 • pull (lift (zpr c.A B mu kl.1) (zpr c.A B mu kl.2)).left
      (cls c.P c.isLB)) = ∑ kl : Fin 8 × Fin 8, F (sig kl.1) (sig kl.2) from rfl, zClsDiag_sum_sig]
  simp only [F, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero]

  simp only [zCls, map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
  lift_snd_assoc, Category.id_comp]
  have hk : ∀ {Y : Over S} (a : Y ⟶ c.A) (b : Y ⟶ B), d • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun a b => zClsDiag_key c hZ a b
  have hk' : ∀ {Y : Over S} (z : ℤ) (a : Y ⟶ c.A) (b : Y ⟶ B), d • z • pull (lift a b).left (cls Q hZ.2.1.isLB) =
      z • pull (lift a (b ≫ mu)).left (cls c.P c.isLB) := fun z a b => by rw [smul_comm, hk]
  simp only [smul_add, Finset.smul_sum, hk, hk', Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
    zero_add, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, one_smul, Finset.sum_add_distrib, mul_smul, two_smul, natCast_zsmul]
  abel

end GlobalTheory.ZarhinFam
end

section

noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def SympCond {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (T : Over S)
    (t₁ : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left) (β : cycAway M →+* k) (z : kˣ),
      x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      (∀ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = 1 ↔ ∃ c, a = M • c) ∧
      (∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, g ^ M = 1 →
        ∃ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = g) ∧
      ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a)
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv c) (unitOn (z ^ (2 * omegaStd a c)))

theorem zetaAway_pow_self (M : ℕ) (hM : M ≠ 0) : zetaAway M ^ M = 1 :=
  Subtype.ext (by simpa [zetaAway, zeta] using (Complex.isPrimitiveRoot_exp M hM).pow_eq_one)

theorem zetaAway_pow_eq (M : ℕ) (hM : M ≠ 0) {k k' : ℕ} (h : (k : ZMod M) = k') :
    zetaAway M ^ k = zetaAway M ^ k' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod k' M, pow_add, pow_add, pow_mul, pow_mul, zetaAway_pow_self M hM,
    one_pow, one_pow, h]

theorem isMultOf_unique {h M : ℕ} (hh : 1 ≤ h) {a : sympSimGrp h M} {n n' : ℕ} (hn : IsMultOf a n)
    (hn' : IsMultOf a n') : (n : ZMod M) = n' := by
  let i : Fin h := ⟨0, hh⟩
  have e1 := hn (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have e2 := hn' (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have h1 : omegaMod M (Pi.single (Sum.inl i) (1 : ZMod M)) (Pi.single (Sum.inr i) 1) = 1 := by
    simp [omegaMod, Pi.single_apply]
  rw [h1, _root_.mul_one] at e1 e2
  rw [← e1, ← e2]

end GlobalTheory.HTSympCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TorusExt

noncomputable section

namespace GlobalTheory.Mum.IdemDiff

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem val_act (oa : D.OAct O) (a : O)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (g : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))

theorem gtPtAct_of_isAdd : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  intro R _ _ D F _ _ O _ _ _ oa a ha g₀ g h t hg hh hadd
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hs : star a * star a = star a := by rw [← star_mul, ha]
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have aa : oa.onB.act a = oa.onB.act a ≫ oa.onB.act a := by rw [← oa.onB.map_mul, ha]
  have ss : oa.onB.act (star a) = oa.onB.act (star a) ≫ oa.onB.act (star a) := by rw [← oa.onB.map_mul, hs]
  obtain ⟨b₁, v₁⟩ := (isAdd_iff_val _ _ _).1 hadd
  have gb : g.b = g.b ≫ oa.onB.act a := by rw [hg.1, Category.assoc, ← aa]
  have tb : t.b = t.b ≫ oa.onB.act a := by
    have e := gb
    rw [b₁, MonObj.mul_comp, ← hh.1] at e
    exact mul_right_cancel e
  refine ⟨tb, fun u hu u₀ χ => corr_of_val D.P.isLB fun y J hJ => (val_act oa a u t χ hJ).trans ?_⟩
  have vg : ∀ χ, charVal g χ y J = charVal g₀ (star a • χ) y J * val₂ u y J (cP D _ χ) g₀.b := fun χ =>
    (val_corr hJ (hg.2 u hu u₀ χ) _).symm.trans (val_act oa a u g₀ χ hJ)
  have vh : charVal h χ y J = charVal h (star a • χ) y J * val₂ u y J (cP D _ χ) h.b :=
    (val_corr hJ (hh.2 u hu u₀ χ) _).symm.trans (val_act oa a u h χ hJ)
  have vc := IsRos.val_comp hG D.P.isAb D.P.isLB ss aa ⟨hu, u₀⟩ ⟨hu, u₀⟩ ⟨hu, u₀⟩ hJ (cP D _ χ) g₀.b
  have vg' : charVal g χ y J = charVal g (star a • χ) y J * val₂ u y J (cP D _ χ) g.b := by
    rw [vg χ, vg (star a • χ), ← mul_smul, hs, vc, cf, hg.1, _root_.mul_assoc]
  have ra := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ t.b h.b (cP D _ χ)).2
  rw [← tb, ← hh.1, ← b₁] at ra
  have e₂ := v₁ (star a • χ) y J hJ
  rw [cf] at e₂
  have a₁ := congrArg Additive.ofMul ra
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul (v₁ χ y J hJ)
  have a₄ := congrArg Additive.ofMul vg'
  have a₅ := congrArg Additive.ofMul vh
  show _ = charVal t χ y J
  apply Additive.ofMul.injective
  simp only [ofMul_mul, th] at a₁ a₂ a₃ a₄ a₅ ⊢
  linear_combination (norm := abel) a₃ - a₄ + a₅ - a₁ - a₂

end GlobalTheory.Mum.IdemDiff
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem isGrpPullback_genMap : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (G' : Over (Sp R')) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left) (h : IsGrpPullback G' G (spMap ρ) β), IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G) (spMap (fracMap ρ hρ)) (genMap hρ β h.1.w) := by
  intro R R' _ _ _ _ ρ hρ G' _ G _ β h
  have n : IsGrpPullback ((Over.pullback (jK R')).obj G') G (spMap (fracMap ρ hρ) ≫ jK R)
      (genMap hρ β h.1.w ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_pullback G' (jK R')).comp h).congr (jK_comp_spMap ρ hρ) (genMap_fst hρ β h.1.w).symm
  exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n (genMap_snd hρ β h.1.w)

end GlobalTheory.Mum.GenDesc
end
